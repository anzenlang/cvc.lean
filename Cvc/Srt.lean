/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Defs

public import Cvc.Basic
public import Cvc.Basic.Env
public import Cvc.Defs



/-! # Sorts

The constructors of `Srt`, the translation from the pure Lean description `Typ`, and the
refinements a sort can satisfy.

`Typ.toSrt` is where function sorts flatten: it walks the right-nested spine of a `Typ.function`
and collects the domains into cvc5's n-ary domain array, which is what makes `α → β → γ` the sort
`(-> α β γ)` while a function in *domain* position stays nested.

`IsArith` and `HasConcat` are the refinement classes the generated operators take. Each is a `Prop`
with a single field discharged by an autoparam, so an instance is proved rather than declared, and
`Typ.typs_of_isArith`/`typs_of_hasConcat` are what let a typed operator case-split on which sort it
actually got.
-/
namespace Cvc public section variable [Ω]



namespace Srt open cvc5 renaming TermManager → Tm, «Sort» → S

section

scoped macro "lift% " fn:ident args:(ppSpace ident)* : term =>
  `((runUnsafe fun tm => tm.$fn $[ $args]* : Env Srt))

scoped macro "def% " id:ident args:(ppSpace ident)* " := " fn:ident : command =>
  let fnId := ``Tm |>.append fn.getId |> Lean.mkIdent
  `(@[inherit_doc $fnId] def $id := fun $[ $args]* => lift% $fn $[ $args]*)

def% bool := getBooleanSort
def% int := getIntegerSort
def% real := getRealSort
def% string := getStringSort
def% regex := getRegExpSort
def% roundingMode := getRoundingModeSort
def% bitVec size := mkBitVectorSort
def% float exp sig := mkFloatingPointSort
def% finiteField size := mkFiniteFieldSort

end

@[inherit_doc Tm.mkArraySort]
def arrayTo (idx elm : Srt) := lift% mkArraySort idx elm

@[inherit_doc arrayTo]
def arrayFrom (elm idx : Srt) := idx.arrayTo elm

/-- An array of `elm`-values indexed by `int`-values. -/
def array (elm : Srt) : Env Srt := int >>= elm.arrayFrom

def bag (elm : Srt) : Env Srt := lift% mkBagSort elm
def set (elm : Srt) : Env Srt := lift% mkSetSort elm
def seq (elm : Srt) : Env Srt := lift% mkSequenceSort elm

def tuple (sorts : Array Srt) : Env Srt := lift% mkTupleSort sorts

@[inherit_doc Tm.mkFunctionSort]
def function (dom : Array Srt) (cod : Srt)
  (domNonempty : 0 < dom.size := by (try grind) <;> fail "failed to prove the domain is nonempty")
: Env Srt :=
  let _ := domNonempty
  lift% mkFunctionSort dom cod

def abstract (a : Abstract) : Env Srt := lift% mkAbstractSort a.toKind

def Abstract.toSrt (a : Abstract) : Env Srt := abstract a

/-! ## Further constructors

`mkDatatypeSort`/`mkDatatypeSorts` are not here: they consume a `Datatype.Decl`, which belongs with
the datatype API.
-/

-- these are written out rather than through `def%`, which leaves its arguments' types to
-- inference and so would take a raw `cvc5.Sort` where an `Srt` is meant

@[inherit_doc Tm.mkPredicateSort]
def predicate (doms : Srts) : Env Srt := lift% mkPredicateSort doms

@[inherit_doc Tm.mkNullableSort]
def nullable (elm : Srt) : Env Srt := lift% mkNullableSort elm

@[inherit_doc Tm.mkRecordSort]
def record (fields : Array (String × Srt)) : Env Srt := lift% mkRecordSort fields

@[inherit_doc Tm.mkParamSort]
def param (symbol : String) : Env Srt := lift% mkParamSort symbol

@[inherit_doc Tm.mkUninterpretedSort]
def uninterpreted (symbol : String) : Env Srt := lift% mkUninterpretedSort symbol

/-- A finite field sort whose size is given in the base `base`. -/
def finiteFieldOfString (size : String) (base : UInt32 := 10) : Env Srt :=
  lift% mkFiniteFieldSortOfString size base

/-- An uninterpreted sort constructor, which an `arity` of parameters instantiate into a sort. -/
def uninterpretedConstructor (arity : Nat) (symbol : String := "") : Env Srt :=
  lift% mkUninterpretedSortConstructorSort arity symbol

/-- A placeholder for a datatype sort not yet resolved.

For mutually recursive parametric datatypes, whose declarations mention each other.
-/
def unresolvedDatatype (symbol : String) (arity : Nat := 0) : Env Srt :=
  lift% mkUnresolvedDatatypeSort symbol arity



/-! ### Datatype sorts

A datatype sort comes from a declaration rather than from its parts, and each call creates a
*fresh* sort even from an identical declaration — see `Cvc/Untyped/Datatype.lean`.
-/

/-- The sort declared under a name in this scope.

A *declared* sort — a datatype, an uninterpreted sort — is fresh every time it is created, so it
cannot be rebuilt from a description the way `Srt.int` or `Srt.set` can. `Srt.datatype` and friends
remember theirs here, and this is how `Typ.toSrt` gets it back.
-/
def ofName (name : String) : Env Srt := do
  match ← getRegisteredSort? name with
  | some srt => return srt
  | none => throwUser <|
    s!"no sort named `{name}` has been declared in this scope; \
declare the datatype before naming it"

/-- Whether a sort has been declared under a name in this scope. -/
def isDeclared (name : String) : Env Bool := do
  return (← getRegisteredSort? name).isSome

@[inherit_doc Tm.mkDatatypeSort]
def datatype (decl : Datatype.Decl) : Env Srt := do
  let name ← decl.toUnsafe.getName
  let srt : Srt ← runUnsafe fun tm => tm.mkDatatypeSort decl
  registerSort name srt.toUnsafe
  return srt

/-- The sorts of a mutually recursive group of datatypes, declared together.

Members refer to each other through `addSelectorUnresolved`, which is only resolved here.
-/
def datatypes (decls : Array Datatype.Decl) : Env Srts := do
  let srts : Srts ← runUnsafe fun tm => tm.mkDatatypeSorts decls
  for h : idx in [0 : decls.size] do
    let name ← decls[idx].toUnsafe.getName
    let some srt := srts[idx]? | throwInternal "`mkDatatypeSorts` answered too few sorts"
    registerSort name srt.toUnsafe
  return srts



/-! ## Testers

Which family a sort belongs to. Each is the guard on the accessors of that family below: asking a
non-array for its index sort fails, and these are how to know not to.
-/

section testers

scoped macro "is% " id:ident " := " fn:ident : command =>
  let fnId := ``S |>.append fn.getId |> Lean.mkIdent
  `(@[inherit_doc $fnId] def $id (srt : Srt) : Bool := $fnId srt.toUnsafe)

is% isBool := isBoolean
is% isInt := isInteger
is% isReal := isReal
is% isString := isString
is% isRegex := isRegExp
is% isRoundingMode := isRoundingMode
is% isBitVec := isBitVector
is% isFloat := isFloatingPoint
is% isFiniteField := isFiniteField
is% isArray := isArray
is% isSet := isSet
is% isBag := isBag
is% isSeq := isSequence
is% isTuple := isTuple
is% isNullable := isNullable
is% isRecord := isRecord
is% isFunction := isFunction
is% isPredicate := isPredicate
is% isAbstract := isAbstract
is% isDatatype := isDatatype
is% isDatatypeConstructor := isDatatypeConstructor
is% isDatatypeSelector := isDatatypeSelector
is% isDatatypeTester := isDatatypeTester
is% isDatatypeUpdater := isDatatypeUpdater
is% isUninterpretedSort := isUninterpretedSort
is% isUninterpretedSortConstructor := isUninterpretedSortConstructor
is% isInstantiated := isInstantiated

end testers



/-! ## Accessors

Each answers only for the family its tester identifies, so each comes in two forms: the plain one
fails elsewhere, the `?`-suffixed one answers `none`.
-/

section accessors

scoped macro "get% " id:ident " : " ty:term " := " fn:ident : command =>
  let fnId := ``S |>.append fn.getId |> Lean.mkIdent
  let fnOptId := ``S |>.append (fn.getId.appendAfter "?") |> Lean.mkIdent
  let idOptId := id.getId.appendAfter "?" |> Lean.mkIdent
  `(@[inherit_doc $fnId]
    def $id (srt : Srt) : Res $ty := $fnId srt.toUnsafe |>.mapError Error.ofUnsafe
    @[inherit_doc $fnId]
    def $idOptId (srt : Srt) : Option $ty := $fnOptId srt.toUnsafe)

/-! ### Any sort -/

get% getKind : cvc5.SortKind := getKind
get% hasSymbol : Bool := hasSymbol
get% getSymbol : String := getSymbol

/-! ### Sized and parameterized sorts -/

get% getBitVecSize : UInt32 := getBitVectorSize
get% getFiniteFieldSize : Nat := getFiniteFieldSize
get% getFloatExponentSize : UInt32 := getFloatingPointExponentSize
get% getFloatSignificandSize : UInt32 := getFloatingPointSignificandSize

/-! ### Containers -/

get% getArrayIndexSort : Srt := getArrayIndexSort
get% getArrayElementSort : Srt := getArrayElementSort
get% getSetElementSort : Srt := getSetElementSort
get% getBagElementSort : Srt := getBagElementSort
get% getSeqElementSort : Srt := getSequenceElementSort
get% getNullableElementSort : Srt := getNullableElementSort
get% getTupleLength : UInt32 := getTupleLength
get% getTupleSorts : Srts := getTupleSorts

/-! ### Functions -/

get% getFunctionArity : Nat := getFunctionArity
get% getFunctionDomainSorts : Srts := getFunctionDomainSorts
get% getFunctionCodomainSort : Srt := getFunctionCodomainSort

/-! ### Abstract and uninterpreted sorts -/

get% getAbstractedKind : cvc5.SortKind := getAbstractedKind
get% getUninterpretedSortConstructor : Srt := getUninterpretedSortConstructor
get% getUninterpretedSortConstructorArity : UInt32 := getUninterpretedSortConstructorArity
get% getInstantiatedParameters : Srts := getInstantiatedParameters

/-! ### Datatypes

The datatype *sorts*: what a constructor, selector or tester sort relates. The `Datatype` these
answer for has its own API, which is not wrapped yet.
-/

get% getDatatype : Datatype := getDatatype
get% getDatatypeArity : Nat := getDatatypeArity
get% getDatatypeConstructorArity : Nat := getDatatypeConstructorArity
get% getDatatypeConstructorDomainSorts : Srts := getDatatypeConstructorDomainSorts
get% getDatatypeConstructorCodomainSort : Srt := getDatatypeConstructorCodomainSort
get% getDatatypeSelectorDomainSort : Srt := getDatatypeSelectorDomainSort
get% getDatatypeSelectorCodomainSort : Srt := getDatatypeSelectorCodomainSort
get% getDatatypeTesterDomainSort : Srt := getDatatypeTesterDomainSort
get% getDatatypeTesterCodomainSort : Srt := getDatatypeTesterCodomainSort

end accessors



/-! ## Instantiation and substitution -/

/-- Instantiates a parametric sort with the given parameters. -/
def instantiate (srt : Srt) (params : Srts) : Res Srt :=
  S.instantiate srt.toUnsafe params |>.mapError Error.ofUnsafe

@[inherit_doc instantiate]
def instantiate? (srt : Srt) (params : Srts) : Option Srt := S.instantiate? srt.toUnsafe params

/-- Replaces `srts` by `replacements` throughout a sort, simultaneously. -/
def substitute (srt : Srt) (srts replacements : Srts) : Res Srt :=
  S.substitute srt.toUnsafe srts replacements |>.mapError Error.ofUnsafe

@[inherit_doc substitute]
def substitute? (srt : Srt) (srts replacements : Srts) : Option Srt :=
  S.substitute? srt.toUnsafe srts replacements

end Srt


/-! ## Lean types encoding cvc sorts and their values -/

namespace Typ

abbrev isArith : Typ → Bool
| int | real => true
| bool | string | regex | roundingMode
| bitVec _ | float _ _ | finiteField _ | arrayTo _ _
| bag _ | set _ | seq _ | prod _ | nullable _
| datatype _ | abstract _ | function _ _ => false

omit [Ω] in
theorem typs_of_isArith {typ : Typ} : typ.isArith → typ = int ∨ typ = real := by grind

abbrev hasConcat : Typ → Bool
| string | seq _ => true
| int | real
| bool | regex | roundingMode
| bitVec _ | float _ _ | finiteField _ | arrayTo _ _
| bag _ | set _ | prod _ | nullable _
| datatype _ | abstract _ | function _ _ => false

omit [Ω] in
theorem typs_of_hasConcat {typ : Typ} : typ.hasConcat → typ = string ∨ ∃ t, typ = seq t := by grind

/-- Helper for `toSrt`. -/
def foldFunctionCod [Monad m] (srt' : Typ)
  (acc : α) (f : α → (s : Typ) → (sizeOf s < sizeOf srt') → m α)
: m (α × (cod : Typ) ×' sizeOf cod ≤ sizeOf srt') :=
  match h : srt' with
  | function dom cod => do
    let acc ← f acc dom (by grind only [= function.sizeOf_spec])
    let (acc, ⟨cod, h⟩) ← cod.foldFunctionCod acc fun acc s h =>
      f acc s (by grind only [= function.sizeOf_spec])
    return (acc, ⟨cod, by grind only [= function.sizeOf_spec]⟩)
  | cod => return (acc, ⟨cod, by grind only⟩)

-- /-- Helper for `toSrt`. -/
-- def foldProdArgs {α : Type} {m : Type → Type} [Monad m] (srt' : Typ)
--   (acc : α) (f : α → (s : Typ) → (sizeOf s ≤ sizeOf srt') → m α)
-- : m α :=
--   match h : srt' with
--   | prod args => do
--     let acc ← f acc fst (by grind)
--     snd.foldProdSnd acc fun acc s h => f acc s (by grind only [= prod.sizeOf_spec])
--   | rgt => f acc rgt (by grind)

/-- Conversion to `Srt`. -/
public def toSrt [Ω] : Typ → Env Srt
| bool => Srt.bool | int => Srt.int | real => Srt.real
| regex => Srt.regex | string => Srt.string
| roundingMode => Srt.roundingMode
| bitVec size => Srt.bitVec size.toUInt32
| float exp sig => Srt.float exp.toUInt32 sig.toUInt32
| finiteField size => Srt.finiteField size
| arrayTo idx elm => do elm.toSrt >>= (← idx.toSrt).arrayTo
| bag elm => elm.toSrt >>= Srt.bag
| set elm => elm.toSrt >>= Srt.set
| seq elm => elm.toSrt >>= Srt.seq
| nullable elm => elm.toSrt >>= Srt.nullable
| abstract a => Srt.abstract a
| prod args => foldProdArgs args >>= Srt.tuple
| datatype name => Srt.ofName name
| function dom cod => do
  let dom ← dom.toSrt
  /- non-empty array, required for `Srt.function` -/
  let acc : {a : Array Srt // 0 < a.size} := ⟨#[dom], by grind⟩
  let (dom, ⟨cod, h⟩) ← cod.foldFunctionCod acc fun acc s h =>
    /- push and update proof that array (`acc`) is non-empty -/
    return ⟨acc.val.push (← s.toSrt), by grind⟩
  let cod ← cod.toSrt
  Srt.function dom cod
where
  foldProdArgs : (l : List Typ) → (acc : Array Srt := #[]) → Env (Array Srt)
    | [], args => return args
    | hd::tl, args => do
      let hd ← hd.toSrt
      foldProdArgs tl <| args.push hd

end Typ


/-- The `Typ` associated to some type. -/
abbrev Typ.of (α : Type) [A : ToTyp α] : Typ := A.typ

/-- `Srt` associated to a type through `WithTyp`. -/
abbrev ToTyp.srt [ToTyp α] : Env Srt := Typ.of α |>.toSrt

@[inherit_doc ToTyp.srt]
abbrev Srt.of (α : Type) [A : ToTyp α] : Env Srt := A.srt

-- namespace WithTyp

-- @[default_instance]
-- instance : WithTyp Bool .bool := {}
-- @[default_instance]
-- instance : WithTyp Nat .int := {}
-- @[default_instance]
-- instance : WithTyp Int .int := {}
-- @[default_instance]
-- instance : WithTyp Rat .real := {}
-- @[default_instance]
-- instance : WithTyp String .string := {}
-- @[default_instance]
-- instance : WithTyp (BitVec size) (.bitVec size) := {}
-- @[default_instance]
-- instance : WithTyp Float.RoundingMode .roundingMode := {}
-- @[default_instance]
-- instance [A : ToTyp α] : WithTyp (Array α) (.seq A.typ) := {}

-- end WithTyp

namespace ToTyp

instance : ToTyp Bool := ⟨.bool⟩
instance : ToTyp Int := ⟨.int⟩
instance : ToTyp Rat := ⟨.real⟩
instance : ToTyp String := ⟨.string⟩
instance : ToTyp (BitVec size) := ⟨.bitVec size⟩
instance : ToTyp Cvc.Float.RoundingMode := ⟨.roundingMode⟩
instance [A : ToTyp α] : ToTyp (Array α) := ⟨.seq A.typ⟩
/-- Lean's `Option` denotes cvc5's `Nullable`. -/
instance [A : ToTyp α] : ToTyp (Option α) := ⟨.nullable A.typ⟩

end ToTyp



class IsArith (α : Type) [A : ToTyp α] : Prop where
  valid_typ : A.typ.isArith := by simp [Typ.isArith, ToTyp.typ] <;> grind

instance : IsArith Int := {}
instance : IsArith Rat := {}

class HasConcat (α : Type) [A : ToTyp α] : Prop where
  valid_typ : A.typ.hasConcat := by simp [Typ.hasConcat, ToTyp.typ] <;> grind

instance : HasConcat String := {}
instance [ToTyp α] : HasConcat (Array α) := {}



/-! ### Regular expressions -/

structure Regex
deriving DecidableEq, Hashable, Ord

namespace Regex

instance : ToTyp Regex := ⟨.regex⟩

end Regex



/-! ### Functions -/

namespace ToTyp

instance [A : ToTyp α] [B : ToTyp β] : ToTyp (α → β) := ⟨.function A.typ B.typ⟩

example : ToTyp (Int → Bool → Int → Rat) := inferInstance

end ToTyp
