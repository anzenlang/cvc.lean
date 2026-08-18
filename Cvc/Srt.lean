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

/-- Reports sort `symbol` as already declared if it is in the `Env`'s registry. -/
def checkFreshSortSymbol (symbol : String) : Env Unit := do
  if ← Srt.isDeclared symbol then throwUser s!"a sort named `{symbol}` is already declared"

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

/-- cvc5's fully abstract sort, `?`.

Not *first*-class: cvc5 accepts it as a container element, an array parameter or a function
codomain, and rejects it as a nullable element, a tuple component or a function domain. That rule
is what `Typ`/`Typ?` encode.
-/
def any : Env Srt := runUnsafe fun tm => tm.mkAbstractSort .ABSTRACT_SORT

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

/-- The first name occurring twice in a list, if any. -/
private def firstDuplicate : List String → Option String
  | [] => none
  | hd :: tl => if tl.contains hd then some hd else firstDuplicate tl

/-- A record sort, of named and ordered fields.

**A record must have at least one field.** cvc5 builds the empty record sort happily, but it
denotes what the empty tuple already denotes and nothing in SMT-LIB has a use for it, so it is
refused here rather than left as a second spelling of the same thing.

**Field names must be distinct, and this is our check, not cvc5's.** cvc5 accepts
`{a : Int, a : Bool}` and builds a datatype carrying two selectors both named `a`, which nothing
can then select unambiguously.

The order is part of the sort: `{a : Int, b : Bool}` and `{b : Bool, a : Int}` are different.

Both checks sit here rather than on the callers, so every path to a record sort inherits them —
`Typ.toSrt` reaches cvc5 only through this function.
-/
def record (fields : Array (String × Srt)) : Env Srt := do
  if fields.isEmpty then
    throwUser "a record sort must have at least one field"
  if let some name := firstDuplicate (fields.toList.map Prod.fst) then
    throwUser s!"record sort has more than one field named `{name}`"
  lift% mkRecordSort fields

@[inherit_doc Tm.mkParamSort]
def param (symbol : String) : Env Srt := lift% mkParamSort symbol

@[inherit_doc Tm.mkUninterpretedSort]
def uninterpreted (symbol : String) : Env Srt := do
  Srt.checkFreshSortSymbol symbol
  let u ← (lift% mkUninterpretedSort symbol)
  registerSort symbol u
  return u

/-- A finite field sort whose size is given in the base `base`. -/
def finiteFieldOfString (size : String) (base : UInt32 := 10) : Env Srt :=
  lift% mkFiniteFieldSortOfString size base

/-- An uninterpreted sort constructor, which an `arity` of parameters instantiate into a sort. -/
def uninterpretedConstructor (arity : Nat) (symbol : String := "") : Env Srt := do
  Srt.checkFreshSortSymbol symbol
  let u ← (lift% mkUninterpretedSortConstructorSort arity symbol)
  registerSort symbol u
  return u

/-- A placeholder for a datatype sort not yet resolved.

For mutually recursive parametric datatypes, whose declarations mention each other.
-/
def unresolvedDatatype (symbol : String) (arity : Nat := 0) : Env Srt :=
  lift% mkUnresolvedDatatypeSort symbol arity



/-! ### Datatype sorts

A datatype sort comes from a declaration rather than from its parts, and each call creates a
*fresh* sort even from an identical declaration — see `Cvc/Untyped/Datatype.lean`.
-/

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
is% isUninterpreted := isUninterpretedSort
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
| bag _ | set _ | seq _ | prod _ | nullable _ | record _
| datatype _ | function _ _ | uninterpreted _ => false

omit [Ω] in
theorem typs_of_isArith {typ : Typ} : typ.isArith → typ = int ∨ typ = real := by grind

abbrev hasConcat : Typ → Bool
| string | seq _ => true
| int | real
| bool | regex | roundingMode
| bitVec _ | float _ _ | finiteField _ | arrayTo _ _
| bag _ | set _ | prod _ | nullable _ | record _
| datatype _ | function _ _ | uninterpreted _ => false

omit [Ω] in
theorem typs_of_hasConcat {typ : Typ} : typ.hasConcat → typ = string ∨ ∃ t, typ = seq t := by grind

end Typ


/-! ## Conversions between `Typ` and `Srt`

Each direction is a mutual pair, `Typ`/`Typ?` being mutual. `Typ.toSrt` is **total**: the split is
exactly cvc5's first-class rule, so every `Typ` denotes a sort it accepts.
-/

mutual

/-- Conversion to `Srt`. -/
public def Typ.toSrt [Ω] : Typ → Env Srt
| .bool => Srt.bool | .int => Srt.int | .real => Srt.real
| .regex => Srt.regex | .string => Srt.string
| .roundingMode => Srt.roundingMode
| .bitVec size => Srt.bitVec size.toUInt32
| .float exp sig => Srt.float exp.toUInt32 sig.toUInt32
| .finiteField size => Srt.finiteField size
| .arrayTo idx elm => do (← Cvc.Typ?.toSrt elm) |> (← Cvc.Typ?.toSrt idx).arrayTo
| .bag elm => Cvc.Typ?.toSrt elm >>= Srt.bag
| .set elm => Cvc.Typ?.toSrt elm >>= Srt.set
| .seq elm => Cvc.Typ?.toSrt elm >>= Srt.seq
| .nullable elm => Cvc.Typ.toSrt elm >>= Srt.nullable
| .prod args => Cvc.Typ.toSrtList args >>= Srt.tuple
| .record fields => Cvc.Typ.toSrtFields fields >>= Srt.record
| .datatype name => Srt.ofName name
-- the spine is flattened on the `Srt` side rather than the `Typ` side: both operands are
-- structurally smaller, where walking the curried spine first is not, and cvc5 does not flatten
-- on its own. A function in *domain* position stays nested, which is what keeps it higher-order
| .function dom cod => do
  let dom ← Cvc.Typ.toSrt dom
  let cod ← Cvc.Typ?.toSrt cod
  if cod.isFunction then
    Srt.function (#[dom] ++ (← cod.getFunctionDomainSorts)) (← cod.getFunctionCodomainSort)
  else Srt.function #[dom] cod
| .uninterpreted name => do
  let some (srt : Srt) ← getRegisteredSort? name
    | throwUser s!"unknown uninterpreted sort `{name}`"
  if srt.isUninterpreted then return srt
  else throwUser s!"sort `{name}` is not an uninterpreted sort"

@[inherit_doc Typ.toSrt]
public def Typ.toSrtList [Ω] : List Typ → Env (Array Srt)
| [] => return #[]
| hd :: tl => return #[← Cvc.Typ.toSrt hd] ++ (← Cvc.Typ.toSrtList tl)

@[inherit_doc Typ.toSrt]
public def Typ.toSrtFields [Ω] : List (String × Typ) → Env (Array (String × Srt))
| [] => return #[]
| (name, ty) :: tl => return #[(name, ← Cvc.Typ.toSrt ty)] ++ (← Cvc.Typ.toSrtFields tl)

@[inherit_doc Typ.toSrt]
public def Typ?.toSrt [Ω] : Typ? → Env Srt
| .typ t => Cvc.Typ.toSrt t
| .any => Srt.any
| .abstract a => Srt.abstract a

end




namespace Srt

/-- The name a *declared* sort round-trips through, checked against the scope's registry.

A `Typ` for a declared sort is only worth anything if `Typ.toSrt` can resolve it back, so the name
is verified to be registered *and* to name this very sort. Skipping the check would silently answer
a `Typ` that resolves to a different sort — cvc5 lets two distinct sorts print the same name, which
is the whole reason the registry exists.
-/
private def checkDeclared (srt : Srt) (name : String) : Env String := do
  let some registered ← getRegisteredSort? name
    | throwUser s!"\
      cannot convert the declared sort `{name}` to a `Typ`: no sort of that name is declared in \
      this scope"
  if registered != srt.toUnsafe then
    throwUser s!"\
      cannot convert the declared sort `{name}` to a `Typ`: the name is registered to a different \
      sort in this scope"
  return name

/-- Curries a cvc5 domain array back into the right-nested spine `Typ` uses. -/
private def curryTo : List Typ → Typ? → Typ?
  | [], cod => cod
  | hd :: tl, cod => .typ (.function hd (curryTo tl cod))

mutual

/-- Conversion to `Typ`, the inverse of `Typ.toSrt` wherever a `Typ` can describe the sort.

`partial` because the recursion is on `Srt`, which is opaque: it is cvc5's `Sort` under the hood,
so nothing here is structurally smaller to Lean.

**The order of the tests is load-bearing.** cvc5 implements tuples, records and nullables *as*
datatypes, so `isDatatype` is true of all three and the narrower testers have to be asked first.

Two shapes are rebuilt rather than read off, both because `Typ.toSrt` flattens them:

- a **function** sort's domain is n-ary in cvc5 and curried in `Typ`, so the spine is folded back
  to the right — `(-> α β γ)` becomes `function α (function β γ)`;
- a **tuple**'s components are already flat on both sides, so `prod` takes them as they come.

Sorts that no `Typ` case describes fail rather than approximate: records, uninterpreted sort
constructors and their instantiations, and the datatype-operator sorts.
-/
public partial def toTyp (srt : Srt) : Env Typ := do
  if srt.isBool then return .bool
  else if srt.isInt then return .int
  else if srt.isReal then return .real
  else if srt.isString then return .string
  else if srt.isRegex then return .regex
  else if srt.isRoundingMode then return .roundingMode
  else if srt.isBitVec then return .bitVec (← srt.getBitVecSize).toNat
  else if srt.isFloat then
    return .float (← srt.getFloatExponentSize).toNat (← srt.getFloatSignificandSize).toNat
  else if srt.isFiniteField then return .finiteField (← srt.getFiniteFieldSize)
  -- an abstract sort is not first-class, so it is a `Typ?` and never a `Typ`
  else if srt.isAbstract then
    throwUser s!"\
      `{srt}` is an abstract sort, which cvc5 does not accept where a first-class one is wanted; \
      it has a `Typ?` but no `Typ`"
  else if srt.isArray then
    return .arrayTo
      (← Cvc.Srt.toTyp? (← srt.getArrayIndexSort)) (← Cvc.Srt.toTyp? (← srt.getArrayElementSort))
  else if srt.isSet then return .set (← Cvc.Srt.toTyp? (← srt.getSetElementSort))
  else if srt.isBag then return .bag (← Cvc.Srt.toTyp? (← srt.getBagElementSort))
  else if srt.isSeq then return .seq (← Cvc.Srt.toTyp? (← srt.getSeqElementSort))
  -- before `isDatatype`: cvc5 implements a nullable as a mono-morphized datatype
  else if srt.isNullable then
    return .nullable (← Cvc.Srt.toTyp (← srt.getNullableElementSort))
  -- likewise a tuple
  else if srt.isTuple then
    return .prod (← (← srt.getTupleSorts).toList.mapM Cvc.Srt.toTyp)
  else if srt.isFunction then
    let doms ← (← srt.getFunctionDomainSorts).toList.mapM Cvc.Srt.toTyp
    let cod ← Cvc.Srt.toTyp? (← srt.getFunctionCodomainSort)
    match doms with
    | [] => throwInternal s!"function sort `{srt}` has an empty domain"
    | hd :: tl => return .function hd (Srt.curryTo tl cod)
  -- an *instantiated* sort — a parametric datatype or an uninterpreted sort constructor applied to
  -- arguments — has a name but no `Typ`: the named cases carry a name and nothing else. This comes
  -- before them because cvc5 reports `(U Int)` as an uninterpreted sort, and because
  -- `isInstantiated` on its own is true even of a *non*-parametric datatype — the parameters are
  -- what actually distinguishes the two
  else if !(srt.getInstantiatedParameters?.getD #[]).isEmpty then
    throwUser s!"\
      `Typ` has no case for `{srt}`, an instantiated sort: `Typ.datatype` and `Typ.uninterpreted` \
      carry a name and nothing else"
  else if srt.isUninterpreted then
    let some symbol := srt.getSymbol?
      | throwUser s!"cannot convert the uninterpreted sort `{srt}` to a `Typ`: it has no name"
    return .uninterpreted (← srt.checkDeclared symbol)
  -- a record is a datatype with one constructor and one selector per field, so the fields are
  -- read off that constructor — in order, the order being part of the sort
  else if srt.isRecord then
    -- the raw cvc5 accessors, this module sitting below the datatype API
    let dt := (← srt.getDatatype).toUnsafe
    if h : 0 < dt.getNumConstructors then
      let ctor := dt[0]'h
      let mut fields := #[]
      for hIdx : idx in [0 : ctor.getNumSelectors] do
        let sel := ctor[idx]
        let srt' : Srt ← Env.lift5 sel.getCodomainSort
        fields := fields.push (← sel.getName, ← Cvc.Srt.toTyp srt')
      return .record fields.toList
    else throwInternal s!"record sort `{srt}` has no constructor"
  else if srt.isUninterpretedSortConstructor then
    throwUser s!"\
      `Typ` has no case for `{srt}`, an uninterpreted sort constructor: it names a sort of arity \
      greater than zero, which `Typ.uninterpreted` cannot describe"
  else if srt.isDatatype then
    -- a datatype sort has no *symbol*; its name is the declaration's
    return .datatype (← srt.checkDeclared (← (← srt.getDatatype).getName))
  else throwUser s!"`Typ` has no case for the sort `{srt}` (sort kind `{← srt.getKind}`)"

/-- Conversion to `Typ?`, which unlike `toTyp` accepts the abstract sorts.

Only reached where cvc5 permits a non-first-class sort — a container element, an array parameter,
a function codomain — so `.any` and `.abstract` land exactly where they are legal.
-/
public partial def toTyp? (srt : Srt) : Env Typ? := do
  if srt.isAbstract then
    let kind ← srt.getAbstractedKind
    -- `?` reports its own kind as its abstracted one; every other abstract sort names a family
    if kind matches .ABSTRACT_SORT then return .any
    else return .abstract (← Srt.Abstract.ofKind kind)
  else return .typ (← Cvc.Srt.toTyp srt)

end

end Srt


/-- The `Typ` associated to some type. -/
abbrev Typ.of (α : Type) [A : ToTyp α] : Typ := A.typ

/-- `Srt` associated to a type through `WithTyp`. -/
abbrev ToTyp.srt [ToTyp α] : Env Srt := Typ.of α |>.toSrt

@[inherit_doc ToTyp.srt]
abbrev Srt.of (α : Type) [A : ToTyp α] : Env Srt := A.srt


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
