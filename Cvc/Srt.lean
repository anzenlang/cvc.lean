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
public meta import Lean.Elab.Term



/-! # Sorts

The constructors of `Srt`, the conversions between a `Srt` and its Lean description `Typ`, and the
classes `IsArith` and `HasConcat` the operators restrict their sorts with.

Function sorts are curried: `α → β → γ` is the sort `(-> α β γ)`, while a function in domain
position stays a higher-order argument.
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

/-- The sort of the finite field with `size` elements, `size` being prime. -/
def finiteField (size : Nat) : Env Srt := lift% mkFiniteFieldSort size

end

/-- The sort declared under `name` in this scope, failing if there is none. -/
def ofName (name : String) : Env Srt := do
  match ← getRegisteredSort? name with
  | some srt => return srt
  | none => throwUser <|
    s!"no sort named `{name}` has been declared in this scope; \
declare the sort before naming it"
-- A *declared* sort — a datatype, an uninterpreted sort — is fresh every time it is created, so it
-- cannot be rebuilt from a description the way `Srt.int` or `Srt.set` can. `Srt.datatype` and
-- friends remember theirs in the scope's state, and this is how `Typ.toSrt` gets it back.

/-- Whether a sort has been declared under a name in this scope. -/
def isDeclared (name : String) : Env Bool := do
  return (← getRegisteredSort? name).isSome

/-- Fails if a sort named `symbol` has already been declared in this scope. -/
def checkFreshSortSymbol (symbol : String) : Env Unit := do
  if ← Srt.isDeclared symbol then throwUser s!"a sort named `{symbol}` is already declared"

/-- Creates the sort of arrays from `idx` to `elm`, *e.g.* `idx.arrayTo elm`. -/
def arrayTo (idx elm : Srt) := lift% mkArraySort idx elm

/-- Creates the sort of arrays to `elm` from `idx`, *e.g.* `elm.arrayFrom idx`. -/
def arrayFrom (elm idx : Srt) := idx.arrayTo elm

/-- An array of `elm`-values indexed by `int`-values. -/
def array (elm : Srt) : Env Srt := int >>= elm.arrayFrom

/-- The sort of bags of `elm`. -/
def bag (elm : Srt) : Env Srt := lift% mkBagSort elm
/-- The sort of sets of `elm`. -/
def set (elm : Srt) : Env Srt := lift% mkSetSort elm
/-- The sort of sequences of `elm`. -/
def seq (elm : Srt) : Env Srt := lift% mkSequenceSort elm

/-- The sort of tuples of the given components. -/
def tuple (sorts : Array Srt) : Env Srt := lift% mkTupleSort sorts

/-- The sort of functions from the domain sorts `dom` to `cod`. -/
def function (dom : Array Srt) (cod : Srt)
  (domNonempty : 0 < dom.size := by (try grind) <;> fail "failed to prove the domain is nonempty")
: Env Srt :=
  let _ := domNonempty
  lift% mkFunctionSort dom cod

/-- The abstract sort of a family, its parameters left unspecified. -/
def abstract (a : Abstract) : Env Srt := lift% mkAbstractSort a.toKind

/-- cvc5's fully abstract sort, `?`.

cvc5 accepts it only as a set, bag or sequence element, an array's index or element, or a function's
codomain.
-/
def any : Env Srt := runUnsafe fun tm => tm.mkAbstractSort .ABSTRACT_SORT

def Abstract.toSrt (a : Abstract) : Env Srt := abstract a

/-! ## Further constructors -/

-- these are written out rather than through `def%`, which leaves its arguments' types to
-- inference and so would take a raw `cvc5.Sort` where an `Srt` is meant

/-- The sort of predicates over `doms`: functions from them to `Bool`. -/
def predicate (doms : Srts) : Env Srt := lift% mkPredicateSort doms

/-- The sort of nullable `elm` values, denoted Lean-side by `Option`. -/
def nullable (elm : Srt) : Env Srt := lift% mkNullableSort elm

/-- The first name occurring twice in a list, if any. -/
private def firstDuplicate : List String → Option String
  | [] => none
  | hd :: tl => if tl.contains hd then some hd else firstDuplicate tl

/-- A record sort, of named fields in order.

Fails on an empty record and on a repeated field name. The order is part of the sort:
`{a : Int, b : Bool}` and `{b : Bool, a : Int}` are different.
-/
def record (fields : Array (String × Srt)) : Env Srt := do
  if fields.isEmpty then
    throwUser "a record sort must have at least one field"
  if let some name := firstDuplicate (fields.toList.map Prod.fst) then
    throwUser s!"record sort has more than one field named `{name}`"
  lift% mkRecordSort fields
-- Both checks are ours: cvc5 builds the empty record sort, which denotes what the empty tuple
-- already denotes, and accepts `{a : Int, a : Bool}`, building a datatype with two selectors named
-- `a` that nothing can select unambiguously. They sit here rather than on the callers, so every
-- path to a record sort inherits them — `Typ.toSrt` reaches cvc5 only through this function.

@[inherit_doc Tm.mkParamSort]
def param (symbol : String) : Env Srt := lift% mkParamSort symbol

/-- A new uninterpreted sort named `symbol`, which `Typ.uninterpreted symbol` then names.

The name must not be taken by another sort declared in this scope.
-/
def uninterpreted (symbol : String) : Env Srt := do
  Srt.checkFreshSortSymbol symbol
  let u ← (lift% mkUninterpretedSort symbol)
  registerSort symbol u
  return u

/-- A finite field sort whose size is given in the base `base`. -/
def finiteFieldOfString (size : String) (base : UInt32 := 10) : Env Srt :=
  lift% mkFiniteFieldSortOfString size base

/-- An uninterpreted sort constructor, which `arity` parameters instantiate into a sort.

The name must not be taken by another sort declared in this scope.
-/
def uninterpretedConstructor (arity : Nat) (symbol : String) : Env Srt := do
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

A datatype sort comes from a `Datatype.Decl`. Each call makes a *fresh* sort, even from an
identical declaration, so a datatype is declared once per scope and then named with `Typ.datatype`.
-/

/-- The sort of the datatype `decl` declares, which `Typ.datatype` then names.

The datatype's name must not be taken by another sort declared in this scope.
-/
def datatype (decl : Datatype.Decl) : Env Srt := do
  let name ← decl.toUnsafe.getName
  let srt : Srt ← runUnsafe fun tm => tm.mkDatatypeSort decl
  registerSort name srt.toUnsafe
  return srt

/-- The sorts of a mutually recursive group of datatypes, declared together.

Members refer to each other through `Datatype.Ctor.Decl.addSelectorUnresolved`. As for
`Srt.datatype`, each name must be new to this scope.
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

/-- Whether this sort instantiates a parametric datatype or an uninterpreted sort constructor.

cvc5 also answers `true` for a datatype sort without parameters: a non-empty
`getInstantiatedParameters` is the reliable test. See `Srt.instantiate`.
-/
def isInstantiated (srt : Srt) : Bool := S.isInstantiated srt.toUnsafe

end testers



/-! ## Accessors

Each answers only for the family its tester identifies, so each comes in two forms: the plain one
fails elsewhere, the `?`-suffixed one answers `none`.
-/

section accessors

-- Accessors whose lean-cvc5 docstring is wrong for ours are written out by hand rather than
-- through `get%`, which inherits it.
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

/-- Whether this sort has a symbol, a name; see `getSymbol`. -/
def hasSymbol (srt : Srt) : Res Bool := S.hasSymbol srt.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc hasSymbol]
def hasSymbol? (srt : Srt) : Option Bool := S.hasSymbol? srt.toUnsafe

/-- The symbol of this sort, its name.

It is the name given to `Srt.uninterpreted`, `Srt.uninterpretedConstructor` or
`Srt.unresolvedDatatype`.
-/
def getSymbol (srt : Srt) : Res String := S.getSymbol srt.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getSymbol]
def getSymbol? (srt : Srt) : Option String := S.getSymbol? srt.toUnsafe

/-! ### Sized and parameterized sorts -/

get% getBitVecSize : UInt32 := getBitVectorSize
get% getFiniteFieldSize : Nat := getFiniteFieldSize
get% getFloatExponentSize : UInt32 := getFloatingPointExponentSize
get% getFloatSignificandSize : UInt32 := getFloatingPointSignificandSize

/-! ### Containers -/

/-- The index sort of an array sort. -/
def getArrayIndexSort (srt : Srt) : Res Srt :=
  S.getArrayIndexSort srt.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getArrayIndexSort]
def getArrayIndexSort? (srt : Srt) : Option Srt := S.getArrayIndexSort? srt.toUnsafe

/-- The element sort of an array sort. -/
def getArrayElementSort (srt : Srt) : Res Srt :=
  S.getArrayElementSort srt.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getArrayElementSort]
def getArrayElementSort? (srt : Srt) : Option Srt := S.getArrayElementSort? srt.toUnsafe

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

/-- The sorts a parametric datatype or an uninterpreted sort constructor was instantiated with.

See `Srt.instantiate`.
-/
def getInstantiatedParameters (srt : Srt) : Res Srts :=
  S.getInstantiatedParameters srt.toUnsafe |>.mapError Error.ofUnsafe
@[inherit_doc getInstantiatedParameters]
def getInstantiatedParameters? (srt : Srt) : Option Srts :=
  S.getInstantiatedParameters? srt.toUnsafe

/-! ### Datatypes

The datatype *sorts*: what a constructor, selector or tester sort relates. The `Datatype` they
answer has its own API, in `Cvc.Untyped.Theory.Datatype`.
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


/-! ## Sort refinements -/

namespace Typ

/-- Whether a sort is arithmetic: `Int` or `Real`. -/
abbrev isArith : Typ → Bool
| int | real => true
| bool | string | regex | roundingMode
| bitVec _ | float _ _ | finiteField _ | arrayTo _ _
| bag _ | set _ | seq _ | prod _ | nullable _ | record _
| datatype _ | function _ _ | uninterpreted _ => false

omit [Ω] in
theorem typs_of_isArith {typ : Typ} : typ.isArith → typ = int ∨ typ = real := by grind

/-- Whether a sort has concatenation: strings and sequences. -/
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


/-! ## Conversions between `Typ` and `Srt` -/

mutual

/-- The sort a `Typ` describes.

Fails only on a `datatype` or `uninterpreted` name no sort was declared under in this scope.
-/
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

A function sort comes back curried, `(-> α β γ)` as `function α (function β γ)`. A declared sort —
a datatype or an uninterpreted sort — converts only if it is the sort this scope registered under
its name.

Sorts that no `Typ` describes fail rather than approximate: the abstract sorts, which `toTyp?`
accepts, instantiated parametric datatypes, uninterpreted sort constructors and their
instantiations, and the datatype-operator sorts.
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
-- `partial` because the recursion is on `Srt`, which is opaque: it is cvc5's `Sort` under the hood,
-- so nothing here is structurally smaller to Lean.
--
-- **The order of the tests is load-bearing.** cvc5 implements tuples, records and nullables *as*
-- datatypes, so `isDatatype` is true of all three and the narrower testers have to be asked first.
--
-- Two shapes are rebuilt rather than read off, both because `Typ.toSrt` flattens them:
--
-- - a **function** sort's domain is n-ary in cvc5 and curried in `Typ`, so the spine is folded back
--   to the right — `(-> α β γ)` becomes `function α (function β γ)`;
-- - a **tuple**'s components are already flat on both sides, so `prod` takes them as they come.

/-- Conversion to `Typ?`, which unlike `toTyp` accepts the abstract sorts. -/
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

/-- The sort a type denotes, through its `ToTyp` instance. -/
abbrev ToTyp.srt [ToTyp α] : Env Srt := Typ.of α |>.toSrt

@[inherit_doc ToTyp.srt]
abbrev Srt.of (α : Type) [A : ToTyp α] : Env Srt := A.srt


/-- The usual order on rationals, which core lacks; at low priority, so that Mathlib's wins. -/
instance (priority := low) instOrdRat : Ord Rat := ⟨fun x y => compareOfLessAndEq x y⟩
-- Without it a real-valued set, bag or array index cannot be spelled, `Set` and friends wanting
-- their elements ordered.

namespace ToTyp

instance : ToTyp Bool := ⟨.bool⟩
instance : ToTyp Int := ⟨.int⟩
instance : ToTyp Rat := ⟨.real⟩
instance : ToTyp String := ⟨.string⟩
instance : ToTyp (BitVec size) := ⟨.bitVec size⟩
instance : ToTyp Cvc.Float.RoundingMode := ⟨.roundingMode⟩
/-- Lean's `Array` denotes cvc5's sequences; SMT-LIB arrays are `TotalMap`. -/
instance [A : ToTyp α] : ToTyp (Array α) := ⟨.seq A.typ⟩
/-- Lean's `Option` denotes cvc5's `Nullable`. -/
instance [A : ToTyp α] : ToTyp (Option α) := ⟨.nullable A.typ⟩

end ToTyp



/-- `α` denotes an arithmetic sort: `Int` or `Rat`. -/
class IsArith (α : Type) [A : ToTyp α] : Prop where
  /-- Proof that `α`'s `Typ` is arithmetic. -/
  valid_typ : A.typ.isArith := by simp [Typ.isArith, ToTyp.typ] <;> grind
-- A `Prop` whose field an autoparam discharges, so an instance is proved rather than declared;
-- `Typ.typs_of_isArith` lets a typed operator case-split on which sort it actually got. Likewise
-- `HasConcat`.

instance : IsArith Int := {}
instance : IsArith Rat := {}

/-- `α` denotes a sort with concatenation: `String` or `Array _`. -/
class HasConcat (α : Type) [A : ToTyp α] : Prop where
  /-- Proof that `α`'s `Typ` has concatenation. -/
  valid_typ : A.typ.hasConcat := by simp [Typ.hasConcat, ToTyp.typ] <;> grind

instance : HasConcat String := {}
instance [ToTyp α] : HasConcat (Array α) := {}



/-! ### Regular expressions -/

/-- The Lean type indexing regular-expression terms; it carries no data. -/
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



/-! ## A sort written either way

Where the sort-erased DSL lets a sort be written — a quantifier's binders, a grammar's
non-terminals and parameters, a record field's stated sort — it accepts **a Lean type or a `Srt`**
alike, through `srtOf%`.
-/
-- Which one was written is only known once the term is elaborated, `int` and `Int` both being
-- identifiers, so it takes an elaborator rather than a macro.

/-- `srtOf% e` is `Srt.of e` when `e` is a Lean type, and `pure e` when it is a `Srt`. -/
syntax (name := srtOfStx) "srtOf% " term:max : term

public meta section

open Lean Elab Term Meta in
/-- Elaborates `srtOf% e` by looking at what `e` turned out to be. -/
@[term_elab srtOfStx] def elabSrtOf : TermElab := fun stx expected? => do
  let `(srtOf% $e) := stx | throwUnsupportedSyntax
  let value ← withSynthesize <| elabTerm e none
  let type ← instantiateMVars (← inferType value)
  if (← whnfR type).isSort then
    elabTerm (← `(Cvc.Srt.of $e)) expected?
  else
    let srt ← elabType (← `(Cvc.Srt))
    unless ← isDefEq type srt do
      -- expansions parenthesize what they pass, which is not what the writer wrote
      let shown := if e.raw.isOfKind ``Lean.Parser.Term.paren then e.raw[1] else e.raw
      throwErrorAt e m!"expected a Lean type or a `Srt`, but `{shown}` has type{indentExpr type}"
    elabTerm (← `(pure ($e : Cvc.Srt))) expected?

end
