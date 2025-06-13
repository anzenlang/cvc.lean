/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Logic
import Cvc.Basic
import Cvc.Srt
import Cvc.Option



/-! # Functions and monads for term, term building, SMT *etc.* helpers and monads -/
namespace Cvc



/-- Type-safe cvc5 terms, input type expected to be `IsSrt` for most uses.

- No direct constructor exposed publicly, users must go through the `Term.Build` monadic
  constructors.
-/
structure Term (α : Type) where
/-- Constructor from an unsafe term. -/
private ofUnsafe ::
  /-- True if the term mentions symbols. -/
  hasSymbols : Bool
  /-- Underlying unsafe term. -/
  toUnsafe : cvc5.Term

/-- Abbreviation for a `Term Bool`. -/
abbrev Formula := Term Bool



namespace Term

/-- Boolean terms. -/
protected abbrev Bool := Term Bool
/-- Integer terms. -/
protected abbrev Int := Term Int
/-- Real/`Rat` terms. -/
protected abbrev Real := Term Rat
/-- String terms. -/
protected abbrev String := Term String
/-- Array terms. -/
protected abbrev Array (α β : Type) := Term (Cvc.TMap α β)
/-- Sequence terms. -/
protected abbrev Seq (α : Type) := Term (Array α)
/-- Function terms. -/
protected abbrev Fun (α β : Type) := Term (α → β)
/-- Product terms. -/
protected abbrev Prod (α β : Type) := Term (α × β)



section variable [A : IsSrt α] (term : Term α)

/-- Sort of some term.

> Note that due to strong-typing, this function does not perform any FFI.
-/
abbrev srt : (term : Term α) → Srt := 𝕂 A.srt

theorem srt_bij : α = term.srt := A.h_bij

/-- Re-types `t` in terms of the type of `t.srt`. -/
def retype : Term term.srt := term.srt_bij ▸ term

/-- Helper for dependent-pattern-matching the sort of a term. -/
def inspectSrt (f : (srt : Srt) → Term srt → β) : β :=
  f term.srt term.retype

end



/-- Monadic constructor from an unsafe term. -/
private def ofUnsafeM [Monad m] [IsSrt α] (hasSymbols : Bool) : m cvc5.Term → m (Term α) :=
  (Term.ofUnsafe hasSymbols <$> ·)

/-- SMT-LIB string representation. -/
def toSmtString (term : Term α) : String :=
  term.toUnsafe.toString

instance : ToString (Term α) := ⟨Term.toSmtString⟩



/-! ## Term building -/
open cvc5 renaming TermManager → Manager

/-- State of the term builder monad. -/
structure Build.State where
/-- Constructor from a term manager. -/
mk' ::
  /-- Term manager. -/
  manager : Manager
  /-- Logic builder, used to track the logic necessary to express the terms actually built.

  Updated when building terms.
  -/
  logic : Logic.Builder := Logic.Builder.mk

namespace Build.State

@[inherit_doc Build.State.mk']
def ofManager (manager : Manager) (logic : Logic.Builder := Logic.Builder.mk) : Build.State :=
  ⟨manager, logic⟩

/-- Creates a new term builder state. -/
def mk : BaseIO Build.State :=
  ofManager <$> cvc5.TermManager.new


end Build.State



/-- Term-building error-state-monad transformer. -/
abbrev BuildT (m : Type → Type u) :=
  ExceptT Error (StateT Build.State m)

/-- Term-building error-state-monad in `IO`. -/
abbrev BuildIO := BuildT IO

/-- Plain term-building error-state-monad. -/
abbrev Build := BuildT Id

namespace BuildT

instance : MonadLift (Except cvc5.Error) Build where
  monadLift code tm := do
    match ← code with
    | .ok res => return (.ok res, tm)
    | .error error => return (.error <| Error.ofCvc5 error, tm)

instance [Monad m] : MonadLift Build (BuildT m) :=
  ⟨fun code state => return code state⟩

instance [Monad m] [MonadLiftT IO m] : MonadLift BuildIO (BuildT m) :=
  ⟨fun code state => return ← code state⟩

/-- Runs term-building code with a specific build state. -/
def runWith' (build : BuildT m α) (state : Build.State) : m (Except Error α × Build.State) :=
  build state

section variable [Monad m]

@[inherit_doc runWith']
def runWith (build : BuildT m α) (state : Build.State) : m (Except Error α) :=
  Prod.fst <$> build.runWith' state

section variable [MonadLiftT BaseIO m]

/-- Runs term-building code, creates an initial build state if none is provided. -/
def run' [MonadLiftT BaseIO m]
  (build : BuildT m α) (state? : Option Build.State := none)
: m (Except Error α × Build.State) := do
  let state ← if let some state := state? then pure state else Build.State.mk
  build state

@[inherit_doc run']
def run [MonadLiftT BaseIO m]
  (build : BuildT m α) (state? : Option Build.State := none)
: m (Except Error α) :=
  Prod.fst <$> build.run' state?

end

end

/-- Runs term-building code in `IO`, creates an initial build state if none is provided -/
def runIO'
  (build : BuildIO α) (state? : Option Build.State := none)
: IO (α × Build.State) := do
  let (a?, state) ← build.run' state?
  match a? with
  | .ok a => return (a, state)
  | .error error =>
    IO.eprintln s!"{error}"
    throw <| IO.Error.userError error.toString

@[inherit_doc runIO']
def runIO (build : BuildIO α) (state? : Option Build.State := none) : IO α :=
  Prod.fst <$> build.runIO' state?

end BuildT

-- export `BuildT.<run>` runners to `Build.<run>`
namespace Build
export BuildT (runWith' runWith run' run runIO' runIO)
end Build

-- also export `Term.BuildT.<run>`/`Term.Build.<run>` runners to `Term.<run>`
export Build (runWith' runWith run' run runIO' runIO)




/-- Applies a monadic function to the term manager part of the `Build.State`. -/
private def managerDoM [Monad m] [MonadLiftT m Build] (f : Manager → m γ) : Build γ := do
  let state ← get
  f state.manager

/-- Applies a function to the term manager part of the `Build.State`. -/
private def managerDo (f : Manager → γ) : Build γ :=
  managerDoM (m := Id) f

/-- Applies a function to the `Logic.Builder` part of the `Build.State`. -/
private def logicDo (f : Logic.Builder → Logic.Builder) : Build Unit :=
  fun state =>
    let logic := f state.logic
    return (.ok (), {state with logic})

end Term



namespace Srt


/-- Conversion to unsafe sorts.

- function sorts are flattened:\
  `srt → srt' → srt'' → nonFunSrt` becomes `#[srt, srt', srt''] → nonFunSrt`
-/
def toSort (srt : Srt) : Term.Build cvc5.Sort :=
  Term.managerDoM fun tm => aux tm srt 10_000
where
  aux (tm : cvc5.TermManager) (srt' : Srt) : (maxRec : Nat) → Term.Build cvc5.Sort
    | 0 => Cvc.throwInternal s!"[Srt.toSort] maximum depth reached on `{srt}`"
    | maxRec + 1 =>
      match srt' with
      | .bool => pure tm.getBooleanSort
      | .int => pure tm.getIntegerSort
      | .real => pure tm.getRealSort
      | .regex => pure tm.getRegExpSort
      | .string => pure tm.getStringSort
      | .roundingMode => pure tm.getRoundingModeSort
      | .finiteField size => tm.mkFiniteFieldSort size
      | .bitVec size => tm.mkBitVectorSort size
      | .float exp sig => tm.mkFloatingPointSort exp sig
      | .uninterpreted name => pure <| tm.mkUninterpretedSort name
      | .bag elm => do tm.mkBagSort (← aux tm elm maxRec)
      | .seq elm => do tm.mkSequenceSort (← aux tm elm maxRec)
      | .set elm => do tm.mkSetSort (← aux tm elm maxRec)
      | .array idx elm => do tm.mkArraySort (← aux tm idx maxRec) (← aux tm elm maxRec)
      | .function dom cod => do
        let (doms, cod) ← flattenFun tm maxRec #[← aux tm dom maxRec] cod
        tm.mkFunctionSort doms cod
      | .prod lft rgt => do tm.mkTupleSort #[← aux tm lft maxRec, ← aux tm rgt maxRec]
      | .unit => tm.mkTupleSort #[]
      | .abstract _k => Cvc.throwInternal s!"[Srt.toSort] todo `{srt'}`"
  flattenFun (tm : cvc5.TermManager) (maxRec : Nat)
    (doms : Array cvc5.Sort)
  : (cod : Srt) → Term.Build (Array cvc5.Sort × cvc5.Sort)
    | .function dom cod => do
      let dom ← aux tm dom maxRec
      flattenFun tm maxRec (doms.push dom) cod
    | cod => return (doms, (← aux tm cod maxRec))

/-- Retrieves the domain and codomain of `srt` for `declareFun`-like functions.

This function uncurries `α → β → ... → γ` to `#[α, β, ...] → γ`.
-/
private def toSignature! (srt : Srt) : Term.Build (Array cvc5.Sort × cvc5.Sort) :=
  Term.managerDoM (toSort.flattenFun srt · 10_000 #[] srt)

end Srt



/-! ## Term creation API -/
namespace Term

/-- Unsafe term creation. -/
private def mk [IsSrt α]
  (hasSymbols : Bool) (k : cvc5.Kind) (args : Array cvc5.Term)
: Build (Term α) :=
  managerDoM fun tm => ofUnsafe hasSymbols <$> tm.mkTerm k args



/-- Builds a constant Boolean term. -/
def bool (b : Bool) : Build Term.Bool :=
  managerDo fun tm => tm.mkBoolean b |> Term.ofUnsafe false

/-- Retrieves the value of a constant Boolean term. -/
def boolVal? (t : Term.Bool) : Option Bool :=
  t.toUnsafe.getBooleanValue?

@[inherit_doc boolVal?]
def boolVal (t : Term.Bool) : Res Bool :=
  if let some t := t.boolVal?
  then return t
  else
    Res.failUser "cannot retrieve Boolean value of a non-constant term"
    |>.context s!"on term `{t}`"

/-- Builds a constant integer term. -/
def int (i : Int) : Build Term.Int := do
  logicDo .int
  managerDo fun tm => tm.mkInteger i |> Term.ofUnsafe false

/-- Retrieves the value of a constant integer term. -/
def intVal? (t : Term.Int) : Option Int :=
  t.toUnsafe.getIntegerValue?

@[inherit_doc intVal?]
def intVal (t : Term.Int) : Res Int :=
  if let some t := t.intVal?
  then return t
  else
    Res.failUser "cannot retrieve integer value of a non-constant term"
    |>.context s!"on term `{t}`"

/-- Retrieves the value of a constant rational/real term. -/
def ratVal? (t : Term.Real) : Res (Option Rat) :=
  t.toUnsafe.getRationalValue?.mapM fun r =>
    if h : r.den ≠ 0 then return Rat.normalize r.num r.den h
    else Res.failInternal s!"cvc5 produced an illegal ration value: `{r}`"

@[inherit_doc ratVal?]
def ratVal (t : Term.Real) : Res Rat := do
  if let some r ← t.ratVal? then return r else
    Res.failUser "cannot retrieve rational value of a non-constant term"
    |>.context s!"on term `{t}`"

-- /-- Retrieves the value of a constant rational/real term. -/
-- def stringVal? (t : Term.String) : Option String :=
--   t.toUnsafe.getStringValue?

-- @[inherit_doc stringVal?]
-- def stringVal (t : Term.String) : Res String := do
--   if let some r ← t.stringVal? then return r else
--     Res.failUser "cannot retrieve string value of a non-constant term"
--     |>.context s!"on term `{t}`"

/-- Builds the Boolean negation of a term. -/
def mkNot (term : Term.Bool) : Build Term.Bool :=
  mk term.hasSymbols .NOT #[term.toUnsafe]

@[inherit_doc mkNot]
def not := mkNot

/-- Builds an if-then-else term. -/
def ite [IsSrt α] (cnd : Term.Bool) (thn els : Term α) : Build (Term α) :=
  mk (cnd.hasSymbols ∨ thn.hasSymbols ∨ els.hasSymbols)
    .ITE #[cnd.toUnsafe, thn.toUnsafe, els.toUnsafe]



/-! ### `n`-ary operators (`2 ≤ n`) -/
section nary2
variable [A : IsSrt α] (terms : Array (Term α)) (lft rgt : Term α)
variable (h_size : 2 ≤ terms.size := by
  (try (try simp <;> try omega) ; done)
  <;> fail "expected an array of **at least** two terms"
)

/-- Builds an equality term. -/
def mkEqual : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .EQUAL (terms.map toUnsafe)

@[inherit_doc mkEqual]
def equal : Build Formula :=
  mkEqual #[lft, rgt]

/-- Builds a conjunction term. -/
def mkAnd : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .AND (terms.map toUnsafe)

@[inherit_doc mkAnd]
def and : Build Formula :=
  mkAnd #[lft, rgt]

-- def iand (k : Nat) (i j : Term Int) : Build Formula := do
--   sorry

/-- Builds a disjunction term. -/
def mkOr : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .OR (terms.map toUnsafe)

@[inherit_doc mkOr]
def or : Build Formula :=
  mkOr #[lft, rgt]

/-- Builds an exclusive-disjunction term. -/
def mkXor : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .XOR (terms.map toUnsafe)

@[inherit_doc mkXor]
def xor : Build Formula :=
  mkXor #[lft, rgt]

/-- Builds a disjunction term. -/
def mkImplies : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .IMPLIES (terms.map toUnsafe)

@[inherit_doc mkImplies]
def implies : Build Formula :=
  mkImplies #[lft, rgt]

/-- Builds a pairwise-*distinct* term. -/
def mkDistinct : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .DISTINCT (terms.map toUnsafe)

@[inherit_doc mkDistinct]
def distinct : Build Formula :=
  mkDistinct #[lft, rgt]

@[inherit_doc mkDistinct]
abbrev mkNEqual := @distinct
@[inherit_doc distinct]
abbrev nequal := @distinct

/-- Builds a less-than term. -/
def mkLt : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .LT (terms.map toUnsafe)

@[inherit_doc mkLt]
def lt : Build Formula :=
  mkLt #[lft, rgt]

/-- Builds a less-than-or-equal-to term. -/
def mkLe : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .LEQ (terms.map toUnsafe)

@[inherit_doc mkLe]
def le : Build Formula :=
  mkLe #[lft, rgt]

/-- Builds a greater-than-or-equal-to term. -/
def mkGe : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .GEQ (terms.map toUnsafe)

@[inherit_doc mkGe]
def ge : Build Formula :=
  mkGe #[lft, rgt]

/-- Builds a greater-than term. -/
def mkGt : Build Formula :=
  let _ := h_size
  mk (terms.any hasSymbols) .GT (terms.map toUnsafe)

@[inherit_doc mkGt]
def gt : Build Formula :=
  mkGt #[lft, rgt]

end nary2



/-! #### Arithmetic -/
section arith

variable [IsSrt α] (terms : Array (Term α)) (lft rgt : Term α)
variable (h_size : 2 ≤ terms.size := by
  (try (try simp <;> try omega) ; done)
  <;> fail "expected an array of **at least** two terms"
)
variable (Arith : IsSrt.Arith α := by
  (try ( exact inferInstance ) ; done)
  <;> fail "expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`"
)

/-- Forbids difference logics. -/
private def nonDiff : Build Unit := logicDo .nonDiff

/-- Forces non-linear logic if non-linear, true if one of the terms has symbols. -/
private def checkNonLinearOfArgs (terms : Array (Term α)) : Build Bool := do
  let mut hasSymbols := false
  let mut nonLinear := false
  for term in terms do
    if term.hasSymbols then
      if hasSymbols then
        nonLinear := true
        break
      else
        hasSymbols := true
  if nonLinear then
    logicDo (.nonLinear ∘ .nonDiff)
  return hasSymbols

/-- Builds an addition term.

- Forbids difference logics.
-/
def mkAdd : Build (Term α) := do
  nonDiff
  let _ := h_size ; let _ := Arith
  mk (terms.any hasSymbols) .ADD (terms.map toUnsafe)

@[inherit_doc mkAdd]
def add : Build (Term α) :=
  mkAdd #[lft, rgt]

/-- Builds a multiplication term.

- Forbids difference logic.
- Forces non-linear logic if non-linear.
-/
def mkMul : Build (Term α) := do
  let _ := h_size ; let _ := Arith
  nonDiff
  let hasSymbols ← checkNonLinearOfArgs terms
  mk hasSymbols .MULT (terms.map toUnsafe)

@[inherit_doc mkMul]
def mul : Build (Term α) := mkMul #[lft, rgt]

/-- Arithmetic division with division by `0` undefined, left associative.

- Forbids difference logic.
- Forces non-linear logic if non-linear.
-/
def mkDiv! : Build (Term α) := do
  let _ := h_size
  nonDiff
  let hasSymbols ← checkNonLinearOfArgs terms
  let terms := terms.map toUnsafe
  Arith.inspect
    (fInt := fun _ => mk hasSymbols .INTS_DIVISION terms)
    (fRat := fun _ => mk hasSymbols .DIVISION terms)

@[inherit_doc mkDiv!]
def div! : Build (Term α) := do
  mkDiv! #[lft, rgt]

/-- Arithmetic division with division by `0` defined to be `0`, left associative. -/
def mkDivTotal : Build (Term α) := do
  nonDiff
  let hasSymbols ← checkNonLinearOfArgs #[lft, rgt]
  let args := #[lft.toUnsafe, rgt.toUnsafe]
  Arith.inspect
    (fInt := fun _ => mk hasSymbols .INTS_DIVISION_TOTAL args)
    (fRat := fun _ => mk hasSymbols .DIVISION_TOTAL args)

@[inherit_doc mkDivTotal]
def divTotal : Build (Term α) := mkDivTotal lft rgt

end arith



/-! ### Function application -/
section apply

/-- Flattens higher-order applications. -/
private partial def flattenHoApply
  (revArgs : Array cvc5.Term) (functionTerm : cvc5.Term)
: Term.Build cvc5.Term := do
  match functionTerm.getKind with
  -- if `functionTerm` is a higher-order apply, deconstruct it
  | .HO_APPLY =>
    let args := functionTerm.getChildren
    if h : 0 < args.size then
      let functionTerm := args[0]
      let args := args.toSubarray (start := 1)
      let revArgs := revArgs |> args.foldr fun arg acc => acc.push arg
      flattenHoApply revArgs functionTerm
    else Cvc.throwInternal s!"cannot deconstruct `HO_APPLY` with no arguments"
  -- otherwise reconstruct a normal application
  | _ =>
    if revArgs.isEmpty
    then Cvc.throwInternal s!"unreachable: `flattenHoApply` with empty list of arguments"
    else
      let revArgs := revArgs.push functionTerm
      -- build the unsafe term
      managerDoM fun tm => tm.mkTerm cvc5.Kind.APPLY_UF revArgs.reverse

/-- Applies a function term to an argument.

## Partial applications and higher-order

This function supports partial applications: they are encoded as `cvc5.Kind.HO_APPLY` terms, which
**would** trigger errors if used in a solver without support for higher-order. Since support for
higher-order makes cvc5-level reasoning much more expensive, we want to avoid having `HO_APPLY`
terms as much as possible.

For this reason, this function detects when it is building an application that yields a non-function
term; in this case, it will destruct the underlying higher-order terms (recursively, and if any) and
rewrite them as a regular (first-order) function application.
-/
protected def apply [IsSrt β]
  (function : Term (α → β)) (arg : Term α)
: Term.Build (Term β) := do
  let hasSymbols := function.hasSymbols ∨ arg.hasSymbols
  let term! := function.toUnsafe
  let sort! := term!.getSort
  let dom ← sort!.getFunctionDomainSorts
  if 1 < dom.size
  then Term.mk hasSymbols .HO_APPLY #[function.toUnsafe, arg.toUnsafe]
  else ofUnsafe hasSymbols <$> flattenHoApply #[arg.toUnsafe] term!

end apply

end Term



/-- A term-value, as produced by `getValue`-like (SMT) function. -/
structure Value (α : Type) where
/-- Private constructor so that users can't compromise this type's semantics. -/
private ofTerm ::
  /-- Underlying term. -/
  toTerm : Term α

namespace Value

protected def toString (value : Value α) : String := toString value.toTerm

instance : ToString (Value α) := ⟨Value.toString⟩

/-- Boolean values. -/
protected abbrev Bool := Value Bool
/-- Integer values. -/
protected abbrev Int := Value Int
/-- Real/`Rat` values. -/
protected abbrev Real := Value Rat
/-- String values. -/
protected abbrev String := Value String
/-- Array values. -/
protected abbrev Array (α β : Type) := Value (Cvc.TMap α β)
/-- Sequence values. -/
protected abbrev Seq (α : Type) := Value (Array α)
/-- Function values. -/
protected abbrev Fun (α β : Type) := Value (α → β)
/-- Product values. -/
protected abbrev Prod (α β : Type) := Value (α × β)

section variable [A : IsSrt α] (value : Value α)

abbrev srt : (value : Value α) → Srt := 𝕂 A.srt

theorem srt_bij : α = value.srt := A.h_bij

def retype : Value value.srt := value.srt_bij ▸ value

def inspectSrt (f : (srt : Srt) → Value srt → β) : β :=
  f value.srt value.retype

end

def boolVal (value : Value.Bool) : Res Bool := value.toTerm.boolVal
def intVal (value : Value.Int) : Res Int := value.toTerm.intVal
def ratVal (value : Value.Real) : Res Rat := value.toTerm.ratVal

end Value



namespace Conv

class ValueToVal (m : Type → Type) (α : Type) extends IsSrt α where
mk' ::
  Val : Type
  ofValue : Value α → m Val

namespace ValueToVal

protected abbrev Id (α : Type) [IsSrt α] : ValueToVal Id α := ⟨Value α, id⟩

def mk [IsSrt α] (Val : Type) (ofValue : Value α → m Val) : ValueToVal m α :=
  ⟨Val, ofValue⟩

def mkId [IsSrt α] : ValueToVal Id α := ⟨Value α, id⟩

instance : CoeSort (ValueToVal m α) Type := ⟨fun conv => conv.Val⟩

abbrev adaptM [A : ValueToVal m α]
  (lift : {β : Type} → m β → m' β)
: ValueToVal m' α := ⟨A.Val, lift ∘ A.ofValue⟩

protected abbrev liftM [MonadLiftT m m'] [A : ValueToVal m α] : ValueToVal m' α :=
  A.adaptM liftM

instance defaultInstUnit : ValueToVal Id Unit := mk Unit fun _ => pure ()
instance defaultInstBool : ValueToVal Res Bool := mk Bool fun v => v.boolVal
instance : ToString defaultInstBool.Val := inferInstanceAs (ToString Bool)
instance defaultInstInt : ValueToVal Res Int := mk Int fun v => v.intVal
instance : ToString defaultInstInt.Val := inferInstanceAs (ToString Int)
instance defaultInstRat : ValueToVal Res Rat := mk Rat fun t => t.ratVal
instance : ToString defaultInstRat.Val := inferInstanceAs (ToString Rat)
instance defaultInstString : ValueToVal Id String := mkId
instance defaultInstRoundingMode : ValueToVal Id RoundingMode := mkId
instance defaultInstRegex : ValueToVal Id Cvc.Regex := mkId

instance defaultInstFloat : ValueToVal Id (Cvc.AnyFloat exp sig) := mkId
instance defaultInstAbstract : ValueToVal Id (Cvc.Abstract k) := mkId
instance defaultInstFiniteField : ValueToVal Id (Cvc.FiniteField n) := mkId
instance defaultInstBitVec : ValueToVal Id (BitVec size) := mkId
instance defaultInstUninterpreted : ValueToVal Id (Uninterpreted name) := mkId

section variable [IsSrt α] [IsSrt β]

instance defaultInstArray : ValueToVal Id (Array α) := mkId
instance defaultInstProd : ValueToVal Id (α × β) := mkId
instance defaultInstFun : ValueToVal Id (α → β) := mkId
instance defaultInstTMap : ValueToVal Id (Cvc.TMap α β) := mkId
instance defaultInstBag : ValueToVal Id (Cvc.Bag α) := mkId
instance defaultInstSet : ValueToVal Id (Cvc.Set α) := mkId

end

abbrev defaultFor : (srt : Srt) → ValueToVal Res srt
| .abstract _kind => defaultInstAbstract.adaptM .ok
| .array _idx _elm =>
  -- let (_, _) := (defaultFor idx, defaultFor elm)
  defaultInstTMap.adaptM .ok
| .bag _elm =>
  -- let _ := defaultFor elm
  defaultInstBag.adaptM .ok
| .bool => defaultInstBool
| .bitVec _n => defaultInstBitVec.adaptM .ok
| .finiteField _n => defaultInstFiniteField.adaptM .ok
| .float _exp _sig => defaultInstFloat.adaptM .ok
| .function _dom _cod =>
  -- let (_, _) := (defaultFor dom, defaultFor cod)
  defaultInstFun.adaptM .ok
| .int => defaultInstInt
| .prod _lft _rgt =>
  -- let (_, _) := (defaultFor lft, defaultFor rgt)
  defaultInstProd.adaptM .ok
| .real => defaultInstRat
| .regex => defaultInstRegex.adaptM .ok
| .roundingMode => defaultInstRoundingMode.adaptM .ok
| .seq _elm =>
  -- let _ := defaultFor elm
  defaultInstArray.adaptM .ok
| .set _elm =>
  -- let _ := defaultFor elm
  defaultInstSet.adaptM .ok
| .string => defaultInstString.adaptM .ok
| .unit => defaultInstUnit.adaptM .ok
| .uninterpreted _ => defaultInstUninterpreted.adaptM .ok

namespace Default

scoped instance (srt : Srt) : ValueToVal Res srt := defaultFor srt

end Default

end ValueToVal



class ValuesToVal (m : Type → Type) where
  instValueToVal : (srt : Srt) → ValueToVal m srt

namespace ValuesToVal

protected abbrev Values : ValuesToVal Id := ⟨(ValueToVal.Id ·)⟩

protected abbrev Default : ValuesToVal Res where
  instValueToVal := ValueToVal.defaultFor

end ValuesToVal

end Conv



/-! ## Conversion of *term-values* -/

class Srt.ToValType where
  Val : Srt → Type

def Srt.ToValType.Terms : ToValType where
  Val (srt : Srt) := Term srt

namespace Term

class ToVals extends toValConv : Srt.ToValType where
  build : (srt : Srt) → Term srt → Val srt

def ToVals.Terms : ToVals where
  toValConv := .Terms
  build := fun _ => id

-- def ToVals.Default : ToVals where

namespace ToVals

-- protected def Terms :

end ToVals

end Term



/-! ## `Smt` environment and functions -/

structure Smt.State where
  solver : cvc5.Solver
  builder : Term.Build.State
  private nextActlitIdx' : Nat

abbrev SmtT (m : Type → Type) :=
  ExceptT Error (StateT Smt.State m)

abbrev SmtIO := SmtT IO

abbrev Smt := SmtT Id

namespace Smt variable [Monad m]

instance : MonadLift m (SmtT m) := ⟨fun code state => return (.ok (← code), state)⟩

instance [Monad m] [Monad m'] [MonadLift m m'] : MonadLift (SmtT m) (SmtT m') :=
  ⟨fun code state => return ← code state⟩

instance [Monad m] : MonadLift Smt (SmtT m) :=
  ⟨fun code state => return code state⟩

instance [Monad m] [MonadLiftT IO m] : MonadLift SmtIO (SmtT m) :=
  ⟨fun code state => return ← code state⟩

instance [Monad m] : MonadLift Term.Build (SmtT m) where
  monadLift build := do
    let res ← modifyGet fun state =>
      let (res, builder) := build state.builder
      (res, {state with builder})
    res

def nextActlitIdx : Smt Nat :=
  modifyGetThe Smt.State fun state =>
    let idx := state.nextActlitIdx'
    (idx, {state with nextActlitIdx' := idx.succ})

private def lift5 [Monad m] (code : cvc5.SolverT m α) : SmtT m α := do
  let state ← getThe Smt.State
  let (res, solver) ← code state.solver
  set {state with solver}
  return ← res

/-- Sets an option in the solver. -/
def setOption (opt : Cvc.Option) : Smt Unit := do
  let (key, val) := opt.keyVal
  let state ← getThe Smt.State
  let (res, solver) ← cvc5.Solver.setOption key val state.solver
  let () ← res
  set {state with solver}


/-- Declares a function symbol. -/
def declare (symbol : String) (α : Type) [IsSrt α] : Smt (Term α) := do
  let srt := getSrt α
  let (doms, cod) ← srt.toSignature!
  let f ← lift5 <| cvc5.Solver.declareFun symbol doms cod
  return Term.ofUnsafe true f

@[inherit_doc declare]
def declare' {α : Type} [IsSrt α] (symbol : String) : Smt (Term α) :=
  declare symbol α

/-- Asserts a formula. -/
def assert (formula : Formula) : Smt Unit := do
  lift5 <| cvc5.Solver.assertFormula formula.toUnsafe

section variable (assuming : Option (Array Formula) := none)

/-- Checks the satisfiability of the formulas asserted with `Smt.assert`. -/
def checkSat : Smt CheckSat := do
  let res ←
    match assuming with
    | none | some #[] =>
      cvc5.Solver.checkSat |> lift5
    | some assuming =>
      assuming.map Term.toUnsafe |> cvc5.Solver.checkSatAssuming |> lift5
  pure <|
    if res.isSat then CheckSat.sat
    else if res.isUnsat then CheckSat.unsat
    else if res.isUnknown then CheckSat.unknown res.toString
    else CheckSat.other res.toString

/-- Simplified `Smt.checkSat`, returns true/false for sat/unsat, `none` for unknown/unexpected. -/
def checkSat? : Smt (Option Bool) :=
  CheckSat.isSat? <$> checkSat assuming

end




/-- Sat-mode state. -/
structure Sat.State extends Smt.State where
/-- Constructor. -/
private mk ::

/-- Unsat-mode state. -/
structure Unsat.State extends Smt.State where
/-- Constructor. -/
private mk ::

/-- Unknown-mode state. -/
structure Unknown.State extends Smt.State where
/-- Constructor. -/
private mk ::

/-- Sat-mode monad, allows running commands such as get-value.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev SatT (m : Type → Type u) :=
  ExceptT Error (StateT Sat.State m)

abbrev Sat := SatT (m := Id)

def Sat.unexpected : SatT m α :=
  Error.throwUser "unexpected sat result"

/-- Unsat-mode monad, allows running commands such as get-proof.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev UnsatT (m : Type → Type u) :=
  ExceptT Error (StateT Unsat.State m)

abbrev Unsat := UnsatT (m := Id)

def Unsat.unexpected : UnsatT m α :=
  Error.throwUser "unexpected unsat result"

/-- Unknown-mode monad, allows running unknown-mode-specific commands.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev UnknownT (m : Type → Type u) :=
  ExceptT Error (StateT Unknown.State m)

abbrev Unknown := UnknownT (m := Id)

def Unknown.unexpected : UnknownT m α :=
  Error.throwUser "unexpected unknown result"



/-- Performs a check-sat and runs sat/unsat/unknown-specific code. -/
def checkSatAnd
  (assuming : Option (Array Formula) := none)
  (ifSat : Smt.SatT m α := Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Unknown.unexpected)
: SmtT m α := do
  if let some isSat ← checkSat? assuming then
    let state ← getThe Smt.State
    if isSat then
      let (res, state) ← ifSat ⟨state⟩
      set state.toState
      return ← res
    else
      let (res, state) ← ifUnsat ⟨state⟩
      set state.toState
      return ← res
  else
    let state ← getThe Smt.State
    let (res, state) ← ifUnknown ⟨state⟩
    set state.toState
    return ← res

namespace Sat

instance [Monad m] : MonadLift Smt.Sat (Smt.SatT m) :=
  ⟨fun code state => return code state⟩
instance [Monad m] : MonadLift Term.Build (Smt.SatT m) := ⟨fun build => do
  let res ← modifyGet fun state =>
    let (res, builder) := build state.builder
    (res, {state with builder})
  res
⟩

/-- Unsafe solver monad lift. -/
private def lift5 (code : cvc5.SolverT m α) : SatT m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, {state with solver})

/-- Retrieves the value of a term in `Sat` mode.

This function is available the following namespaces: `Cvc.Term`, `Cvc.Smt`, and `Cvc.Smt.Sat`.
-/
def getValue (term : Term α) : Sat (Value α) := do
  let term! ← lift5 <| cvc5.Solver.getValue (m := Id) term.toUnsafe
  return Term.ofUnsafe false term! |> Value.ofTerm

/-- Retrieves the values of some terms of the same sort in `Sat` mode.

This function is available the following namespaces: `Cvc.Term`, `Cvc.Smt`, and `Cvc.Smt.Sat`.
-/
def getValues (terms : Array (Term α)) : Sat (Array (Term α × Value α)) := do
  let mut values := Array.mkEmpty terms.size
  for term in terms do
    let value ← getValue term
    values := values.push (term, value)
  return values

/-- Retrieves the *concrete `Val`ue* of a term in `Sat` mode. -/
def getValUsing [Monad m] [MonadLiftT m Sat]
  (Val : Conv.ValueToVal m α) (term : Term α)
: Sat Val :=
  getValue term >>= liftM ∘ Val.ofValue

@[inherit_doc getValUsing]
def getVal [Monad m] [MonadLiftT m Sat] [Val : Conv.ValueToVal m α] (term : Term α) : Sat Val :=
  getValUsing Val term

/-- Retrieves the *concrete values* of some terms of the same sort in `Sat` mode. -/
def getValsUsing (Val : Conv.ValueToVal Sat α) (terms : Array (Term α))
: Sat (Array (Term α × Val)) := do
  let mut values := Array.mkEmpty terms.size
  for term in terms do
    let value ← getVal term
    values := values.push (term, value)
  return values

@[inherit_doc getValsUsing]
def getVals [Val : Conv.ValueToVal Sat α] (terms : Array (Term α)) : Sat (Array (Term α × Val)) :=
  getValsUsing Val terms

end Sat

export Sat (getValue getValues getValUsing getValsUsing getVal getVals)



namespace Unsat

instance [Monad m] : MonadLift Smt.Unsat (Smt.UnsatT m) :=
  ⟨fun code state => return code state⟩
instance [Monad m] : MonadLift Term.Build (Smt.UnsatT m) := ⟨fun build => do
  let res ← modifyGet fun state =>
    let (res, builder) := build state.builder
    (res, {state with builder})
  res
⟩

/-- Unsafe solver monad lift. -/
private def lift5 (code : cvc5.SolverT m α) : UnsatT m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, {state with solver})

/-- Retrieves the unsat-proofs in `Unsat` mode. -/
def getProof : Unsat (Array cvc5.Proof) := do
  lift5 <| cvc5.Solver.getProof

end Unsat

export Unsat (getProof)



namespace Unknown

instance [Monad m] : MonadLift Smt.Unknown (Smt.UnknownT m) :=
  ⟨fun code state => return code state⟩
instance [Monad m] : MonadLift Term.Build (Smt.UnknownT m) := ⟨fun build => do
  let res ← modifyGet fun state =>
    let (res, builder) := build state.builder
    (res, {state with builder})
  res
⟩

/-- Unsafe solver monad lift. -/
private def lift5 (code : cvc5.SolverT m α) : UnknownT m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, {state with solver})

end Unknown

end Smt



namespace Term

export Smt (getValue getValues getVal getValUsing getVals getValsUsing)

namespace ToVal
export Term (getVal getValUsing getVals getValsUsing)
end ToVal

/-- Returns the symbol of a symbol-term. -/
def getSymbol? (term : Term α) : Option String :=
  term.toUnsafe.getSymbol?

end Term



namespace SmtT variable [M : Monad m]

def runWith' (smt : SmtT m α) (state : Smt.State) : m (Except Error α × Smt.State) :=
  smt state

def runWith (smt : SmtT m α) (state : Smt.State) : m (Except Error α) :=
  Prod.fst <$> smt.runWith' state

def run' [MonadLiftT BaseIO m]
  (smt : SmtT m α) (state? : Option Smt.State := none)
: m (Except Error (α × Smt.State)) := do
  if let some state := state? then
    let (res, state) ← smt.runWith' state
    return res.map (·, state)
  else
    let tm ← cvc5.TermManager.new
    let builder := Term.Build.State.ofManager tm
    let res ← cvc5.Solver.run builder.manager fun solver => do
      let (res, state) ← smt ⟨solver, builder, 0⟩
      return (.ok (res, state), solver)
    match res with
    | .ok (.ok res, state) => return .ok (res, state)
    | .ok (.error err, _) => return .error err
    | .error err => return .error <| Error.ofCvc5 err

abbrev run [MonadLiftT BaseIO m]
  (smt : SmtT m α) (state? : Option Smt.State := none)
: m (Except Error α) := do
  Except.map Prod.fst <$> smt.run' state?

def runIO' (smt : SmtIO α) (state? : Option Smt.State := none) : IO (α × Smt.State) := do
  match ← smt.run' state? with
  | .ok res => return res
  | .error err =>
    IO.eprintln s!"{err}"
    throw <| IO.Error.userError err.toString

def runIO (smt : SmtIO α) (state? : Option Smt.State := none) : IO α :=
  Prod.fst <$> smt.runIO' state?

def runWithBuilder'
  (smt : SmtT m α) (builder : Term.Build.State)
: m (Except Error (α × Smt.State)) := do
  let res ← cvc5.Solver.run builder.manager fun solver => do
    let (res, state) ← smt.runWith' ⟨solver, builder, 0⟩
    return (.ok (res.map (·, state)), state.solver)
  match res with
  | .ok (.ok (res, state)) => return .ok (res, state)
  | .ok (.error err) => return .error err
  | .error err => return .error <| Error.ofCvc5 err

def runWithBuilder (smt : SmtT m α) (builder : Term.Build.State) : m (Except Error α) :=
  Except.map Prod.fst <$> smt.runWithBuilder' builder

end SmtT

namespace Smt
export SmtT (runWith' runWith run' run runIO' runIO runWithBuilder' runWithBuilder)
end Smt
