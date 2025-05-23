/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Logic
import Cvc.Basic
import Cvc.Srt



namespace Cvc



/-- Type-safe cvc5 terms, input type expected to be `Srt.Bij` for most uses.

For the type-erased version, see `ETerm`.
-/
structure Term (α : Type) where
/-- **[private]** Constructor from an unsafe term. -/
private ofUnsafe ::
  /-- True if the term mentions symbols. -/
  hasSymbols : Bool
  /-- Underlying unsafe term. -/
  toUnsafe : cvc5.Term

/-- Type-erased version `Term`. -/
structure ETerm where
/-- Constructor from a typed-term. -/
ofTerm ::
  /-- Type of the underlying typed-term. -/
  {α : Type}
  /-- Typed version of a type-erased term. -/
  typed : Term α

/-- Abbreviation for a `Term Bool`. -/
abbrev Formula := Term Bool

namespace Term

/-- Erases the type of a typed term. -/
def erase : Term α → ETerm := .ofTerm

/-- Boolean terms. -/
protected abbrev Bool := Term Bool
/-- Integer terms. -/
protected abbrev Int := Term Int
/-- Real/`Rat` terms. -/
protected abbrev Real := Term Rat
/-- Array terms. -/
protected abbrev Array (α β : Type) := Term (Cvc.TMap α β)
/-- Sequence terms. -/
protected abbrev Seq (α : Type) := Term (Array α)
/-- Function terms. -/
protected abbrev Fun (α β : Type) := Term (α → β)
/-- Product terms. -/
protected abbrev Prod (α β : Type) := Term (α × β)



section variable [A : Srt.Bij α] (t : Term α)

/-- Sort of some term.

> Note that due to strong-typing, this function does not perform any FFI.
-/
abbrev srt : (t : Term α) → Srt := fun _ => A.srt

theorem srt_bij : (t : Term α) → α = t.srt.toType := fun _ => A.h_bij

/-- Re-types `t` in terms of the type of `t.srt`. -/
def retype (t : Term α) : Term t.srt.toType :=
  t.srt_bij ▸ t

/-- Helper for dependent-pattern-matching the sort of a term. -/
def inspectType (t : Term α) (f : (srt : Srt) → Term srt.toType → β) : β :=
  f t.srt t.retype

end



/-- **[private]** Monadic constructor from an unsafe term. -/
private def ofUnsafeM [Monad m] [Srt.Bij α] (hasSymbols : Bool) : m cvc5.Term → m (Term α) :=
  (Term.ofUnsafe hasSymbols <$> ·)

/-- SMT-LIB string representation. -/
def toSmtString (term : Term α) : String :=
  term.toUnsafe.toString

instance : ToString (Term α) := ⟨Term.toSmtString⟩



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

def runWith' (build : BuildT m α) (state : Build.State) : m (Except Error α × Build.State) :=
  build state

section variable [Monad m]

def runWith (build : BuildT m α) (state : Build.State) : m (Except Error α) :=
  Prod.fst <$> build.runWith' state

section variable [MonadLiftT BaseIO m]

def run' [MonadLiftT BaseIO m]
  (build : BuildT m α) (state? : Option Build.State := none)
: m (Except Error α × Build.State) := do
  let state ← if let some state := state? then pure state else Build.State.mk
  build state

def run [MonadLiftT BaseIO m]
  (build : BuildT m α) (state? : Option Build.State := none)
: m (Except Error α) :=
  Prod.fst <$> build.run' state?

end

end

def runIO'
  (build : BuildIO α) (state? : Option Build.State := none)
: IO (α × Build.State) := do
  let (a?, state) ← build.run' state?
  match a? with
  | .ok a => return (a, state)
  | .error error =>
    IO.eprintln s!"{error}"
    throw <| IO.Error.userError error.toString

def runIO (build : BuildIO α) (state? : Option Build.State := none) : IO α :=
  Prod.fst <$> build.runIO' state?

end BuildT

namespace Build
export BuildT (runWith' runWith run' run runIO' runIO)
end Build

export Build (runWith' runWith run' run runIO' runIO)




/-- **[private]** Applies a monadic function to the term manager part of the `Build.State`. -/
private def managerDoM [Monad m] [MonadLiftT m Build] (f : Manager → m γ) : Build γ := do
  let state ← get
  f state.manager

/-- **[private]** Applies a function to the term manager part of the `Build.State`. -/
private def managerDo (f : Manager → γ) : Build γ :=
  managerDoM (m := Id) f

/-- **[private]** Applies a function to the `Logic.Builder` part of the `Build.State`. -/
private def logicDo (f : Logic.Builder → Logic.Builder) : Build Unit :=
  fun state =>
    let logic := f state.logic
    return (.ok (), {state with logic})

end Term



namespace Srt


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
      | .uninterpreted cons => pure <| tm.mkUninterpretedSort cons.toString
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

private def toSignature! (srt : Srt) : Term.Build (Array cvc5.Sort × cvc5.Sort) :=
  Term.managerDoM (toSort.flattenFun srt · 10_000 #[] srt)

end Srt



namespace Term

/-- **[private]** Unsafe term creation. -/
private def mk
  (hasSymbols : Bool) (k : cvc5.Kind) (args : Array cvc5.Term)
: Build (Term α) :=
  managerDoM fun tm => ofUnsafe hasSymbols <$> tm.mkTerm k args



/-- Builds a constant Boolean term. -/
def bool (b : Bool) : Build Term.Bool :=
  managerDo fun tm => tm.mkBoolean b |> Term.ofUnsafe false

/-- Builds a constant integer term. -/
def int (i : Int) : Build Term.Int := do
  logicDo .int
  managerDo fun tm => tm.mkInteger i |> Term.ofUnsafe false

/-- Builds the Boolean negation of a term. -/
def mkNot (term : Term.Bool) : Build Term.Bool :=
  mk term.hasSymbols .NOT #[term.toUnsafe]

@[inherit_doc mkNot]
def not := mkNot

/-- Builds an if-then-else term. -/
def ite (cnd : Term.Bool) (thn els : Term α) : Build (Term α) :=
  mk (cnd.hasSymbols ∨ thn.hasSymbols ∨ els.hasSymbols)
    .ITE #[cnd.toUnsafe, thn.toUnsafe, els.toUnsafe]

section nary2
variable [A : Srt.Bij α] (terms : Array (Term α)) (lft rgt : Term α)
variable (h_size : 2 ≤ terms.size := by
  (try (try simp <;> try omega) ; done)
  <;> fail "expected an array of **at least** two terms"
)
variable (h_arith : Cvc.is_arith α := by
  (try simp [Cvc.is_arith, Cvc.Srt.is_arith, *] ; done)
  <;> fail
    "expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.Srt.Bij.Arith`"
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

/-- Builds an addition term.

- Forbids difference logic.
-/
def mkAdd : Build (Term α) := do
  let _ := h_size ; let _ := h_arith
  logicDo .nonDiff
  mk (terms.any hasSymbols) .ADD (terms.map toUnsafe)

@[inherit_doc mkAdd]
def add : Build (Term α) :=
  mkAdd #[lft, rgt]

/-- Builds a multiplication term.

- Forbids difference logic.
- Forces non-linear logic if non-linear.
-/
def mkMul : Build (Term α) := do
  let _ := h_size ; let _ := h_arith
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
  mk hasSymbols .MULT (terms.map toUnsafe)

@[inherit_doc mkMul]
def mul : Build (Term α) :=
  mkMul #[lft, rgt]

end nary2



section apply

/-- **[private]** Flattens higher-order applications. -/
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
protected def apply (function : Term (α → β)) (arg : Term α) : Term.Build (Term β) := do
  let hasSymbols := function.hasSymbols ∨ arg.hasSymbols
  let term! := function.toUnsafe
  let sort! := term!.getSort
  let dom ← sort!.getFunctionDomainSorts
  if 1 < dom.size
  then Term.mk hasSymbols .HO_APPLY #[function.toUnsafe, arg.toUnsafe]
  else ofUnsafe hasSymbols <$> flattenHoApply #[arg.toUnsafe] term!

end apply

end Term



structure Smt.State where
  solver : cvc5.Solver
  builder : Term.Build.State

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

private def lift5 [Monad m] (code : cvc5.SolverT m α) : SmtT m α := do
  let state ← getThe Smt.State
  let (res, solver) ← code state.solver
  set {state with solver}
  return ← res

/-- Declares a function symbol. -/
def declare (symbol : String) (α : Type) [Srt.Bij α] : Smt (Term α) := do
  let srt := getSrt α
  let (doms, cod) ← srt.toSignature!
  let f ← lift5 <| cvc5.Solver.declareFun symbol doms cod
  return Term.ofUnsafe true f

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
/-- **[private]** Constructor. -/
private mk ::

/-- Unsat-mode state. -/
structure Unsat.State extends Smt.State where
/-- **[private]** Constructor. -/
private mk ::

/-- Unknown-mode state. -/
structure Unknown.State extends Smt.State where
/-- **[private]** Constructor. -/
private mk ::

/-- Sat-mode monad, allows running commands such as get-value.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev SatT (m : Type → Type u) :=
  ExceptT Error (StateT Sat.State m)

abbrev Sat := SatT (m := Id)

/-- Unsat-mode monad, allows running commands such as get-proof.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev UnsatT (m : Type → Type u) :=
  ExceptT Error (StateT Unsat.State m)

abbrev Unsat := UnsatT (m := Id)

/-- Unknown-mode monad, allows running unknown-mode-specific commands.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev UnknownT (m : Type → Type u) :=
  ExceptT Error (StateT Unknown.State m)

abbrev Unknown := UnknownT (m := Id)



/-- Performs a check-sat and runs sat/unsat/unknown-specific code. -/
def checkSatAnd
  (assuming : Option (Array Formula) := none)
  (ifSat : Smt.SatT m α := Error.throwUser "unexpected sat result")
  (ifUnsat : Smt.UnsatT m α := Error.throwUser "unexpected unsat result")
  (ifUnknown : Smt.UnknownT m α := Error.throwUser "unexpected unknown result")
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

/-- **[private]** Unsafe solver monad lift. -/
private def lift5 (code : cvc5.SolverT m α) : SatT m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, {state with solver})

/-- Retrieves the value of a term in `Sat` mode. -/
def getValue (term : Term α) : Sat (Term α) := do
  let term! ← lift5 <| cvc5.Solver.getValue (m := Id) term.toUnsafe
  return Term.ofUnsafe false term!

/-- Retrieves the values of some terms of the same sort in `Sat` mode. -/
def getValues (terms : Array (Term α)) : Sat (Array (Term α × Term α)) := do
  let mut values := Array.mkEmpty terms.size
  for term in terms do
    let value ← getValue term
    values := values.push (term, value)
  return values

end Sat



namespace Unsat

/-- **[private]** Unsafe solver monad lift. -/
private def lift5 (code : cvc5.SolverT m α) : UnsatT m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, {state with solver})

/-- Retrieves the unsat-proofs in `Unsat` mode. -/
def getProof : Unsat (Array cvc5.Proof) := do
  lift5 <| cvc5.Solver.getProof

end Unsat



namespace Unknown

/-- **[private]** Unsafe solver monad lift. -/
private def lift5 (code : cvc5.SolverT m α) : UnknownT m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, {state with solver})

end Unknown

end Smt



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
      let (res, state) ← smt ⟨solver, builder⟩
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
    let (res, state) ← smt.runWith' ⟨solver, builder⟩
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
