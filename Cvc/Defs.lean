/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init
import Cvc.Srt



namespace Cvc

/-- Strongly-typed term.

This is just a wrapper around an unsafe term (`cvc5.Term`).

- Constructor is private for type-safety reasons.
- Accessor is public as this does not impact type-safety.
-/
inductive Term {γ : Type u} : γ → Type u
/-- **[private]** Constructor from an unsafe term.

Private as this would allow user creating term of any `Srt`/`Type`

- `toUnsafe`: raw cvc5 term.
- `hasSymbols`: experimental, **only really valid in the `Term.Build` monad**, indicates whether the
  term is known to mention symbols. Once we're in the `Smt` monad, we would need to check terms
  created by the solver.

  Currently, one can trigger logic-unsafety by
  - running `Smt` code in a non-linear logic,
  - having the solver generate a non-linear term `t`,
  - exit `Smt` returning `t`,
  - running `Smt` code in a linear logic,
  - using `t`.
-/
| private ofUnsafe {a : γ} (hasSymbols : Bool) (toUnsafe : cvc5.Term) : Term a

/-- Abbreviation for a formula (`Srt.bool`) term. -/
abbrev Formula := Term Srt.bool

abbrev Term0 := Term (γ := Srt)

abbrev Term1 := Term (γ := Type)

-- with this version of `Term` we can pass `Srt` values and types
namespace Test

/-- info: Term Srt.bool : Type -/
#guard_msgs in #check Term Srt.bool
/-- info: Term0 Srt.bool : Type -/
#guard_msgs in #check Term0 Srt.bool

/-- info: Term Bool : Type 1 -/
#guard_msgs in #check Term Bool
/-- info: Term1 Bool : Type 1 -/
#guard_msgs in #check Term1 Bool

end Test



namespace Term

/-- **[private]** Monadic term constructor. -/
def ofUnsafeM [Monad m] : m cvc5.Term → m (Term α) :=
  (Term.ofUnsafe false <$> ·)

protected
def srt {srt : Srt} : Term srt → Srt :=
  fun _ => srt

/-- Unsafe term accessor. -/
def toUnsafe : Term α → cvc5.Term
| Term.ofUnsafe _ term => term

/-- Experimental, **only really valid in the `Term.Build` monad**, indicates whether the term is
known to mention symbols. Once we're in the `Smt` monad, we would need to check terms created by the
solver.

Currently, one can trigger logic-unsafety by
- running `Smt` code in a non-linear logic,
- having the solver generate a non-linear term `t`,
- exit `Smt` returning `t`,
- running `Smt` code in a linear logic,
- using `t`.
-/
private
def hasSymbols : Term α → Bool
| Term.ofUnsafe hs _ => hs

/-- Turns a `Term0` into a `Term1`. -/
def liftWith (Driver : Type) [I : Srt.ToType Driver] : Term srt → Term (I.srtToType srt)
| Term.ofUnsafe hs term => Term.ofUnsafe hs term

@[inherit_doc liftWith]
def lift {Driver} [I : Srt.ToType Driver] (term : Term srt) : Term (I.srtToType srt) :=
  liftWith Driver term

/-- Turns a `Term1` into a `Term0`. -/
def asSrt [ToSrt α] : Term α → Term (Srt.ofType α)
| Term.ofUnsafe hs term => Term.ofUnsafe hs term

/-- Facilitates pattern-matching on the `Srt` of a `Term1`. -/
def inspectSrt [ToSrt α] (t : Term α) (f : (srt : Srt) → Term srt → γ) : γ :=
  let t := t.asSrt
  f t.srt t

/-- SMT-LIB string representation. -/
protected
def toSmtString : Term α → String
| Term.ofUnsafe _ t => t.toString

instance : ToString (Term α) := ⟨Term.toSmtString⟩



section abbrevs

protected
abbrev Bool := Term0 .bool

protected
abbrev Int := Term0 .int

protected
abbrev Abstract (kind : Srt.Kind) := Term0 (.abstract kind)

protected
abbrev Array (idx elm : Srt) := Term0 (.array idx elm)

end abbrevs


open cvc5 renaming TermManager → Tm



/-- Term builder state. -/
structure Build.State where
  /-- The term manager. -/
  private tm : Tm
  /-- The logic. -/
  private logic : Logic.Builder

/-- Cvc term builder transformer monad. -/
abbrev Build :=
  ExceptT Error (StateM Build.State)

instance : MonadLift (Except cvc5.Error) Build where
  monadLift code tm := do
    match ← code with
    | .ok res => return (.ok res, tm)
    | .error e => return (.error <| Error.ofCvc5 e, tm)

/-- **[private]** Type-unsafe term constructor. -/
private
def mkTerm (hasSymbols : Bool) (k : cvc5.Kind) (args : Array cvc5.Term) : Build (Term0 srt) := do
  let state ← get
  let uTerm ← state.tm.mkTerm k args
  -- no `set`, just `state.tm` side-effects
  return Term.ofUnsafe hasSymbols uTerm

private
def tmDoM [Monad m] [MonadLiftT m Build] (f : Tm → m γ) : Build γ :=
  get >>= liftM ∘ f ∘ Build.State.tm

private
def tmDo (f : Tm → γ) : Build γ := tmDoM (m := Id) f

private
def logicDo (f : Logic.Builder → Logic.Builder) : Build Unit := fun state =>
  let logic := f state.logic
  return (.ok (), {state with logic})

end Term



namespace Term variable {α : Srt}

/-- Boolean constant constructor. -/
protected
def bool (b : Bool) : Build Formula :=
  tmDo (fun tm => tm.mkBoolean b |> Term.ofUnsafe false)

/-- Integer constant constructor. -/
protected
def int (i : Int) : Build Term.Int := do
  logicDo .int
  tmDo (· |>.mkInteger i |> Term.ofUnsafe false)

/-- If-then-else constructor. -/
def ite (cnd : Formula) (thn els : Term α) : Build (Term α) :=
  mkTerm (cnd.hasSymbols ∨ thn.hasSymbols ∨ els.hasSymbols)
    .ITE #[cnd.toUnsafe, thn.toUnsafe, els.toUnsafe]

section nary2 variable (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp <;> omega)

/-- N-ary equality constructor. -/
def mkEqual : Build Formula :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .EQUAL (terms.map toUnsafe)

/-- N-ary less-than constructor. -/
def mkLt : Build Formula :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .LT (terms.map toUnsafe)

/-- N-ary less-than-or-equal-to constructor. -/
def mkLe : Build Formula :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .LEQ (terms.map toUnsafe)

/-- N-ary greater-than-or-equal-to constructor. -/
def mkGe : Build Formula :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .GEQ (terms.map toUnsafe)

/-- N-ary greater-than constructor. -/
def mkGt : Build Formula :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .GT (terms.map toUnsafe)

/-- N-ary addition. -/
def mkAdd : Build (Term α) := do
  let _ := valid
  logicDo .nonDiff
  mkTerm (terms.any hasSymbols)
    .ADD (terms.map toUnsafe)

/-- N-ary multiplication. -/
def mkMul : Build (Term α) := do
  let _ := valid
  let mut nl? := none
  for term in terms do
    if term.hasSymbols then
      match nl? with
      | none => nl? := some false
      | some false =>
        nl? := some true
        break
      | _ => break -- unreachable
  let nl := nl?.getD false
  let hs := nl?.isSome
  if nl then
    logicDo .nonLinear
  mkTerm hs .MULT (terms.map toUnsafe)

end nary2

/-- Binary equality. -/
def equal (lft rgt : Term α) : Build Formula :=
  mkEqual #[lft, rgt]

/-- Binary less-than. -/
def lt (lft rgt : Term α) : Build Formula :=
  mkLt #[lft, rgt]

/-- Binary less-than-or-equal-to. -/
def le (lft rgt : Term α) : Build Formula :=
  mkEqual #[lft, rgt]

/-- Binary greater-than-or-equal-to. -/
def ge (lft rgt : Term α) : Build Formula :=
  mkEqual #[lft, rgt]

/-- Binary greater-than. -/
def gt (lft rgt : Term α) : Build Formula :=
  mkEqual #[lft, rgt]

/-- Binary addition. -/
def add (lft rgt : Term α) : Build (Term α) := do
  mkAdd #[lft, rgt]

/-- Binary multiplication. -/
def mul (lft rgt : Term α) : Build (Term α) := do
  mkMul #[lft, rgt]

end Term



/-- Opaque solver state. -/
structure Smt.State where
/-- **[private]** Constructor. -/
private mk ::
  /-- **[private]** Solver accessor. -/
  private solver : cvc5.Solver

/-- Smt error-`Smt.State`-monad.

Cannot run sat/unsat/unknown-specific command such as get-value, get-proof, *etc.* See `Smt.Sat`,
`Smt.Unsat`, and `Smt.Unknown`.
-/
abbrev Smt (m : Type → Type u) :=
  ExceptT Error (StateT Smt.State m)

namespace Smt variable [M : Monad m]

protected
instance : MonadLift m (Smt m) :=
  ⟨fun code state => return (.ok (← code), state)⟩

/-- **[private]** Lifts `cvc5.SolverT` code. -/
private
def lift5 (code : cvc5.SolverT m α) : Smt m α := do
  let state ← get
  let (res, solver) ← code state.solver
  set {state with solver}
  return ← Res.lift res

/-- Throws an `Error.userError`. -/
protected
def throwUser [MonadExcept Error m] (msg : String) : m α := do
  throw <| Error.userError msg

/-- Asserts a formula. -/
def assert (formula : Formula) : Smt m Unit := do
  lift5 <| cvc5.Solver.assertFormula (m := m) formula.toUnsafe

section variable (assuming : Option (Array Formula) := none)

/-- Checks the satisfiability of the formulas asserted with `Smt.assert`. -/
def checkSat : Smt m CheckSat := do
  let res ←
    match assuming with
    | none | some #[] => lift5 <| cvc5.Solver.checkSat (m := m)
    | some assuming =>
      assuming.map Term.toUnsafe
      |> cvc5.Solver.checkSatAssuming (m := m)
      |> lift5
  pure <|
    if res.isSat then CheckSat.sat
    else if res.isUnsat then CheckSat.unsat
    else if res.isUnknown then CheckSat.unknown res.toString
    else CheckSat.other res.toString

/-- Simplified `Smt.checkSat`, returns true/false for sat/unsat, `none` for unknown/unexpected. -/
def checkSat? : Smt m (Option Bool) :=
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
abbrev Sat (m : Type → Type u) :=
  ExceptT Error (StateT Sat.State m)

/-- Unsat-mode monad, allows running commands such as get-proof.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev Unsat (m : Type → Type u) :=
  ExceptT Error (StateT Unsat.State m)

/-- Unknown-mode monad, allows running unknown-mode-specific commands.

`Smt` does not lift to this monad as this would allow issuing a check-sat that could switch to a
different solver mode.
-/
abbrev Unknown (m : Type → Type u) :=
  ExceptT Error (StateT Unknown.State m)



/-- Performs a check-sat and runs sat/unsat/unknown-specific code. -/
def checkSatAnd
  (assuming : Option (Array Formula) := none)
  (ifSat : Smt.Sat m α := Smt.throwUser "unexpected sat result")
  (ifUnsat : Smt.Unsat m α := Smt.throwUser "unexpected unsat result")
  (ifUnknown : Smt.Unknown m α := Smt.throwUser "unexpected unknown result")
: Smt m α := do
  if let some isSat ← checkSat? assuming then
    let state ← get
    if isSat then
      let (res, state) ← ifSat ⟨state⟩
      set state.toState
      return ← res
    else
      let (res, state) ← ifUnsat ⟨state⟩
      set state.toState
      return ← res
  else
    let state ← get
    let (res, state) ← ifUnknown ⟨state⟩
    set state.toState
    return ← res



namespace Sat

private
def lift5 (code : cvc5.SolverT m α) : Sat m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, ⟨⟨solver⟩⟩)

def getValue {α : Srt} (term : Term α) : Sat m (Term α) := do
  let term! ← lift5 <| cvc5.Solver.getValue term.toUnsafe
  return Term.ofUnsafe false term!

def getValues {α : Srt} (terms : Array (Term α)) : Sat m (Array (Term α × Term α)) := do
  let mut values := Array.mkEmpty terms.size
  for term in terms do
    let value ← getValue term
    values := values.push (term, value)
  return values

end Sat

namespace Unsat

private
def lift5 (code : cvc5.SolverT m α) : Unsat m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, ⟨⟨solver⟩⟩)

def getProof : Unsat m (Array cvc5.Proof) := do
  lift5 <| cvc5.Solver.getProof

end Unsat

namespace Unknown

private
def lift5 (code : cvc5.SolverT m α) : Unknown m α := fun state => do
  let (res, solver) ← code state.solver
  return (Res.lift res, ⟨⟨solver⟩⟩)

end Unknown

end Smt
