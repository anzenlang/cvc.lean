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

abbrev Pred := Term Srt.bool

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
def bool (b : Bool) : Build Pred :=
  tmDo (fun tm => tm.mkBoolean b |> Term.ofUnsafe false)

/-- Integer constant constructor. -/
protected
def int (i : Int) : Build Term.Int := do
  logicDo .int
  tmDo (· |>.mkInteger i |> Term.ofUnsafe false)

/-- If-then-else constructor. -/
def ite (cnd : Pred) (thn els : Term α) : Build (Term α) :=
  mkTerm (cnd.hasSymbols ∨ thn.hasSymbols ∨ els.hasSymbols)
    .ITE #[cnd.toUnsafe, thn.toUnsafe, els.toUnsafe]

section nary2 variable (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp <;> omega)

/-- N-ary equality constructor. -/
def mkEqual : Build Pred :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .EQUAL (terms.map toUnsafe)

/-- N-ary less-than constructor. -/
def mkLt : Build Pred :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .LT (terms.map toUnsafe)

/-- N-ary less-than-or-equal-to constructor. -/
def mkLe : Build Pred :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .LEQ (terms.map toUnsafe)

/-- N-ary greater-than-or-equal-to constructor. -/
def mkGe : Build Pred :=
  let _ := valid
  mkTerm (terms.any hasSymbols) .GEQ (terms.map toUnsafe)

/-- N-ary greater-than constructor. -/
def mkGt : Build Pred :=
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
def equal (lft rgt : Term α) : Build Pred :=
  mkEqual #[lft, rgt]

/-- Binary less-than. -/
def lt (lft rgt : Term α) : Build Pred :=
  mkLt #[lft, rgt]

/-- Binary less-than-or-equal-to. -/
def le (lft rgt : Term α) : Build Pred :=
  mkEqual #[lft, rgt]

/-- Binary greater-than-or-equal-to. -/
def ge (lft rgt : Term α) : Build Pred :=
  mkEqual #[lft, rgt]

/-- Binary greater-than. -/
def gt (lft rgt : Term α) : Build Pred :=
  mkEqual #[lft, rgt]

/-- Binary addition. -/
def add (lft rgt : Term α) : Build (Term α) := do
  mkAdd #[lft, rgt]

/-- Binary multiplication. -/
def mul (lft rgt : Term α) : Build (Term α) := do
  mkMul #[lft, rgt]

end Term



structure Smt.State where
private mk ::
  private solver : cvc5.Solver

abbrev SmtT (m : Type → Type u) :=
  ExceptT Error (StateT Smt.State m)

abbrev Smt := SmtT (m := Id)

namespace Smt variable [Monad m]

instance : MonadLift Smt (SmtT m) :=
  ⟨fun code state => return code state⟩

instance : MonadLift (cvc5.SolverT m) (SmtT m) where
  monadLift code state := do
    let (res, solver) ← code state.solver
    return (res, {state with solver})

private
def liftRes : Except cvc5.Error α → Except Error α :=
  Except.mapError Error.ofCvc5

def assert (formula : Term Bool) : SmtT m Unit := do
  cvc5.Solver.assertFormula (m := m) formula.toUnsafe

def checkSat : SmtT m CheckSat := do
  let res ← cvc5.Solver.checkSat (m := m)
  pure <|
    if res.isSat then CheckSat.sat
    else if res.isUnsat then CheckSat.unsat
    else if res.isUnknown then CheckSat.unknown res.toString
    else CheckSat.other res.toString

def checkSat? : SmtT m (Option Bool) :=
  CheckSat.isSat? <$> checkSat

end Smt
