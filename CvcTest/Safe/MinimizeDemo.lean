import CvcTest.Safe.Minimize



namespace Cvc.Safe.Test.Minimize

open scoped Term


namespace Test1

structure State (F : Type → Type) where
  n1 : F Int
  n2 : F Int
  n3 : F Int

abbrev Sys := Arith State

instance : Vars State where
  mapM s f := do
    let n1 ← f s.n1
    let n2 ← f s.n2
    let n3 ← f s.n3
    return {n1, n2, n3}

def vars : State Decl := ⟨"n1", "n2", "n3"⟩

/-- info:
got a model:
- `n1 = 2`
- `n2 = 1`
- `n3 = 1`
-/
#test do
  let preds : Array (Pred State) := #[
    smtFun! terms => 0 < terms.n1,
    smtFun! terms => 0 < terms.n2,
    smtFun! terms => 2 * terms.n1 + 3 * terms.n2 = 7*terms.n3
  ]
  if let some model ← findModel? vars preds then
    println! "got a model:"
    println! "- `n1 = {model.n1}`"
    println! "- `n2 = {model.n2}`"
    println! "- `n3 = {model.n3}`"
  else
    panic "no model available"



/-- info:
done in 42 iterations
minimum value is `-55` on
- n1 = 10
- n2 = 10
- n3 = -5
-/
#guard_msgs in #eval do
  let constraints : Array (Pred State) := #[
    smtFun! terms => (-10) ≤ terms.n1 ∧ terms.n1 ≤ 10,
    smtFun! terms => (-10) ≤ terms.n2 ∧ terms.n2 ≤ 10,
    smtFun! terms => (-5) ≤ terms.n3 ∧ terms.n3 ≤ 5
  ]
  let f : Fun State Int := smtFun! terms =>
    terms.n1 - 2 * terms.n2 + 3 * (terms.n3 - terms.n1)
  let minimized? ← minimize vars f constraints
  if let (some (val, model), count) := minimized? then
    println! "done in {count} iteration{if count > 1 then "s" else ""}"
    println! "minimum value is `{val}` on"
    println! "- n1 = {model.n1}"
    println! "- n2 = {model.n2}"
    println! "- n3 = {model.n3}"
