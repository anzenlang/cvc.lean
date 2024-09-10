import CvcTest.Safe.MinimizeSimpler



namespace Cvc.Safe.Test.Minimize



namespace Test1

structure MyVars (α : Type) where
  n1 : α
  n2 : α
  n3 : α

namespace MyVars

instance : Vars MyVars where
  mapM s f := do
    let n1 ← f s.n1
    let n2 ← f s.n2
    let n3 ← f s.n3
    return {n1, n2, n3}

end MyVars

def vars : MyVars String := ⟨"n1", "n2", "n3"⟩

/-- info:
got a model:
- `n1 = 2`
- `n2 = 1`
- `n3 = 1`
-/
#test do
  let preds : Array (Pred MyVars) := #[
    smt! terms => 0 < terms.n1,
    smt! terms => 0 < terms.n2,
    smt! terms => ((2*terms.n1) + (3*terms.n2)) = 7*terms.n3
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
minimum value is `-75` on
- n1 = -10
- n2 = 10
- n3 = 5
-/
#guard_msgs in #eval do
  let constraints : Array (Pred MyVars) := #[
    smt! terms => ((-10) ≤ terms.n1) ∧ (terms.n1 ≤ 10),
    smt! terms => ((-10) ≤ terms.n2) ∧ (terms.n2 ≤ 10),
    smt! terms => ((-5) ≤ terms.n3) ∧ (terms.n3 ≤ 5)
  ]
  let f : Fun MyVars Int :=
    smt! terms =>
      terms.n1 - (2 * terms.n2) + 3 * (terms.n3 - terms.n1)
  let minimized? ← minimize vars f constraints
  if let (some (val, model), count) := minimized? then
    println! "done in {count} iteration{if count > 1 then "s" else ""}"
    println! "minimum value is `{val}` on"
    println! "- n1 = {model.n1}"
    println! "- n2 = {model.n2}"
    println! "- n3 = {model.n3}"
