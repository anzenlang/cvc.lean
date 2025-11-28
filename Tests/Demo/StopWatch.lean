/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Tests.Demo.Induction



namespace Cvc.Induction.Tests.StopWatch variable [Cvc.Scope]

namespace Sw

protected structure State (α : Type) where
  startStop : α
  reset : α
  counting : α
  counter : α

def Idents : Sw.State String where
  startStop := "startStop"
  reset := "reset"
  counting := "counting"
  counter := "counter"

instance Spec : State Sw.State where
  mapM sw f := return ⟨
    ← f sw.startStop .bool, ← f sw.reset .bool, ← f sw.counting .bool, ← f sw.counter .int
  ⟩
  foldM sw f init := do
    let mut acc := init
    acc ← f acc sw.startStop .bool
    acc ← f acc sw.reset .bool
    acc ← f acc sw.counting .bool
    acc ← f acc sw.counter .int
    return acc

section open scoped Cvc.Term.Dsl

def base : Spec.Pred := fun state =>
  smt! state.counter = 0 ∧ state.counting = state.startStop

def step : Spec.Rel := fun prev curr => smt!
  (curr.counting = if curr.startStop then ¬ prev.counting else prev.counting)
  ∧
  (curr.counter =
    if curr.reset then 0 else
    if curr.counting then prev.counter + 1
    else prev.counter)

def counter_pos : Spec.Pred × String where
  fst state := smt! 0 ≤ state.counter
  snd := "0 ≤ counter"

def counter_not_7 : Spec.Pred × String where
  fst state := smt! state.counter ≠ 7
  snd := "counter ≠ 7"

def counter_lt_7 : Spec.Pred × String where
  fst state := smt! state.counter < 7
  snd := "counter < 7"

def counter_not_m7 : Spec.Pred × String where
  fst state := smt! state.counter ≠ -7
  snd := "counter ≠ -7"

def zero_of_reset : Spec.Pred × String where
  fst state := smt! state.reset → state.counter = 0
  snd := "reset → counter = 0"

end

def mk (candidates : Spec.Candidates) : Spec.Sys :=
  ⟨Sw.Idents, base, step, candidates⟩

def simple : Spec.Sys :=
  mk #[counter_pos]

def invalid : Spec.Sys :=
  mk #[counter_not_7]

def unprovable : Spec.Sys :=
  mk #[counter_not_m7]

def valid := mk #[counter_pos, counter_not_m7, zero_of_reset]

def all := mk #[counter_pos, counter_not_7, counter_lt_7, counter_not_m7, zero_of_reset]

end Sw

def demo (spec : Sw.Spec.Sys)
  (k : Nat := 1) (stepInfo := false) (showBaseLog := false) (showStepLog := false)
: Env Unit := do
  println! "|===| creating system..."
  let sys ← Sys.mk spec
  sys.print "| "
  let sys ← sys.run k
    (beforeLoopingDo :=
      if stepInfo then fun sys => do
        println! "|===| before step {sys.k}"
        sys.print "| "
      else fun _ => return ()
    )
  if sys.isDone
  then println! "|===| done after {sys.k} step(s) 🎉"
  else println! "|===| not done after {sys.k} step(s) 😿"
  sys.print "| "
  println! "|===|"
  if showBaseLog then
    println! "\nbase solver log:\n```smtlib\n{← sys.baseSolver.getLog}\n```"
  if showStepLog then
    println! "\nstep solver log:\n```smtlib\n{← sys.stepSolver.getLog}\n```"

/-- info:
|===| creating system...
| candidates
| -[0]-[unknown] "0 ≤ counter"
|===| done after 1 step(s) 🎉
| candidates
| -[0]-[valid@1] "0 ≤ counter"
|===|
-/
#guard_msgs in #eval Env.runIO <| demo <| Sw.simple

/-- info:
|===| creating system...
| candidates
| -[0]-[unknown] "counter ≠ 7"
|===| done after 8 step(s) 🎉
| candidates
| -[0]-[invalid@7] "counter ≠ 7"
|===|
-/
#guard_msgs in #eval Env.runIO <| demo (k := 10) <| Sw.invalid

/-- info:
|===| creating system...
| candidates
| -[0]-[unknown] "0 ≤ counter"
| -[1]-[unknown] "counter ≠ -7"
| -[2]-[unknown] "reset → counter = 0"
|===| done after 1 step(s) 🎉
| candidates
| -[0]-[valid@1] "0 ≤ counter"
|     proved in cluster [0, 1, 2]
| -[1]-[valid@1] "counter ≠ -7"
|     proved in cluster [0, 1, 2]
| -[2]-[valid@1] "reset → counter = 0"
|     proved in cluster [0, 1, 2]
|===|
-/
#guard_msgs in #eval Env.runIO <| demo (k := 10) <| Sw.valid

/-- info:
|===| creating system...
| candidates
| -[0]-[unknown] "0 ≤ counter"
| -[1]-[unknown] "counter ≠ 7"
| -[2]-[unknown] "counter < 7"
| -[3]-[unknown] "counter ≠ -7"
| -[4]-[unknown] "reset → counter = 0"
|===| done after 8 step(s) 🎉
| candidates
| -[0]-[valid@1] "0 ≤ counter"
|     proved in cluster [0, 3, 4]
| -[1]-[invalid@7] "counter ≠ 7"
|     falsified in cluster [1, 2]
| -[2]-[invalid@7] "counter < 7"
|     falsified in cluster [1, 2]
| -[3]-[valid@1] "counter ≠ -7"
|     proved in cluster [0, 3, 4]
| -[4]-[valid@1] "reset → counter = 0"
|     proved in cluster [0, 3, 4]
|===|
-/
#guard_msgs in #eval Env.runIO <| demo (k := 10) <| Sw.all
