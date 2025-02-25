/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc



/-! # Comparison between `lean-cvc5`, `cvc.lean` basic, and `cvc.lean` safe(r) -/



section
open cvc5

def cvc5Demo (tm : TermManager) : SolverT BaseIO (Option Term) := do
  let intSort := tm.getIntegerSort

  let three ← tm.mkInteger 3
  let six ← tm.mkInteger 6

  Solver.setLogic "QF_LIA"
  Solver.setOption "produce-models" "true"

  let n ← Solver.declareFun "n" #[] intSort true

  -- `3 * n`
  let three_n ← tm.mkTerm .MULT #[three, n]
  -- `3 * n = 6`
  let t ← tm.mkTerm .EQUAL #[three_n, six]

  Solver.assertFormula t

  let isSatRes ← Solver.checkSat

  if isSatRes.isSat then
    let nVal ← Solver.getValue n
    return nVal
  else
    return none

/-- info: ok: (some 2) -/
#guard_msgs in
#eval do
  let tm ← TermManager.new
  cvc5Demo tm |> Solver.run tm

end



section
open Cvc

open Smt in
def cvcBasicDemo : SmtIO (Option Term) := do
  let three ← Term.mkInt 3
  let six ← Term.mkInt 6

  setLogic Logic.qf_lia
  setOption .produceModels

  let n ← declareFun "n" Int

  let three_n ← three.mul n
  let t ← three_n.eq six

  assert t

  let isSat? ← checkSat?

  if let some true := isSat? then
    let nVal ← getValue n
    return nVal
  else
    return none

/-- info: 2 -/
#guard_msgs in
#eval do
  if let some nVal ← cvcBasicDemo.run! then
    return nVal
  else
    IO.throwServerError "expected sat result"

end



section
open Cvc (Logic)
open Cvc.Safe

open Smt in
def cvcSafeDemo : SmtT IO (Option Int) := do
  let three ← Term.mkInt 3
  let six ← Term.mkInt 6

  setLogic .qf_lia
  setOption .produceModels

  let n ← declareFun "n" Int
  let three_n ← three.mul n
  let t ← three_n.eq six

  assert t

  checkSat (m := IO)
    (ifSat := do
      let nVal ← getValue n
      return some nVal)
    (ifUnsat := return none)


/-- info: 2 -/
#guard_msgs in
#eval do
  if let some nVal ← cvcSafeDemo.run! then
    return nVal
  else
    IO.throwServerError "expected sat result"



open Smt in
open scoped Term in
def cvcSafeDemo' : SmtT IO (Option (Int × Bool)) := do
  setLogic Logic.lia.qf.uf
  setOption .produceModels

  let n ← declareFun "n" Int
  let f ← declareFun "f" (Int → Bool)
  let t ← smt! 3 * n = 6 ∧ (¬ n ≤ 1 ∨ f n)

  assert t

  checkSat
    (ifSat := do
      let nVal ← getValue n
      let appVal ← getValue (← smt! f n)
      return (nVal, appVal))


/-- info:
n   = 2
f n = false
-/
#guard_msgs in
#eval do
  let res ← cvcSafeDemo'.run!
    (handleError := fun e => do
      println! "error: {e}"
      return none
    )
  if let some (nVal, appVal) := res then
    println! "n   = {nVal}"
    println! "f n = {appVal}"
end
