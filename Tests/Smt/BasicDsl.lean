/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/
import Tests.Basic



namespace Cvc.Test



open scoped Cvc.Symbols.Dsl
open scoped Cvc.Term.Dsl



namespace System

symbol structure State where
  reset : Bool
  startStop : Bool
  counter : Int
  counting : Bool

namespace State

def init (state : State.Terms) : Term.Build Formula := do
  smt! 0 ≤ state.counter! ∧ state.counting! = false

end State

end System


Smt.test!

[Symbols.basics]
  Smt.setOption Cvc.Option.produceModels
  let symbols := System.State.idents
  let state ← symbols.declare
  let init ← state.init
  show[init]
  Smt.assert (← state.init)
  Smt.checkSatAnd
    (ifSat := do
      println! "sat"
      let val ← state.getVal
      println! "- reset     ↦ {val.reset!}"
      println! "- startStop ↦ {val.startStop!}"
      println! "- counter   ↦ {val.counter!}"
      println! "- counting  ↦ {val.counting!}"
    )
    (ifUnsat := do
      println! "unsat")
/-- info:
init ↦ (and (<= 0 counter) (= counting false))

sat
- reset     ↦ false
- startStop ↦ false
- counter   ↦ 0
- counting  ↦ false
-/
