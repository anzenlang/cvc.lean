/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init



namespace Cvc.Test

def lift {α : Type} [ToString E] : (t? : Except E α) → IO α
| .ok res => return res
| .error e => do
  IO.eprintln e
  panic! "something went wrong"

open cvc5 in
/--info:
boolSort := Bool
intSort := Int
intToBoolSort := (-> Int Bool)
arraySort := (Array (-> Int Bool) Int)
tupleSort := UnitTuple
tupleSort' := (Tuple Bool)
pair := (Tuple Bool Int)
pairNestedLft := (Tuple (Tuple Bool Int) Int)
pairNestedRgt := (Tuple Int (Tuple Bool Int))
tupleSort'' := (Tuple Bool Int (Array (-> Int Bool) Int))
logic = HO_ALIA
asserting (= arr (store arr key val))
asserting (= (select arr key) 1)
sat
-/
#guard_msgs in #eval (@id (IO Unit)) do
  let tm ← TermManager.new

  let boolSort := tm.getBooleanSort
  println! "boolSort := {boolSort}"
  let intSort := tm.getIntegerSort
  println! "intSort := {intSort}"
  let intToBoolSort ← lift <| tm.mkFunctionSort #[intSort] boolSort
  println! "intToBoolSort := {intToBoolSort}"
  let arraySort ← lift <| tm.mkArraySort intToBoolSort intSort
  println! "arraySort := {arraySort}"
  let tupleSort ← lift <| tm.mkTupleSort #[]
  println! "tupleSort := {tupleSort}"
  let tupleSort' ← lift <| tm.mkTupleSort #[boolSort]
  println! "tupleSort' := {tupleSort'}"
  let pair ← lift <| tm.mkTupleSort #[boolSort, intSort]
  println! "pair := {pair}"
  let pairNestedLft ← lift <| tm.mkTupleSort #[pair, intSort]
  println! "pairNestedLft := {pairNestedLft}"
  let pairNestedRgt ← lift <| tm.mkTupleSort #[intSort, pair]
  println! "pairNestedRgt := {pairNestedRgt}"
  let tupleSort'' ← lift <| tm.mkTupleSort #[boolSort, intSort, arraySort]
  println! "tupleSort'' := {tupleSort''}"

  lift <| ← Solver.run (m := IO) tm do
    let logic := Logic.lia.array.ho.toSmtLib
    println! "logic = {logic}"
    Solver.setLogic logic
    Solver.setOption "produce-models" "true"
    let arr1 ← Solver.declareFun "arr" #[] arraySort
    -- let arr2 ← Solver.declareFun "arr" #[] arraySort
    let arr2 := arr1
    let key ← Solver.declareFun "key" #[intSort] boolSort
    let val ← Solver.declareFun "val" #[] intSort
    let tStore ← lift <| tm.mkTerm .STORE #[arr2, key, val]
    let tEq ← lift <| tm.mkTerm .EQUAL #[arr1, tStore]
    let arrayGet ← lift <| tm.mkTerm .SELECT #[ arr1, key ]
    let arrayGetEq ← lift <| tm.mkTerm .EQUAL #[arrayGet, tm.mkInteger 1]

    -- println! "\n|================|"
    -- let keySrt ← lift <| Srt.ofUnsafe key.getSort
    -- println! "keySrt : {keySrt} := {key}"
    -- let ⟨keySrt', keyVariant⟩ ← lift <| Term.unsafeToVariant key
    -- println! "  → {keyVariant} : {keySrt'}"
    -- let valSrt ← lift <| Srt.ofUnsafe val.getSort
    -- println! "valSrt : {valSrt} := {val}"
    -- let ⟨valSrt', valVariant⟩ ← lift <| Term.unsafeToVariant val
    -- println! "  → {valVariant} : {valSrt'}"
    -- let tStoreSrt ← lift <| Srt.ofUnsafe tStore.getSort
    -- println! "tStoreSrt : {tStoreSrt} := {tStore}"
    -- let ⟨tStoreSrt', tStoreVariant⟩ ← lift <| Term.unsafeToVariant tStore
    -- println! "  → {tStoreVariant} : {tStoreSrt'}"
    -- let tEqSrt ← lift <| Srt.ofUnsafe tEq.getSort
    -- println! "tEqSrt : {tEqSrt} := {tEq}"
    -- let ⟨tEqSrt', tEqVariant⟩ ← lift <| Term.unsafeToVariant tEq
    -- println! "  → {tEqVariant} : {tEqSrt'}"
    -- let tEqSrt ← lift <| Srt.ofUnsafe tEq.getSort
    -- println! "tEqSrt : {tEqSrt} := {tEq}"
    -- let ⟨tEqSrt', tEqVariant⟩ ← lift <| Term.unsafeToVariant tEq
    -- println! "  → {tEqVariant} : {tEqSrt'}"
    -- let arrayGetSrt ← lift <| Srt.ofUnsafe arrayGet.getSort
    -- println! "arrayGetSrt : {arrayGetSrt} := {arrayGet}"
    -- let ⟨arrayGetSrt', arrayGetVariant⟩ ← lift <| Term.unsafeToVariant arrayGet
    -- println! "  → {arrayGetVariant} : {arrayGetSrt'}"
    -- let arrayGetEqSrt ← lift <| Srt.ofUnsafe arrayGetEq.getSort
    -- println! "arrayGetEqSrt : {arrayGetEqSrt} := {arrayGetEq}"
    -- let ⟨arrayGetEqSrt', arrayGetEqVariant⟩ ← lift <| Term.unsafeToVariant arrayGetEq
    -- println! "  → {arrayGetEqVariant} : {arrayGetEqSrt'}"
    -- println! "|================|\n"

    println! "asserting {tEq}"
    Solver.assertFormula tEq
    println! "asserting {arrayGetEq}"
    Solver.assertFormula arrayGetEq
    let res ← Solver.checkSat
    if res.isSat then
      println! "sat"
      -- let arr1Val ← Solver.getValue arr1
      -- println! "{arr1} = {arr1Val}"
      -- println! "done"
      -- let arr2Val ← Solver.getValue arr2
      -- println! "{arr2} = {arr2Val}"
      -- let keyVal ← Solver.getValue key
      -- println! "{key} = {keyVal}"
      -- let valVal ← Solver.getValue val
      -- println! "{val} = {valVal}"
      -- let val ← Solver.getValue arrayGet
      -- println! "{arrayGet} = {val}"
    else if res.isUnsat then
      println! "unsat"
    else
      println! "unknown"
