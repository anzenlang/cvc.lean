/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Safe.Init



namespace Cvc.Safe.Test

open Smt



/-- error: application type mismatch
  assert f'
argument
  f'
has type
  Term (Int → Bool) : Type
but is expected to have type
  Term Bool : Type
---
error: cannot evaluate expression that depends on the `sorry` axiom.
Use `#eval!` to evaluate nevertheless (which may cause lean to crash).
-/
#test do
  setLogic Logic.qf_lia.uf

  let f ← declareFun "f" (Int → Int → Bool)
  assertEq f.getSrt.toString "(-> Int Int Bool)"
  -- make sure `f` has the right `Term` type
  let _ : Term (Int → Int → Bool) := f

  let n : Term Int ← declareFun "n" Int
  assertEq n.getSrt.toString "Int"

  let m ← declareFun "m" Int
  assertEq m.getSrt.toString "Int"

  let f' ← f n
  assertEq f'.toString "(f n)"
  assertEq f'.getSrt.toString "(-> Int Bool)"
  -- make sure `f'` has the right `Term` type
  let _ : Term (Int → Bool) := f'

  assert f' -- error: `assert` expects a `Term Bool`



#test do
  setLogic Logic.qf_lia.uf

  let f ← declareFun "f" (Int → Int → Bool)
  assertEq f.getSrt.toString "(-> Int Int Bool)"
  -- make sure `f` has the right `Term` type
  let _ : Term (Int → Int → Bool) := f

  let n : Term Int ← declareFun "n" Int
  assertEq n.getSrt.toString "Int"

  let m ← declareFun "m" Int
  assertEq m.getSrt.toString "Int"

  -- (partial) application works out of the box, but only for one argument
  -- for more arguments see `smt!` below
  let fApp1 ← f n
  assertEq fApp1.toString "(@ f n)"
  assertEq fApp1.getSrt.toString "(-> Int Bool)"
  -- make sure `fApp1` has the right `Term` type
  let _ : Term (Int → Bool) := fApp1

  let fApp2 ← fApp1 m
  assertEq fApp2.toString "(f n m)"
  assertEq fApp2.getSrt.toString "Bool"
  -- make sure `fApp2` has the right `Term` type
  let _ : Term Bool := fApp2

  assert fApp2

  let isSat? ← checkSat?
  assertEq isSat? true

  let not_fApp2 ← fApp2.not
  assertEq not_fApp2.toString "(not (f n m))"
  assertEq not_fApp2.getSrt.toString "Bool"

  assert not_fApp2

  let isSat ←
    checkSat
      (ifSat := pure true)
      (ifUnsat := pure false)
  assertEq isSat false

  -- using `smt!`

  let fApp1' ← smt! f n
  assertEq fApp1'.toString "(@ f n)"
  let _ : Term (Int → Bool) := fApp1'

  let fApp ← smt! f n m
  assertEq fApp.toString "(f n m)"
  let _ : Term Bool := fApp

  let not_fApp ← smt! ¬ f n m
  assertEq not_fApp.toString "(not (f n m))"
  let _ : Term Bool := not_fApp
