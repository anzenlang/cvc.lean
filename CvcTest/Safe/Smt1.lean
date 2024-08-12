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
error: cannot evaluate code because '_eval._lambda_6' uses 'sorry' and/or contains errors
-/
test! do
  setLogic Logic.qf_lia.uf

  let f ← declareFun "f" (Int → Int → Bool)
  assertEq (← f.getSrt).toString "(-> Int Int Bool)"
  -- make sure `f` has the right `Term` type
  let _ : Term (Int → Int → Bool) := f

  let n : Term Int ← declareFun "n" Int
  assertEq (← n.getSrt).toString "Int"

  let m ← declareFun "m" Int
  assertEq (← m.getSrt).toString "Int"

  let f' ← f n
  assertEq f'.toString "(f n)"
  assertEq (← f'.getSrt).toString "(-> Int Bool)"
  -- make sure `f'` has the right `Term` type
  let _ : Term (Int → Bool) := f'

  assert f'



test! do
  setLogic Logic.qf_lia.uf

  let f ← declareFun "f" (Int → Int → Bool)
  assertEq (← f.getSrt).toString "(-> Int Int Bool)"
  -- make sure `f` has the right `Term` type
  let _ : Term (Int → Int → Bool) := f

  let n : Term Int ← declareFun "n" Int
  assertEq (← n.getSrt).toString "Int"

  let m ← declareFun "m" Int
  assertEq (← m.getSrt).toString "Int"

  let f' ← f n
  assertEq f'.toString "(f n)"
  assertEq (← f'.getSrt).toString "(-> Int Bool)"
  -- make sure `f'` has the right `Term` type
  let _ : Term (Int → Bool) := f'

  let f'' ← f' m
  assertEq f''.toString "(f n m)"
  assertEq (← f''.getSrt).toString "Bool"
  -- make sure `f''` has the right `Term` type
  let _ : Term Bool := f''

  assert f''

  let isSat? ← checkSat?
  assertEq isSat? true

  let not_f'' ← f''.not
  assertEq not_f''.toString "(not (f n m))"
  assertEq (← not_f''.getSrt).toString "Bool"

  assert not_f''

  let isSat? ← checkSat?
  assertEq isSat? false
