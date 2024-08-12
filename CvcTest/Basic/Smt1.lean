/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Basic.Init



namespace Cvc.Test


open Smt

test! do
  setLogic Logic.qf_lia

  let n ← declareFun "n" Int
  assertEq n.getSrt.toString "Int"

  let f ← declareFun "f" (Int → Int → Bool)
  assertEq f.getSrt.toString "(-> Int Int Bool)"
