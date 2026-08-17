/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Array
import Cvc.Typed.Core.Bool
import Cvc.Typed.Core.Arith

public meta import Cvc.Typed.Theory.Array
public meta import Cvc.Typed.Core.Bool
public meta import Cvc.Typed.Core.Arith



/-! # Generated Array constructors, typed -/
namespace Cvc.Tests.Typed.Term.Array

open Cvc
open Cvc.Typed.Term

/-- info:
select  : (select a i)
store   : (store a i j)
eqRange : (eqrange a a i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Typed.Term.mkSymbolAs (Cvc.TotalMap Int Int) "a"
  let i ← Cvc.Typed.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Typed.Term.mkSymbolAs (Int) "j"

  println! "select  : {← select a i}"
  println! "store   : {← store a i j}"
  println! "eqRange : {← eqRange a a i j}"

/-! ## Constructors -/

/-- info: mkConstArray : ((as const (Array Int Int)) 0) -/
#guard_msgs in #eval Env.runIO do
  let zero ← mkInt 0
  println! "mkConstArray : {← (mkConstArray zero : Env (Cvc.Typed.Term (Cvc.TotalMap Int Int)))}"
