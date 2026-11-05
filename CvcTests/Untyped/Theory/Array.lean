/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

meta import Cvc.Untyped.Core.Bool
meta import Cvc.Untyped.Theory.Arith
meta import Cvc.Untyped.Theory.Array



/-! # Generated Array constructors, sort-erased -/
namespace Cvc.Tests.Untyped.Term.Array

open Cvc
open Cvc.Untyped.Term

/-- info:
select  : (select a i)
store   : (store a i j)
eqRange : (eqrange a a i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Untyped.Term.mkSymbolAs (Cvc.TotalMap Int Int) "a"
  let i ← Cvc.Untyped.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Untyped.Term.mkSymbolAs (Int) "j"

  println! "select  : {← select a i}"
  println! "store   : {← store a i j}"
  println! "eqRange : {← eqRange a a i j}"

/-! ## Constructors -/

/-- info: mkConstArray : ((as const (Array Int Int)) 0) -/
#guard_msgs in #eval Env.runIO do
  let zero ← mkInt 0
  -- the *index* sort; the element sort comes off the default value
  let idx ← Srt.of Int
  println! "mkConstArray : {← mkConstArray idx zero}"
