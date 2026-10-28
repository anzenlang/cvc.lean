/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.FiniteField
import Cvc.Untyped.Core.Bool
import Cvc.Types.FiniteField

public meta import Cvc.Untyped.Theory.FiniteField
public meta import Cvc.Untyped.Core.Bool
public meta import Cvc.Types.FiniteField



/-! # Generated FiniteField constructors, sort-erased -/
namespace Cvc.Tests.Untyped.Term.FiniteField

open Cvc
open Cvc.Untyped.Term

/-- info:
add   : (ff.add a b)
mul   : (ff.mul a b)
neg   : (ff.neg a)
bitsum: (ff.bitsum a b)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Untyped.Term.mkSymbolAs (Cvc.FiniteField 7) "a"
  let b ← Cvc.Untyped.Term.mkSymbolAs (Cvc.FiniteField 7) "b"

  println! "add   : {← ffAdd a b}"
  println! "mul   : {← ffMul a b}"
  println! "neg   : {← ffNeg a}"
  println! "bitsum: {← ffBitsum a b}"
