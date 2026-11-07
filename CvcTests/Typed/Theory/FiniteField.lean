/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.FiniteField
import Cvc.Typed.Core.Bool

public meta import Cvc.Typed.Theory.FiniteField
public meta import Cvc.Typed.Core.Bool



/-! # Generated FiniteField constructors, typed -/
namespace Cvc.Tests.Typed.Term.FiniteField

open Cvc
open Cvc.Typed.Term

/-- info:
add   : (ff.add a b)
mul   : (ff.mul a b)
neg   : (ff.neg a)
bitsum: (ff.bitsum a b)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Typed.Term.mkSymbolAs (Cvc.FiniteField 7) "a"
  let b ← Cvc.Typed.Term.mkSymbolAs (Cvc.FiniteField 7) "b"

  println! "add   : {← ffAdd a b}"
  println! "mul   : {← ffMul a b}"
  println! "neg   : {← ffNeg a}"
  println! "bitsum: {← ffBitsum a b}"

/-! An element comes back as the same element of the field, in cvc5's symmetric representation
rather than as the integer it was built from.
-/

/-- info:
0 → 0 : same element
4 → -3 : same element
6 → -1 : same element
7 → 0 : same element
10 → 3 : same element
-4 → 3 : same element
-/
#guard_msgs in #eval Env.runIO do
  for i in [0, 4, 6, 7, 10, -4] do
    let back : Cvc.FiniteField 7 ← extractValue (← mkValue (⟨i⟩ : Cvc.FiniteField 7))
    println! "{i} → {back} : {if (back.repr - i) % 7 == 0 then "same element" else "DIFFERENT"}"
