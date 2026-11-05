/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped

public meta import Cvc.Untyped



/-! # Building from a kind

`mkOfKind` applies a raw `Kind`, checked by cvc5 alone; `replaceKids` reuses an existing term's
operator, indices included, with other kids.
-/
namespace Cvc.Tests.Untyped.Kind

open Cvc
open Cvc.Untyped

/-- info: (+ x y 1)
(=> p (< x y))
error: [internal] expecting a Boolean subexpression
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let p ← Term.mkSymbol (← Srt.bool) "p"
  println! ← Term.mkOfKind .ADD #[x, y, ← Term.mkInt 1]
  println! ← Term.mkOfKind .IMPLIES #[p, ← Term.mkOfKind .LT #[x, y]]
  -- nothing is checked before cvc5 is
  try discard <| Term.mkOfKind .AND #[x, p]
  catch e => println! "error: {e}"

/-- info: (+ y x)
((_ extract 3 0) c)
(f y)
7
(forall ((n Int)) (< n y))
error: [internal] expecting an arithmetic subterm
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let p ← Term.mkSymbol (← Srt.bool) "p"
  let b ← Term.mkSymbol (← Srt.bitVec 8) "b"
  let c ← Term.mkSymbol (← Srt.bitVec 8) "c"
  let f ← Term.mkSymbol (← Srt.function #[int] int) "f"
  println! ← (← Term.add x y).replaceKids #[y, x]
  -- an indexed operator keeps its indices
  println! ← (← Term.bvExtract 3 0 b).replaceKids #[c]
  -- an application's first kid is the function
  println! ← (← Term.apply f x).replaceKids #[f, y]
  -- a term with no kids is its own rebuild
  println! ← (← Term.mkInt 7).replaceKids #[]
  -- a quantifier's kids are its variable list and its body
  let q ← Term.forallH [("n", int)] fun n => Term.lt n x
  let #[vars, _] := q.getKids | println! "not a quantifier"
  let #[n] := vars.getKids | println! "not one variable"
  println! ← q.replaceKids #[vars, ← Term.lt n y]
  try discard <| (← Term.add x y).replaceKids #[x, p]
  catch e => println! "error: {e}"
