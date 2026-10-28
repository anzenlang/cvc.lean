/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped

public meta import Cvc.Untyped



/-! # Folding and walking, sort-erased -/
namespace Cvc.Tests.Untyped.Traverse

open Cvc
open Cvc.Untyped

public section variable [Ω]

def.term_view V

end

/-! ## Folding

Every node is visited and handed over with its view. Only the functions a fold needs are passed.
-/

/-- info: nodes: 23
first comparison: (some #[(+ x 1), (* 2 k)])
deepest quantifier nesting: 2
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let k ← Term.mkSymbol int "k"
  let p ← Term.mkSymbol (← Srt.bool) "p"
  let t ← smt! (x + 1 < 2 * k ∧ p) ∧ ∀ (n : int), n < k → ∃ (m : int), n < m
  -- counting nodes: a quantifier's variable list is a node like any other
  let nodes ← t.fold 0 (pre := fun _ (_ : V) n => return .descend (n + 1))
  println! "nodes: {nodes}"
  -- the first `<`, then stop
  let first ← t.fold none (pre := fun _ v found => match v with
    | V.lt ks => return .stop (some s!"{ks.val}")
    | _ => return .descend found)
  println! "first comparison: {first}"
  -- the deepest nesting of quantifiers: `pre` and `post` together
  let (_, deepest) ← t.fold (0, 0)
    (pre := fun _ v (depth, deepest) => match v with
      | V.forall' .. | V.exists' .. => return .descend (depth + 1, max deepest (depth + 1))
      | _ => return .descend (depth, deepest))
    (post := fun _ v (depth, deepest) => match v with
      | V.forall' .. | V.exists' .. => return .continue (depth - 1, deepest)
      | _ => return .continue (depth, deepest))
  println! "deepest quantifier nesting: {deepest}"

/-! A fold runs in any monad: here `Id`, no `Env` involved once the term exists. -/

section variable [Ω]

/-- The symbols a term mentions, in order of first appearance. -/
def symbols (t : Term) : Array String :=
  Id.run <| t.fold #[] (pre := fun _ v syms => match v with
    | V.symbol name => return .descend (if syms.contains name then syms else syms.push name)
    | _ => return .descend syms)

end

/-- info: #[x, y]
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  println! symbols (← smt! x + y < x * 2)



/-! ## Walking

A walk's functions get the zipper focused on the node, and may replace it; a replacement must keep
the node's sort, which is checked. `post` sees a node rebuilt with its replaced kids, so a bottom-up
simplifier is a `post` alone.
-/

section variable [Ω]

/-- Whether a term is the integer literal `n`. -/
def isInt (n : Int) (t : Term) : Bool := match V.of t with
  | .value v => v.getIntValue? == some n
  | _ => false

/-- Simplifies `t + 0`, `0 + t`, `t * 1` and `¬¬t`, bottom-up, counting the steps. -/
def simplify (t : Term) : Env (Term × Nat) :=
  t.walk 0 (post := fun _ v n => match v with
    | V.add ks | V.mul ks =>
      let unit := if v matches V.mul _ then 1 else 0
      match ks.val.toList with
      | [a, b] =>
        if isInt unit b then return .replace a (n + 1)
        else if isInt unit a then return .replace b (n + 1)
        else return .continue n
      | _ => return .continue n
    | V.not t => match V.of t with
      | V.not u => return .replace u (n + 1)
      | _ => return .continue n
    | _ => return .continue n)

end

/-- info: (not (not (and (< (* (+ x 0) 1) y) (not (not (not (not (= (+ 0 y) x))))))))
  ↦ (and (< x y) (= y x)), in 6 steps
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let t ← smt! ¬ ¬ ((x + 0) * 1 < y ∧ ¬ ¬ ¬ ¬ (0 + y = x))
  let (s, n) ← simplify t
  println! "{t}\n  ↦ {s}, in {n} steps"

/-! `replaceAndRevisit` visits the replacement from `pre`, so a top-down rewrite collapses nested
cases one after the other; `stop` ends the walk, keeping what was replaced; and a replacement of
another sort is refused. -/

/-- info: top-down : (and p (= x x))
first x  : (and (not (not (not (not p)))) (= 0 x))
cannot replace `p`, of sort `Bool`, by `0`, of sort `Int`
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let p ← Term.mkSymbol (← Srt.bool) "p"
  let t ← smt! ¬ ¬ ¬ ¬ p ∧ x = x
  let (s, _) ← t.walk () (pre := fun _ v _ => match v with
    | V.not t => match V.of t with
      | V.not u => return .replaceAndRevisit u ()
      | _ => return .descend ()
    | _ => return .descend ())
  println! "top-down : {s}"
  let zero ← Term.mkInt 0
  let (s, _) ← t.walk false (pre := fun _ v done =>
    if done then return .stop done else match v with
    | V.symbol "x" => return .replace zero true
    | _ => return .descend done)
  println! "first x  : {s}"
  try
    discard <| t.walk () (pre := fun _ v _ => match v with
      | V.symbol "p" => return .replace zero ()
      | _ => return .descend ())
  catch e => println! "{e}"



/-! ## The zipper by hand -/

/-- info: focus: y, depth 2
left of it: x
root: (< (+ x 7) 3)
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let t ← smt! x + y < 3
  let z := ZipperOf.ofTermErased t
  let some z := z.down 0 | println! "no kid"
  let some z := z.down 1 | println! "no kid"
  println! "focus: {z.focus}, depth {z.depth}"
  let z ← z.replace (← Term.mkInt 7)
  let some z := z.left | println! "no sibling"
  println! "left of it: {z.focus}"
  println! "root: {← z.root}"
