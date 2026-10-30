/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed

public meta import Cvc.Typed



/-! # Folding and walking, typed

The sort-erased traversals' order and steps, with each node handed over at its sort. A function
matches the sort alongside the view, `match τ, v with`, so that each alternative refines it, and as
a term rather than inside `do`, so that the refinement reaches the result type.
-/
namespace Cvc.Tests.Typed.Traverse

open Cvc
open Cvc.Typed

public section variable [Ω]

def.term_view V

end

/-! ## Folding

A node whose sort a `Typ` describes goes to `pre`/`post`, any other to `prePlain`/`postPlain`: here,
a quantifier's variable list. Only the functions a fold needs are passed.
-/

/-- info: typed nodes: 21, plain nodes: 2
first integer comparison: (some #[(+ x 1), (* 2 k)])
deepest quantifier nesting: 2
integer symbols: #[x, k]
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let k ← Term.mkSymbolAs Int "k"
  let p ← Term.mkSymbolAs Bool "p"
  let t ← smt! (x + 1 < 2 * k ∧ p) ∧ ∀ (n : Int), n < k → ∃ (m : Int), n < m
  let (typed, plain) ← t.fold (0, 0)
    (pre := fun _ (_ : V _) (a, b) => return .descend (a + 1, b))
    (prePlain := fun _ (a, b) => return .descend (a, b + 1))
  println! "typed nodes: {typed}, plain nodes: {plain}"
  -- `ks : Kids Int`: the comparison's operand sort is matched as `.int`
  let first ← t.fold none (pre := fun {τ} _ (v : V τ) found => match τ, v with
    | _, .lt .int ks => return .stop (some s!"{ks.val}")
    | _, _ => return .descend found)
  println! "first integer comparison: {first}"
  let (_, deepest) ← t.fold (0, 0)
    (pre := fun {τ} _ (v : V τ) (depth, deepest) => match τ, v with
      | _, .forall' .. | _, .exists' .. => return .descend (depth + 1, max deepest (depth + 1))
      | _, _ => return .descend (depth, deepest))
    (post := fun {τ} _ (v : V τ) (depth, deepest) => match τ, v with
      | _, .forall' .. | _, .exists' .. => return .continue (depth - 1, deepest)
      | _, _ => return .continue (depth, deepest))
  println! "deepest quantifier nesting: {deepest}"
  let syms ← t.fold #[] (pre := fun {τ} _ (v : V τ) syms => match τ, v with
    | .int, .symbol name => return .descend (if syms.contains name then syms else syms.push name)
    | _, _ => return .descend syms)
  println! "integer symbols: {syms}"



/-! ## Walking

A typed node's replacement is a term of its sort, so an ill-sorted one does not compile; a plain
node's is checked. `post` sees a node rebuilt with its replaced kids, so a bottom-up simplifier is a
`post` alone.
-/

section variable [Ω]

/-- Whether a term is the integer literal `n`. -/
def isInt (n : Int) (t : Term Int) : Bool := t.relax.getIntValue? == some n

/-- Simplifies `t + 0`, `0 + t`, `t * 1` and `¬¬t` over integers, bottom-up, counting the steps.

At `.int`, an `add`'s kids are `Term Int`s, so either is a replacement of the right sort; at
`.bool`, so is the operand of a double negation.
-/
def simplify (t : Term Bool) : Env (Term Bool × Nat) :=
  t.walk 0 (post := fun {τ} _ (v : V τ) n => match τ, v with
    | .int, .add ks | .int, .mul ks =>
      let unit := if v matches .mul _ then 1 else 0
      match ks.val.toList with
      | [a, b] =>
        if isInt unit b then return .replace a (n + 1)
        else if isInt unit a then return .replace b (n + 1)
        else return .continue n
      | _ => return .continue n
    | .bool, .not t => do
      match ← V.of .bool t with
      | .not u => return .replace u (n + 1)
      | _ => return .continue n
    | _, _ => return .continue n)

end

/-- info: (not (not (and (< (* (+ x 0) 1) y) (not (not (not (not (= (+ 0 y) x))))))))
  ↦ (and (< x y) (= y x)), in 6 steps
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  let t ← smt! ¬ ¬ ((x + 0) * 1 < y ∧ ¬ ¬ ¬ ¬ (0 + y = x))
  let (s, n) ← simplify t
  println! "{t}\n  ↦ {s}, in {n} steps"

/-! `replaceAndRevisit` visits the replacement from `pre`, and `stop` ends the walk, keeping what
was replaced. A plain node's replacement of another sort is refused at run time. -/

/-- info: top-down : (and p (= x x))
first x  : (and (not (not (not (not p)))) (= 0 x))
refused  : cannot replace `((n Int))`, of sort `the type of bound variable lists`, by `0`, of sort `Int`
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let p ← Term.mkSymbolAs Bool "p"
  let t ← smt! ¬ ¬ ¬ ¬ p ∧ x = x
  let (s, _) ← t.walk () (pre := fun {τ} _ (v : V τ) _ => match τ, v with
    | .bool, .not t => do
      match ← V.of .bool t with
      | .not u => return .replaceAndRevisit u ()
      | _ => return .descend ()
    | _, _ => return .descend ())
  println! "top-down : {s}"
  let zero ← Term.mkInt 0
  let (s, _) ← t.walk false (pre := fun {τ} _ (v : V τ) done =>
    if done then return .stop done else match τ, v with
    | .int, .symbol "x" => return .replace zero true
    | _, _ => return .descend done)
  println! "first x  : {s}"
  let q ← smt! ∀ (n : Int), n < x
  try
    discard <| q.walk (V := V) () (prePlain := fun _ _ => return .replace zero.relax ())
  catch e => println! "refused  : {e}"

/-! A typed replacement of the wrong sort is a type error. -/

/--
error: Application type mismatch: The argument
  zero
has type
  Term Int
but is expected to have type
  Term Bool
in the application
  WalkPre.replace zero

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 6
-/
#guard_msgs in
example [Ω] (t : Term Bool) (zero : Term Int) : Env (Term Bool × Unit) :=
  t.walk () (pre := fun {τ} _ (v : V τ) _ => match τ, v with
    | .bool, .symbol _ => return .replace zero ()
    | _, _ => return .descend ())



/-! ## The zipper by hand

Moving answers a `Zipper.Any`, the focus's sort read off the term; matching it as `some .int` gives
a zipper whose focus is a `Term Int`, and whose replacement must be one.
-/

/-- info: focus: y, depth 2
left of it: x
root: (< (+ x 7) 3)
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  let t ← smt! x + y < 3
  let ⟨_, z⟩ ← Zipper.ofTerm t
  let some ⟨_, z⟩ ← z.down 0 | println! "no kid"
  let some ⟨some .int, z⟩ ← z.down 1 | println! "no integer kid"
  let y' : Term Int := z.focus
  println! "focus: {y'}, depth {z.depth}"
  let z := z.replace (← Term.mkInt 7)
  let some ⟨_, z⟩ ← z.left | println! "no sibling"
  println! "left of it: {z.relaxedFocus}"
  println! "root: {← z.root}"
