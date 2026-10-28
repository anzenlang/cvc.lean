/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped

public meta import Cvc.Untyped



/-! # Taking sort-erased terms apart

`def.term_view V` generates `V`, the view of every imported theory: a term taken apart one level,
its operator a constructor and its kids, indices and names as fields. Taking a term apart reads
nothing from the solver, so `V.of` is a pure function and everything built on it runs in any monad.

`Cvc.Untyped.View` is the module that brings it in, with the traversals over it; `Cvc.Untyped`
imports it, and every theory besides.
-/
namespace Cvc.Untyped.Examples.Views

open Cvc Untyped

public section variable [Ω]

def.term_view V

end

variable [Ω]



/-! ## A printer

A plain recursive function. The leaves are values, declared symbols and bound variables; anything
the printer does not know is printed as cvc5 prints it, including the aggregate's own catch-all,
`other`, for an operator no imported theory's view takes apart.
-/

/-- A Lean-like rendering of a term, as far as this printer reaches. -/
partial def render (t : Term) : String :=
  let all (op : String) (ks : Kids) :=
    "(" ++ s!" {op} ".intercalate (ks.val.map render).toList ++ ")"
  match V.of t with
  | .value t => toString t
  | .bvar x => toString x.toTerm
  | .symbol name => name
  | .not t => s!"¬{render t}"
  | .and ks => all "∧" ks
  | .or ks => all "∨" ks
  | .implies ks => all "→" ks
  | .ite c a b => s!"(if {render c} then {render a} else {render b})"
  | .equal ks => all "=" ks
  | .lt ks => all "<" ks
  | .add ks => all "+" ks
  | .mul ks => all "*" ks
  | .bvExtract hi lo bv => s!"{render bv}[{hi}:{lo}]"
  | .forall' vars body _ => s!"(∀ {vars.map (·.toTerm)}, {render body})"
  | .apply f args => s!"{render f}({", ".intercalate (args.val.map render).toList})"
  | _ => s!"⟪{t}⟫"

/-- info:
((x + 1) < (2 * y))
((b[3:0] = #b0001) → (if p then (y < x) else ⟪(bvult b #b00000001)⟫))
(f(x, p) < 7)
(∀ #[n], (n < x))
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let p ← Term.mkSymbol (← Srt.bool) "p"
  let b ← Term.mkSymbol (← Srt.bitVec 8) "b"
  let f ← Term.mkSymbol (← Srt.function #[int, ← Srt.bool] int) "f"
  let low ← Term.bvExtract 3 0 b
  println! render (← smt! x + 1 < 2 * y)
  let one ← Term.mkBitVec 8 1
  println! render (← smt!
    ![Term.equal low (← Term.mkBitVec 4 1)] → if p then y < x else ![Term.bvUlt b one])
  println! render (← smt! f x p < 7)
  println! render (← smt! ∀ (n : int), n < x)



/-! ## Folding

`Term.fold` visits every node in depth-first order, with the node's view; `pre` acts on reaching a
node and may skip its kids or stop, `post` on leaving it. Pure here: `Id`.
-/

/-- The symbols a term mentions, in order of first appearance, not looking under quantifiers. -/
def freeSymbols (t : Term) : Array String :=
  Id.run <| t.fold #[] (pre := fun _ v syms => match v with
    | .symbol name => return .descend (if syms.contains name then syms else syms.push name)
    | .forall' .. | .exists' .. => return .skip syms
    | _ => return .descend syms)

/-- info: #[x, y, k] -/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let k ← Term.mkSymbol int "k"
  println! freeSymbols (← smt! x < y ∧ (∀ (n : int), n < k + 1) ∧ y = k)



/-! ## Rewriting

`Term.walk` visits each node through a zipper and may replace it, with a term of the node's sort —
which is checked, since nothing here says what that sort is. `post` sees a node rebuilt with its
replaced kids, so a bottom-up rewrite is a `post` alone; rebuilding needs the term manager, so a
walk runs in a monad `Env` lifts into. Here, integer sums and products of literals are folded into
one.
-/

/-- Folds integer sums and products of literals, bottom-up, counting the folds. -/
def foldConstants (t : Term) : Env (Term × Nat) :=
  t.walk 0 (post := fun _ v n => do
    let (ks, unit, op) ← match v with
      | .add ks => pure (ks, 0, (· + ·))
      | .mul ks => pure (ks, 1, (· * ·))
      | _ => return .continue n
    let some ns := ks.val.toList.mapM (·.getIntValue?) | return .continue n
    return .replace (← Term.mkInt (ns.foldl op unit)) (n + 1))

/-- info: (and (< (+ x (* 2 3)) (+ 1 2 3)) (= y (* 4 (+ 1 1))))
  ↦ (and (< (+ x 6) 6) (= y 8)), 4 folds
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let t ← smt! x + 2 * 3 < +[1, 2, 3] ∧ y = 4 * (1 + 1)
  let (s, n) ← foldConstants t
  println! "{t}\n  ↦ {s}, {n} folds"

/-! A replacement of another sort is refused rather than built. -/

/-- info: cannot replace `p`, of sort `Bool`, by `0`, of sort `Int` -/
#guard_msgs in #eval Env.runIO do
  let p ← Term.mkSymbol (← Srt.bool) "p"
  let zero ← Term.mkInt 0
  try
    discard <| p.walk () (pre := fun _ (_ : V) _ => return .replace zero ())
  catch e => println! "{e}"



/-! ## Datatypes, records included

Constructors, selectors, updaters and testers are viewed generically, by name: which ones a
datatype has is a fact about its declaration. A record is a datatype to cvc5, so it is viewed the
same way, its constructor under the name cvc5 gives it.
-/

/-- info:
built by __cvc5_record_a_Int_b_Bool_ctor from #[7, true]
field a of (__cvc5_record_a_Int_b_Bool_ctor 7 true)
-/
#guard_msgs in #eval Env.runIO do
  let r ← smt! {a := 7, b := true}
  match V.of r with
  | .construct ctor args => println! "built by {ctor} from {args}"
  | _ => println! "something else"
  match V.of (← smt! ![return r].a) with
  | .selectField field arg => println! "field {field} of {arg}"
  | _ => println! "something else"
