/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc
public meta import Cvc
public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Cvc



set_option pp.rawOnError true



#doc (Manual) "Taking Terms Apart" =>
%%%
tag := "views"
htmlSplit := .never
%%%

Building terms is half of the story: a solver hands terms back — models, unsat cores, proofs, synthesized functions — and a rewrite has to look inside a term before it replaces it. cvc.lean takes a term apart through a *view*: the term one level down, its operator as a constructor and its kids, indices and names as fields.

`import Cvc.Typed.View` (or `Cvc.Untyped.View`) brings in everything this chapter uses; `import Cvc` includes it.

# The View of the Imported Theories

Each theory comes with a view of its operators, and `def.term_view V` gathers the views of every theory the current module imports into one inductive `V`. A theory that is not imported is not viewed: its terms fall into `V`'s catch-all, `other`. Besides one constructor per operator, `V` has leaves for values, declared symbols and bound variables.

```lean
section
variable [Ω]
open Typed
def.term_view V
end
```

In the typed layer `V : Typ → Type`: `V τ` is a term of sort `τ` taken apart. Each operator has a constructor whose kids are typed at their sorts — a comparison's operand sort is a field, which types its kids:

```lean (name := views_lt)
#check @V.lt
```
```leanOutput views_lt
@V.lt : [inst : Ω] → (α : Typ) → {h0 : α.isArith = true} → Typed.Kids α.Denote → V Typ.bool
```

`V.of τ t` views a term `t` of sort `τ`. Matching on the sort *alongside* the view refines both: at `.lt .int ks`, the kids `ks` are `Term Int`s.

```lean (name := views_of)
open Typed in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let t ← smt! x + 1 < 2 * x
  match ← V.of .bool t with
  | .lt .int ks =>
    let kids : Array (Term Int) := ks.val
    println! "an integer comparison of {kids}"
  | _ => println! "something else"
```
```leanOutput views_of
an integer comparison of #[(+ x 1), (* 2 x)]
```

Matching at the wrong sort is caught statically: the kids of a real comparison are not integers.

```lean +error (name := views_bad)
open Typed in
example [Ω] (v : V .bool) : Option (Kids Int) :=
  match v with
  | .lt .real ks => some ks
  | _ => none
```
```leanOutput views_bad
Application type mismatch: The argument
  ks
has type
  Kids Rat
but is expected to have type
  Kids Int
in the application
  some ks

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
```

# Folding and Rewriting

`Term.fold` visits a term's nodes depth first, handing each to two optional functions with its view: `pre` on reaching the node, which may skip its kids or stop the fold, and `post` on leaving it. The typed layer has two more, `prePlain` and `postPlain`, for the nodes whose sort has no `Typ` — a quantifier's variable list, for instance.

```lean (name := views_fold)
open Typed in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  let t ← smt! x < y ∧ y = x + 1
  let syms ← t.fold #[] (pre := fun {τ} _ (v : V τ) acc =>
    match τ, v with
    | .int, .symbol x =>
      if acc.contains x then return .descend acc
      else return .descend (acc.push x)
    | _, _ => return .descend acc)
  println! "integer symbols: {syms}"
```
```leanOutput views_fold
integer symbols: #[x, y]
```

`Term.walk` visits the nodes through a *zipper*, which also sees where the node sits, and may replace a node. A typed node's replacement is a term of its sort, so a rewrite cannot build an ill-sorted term; a sort-erased replacement is checked. `post` sees a node rebuilt with its replaced kids, so a bottom-up rewrite is a `post` alone — here, removing double negations:

```lean (name := views_walk)
open Typed in #eval Env.runIO do
  let p ← Term.mkSymbolAs Bool "p"
  let q ← Term.mkSymbolAs Bool "q"
  let t ← smt! ¬ ¬ p ∧ ¬ ¬ ¬ q
  let (s, _) ← t.walk () (post := fun {τ} _ (v : V τ) _ =>
    match τ, v with
    | .bool, .not t => do
      match ← V.of .bool t with
      | .not u => return .replace u ()
      | _ => return .continue ()
    | _, _ => return .continue ())
  println! "{t} ↦ {s}"
```
```leanOutput views_walk
(and (not (not p)) (not (not (not q)))) ↦ (and p (not q))
```

The sort-erased layer works the same way, without the sorts: `V.of` is a pure function there, and a fold runs in any monad.
