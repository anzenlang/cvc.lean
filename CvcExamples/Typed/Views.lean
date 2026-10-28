/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed

public meta import Cvc.Typed



/-! # Taking typed terms apart

`def.term_view V` generates `V : Typ → Type`, the view of every imported theory: `V τ` is a term of
sort `τ` taken apart one level, its operator a constructor and its kids typed at their sorts.
Matching the sort alongside the view refines both — `.lt .int ks` gives `ks : Kids Int` — so a
function written against it reads kids at the Lean types they denote.

`Cvc.Typed.View` is the module that brings it in, with the traversals over it; `Cvc.Typed` imports
it, and every theory besides.
-/
namespace Cvc.Typed.Examples.Views

open Cvc Typed

public section variable [Ω]

def.term_view V

end

variable [Ω]



/-! ## A printer

One function over every sort: it takes `τ` and a term of that sort, and recurses at whatever sort a
kid has — `V.of` is the same for all of them. An application's arguments and a quantifier's
variables have sorts the node's own sort does not fix, so they come with the list of their sorts,
matching on which refines them.
-/

mutual

/-- A Lean-like rendering of a term, as far as this printer reaches. -/
partial def render (τ : Typ) (t : Term τ.Denote) : Env String := do
  let all (σ : Typ) (op : String) (ks : Kids σ.Denote) : Env String := do
    return "(" ++ s!" {op} ".intercalate (← ks.val.mapM (render σ)).toList ++ ")"
  match τ, ← V.of τ t with
  | _, .value t => return toString t
  | _, .symbol name => return name
  | _, .bvar x => return toString x.toTerm
  | _, .not t => return s!"¬{← render .bool t}"
  | _, .and ks => all .bool "∧" ks
  | _, .or ks => all .bool "∨" ks
  | _, .implies ks => all .bool "→" ks
  | τ, .ite c a b => return s!"(if {← render .bool c} then {← render τ a} else {← render τ b})"
  | _, .equal σ ks => all σ "=" ks
  | _, .lt σ ks => all σ "<" ks
  | τ, .add ks => all τ "+" ks
  | τ, .mul ks => all τ "*" ks
  | _, .intMod l r => return s!"({← render .int l} % {← render .int r})"
  -- the variables' sorts come with them
  | _, .forall' _ vars body _ =>
    return s!"(∀ {", ".intercalate vars.toStrings}, {← render .bool body})"
  | _, .exists' _ vars body _ =>
    return s!"(∃ {", ".intercalate vars.toStrings}, {← render .bool body})"
  -- the arguments' sorts refine the function and the arguments
  | _, .apply doms f args => return s!"{f}({", ".intercalate (← renderArgs doms args)})"
  | _, _ => return s!"⟪{t}⟫"

/-- An application's arguments, each rendered at its sort. -/
partial def renderArgs : (doms : List Typ) → View.Apply.Args doms → Env (List String)
  | [τ], .last t => return [← render τ t]
  | τ :: τs, .cons t rest => return (← render τ t) :: (← renderArgs τs rest)

end

/-- info:
((x + 1) < (2 * y))
(((x % 3) = 0) → (if p then (y < x) else ⟪(bvult b #b0001)⟫))
(f(x, p) < (if (g(x) ∧ p) then 0 else 7))
(∀ n : Int, k : Int, ((n < k) → (∃ m : Int, ((n < m) ∧ (m < k)))))
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  let p ← Term.mkSymbolAs Bool "p"
  let b ← Term.mkSymbolAs (BitVec 4) "b"
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  let g ← Term.mkSymbolAs (Int → Bool) "g"
  let one ← Term.mkBitVec 4 1
  println! ← render .bool (← smt! x + 1 < 2 * y)
  println! ← render .bool (← smt! x % 3 = 0 → if p then y < x else ![Term.bvUlt b one])
  println! ← render .bool (← smt! f x p < if g x ∧ p then 0 else 7)
  println! ← render .bool (← smt! ∀ (n k : Int), n < k → ∃ (m : Int), n < m ∧ m < k)



/-! ## Putting a term back together

What a view holds is enough to rebuild the node: an application's arguments convert back to the
spine `applyN` takes, a quantifier's variables to the `BVars` `mkForall` takes, with the
non-emptiness it asks for.
-/

/-- info:
(f x p) rebuilt: (f x p)
(forall ((n Int)) (exists ((m Int)) (< n m))) rebuilt, the same term: true
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let p ← Term.mkSymbolAs Bool "p"
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  let t ← smt! f x p
  match ← V.of .int t with
  | .apply _ f args => println! "{t} rebuilt: {← f.applyN args.toArgs}"
  | _ => println! "not an application"
  let q ← smt! ∀ (n : Int), ∃ (m : Int), n < m
  match ← V.of .bool q with
  | .forall' _ vars body _ =>
    let rebuilt ← Term.mkForall vars.toBVars body vars.toBVars_ne_nil
    println! "{q} rebuilt, the same term: {rebuilt == q}"
  | _ => println! "not a quantifier"



/-! ## Rewriting

`Term.walk` visits each node through a zipper and may replace it. A replacement is a term of the
node's sort — anything else is a type error — and `post` sees a node rebuilt with its replaced kids,
so a bottom-up rewrite is a `post` alone. Here, integer sums and products whose operands are all
literals are folded into one literal.
-/

/-- The integer literals `ks` are, if they all are. -/
def literals (ks : Kids Int) : Option (List Int) :=
  ks.val.toList.mapM fun k => (k.getIntValue.run).toOption

/-- Folds integer sums and products of literals, bottom-up, counting the folds. -/
def foldConstants (t : Term Bool) : Env (Term Bool × Nat) :=
  t.walk 0 (post := fun {τ} _ (v : V τ) n => match τ, v with
    | .int, .add ks => do
      let some ns := literals ks | return .continue n
      return .replace (← Term.mkInt (ns.foldl (· + ·) 0)) (n + 1)
    | .int, .mul ks => do
      let some ns := literals ks | return .continue n
      return .replace (← Term.mkInt (ns.foldl (· * ·) 1)) (n + 1)
    | _, _ => return .continue n)

/-- info: (and (< (+ x (* 2 3)) (+ 1 2 3)) (= y (* 4 (+ 1 1))))
  ↦ (and (< (+ x 6) 6) (= y 8)), 4 folds
-/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  let t ← smt! x + 2 * 3 < +[1, 2, 3] ∧ y = 4 * (1 + 1)
  let (s, n) ← foldConstants t
  println! "{t}\n  ↦ {s}, {n} folds"



/-! ## Generic code, and `Term.cast`

A kid is indexed by the *denotation* of its sort, `Typ.Denote σ`, which reduces to the Lean type
when the sort is known: at `.set .int`, a union's kids are `Term (Set Int)`. Code generic over an
element type `γ` only knows the sort as `Typ.of γ` — displayed unfolded, `ToTyp.typ γ` — and there
it does not reduce: the kids are `Term (Set (ToTyp.typ γ).Denote)`, which is not `Term (Set γ)`.
-/

/--
error: Application type mismatch: The argument
  ks.val
has type
  Array (Term (Set (ToTyp.typ γ).Denote))
but is expected to have type
  Array (Term (Set γ))
in the application
  some ks.val

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example [ToTyp γ] [Ord γ] (t : Term (Set γ)) : Env (Option (Array (Term (Set γ)))) := do
  match ← V.of (Typ.of (Set γ)) t.cast with
  | .setUnion ks => return some ks.val
  | _ => return none

/-! The two types index the same sort, which is what `Term.cast` asks: it moves a term to another
index, checking — by `rfl`, at compile time — that both are the same sort. The same cast puts the
caller's term at the index `V.of` takes. -/

/-- The operands of a union of `γ`-sets, at the caller's own index. -/
def unionOperands [ToTyp γ] [Ord γ] (t : Term (Set γ)) : Env (Option (Array (Term (Set γ)))) := do
  match ← V.of (Typ.of (Set γ)) t.cast with
  | .setUnion ks => return some (ks.val.map (·.cast))
  | _ => return none

/-- info: (some #[s, t]) -/
#guard_msgs in #eval Env.runIO do
  let s ← Term.mkSymbolAs (Set Int) "s"
  let t ← Term.mkSymbolAs (Set Int) "t"
  println! (← unionOperands (← smt! s ∪ t))



/-! ## A sort with no Lean type of its own

A declared sort the user names with their own type — `Loc` below — is viewed at its `Typ`, which
denotes `Sorted (.uninterpreted "Loc")`, a stand-in indexed by the sort. `Term.cast` moves a kid to
the user's type, and refuses at compile time a type of another sort.
-/

/-- A user's index for the uninterpreted sort `Loc`. -/
structure Loc where
instance : ToTyp Loc := ⟨.uninterpreted "Loc"⟩

/-- info: a location equality: #[a, b] -/
#guard_msgs in #eval Env.runIO do
  discard <| Srt.uninterpreted "Loc"
  let a ← Term.mkSymbolAs Loc "a"
  let b ← Term.mkSymbolAs Loc "b"
  match ← V.of .bool (← smt! a = b) with
  | .equal (.uninterpreted "Loc") ks =>
    let locs : Array (Term Loc) := ks.val.map (·.cast)
    println! "a location equality: {locs}"
  | _ => println! "something else"

/--
error: could not synthesize default value for parameter '_sameSort' using tactics
---
error: cannot cast: the two types index different sorts
inst✝ : Ω
t : Term (Sorted (Typ.uninterpreted "Loc"))
⊢ Typ.of (Sorted (Typ.uninterpreted "Loc")) = Typ.of Int
-/
#guard_msgs in
example (t : Term (Sorted (.uninterpreted "Loc"))) : Term Int := t.cast
