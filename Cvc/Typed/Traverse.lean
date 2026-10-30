/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Traverse
public import Cvc.Typed.Core.View



/-! # Folding over typed terms, and walking them with a zipper

`Term.fold` visits a term's nodes; `Term.walk` visits them through a zipper and can replace them.
Both hand each node to the user as its view at its sort — through `ViewFamily`, which
`def.term_view V` instantiates — and both take four optional functions: `pre` and `post` for a node
whose sort a `Typ` describes, called on reaching it and on leaving it, and `prePlain` and
`postPlain` for any other node — a constructor at the head of an application, a quantifier's
variable list, a term of a parametric datatype. Every node is visited, by one pair or the other.

**Both run in a monad `Env` lifts into.** Presenting a node reads its sort, which the library does
in `Env`, and a walk rebuilds what it replaced under, which goes through the term manager.

The order, the steps and the zipper are the sort-erased ones, `Cvc.Untyped.Traverse`, with each
node's sort carried as the zipper's payload. What the index adds is in the replacements: a typed
node's is a term of its sort, so it cannot be ill-sorted, while a plain node's is checked.
-/

namespace Cvc.Typed public section variable [Ω]

/-! ## Folding -/

/-- A node as a typed fold presents it: at its sort if a `Typ` describes it, erased otherwise. -/
private inductive FoldNode (V : Typ → Type) where
  | typed (τ : Typ) (t : Term τ.Denote) (v : V τ)
  | plain (t : Untyped.Term)

/-- Presents a node: reads its sort, and views it if a `Typ` describes it. -/
private def FoldNode.of [ViewFamily V] (u : Untyped.Term) : Env (FoldNode V) := do
  match ← View.typOf? u with
  | some τ =>
    let t : Term τ.Denote := View.reindex u
    return .typed τ t (← ViewFamily.viewOf τ t)
  | none => return .plain u

/-- Folds over a term's nodes, in depth-first order, with early exit.

Each node is entered — `pre`, or `prePlain` if no `Typ` describes its sort — then, unless that
answered `skip`, its kids are folded over left to right, and then it is left — `post` or
`postPlain`. `pre` and `post` take the node at its sort, with its view, so matching on the view
refines the sort. Every function defaults to carrying on, so a fold passes only those it needs.
-/
def Term.fold [Monad m] [MonadLiftT Env m] [ViewFamily V] (t : Term ρ) (init : σ)
  (pre : {τ : Typ} → Term τ.Denote → V τ → σ → m (FoldPre σ) := fun _ _ s => return .descend s)
  (post : {τ : Typ} → Term τ.Denote → V τ → σ → m (FoldPost σ) :=
    fun _ _ s => return .continue s)
  (prePlain : Untyped.Term → σ → m (FoldPre σ) := fun _ s => return .descend s)
  (postPlain : Untyped.Term → σ → m (FoldPost σ) := fun _ s => return .continue s)
: m σ :=
  Untyped.foldWith (fun u => monadLift (FoldNode.of u : Env (FoldNode V))) t.relax init
    (fun n s => match n with
      | .typed _ t v => pre t v s
      | .plain u => prePlain u s)
    (fun n s => match n with
      | .typed _ t v => post t v s
      | .plain u => postPlain u s)



/-! ## The zipper

A position in a `Term ρ`, indexed by the root's Lean type and by the focus's sort: `some τ` if a
`Typ` describes it, `none` otherwise. Nothing about the path is at the type level. An edit replaces
the focus by a term of the same sort — statically for `replace`, checked for `replacePlain` — so
every ancestor keeps its sort and `root` answers a `Term ρ`. Moving answers a `Zipper.Any`, the
sort of where it lands being read off the term.
-/

/-- A position in a `Term ρ`, focused on a node whose sort is `s`. -/
structure Zipper (ρ : Type) (s : Option Typ) where
  private mk ::
  /-- The sort-erased zipper, each node's payload its sort; the focus's is `s`. -/
  private raw : Untyped.ZipperOf (Option Typ)

/-- A zipper at whatever sort its focus has. -/
abbrev Zipper.Any (ρ : Type) := (s : Option Typ) × Zipper ρ s

/-- What the focus is, by its sort: a typed term, or a sort-erased one. -/
abbrev Zipper.Focus : Option Typ → Type
  | some τ => Term τ.Denote
  | none => Untyped.Term

namespace Zipper

/-- A sort-erased zipper, at the sort its payload says. -/
private def ofRaw (z : Untyped.ZipperOf (Option Typ)) : Zipper.Any ρ := ⟨z.payloadOf, ⟨z⟩⟩

/-- A zipper focused on a term's root. -/
def ofTerm (t : Term ρ) : Env (Zipper.Any ρ) := do
  return ofRaw (.ofTerm t.relax (← View.typOf? t.relax))

/-- The focus. -/
def focus : Zipper ρ s → Focus s :=
  match s with
  | some _ => fun z => View.reindex z.raw.focus
  | none => fun z => z.raw.focus

/-- The focus, sort-erased. -/
def relaxedFocus (z : Zipper ρ s) : Untyped.Term := z.raw.focus

/-- The focus's view. -/
def view [ViewFamily V] (z : Zipper ρ (some τ)) : Env (V τ) := ViewFamily.viewOf τ z.focus

/-- How deep the focus is: `0` at the root. -/
def depth (z : Zipper ρ s) : Nat := z.raw.depth

/-- Focuses on the `i`-th kid, if there is one. -/
def down (z : Zipper ρ s) (i : Nat) : Env (Option (Zipper.Any ρ)) := do
  return (← z.raw.downWith View.typOf? i).map ofRaw

/-- Focuses on the next sibling, if there is one. -/
def right (z : Zipper ρ s) : Env (Option (Zipper.Any ρ)) := do
  return (← z.raw.rightWith View.typOf?).map ofRaw

/-- Focuses on the previous sibling, if there is one. -/
def left (z : Zipper ρ s) : Env (Option (Zipper.Any ρ)) := do
  return (← z.raw.leftWith View.typOf?).map ofRaw

/-- Focuses on the parent, if there is one, rebuilding it if anything below it was replaced. -/
def up (z : Zipper ρ s) : Env (Option (Zipper.Any ρ)) := do
  return (← z.raw.up).map ofRaw

/-- The whole term, with every replacement made. -/
def root (z : Zipper ρ s) : Env (Term ρ) := do
  return View.reindex (← z.raw.root)

/-- Replaces the focus by a term of its sort. -/
def replace (z : Zipper ρ (some τ)) (t : Term τ.Denote) : Zipper ρ (some τ) :=
  ⟨z.raw.replaceUnchecked t.relax⟩

/-- Replaces a sort-erased focus, checking that the replacement has the focus's sort. -/
def replacePlain (z : Zipper ρ none) (t : Untyped.Term) : Env (Zipper ρ none) := do
  Untyped.checkSameSort z.raw.focus t
  return ⟨z.raw.replaceUnchecked t⟩

/-- The whole term, with every replacement made. -/
def Any.root (z : Zipper.Any ρ) : Env (Term ρ) := z.2.root

end Zipper



/-! ## Walking -/

/-- Walks a term's nodes through a zipper, in depth-first order, replacing some.

The same order as `Term.fold`, and the same four functions, each handed the zipper focused on the
node — so it sees the node's context too — and answering whether to replace it. A typed node's
replacement is a term of its sort; a plain node's is checked against its sort. `post` sees a node
rebuilt with its replaced kids. Answers the rebuilt term with the final state, `stop` included.
-/
def Term.walk [Monad m] [MonadLiftT Env m] [ViewFamily V] (t : Term ρ) (init : σ)
  (pre : {τ : Typ} → Zipper ρ (some τ) → V τ → σ → m (WalkPre σ (Term τ.Denote)) :=
    fun _ _ s => return .descend s)
  (post : {τ : Typ} → Zipper ρ (some τ) → V τ → σ → m (WalkPost σ (Term τ.Denote)) :=
    fun _ _ s => return .continue s)
  (prePlain : Zipper ρ none → σ → m (WalkPre σ Untyped.Term) := fun _ s => return .descend s)
  (postPlain : Zipper ρ none → σ → m (WalkPost σ Untyped.Term) := fun _ s => return .continue s)
: m (Term ρ × σ) := do
  let z₀ := Untyped.ZipperOf.ofTerm t.relax (← (View.typOf? t.relax : Env _))
  let (u, s) ← Untyped.ZipperOf.walkWith (fun k => monadLift (View.typOf? k)) z₀ init
    (fun z s => do
      match z.payloadOf with
      | some τ =>
        let zt : Zipper ρ (some τ) := ⟨z⟩
        return (← pre zt (← (zt.view : Env _)) s).map Term.relax
      | none =>
        let step ← prePlain ⟨z⟩ s
        match step with
        | .replace r _ | .replaceAndRevisit r _ => (Untyped.checkSameSort z.focus r : Env _)
        | _ => pure ()
        return step)
    (fun z s => do
      match z.payloadOf with
      | some τ =>
        let zt : Zipper ρ (some τ) := ⟨z⟩
        return (← post zt (← (zt.view : Env _)) s).map Term.relax
      | none =>
        let step ← postPlain ⟨z⟩ s
        match step with
        | .replace r _ | .replaceAndRevisit r _ => (Untyped.checkSameSort z.focus r : Env _)
        | _ => pure ()
        return step)
  return (View.reindex u, s)

end

end Cvc.Typed
