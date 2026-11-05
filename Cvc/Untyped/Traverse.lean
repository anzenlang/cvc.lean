/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module


public import Cvc.Untyped.Core.View



/-! # Folding over terms, and walking them with a zipper

`Term.fold` visits a term's nodes; `Term.walk` visits them through a zipper and can replace them.
Both hand each node to the user as its **view**, the inductive `def.term_view V` generates, and both
take two optional functions: `pre`, called on reaching a node, before its kids, and `post`, called
on leaving it, after them. Each answers what to do next — descend, skip the kids, stop, and for a
walk replace the node — along with the new state.

**`fold` runs in any monad.** Taking a term apart is pure, and the only failure, an ill-formed term,
is one cvc5 never builds. **`walk` needs `Env`**, to rebuild what it replaced under: building a term
goes through the term manager.

The machinery is written once, here, and shared with the typed layer: the zipper carries a payload
per node, which the typed layer uses for each node's sort, and `foldWith`/`walkWith` take how a
node is presented to the user's functions.
-/

namespace Cvc public section

/-- What a fold does on reaching a node, before its kids. -/
inductive FoldPre (σ : Type) where
  /-- Visit the kids. -/
  | descend (s : σ)
  /-- Do not visit the kids; the node is still left, `post` and all. -/
  | skip (s : σ)
  /-- End the fold. -/
  | stop (s : σ)

/-- What a fold does on leaving a node, after its kids. -/
inductive FoldPost (σ : Type) where
  /-- Carry on. -/
  | continue (s : σ)
  /-- End the fold. -/
  | stop (s : σ)

/-- What a walk does on reaching a node, before its kids. `R` is what replaces the node. -/
inductive WalkPre (σ R : Type) where
  /-- Visit the kids. -/
  | descend (s : σ)
  /-- Do not visit the kids; the node is still left, `post` and all. -/
  | skip (s : σ)
  /-- Replace the node, without visiting the replacement; it is then left. -/
  | replace (t : R) (s : σ)
  /-- Replace the node and visit the replacement, from `pre`. -/
  | replaceAndRevisit (t : R) (s : σ)
  /-- End the walk, keeping every replacement made. -/
  | stop (s : σ)

/-- What a walk does on leaving a node, after its kids. `R` is what replaces the node. -/
inductive WalkPost (σ R : Type) where
  /-- Carry on. -/
  | continue (s : σ)
  /-- Replace the node, and carry on. -/
  | replace (t : R) (s : σ)
  /-- Replace the node and visit the replacement, from `pre`. -/
  | replaceAndRevisit (t : R) (s : σ)
  /-- End the walk, keeping every replacement made. -/
  | stop (s : σ)

/-- The same step, its replacement mapped. -/
def WalkPre.map (f : R → R') : WalkPre σ R → WalkPre σ R'
  | .descend s => .descend s
  | .skip s => .skip s
  | .replace t s => .replace (f t) s
  | .replaceAndRevisit t s => .replaceAndRevisit (f t) s
  | .stop s => .stop s

/-- The same step, its replacement mapped. -/
def WalkPost.map (f : R → R') : WalkPost σ R → WalkPost σ R'
  | .continue s => .continue s
  | .replace t s => .replace (f t) s
  | .replaceAndRevisit t s => .replaceAndRevisit (f t) s
  | .stop s => .stop s

end

namespace Untyped public section variable [Ω]

/-! ## Folding -/

/-- A pending step of a fold. -/
private inductive FoldTask (N : Type) where
  | enter (t : Term)
  | leave (n : N)

/-- Folds over a term's nodes, presented as `present` builds them: what `Term.fold` and its typed
counterpart are built on.

Depth-first: each node is entered — `pre` — then, unless that answered `skip`, its kids are folded
over left to right, and then it is left — `post`.
-/
def foldWith [Monad m] (present : Term → m N) (t : Term) (init : σ)
  (pre : N → σ → m (FoldPre σ)) (post : N → σ → m (FoldPost σ))
: m σ := do
  let mut tasks : List (FoldTask N) := [.enter t]
  let mut s := init
  repeat
    match tasks with
    | [] => break
    | .enter u :: rest =>
      let n ← present u
      match ← pre n s with
      | .descend s' => s := s'; tasks := u.getKids.toList.map .enter ++ .leave n :: rest
      | .skip s' => s := s'; tasks := .leave n :: rest
      | .stop s' => return s'
    | .leave n :: rest =>
      match ← post n s with
      | .continue s' => s := s'; tasks := rest
      | .stop s' => return s'
  return s

/-- Folds over a term's nodes, in depth-first order, with early exit.

Each node is handed over with its view. Both functions default to carrying on, so a fold passes only
those it needs: `pre` to act on reaching a node, and to skip its kids; `post` to act on leaving it,
once its kids are done. Runs in any monad.
-/
def Term.fold [Monad m] [TermView V] (t : Term) (init : σ)
  (pre : Term → V → σ → m (FoldPre σ) := fun _ _ s => return .descend s)
  (post : Term → V → σ → m (FoldPost σ) := fun _ _ s => return .continue s)
: m σ :=
  foldWith (fun u => return (u, TermView.viewOf u)) t init
    (fun (u, v) s => pre u v s) (fun (u, v) s => post u v s)



/-! ## The zipper

A position in a term: the focus, and the path back to the root. Each node carries a payload `P`,
computed when the zipper reaches it — nothing for the sort-erased `Zipper`, its sort for the typed
one. Nothing about the path is at the type level: an edit replaces the focus by a term of the same
sort, so every ancestor keeps its sort.
-/

/-- One ancestor of the focus, as the path to the root holds it. -/
structure ZipperOf.Frame (P : Type) where
  private mk ::
  /-- The ancestor, as it was before anything below it was replaced. -/
  private parent : Term
  /-- The ancestor's payload. -/
  private payload : P
  /-- Whether the ancestor itself is a replacement, unknown to its own parent. -/
  private parentDirty : Bool
  /-- The kids left of the focus, in order. -/
  private left : Terms
  /-- The kids right of the focus, in order. -/
  private right : List Term
  /-- Whether a kid other than the focus was replaced. -/
  private dirty : Bool

/-- A position in a term, each node carrying a payload `P`. -/
structure ZipperOf (P : Type) where
  private mk ::
  private term : Term
  private payload : P
  /-- Whether the focus was replaced, unknown to its parent. -/
  private dirty : Bool
  private path : List (ZipperOf.Frame P)

namespace ZipperOf

/-- A zipper focused on a term's root. -/
def ofTerm (t : Term) (payload : P) : ZipperOf P := ⟨t, payload, false, []⟩

/-- The focus. -/
def focus (z : ZipperOf P) : Term := z.term

/-- The focus's payload. -/
def payloadOf (z : ZipperOf P) : P := z.payload

/-- How deep the focus is: `0` at the root. -/
def depth (z : ZipperOf P) : Nat := z.path.length

/-- Focuses on the `i`-th kid, if there is one, computing its payload. -/
def downWith [Monad m] (pay : Term → m P) (z : ZipperOf P) (i : Nat)
: m (Option (ZipperOf P)) := do
  let kids := z.term.getKids
  if h : i < kids.size then
    let k := kids[i]
    let frame : Frame P := {
      parent := z.term, payload := z.payload, parentDirty := z.dirty
      left := kids.extract 0 i, right := (kids.extract (i + 1)).toList, dirty := false
    }
    return some ⟨k, ← pay k, false, frame :: z.path⟩
  return none

/-- Focuses on the next sibling, if there is one, computing its payload. -/
def rightWith [Monad m] (pay : Term → m P) (z : ZipperOf P) : m (Option (ZipperOf P)) := do
  let f :: fs := z.path | return none
  let k :: ks := f.right | return none
  let frame := { f with left := f.left.push z.term, right := ks, dirty := f.dirty || z.dirty }
  return some ⟨k, ← pay k, false, frame :: fs⟩

/-- Focuses on the previous sibling, if there is one, computing its payload. -/
def leftWith [Monad m] (pay : Term → m P) (z : ZipperOf P) : m (Option (ZipperOf P)) := do
  let f :: fs := z.path | return none
  let some k := f.left.back? | return none
  let frame :=
    { f with left := f.left.pop, right := z.term :: f.right, dirty := f.dirty || z.dirty }
  return some ⟨k, ← pay k, false, frame :: fs⟩

/-- Focuses on the parent, if there is one, rebuilding it if anything below it was replaced. -/
def up (z : ZipperOf P) : Env (Option (ZipperOf P)) := do
  let f :: fs := z.path | return none
  if z.dirty || f.dirty then
    let parent ← f.parent.replaceKids (f.left.push z.term ++ f.right.toArray)
    return some ⟨parent, f.payload, true, fs⟩
  return some ⟨f.parent, f.payload, f.parentDirty, fs⟩

/-- The whole term, with every replacement made. -/
partial def root (z : ZipperOf P) : Env Term := do
  match ← z.up with
  | some z => z.root
  | none => return z.term

/-- Replaces the focus, unchecked: the caller guarantees the replacement has the focus's sort, which
is what keeps every ancestor well-sorted. -/
def replaceUnchecked (z : ZipperOf P) (t : Term) : ZipperOf P := ⟨t, z.payload, true, z.path⟩

/-- Walks a term's nodes through a zipper, presented as the functions see fit: what `Term.walk` and
its typed counterpart are built on.

Depth-first: `pre` on reaching a node, then — unless it skipped, replaced or stopped — its kids,
then `post` on leaving it. A replacement is unchecked; a `stop` keeps every replacement made.
Answers the rebuilt term and the final state.
-/
def walkWith [Monad m] [MonadLiftT Env m] (pay : Term → m P) (z₀ : ZipperOf P) (init : σ)
  (pre : ZipperOf P → σ → m (WalkPre σ Term)) (post : ZipperOf P → σ → m (WalkPost σ Term))
: m (Term × σ) := do
  let mut z := z₀
  let mut entering := true
  let mut s := init
  repeat
    if entering then
      match ← pre z s with
      | .descend s' =>
        s := s'
        match ← z.downWith pay 0 with
        | some z' => z := z'
        | none => entering := false
      | .skip s' => s := s'; entering := false
      | .replace r s' => s := s'; z := z.replaceUnchecked r; entering := false
      | .replaceAndRevisit r s' => s := s'; z := z.replaceUnchecked r
      | .stop s' => return (← (z.root : Env _), s')
    else
      -- leaving: `post`, then on to the next sibling, or up to leave the parent
      let mut advance := true
      match ← post z s with
      | .continue s' => s := s'
      | .replace r s' => s := s'; z := z.replaceUnchecked r
      | .replaceAndRevisit r s' =>
        s := s'; z := z.replaceUnchecked r; entering := true; advance := false
      | .stop s' => return (← (z.root : Env _), s')
      if advance then
        match ← z.rightWith pay with
        | some z' => z := z'; entering := true
        | none =>
          match ← (z.up : Env _) with
          | some z' => z := z'
          | none => return (← (z.root : Env _), s)
  return (← (z.root : Env _), s)

end ZipperOf



/-! ## The sort-erased zipper -/

/-- A position in a sort-erased term. -/
abbrev Zipper := ZipperOf Unit

namespace ZipperOf

/-- A sort-erased zipper focused on a term's root. -/
def ofTermErased (t : Term) : Zipper := .ofTerm t ()

/-- The focus's view. -/
def view [TermView V] (z : Zipper) : V := TermView.viewOf z.focus

/-- Focuses on the `i`-th kid, if there is one. -/
def down (z : Zipper) (i : Nat) : Option Zipper := Id.run (z.downWith (fun _ => return ()) i)

/-- Focuses on the next sibling, if there is one. -/
def right (z : Zipper) : Option Zipper := Id.run (z.rightWith fun _ => return ())

/-- Focuses on the previous sibling, if there is one. -/
def left (z : Zipper) : Option Zipper := Id.run (z.leftWith fun _ => return ())

end ZipperOf

/-- Fails unless a replacement has the sort of what it replaces: the check that keeps every ancestor
well-sorted. -/
def checkSameSort (old new : Term) : Env Unit := do
  let (oldSrt, newSrt) := (← old.getSort, ← new.getSort)
  unless oldSrt == newSrt do
    throwUser s!"cannot replace `{old}`, of sort `{oldSrt}`, by `{new}`, of sort `{newSrt}`"

/-- Replaces the focus, checking that the replacement has the focus's sort. -/
def ZipperOf.replace (z : Zipper) (t : Term) : Env Zipper := do
  checkSameSort z.focus t
  return z.replaceUnchecked t

/-- Walks a term's nodes through a zipper, in depth-first order, replacing some.

The same order as `Term.fold`, and the same two optional functions, each handed the zipper focused
on the node — so it sees the node's context too — and its view, and answering whether to replace it.
A replacement must have the sort of the node it replaces, which is checked. `post` sees a node
rebuilt with its replaced kids. Answers the rebuilt term with the final state, `stop` included.

Runs in any monad `Env` lifts into: rebuilding a term goes through the term manager.
-/
def Term.walk [Monad m] [MonadLiftT Env m] [TermView V] (t : Term) (init : σ)
  (pre : Zipper → V → σ → m (WalkPre σ Term) := fun _ _ s => return .descend s)
  (post : Zipper → V → σ → m (WalkPost σ Term) := fun _ _ s => return .continue s)
: m (Term × σ) :=
  ZipperOf.walkWith (fun _ => return ()) (.ofTermErased t) init
    (fun z s => do
      let step ← pre z z.view s
      match step with
      | .replace r _ | .replaceAndRevisit r _ => (checkSameSort z.focus r : Env _)
      | _ => pure ()
      return step)
    (fun z s => do
      let step ← post z z.view s
      match step with
      | .replace r _ | .replaceAndRevisit r _ => (checkSameSort z.focus r : Env _)
      | _ => pure ()
      return step)

end

end Untyped

end Cvc
