/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module



/-! # What a traversal does next

The answers a traversal's `pre` and `post` functions give, shared by everything that folds or walks:
the terms of both layers (`Cvc.Untyped.Term.fold`, `Cvc.Typed.Term.walk`, …) and proofs
(`Cvc.Untyped.Solver.Proof.fold`, …). Each carries the new state, and says whether to descend,
skip, stop, or — for a walk — replace the node.
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

end Cvc
