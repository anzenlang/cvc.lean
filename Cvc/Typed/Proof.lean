/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Typed.Core.Defs
import all Cvc.Typed.Core.Solver
public import Cvc.Typed.Core.Solver
public import Cvc.Untyped.Proof
import Std.Data.HashSet



/-! # Inspecting proofs, typed

The sort-erased `Cvc.Untyped.Proof` with formulas typed: a step's view holds its formulas — an
assumption, a pivot, a clause-form input — as `Term Bool`, and `freeAssumptions` answers them so.

A term that is not a formula — `REFL`'s term, `CONG`'s application, a rewrite's instantiation —
stays **sort-erased**, as `Solver.Proof.getArguments` does: a rule fixes no sort for it, so there is
no index to give it, and `Untyped.Term.typeCheck` is the way to put one on.

The decoding is the sort-erased one; each formula is then checked to be Boolean, and a step whose
formulas are not falls back to `other`, so a `Term Bool` here is never a guess.
-/

namespace Cvc.Typed public section variable [Ω]

/-- A step of a typed proof, taken apart: formulas as `Term Bool`, other terms sort-erased. -/
abbrev Solver.ProofView (s : Solver) (pc : Proof.Component) : Type :=
  Cvc.Proof.View (s.Proof pc) (Term Bool) Untyped.Term

namespace Solver.Proof

/-- A sort-erased formula as a `Term Bool`, if it is Boolean. -/
private def formula? (t : Untyped.Term) : Option (Term Bool) :=
  match t.getSort? with
  | some srt => if srt.isBool then some t else none
  | none => none

variable {s : Solver} (p : s.Proof pc)



/-! ## Decoding a step -/

/-- The root step of `p`, taken apart, with `premises` standing for its premises.

What `view` and `foldUp` are built on: `view` passes the premises themselves, `foldUp` what it
computed for them. `premises` is expected to hold one element per premise, in order, as
`getChildren` does; a step whose premises do not match its rule's layout is `other`, and so is one
with a formula that is not Boolean.
-/
def viewWith (premises : Array X) : Cvc.Proof.View X (Term Bool) Untyped.Term :=
  let v := Untyped.Solver.Proof.viewWith p.relax premises
  v.mapM (m := Option) pure formula? pure
  |>.getD (.other p.getRule premises p.getArguments)

/-- The root step of `p`, taken apart: its rule as a constructor, its premises and arguments. -/
def view : s.ProofView pc := p.viewWith p.getChildren



/-! ## Traversing -/

@[inherit_doc Untyped.Solver.Proof.fold]
def fold [Monad m] (init : σ)
  (pre : s.Proof pc → s.ProofView pc → σ → m (FoldPre σ) := fun _ _ s => return .descend s)
  (post : s.Proof pc → s.ProofView pc → σ → m (FoldPost σ) := fun _ _ s => return .continue s)
  (revisit := false)
: m σ :=
  Cvc.Proof.foldWith (·.getChildren) (fun q => (q, q.view)) #[p] init
    (fun (q, v) s => pre q v s) (fun (q, v) s => post q v s) revisit

@[inherit_doc Untyped.Solver.Proof.foldUp]
def foldUp [Monad m] (f : s.Proof pc → Cvc.Proof.View β (Term Bool) Untyped.Term → m β) : m β := do
  let premises ← Cvc.Proof.foldUpWith (·.getChildren) (fun q bs => f q (q.viewWith bs))
    p.getChildren
  f p (p.viewWith premises)

/-- `for step in p do …` visits the distinct steps of `p`, in the order `fold` enters them.

`break` ends the loop.
-/
instance [Monad m] : ForIn m (s.Proof pc) (s.Proof pc) where
  forIn p init f :=
    Cvc.Proof.foldWith (·.getChildren) id #[p] init
      (fun q b => do
        match ← f q b with
        | .done b => return .stop b
        | .yield b => return .descend b)
      (fun _ b => return .continue b)



/-! ## Questions about a proof -/

@[inherit_doc Untyped.Solver.Proof.size]
def size : Nat := Id.run do
  let mut n := 0
  for _ in p do n := n + 1
  return n

@[inherit_doc Untyped.Solver.Proof.ruleCounts]
def ruleCounts : Array (ProofRule × Nat) := Id.run do
  let mut counts : Array (ProofRule × Nat) := #[]
  for q in p do
    let rule := q.getRule
    counts := match counts.findIdx? (·.1 == rule) with
      | some i => counts.modify i fun (r, n) => (r, n + 1)
      | none => counts.push (rule, 1)
  return counts

@[inherit_doc Untyped.Solver.Proof.freeAssumptions]
def freeAssumptions : Terms Bool :=
  p.foldUp (m := Id) fun _ v => match v with
    | .assume f => #[f]
    | .scope body discharged => body.filter (!discharged.contains ·)
    | v => Id.run do
      let mut seen : Std.HashSet (Term Bool) := {}
      let mut all := #[]
      for fs in v.premises do
        for f in fs do
          if !seen.contains f then
            seen := seen.insert f
            all := all.push f
      return all

@[inherit_doc Untyped.Solver.Proof.trusted]
def trusted : s.Proofs pc := Id.run do
  let mut steps := #[]
  for q in p do
    if q.getRule == .TRUST || q.getRule == .TRUST_THEORY_REWRITE then steps := steps.push q
  return steps

end Solver.Proof

namespace Solver.Proofs variable {s : Solver} (ps : s.Proofs pc)

@[inherit_doc Untyped.Solver.Proofs.fold]
def fold [Monad m] (init : σ)
  (pre : s.Proof pc → s.ProofView pc → σ → m (FoldPre σ) := fun _ _ s => return .descend s)
  (post : s.Proof pc → s.ProofView pc → σ → m (FoldPost σ) := fun _ _ s => return .continue s)
  (revisit := false)
: m σ :=
  Cvc.Proof.foldWith (·.getChildren) (fun q => (q, q.view)) ps init
    (fun (q, v) s => pre q v s) (fun (q, v) s => post q v s) revisit

@[inherit_doc Untyped.Solver.Proofs.foldUp]
def foldUp [Monad m] (f : s.Proof pc → Cvc.Proof.View β (Term Bool) Untyped.Term → m β)
: m (Array β) :=
  Cvc.Proof.foldUpWith (·.getChildren) (fun q bs => f q (q.viewWith bs)) ps

end Solver.Proofs

end

end Cvc.Typed
