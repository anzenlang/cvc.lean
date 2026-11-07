/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Untyped.Core.Defs
public import Cvc.Untyped.Core.Solver
public import Cvc.Proof
import Std.Data.HashSet



/-! # Inspecting proofs, sort-erased

A proof is what an unsat answer can be asked for, with `Solver.getUnsatProof`. This module takes
one apart:

- `Solver.Proof.view` answers the root step as a `Cvc.Proof.View`, its rule a constructor and its
  premises and arguments fields;
- `Solver.Proof.fold` visits the distinct steps depth-first, with early exit, in any monad, and
  `for step in proof do …` does the same through `ForIn`;
- `Solver.Proof.foldUp` computes a value for every distinct step from its premises' values, which
  is the shape of anything that rebuilds a proof elsewhere;
- `size`, `ruleCounts`, `freeAssumptions` and `trusted` answer the usual questions.

`Solver.Proofs.fold` and `Solver.Proofs.foldUp` do the same over several proofs at once, sharing
what they visit, which is what the components other than `full` answer: one proof per theory lemma,
for instance.

Every traversal visits a step shared by many others once, as `Cvc.Proof` explains.
-/

namespace Cvc.Untyped public section variable [Ω]

/-- A step of a sort-erased proof, taken apart: `Cvc.Proof.View` over sort-erased terms. -/
abbrev Solver.ProofView (s : Solver) (pc : Proof.Component) : Type :=
  Cvc.Proof.View (s.Proof pc) Term Term

namespace Solver.Proof



/-! ## Decoding a step -/

/-- An argument cvc5 encodes as a natural number: an index, or an identifier. -/
private def natArg? (t : Term) : Option Nat :=
  match cvc5.Term.getIntegerValue? t with
  | some i => if 0 ≤ i then some i.toNat else none
  | none => none

/-- A list argument: cvc5 packs one into an s-expression, the kids of which are the elements. -/
private def listArg (t : Term) : Terms :=
  if t.getKind? == some .SEXPR then t.getKids else #[t]

/-- The steps of a chain resolution over `premises` premises, from its polarities and pivots. -/
private def stepsArg? (pols pivots : Term) (premises : Nat) : Option (Array (Bool × Term)) := do
  let pols := listArg pols
  let pivots := listArg pivots
  guard (pols.size = pivots.size ∧ pols.size + 1 = premises)
  return (← pols.mapM (·.getBoolValue?)).zip pivots

/-- One premise and no argument. -/
private def unary (ps : Array X) (args : Terms) (mk : X → V) : Option V := do
  let #[p] := ps | none
  let #[] := args | none
  return mk p

/-- Two premises and no argument. -/
private def binary (ps : Array X) (args : Terms) (mk : X → X → V) : Option V := do
  let #[p, q] := ps | none
  let #[] := args | none
  return mk p q

/-- No premise and a single argument. -/
private def leaf (ps : Array X) (args : Terms) (mk : Term → V) : Option V := do
  let #[] := ps | none
  let #[t] := args | none
  return mk t

/-- No premise, an argument and an index. -/
private def indexedLeaf (ps : Array X) (args : Terms) (mk : Term → Nat → V) : Option V := do
  let #[] := ps | none
  let #[t, i] := args | none
  return mk t (← natArg? i)

/-- A step of rule `rule` with premises `ps` and arguments `args`, decoded, if it has the layout
cvc5 documents for that rule. -/
private def decode? (rule : ProofRule) (ps : Array X) (args : Terms)
  (rewrite : Option ProofRewriteRule)
: Option (Cvc.Proof.View X Term Term) :=
  match rule with
  -- assumptions
  | .ASSUME => leaf ps args .assume
  | .SCOPE => do
    let #[body] := ps | none
    return .scope body args
  -- rewriting
  | .EVALUATE => leaf ps args .evaluate
  | .DSL_REWRITE => do
    let _ :: instantiation := args.toList | none
    return .dslRewrite (← rewrite) ps instantiation.toArray
  | .THEORY_REWRITE => do
    let #[] := ps | none
    let #[_, _] := args | none
    return .theoryRewrite (← rewrite)
  | .ACI_NORM => leaf ps args fun _ => .aciNorm
  | .ABSORB => leaf ps args fun _ => .absorb
  -- trusted steps
  | .TRUST => do
    let id :: _ :: extra := args.toList | none
    return .trust (← natArg? id) ps extra.toArray
  | .TRUST_THEORY_REWRITE => do
    let #[] := ps | none
    let #[_, theory, method] := args | none
    return .trustTheoryRewrite (← natArg? theory) (← natArg? method)
  | .SAT_REFUTATION => do
    let #[] := args | none
    return .satRefutation ps
  -- resolution
  | .RESOLUTION => do
    let #[left, right] := ps | none
    let #[polarity, pivot] := args | none
    return .resolution left right (← polarity.getBoolValue?) pivot
  | .CHAIN_RESOLUTION => do
    let #[pols, pivots] := args | none
    return .chainResolution ps (← stepsArg? pols pivots ps.size)
  | .CHAIN_M_RESOLUTION => do
    let #[_, pols, pivots] := args | none
    return .chainMResolution ps (← stepsArg? pols pivots ps.size)
  | .FACTORING => unary ps args .factoring
  | .REORDERING => do
    let #[p] := ps | none
    let #[_] := args | none
    return .reordering p
  | .SPLIT => leaf ps args .split
  -- Boolean reasoning
  | .EQ_RESOLVE => binary ps args .eqResolve
  | .MODUS_PONENS => binary ps args .modusPonens
  | .NOT_NOT_ELIM => unary ps args .notNotElim
  | .CONTRA => binary ps args .contra
  | .AND_ELIM => do
    let #[p] := ps | none
    let #[i] := args | none
    return .andElim p (← natArg? i)
  | .AND_INTRO => do
    let #[] := args | none
    return .andIntro ps
  | .NOT_OR_ELIM => do
    let #[p] := ps | none
    let #[i] := args | none
    return .notOrElim p (← natArg? i)
  | .IMPLIES_ELIM => unary ps args .impliesElim
  | .NOT_IMPLIES_ELIM1 => unary ps args .notImpliesElim1
  | .NOT_IMPLIES_ELIM2 => unary ps args .notImpliesElim2
  | .EQUIV_ELIM1 => unary ps args .equivElim1
  | .EQUIV_ELIM2 => unary ps args .equivElim2
  | .NOT_EQUIV_ELIM1 => unary ps args .notEquivElim1
  | .NOT_EQUIV_ELIM2 => unary ps args .notEquivElim2
  | .XOR_ELIM1 => unary ps args .xorElim1
  | .XOR_ELIM2 => unary ps args .xorElim2
  | .NOT_XOR_ELIM1 => unary ps args .notXorElim1
  | .NOT_XOR_ELIM2 => unary ps args .notXorElim2
  | .ITE_ELIM1 => unary ps args .iteElim1
  | .ITE_ELIM2 => unary ps args .iteElim2
  | .NOT_ITE_ELIM1 => unary ps args .notIteElim1
  | .NOT_ITE_ELIM2 => unary ps args .notIteElim2
  | .NOT_AND => unary ps args .notAnd
  -- clausal form
  | .CNF_AND_POS => indexedLeaf ps args .cnfAndPos
  | .CNF_AND_NEG => leaf ps args .cnfAndNeg
  | .CNF_OR_POS => leaf ps args .cnfOrPos
  | .CNF_OR_NEG => indexedLeaf ps args .cnfOrNeg
  | .CNF_IMPLIES_POS => leaf ps args .cnfImpliesPos
  | .CNF_IMPLIES_NEG1 => leaf ps args .cnfImpliesNeg1
  | .CNF_IMPLIES_NEG2 => leaf ps args .cnfImpliesNeg2
  | .CNF_EQUIV_POS1 => leaf ps args .cnfEquivPos1
  | .CNF_EQUIV_POS2 => leaf ps args .cnfEquivPos2
  | .CNF_EQUIV_NEG1 => leaf ps args .cnfEquivNeg1
  | .CNF_EQUIV_NEG2 => leaf ps args .cnfEquivNeg2
  | .CNF_XOR_POS1 => leaf ps args .cnfXorPos1
  | .CNF_XOR_POS2 => leaf ps args .cnfXorPos2
  | .CNF_XOR_NEG1 => leaf ps args .cnfXorNeg1
  | .CNF_XOR_NEG2 => leaf ps args .cnfXorNeg2
  | .CNF_ITE_POS1 => leaf ps args .cnfItePos1
  | .CNF_ITE_POS2 => leaf ps args .cnfItePos2
  | .CNF_ITE_POS3 => leaf ps args .cnfItePos3
  | .CNF_ITE_NEG1 => leaf ps args .cnfIteNeg1
  | .CNF_ITE_NEG2 => leaf ps args .cnfIteNeg2
  | .CNF_ITE_NEG3 => leaf ps args .cnfIteNeg3
  -- equality
  | .REFL => leaf ps args .refl
  | .SYMM => unary ps args .symm
  | .TRANS => do
    let #[] := args | none
    return .trans ps
  | .CONG => do
    let #[app] := args | none
    return .cong ps app
  | .NARY_CONG => do
    let #[app] := args | none
    return .naryCong ps app
  | .PAIRWISE_CONG => do
    let #[app] := args | none
    return .pairwiseCong ps app
  | .TRUE_INTRO => unary ps args .trueIntro
  | .TRUE_ELIM => unary ps args .trueElim
  | .FALSE_INTRO => unary ps args .falseIntro
  | .FALSE_ELIM => unary ps args .falseElim
  | _ => none

variable {s : Solver} (p : s.Proof pc)

/-- The root step of `p`, taken apart, with `premises` standing for its premises.

What `view` and `foldUp` are built on: `view` passes the premises themselves, `foldUp` what it
computed for them. `premises` is expected to hold one element per premise, in order, as
`getChildren` does; a step whose premises do not match its rule's layout is `other`.
-/
def viewWith (premises : Array X) : Cvc.Proof.View X Term Term :=
  decode? p.getRule premises p.getArguments p.getRewriteRule?
  |>.getD (.other p.getRule premises p.getArguments)

/-- The root step of `p`, taken apart: its rule a constructor, its premises and arguments fields. -/
def view : s.ProofView pc := p.viewWith p.getChildren



/-! ## Traversing -/

/-- Folds over the distinct steps of `p`, depth-first, with early exit, in any monad.

Each step is handed over with its view. `pre` is called on reaching a step, before its premises,
and can skip them or stop; `post` on leaving it, once its premises are done, and can stop. Both
default to carrying on.

A step shared by several others is visited once, on the first path that reaches it, unless
`revisit` is set — which can take exponentially long.
-/
def fold [Monad m] (init : σ)
  (pre : s.Proof pc → s.ProofView pc → σ → m (FoldPre σ) := fun _ _ s => return .descend s)
  (post : s.Proof pc → s.ProofView pc → σ → m (FoldPost σ) := fun _ _ s => return .continue s)
  (revisit := false)
: m σ :=
  Cvc.Proof.foldWith (·.getChildren) (fun q => (q, q.view)) #[p] init
    (fun (q, v) s => pre q v s) (fun (q, v) s => post q v s) revisit

/-- Computes a value for every distinct step of `p`, bottom-up, and answers the root's.

`f` is handed each step with its view, the premises of which are the values already computed for
them. It is called once per distinct step, so a sub-proof shared by many steps is computed once,
which is what rebuilding a proof elsewhere wants. To end early, throw, in `Except` for instance.
-/
def foldUp [Monad m] (f : s.Proof pc → Cvc.Proof.View β Term Term → m β) : m β := do
  let premises ← Cvc.Proof.foldUpWith (·.getChildren) (fun q bs => f q (q.viewWith bs))
    p.getChildren
  f p (p.viewWith premises)

/-- `for step in p do …` visits the distinct steps of `p` in the order `fold` enters them.

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

/-- The number of distinct steps in `p`. -/
def size : Nat := Id.run do
  let mut n := 0
  for _ in p do n := n + 1
  return n

/-- How many distinct steps of `p` apply each rule, rules in the order they are first reached. -/
def ruleCounts : Array (ProofRule × Nat) := Id.run do
  let mut counts : Array (ProofRule × Nat) := #[]
  for q in p do
    let rule := q.getRule
    counts := match counts.findIdx? (·.1 == rule) with
      | some i => counts.modify i fun (r, n) => (r, n + 1)
      | none => counts.push (rule, 1)
  return counts

/-- The assumptions `p` leaves open, in the order they are first reached.

These are the formulas of its `ASSUME` steps that no enclosing `SCOPE` discharges.

A proof cvc5 answers for the `full` component leaves none open, its root scope discharging the
assertions. Below that scope, they are the assertions the refutation actually uses.
-/
def freeAssumptions : Terms :=
  p.foldUp (m := Id) fun _ v => match v with
    | .assume f => #[f]
    | .scope body discharged => body.filter (!discharged.contains ·)
    | v => Id.run do
      let mut seen : Std.HashSet Term := {}
      let mut all := #[]
      for fs in v.premises do
        for f in fs do
          if !seen.contains f then
            seen := seen.insert f
            all := all.push f
      return all

/-- The distinct steps of `p` that cvc5 does not justify, in the order they are first reached.

These are its `TRUST` and `TRUST_THEORY_REWRITE` steps.
-/
def trusted : s.Proofs pc := Id.run do
  let mut steps := #[]
  for q in p do
    if q.getRule == .TRUST || q.getRule == .TRUST_THEORY_REWRITE then steps := steps.push q
  return steps

end Solver.Proof

namespace Solver.Proofs variable {s : Solver} (ps : s.Proofs pc)

/-- `Solver.Proof.fold` over several proofs at once, left to right.

A step they share is visited once in all.
-/
def fold [Monad m] (init : σ)
  (pre : s.Proof pc → s.ProofView pc → σ → m (FoldPre σ) := fun _ _ s => return .descend s)
  (post : s.Proof pc → s.ProofView pc → σ → m (FoldPost σ) := fun _ _ s => return .continue s)
  (revisit := false)
: m σ :=
  Cvc.Proof.foldWith (·.getChildren) (fun q => (q, q.view)) ps init
    (fun (q, v) s => pre q v s) (fun (q, v) s => post q v s) revisit

/-- `Solver.Proof.foldUp` over several proofs at once, answering each proof's value, in order.

A step they share is computed once in all.
-/
def foldUp [Monad m] (f : s.Proof pc → Cvc.Proof.View β Term Term → m β) : m (Array β) :=
  Cvc.Proof.foldUpWith (·.getChildren) (fun q bs => f q (q.viewWith bs)) ps

end Solver.Proofs

end

end Cvc.Untyped
