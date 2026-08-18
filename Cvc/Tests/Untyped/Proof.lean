/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Solver
import Cvc.Untyped.Core

public meta import Cvc.Untyped.Solver
public meta import Cvc.Untyped.Core



/-! # Proofs, sort-erased

A proof is what an *unsat* answer can be asked for, so `getUnsatProof` lives in `EnvUnsat` and
needs cvc5's `produce-proofs` option. The accessors on a proof are pure, so a branch can walk one;
printing is `Env`, so a proof a branch wants to print has to be carried out of it first, which is
what these tests do.

`Solver.Proof` carries two indices, and neither is decoration:

- the **solver** that produced it, because cvc5's `proofToString` takes that solver, and the index
  is what stops two solvers' proofs from being mixed;
- the **component** it was asked for, because printing in any format but `Proof.Format.no` is legal
  only when that component is `full`. See "Printing" below.
-/
namespace Cvc.Tests.Untyped.Proof

open Cvc
open Cvc.Untyped

variable [Ω] {s : Solver}

/-- `b ∧ ¬b`, the smallest refutation there is. -/
def contradiction (s : Solver) : Env Unit := do
  let bool ← Srt.bool
  let b ← s.declareConst "b" bool
  s.assert b
  (do Term.not b) >>= s.assert

/-- A solver with proofs on, holding `contradiction`. -/
def solver (proofs := true) : Env Solver := do
  let s ← Solver.new
  if proofs then s.setOption "produce-proofs" "true"
  contradiction s
  return s

/-- The rules of a proof tree, indented by depth. Fuel because a proof is not structurally
recursive as far as Lean is concerned. -/
def rules (fuel : Nat) (p : s.Proof pc) (depth := 0) (acc : Array String := #[]) : Array String :=
  match fuel with
  | 0 => acc.push "<out of fuel>"
  | fuel + 1 =>
    let acc := acc.push s!"{"".pushn ' ' (2 * depth)}{p.getRule}"
    p.getChildren.foldl (fun acc kid => rules fuel kid (depth + 1) acc) acc

/-- Every step of a proof tree. -/
def steps (fuel : Nat) (p : s.Proof pc) (acc : s.Proofs pc := #[]) : s.Proofs pc :=
  match fuel with
  | 0 => acc
  | fuel + 1 => p.getChildren.foldl (fun acc kid => steps fuel kid acc) (acc.push p)



/-! ## The root step -/

/-- info:
proofs    : 1
rule      : SCOPE
result    : (not (and b (not b)))
arguments : 0
children  : 1
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  println! "proofs    : {proofs.size}"
  for p in proofs do
    println! "rule      : {p.getRule}"
    println! "result    : {p.getResult}"
    println! "arguments : {p.getArguments.size}"
    println! "children  : {p.getChildren.size}"

/-! ## Walking the tree

`getChildren` is the premises of the root step, so a proof is walked by recursion. The refutation
of `b ∧ ¬b` is the whole tree below.
-/

/-- info:
SCOPE
  SCOPE
    CONTRA
      ASSUME
      ASSUME
steps : 5
leaves: 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    for line in rules 20 p do println! "{line}"
    let all := steps 20 p
    println! "steps : {all.size}"
    println! "leaves: {(all.filter (·.getChildren.isEmpty)).size}"

/-! ## Printing, and the format argument

There are two spellings. `toString` prints in `Proof.Format.no`, which is legal whatever the
component, so it asks nothing of the caller. `toStringFmt` takes the format, and with it an
obligation — the format is `.no`, or the proof's component is `full` — discharged by `grind`
whenever the two are literals, so a correct call reads as though there were no obligation at all.

Every format is accepted on a `full` proof. The renderings are checked to *differ* rather than
pinned line by line: what matters is that the argument reaches cvc5 at all, and the exact output is
cvc5's to change.

`fromSolver` is whatever cvc5 defaults to, which today is `cpc` — the one assertion below that is
about cvc5's configuration rather than about this wrapper.
-/

/-- info:
toString       : true
five distinct  : true
default is cpc : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    println! "toString       : {!(← p.toString).isEmpty}"
    let renderings ← #[Proof.Format.fromSolver, .no, .dot, .alethe, .lfsc].mapM
      fun fmt => p.toStringFmt fmt
    let distinct := renderings.foldl
      (fun acc r => if acc.contains r then acc else acc.push r) (#[] : Array String)
    println! "five distinct  : {distinct.size == renderings.size}"
    println! "default is cpc : {(← p.toStringFmt) == (← p.toStringFmt .cpc)}"

/-! A child inherits its parent's component, so every format stays available down a `full` proof.
That is cvc5's reading too, checked here because the index asserting it is what makes the
obligation dischargeable at every depth rather than only at the root. -/

/-- info:
child rule       : SCOPE
child formats    : true
grandchild dot   : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    for kid in p.getChildren do
      println! "child rule       : {kid.getRule}"
      let renderings ← #[Proof.Format.no, .dot, .alethe].mapM fun fmt => kid.toStringFmt fmt
      println! "child formats    : {renderings.all (!·.isEmpty)}"
      for gkid in kid.getChildren do
        println! "grandchild dot   : {!(← gkid.toStringFmt .dot).isEmpty}"

/-! ## Rewrite rules

`getRewriteRule?` answers exactly on the two rules that carry one, and `getRewriteRule` is the same
thing with that condition as a hypothesis — which a `match` on `getRule` is what produces.
-/

/-- The total form, reached the way a caller has to reach it. -/
def rewriteRuleOf (p : s.Proof pc) : Option ProofRewriteRule :=
  match h : p.getRule with
  | .DSL_REWRITE => some (p.getRewriteRule (.inl h))
  | .THEORY_REWRITE => some (p.getRewriteRule (.inr h))
  | _ => none

/-- info:
steps with a rewrite rule : true
matches the rule exactly  : true
total form agrees         : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-proofs" "true"
  s.setOption "proof-granularity" "dsl-rewrite"
  -- proving `x + 0 ≠ x` unsat goes through rewriting, so the tree has rewrite steps in it
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let zero ← Term.mkInt 0
  (do Term.add x zero) >>= (Term.distinct · x) >>= s.assert

  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  let all := proofs.flatMap (steps 100 ·)
  let carries (p : s.Proof .full) : Bool :=
    p.getRule == .DSL_REWRITE || p.getRule == .THEORY_REWRITE
  println! "steps with a rewrite rule : {!(all.filter (·.getRewriteRule?.isSome)).isEmpty}"
  println! "matches the rule exactly  : {all.all fun p => p.getRewriteRule?.isSome == carries p}"
  println! "total form agrees         : {all.all fun p => rewriteRuleOf p == p.getRewriteRule?}"

/-! ## Components

A component other than `full` answers a proof of that component alone, and which component it was
travels in the proof's type. That is what turns the pairing cvc5 requires into a *type* obligation:
printing a non-`full` proof in anything but `Proof.Format.no` does not compile.

It is worth a type because the alternative is not an exception but a **segfault**, a cvc5 bug.
Nothing below can call it wrongly, which is the point; what the two `example`s pin instead is the
obligation itself, so that weakening it would show up here rather than in a crash.
-/

/-- The obligation `toStringFmt` carries, supplied by hand rather than by `grind`. -/
example (p : s.Proof .sat) : (Proof.Format.dot = .no ∨ Proof.Component.sat = .full) → Env String :=
  fun h => p.toStringFmt .dot h

/-- And it is false for exactly the pairing that would crash, so no call can supply it. -/
example : ¬ (Proof.Format.dot = .no ∨ Proof.Component.sat = .full) := by grind

/-- info:
sat component : 1 proof(s), rule ASSUME
printed       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof .sat)
  for p in proofs do
    println! "sat component : {proofs.size} proof(s), rule {p.getRule}"
    println! "printed       : {!(← p.toStringFmt .no).isEmpty}"

/-! ## What fails -/

/-- info: without produce-proofs: caught -/
#guard_msgs in #eval Env.runIO do
  let s ← solver (proofs := false)
  let outcome ← s.checkSat (ifUnsat := do
    try
      let _ ← s.getUnsatProof
      return "no error"
    catch _ => return "caught")
  println! "without produce-proofs: {outcome}"

/-! A proof is a wrapper like any other, so it has no `Inhabited` and cannot be conjured out of an
array. -/

/--
error: failed to synthesize instance of type class
  Inhabited (s.Proof pc)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (proofs : s.Proofs pc) : s.Proof pc := proofs[0]!
