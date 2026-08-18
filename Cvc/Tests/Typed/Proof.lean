/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Solver
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Solver
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # Proofs, typed

The proof API is the sort-erased one re-typed in exactly two places, so most of what is checked
here is that the *indices* come out right rather than that the values do — the sort-erased suite
covers the values, and the obligation on printing.

- `getResult : Term Bool`, a proof's conclusion being a formula;
- `getChildren : s.Proofs pc`, carrying the producing solver *and* the component across.

`getArguments` deliberately stays **sort-erased**. A rule's arguments are heterogeneous — cvc5
documents that some of them may be strings — so there is no index to give them, and `typeCheck` is
the way to put one on when the caller knows the rule.

`getRule`, `getRewriteRule?` and `getRewriteRule` mention no term, so they are inherited unchanged.
-/
namespace Cvc.Tests.Typed.Proof

open Cvc
open Cvc.Typed

variable [Ω] {s : Solver}

/-- `b ∧ ¬b`, the smallest refutation there is. -/
def solver (proofs := true) : Env Solver := do
  let s ← Solver.new
  if proofs then s.setOption "produce-proofs" "true"
  let b ← s.declareConst Bool "b"
  s.assert b
  (do Term.not b) >>= s.assert
  return s

/-- Every step of a proof tree. -/
def steps (fuel : Nat) (p : s.Proof pc) (acc : s.Proofs pc := #[]) : s.Proofs pc :=
  match fuel with
  | 0 => acc
  | fuel + 1 => p.getChildren.foldl (fun acc kid => steps fuel kid acc) (acc.push p)



/-! ## The indices the accessors carry -/

section indices
variable (p : s.Proof pc)

/-- A proof concludes a formula. -/
example : Term Bool := p.getResult
/-- Its premises are proofs of the same solver. -/
example : s.Proofs pc := p.getChildren
/-- Its arguments are not all Boolean, so they stay sort-erased. -/
example : Untyped.Terms := p.getArguments
/-- The rule mentions no term at all. -/
example : ProofRule := p.getRule
/-- Neither does the rewrite rule. -/
example : Option ProofRewriteRule := p.getRewriteRule?
end indices

/-! Dot notation has to reach the *typed* accessor, and three things are load-bearing for that: the
abbreviation being named `Solver.Proof`, matching the namespace the re-typings live in;
`getUnsatProof` being re-typed here, so that what it answers is headed by *this* layer's `Proofs`;
and that `Proofs` naming this layer's `Proof` as its element rather than aliasing the sort-erased
array. Get any one wrong and the sort-erased accessor answers instead, silently — nothing fails to
compile, which is why each has an `example` below. -/

section reaching
variable (s : Solver) (ps : s.Proofs pc)

/-- What `getUnsatProof` answers is this layer's array of proofs. -/
example : EnvUnsat (s.Proofs .full) := s.getUnsatProof
/-- Taking one out of it keeps this layer's index — `for`, `map` and `getElem` all unfold the
array, and an element type that named the sort-erased proof would surface there. -/
example : Array (Term Bool) := ps.map (·.getResult)
/-- Same through a `for`. -/
example : IO Unit := do for p in ps do let _ : Term Bool := p.getResult

end reaching



/-! ## The root step, end to end -/

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

/-! The conclusion is a `Term Bool`, so it is an operand of the Boolean operators with no
re-typing — which is the whole point of the index. -/

/-- info:
negated    : (not (not (and b (not b))))
its own ¬  : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    let negated ← smt! ¬ ![pure p.getResult]
    println! "negated    : {negated}"
    println! "its own ¬  : {negated == (← Term.not p.getResult)}"

/-! ## Walking the tree -/

/-- info:
steps  : 5
leaves : 2
rules  : SCOPE SCOPE CONTRA ASSUME ASSUME
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    let all := steps 20 p
    println! "steps  : {all.size}"
    println! "leaves : {(all.filter (·.getChildren.isEmpty)).size}"
    println! "rules  : {" ".intercalate (all.toList.map (toString ·.getRule))}"

/-! ## Rewrite rules

The condition on the total form is a hypothesis, and matching on `getRule` is what produces it.
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
  let x ← s.declareConst Int "x"
  (smt! x + 0 ≠ x) >>= s.assert

  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  let all := proofs.flatMap (steps 100 ·)
  let carries (p : s.Proof .full) : Bool :=
    p.getRule == .DSL_REWRITE || p.getRule == .THEORY_REWRITE
  println! "steps with a rewrite rule : {!(all.filter (·.getRewriteRule?.isSome)).isEmpty}"
  println! "matches the rule exactly  : {all.all fun p => p.getRewriteRule?.isSome == carries p}"
  println! "total form agrees         : {all.all fun p => rewriteRuleOf p == p.getRewriteRule?}"

/-! ## Printing

`toString` prints in `Proof.Format.no`, legal whatever the component; `toStringFmt` takes the
format and, with it, the obligation that the format is `.no` or the component is `full`. Neither is
re-typed here — no term appears in either signature — but both are restated so the obligation is
stated against *this* layer's `Proof`, and the two `example`s below pin it.

cvc5 answers a **segfault** rather than an exception when that pairing is violated — a cvc5 bug,
and why the pairing is worth a type at all.
-/

/-- info:
non-empty   : true
dot differs : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    println! "non-empty   : {!(← p.toString).isEmpty}"
    println! "dot differs : {(← p.toStringFmt .dot) != (← p.toString)}"

/-- The obligation `toStringFmt` carries, supplied by hand rather than by `grind`. -/
example (p : s.Proof .sat) : (Proof.Format.dot = .no ∨ Proof.Component.sat = .full) → Env String :=
  fun h => p.toStringFmt .dot h

/-- And it is false for exactly the pairing that would crash, so no call can supply it. -/
example : ¬ (Proof.Format.dot = .no ∨ Proof.Component.sat = .full) := by grind
