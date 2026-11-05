/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core
import Cvc.Untyped.Theory
import Cvc.Untyped.Proof
import Cvc.Typed.Proof

public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory
public meta import Cvc.Untyped.Proof
public meta import Cvc.Typed.Proof



/-! # Proof rules, decoded

`Cvc.Proof.View` decodes a rule only when its step has the layout cvc5 documents, and falls back on
`other` otherwise, so a layout that cvc5 changes, or that the decoder reads wrongly, would go
unnoticed without a step of that rule to look at. Each problem below makes cvc5 produce at least one
step of the rules it names, and the step is shown as both layers decode it: its premises, its
formulas and terms in field order, and its other fields — `OTHER` if it fell back.

The rules the other proof tests already meet (`ASSUME`, `SCOPE`, the resolutions, `EQ_RESOLVE`,
`MODUS_PONENS`, `CONTRA`, `AND_INTRO`, `AND_ELIM`, `IMPLIES_ELIM`, `XOR_ELIM1`/`2`, `CNF_AND_NEG`,
the equality rules, `EVALUATE`, `DSL_REWRITE`, `THEORY_REWRITE`) are not repeated. Three decoded
rules are missing for want of a problem producing them: `SAT_REFUTATION` (not produced with this
build's SAT solver), `SPLIT` (a tautology a refutation has no use for), and `PAIRWISE_CONG` (cvc5
rewrites `distinct` into disequalities before any congruence under it).

Most problems turn `simplification` off, so that unit assertions are not substituted into the other
assertions before the SAT solver sees them, and the eliminations survive.
-/
namespace Cvc.Tests.ProofRules

open Cvc
open Cvc.Untyped

variable [Ω]

/-- A step's view: its premises, its formulas and terms in field order, and its other fields. -/
def describe (v : Cvc.Proof.View P F T) [ToString F] [ToString T] : String :=
  match v with
  | .other .. => "OTHER"
  | v =>
    let (_, shown) := (v.mapM (m := StateM (Array String)) pure
      (fun f => do modify (·.push (toString f)); return f)
      (fun t => do modify (·.push (toString t)); return t)).run #[]
    let extra := match v with
      | .andElim _ i | .notOrElim _ i | .cnfAndPos _ i | .cnfOrNeg _ i => s!", index {i}"
      | .trust id .. => s!", id {id}"
      | .trustTheoryRewrite theory method => s!", theory {theory}, method {method}"
      | .theoryRewrite rule | .dslRewrite rule .. => s!", {rule}"
      | _ => ""
    s!"{v.premises.size} premises, {shown}{extra}"

/-- For each of `rules`, the first step of `problem`'s refutation applying it, as both layers decode
it. -/
def exhibit (rules : List ProofRule) (problem : Untyped.Solver → Env Unit)
  (options : List (String × String) := []) (granularity : Option String := none)
: Env Unit := do
  let s ← Untyped.Solver.new
  s.setOption "produce-proofs" "true"
  if let some g := granularity then s.setOption "proof-granularity" g
  for (k, v) in options do s.setOption k v
  problem s
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for rule in rules do
    let found := proofs.fold none (m := Id) (pre := fun q _ found =>
      return if q.getRule == rule then .stop (some q) else .descend found)
    match found with
    | some q =>
      let untyped := describe q.view
      let typed := describe q.toTyped.view
      println! "{rule}: {untyped}{if typed == untyped then "" else s!"\n  typed: {typed}"}"
    | none => println! "{rule}: not produced"

/-- Four Boolean constants. -/
def bools (s : Untyped.Solver) : Env (Term × Term × Term × Term) := do
  let bool ← Srt.bool
  return (← s.declareConst "a" bool, ← s.declareConst "b" bool, ← s.declareConst "c" bool,
    ← s.declareConst "d" bool)

/-- No simplification, so that unit assertions survive until the SAT solver. -/
def noSimp : List (String × String) := [("simplification", "none")]

open Untyped.Term



/-! ## Boolean eliminations -/

/-- info: NOT_OR_ELIM: 1 premises, #[], index 0
NOT_NOT_ELIM: 1 premises, #[]
NOT_AND: 1 premises, #[]
NOT_IMPLIES_ELIM1: 1 premises, #[]
NOT_IMPLIES_ELIM2: 1 premises, #[]
EQUIV_ELIM1: 1 premises, #[]
EQUIV_ELIM2: 1 premises, #[]
NOT_EQUIV_ELIM1: 1 premises, #[]
NOT_EQUIV_ELIM2: 1 premises, #[]
NOT_XOR_ELIM1: 1 premises, #[]
NOT_XOR_ELIM2: 1 premises, #[]
ITE_ELIM1: 1 premises, #[]
ITE_ELIM2: 1 premises, #[]
NOT_ITE_ELIM1: 1 premises, #[]
NOT_ITE_ELIM2: 1 premises, #[]
-/
#guard_msgs in #eval Env.runIO do
  exhibit [.NOT_OR_ELIM] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← or a b)); s.assert a
  exhibit [.NOT_NOT_ELIM] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← or (← not a) b)); s.assert (← not a)
  exhibit [.NOT_AND] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← and a b)); s.assert a; s.assert b
  exhibit [.NOT_IMPLIES_ELIM1, .NOT_IMPLIES_ELIM2] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← implies a b)); s.assert (← or (← not a) b)
  exhibit [.EQUIV_ELIM1] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← equal a b); s.assert a; s.assert (← not b)
  exhibit [.EQUIV_ELIM2] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← equal a b); s.assert (← not a); s.assert b
  exhibit [.NOT_EQUIV_ELIM1] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← equal a b)); s.assert (← not a); s.assert (← not b)
  exhibit [.NOT_EQUIV_ELIM2] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← equal a b)); s.assert a; s.assert b
  exhibit [.NOT_XOR_ELIM1] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← xor a b)); s.assert (← not a); s.assert b
  exhibit [.NOT_XOR_ELIM2] (options := noSimp) fun s => do
    let (a, b, _, _) ← bools s
    s.assert (← not (← xor a b)); s.assert a; s.assert (← not b)
  exhibit [.ITE_ELIM1] (options := noSimp) fun s => do
    let (a, b, c, _) ← bools s
    s.assert (← ite a b c); s.assert a; s.assert (← not b)
  exhibit [.ITE_ELIM2] (options := noSimp) fun s => do
    let (a, b, c, _) ← bools s
    s.assert (← ite a b c); s.assert (← not a); s.assert (← not c)
  exhibit [.NOT_ITE_ELIM1] (options := noSimp) fun s => do
    let (a, b, c, _) ← bools s
    s.assert (← not (← ite a b c)); s.assert a; s.assert b
  exhibit [.NOT_ITE_ELIM2] (options := noSimp) fun s => do
    let (a, b, c, _) ← bools s
    s.assert (← not (← ite a b c)); s.assert (← not a); s.assert c



/-! ## Clausal form

A connective nested under a disjunction gets clausal-form steps for it, when the refutation needs
them.
-/

/-- info: CNF_AND_POS: 0 premises, #[(and a b)], index 1
CNF_OR_POS: 0 premises, #[(or a b)]
CNF_OR_NEG: 0 premises, #[(or a b)], index 0
CNF_IMPLIES_POS: 0 premises, #[(=> a b)]
CNF_IMPLIES_NEG1: 0 premises, #[(=> a b)]
CNF_IMPLIES_NEG2: 0 premises, #[(=> a b)]
CNF_EQUIV_POS1: 0 premises, #[(= a b)]
CNF_EQUIV_POS2: 0 premises, #[(= a b)]
CNF_EQUIV_NEG1: 0 premises, #[(= a b)]
CNF_EQUIV_NEG2: 0 premises, #[(= a b)]
CNF_XOR_POS1: 0 premises, #[(xor a b)]
CNF_XOR_POS2: 0 premises, #[(xor a b)]
CNF_XOR_NEG1: 0 premises, #[(xor a b)]
CNF_XOR_NEG2: 0 premises, #[(xor a b)]
CNF_ITE_POS1: 0 premises, #[(ite a b c)]
CNF_ITE_POS2: 0 premises, #[(ite a b c)]
CNF_ITE_NEG1: 0 premises, #[(ite a b c)]
CNF_ITE_NEG2: 0 premises, #[(ite a b c)]
CNF_ITE_POS3: 0 premises, #[(ite a b c)]
CNF_ITE_NEG3: 0 premises, #[(ite a b c)]
-/
#guard_msgs in #eval Env.runIO do
  exhibit [.CNF_AND_POS] fun s => do
    let (a, b, c, d) ← bools s
    s.assert (← or (← and a b) (← and c d))
    s.assert (← or (← not a) (← not b)); s.assert (← or (← not c) (← not d))
  exhibit [.CNF_OR_POS] fun s => do
    let (a, b, c, d) ← bools s
    s.assert (← or (← and (← or a b) c) d)
    s.assert (← not d); s.assert (← not a); s.assert (← not b)
  exhibit [.CNF_OR_NEG] (options := noSimp) fun s => do
    let (a, b, c, d) ← bools s
    s.assert (← or (← not (← or a b)) d)
    s.assert (← not d); s.assert (← or a c); s.assert (← not c)
  exhibit [.CNF_IMPLIES_POS] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← implies a b) d); s.assert (← not d); s.assert a; s.assert (← not b)
  exhibit [.CNF_IMPLIES_NEG1, .CNF_IMPLIES_NEG2] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← not (← implies a b)) d); s.assert (← not d)
    s.assert (← or (← not a) b)
  exhibit [.CNF_EQUIV_POS1] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← equal a b) d); s.assert (← not d); s.assert a; s.assert (← not b)
  exhibit [.CNF_EQUIV_POS2] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← equal a b) d); s.assert (← not d); s.assert (← not a); s.assert b
  exhibit [.CNF_EQUIV_NEG1] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← not (← equal a b)) d); s.assert (← not d)
    s.assert (← not a); s.assert (← not b)
  exhibit [.CNF_EQUIV_NEG2] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← not (← equal a b)) d); s.assert (← not d); s.assert a; s.assert b
  exhibit [.CNF_XOR_POS1] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← xor a b) d); s.assert (← not d); s.assert (← not a); s.assert (← not b)
  exhibit [.CNF_XOR_POS2] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← xor a b) d); s.assert (← not d); s.assert a; s.assert b
  exhibit [.CNF_XOR_NEG1] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← not (← xor a b)) d); s.assert (← not d); s.assert a; s.assert (← not b)
  exhibit [.CNF_XOR_NEG2] (options := noSimp) fun s => do
    let (a, b, _, d) ← bools s
    s.assert (← or (← not (← xor a b)) d); s.assert (← not d); s.assert (← not a); s.assert b
  exhibit [.CNF_ITE_POS1, .CNF_ITE_POS2, .CNF_ITE_NEG1, .CNF_ITE_NEG2] fun s => do
    let (a, b, c, d) ← bools s
    s.assert (← or (← ite a b c) d); s.assert (← or (← not (← ite a b c)) (← not d))
    s.assert (← or d (← not b)); s.assert (← or d (← not c))
    s.assert (← or (← not d) b); s.assert (← or (← not d) c)
  exhibit [.CNF_ITE_POS3] (options := noSimp) fun s => do
    let (a, b, c, d) ← bools s
    s.assert (← or (← ite a b c) d); s.assert (← not d); s.assert (← not b); s.assert (← not c)
  exhibit [.CNF_ITE_NEG3] (options := noSimp) fun s => do
    let (a, b, c, d) ← bools s
    s.assert (← or (← not (← ite a b c)) d); s.assert (← not d); s.assert b; s.assert c



/-! ## Factoring, equality, rewriting and trusted steps

`FACTORING` needs `proof-chain-m-res` off, which otherwise folds it into `CHAIN_M_RESOLUTION`.
`TRUST` comes from the `pp-only` proof mode, which justifies only preprocessing; the theory and
method identifiers of `TRUST_THEORY_REWRITE` are cvc5's internal ones.
-/

/-- info: FACTORING: 1 premises, #[]
TRUE_INTRO: 1 premises, #[]
TRUE_ELIM: 1 premises, #[]
FALSE_INTRO: 1 premises, #[]
FALSE_ELIM: 1 premises, #[]
ABSORB: 0 premises, #[]
ACI_NORM: 0 premises, #[]
TRUST_THEORY_REWRITE: 0 premises, #[], theory 4, method 6
TRUST: 3 premises, #[], id 3
-/
#guard_msgs in #eval Env.runIO do
  exhibit [.FACTORING] (options := noSimp ++ [("proof-chain-m-res", "false")]) fun s => do
    let (a, b, c, _) ← bools s
    s.assert (← or a (← and a b))
    s.assert (← or (← not a) c); s.assert (← or (← not a) (← not c))
  exhibit [.TRUE_INTRO, .TRUE_ELIM] (options := noSimp) fun s => do
    let p ← mkSymbolAs (Int → Bool) "P"
    let x ← mkSymbolAs Int "x"
    let y ← mkSymbolAs Int "y"
    s.assert (← apply p x); s.assert (← equal x y); s.assert (← not (← apply p y))
  exhibit [.FALSE_INTRO, .FALSE_ELIM] (options := noSimp) fun s => do
    let p ← mkSymbolAs (Int → Bool) "P"
    let x ← mkSymbolAs Int "x"
    let y ← mkSymbolAs Int "y"
    s.assert (← not (← apply p x)); s.assert (← equal x y); s.assert (← apply p y)
  exhibit [.ABSORB, .ACI_NORM] (granularity := some "dsl-rewrite") fun s => do
    let (a, b, c, _) ← bools s
    s.assert (← or (← and a (← and b (← mkBool false))) (← and c (← not c)))
  exhibit [.TRUST_THEORY_REWRITE] (granularity := some "theory-rewrite") fun s => do
    let x ← mkSymbolAs (BitVec 4) "x"
    let y ← mkSymbolAs (BitVec 4) "y"
    s.assert (← equal (← bvAnd x (← bvAnd y (← mkBitVec 4 0))) (← mkBitVec 4 1))
  exhibit [.TRUST] (options := [("proof-mode", "pp-only")]) fun s => do
    let (a, b, c, d) ← bools s
    s.assert (← or (← and a b) (← and c d))
    s.assert (← or (← not a) (← not b)); s.assert (← or (← not c) (← not d))

end Cvc.Tests.ProofRules
