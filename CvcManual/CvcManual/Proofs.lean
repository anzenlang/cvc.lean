/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc
public meta import Cvc

import all Cvc.Proof
import all Cvc.Untyped.Core.Solver
import all Cvc.Untyped.Proof
import all Cvc.Typed.Core.Solver
import all Cvc.Typed.Proof

public import VersoManual
public import CvcManual.Decl

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open CvcManual



set_option pp.rawOnError true

-- the docstring of `Cvc.Proof.View`, seventy-odd constructors, takes longer than the default
set_option maxHeartbeats 1000000



#doc (Manual) "Proofs" =>
%%%
tag := "proofs"
htmlSplit := .never
%%%

An _unsat_ answer comes with a proof, if the solver was asked to produce one. cvc.lean hands it over as data: each step of the proof can be taken apart into its rule, its premises and its arguments, and the whole proof can be traversed — to find the lemmas a refutation relies on, to see which assertions it uses, or to rebuild it elsewhere.

As for the solver, the rest of this section uses the typed layer; the sort-erased one is the same with sort-erased formulas.

```lean -show
section typed
```

```lean
open Cvc Typed
variable [Ω]
```

# Getting a Proof

A proof is only available where the answer was _unsat_, so `getUnsatProof` lives in the unsat mode, and needs cvc5's `produce-proofs` option.

{decl Cvc.Typed.Solver.getUnsatProof}

{decl Cvc.Typed.Solver.Proof}

A proof is indexed by the solver that produced it and by the _component_ it was asked for: the whole refutation (`full`, the default), or one of its parts — preprocessing, the SAT solver's reasoning, the theory lemmas. Printing a proof in a format other than `Proof.Format.no` is only legal for `full`, and the index is what makes that a type obligation.

`for step in proof do …` visits the distinct steps of a proof:

```lean (name := ex_Proof_walk)
#eval Env.runIO do
  let s ← Solver.new
  s.setOpt .smt_produceProofs true
  let b ← Term.mkSymbolAs Bool "b"
  s.assert b
  s.assert (← smt! ¬ b)
  let proofs ← s.checkSat
    (ifUnsat := s.getUnsatProof)
  for p in proofs do
    for step in p do
      println! "{step.getRule} ⊢ {step.getResult}"
```
```leanOutput ex_Proof_walk
SCOPE ⊢ (not (and b (not b)))
SCOPE ⊢ (not (and b (not b)))
CONTRA ⊢ false
ASSUME ⊢ b
ASSUME ⊢ (not b)
```

# Taking a Step Apart

`view` answers a step as a {lean}`Solver.ProofView`, one constructor per rule:

{decl Cvc.Typed.Solver.Proof.view}

The two layers' views are one type, `Cvc.Proof.View P F T`, at each layer's own types: `P` is a premise, `F` a formula and `T` a term of any sort. A typed view's formulas are {lean}`Term Bool` and its other terms sort-erased; a sort-erased view's are all sort-erased:

{decl Cvc.Typed.Solver.ProofView}

{decl Cvc.Untyped.Solver.ProofView}

The premise type is a parameter too, so that `foldUp` (see below) can hand over a step whose premises are values it has already computed rather than proofs. Here is the generic type, with every rule it decodes:

{decl Cvc.Proof.View}

A typed step's view holds its formulas — an assumption, a pivot, a clause-form input — as {lean}`Term Bool`, so they are operands of the Boolean operators as they are. A term of any other sort stays sort-erased, as the arguments of a proof do: no rule fixes its sort.

```lean (name := ex_Proof_view)
def describe {s : Solver} : s.ProofView pc → String
  | .assume f => s!"assume {f}"
  | .scope _ fs => s!"scope, discharging {fs}"
  | .contra .. => "contra"
  | v => s!"{v.rule}"

#eval Env.runIO do
  let s ← Solver.new
  s.setOpt .smt_produceProofs true
  let b ← Term.mkSymbolAs Bool "b"
  s.assert b
  s.assert (← smt! ¬ b)
  let proofs ← s.checkSat
    (ifUnsat := s.getUnsatProof)
  for p in proofs do
    for step in p do println! describe step.view
```
```leanOutput ex_Proof_view
scope, discharging #[]
scope, discharging #[b, (not b)]
contra
assume b
assume (not b)
```

# Traversing a Proof

The examples below refute `x ≥ 1`, `x ≤ 1` and `f x ≠ f 1`: arithmetic decides `x = 1` and congruence does the rest, so the proof goes through two theories and through rewriting.

```lean
def congruence : Env Solver := do
  let s ← Solver.new
  s.setOpt .smt_produceProofs true
  let f ← Term.mkSymbolAs (Int → Int) "f"
  let x ← Term.mkSymbolAs Int "x"
  (smt! x ≥ 1) >>= s.assert
  (smt! x ≤ 1) >>= s.assert
  (smt! f x ≠ f 1) >>= s.assert
  return s
```

A proof is a graph rather than a tree: cvc5 shares a sub-proof between the steps that use it. Every traversal visits a shared step once, telling steps apart by identity.

## Folding

{decl Cvc.Typed.Solver.Proof.fold}

`pre` can end the fold early. The first resolution step reached is the SAT solver's refutation, and its premises are the clauses it resolved:

```lean (name := ex_Proof_clauses)
#eval Env.runIO do
  let s ← congruence
  let proofs ← s.checkSat
    (ifUnsat := s.getUnsatProof)
  for p in proofs do
    let clauses : Array (Term Bool) :=
      p.fold #[] (m := Id)
        (pre := fun _ v acc => return match v with
          | .chainMResolution ps _ =>
            .stop (ps.map (·.getResult))
          | _ => .descend acc)
    for c in clauses do println! "- {c}"
```
```leanOutput ex_Proof_clauses
- (or (>= x 2) (= (f x) (f 1)) (not (>= x 1)))
- (not (= (f x) (f 1)))
- (not (>= x 2))
- (>= x 1)
```

The fold runs in the caller's monad, and `break` ends a `for` loop over the steps just as `stop` ends a fold.

## Bottom-Up

{decl Cvc.Typed.Solver.Proof.foldUp}

`foldUp` hands each step a view whose premises are the values already computed for them — the shape of anything that rebuilds a proof elsewhere. Ending early is the monad's business: here, a rebuild gives up on the first step it has no rule for.

```lean (name := ex_Proof_foldUp)
#eval Env.runIO do
  let s ← congruence
  let proofs ← s.checkSat
    (ifUnsat := s.getUnsatProof)
  for p in proofs do
    let rebuilt : Except String Nat :=
      p.foldUp fun q v => match v with
        | .other .. =>
          throw s!"no rule for {q.getRule}"
        | v => return v.premises.foldl (· + ·) 1
    match rebuilt with
    | .ok n => println! "rebuilt, {n} steps as a tree"
    | .error e => println! e
```
```leanOutput ex_Proof_foldUp
no rule for INT_TIGHT_UB
```

# Lemmas and Unsat Explanations

{decl Cvc.Typed.Solver.Proof.freeAssumptions}

A `full` proof leaves no assumption open, its root scope discharging the assertions. Below that scope, the open assumptions are the assertions the refutation actually uses:

```lean (name := ex_Proof_used)
#eval Env.runIO do
  let s ← congruence
  let proofs ← s.checkSat
    (ifUnsat := s.getUnsatProof)
  for p in proofs do
    if let .scope outer _ := p.view then
      if let .scope refutation _ := outer.view then
        for f in refutation.freeAssumptions do
          println! "- {f}"
```
```leanOutput ex_Proof_used
- (<= x 1)
- (distinct (f x) (f 1))
- (>= x 1)
```

The `theoryLemmas` component answers one proof per theory lemma, whose conclusion is the lemma. `Solver.Proofs.fold` and `Solver.Proofs.foldUp` traverse several proofs at once.

```lean (name := ex_Proof_lemmas)
#eval Env.runIO do
  let s ← congruence
  let lemmas ← s.checkSat (ifUnsat :=
    s.getUnsatProof .theoryLemmas)
  for p in lemmas do
    println! "lemma : {p.getResult}"
    println! "steps : {p.size}"
```
```leanOutput ex_Proof_lemmas
lemma : (or (>= x 2) (= (f x) (f 1)) (not (>= x 1)))
steps : 28
```

{decl Cvc.Typed.Solver.Proof.ruleCounts}
{decl Cvc.Typed.Solver.Proof.trusted}
{decl Cvc.Typed.Solver.Proof.size}

# Typed and Sort-Erased Proofs

Each layer has its own proof type. The typed one is the sort-erased one under a type of its own, so `toUntyped` (or `relax`) and `toTyped` cross for free, and a sort-erased function never answers for a typed proof by accident. The two views decode the same steps; they differ only in how formulas are typed.

```lean -show
end typed
```
