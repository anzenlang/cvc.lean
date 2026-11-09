/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core.Solver
import Cvc.Untyped.Core
import Cvc.Untyped.Theory.Arith
import Cvc.Untyped.Theory.Fun
import Cvc.Untyped.Proof

public meta import Cvc.Untyped.Core.Solver
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory.Arith
public meta import Cvc.Untyped.Theory.Fun
public meta import Cvc.Untyped.Proof



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

Then the inspection API of `Cvc.Untyped.Proof`: each step's view, which rules are left undecoded,
sharing, ending a traversal early, folding in a monad, `foldUp`, the ready-made questions, several
proofs at once, and that every step of every component answers.
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
  Term.not b >>= s.assert

/-- A solver with proofs on, holding `contradiction`. -/
def solver (proofs := true) : Env Solver := do
  let s ← Solver.new
  if proofs then s.setOption "produce-proofs" "true"
  contradiction s
  return s

/-- `x ≥ 1`, `x ≤ 1` and `f x ≠ f 1`: arithmetic decides `x = 1`, congruence does the rest, so the
refutation goes through both theories and through rewriting. -/
def congruence (s : Solver) : Env Unit := do
  let f ← Term.mkSymbolAs (Int → Int) "f"
  let x ← Term.mkSymbolAs Int "x"
  let one ← Term.mkInt 1
  Term.ge x one >>= s.assert
  Term.le x one >>= s.assert
  Term.distinct (← Term.apply f x) (← Term.apply f one) >>= s.assert

/-- A solver with proofs on, holding `problem`. -/
def solverWith (problem : Solver → Env Unit) : Env Solver := do
  let s ← Solver.new
  s.setOption "produce-proofs" "true"
  problem s
  return s

/-- One line per step, saying what its view holds. -/
def describe : s.ProofView pc → String
  | .assume f => s!"assume {f}"
  | .scope _ discharged => s!"scope, discharging {discharged}"
  | .resolution _ _ polarity pivot => s!"resolution on {pivot}, polarity {polarity}"
  | .chainResolution ps steps => s!"chainResolution of {ps.size}, steps {steps}"
  | .chainMResolution ps steps => s!"chainMResolution of {ps.size}, steps {steps}"
  | .dslRewrite rule ps inst =>
    s!"dslRewrite {rule} {inst}" ++ if ps.isEmpty then "" else s!", {ps.size} premises"
  | .theoryRewrite rule => s!"theoryRewrite {rule}"
  | .evaluate t => s!"evaluate {t}"
  | .refl t => s!"refl {t}"
  | .cong ps app => s!"cong of {ps.size} on {app}"
  | .naryCong ps app => s!"naryCong of {ps.size} on {app}"
  | .andElim _ index => s!"andElim at {index}"
  | .cnfAndNeg f => s!"cnfAndNeg {f}"
  | .other rule ps args => s!"other {rule}: {ps.size} premises, {args.size} arguments"
  | v => s!"{v.rule}, {v.premises.size} premises"

/-- The distinct steps of `p`, indented by depth, a shared one shown on the first path reaching it.
-/
def render (p : s.Proof pc) : Array String :=
  Id.run <| Prod.snd <$> p.fold (0, #[])
    (pre := fun _ v (depth, lines) =>
      return .descend (depth + 1, lines.push s!"{"".pushn ' ' (2 * depth)}{describe v}"))
    (post := fun _ _ (depth, lines) => return .continue (depth - 1, lines))

/-- Every distinct step of `p`. -/
def steps (p : s.Proof pc) : s.Proofs pc := Id.run do
  let mut all := #[]
  for q in p do all := all.push q
  return all



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

`getChildren` is the premises of the root step; `fold` walks them all, and `view` takes each step
apart. The refutation of `b ∧ ¬b` is the whole tree below: the outer scope discharges nothing, the
inner one the two assertions, which `CONTRA` refutes.
-/

/-- info:
scope, discharging #[]
  scope, discharging #[b, (not b)]
    CONTRA, 2 premises
      assume b
      assume (not b)
steps : 5
leaves: 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    for line in render p do println! "{line}"
    let all := steps p
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
  Term.add x zero >>= (Term.distinct · x) >>= s.assert

  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  let all := proofs.flatMap steps
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

/-! ## Taking a step apart

`view` answers a step as a `Cvc.Proof.View`: its rule as a constructor, its premises and arguments
as fields, decoded from the layout cvc5 documents for the rule. The refutation below goes through
arithmetic, congruence and rewriting, which is most of what a proof is made of. A step shared by
several others is shown once, where it is first reached. The two arithmetic rules are not decoded,
and come out as `other` with everything cvc5 gives.
-/

/-- info: scope, discharging #[]
  scope, discharging #[(>= x 1), (<= x 1), (distinct (f x) (f 1))]
    chainMResolution of 4, steps #[(true, (= (f x) (f 1))), (true, (>= x 2)), (false, (>= x 1))]
      REORDERING, 1 premises
        EQ_RESOLVE, 2 premises
          resolution on (and (>= x 1) (not (>= x 2))), polarity true
            cnfAndNeg (and (>= x 1) (not (>= x 2)))
            IMPLIES_ELIM, 1 premises
              scope, discharging #[(>= x 1), (not (>= x 2))]
                MODUS_PONENS, 2 premises
                  MODUS_PONENS, 2 premises
                    AND_INTRO, 2 premises
                      assume (>= x 1)
                      EQ_RESOLVE, 2 premises
                        assume (<= x 1)
                        TRANS, 2 premises
                          dslRewrite arith-leq-norm #[x, 1]
                          cong of 1 on (not (>= x (+ 1 1)))
                            cong of 2 on (>= x (+ 1 1))
                              refl x
                              evaluate (+ 1 1)
                    scope, discharging #[(>= x 1), (not (>= x 2))]
                      other ARITH_TRICHOTOMY: 2 premises, 0 arguments
                        assume (>= x 1)
                        other INT_TIGHT_UB: 1 premises, 0 arguments
                          EQ_RESOLVE, 2 premises
                            EQ_RESOLVE, 2 premises
                            SYMM, 1 premises
                              dslRewrite arith-elim-lt #[x, 2]
                  scope, discharging #[(= x 1)]
                    cong of 1 on (f x)
                      assume (= x 1)
          naryCong of 3 on (or (not (>= x 1)) (not (not (>= x 2))) (= (f x) (f 1)))
            refl (not (>= x 1))
            dslRewrite bool-double-not-elim #[(>= x 2)]
            refl (= (f x) (f 1))
      EQ_RESOLVE, 2 premises
        assume (distinct (f x) (f 1))
        theoryRewrite distinct-elim
      EQ_RESOLVE, 2 premises
      assume (>= x 1)
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    for line in render p do println! "{line}"

/-! Which rules come out as `other` is what a cvc5 upgrade would change first, so it is pinned: a
decoded rule whose layout moved would show up here. -/

/-- info: b ∧ ¬b: #[]
congruence: #[ARITH_TRICHOTOMY, INT_TIGHT_UB]
-/
#guard_msgs in #eval Env.runIO do
  for (name, problem) in [("b ∧ ¬b", contradiction), ("congruence", congruence)] do
    let s ← solverWith problem
    let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
    let others := proofs.fold #[] (m := Id) (pre := fun _ v acc => return .descend <|
      match v with
      | .other rule .. => if acc.contains rule then acc else acc.push rule
      | _ => acc)
    println! "{name}: {others}"

/-! ## Sharing

cvc5 shares a sub-proof between the steps that use it, and proofs are equal by identity, so every
traversal visits a shared step once. `revisit` visits it on every path instead.
-/

/-- info: distinct steps : 41
every path     : 55
steps equal to themselves only : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    let reached := p.fold 0 (m := Id) (revisit := true)
      (pre := fun _ _ n => return .descend (n + 1))
    println! "distinct steps : {p.size}"
    println! "every path     : {reached}"
    println! "steps equal to themselves only : {(steps p).all fun q => (steps p).count q == 1}"

/-! ## Ending early

`pre` answers `stop` to end the fold and `skip` to leave a step's premises out; `post` can stop too.
`break` ends a `for` loop over the steps.
-/

/-- info: clauses resolved : #[(or (>= x 2) (= (f x) (f 1)) (not (>= x 1))), (not (= (f x) (f 1))), (not (>= x 2)), (>= x 1)]
steps, lemmas skipped : 16 of 41
first rewrite rule : (some arith-leq-norm)
first leaf at depth : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    -- the clauses the SAT solver resolved: the premises of the first resolution step reached
    let clauses := p.fold #[] (m := Id) (pre := fun _ v acc => return match v with
      | .chainMResolution ps _ => .stop (ps.map (·.getResult))
      | _ => .descend acc)
    println! "clauses resolved : {clauses}"
    -- the steps outside the theory lemmas, which are below the clauses being reordered
    let outside := p.fold 0 (m := Id) (pre := fun _ v n => return match v with
      | .reordering _ => .skip (n + 1)
      | _ => .descend (n + 1))
    println! "steps, lemmas skipped : {outside} of {p.size}"
    -- the first rewrite rule reached
    let mut first := none
    for q in p do
      if let some rule := q.getRewriteRule? then
        first := some rule
        break
    println! "first rewrite rule : {first}"
    -- the depth of the first leaf, stopping on leaving it
    let depth := p.fold (0, 0) (m := Id)
      (pre := fun _ _ (d, _) => return .descend (d + 1, d + 1))
      (post := fun q _ (d, deepest) =>
        return if q.getChildren.isEmpty then .stop (d, deepest) else .continue (d - 1, deepest))
    println! "first leaf at depth : {depth.1}"

/-! ## In any monad

The fold's functions run in the caller's monad, here `Env`, printing as they go.
-/

/-- info: assumption 12 : (>= x 1)
assumption 14 : (<= x 1)
assumption 23 : (>= x 1)
assumption 31 : (= x 1)
assumption 37 : (distinct (f x) (f 1))
assumption 40 : (>= x 1)
steps entered : 41
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    let n ← p.fold 0 (pre := fun _ v n => do
      if let .assume f := v then println! "assumption {n} : {f}"
      return .descend (n + 1))
    println! "steps entered : {n}"

/-! ## Bottom-up

`foldUp` computes a value for each distinct step from its premises' values, which its view holds in
place of the premises. It is called once per distinct step, however many paths reach one.
-/

/-- info: as a term : (λ (λ (contra ⟨b⟩ ⟨(not b)⟩))) -/
#guard_msgs in #eval Env.runIO do
  let s ← solver
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    let term := p.foldUp (m := Id) fun _ v => match v with
      | .assume f => s!"⟨{f}⟩"
      | .scope body _ => s!"(λ {body})"
      | .contra h n => s!"(contra {h} {n})"
      | v => s!"({v.rule} {" ".intercalate v.premises.toList})"
    println! "as a term : {term}"

/-- info: as a tree : 55 steps
computed  : 41 times, the distinct steps
rebuilt   : cannot rebuild INT_TIGHT_UB
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    -- the size of the proof as a tree, every shared step counted on every path to it
    let (tree, calls) := (p.foldUp fun _ v => do
      modify (· + 1)
      return v.premises.foldl (· + ·) 1 : StateM Nat Nat).run 0
    println! "as a tree : {tree} steps"
    println! "computed  : {calls} times, the distinct steps"
    -- giving up on the first step that is not decoded, as a reconstruction would
    let rebuilt : Except String Unit := p.foldUp fun q v => match v with
      | .other .. => throw s!"cannot rebuild {q.getRule}"
      | _ => return ()
    println! "rebuilt   : {match rebuilt with | .ok () => "yes" | .error e => e}"

/-! ## Questions about a proof

A `full` proof leaves no assumption open — its root scope discharges the assertions — but the
refutation below that scope does, and those are the assertions it uses.
-/

/-- info: rules : #[(SCOPE, 5), (CHAIN_M_RESOLUTION, 1), (REORDERING, 1), (EQ_RESOLVE, 6), (RESOLUTION, 1), (CNF_AND_NEG, 1), (IMPLIES_ELIM, 1), (MODUS_PONENS, 2), (AND_INTRO, 1), (ASSUME, 6), (TRANS, 1), (DSL_REWRITE, 3), (CONG, 3), (REFL, 3), (EVALUATE, 1), (ARITH_TRICHOTOMY, 1), (INT_TIGHT_UB, 1), (SYMM, 1), (NARY_CONG, 1), (THEORY_REWRITE, 1)]
open  : #[]
used  : #[(<= x 1), (distinct (f x) (f 1)), (>= x 1)]
trusted steps : 0
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let proofs ← s.checkSat (ifUnsat := do return ← s.getUnsatProof)
  for p in proofs do
    println! "rules : {p.ruleCounts}"
    println! "open  : {p.freeAssumptions}"
    if let .scope outer _ := p.view then
      if let .scope refutation _ := outer.view then
        println! "used  : {refutation.freeAssumptions}"
    println! "trusted steps : {p.trusted.size}"

/-! ## Several proofs

A component other than `full` can answer several proofs — one per theory lemma, for the
`theoryLemmas` component — and `Solver.Proofs.fold`/`foldUp` go over all of them, a step they share
being visited once in all. Each lemma is its proof's conclusion.
-/

/-- info: lemma : (or (>= x 2) (= (f x) (f 1)) (not (>= x 1)))
assumed within : #[(>= x 1), (not (>= x 2)), (>= x 1), (not (>= x 2)), (= x 1)]
tree sizes : #[28]
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let lemmas ← s.checkSat (ifUnsat := do return ← s.getUnsatProof .theoryLemmas)
  for p in lemmas do println! "lemma : {p.getResult}"
  let assumed := lemmas.fold #[] (m := Id) (pre := fun _ v acc => return .descend <|
    match v with
    | .assume f => acc.push f
    | _ => acc)
  println! "assumed within : {assumed}"
  let sizes := lemmas.foldUp (m := Id) fun _ v => return v.premises.foldl (· + ·) 1
  println! "tree sizes : {sizes}"

/-! ## Every step answers

No proof cvc5 hands back is the null proof: every step of every component answers its rule, its
conclusion, its arguments and its view.
-/

/-- info: Cvc.Proof.Component.rawPreprocess: 4 proofs, 13 steps, 13 arguments, views agree: true
Cvc.Proof.Component.preprocess: 3 proofs, 12 steps, 12 arguments, views agree: true
Cvc.Proof.Component.sat: 1 proofs, 5 steps, 7 arguments, views agree: true
Cvc.Proof.Component.theoryLemmas: 1 proofs, 28 steps, 20 arguments, views agree: true
Cvc.Proof.Component.full: 1 proofs, 41 steps, 39 arguments, views agree: true
-/
#guard_msgs in #eval Env.runIO do
  let s ← solverWith congruence
  let lines ← s.checkSat (ifUnsat := do
    let mut lines := #[]
    for pc in [Proof.Component.rawPreprocess, .preprocess, .sat, .theoryLemmas, .full] do
      let proofs ← s.getUnsatProof pc
      let (steps, args, agree) := proofs.fold (0, 0, true) (m := Id)
        (pre := fun q v (n, args, agree) =>
          let agree := agree && v.rule == q.getRule && q.getResult == q.getResult
          return .descend (n + 1, args + q.getArguments.size, agree))
      lines := lines.push
        s!"{repr pc}: {proofs.size} proofs, {steps} steps, {args} arguments, views agree: {agree}"
    return lines)
  for line in lines do println! line

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
