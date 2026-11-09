/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Defs
public import Cvc.Basic.Traverse
import Std.Data.HashMap
import Std.Data.HashSet



/-! # Proofs, whichever the layer

What the two layers' proof APIs share: `Proof.View`, a proof step taken apart, and the traversals
both layers build `fold`, `foldUp` and their `ForIn` instance on. Nothing here mentions a solver or
a term; the layers instantiate it — `Cvc.Untyped.Solver.Proof` and `Cvc.Typed.Solver.Proof`.

**A proof is a graph, not a tree.** cvc5 shares a sub-proof between the steps that use it, so a
step can be reached along many paths, and a traversal that does not remember what it has visited
redoes the work every time — exponentially often in the worst case. Both traversals here visit each
distinct step once, telling steps apart by identity.
-/

namespace Cvc.Proof public section



/-! ## Taking a step apart -/

/-- One step of a cvc5 proof: its rule as a constructor, its premises and arguments as fields.

The parameters say what the fields are, so that each layer picks its own, and so that a traversal
can hand over a step whose premises are something else entirely:

- `P` is a premise — a proof, or what a bottom-up traversal computed for one;
- `F` is a formula — a sort-erased term, or a typed `Term Bool`;
- `T` is a term of any sort.

The conclusion is not a field: it is the step's own result. Neither is an argument that only
restates it, such as `REORDERING`'s target clause or `THEORY_REWRITE`'s equality.

A rule is decoded only when its step has the layout cvc5 documents; anything else is `other`,
holding the step's premises and arguments as cvc5 gives them. So no step is lost, and a layout cvc5
changes degrades to `other` rather than to a wrong reading. Which rules are decoded can grow, and a
rule moving out of `other` is the change to expect from one version to the next.

Which rules appear at all depends on cvc5's `proof-granularity` option. Coarse settings leave
`MACRO_…` steps, which are `other` here; `dsl-rewrite` breaks rewriting down into `dslRewrite`,
`theoryRewrite` and the equality rules.
-/
inductive View (P F T : Type) where
  -- Assumptions
  /-- `ASSUME`, an open leaf: concludes `f`, unless an enclosing `scope` discharges it. -/
  | assume (f : F)
  /-- `SCOPE`: discharges `discharged` from `body : F`, concluding `F₁ ∧ … ∧ Fₙ ⇒ F`.

  When `F` is `false`, the conclusion is `¬(F₁ ∧ … ∧ Fₙ)` instead.
  -/
  | scope (body : P) (discharged : Array F)
  -- Rewriting
  /-- `EVALUATE`: `t = v`, `v` being the value `t` evaluates to. -/
  | evaluate (t : T)
  /-- `DSL_REWRITE`: an instance of the RARE rule `rule`, its variables instantiated in order.

  The premises are the rule's conditions, instantiated likewise. A variable with list semantics is
  instantiated with the list of terms it stands for.
  -/
  | dslRewrite (rule : ProofRewriteRule) (premises : Array P) (instantiation : Array T)
  /-- `THEORY_REWRITE`: `t = t'`, the conclusion, by the theory rewrite rule `rule`. -/
  | theoryRewrite (rule : ProofRewriteRule)
  /-- `ACI_NORM`: `t = s`, equal modulo associativity, commutativity, idempotence and identity. -/
  | aciNorm
  /-- `ABSORB`: `t = z`, `z` being a zero element `t` contains beneath its operator. -/
  | absorb
  -- Trusted steps
  /-- `TRUST`: a step cvc5 does not justify, `id` saying what kind of step it is.

  The premises, possibly none, entail the conclusion; `extra` is whatever further arguments cvc5
  recorded. `id` is cvc5's internal trust identifier, which its API does not name.
  -/
  | trust (id : Nat) (premises : Array P) (extra : Array T)
  /-- `TRUST_THEORY_REWRITE`: an unchecked theory rewrite, the equality being the conclusion.

  `theory` identifies the theory whose rewriter applied and `method` the kind of rewriting; both are
  cvc5's internal identifiers, which its API does not name.
  -/
  | trustTheoryRewrite (theory method : Nat)
  /-- `SAT_REFUTATION`: `false` from the clauses `premises`, the SAT solver's unsat core. -/
  | satRefutation (premises : Array P)
  -- Resolution
  /-- `RESOLUTION` of `left` and `right` on `pivot`.

  The pivot occurs in `left` as is and in `right` negated when `polarity` is `true`, the other way
  round when it is `false`.
  -/
  | resolution (left right : P) (polarity : Bool) (pivot : F)
  /-- `CHAIN_RESOLUTION`: resolves `premises` left to right, step `i` on `steps[i]`'s pivot.

  Each step is a polarity and a pivot, as in `resolution`, and there is one step fewer than there
  are premises.
  -/
  | chainResolution (premises : Array P) (steps : Array (Bool × F))
  /-- `CHAIN_M_RESOLUTION`: `chainResolution` with factoring and reordering.

  The conclusion is the result of the resolution as a set of literals.
  -/
  | chainMResolution (premises : Array P) (steps : Array (Bool × F))
  /-- `FACTORING`: `premise`'s clause, every literal's repetitions dropped. -/
  | factoring (premise : P)
  /-- `REORDERING`: `premise`'s clause, its literals in the conclusion's order. -/
  | reordering (premise : P)
  /-- `SPLIT`: `f ∨ ¬f`. -/
  | split (f : F)
  -- Boolean reasoning
  /-- `EQ_RESOLVE`: `F₂` from `premise : F₁` and `equiv : F₁ = F₂`. -/
  | eqResolve (premise equiv : P)
  /-- `MODUS_PONENS`: `F₂` from `premise : F₁` and `implication : F₁ ⇒ F₂`. -/
  | modusPonens (premise implication : P)
  /-- `NOT_NOT_ELIM`: `F` from `¬¬F`. -/
  | notNotElim (premise : P)
  /-- `CONTRA`: `false` from `premise : F` and `negation : ¬F`. -/
  | contra (premise negation : P)
  /-- `AND_ELIM`: the conjunct at `index` of `premise : F₀ ∧ … ∧ Fₙ`, counting from zero. -/
  | andElim (premise : P) (index : Nat)
  /-- `AND_INTRO`: the conjunction of the premises' conclusions. -/
  | andIntro (premises : Array P)
  /-- `NOT_OR_ELIM`: `¬Fᵢ` from `premise : ¬(F₀ ∨ … ∨ Fₙ)`, `i` being `index`, from zero. -/
  | notOrElim (premise : P) (index : Nat)
  /-- `IMPLIES_ELIM`: `¬F₁ ∨ F₂` from `F₁ ⇒ F₂`. -/
  | impliesElim (premise : P)
  /-- `NOT_IMPLIES_ELIM1`: `F₁` from `¬(F₁ ⇒ F₂)`. -/
  | notImpliesElim1 (premise : P)
  /-- `NOT_IMPLIES_ELIM2`: `¬F₂` from `¬(F₁ ⇒ F₂)`. -/
  | notImpliesElim2 (premise : P)
  /-- `EQUIV_ELIM1`: `¬F₁ ∨ F₂` from `F₁ = F₂`. -/
  | equivElim1 (premise : P)
  /-- `EQUIV_ELIM2`: `F₁ ∨ ¬F₂` from `F₁ = F₂`. -/
  | equivElim2 (premise : P)
  /-- `NOT_EQUIV_ELIM1`: `F₁ ∨ F₂` from `F₁ ≠ F₂`. -/
  | notEquivElim1 (premise : P)
  /-- `NOT_EQUIV_ELIM2`: `¬F₁ ∨ ¬F₂` from `F₁ ≠ F₂`. -/
  | notEquivElim2 (premise : P)
  /-- `XOR_ELIM1`: `F₁ ∨ F₂` from `F₁ ⊕ F₂`. -/
  | xorElim1 (premise : P)
  /-- `XOR_ELIM2`: `¬F₁ ∨ ¬F₂` from `F₁ ⊕ F₂`. -/
  | xorElim2 (premise : P)
  /-- `NOT_XOR_ELIM1`: `F₁ ∨ ¬F₂` from `¬(F₁ ⊕ F₂)`. -/
  | notXorElim1 (premise : P)
  /-- `NOT_XOR_ELIM2`: `¬F₁ ∨ F₂` from `¬(F₁ ⊕ F₂)`. -/
  | notXorElim2 (premise : P)
  /-- `ITE_ELIM1`: `¬C ∨ F₁` from `ite C F₁ F₂`. -/
  | iteElim1 (premise : P)
  /-- `ITE_ELIM2`: `C ∨ F₂` from `ite C F₁ F₂`. -/
  | iteElim2 (premise : P)
  /-- `NOT_ITE_ELIM1`: `¬C ∨ ¬F₁` from `¬(ite C F₁ F₂)`. -/
  | notIteElim1 (premise : P)
  /-- `NOT_ITE_ELIM2`: `C ∨ ¬F₂` from `¬(ite C F₁ F₂)`. -/
  | notIteElim2 (premise : P)
  /-- `NOT_AND`: `¬F₁ ∨ … ∨ ¬Fₙ` from `¬(F₁ ∧ … ∧ Fₙ)`. -/
  | notAnd (premise : P)
  -- Clausal form
  /-- `CNF_AND_POS`: `¬f ∨ Fᵢ`, `f` being `F₀ ∧ … ∧ Fₙ` and `i` `index`, counting from zero. -/
  | cnfAndPos (f : F) (index : Nat)
  /-- `CNF_AND_NEG`: `f ∨ ¬F₁ ∨ … ∨ ¬Fₙ`, `f` being `F₁ ∧ … ∧ Fₙ`. -/
  | cnfAndNeg (f : F)
  /-- `CNF_OR_POS`: `¬f ∨ F₁ ∨ … ∨ Fₙ`, `f` being `F₁ ∨ … ∨ Fₙ`. -/
  | cnfOrPos (f : F)
  /-- `CNF_OR_NEG`: `f ∨ ¬Fᵢ`, `f` being `F₀ ∨ … ∨ Fₙ` and `i` `index`, counting from zero. -/
  | cnfOrNeg (f : F) (index : Nat)
  /-- `CNF_IMPLIES_POS`: `¬f ∨ ¬F₁ ∨ F₂`, `f` being `F₁ ⇒ F₂`. -/
  | cnfImpliesPos (f : F)
  /-- `CNF_IMPLIES_NEG1`: `f ∨ F₁`, `f` being `F₁ ⇒ F₂`. -/
  | cnfImpliesNeg1 (f : F)
  /-- `CNF_IMPLIES_NEG2`: `f ∨ ¬F₂`, `f` being `F₁ ⇒ F₂`. -/
  | cnfImpliesNeg2 (f : F)
  /-- `CNF_EQUIV_POS1`: `¬f ∨ ¬F₁ ∨ F₂`, `f` being `F₁ = F₂`. -/
  | cnfEquivPos1 (f : F)
  /-- `CNF_EQUIV_POS2`: `¬f ∨ F₁ ∨ ¬F₂`, `f` being `F₁ = F₂`. -/
  | cnfEquivPos2 (f : F)
  /-- `CNF_EQUIV_NEG1`: `f ∨ F₁ ∨ F₂`, `f` being `F₁ = F₂`. -/
  | cnfEquivNeg1 (f : F)
  /-- `CNF_EQUIV_NEG2`: `f ∨ ¬F₁ ∨ ¬F₂`, `f` being `F₁ = F₂`. -/
  | cnfEquivNeg2 (f : F)
  /-- `CNF_XOR_POS1`: `¬f ∨ F₁ ∨ F₂`, `f` being `F₁ ⊕ F₂`. -/
  | cnfXorPos1 (f : F)
  /-- `CNF_XOR_POS2`: `¬f ∨ ¬F₁ ∨ ¬F₂`, `f` being `F₁ ⊕ F₂`. -/
  | cnfXorPos2 (f : F)
  /-- `CNF_XOR_NEG1`: `f ∨ ¬F₁ ∨ F₂`, `f` being `F₁ ⊕ F₂`. -/
  | cnfXorNeg1 (f : F)
  /-- `CNF_XOR_NEG2`: `f ∨ F₁ ∨ ¬F₂`, `f` being `F₁ ⊕ F₂`. -/
  | cnfXorNeg2 (f : F)
  /-- `CNF_ITE_POS1`: `¬f ∨ ¬C ∨ F₁`, `f` being `ite C F₁ F₂`. -/
  | cnfItePos1 (f : F)
  /-- `CNF_ITE_POS2`: `¬f ∨ C ∨ F₂`, `f` being `ite C F₁ F₂`. -/
  | cnfItePos2 (f : F)
  /-- `CNF_ITE_POS3`: `¬f ∨ F₁ ∨ F₂`, `f` being `ite C F₁ F₂`. -/
  | cnfItePos3 (f : F)
  /-- `CNF_ITE_NEG1`: `f ∨ ¬C ∨ ¬F₁`, `f` being `ite C F₁ F₂`. -/
  | cnfIteNeg1 (f : F)
  /-- `CNF_ITE_NEG2`: `f ∨ C ∨ ¬F₂`, `f` being `ite C F₁ F₂`. -/
  | cnfIteNeg2 (f : F)
  /-- `CNF_ITE_NEG3`: `f ∨ ¬F₁ ∨ ¬F₂`, `f` being `ite C F₁ F₂`. -/
  | cnfIteNeg3 (f : F)
  -- Equality
  /-- `REFL`: `t = t`. -/
  | refl (t : T)
  /-- `SYMM`: `t₂ = t₁` from `t₁ = t₂`, or `t₂ ≠ t₁` from `t₁ ≠ t₂`. -/
  | symm (premise : P)
  /-- `TRANS`: `t₁ = tₙ` from the chain `t₁ = t₂`, …, `tₙ₋₁ = tₙ`. -/
  | trans (premises : Array P)
  /-- `CONG`: `f(t₁, …, tₙ) = f(s₁, …, sₙ)` from `tᵢ = sᵢ`, `app` being `f(t₁, …, tₙ)`.

  Used for operators of fixed arity, indexed ones and uninterpreted functions included.
  -/
  | cong (premises : Array P) (app : T)
  /-- `NARY_CONG`: `cong` for a variadic, associative operator such as `and` or `+`. -/
  | naryCong (premises : Array P) (app : T)
  /-- `PAIRWISE_CONG`: `cong` for a variadic, pairwise operator, which today means `distinct`. -/
  | pairwiseCong (premises : Array P) (app : T)
  /-- `TRUE_INTRO`: `F = true` from `F`. -/
  | trueIntro (premise : P)
  /-- `TRUE_ELIM`: `F` from `F = true`. -/
  | trueElim (premise : P)
  /-- `FALSE_INTRO`: `F = false` from `¬F`. -/
  | falseIntro (premise : P)
  /-- `FALSE_ELIM`: `¬F` from `F = false`. -/
  | falseElim (premise : P)
  -- Everything else
  /-- Any other step, as cvc5 gives it: a rule not decoded, or a step whose layout was not expected.

  Which rules are decoded grows over time, so a pattern `.other .SOME_RULE …` stops matching
  once that rule is decoded: match on the step's rule instead for a rule not decoded.
  -/
  | other (rule : ProofRule) (premises : Array P) (args : Array T)

/-- The rule a step applies. -/
def View.rule : View P F T → ProofRule
  | .assume .. => .ASSUME
  | .scope .. => .SCOPE
  | .evaluate .. => .EVALUATE
  | .dslRewrite .. => .DSL_REWRITE
  | .theoryRewrite .. => .THEORY_REWRITE
  | .aciNorm .. => .ACI_NORM
  | .absorb .. => .ABSORB
  | .trust .. => .TRUST
  | .trustTheoryRewrite .. => .TRUST_THEORY_REWRITE
  | .satRefutation .. => .SAT_REFUTATION
  | .resolution .. => .RESOLUTION
  | .chainResolution .. => .CHAIN_RESOLUTION
  | .chainMResolution .. => .CHAIN_M_RESOLUTION
  | .factoring .. => .FACTORING
  | .reordering .. => .REORDERING
  | .split .. => .SPLIT
  | .eqResolve .. => .EQ_RESOLVE
  | .modusPonens .. => .MODUS_PONENS
  | .notNotElim .. => .NOT_NOT_ELIM
  | .contra .. => .CONTRA
  | .andElim .. => .AND_ELIM
  | .andIntro .. => .AND_INTRO
  | .notOrElim .. => .NOT_OR_ELIM
  | .impliesElim .. => .IMPLIES_ELIM
  | .notImpliesElim1 .. => .NOT_IMPLIES_ELIM1
  | .notImpliesElim2 .. => .NOT_IMPLIES_ELIM2
  | .equivElim1 .. => .EQUIV_ELIM1
  | .equivElim2 .. => .EQUIV_ELIM2
  | .notEquivElim1 .. => .NOT_EQUIV_ELIM1
  | .notEquivElim2 .. => .NOT_EQUIV_ELIM2
  | .xorElim1 .. => .XOR_ELIM1
  | .xorElim2 .. => .XOR_ELIM2
  | .notXorElim1 .. => .NOT_XOR_ELIM1
  | .notXorElim2 .. => .NOT_XOR_ELIM2
  | .iteElim1 .. => .ITE_ELIM1
  | .iteElim2 .. => .ITE_ELIM2
  | .notIteElim1 .. => .NOT_ITE_ELIM1
  | .notIteElim2 .. => .NOT_ITE_ELIM2
  | .notAnd .. => .NOT_AND
  | .cnfAndPos .. => .CNF_AND_POS
  | .cnfAndNeg .. => .CNF_AND_NEG
  | .cnfOrPos .. => .CNF_OR_POS
  | .cnfOrNeg .. => .CNF_OR_NEG
  | .cnfImpliesPos .. => .CNF_IMPLIES_POS
  | .cnfImpliesNeg1 .. => .CNF_IMPLIES_NEG1
  | .cnfImpliesNeg2 .. => .CNF_IMPLIES_NEG2
  | .cnfEquivPos1 .. => .CNF_EQUIV_POS1
  | .cnfEquivPos2 .. => .CNF_EQUIV_POS2
  | .cnfEquivNeg1 .. => .CNF_EQUIV_NEG1
  | .cnfEquivNeg2 .. => .CNF_EQUIV_NEG2
  | .cnfXorPos1 .. => .CNF_XOR_POS1
  | .cnfXorPos2 .. => .CNF_XOR_POS2
  | .cnfXorNeg1 .. => .CNF_XOR_NEG1
  | .cnfXorNeg2 .. => .CNF_XOR_NEG2
  | .cnfItePos1 .. => .CNF_ITE_POS1
  | .cnfItePos2 .. => .CNF_ITE_POS2
  | .cnfItePos3 .. => .CNF_ITE_POS3
  | .cnfIteNeg1 .. => .CNF_ITE_NEG1
  | .cnfIteNeg2 .. => .CNF_ITE_NEG2
  | .cnfIteNeg3 .. => .CNF_ITE_NEG3
  | .refl .. => .REFL
  | .symm .. => .SYMM
  | .trans .. => .TRANS
  | .cong .. => .CONG
  | .naryCong .. => .NARY_CONG
  | .pairwiseCong .. => .PAIRWISE_CONG
  | .trueIntro .. => .TRUE_INTRO
  | .trueElim .. => .TRUE_ELIM
  | .falseIntro .. => .FALSE_INTRO
  | .falseElim .. => .FALSE_ELIM
  | .other rule .. => rule

/-- A step's premises, in the order cvc5 gives them. -/
def View.premises : View P F T → Array P
  | .assume _ => #[]
  | .scope body _ => #[body]
  | .evaluate _ => #[]
  | .dslRewrite _ premises _ => premises
  | .theoryRewrite _ => #[]
  | .aciNorm => #[]
  | .absorb => #[]
  | .trust _ premises _ => premises
  | .trustTheoryRewrite _ _ => #[]
  | .satRefutation premises => premises
  | .resolution left right _ _ => #[left] ++ #[right]
  | .chainResolution premises _ => premises
  | .chainMResolution premises _ => premises
  | .factoring premise => #[premise]
  | .reordering premise => #[premise]
  | .split _ => #[]
  | .eqResolve premise equiv => #[premise] ++ #[equiv]
  | .modusPonens premise implication => #[premise] ++ #[implication]
  | .notNotElim premise => #[premise]
  | .contra premise negation => #[premise] ++ #[negation]
  | .andElim premise _ => #[premise]
  | .andIntro premises => premises
  | .notOrElim premise _ => #[premise]
  | .impliesElim premise => #[premise]
  | .notImpliesElim1 premise => #[premise]
  | .notImpliesElim2 premise => #[premise]
  | .equivElim1 premise => #[premise]
  | .equivElim2 premise => #[premise]
  | .notEquivElim1 premise => #[premise]
  | .notEquivElim2 premise => #[premise]
  | .xorElim1 premise => #[premise]
  | .xorElim2 premise => #[premise]
  | .notXorElim1 premise => #[premise]
  | .notXorElim2 premise => #[premise]
  | .iteElim1 premise => #[premise]
  | .iteElim2 premise => #[premise]
  | .notIteElim1 premise => #[premise]
  | .notIteElim2 premise => #[premise]
  | .notAnd premise => #[premise]
  | .cnfAndPos _ _ => #[]
  | .cnfAndNeg _ => #[]
  | .cnfOrPos _ => #[]
  | .cnfOrNeg _ _ => #[]
  | .cnfImpliesPos _ => #[]
  | .cnfImpliesNeg1 _ => #[]
  | .cnfImpliesNeg2 _ => #[]
  | .cnfEquivPos1 _ => #[]
  | .cnfEquivPos2 _ => #[]
  | .cnfEquivNeg1 _ => #[]
  | .cnfEquivNeg2 _ => #[]
  | .cnfXorPos1 _ => #[]
  | .cnfXorPos2 _ => #[]
  | .cnfXorNeg1 _ => #[]
  | .cnfXorNeg2 _ => #[]
  | .cnfItePos1 _ => #[]
  | .cnfItePos2 _ => #[]
  | .cnfItePos3 _ => #[]
  | .cnfIteNeg1 _ => #[]
  | .cnfIteNeg2 _ => #[]
  | .cnfIteNeg3 _ => #[]
  | .refl _ => #[]
  | .symm premise => #[premise]
  | .trans premises => premises
  | .cong premises _ => premises
  | .naryCong premises _ => premises
  | .pairwiseCong premises _ => premises
  | .trueIntro premise => #[premise]
  | .trueElim premise => #[premise]
  | .falseIntro premise => #[premise]
  | .falseElim premise => #[premise]
  | .other _ premises _ => premises

/-- Maps a step's premises, formulas and terms, in a monad. -/
def View.mapM [Monad m] (fp : P → m P') (ff : F → m F') (ft : T → m T')
: View P F T → m (View P' F' T')
  | .assume f => return .assume (← ff f)
  | .scope body discharged => return .scope (← fp body) (← discharged.mapM ff)
  | .evaluate t => return .evaluate (← ft t)
  | .dslRewrite rule premises instantiation =>
    return .dslRewrite rule (← premises.mapM fp) (← instantiation.mapM ft)
  | .theoryRewrite rule => return .theoryRewrite rule
  | .aciNorm => return .aciNorm
  | .absorb => return .absorb
  | .trust id premises extra => return .trust id (← premises.mapM fp) (← extra.mapM ft)
  | .trustTheoryRewrite theory method => return .trustTheoryRewrite theory method
  | .satRefutation premises => return .satRefutation (← premises.mapM fp)
  | .resolution left right polarity pivot =>
    return .resolution (← fp left) (← fp right) polarity (← ff pivot)
  | .chainResolution premises steps =>
    return .chainResolution (← premises.mapM fp) (← steps.mapM fun (b, f) => (b, ·) <$> ff f)
  | .chainMResolution premises steps =>
    return .chainMResolution (← premises.mapM fp) (← steps.mapM fun (b, f) => (b, ·) <$> ff f)
  | .factoring premise => return .factoring (← fp premise)
  | .reordering premise => return .reordering (← fp premise)
  | .split f => return .split (← ff f)
  | .eqResolve premise equiv => return .eqResolve (← fp premise) (← fp equiv)
  | .modusPonens premise implication => return .modusPonens (← fp premise) (← fp implication)
  | .notNotElim premise => return .notNotElim (← fp premise)
  | .contra premise negation => return .contra (← fp premise) (← fp negation)
  | .andElim premise index => return .andElim (← fp premise) index
  | .andIntro premises => return .andIntro (← premises.mapM fp)
  | .notOrElim premise index => return .notOrElim (← fp premise) index
  | .impliesElim premise => return .impliesElim (← fp premise)
  | .notImpliesElim1 premise => return .notImpliesElim1 (← fp premise)
  | .notImpliesElim2 premise => return .notImpliesElim2 (← fp premise)
  | .equivElim1 premise => return .equivElim1 (← fp premise)
  | .equivElim2 premise => return .equivElim2 (← fp premise)
  | .notEquivElim1 premise => return .notEquivElim1 (← fp premise)
  | .notEquivElim2 premise => return .notEquivElim2 (← fp premise)
  | .xorElim1 premise => return .xorElim1 (← fp premise)
  | .xorElim2 premise => return .xorElim2 (← fp premise)
  | .notXorElim1 premise => return .notXorElim1 (← fp premise)
  | .notXorElim2 premise => return .notXorElim2 (← fp premise)
  | .iteElim1 premise => return .iteElim1 (← fp premise)
  | .iteElim2 premise => return .iteElim2 (← fp premise)
  | .notIteElim1 premise => return .notIteElim1 (← fp premise)
  | .notIteElim2 premise => return .notIteElim2 (← fp premise)
  | .notAnd premise => return .notAnd (← fp premise)
  | .cnfAndPos f index => return .cnfAndPos (← ff f) index
  | .cnfAndNeg f => return .cnfAndNeg (← ff f)
  | .cnfOrPos f => return .cnfOrPos (← ff f)
  | .cnfOrNeg f index => return .cnfOrNeg (← ff f) index
  | .cnfImpliesPos f => return .cnfImpliesPos (← ff f)
  | .cnfImpliesNeg1 f => return .cnfImpliesNeg1 (← ff f)
  | .cnfImpliesNeg2 f => return .cnfImpliesNeg2 (← ff f)
  | .cnfEquivPos1 f => return .cnfEquivPos1 (← ff f)
  | .cnfEquivPos2 f => return .cnfEquivPos2 (← ff f)
  | .cnfEquivNeg1 f => return .cnfEquivNeg1 (← ff f)
  | .cnfEquivNeg2 f => return .cnfEquivNeg2 (← ff f)
  | .cnfXorPos1 f => return .cnfXorPos1 (← ff f)
  | .cnfXorPos2 f => return .cnfXorPos2 (← ff f)
  | .cnfXorNeg1 f => return .cnfXorNeg1 (← ff f)
  | .cnfXorNeg2 f => return .cnfXorNeg2 (← ff f)
  | .cnfItePos1 f => return .cnfItePos1 (← ff f)
  | .cnfItePos2 f => return .cnfItePos2 (← ff f)
  | .cnfItePos3 f => return .cnfItePos3 (← ff f)
  | .cnfIteNeg1 f => return .cnfIteNeg1 (← ff f)
  | .cnfIteNeg2 f => return .cnfIteNeg2 (← ff f)
  | .cnfIteNeg3 f => return .cnfIteNeg3 (← ff f)
  | .refl t => return .refl (← ft t)
  | .symm premise => return .symm (← fp premise)
  | .trans premises => return .trans (← premises.mapM fp)
  | .cong premises app => return .cong (← premises.mapM fp) (← ft app)
  | .naryCong premises app => return .naryCong (← premises.mapM fp) (← ft app)
  | .pairwiseCong premises app => return .pairwiseCong (← premises.mapM fp) (← ft app)
  | .trueIntro premise => return .trueIntro (← fp premise)
  | .trueElim premise => return .trueElim (← fp premise)
  | .falseIntro premise => return .falseIntro (← fp premise)
  | .falseElim premise => return .falseElim (← fp premise)
  | .other rule premises args => return .other rule (← premises.mapM fp) (← args.mapM ft)

/-- Maps a step's premises, formulas and terms. -/
def View.map (fp : P → P') (ff : F → F') (ft : T → T') (v : View P F T) : View P' F' T' :=
  Id.run (v.mapM (fun p => return fp p) (fun f => return ff f) (fun t => return ft t))



/-! ## Traversing -/

/-- A pending step of `foldWith`. -/
private inductive FoldTask (P N : Type) where
  | enter (p : P)
  | leave (n : N)

/-- Folds over the distinct steps reachable from `roots`, each presented as `present` builds it.

What both layers' `fold` are built on. Depth-first: each step is entered — `pre` — then, unless
that answered `skip`, its premises (`kids`) are folded over left to right, and then it is left —
`post`. A step reached again is passed over entirely unless `revisit` is set, in which case it is
entered every time it is reached, which can take exponentially long on a proof sharing many
sub-proofs.
-/
def foldWith [Monad m] [BEq P] [Hashable P] (kids : P → Array P) (present : P → N)
  (roots : Array P) (init : σ) (pre : N → σ → m (FoldPre σ)) (post : N → σ → m (FoldPost σ))
  (revisit : Bool := false)
: m σ := do
  let mut tasks : List (FoldTask P N) := roots.toList.map .enter
  let mut seen : Std.HashSet P := {}
  let mut s := init
  repeat
    match tasks with
    | [] => break
    | .enter p :: rest =>
      if !revisit && seen.contains p then
        tasks := rest
      else
        seen := seen.insert p
        let n := present p
        match ← pre n s with
        | .descend s' => s := s'; tasks := (kids p).toList.map .enter ++ .leave n :: rest
        | .skip s' => s := s'; tasks := .leave n :: rest
        | .stop s' => return s'
    | .leave n :: rest =>
      match ← post n s with
      | .continue s' => s := s'; tasks := rest
      | .stop s' => return s'
  return s

/-- A pending step of `foldUpWith`. -/
private inductive FoldUpTask (P : Type) where
  | enter (p : P)
  | leave (p : P) (arity : Nat)

/-- Computes a value for every distinct step reachable from `roots`, bottom-up.

What both layers' `foldUp` are built on. `step` is handed a step and the values of its premises
(`kids`), in order, and is called once per distinct step, so a sub-proof shared by many steps is
computed once. Answers the roots' values, in order. Ending early is the monad's business, by
throwing for instance.
-/
def foldUpWith [Monad m] [BEq P] [Hashable P] (kids : P → Array P) (step : P → Array β → m β)
  (roots : Array P)
: m (Array β) := do
  let mut tasks : List (FoldUpTask P) := roots.toList.map .enter
  let mut memo : Std.HashMap P β := {}
  -- the values of the steps left so far and not yet consumed by their parent, in order
  let mut values : Array β := #[]
  repeat
    match tasks with
    | [] => break
    | .enter p :: rest =>
      match memo.get? p with
      | some b => values := values.push b; tasks := rest
      | none =>
        let ks := kids p
        tasks := ks.toList.map .enter ++ .leave p ks.size :: rest
    | .leave p arity :: rest =>
      let start := values.size - arity
      let b ← step p (values.extract start values.size)
      memo := memo.insert p b
      values := (values.extract 0 start).push b
      tasks := rest
  return values

end

end Cvc.Proof
