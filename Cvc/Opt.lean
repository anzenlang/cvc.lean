/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

/-! # Cvc5 options. -/
namespace Cvc

namespace Opt

/-- (De)activates non-clausal simplification. -/
inductive SimpMode
/-- Do not perform non-clausal simplification. -/
| none
/-- Save up all assertions; run non-clausal simplification and clausal (MiniSat) propagation for all
of them only after reaching a querying command (`checkSat` or *query* or predicate *subtype*
declaration).
-/
| batch

namespace SimpMode
protected def toString : SimpMode → String
| none => "none"
| batch => "batch"

instance : ToString SimpMode := ⟨SimpMode.toString⟩
end SimpMode

/-- Mode for producing model cores. -/
inductive ModelCoresMode
/-- Do not compute model cores. -/
| none
/-- Only include a subset of variales whose values are sufficient to show the input formula is
satsified by the given model.
-/
| simple
/-- Only include a subset of variables whose values, in addition to the values of variables whose
values are implied, are sufficient to show the input formula is satisfied by the given model.
 -/
| nonImplied

namespace ModelCoresMode
protected def toString : ModelCoresMode → String
| none => "none"
| simple => "simple"
| nonImplied => "non-implied"

instance : ToString ModelCoresMode := ⟨ModelCoresMode.toString⟩
end ModelCoresMode

/-- Proof modes. -/
inductive ProofMode
/-- Do not produce proofs. -/
| off
/-- Only produce proofs for preprocessing. -/
| ppOnly
/-- Produce proofs for preprocessing and for the SAT solver. -/
| satProof
/-- Produce full proofs of preprocessing, SAT and theory lemmas. -/
| fullProof
/-- Produce full proofs of preprocessing, SAT and theory lemmas.

Additionally disable techniques that will lead to incomplete proofs.
-/
| fullProofStrict

namespace ProofMode
protected def toString : ProofMode → String
| off => "off"
| ppOnly => "pp-only"
| satProof => "sat-proof"
| fullProof => "full-proof"
| fullProofStrict => "full-proof-strict"

instance : ToString ProofMode := ⟨ProofMode.toString⟩
end ProofMode

/-- Unsat core modes. -/
inductive UnsatCoresMode
/-- Do not produce unsat cores. -/
| off
/-- Produce unsat cores from the SAT proof and preprocessing proofs. -/
| satProof
/-- Produce unsat cores using solving under assumptions and preprocessing proofs. -/
| assumptions

namespace UnsatCoresMode
protected def toString : UnsatCoresMode → String
| off => "off"
| satProof => "sat-proof"
| assumptions => "assumptions"

instance : ToString UnsatCoresMode := ⟨UnsatCoresMode.toString⟩
end UnsatCoresMode

/-- Extended rewriter preprocessing pass modes. -/
inductive ExtRewPrepMode
/-- Do not use extended rewriter as a preprocessing pass.-/
| off
/-- Use extended rewriter as a preprocessing pass. -/
| use
/-- Use aggressive extended rewriter as a preprocessing pass. -/
| agg

namespace ExtRewPrepMode
protected def toString : ExtRewPrepMode → String
| off => "off"
| use => "use"
| agg => "agg"

instance : ToString ExtRewPrepMode := ⟨ExtRewPrepMode.toString⟩
end ExtRewPrepMode

/-- Interpolants grammar mode. -/
inductive InterpolantsMode
/-- Use the default grammar for the theory or the user-defined grammar if given. -/
| default
/-- Use only operators that occur in the assumptions. -/
| assumptions
/-- Use only operators that occur in the conjecture. -/
| conjecture
/-- Use only operators that occur both in the assumptions and the conjecture. -/
| shared
/-- Use only operators that occur either in the assumptions or the conjecture. -/
| all

namespace InterpolantsMode
protected def toString : InterpolantsMode → String
| default => "default"
| assumptions => "assumptions"
| conjecture => "conjecture"
| shared => "shared"
| all => "all"

instance : ToString InterpolantsMode := ⟨InterpolantsMode.toString⟩
end InterpolantsMode

/-- Difficulty output modes. -/
inductive DifficultyMode
/-- Difficulty of an assertion is how many lemmas (at full effort) use a literal that the assertion
depends on to be satisfied.
-/
| lemmaLiteral
/-- Difficulty of an assertion is how many lemmas use a literal that the assertion depends on to be
satisfied.
-/
| lemmaLiteralAll
/-- Difficulty of an assertion is how many times it was not satisfied in a candidate model. -/
| modelCheck

namespace DifficultyMode
protected def toString : DifficultyMode → String
| lemmaLiteral => "lemma-literal"
| lemmaLiteralAll => "lemal-literal-all"
| modelCheck => "model-check"

instance : ToString DifficultyMode := ⟨DifficultyMode.toString⟩
end DifficultyMode

inductive Common
/-- Support the `getValue` and `getModel` commands, default `false`. -/
| produceModels (active : Bool)
/-- After sat/invalid/unknown, check that the generated model satisfies user assertions, default
`false`.
-/
| checkModels (active : Bool)

namespace Common
def keyVal : Common → String × String
| produceModels active => ("produce-models", toString active)
| checkModels active => ("check-models", toString active)
end Common

inductive Regular
/-- Eliminate functions by ackermannization, default `false`. -/
| ackermann (active : Bool)
/-- Simplification mode, default `SimpMode.batch`. -/
| simpMode (mode : SimpMode)
/-- Use static learning, default `true`. -/
| staticLearning (active : Bool)
/-- Rewrite the input based on learned literals, default `false`. -/
| learnedRewrite (active : Bool)
/-- Model cores modes, default `ModelCoresMode.none`. -/
| modelCoresMode (mode : ModelCoresMode)
/-- Produce learned literals, support `getLearnedLiterals`, default `false`. -/
| produceLearnedLiterals (active : Bool)
/-- Produce proofs, support `checkProofs` and `getProof`, default `false`. -/
| produceProofs (active : Bool)
/-- After unsat/invalid, check the generated proof (with proof), default `false`. -/
| checkProofs (active : Bool)
/-- Turn on unsat core generation, default `false`.

Unless otherwise specified, cores will be produced using SAT solving under assumptions and
preprocessing proofs.
-/
| produceUnsatCores (active : Bool)
/-- Print all formulas regardless of whether they are named, *e.g.* in unsat cores, default `false`.
-/
| printCoresFull (active : Bool)
/-- After unsat/valid, produce and check an unsat core (expensive), default `false`. -/
| checkUnsatCores (active : Bool)
/-- Turn on unsat assumptions generation, default `false`. -/
| produceUnsatAssumptions (active : Bool)
/-- Enable tracking of difficulty, default `false`. -/
| produceDifficulty (active : Bool)
/-- Checks whether produced solutions to functions-to-synthesize satisfy the conjecture, default
`false`.
-/
| checkSynthSol (active : Bool)
/-- Support the `getAssignment` command, default `false`. -/
| produceAssignments (active : Bool)
/-- Keep an assertions list, default `true`.

Note that this option is always enabled.
-/
| produceAssertions (active : Bool)
/-- Extended rewriter preprocessing pass modes, default `ExtRewPrepMode.off`. -/
| extRewPrep (mode : ExtRewPrepMode)
/-- Turn on unconstrained simplification, see Bruttomesso/Brummayer PhD thesis.

Fully supported only in (subsets of) the logic `QF_ABV`.
-/
| unconstrainedSimp (active : Bool)
/-- Calculate sort inference of input problem, convert the input based on monotonic sorts. -/
| sortInference (active : Bool)
/-- Turn on interpolation generation. -/
| produceInterpolants (active : Bool)
/-- Interpolants grammar mode. -/
| interpolantsMode (mode : InterpolantsMode)

namespace Regular
def keyVal : Regular → String × String
| ackermann b => ("ackermann", toString b)
| simpMode m => ("simplification-mode", toString m)
| staticLearning b => ("static-learning", toString b)
| learnedRewrite b => ("learned-rewrite", toString b)
| modelCoresMode m => ("model-cores", toString m)
| produceLearnedLiterals b => ("produce-learned-literals", toString b)
| produceProofs b => ("produce-proofs", toString b)
| checkProofs b => ("check-proofs", toString b)
| produceUnsatCores b => ("produce-unsat-cores", toString b)
| printCoresFull b => ("print-cores-full", toString b)
| checkUnsatCores b => ("check-unsat-cores", toString b)
| produceUnsatAssumptions b => ("produce-unsat-assumptions", toString b)
| produceDifficulty b => ("produce-difficulty", toString b)
| checkSynthSol b => ("check-synth-sol", toString b)
| produceAssignments b => ("produce-assignments", toString b)
| produceAssertions b => ("produce-assertions", toString b)
| extRewPrep b => ("ext-rew-prep", toString b)
| unconstrainedSimp b => ("unconstrained-simp", toString b)
| sortInference b => ("sort-inference", toString b)
| produceInterpolants b => ("produce-interpolants", toString b)
| interpolantsMode m => ("interpolants-mode", toString m)
end Regular

inductive Expert
/-- Apply boolean constant propagation as a substitution during simplification, default `false`. -/
| simpBoolConstProp (active : Bool)
/-- After sat/invalid/unknown, check that the generated model satisfies user **and internal**
assertions, default `false`.
-/
| debugCheckModels (active : Bool)
/-- Allow variable elimination based on unevaluatable terms to variables, default `true`. -/
| modelVarElimUneval (active : Bool)
/-- Proof mode, default `ProofMode.off`. -/
| proofMode (mode : ProofMode)
/-- Unsat cores mode, default `UnsatCoresMode.off`. -/
| unsatCoresMode (mode : UnsatCoresMode)
/-- If an unsat core is produced, it is reduced to a minimal unsat core, default `false`. -/
| minimalUnsatCores (active : Bool)
/-- Difficulty mode, default `DifficultyMode.lemmaLiteralAll`. -/
| difficultyMode (mode : DifficultyMode)
/-- Turn on *if-then-else* simplification, default `false`.

See Kim (and Somenzi) et al., SAT 2009.
-/
| doIteSimp (active : Bool)
/-- Do the *if-then-else* simplification pass again if repeating simplification, default `false`. -/
| doIteSimpOnRepeat (active : Bool)
/-- Enables simplify-with-care in if-then-else simplification. -/
| simplifyWithCareEnabled (active : Bool)
/-- Enables compressing if-then-else-s after if-then-else simplification. -/
| compressItes (active : Bool)
/-- Remove if-then-else-s early in preprocessing. -/
| earlyIteRemoval (active : Bool)
/-- Make multiple passes with nonclausal simplifier. -/
| repeatSimp (active : Bool)
/-- In models, output arrays using abstract values, as required by the SMT-LIB standard.

This may support more than arrays in the future.
-/
| abstractValues (active : Bool)

namespace Expert
def keyVal : Expert → String × String
| simpBoolConstProp b => ("simplification-bcp", toString b)
| debugCheckModels b => ("debug-check-models", toString b)
| modelVarElimUneval b => ("model-var-elim-uneval", toString b)
| proofMode m => ("proof-mode", toString m)
| unsatCoresMode m => ("unsat-cores-mode", toString m)
| minimalUnsatCores b => ("minimal-unsat-cores", toString b)
| difficultyMode m => ("difficulty-mode", toString m)
| doIteSimp b => ("ite-simp", toString b)
| doIteSimpOnRepeat b => ("on-repeat-ite-simp", toString b)
| simplifyWithCareEnabled b => ("simp-with-care", toString b)
| compressItes b => ("simp-ite-compress", toString b)
| earlyIteRemoval b => ("early-ite-removal", toString b)
| repeatSimp b => ("repeat-simp", toString b)
| abstractValues b => ("abstract-values", toString b)
end Expert

end Opt



inductive Opt
| common (c : Opt.Common)
| regular (r : Opt.Regular)
| expert (e : Opt.Expert)

namespace Opt
instance instCoeCommon : Coe Common Opt := ⟨Opt.common⟩
instance instCoeRegular : Coe Regular Opt := ⟨Opt.regular⟩
instance instCoeExpert : Coe Expert Opt := ⟨Opt.expert⟩

@[inherit_doc Common.produceModels]
def produceModels (active : Bool := true) : Opt :=
  Common.produceModels active

@[inherit_doc Regular.produceProofs]
def produceProofs (active : Bool := true) : Opt :=
  Regular.produceProofs active

@[inherit_doc Regular.produceUnsatCores]
def produceUnsatCores (active : Bool := true) : Opt :=
  Regular.produceUnsatCores active

@[inherit_doc Regular.produceInterpolants]
def produceInterpolants (active : Bool := true) : Opt :=
  Regular.produceInterpolants active

@[inherit_doc Regular.produceAssignments]
def produceAssignments (active : Bool := true) : Opt :=
  Regular.produceAssignments active

@[inherit_doc Regular.produceAssertions]
def produceAssertions (active : Bool := true) : Opt :=
  Regular.produceAssertions active

def keyVal : Opt → String × String
| common c => c.keyVal
| regular r => r.keyVal
| expert e => e.keyVal
end Opt
