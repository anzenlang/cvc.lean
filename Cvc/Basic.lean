/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command

public import Cvc.Basic.Error
public import Cvc.Basic.Env

import all Cvc.Basic.Env



/-! # cvc5's enumerations

The cvc5 enumerations the API takes or answers, mirrored as Lean inductives, plus the constant
combinators `𝕂` and `𝕂²`.
-/

namespace Cvc

section open Lean Elab Command

/-- The constant combinator. -/
macro "𝕂 " t:term : term => `(fun _ => $t)
/-- The constant combinator ignoring its first two arguments. -/
macro "𝕂² " t:term : term => `(fun _ _ => $t)

syntax (name := enumDefStx)
  atomic( (docComment)? "enum_def%") ident " ← " ("[" ident "/" ident "]")? ident
    (ppLine ppIndent(
      atomic((docComment ppLine)? "| ") ("default!")? rawIdent " ← " ident
    ))*
: command

open Parser.Term (attrInstance) in
@[command_elab enumDefStx]
public meta def enumDefStxElab : CommandElab
| `(
  $[ $doc?:docComment ]?
  enum_def% $id  ← $[[$ofSrcId? / $toSrcId?]]? $srcId
    $[ $[ $variantDocs?:docComment ]?
    | $[ default!%$default? ]? $variantIds ← $variantSrcIds ]*
) => do
  let ofSrcId ← ofSrcId?.getDM do `ofUnsafe |> mkIdent |> pure
  let toSrcId ← toSrcId?.getDM do `toUnsafe |> mkIdent |> pure
  let variantDefault? := default?.zip variantIds |>.find? (Option.isSome ∘ Prod.fst) |>.map Prod.snd
  let variantSrcIds := variantSrcIds.map (· |>.getId |> srcId.getId.append |> mkIdent)
  let mods ←
    if let some doc := doc? then `(declModifiers| $doc:docComment)
    else `(declModifiers| @[inherit_doc $srcId])
  let stx ← `(
      $mods:declModifiers
      inductive $id:ident where
      $[ $[ $variantDocs?:docComment ]? | $variantIds:ident ]*
      deriving Repr, BEq, DecidableEq, Hashable, Ord
    )
  elabCommand stx

  let leanDefaultId := ``default |> mkIdent
  let leanReprId := ``repr |> mkIdent
  let leanToStringId := ``toString |> mkIdent
  let defaultDef ←
    if let some variantDefault := variantDefault? then `($variantDefault:ident)
    else `( .ofNat 0 )
  let propOfTo := s!"{ofSrcId.getId}_{toSrcId.getId}" |> Name.mkStr1 |> mkIdent
  let propToOf := s!"{toSrcId.getId}_{ofSrcId.getId}" |> Name.mkStr1 |> mkIdent
  let bleId := `ble |> mkIdent
  let bltId := `blt |> mkIdent
  let stx ← `(
    namespace $id
    /-- Translation from cvc5. -/
    private def $ofSrcId:ident (val : $srcId) : $id := val.ctorIdx |> .ofNat
    /-- Translation to cvc5. -/
    private def $toSrcId:ident (val : $id) : $srcId := val.ctorIdx |> .ofNat
    private theorem $propOfTo:ident (val : $id) : $ofSrcId ($toSrcId val) = val :=
      by cases val <;> rfl
    private theorem $propToOf (val : $srcId) : $toSrcId ($ofSrcId val) = val :=
      by cases val <;> rfl

    instance : Inhabited $id := ⟨$defaultDef⟩
    /-- Default value. -/
    protected def default : $id := $leanDefaultId

    instance : ToString $id := ⟨(s!"{$leanReprId ·}")⟩
    /-- String representation. -/
    protected def toString : $id → String := $leanToStringId

    protected abbrev $bleId (val1 val2 : $id) : Bool :=
      match compare val1 val2 with | Ordering.lt | Ordering.eq => true | Ordering.gt => false
    instance : LE $id := ⟨(· |>.$bleId ·)⟩
    instance : DecidableLE $id :=
      fun val1 val2 => if h : val1 |>.$bleId val2 then isTrue h else isFalse h

    protected abbrev $bltId (val1 val2 : $id) : Bool :=
      match compare val1 val2 with | Ordering.lt => true | Ordering.eq | Ordering.gt => false
    instance : LT $id := ⟨(· |>.$bltId ·)⟩
    instance : DecidableLT $id :=
      fun val1 val2 => if h : val1 |>.$bltId val2 then isTrue h else isFalse h
    end $id
  )
  elabCommand stx

  for (variantId, variantSrcId) in variantIds.zip variantSrcIds do
    let stx ←
      `(open $id:ident in example : ($toSrcId:ident $variantId:ident) = $variantSrcId:ident := rfl)
    elabCommand stx
    let stx ←
      `(open $id:ident in example : ($ofSrcId:ident $variantSrcId:ident) = $variantId:ident := rfl)
    elabCommand stx
| _ => throwUnsupportedSyntax


public section

/-- Why a check answered "unknown". -/
enum_def% Unknown.Explanation ← cvc5.UnknownExplanation
  /-- A full check is required, for instance after preprocessing only. -/
  | requiresFullCheck ← REQUIRES_FULL_CHECK
  /-- A theory solver is incomplete. -/
  | incomplete ← INCOMPLETE
  /-- The time limit was reached. -/
  | timeOut ← TIMEOUT
  /-- The resource limit was reached. -/
  | resourceOut ← RESOURCEOUT
  /-- The memory limit was reached. -/
  | memOut ← MEMOUT
  /-- The solver was interrupted. -/
  | interrupted ← INTERRUPTED
  /-- An unsupported feature was encountered. -/
  | unsupported ← UNSUPPORTED
  /-- Another reason. -/
  | other ← OTHER
  /-- Another check is required. -/
  | requiresCheckAgain ← REQUIRES_CHECK_AGAIN
  /-- No specific reason was given. -/
  | default! unknownReason ← UNKNOWN_REASON

/-- The SMT-LIB rounding modes of floating-point arithmetic. -/
enum_def% Float.RoundingMode ← cvc5.RoundingMode
  /-- To the nearest representable number, ties to the one with an even last digit. -/
  | nearestTiesToEven ← ROUND_NEAREST_TIES_TO_EVEN
  /-- Towards positive infinity. -/
  | towardPositive ← ROUND_TOWARD_POSITIVE
  /-- Towards negative infinity. -/
  | towardNegative ← ROUND_TOWARD_NEGATIVE
  /-- Towards zero. -/
  | towardZero ← ROUND_TOWARD_ZERO
  /-- To the nearest representable number, ties away from zero. -/
  | nearestTiesToAway ← ROUND_NEAREST_TIES_TO_AWAY

/-- How a solver's `blockModel` blocks a model. -/
enum_def% Model.BlockMode ← cvc5.BlockModelsMode
  /-- Block models based on the SAT skeleton. -/
  | literals ← LITERALS
  /-- Block models based on the concrete model values for the free variables. -/
  | values ← VALUES

/-- Kinds of learned literals.

A literal may belong to several kinds; it is classified by the first one in this list it fits.
-/
enum_def% LearnedLitType ← cvc5.LearnedLitType
  /-- An equality `(= x t)`, `x` not occurring in `t`, turned into a substitution. -/
  | preprocessSolved ← PREPROCESS_SOLVED
  /-- A top-level literal (unit clause) from the preprocessed input formulas. -/
  | preprocess ← PREPROCESS
  /-- A literal of the preprocessed input formulas that is not top-level after preprocessing.

  Typically the most interesting kind of literal to learn.
  -/
  | input ← INPUT
  /-- An internal literal `(= x t)` solvable for an input variable `x` not occurring in `t`. -/
  | solvable ← SOLVABLE
  /-- An internal literal `(= t c)`, `c` a constant, propagating a constant for an input term. -/
  | constantProp ← CONSTANT_PROP
  /-- Any other internal literal. -/
  | internal ← INTERNAL
  /-- Answered when the `produce-learned-literals` option is not set. -/
  | unknown ← UNKNOWN

/-- The part of a refutation a proof is asked for. -/
enum_def% Proof.Component ← [ofUnsafe / toUnsafe] cvc5.ProofComponent
  /-- Proofs of the preprocessed input formulas, from the input formulas. -/
  | rawPreprocess ← RAW_PREPROCESS
  /-- Proofs of the clauses the SAT proof uses, from the input formulas it uses. -/
  | preprocess ← PREPROCESS
  /-- A proof of `false` from the preprocessed input clauses and the theory lemmas. -/
  | sat ← SAT
  /-- Proofs of the theory lemmas the SAT proof uses. -/
  | theoryLemmas ← THEORY_LEMMAS
  /-- A proof of `false` from the input formulas. -/
  | default! full ← FULL

/-- The format a proof is printed in. -/
enum_def% Proof.Format ← [ofUnsafe / toUnsafe] cvc5.ProofFormat
  /-- cvc5's own output, untranslated; the only format a non-`full` proof can be printed in. -/
  | no ← NONE
  /-- DOT, for Graphviz. -/
  | dot ← DOT
  /-- LFSC. -/
  | lfsc ← LFSC
  /-- Alethe. -/
  | alethe ← ALETHE
  /-- The Cooperating Proof Calculus, over Eunoia signatures. -/
  | cpc ← CPC
  /-- The format the solver's options select. -/
  | default! fromSolver ← DEFAULT



/-- What `Solver.findSynth` looks for. -/
enum_def% Synth.FindTarget ← cvc5.FindSynthTarget
  /-- The next term in the enumeration of the grammar. -/
  | enum ← ENUM
  /-- A pair of equivalent terms `t`, `s` of the grammar that do not rewrite to the same term.

  Answers the equality `(= t s)`; useful to synthesize rewrite rules. The rewriter is the one the
  `sygus-rewrite` option selects.
  -/
  | rewrite ← REWRITE
  /-- A term `t` of the grammar rewriting to a term `s` not equivalent to it.

  Answers the equality `(= t s)`; any answer is an unsoundness of the rewriter.
  -/
  | rewriteUnsound ← REWRITE_UNSOUND
  /-- Like `rewrite`, for terms matching terms of the input assertions. -/
  | rewriteInput ← REWRITE_INPUT
  /-- A query over the grammar, as equalities if its terms are not Boolean. -/
  | query ← QUERY

/-- Option category enumeration.

Specifies the category of an option for user interface purposes.
-/
enum_def% Option.Category ← cvc5.OptionCategory
  /-- Option available to regular users. -/
  | regular ← REGULAR
  /-- Option available to expert users. -/
  | expert ← EXPERT
  /-- Common options. -/
  | common ← COMMON
  /-- Undocumented options. -/
  | undocumented ← UNDOCUMENTED

/-- An input language cvc5 can parse. -/
enum_def% InputLanguage ← cvc5.InputLanguage
  /-- The SMT-LIB version 2.6 language. -/
  | smtLib_2_6 ← SMT_LIB_2_6
  /-- The SyGuS version 2.1 language. -/
  | sygus_2_1 ← SYGUS_2_1
  /-- No language given. -/
  | unknown ← UNKNOWN

end
