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



namespace Cvc -- variable [Ω]

section open Lean Elab Command

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

enum_def% Unknown.Explanation ← cvc5.UnknownExplanation
  | requiresFullCheck ← REQUIRES_FULL_CHECK
  | incomplete ← INCOMPLETE
  | timeOut ← TIMEOUT
  | resourceOut ← RESOURCEOUT
  | memOut ← MEMOUT
  | interrupted ← INTERRUPTED
  | unsupported ← UNSUPPORTED
  | other ← OTHER
  | requiresCheckAgain ← REQUIRES_CHECK_AGAIN
  | default! unknownReason ← UNKNOWN_REASON

enum_def% Float.RoundingMode ← cvc5.RoundingMode
  | nearestTiesToEven ← ROUND_NEAREST_TIES_TO_EVEN
  | towardPositive ← ROUND_TOWARD_POSITIVE
  | towardNegative ← ROUND_TOWARD_NEGATIVE
  | towardZero ← ROUND_TOWARD_ZERO
  | nearestTiesToAway ← ROUND_NEAREST_TIES_TO_AWAY

enum_def% Model.BlockMode ← cvc5.BlockModelsMode
  /-- Block models based on the SAT skeleton. -/
  | literals ← LITERALS
  /-- Block models based on the concrete model values for the free variables. -/
  | values ← VALUES

/-- Types of learned literals.

Note that a literal may conceptually belong to multiple categories. We
classify literals based on the first criteria in this list that they meet.
-/
enum_def% LearnedLitType ← cvc5.LearnedLitType
  /-- An equality that was turned into a substitution during preprocessing.

  In particular, literals in this category are of the form (= x t) where
  x does not occur in t.
  -/
  | preprocessSolved ← PREPROCESS_SOLVED
  /-- A top-level literal (unit clause) from the preprocessed set of input formulas. -/
  | preprocess ← PREPROCESS
  /--
  A literal from the preprocessed set of input formulas that does not
  occur at top-level after preprocessing.

  Typically, this is the most interesting category of literals to learn.
  -/
  | input ← INPUT
  /-- An internal literal that is solvable for an input variable.

  In particular, literals in this category are of the form (= x t) where
  x does not occur in t, the preprocessed set of input formulas contains the
  term x, but not the literal (= x t).

  Note that solvable literals can be turned into substitutions during
  preprocessing.
  -/
  | solvable ← SOLVABLE
  /-- An internal literal that can be made into a constant propagation for an input term.

  In particular, literals in this category are of the form (= t c) where
  c is a constant, the preprocessed set of input formulas contains the
  term t, but not the literal (= t c).
  -/
  | constantProp ← CONSTANT_PROP
  /-- Any internal literal that does not fall into the above categories. -/
  | internal ← INTERNAL
  /-- Special case for when produce-learned-literals is not set. -/
  | unknown ← UNKNOWN

enum_def% Proof.Component ← cvc5.ProofComponent
  | rawPreprocess ← RAW_PREPROCESS
  | preprocess ← PREPROCESS
  | sat ← SAT
  | theoryLemmas ← THEORY_LEMMAS
  | default! full ← FULL

enum_def% Proof.Format ← cvc5.ProofFormat
  | no ← NONE
  | dot ← DOT
  | lfsc ← LFSC
  | alethe ← ALETHE
  | cpc ← CPC
  | default! fromSolver ← DEFAULT



/--
Find synthesis targets, used as an argument to Solver::findSynth. These
specify various kinds of terms that can be found by this method.
-/
enum_def% Synth.FindTarget ← cvc5.FindSynthTarget
  /--
  Find the next term in the enumeration of the target grammar.
  -/
  | enum ← ENUM
  /--
  Find a pair of terms (t,s) in the target grammar which are equivalent
  but do not rewrite to the same term in the given rewriter
  (--sygus-rewrite=MODE). If so, the equality (= t s) is returned by
  findSynth.

  This can be used to synthesize rewrite rules. Note if the rewriter is set
  to none (--sygus-rewrite=none), this indicates a possible rewrite when
  implementing a rewriter from scratch.
  -/
  | rewrite ← REWRITE
  /--
  Find a term t in the target grammar which rewrites to a term s that is
  not equivalent to it. If so, the equality (= t s) is returned by
  findSynth.

  This can be used to test the correctness of the given rewriter. Any
  returned rewrite indicates an unsoundness in the given rewriter.
  -/
  | rewriteUnsound ← REWRITE_UNSOUND
  /--
  Find a rewrite between pairs of terms (t,s) that are matchable with terms
  in the input assertions where t and s are equivalent but do not rewrite
  to the same term in the given rewriter (--sygus-rewrite=MODE).

  This can be used to synthesize rewrite rules that apply to the current
  problem.
  -/
  | rewriteInput ← REWRITE_INPUT
  /--
  Find a query over the given grammar. If the given grammar generates terms
  that are not Boolean, we consider equalities over terms from the given
  grammar.

  The algorithm for determining which queries to generate is configured by
  --sygus-query-gen=MODE. Queries that are internally solved can be
  filtered by the option --sygus-query-gen-filter-solved.
  -/
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

/-- The different reasons for returning an "unknown" result. -/
enum_def% InputLanguage ← cvc5.InputLanguage
  /-- The SMT-LIB version 2.6 language. -/
  | smtLib_2_6 ← SMT_LIB_2_6
  /-- The SyGuS version 2.1 language. -/
  | sygus_2_1 ← SYGUS_2_1
  /-- No language given. -/
  | unknown ← UNKNOWN

end
