/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Term



/-! # The `smt!` term DSL

`smt!` writes a term in notation close to Lean's own — `smt! i + 2 * j ≤ k ∧ ¬ b` — and builds it
in `Env`. `smtU!` builds a sort-erased term and `smtT!` a typed one; `open Cvc.Untyped` or
`open Cvc.Typed` makes `smt!` stand for the matching one.

This module declares the forms that belong to no theory: parentheses, `![e]` to splice a Lean term,
identifiers, application `f a b`, `let x ← t; u` and `fun (x : s) => t`. Every other form —
literals, operators, `if`, `match`, quantifiers — is declared by the theory module it belongs to, so
`smt!` accepts exactly the notations of the theories imported.
-/
-- Operator grammar is generated per theory: `gen_untyped%` emits one grammar rule per operator
-- carrying a notation, named `…smtOp.<shape>.<id>`, and `expandSmt` dispatches on the last three
-- components of a node's kind, so the expansion logic is written once. Each entry point expands to
-- fully qualified names of its layer, so nothing has to be in scope at the use site.
--
-- The `smtTerm` category is deliberately *not* declared with `behavior := symbol`: symbol behavior
-- breaks the longest match between an infix token and its bracket form (`∧` versus `∧[`). Nothing
-- is reserved by this, since the category's atoms are symbols rather than identifiers.
namespace Cvc public meta section

open Lean Elab



-- syntax category names are global — they become `Lean.Parser.Category.<name>`, with no
-- namespace — so the name is prefixed to keep it collision-free
declare_syntax_cat smtTerm

-- Atoms. All of them — these three, and the number and string literals the theories declare — are
-- at `:max`, as their counterparts in Lean's own `term` category are, because that is what `smtApp`
-- parses its function and its arguments at. Anything below `max` — `if`, `let`, `match`, and every
-- operator — needs parentheses to be an argument, which is exactly how Lean reads its own
-- application.

/-- Parenthesized SMT term. -/
syntax:max (name := smtParen) "(" smtTerm ")" : smtTerm
/-- Escape back into Lean: `![e]` splices the Lean term `e`, which must be an `Env`-term. -/
syntax:max (name := smtEscape) "![" term "]" : smtTerm
/-- An identifier denotes an already-built term, lifted with `pure`. -/
syntax:max (name := smtIdent) ident : smtTerm
/-- `let x ← t; u` binds the term `t` to `x` in `u`. -/
syntax (name := smtLet) "let " ident " ← " smtTerm "; " ppLine smtTerm : smtTerm
/-- Function application, `f arg₁ arg₂ …`, spelled as Lean spells it.

`f i b` applies `f` to two arguments, and a new line at or left of the application's column is not
read as one more argument. `if`, `let`, `match` and every operator need parentheses to be an
argument, exactly as in Lean.
-/
syntax:lead (name := smtApp) smtTerm:max (ppSpace colGt smtTerm:max)+ : smtTerm
-- Declared exactly as Lean's own `app` is (`trailing_parser:leadPrec:maxPrec many1 argument`): the
-- rule sits at `lead` while its function and arguments are parsed at `max`. The gap is what makes
-- the application flat — at `max` the rule cannot apply to its own argument, so `f i b` is one node
-- with two arguments rather than `f` applied to `(i b)`. `colGt` stops a new line at or left of the
-- application's column from being read as one more argument, which is what keeps a `match`
-- alternative's body from swallowing the next `|`.

/-! ### Binders

A lambda and a quantifier bind their variables the way Lean's do, in parentheses with a sort after
the colon: `(x y : s)`. Sort-erased, the sort is a Lean type (`Int`) or a `Srt` value (`int`);
typed, it is the Lean type indexing the variable.
-/

/-- Binders of an `smt!` lambda or quantifier. -/
declare_syntax_cat smtQuantBinder (behavior := symbol)

/-- Variables sharing a sort: `(x y : s)`. -/
syntax (name := smtQuantBinder) "(" ident+ " : " term ")" : smtQuantBinder

/-- A lambda, `fun (x y : s) => body`, spelled as Lean spells it.

The body extends as far right as it can, as in Lean, so a lambda in argument position needs
parentheses. cvc5 prints the variables under the names written.
-/
syntax:lead (name := smtFun) ("fun" <|> "λ") (ppSpace smtQuantBinder)+ " => " smtTerm : smtTerm


/-- Expands one `smtTerm` of the layer whose root is named, deferring its sub-terms to itself.

This is the DSL's dispatch: each theory adds the expansion of its own forms as a `macro_rules`
alternative for it, tried before those of the modules it imports.
-/
syntax (name := smtExpand) "smtExpand% " ident ppSpace smtTerm : term
-- A `macro_rules` table on purpose: `macro_rules` composes across modules — a later alternative is
-- tried first and falls through to earlier ones when it answers `Macro.throwUnsupported` — so a
-- theory can add the expansion of its own forms without the base module knowing they exist. An
-- environment extension would not do: `MacroM` can resolve names but cannot read one.
--
-- Recursion goes through this node rather than through a function, which is what lets a core form
-- contain a theory's form and the other way round.

/-- An identifier leaf of the layer whose root is named, elaborated by `Cvc.Ext.elabSmtIdent`. -/
syntax (name := smtIdentElab) "smtIdent% " ident ppSpace ident : term

/-- Builds a sort-erased term in `Env` from `smt!` notation. -/
syntax (name := smtUStx) "smtU! " ppLine group(colGt smtTerm) : term
/-- Builds a typed term in `Env` from `smt!` notation. -/
syntax (name := smtTStx) "smtT! " ppLine group(colGt smtTerm) : term



/-! ## The expander

The DSL's own machinery, used by the theory modules to declare their forms.
-/
-- It lives in `Cvc.Ext` rather than in `Cvc` so that none of it can clash with the API a user
-- opens: names like `bindArgs`, `freshId` and `patArgs` would otherwise sit beside the term
-- constructors, and a helper named like one — `sub`, say — would shadow `Cvc.Untyped.Term.sub`
-- wherever both namespaces are open.
namespace Ext

/-- The layer an `smt!` expansion targets. -/
structure Layer where
  /-- The layer's own namespace, holding what is not a term constructor. -/
  root : Name
deriving Inhabited, BEq

namespace Layer

/-- The sort-erased layer. -/
def untyped : Layer where
  root := `Cvc.Untyped

/-- The typed layer. -/
def typed : Layer where
  root := `Cvc.Typed

/-- The layer a `smtExpand%` node names. -/
def ofIdent (id : Ident) : Layer := ⟨id.getId⟩

/-- The identifier naming this layer in a `smtExpand%` node. -/
def ident (layer : Layer) : Ident := mkIdent layer.root

/-- Namespace holding the generated operator constructors. -/
def ops (layer : Layer) : Name := layer.root ++ `Term

/-- The identifier of an operator of this layer. -/
def op (layer : Layer) (id : Name) : Ident := mkIdent (layer.ops ++ id)

/-- The identifier of a declaration of this layer that is not a term constructor. -/
def name (layer : Layer) (id : Name) : Ident := mkIdent (layer.root ++ id)

end Layer



/-- Decomposes a generated operator node kind into its shape and operator name.

Grammar rules are named `…smtOp.<shape>.<id>`, so the trailing three components identify the
operator regardless of the namespace the rule was generated in.
-/
def smtOpKind? : Name → Option (Name × Name)
  | .str (.str (.str _ "smtOp") shape) id => some (Name.mkSimple shape, Name.mkSimple id)
  | _ => Option.none

/-- Name of the n-ary function of an operator, `<id>N`. -/
def naryIdOf (id : Name) : Name := id.appendAfter "N"



/-- Binds every argument in order, then applies `mk` to the identifiers they were bound to.

Binder names are macro-scoped, so they cannot capture user identifiers. Two calls in one expansion
produce the *same* binder names, macro scopes and all, so a nested one shadows what the outer
bound. `binder` is what tells them apart where that matters.
-/
def bindArgs (args : Array (TSyntax `term)) (mk : Array Ident → MacroM (TSyntax `term))
(binder : String := "smtArg") : MacroM (TSyntax `term) := do
  let mut ids := #[]
  for i in [0:args.size] do
    ids := ids.push (mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple s!"{binder}{i}")))
  let mut body ← mk ids
  for i in [0:args.size] do
    let j := args.size - 1 - i
    body ← `($(args[j]!) >>= fun $(ids[j]!) => $body)
  return body
-- Expansion goes through `>>=` rather than `do`-notation because an antiquotation in `doElem`
-- head position does not elaborate: `` `(do $fn (← $a) (← $b)) `` is rejected, whereas the bind
-- chain above is fine.

/-- A macro-scoped identifier, for a name the expansion binds but the writer never sees. -/
def freshId (base : String) : MacroM Ident := do
  return mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple base))

/-- A sub-term's expansion, deferred to `smtExpand%` so that a theory's forms can be reached. -/
def deferSmt (layer : Layer) (stx : Syntax) : MacroM (TSyntax `term) := do
  let l := layer.ident
  let t : TSyntax `smtTerm := ⟨stx⟩
  `(smtExpand% $l $t)

/-- Expands one `smtTerm` node into a term of the given layer.

Operator nodes are dispatched by kind; everything else is a fixed form declared above. Sub-terms
are *not* expanded here — they go back through `smtExpand%`, so a form this module does not know
can still occur inside one it does.
-/
partial def expandSmt (layer : Layer) (stx : Syntax) : MacroM (TSyntax `term) := do
  let kind := stx.getKind

  -- generated operators
  if let some (shape, id) := smtOpKind? kind then
    match shape with
    | `binary =>
      let fn := layer.op id
      let args ← #[stx[0], stx[2]].mapM (deferSmt layer)
      bindArgs args fun ids => `($fn $(ids[0]!) $(ids[1]!))
    | `prefix =>
      let fn := layer.op id
      let args ← #[stx[1]].mapM (deferSmt layer)
      bindArgs args fun ids => `($fn $(ids[0]!))
    | `nary =>
      let fn := layer.op (naryIdOf id)
      let args ← stx[1].getSepArgs.mapM (deferSmt layer)
      bindArgs args fun ids => `($fn #[ $ids,* ])
    | _ => Macro.throwErrorAt stx s!"unknown generated operator shape `{shape}`"
  else

  -- fixed forms
  match kind with
  | ``smtParen => deferSmt layer stx[1]
  | ``smtEscape => return ⟨stx[1]⟩
  | ``smtIdent =>
    -- `true`/`false` are `Core.Bool`'s and an identifier naming *fields* is `Theory.Record`'s;
    -- each adds an alternative of its own, so what reaches here is a plain name
    let id : Ident := ⟨stx[0]⟩
    `(smtIdent% $(layer.ident) $id)
  | ``smtLet =>
    let id : Ident := ⟨stx[1]⟩
    let value ← deferSmt layer stx[3]
    let body ← deferSmt layer stx[5]
    `($value >>= fun $id => $body)
  | ``smtApp =>
    -- the two layers spell "the arguments" differently: an array sort-erased, an `Args` spine
    -- typed, where non-emptiness is structural rather than an autoparam
    let fn ← deferSmt layer stx[0]
    let args ← stx[1].getArgs.mapM (deferSmt layer)
    let applyN := layer.op `applyN
    bindArgs (#[fn] ++ args) fun ids => do
      let fnId := ids[0]!
      let argIds := ids.extract 1 ids.size
      if layer == .typed then
        -- built with `mkIdent`, never written literally: this module imports neither layer
        let mut spine ← `($(layer.op `Args.last) $(argIds.back!))
        for arg in argIds.pop.reverse do
          spine ← `($(layer.op `Args.cons) $arg $spine)
        `($applyN $fnId $spine)
      else
        `($applyN $fnId #[ $argIds,* ])
  | _ => Macro.throwErrorAt stx s!"unsupported SMT term (kind `{kind}`)"

/-- Whether a type is one of the layers' terms, or what converts to one.

This is where a dotted identifier stops being a Lean projection and starts reading record fields.
-/
def isSmtTermType (type : Expr) : Bool :=
  match type.consumeMData.getAppFn.constName? with
  -- written out rather than resolved, this module importing neither layer
  | some n => [`Cvc.Untyped.Term, `Cvc.Untyped.BVar, `Cvc.Untyped.NT,
               `Cvc.Typed.Term, `Cvc.Typed.BVar, `Cvc.Typed.NT].contains n
  -- not headed by a constant: nothing says it is a Lean structure, so it is read as a term
  | none => true

/-- The conversion to a term of a typed non-terminal's, bound variable's or state symbol's type.

A state symbol is a `Symbols.At`, whose `get` answers the term it wraps when the wrap is the
layer's terms, as it is wherever `smt!` meets one.
-/
def typedToTerm? (type : Expr) : Option Name :=
  match type.consumeMData.getAppFn.constName? with
  | some `Cvc.Typed.NT => some `Cvc.Typed.NT.toTerm
  | some `Cvc.Typed.BVar => some `Cvc.Typed.BVar.toTerm
  | some `Cvc.Typed.Symbols.At => some `Cvc.Typed.Symbols.At.get
  | _ => none

/-- Elaborates an identifier leaf: the term it names, lifted with `pure`.

Typed, a non-terminal, a bound variable or a state symbol (`Symbols.At`) is converted to its term,
at the index its own type carries, so `smt! n * m` works over two non-terminals with nothing else
fixing the index. Anything else is elaborated exactly as written. Not only identifiers come through
here: a field projection on a Lean value does too.
-/
def elabSmtIdent (layer : Layer) (id : Term) (expected? : Option Expr)
: Elab.Term.TermElabM Expr := do
  if layer == .typed then
    -- an error here is the user's, and is reported from here alone: recovering from it would have
    -- the elaboration below report it a second time
    let e ← Elab.Term.withoutErrToSorry (Elab.Term.elabTerm id none)
    let type ← instantiateMVars (← Meta.inferType e)
    if let some conv := typedToTerm? type then
      let e ← Elab.Term.exprToSyntax e
      return ← Elab.Term.elabTerm (← `(pure ($(mkIdent conv) $e))) expected?
  -- passing the identifier through unchanged keeps its use visible to the unused-variable linter
  Elab.Term.elabTerm (← `(pure $id)) expected?
-- The conversion is done here, by looking at the identifier's type, rather than left to the
-- coercion. The coercion needs the index it targets to be known, and in `smt! n * m` with no
-- expected type nothing fixes it, so two non-terminals — or `x + y` over two state symbols — could
-- not be combined at all. Converting by hand needs no index: it is read off the identifier's own
-- type. A term of any other type goes through unchanged, so a sort mismatch between two terms is
-- reported as it would be without the DSL.

@[term_elab smtIdentElab, inherit_doc smtIdentElab]
def elabSmtIdentTerm : Elab.Term.TermElab := fun stx expected? => do
  let `(smtIdent% $l $id) := stx | Elab.throwUnsupportedSyntax
  elabSmtIdent (Layer.ofIdent l) id expected?

/-- The variables of a lambda's or quantifier's binders, in order, each with its written sort. -/
def quantBinders (binders : Syntax) : Array (Ident × Term) := Id.run do
  let mut acc := #[]
  for binder in binders.getArgs do
    for id in binder[1].getArgs do
      acc := acc.push ((⟨id⟩ : Ident), (⟨binder[3]⟩ : Term))
  return acc

/-- The name cvc5 gives a bound variable: the one the writer gave it. -/
def quantName (id : Ident) : StrLit := Syntax.mkStrLit id.getId.eraseMacroScopes.toString

end Ext

end

macro_rules
  | `(smtU! $t:smtTerm) => do let l := Ext.Layer.untyped.ident; `(smtExpand% $l $t)
  | `(smtT! $t:smtTerm) => do let l := Ext.Layer.typed.ident; `(smtExpand% $l $t)

/-- Every form this module knows, tried after any a theory adds. -/
macro_rules
  | `(smtExpand% $l $t:smtTerm) => Ext.expandSmt (Ext.Layer.ofIdent l) t.raw


