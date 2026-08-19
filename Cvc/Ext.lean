/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Term



/-! # The `smt!` term DSL, layer-parameterized

This module holds the parts of the DSL that do not depend on a theory: the `smtTerm`
category, the forms that are not operators (literals, identifiers, `if`/`let`, escapes), the two
layer entry points, and the expander shared by both.

Operator grammar is *not* here. `gen_untyped%` emits one grammar rule per operator carrying a
notation, named `…smtOp.<shape>.<id>`, so a theory's notation is compiled with that theory and no
other. `expandSmt` dispatches on the last three components of a node's kind, which is what lets the
grammar be generated per theory while the expansion logic is written once.

There are two entry points rather than one because each expands to a *different* namespace:
`smtU!` builds `Cvc.Untyped.Term.…` and `smtT!` builds `Cvc.Typed.Term.…`, both
fully qualified. Nothing has to be in scope at the use site. Each layer additionally exposes a
`scoped` `smt!` alias, so opening one layer gives the short spelling.

The `smtTerm` category is deliberately *not* declared with `behavior := symbol`: symbol
behavior breaks the longest match between an infix token and its bracket form (`∧` versus `∧[`).
Nothing is reserved by this, since the category's atoms are symbols rather than identifiers.
-/
namespace Cvc public meta section

open Lean Elab



-- syntax category names are global — they become `Lean.Parser.Category.<name>`, with no
-- namespace — so the name is prefixed to keep it collision-free
declare_syntax_cat smtTerm

/-! ### Atoms

All five are at `:max`, as their counterparts in Lean's own `term` category are, because that is
what `smtApp` parses its function and its arguments at. Anything below `max` — `if`, `let`,
`match`, and every operator — needs parentheses to be an argument, which is exactly how Lean reads
its own application.
-/

/-- Parenthesized SMT term. -/
syntax:max (name := smtParen) "(" smtTerm ")" : smtTerm
/-- Escape back into Lean: `![e]` splices the Lean term `e`, which must be an `Env`-term. -/
syntax:max (name := smtEscape) "![" term "]" : smtTerm
/-- An identifier denotes an already-built term, lifted with `pure`. -/
syntax:max (name := smtIdent) ident : smtTerm
/-- Binds an intermediate term. -/
syntax (name := smtLet) "let " ident " ← " smtTerm "; " ppLine smtTerm : smtTerm
/-- Function application, `f arg₁ arg₂ …`, spelled as Lean spells it.

Declared exactly as Lean's own `app` is (`trailing_parser:leadPrec:maxPrec many1 argument`): the
rule sits at `lead` while its function and arguments are parsed at `max`. The gap is what makes the
application flat — at `max` the rule cannot apply to its own argument, so `f i b` is one node with
two arguments rather than `f` applied to `(i b)`. `colGt` stops a new line at or left of the
application's column from being read as one more argument, which is what keeps a `match`
alternative's body from swallowing the next `|`.

Everything below `max` — `if`, `let`, `match`, and every operator — needs parentheses to be an
argument, exactly as in Lean.
-/
syntax:lead (name := smtApp) smtTerm:max (ppSpace colGt smtTerm:max)+ : smtTerm


/-- Expands one `smtTerm` of the layer whose root is named, deferring its sub-terms to itself.

This is the DSL's dispatch, and it is a `macro_rules` table on purpose: `macro_rules` composes
across modules — a later alternative is tried first and falls through to earlier ones when it
answers `Macro.throwUnsupported` — so a theory can add the expansion of its own forms without the
base module knowing they exist. An environment extension would not do: `MacroM` can resolve names
but cannot read one.

Recursion goes through this node rather than through a function, which is what lets a core form
contain a theory's form and the other way round.
-/
syntax (name := smtExpand) "smtExpand% " ident ppSpace smtTerm : term

/-- Builds a sort-erased term. -/
syntax (name := smtUStx) "smtU! " ppLine group(colGt smtTerm) : term
/-- Builds a typed term. -/
syntax (name := smtTStx) "smtT! " ppLine group(colGt smtTerm) : term



/-! ## The expander

Everything below is the DSL's own machinery, and it lives in `Cvc.Ext` rather than in `Cvc` so that
none of it can clash with the API a user opens. Names like `bindArgs`, `freshId` and `patArgs` would
otherwise sit beside the term constructors — and `deferSmt` was `sub` once, which shadowed
`Cvc.Untyped.Term.sub` wherever both were open.
-/
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

Expansion goes through `>>=` rather than `do`-notation because an antiquotation in `doElem`
head position does not elaborate: `` `(do $fn (← $a) (← $b)) `` is rejected, whereas the bind
chain below is fine. Binder names are macro-scoped, so they cannot capture user identifiers.

Two calls in one expansion produce the *same* binder names, macro scopes and all, so a nested one
shadows what the outer bound. `binder` is what tells them apart where that matters.
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

/-- A macro-scoped identifier, for a name the expansion binds but the writer never sees. -/
def freshId (base : String) : MacroM Ident := do
  return mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple base))

/-- A sub-term's expansion, deferred to `smtExpand%` so that a theory's forms can be reached.

Not named `sub`: `Cvc.Untyped.Term.sub` is subtraction, and a `Cvc.sub` beside it shadows that
wherever both namespaces are open.
-/
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
    `(pure $id)
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

end Ext

end

macro_rules
  | `(smtU! $t:smtTerm) => do let l := Ext.Layer.untyped.ident; `(smtExpand% $l $t)
  | `(smtT! $t:smtTerm) => do let l := Ext.Layer.typed.ident; `(smtExpand% $l $t)

/-- Every form this module knows, tried after any a theory adds. -/
macro_rules
  | `(smtExpand% $l $t:smtTerm) => Ext.expandSmt (Ext.Layer.ofIdent l) t.raw


