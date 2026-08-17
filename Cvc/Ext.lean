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
/-- Integer literal. -/
syntax:max (name := smtNum) num : smtTerm
/-- Real literal, `1.5` or `1.5e-3`.

The literal is handed to `mkReal` unascribed, so Lean elaborates it against that function's `Rat`
argument through `OfScientific`. Nothing here has to name `Rat`, which is what keeps this module
free of any dependency on where that type comes from.
-/
syntax:max (name := smtSci) scientific : smtTerm
/-- String literal. -/
syntax:max (name := smtStr) str : smtTerm
/-- Conditional, expanding to the `ite` operator. -/
syntax (name := smtIte)
  withPosition(
    "if " smtTerm (colGe " then " smtTerm) (colGe " else " (colGe smtTerm))
  )
: smtTerm
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

/-! ### Matching

`match … with | ctor x y => … | _ => …` over a datatype, binding each constructor's fields
without the writer having to make bound variables.

`match` and `with` are Lean keywords already, so unlike an identifier-shaped atom of a new rule
these reserve nothing. Neither new category needs `behavior := symbol` for the same reason
`smtTerm` does not: every atom here is a symbol rather than an identifier, so nothing would be
reserved either way, and a rule leading with `ident` is what symbol behavior indexes worst.

The alternatives get categories of their own rather than an inline `many` group, since the expander
navigates nodes by index and nesting them would make that unreadable.

The catch-all is spelled `_` and nothing else. A bare identifier is always a constructor name: a
nullary constructor and a variable standing for the scrutinee are the same syntax, and cvc5 reads a
lone variable pattern as the catch-all, so naming the two apart is what keeps `| nil => …` meaning
the constructor. Nothing is lost — the body of a catch-all can mention the scrutinee directly.
-/

/-- One variable bound by a pattern, optionally at a stated sort. -/
declare_syntax_cat smtPatArg
/-- A variable whose sort is inferred. -/
syntax (name := smtPatArg) ident : smtPatArg
/-- A variable at a stated sort, `(x : Lst)`. -/
syntax (name := smtPatArgOf) "(" ident " : " term ")" : smtPatArg

/-- One alternative of a match. -/
declare_syntax_cat smtMatchAlt
/-- An alternative matching one constructor, binding one variable per field. -/
syntax (name := smtAlt) " | " ident (ppSpace smtPatArg)* " => " smtTerm : smtMatchAlt
/-- The catch-all alternative, taken when no earlier one matches. -/
syntax (name := smtAltAny) " | " "_" " => " smtTerm : smtMatchAlt

/-- Matches a datatype term against its constructors. -/
syntax (name := smtMatch)
  withPosition("match " smtTerm " with" (ppLine colGe smtMatchAlt)+)
: smtTerm

/-- Builds a sort-erased term. -/
syntax (name := smtUStx) "smtU! " ppLine group(colGt smtTerm) : term
/-- Builds a typed term. -/
syntax (name := smtTStx) "smtT! " ppLine group(colGt smtTerm) : term



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
-/
def bindArgs (args : Array (TSyntax `term)) (mk : Array Ident → MacroM (TSyntax `term))
: MacroM (TSyntax `term) := do
  let mut ids := #[]
  for i in [0:args.size] do
    ids := ids.push (mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple s!"smtArg{i}")))
  let mut body ← mk ids
  for i in [0:args.size] do
    let j := args.size - 1 - i
    body ← `($(args[j]!) >>= fun $(ids[j]!) => $body)
  return body

/-- A macro-scoped identifier, for a name the expansion binds but the writer never sees. -/
def freshId (base : String) : MacroM Ident := do
  return mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple base))

/-- The name a pattern variable binds. -/
def patBinderName (arg : Syntax) : Name :=
  if arg.getKind == ``smtPatArgOf then arg[1].getId else arg[0].getId

/-- Whether an identifier is *referenced* anywhere in a piece of syntax.

Used on a match body, before it is expanded, to tell whether a variable the pattern binds is
mentioned at all — which in the typed layer is what decides whether its index can be inferred.

Binders shadow, so this stops at one: a nested alternative or `let` that rebinds the name is
talking about a different variable, and descending into its body would report an occurrence that
is not one.
-/
partial def occursIn (name : Name) : Syntax → Bool
  | .ident _ _ id _ => id == name
  | .node _ kind args =>
    if kind == ``smtAlt && args[2]!.getArgs.any (patBinderName · == name) then
      -- shadowed in the body; only a sort ascription of this alternative could still name it, and
      -- the binders themselves must not count, being the very thing doing the shadowing
      args[2]!.getArgs.any fun arg => arg.getKind == ``smtPatArgOf && occursIn name arg[3]
    else if kind == ``smtLet && args[1]!.getId == name then
      -- shadowed in the body, but the bound value is evaluated before the shadowing
      occursIn name args[3]!
    else args.any (occursIn name)
  | _ => false

/-- Parses a pattern's variables into their binders and their sort ascriptions, where given. -/
def patArgs (args : Array Syntax) : MacroM (Array (Ident × Option (TSyntax `term))) :=
  args.mapM fun arg => do
    match arg.getKind with
    | ``smtPatArg => return (⟨arg[0]⟩, none)
    | ``smtPatArgOf => return (⟨arg[1]⟩, some ⟨arg[3]⟩)
    | k => Macro.throwErrorAt arg s!"unsupported pattern variable (kind `{k}`)"

mutual

/-- Expands one `smtTerm` node into a term of the given layer.

Operator nodes are dispatched by kind; everything else is a fixed form declared above.
-/
partial def expandSmt (layer : Layer) (stx : Syntax) : MacroM (TSyntax `term) := do
  let kind := stx.getKind

  -- generated operators
  if let some (shape, id) := smtOpKind? kind then
    match shape with
    | `binary =>
      let fn := layer.op id
      let args ← #[stx[0], stx[2]].mapM (expandSmt layer)
      bindArgs args fun ids => `($fn $(ids[0]!) $(ids[1]!))
    | `prefix =>
      let fn := layer.op id
      let args ← #[stx[1]].mapM (expandSmt layer)
      bindArgs args fun ids => `($fn $(ids[0]!))
    | `nary =>
      let fn := layer.op (naryIdOf id)
      let args ← stx[1].getSepArgs.mapM (expandSmt layer)
      bindArgs args fun ids => `($fn #[ $ids,* ])
    | _ => Macro.throwErrorAt stx s!"unknown generated operator shape `{shape}`"
  else

  -- fixed forms
  match kind with
  | ``smtParen => expandSmt layer stx[1]
  | ``smtEscape => return ⟨stx[1]⟩
  | ``smtNum =>
    let n : TSyntax `term := ⟨stx[0]⟩
    `($(layer.op `mkInt) ($n : Int))
  | ``smtSci =>
    let r : TSyntax `term := ⟨stx[0]⟩
    `($(layer.op `mkReal) $r)
  | ``smtStr =>
    let s : TSyntax `term := ⟨stx[0]⟩
    `($(layer.op `mkString) $s false)
  | ``smtIdent =>
    let id : Ident := ⟨stx[0]⟩
    -- `true`/`false` parse as identifiers in this category
    match id.getId with
    | `true => `($(layer.op `mkTrue))
    | `false => `($(layer.op `mkFalse))
    | _ => `(pure $id)
  | ``smtIte =>
    let fn := layer.op `ite
    let args ← #[stx[1], stx[3], stx[5]].mapM (expandSmt layer)
    bindArgs args fun ids => `($fn $(ids[0]!) $(ids[1]!) $(ids[2]!))
  | ``smtLet =>
    let id : Ident := ⟨stx[1]⟩
    let value ← expandSmt layer stx[3]
    let body ← expandSmt layer stx[5]
    `($value >>= fun $id => $body)
  | ``smtApp =>
    -- the two layers spell "the arguments" differently: an array sort-erased, an `Args` spine
    -- typed, where non-emptiness is structural rather than an autoparam
    let fn ← expandSmt layer stx[0]
    let args ← stx[1].getArgs.mapM (expandSmt layer)
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
  | ``smtMatch =>
    let scrut ← expandSmt layer stx[1]
    let scrutId ← freshId "smtScrut"
    let alts ← stx[3].getArgs.mapM (expandMatchAlt layer scrutId)
    let body ← bindArgs alts fun ids => `($(layer.op `mkMatch) $scrutId #[ $ids,* ])
    `($scrut >>= fun $scrutId => $body)
  | _ => Macro.throwErrorAt stx s!"unsupported SMT term (kind `{kind}`)"

/-- Expands one alternative of a `match` into a term building that case.

The variables a pattern binds are spliced as binders *as the writer wrote them*, never through
`mkIdent`, or hygiene would hide them from the body. Everything the expansion binds for its own
sake is macro-scoped instead, so the two cannot collide.

Each variable is bound twice: once to the bound variable itself, which the case needs, and once —
under the writer's name — to the term it converts to, which is what the body may mention. That
saves the coercion having to fire at every use.

The two layers build a case differently enough to be worth separate arms. Sort-erased, a bound
variable is made at the field's declared sort and the pattern is applied by hand; typed,
`Datatype.Ctor.case` builds the pattern and checks both the arity and the sorts, so all this has to
supply is the variables.
-/
partial def expandMatchAlt (layer : Layer) (scrutId : Ident) (alt : Syntax)
: MacroM (TSyntax `term) := do
  match alt.getKind with
  | ``smtAltAny =>
    let body ← expandSmt layer alt[3]
    let bvId ← freshId "smtAnyVar"
    let bodyId ← freshId "smtBody"
    if layer == .typed then
      -- the index comes from `caseAny`, which shares it with the scrutinee
      `($(layer.name `BVar.mk) "_" >>= fun $bvId =>
        $body >>= fun $bodyId =>
        $(layer.name `Datatype.caseAny) $bvId $bodyId)
    else
      let srtId ← freshId "smtSrt"
      `($(layer.op `getSort) $scrutId >>= fun $srtId =>
        $(layer.name `BVar.mk) $srtId "_" >>= fun $bvId =>
        $body >>= fun $bodyId =>
        $(layer.op `matchBindCase) #[$bvId] ($bvId).toTerm $bodyId)
  | ``smtAlt =>
    let ctor : Ident := ⟨alt[1]⟩
    let rawBody := alt[4]
    let body ← expandSmt layer rawBody

    let pats ← patArgs alt[2].getArgs
    let binders := pats.map Prod.fst
    let mut vars : Array Ident := #[]
    for idx in [0 : pats.size] do
      vars := vars.push (← freshId s!"smtBVar{idx}")
    let bvIds := vars
    let bvTerms ← bvIds.mapM fun id => `(($id).toTerm)

    let ctorId ← freshId "smtCtor"
    let bodyId ← freshId "smtBody"

    -- built innermost outwards, so each binder is in scope of everything after it
    if layer == .typed then
      -- every field is bound sort-erased, at the sort the declaration gives it; only the ones the
      -- body can name are re-typed, since a field the body ignores offers no index to infer
      let mut acc ← `(($ctorId).caseErased #[ $bvIds,* ] $bodyId)
      acc ← `($body >>= fun $bodyId => $acc)
      for idx in [0 : pats.size] do
        let jdx := pats.size - 1 - idx
        let (binder, typ?) := pats[jdx]!
        let used := occursIn binder.getId rawBody
        unless typ?.isNone && !used do
          let tc ←
            match typ? with
            | some typ => `((($(bvIds[jdx]!)).toTerm).typeCheckAs $typ)
            | none => `((($(bvIds[jdx]!)).toTerm).typeCheck)
          -- a used variable is bound under the writer's own name, so a mismatch in the body names
          -- it; one that is only ascribed is bound out of sight, its check being the whole point
          let bindTo ← if used then pure binder else freshId "smtChecked"
          acc ← `($tc >>= fun $bindTo => $acc)
      for idx in [0 : pats.size] do
        let jdx := pats.size - 1 - idx
        let name : TSyntax `term := quote pats[jdx]!.fst.getId.toString
        acc ← `(($ctorId).mkBVarAt $(quote jdx) $name >>= fun $(bvIds[jdx]!) => $acc)
      acc ← `(($ctorId).checkArity $(quote pats.size) >>= fun _ => $acc)
      `($(layer.op `ctorOf) $scrutId $(quote ctor.getId.toString) >>= fun $ctorId => $acc)
    else
      for (_, typ?) in pats do
        if let some typ := typ? then
          Macro.throwErrorAt typ
            "a sort ascription has no meaning in the sort-erased layer, where a field's sort comes \
            from the datatype's declaration"
      let ctorTermId ← freshId "smtCtorTerm"
      let patId ← freshId "smtPat"
      let mut acc ←
        if pats.isEmpty
        then `($(layer.op `matchCase) $patId $bodyId)
        else `($(layer.op `matchBindCase) #[ $bvIds,* ] $patId $bodyId)
      -- the body, under the writer's names for the variables the pattern binds
      acc ←
        if pats.isEmpty
        then `($body >>= fun $bodyId => $acc)
        else `((fun $binders* => $body) $bvTerms* >>= fun $bodyId => $acc)
      acc ← `($(layer.op `applyConstructor) $ctorTermId #[ $bvTerms,* ] >>= fun $patId => $acc)
      acc ← `(($ctorId).getTerm >>= fun $ctorTermId => $acc)
      for idx in [0 : pats.size] do
        let jdx := pats.size - 1 - idx
        let name : TSyntax `term := quote pats[jdx]!.fst.getId.toString
        let at' : TSyntax `term := quote jdx
        acc ← `(($ctorId).mkBVarAt $at' $name >>= fun $(bvIds[jdx]!) => $acc)
      acc ← `(($ctorId).checkArity $(quote pats.size) >>= fun _ => $acc)
      `($(layer.op `ctorOf) $scrutId $(quote ctor.getId.toString) >>= fun $ctorId => $acc)
  | k => Macro.throwErrorAt alt s!"unsupported match alternative (kind `{k}`)"

end

macro_rules
  | `(smtU! $t:smtTerm) => expandSmt .untyped t
  | `(smtT! $t:smtTerm) => expandSmt .typed t
