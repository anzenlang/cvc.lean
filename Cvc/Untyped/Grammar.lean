/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic
import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.Core.BVar
-- `import all`: the solver's conversion to cvc5 is private
import all Cvc.Untyped.Core.Solver

public import Cvc.Untyped.Core.BVar
public import Cvc.Untyped.Core.Solver
public import Cvc.Untyped.Theory.Quant
public meta import Cvc.Untyped.Theory.Quant
public import Cvc.Ext
public meta import Cvc.Ext



/-! # SyGuS grammars, sort-erased

A grammar restricts the shape of a term the solver is allowed to produce — the candidates a
`synth-fun` may return, or the shape of an interpolant or abduct.

Two kinds of variable go into one: the **parameters** the synthesized term may mention, and the
**non-terminals** the rules are written over. cvc5 takes both as plain bound variables, which makes
them trivial to mix up, so a non-terminal has its own type here. `NT` converts to a term, because a
non-terminal appears inside its own rules, but not to a `BVar`: handing one to `mkGrammar` as a
parameter is exactly the mistake worth ruling out.

**A grammar freezes once it is used.** `addRule` and friends answer a *new* `Grammar`, so the type
reads as though grammars were persistent values, but the object underneath is shared: once a
grammar has been passed to `synthFun`, cvc5 rejects every further rule with `Grammar cannot be
modified after passing it as an argument to synthFun`. Build a grammar completely before using it.
-/
namespace Cvc public section variable [Ω]

namespace Untyped



/-! ## Non-terminal symbols -/

/-- A grammar's non-terminal symbol.

A bound variable, but not interchangeable with one: `mkGrammar` takes the parameters and the
non-terminals as separate arrays, and nothing but the type stops them being swapped.

A *structure* rather than an alias: a `def` wrapper would need `BVar`, and so `Term`, exposed for
its conversions to compile across a module boundary, and exposing `Term` would make the two layers
the same type to every downstream module. One field, so it costs nothing at runtime.
-/
structure NT where
  private ofBVar ::
  private bvar : BVar
deriving BEq, Ord, Hashable

/-- An array of non-terminal symbols. -/
abbrev NTs := Array NT

namespace NT

/-- A non-terminal symbol of the given sort. -/
def mk (srt : Srt) (name : String) : Env NT := do return ⟨← BVar.mk srt name⟩

/-- Turns itself into a bound variable.

Explicit on purpose: there is no coercion, because a non-terminal is not a parameter.
-/
def toBVar (nt : NT) : BVar := nt.bvar

/-- Turns itself into a term, which is how a non-terminal appears inside its own rules. -/
def toTerm (nt : NT) : Term := nt.toBVar.toTerm

instance : Coe NT Term := ⟨toTerm⟩

instance : ToString NT := ⟨toString ∘ toTerm⟩

end NT



end Untyped



/-! ## Grammars

A grammar belongs to the scope, as a term does: cvc5 builds one through a solver, but any solver
of the same term manager accepts it. The type is declared beside `Solver`, whose interpolant and
abduct queries take one; what is here builds one.
-/

namespace Untyped.Solver open Untyped variable (s : Solver)

/-- A grammar over the given parameters, starting at `start`.

`boundVars` are the parameters of the `synth-fun` this grammar will constrain, and must be the very
same variables that function is declared with. `others` are the further non-terminals the rules may
mention: every one has to be declared here, since a rule over an undeclared symbol is rejected.

The start symbol is a separate argument rather than the head of one array, because cvc5 takes the
*first* non-terminal as the start symbol and then drops whatever is unreachable from it — silently.
Handing it `#[cnd, start]` instead of `#[start, cnd]` yields a grammar containing neither `start`
nor its rules, with no error. Naming the start symbol makes that unrepresentable, and makes the
array's non-emptiness structural rather than a side condition.
-/
def mkGrammar (boundVars : BVars) (start : NT) (others : NTs := #[]) : Env Grammar := do
  let raw : cvc5.Grammar ← runUnsafe' do
    s.toUnsafe.mkGrammar (boundVars.map BVar.toTerm) (#[start.toTerm] ++ others.map NT.toTerm)
  return ⟨raw, boundVars, ← start.toTerm.getSort⟩

end Untyped.Solver

namespace Untyped.Grammar open Untyped variable (g : Grammar)

def mk (boundVars : BVars) (start : NT) (others : NTs := #[]) : Env Grammar := do
  -- need to create a solver although it will never be used
  -- waiting for upstream to provide a solver-free constructor
  let s ← Solver.new
  s.mkGrammar boundVars start others

/-- The sort of the functions the grammar generates.

The parameters' sorts arrowed onto the start symbol's, flattened as a curried Lean arrow is, or the
start symbol's sort alone when there are no parameters.
-/
def signatureSrt : Env Srt := do
  let dom ← g.boundVars.mapM (·.toTerm.getSort)
  if h : 0 < dom.size then
    if g.startSrt.isFunction then
      let dom' := dom ++ (← g.startSrt.getFunctionDomainSorts)
      Srt.function dom' (← g.startSrt.getFunctionCodomainSort)
    else Srt.function dom g.startSrt
  else return g.startSrt

/-- The same grammar with its underlying cvc5 grammar replaced. -/
private def withRaw (code : cvc5.Env cvc5.Grammar) : Env Grammar := do
  let raw ← runUnsafe' code
  return {g with raw}

/-- Adds a production rule.

`nt` must be one of the non-terminals this grammar was declared with, and `rule` must have its
sort. Neither is visible in a signature, so both are checked when the rule is added.
-/
def addRule (nt : NT) (rule : Term) : Env Grammar :=
  g.withRaw do g.raw.addRule nt.toTerm rule

@[inherit_doc addRule]
def addRules (nt : NT) (rules : Terms) : Env Grammar :=
  g.withRaw do g.raw.addRules nt.toTerm rules

/-- Allows any constant of the non-terminal's sort. -/
def addAnyConstant (nt : NT) : Env Grammar :=
  g.withRaw do g.raw.addAnyConstant nt.toTerm

/-- Allows any of the grammar's parameters that has the non-terminal's sort. -/
def addAnyVariable (nt : NT) : Env Grammar :=
  g.withRaw do g.raw.addAnyVariable nt.toTerm

end Untyped.Grammar

end

end Cvc



/-! ## `smt.grammar!`

A grammar written as one block, BNF-style, with `smt!` terms as its alternatives:

```lean
smt.grammar! s (x y : Int) where
  start : Int  := x | y | if cnd then start else start
  cnd   : Bool := start ≤ start
```

- `s` is a solver to build the grammar with — any solver of the scope will do, a grammar belonging
  to the scope rather than to a solver; the binders after it are the grammar's parameters.
- Each line declares a non-terminal and its sort, then its alternatives separated by `|`. The first
  line's is the start symbol.
- Inside the alternatives a non-terminal or parameter stands for its term, so rules mention one
  another and themselves freely. Every non-terminal is made before any rule is added.
- `?const` and `?var` are cvc5's "any constant" and "any parameter" of the non-terminal's sort.

A sort is written as a Lean type or a `Srt` sort-erased, and as a Lean type typed — the typed
`smt.grammar!` being an ordinary `Grammar` whose index is the parameters folded over the start sort.

### Extending a grammar afterwards

`smt.grammar!` answers the grammar alone, its parameters and non-terminals being made out of sight,
so nothing can be added to it later. Two forms with the same body answer them too:

- `smt.mkGrammar! s … where …` answers `grammar × NT₁ × NT₂ × …` without parameters, and
  `(grammar × PARAM₁ × …) × NT₁ × NT₂ × …` with some, in declaration order. The parameters are
  grouped with the grammar so that one cannot be taken for a non-terminal by position.
- `smt.letGrammar! g ← s … where …` is a `do` element binding `g`, the parameters and the
  non-terminals under the names the block declares, so the order cannot be got wrong:

  ```lean
  smt.letGrammar! g ← s (x y : Int) where
    start : Int  := x | y
    cnd   : Bool := start ≤ start
  let g ← g.addRule start (← smt! if cnd then start else start)
  ```

  A parameter is bound as a `BVar` and a non-terminal as an `NT`, both converting to terms. The
  names are bound without a source position, so one never used afterwards draws no warning.

In these two forms a non-terminal may be declared without alternatives, `nt : sort` alone, for its
rules to be added afterwards — rules computed from data, say, which a block cannot spell:

```lean
smt.letGrammar! g ← s (x : Int) where
  start : Int := x | start + num
  num   : Int
let mut g := g
for k in [3, 7] do g ← g.addRule num (← Term.mkInt k)
```

`smt.grammar!` refuses such a line, since the grammar it answers cannot be extended.

A grammar can be extended until it is used for synthesis, after which cvc5 rejects new rules. A
non-terminal unreachable from the start symbol is left out of the grammar until a rule reaches it.

All three forms are `scoped` in each layer, as `smt!` is: `open Cvc.Untyped` selects this one.
-/

namespace Cvc

/-- One alternative of a `smt.grammar!` rule. -/
declare_syntax_cat smtGrammarAlt (behavior := symbol)

/-- `?const` or `?var`: any constant, or any parameter, of the non-terminal's sort. -/
syntax (name := smtGrammarAny) "?" ident : smtGrammarAlt

/-- An alternative that is a term. -/
syntax (name := smtGrammarTerm) smtTerm : smtGrammarAlt

/-- One line of a `smt.grammar!`: a non-terminal, its sort, and its alternatives. -/
declare_syntax_cat smtGrammarRule (behavior := symbol)

/-- `nt : sort := alt | alt | …`, or `nt : sort` alone, its rules to be added afterwards. -/
syntax (name := smtGrammarRule)
  withPosition(ident " : " term (" := " sepBy1(smtGrammarAlt, " | "))?) : smtGrammarRule

/-- What follows `smt.grammar!`: the solver, the parameters, and the rules. -/
declare_syntax_cat smtGrammarBody (behavior := symbol)

/-- `s (x : Int) … where` followed by the rules, one per line. -/
syntax (name := smtGrammarBody)
  term:max (ppSpace smtQuantBinder)* " where" many1Indent(ppLine smtGrammarRule) : smtGrammarBody

/-- A sort-erased grammar; `smt.grammar!` under `open Cvc.Untyped`. -/
syntax (name := grammarU) "grammarU! " smtGrammarBody : term

/-- A typed grammar; `smt.grammar!` under `open Cvc.Typed`. -/
syntax (name := grammarT) "grammarT! " smtGrammarBody : term

/-- A sort-erased grammar and its parts; `smt.mkGrammar!` under `open Cvc.Untyped`. -/
syntax (name := mkGrammarU) "mkGrammarU! " smtGrammarBody : term

/-- A typed grammar and its parts; `smt.mkGrammar!` under `open Cvc.Typed`. -/
syntax (name := mkGrammarT) "mkGrammarT! " smtGrammarBody : term

namespace Untyped

/-- Sort-erased `smt.grammar!`. -/
scoped syntax "smt.grammar! " smtGrammarBody : term

macro_rules
  | `(smt.grammar! $body) => `(grammarU! $body)

/-- Sort-erased `smt.mkGrammar!`: the grammar together with its parameters and non-terminals. -/
scoped syntax "smt.mkGrammar! " smtGrammarBody : term

macro_rules
  | `(smt.mkGrammar! $body) => `(mkGrammarU! $body)

/-- Sort-erased `smt.letGrammar!`: binds the grammar, its parameters and its non-terminals. -/
scoped syntax "smt.letGrammar! " ident " ← " smtGrammarBody : doElem

end Untyped

public meta section

open Lean

namespace Ext

/-- Whether an identifier of this name occurs anywhere in a piece of syntax. -/
def mentions (name : Name) (stx : Syntax) : Bool :=
  (stx.find? fun s => s.isIdent && s.getId == name).isSome

/-- A right-nested tuple of the given terms, `(a, b, c)`; a single term stands for itself. -/
def mkTuple : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => Macro.throwUnsupported
  | [t] => pure t
  | t :: ts => do `(($t, $(← mkTuple ts)))

/-- The right-nested product of the given types, `α × β × γ`; a single type stands for itself. -/
def mkProd : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => Macro.throwUnsupported
  | [t] => pure t
  | t :: ts => do `($t × $(← mkProd ts))

/-- The alternatives of one `smt.grammar!` rule, none when it only declares its non-terminal. -/
def ruleAlts (rule : Syntax) : Array Syntax :=
  if rule[3].isNone then #[] else rule[3][1].getSepArgs

/-- Expands the body of a `smt.grammar!` or `smt.mkGrammar!` for the given layer.

With `withParts`, the result carries what the grammar was built from as well as the grammar, so
that it can be extended afterwards: `grammar × NT₁ × NT₂ × …` without parameters, and
`(grammar × PARAM₁ × …) × NT₁ × NT₂ × …` with some, the grouping keeping the two apart.
-/
def expandGrammar (layer : Layer) (body : Syntax) (withParts : Bool := false)
: MacroM (TSyntax `term) := do
  let solver : Term := ⟨body[0]⟩
  let params := quantBinders body[1]
  let rules := body[3].getArgs
  let typed := layer == Layer.typed
  -- what the rules mention, so that only those names are bound and the linter stays quiet
  let alts := rules.flatMap ruleAlts
  let mentioned (id : Ident) : Bool := alts.any (mentions id.getId)
  -- refuse a non-terminal declared twice, which would silently shadow the first
  let ntIds : Array Ident := rules.map (⟨·[0]⟩)
  for i in [0:ntIds.size] do
    for j in [0:i] do
      if ntIds[i]!.getId == ntIds[j]!.getId then
        Macro.throwErrorAt ntIds[i]! s!"non-terminal `{ntIds[i]!.getId}` is declared twice"
  -- a non-terminal without alternatives is only useful if its rules can be added afterwards
  if !withParts then
    for (id, rule) in ntIds.zip rules do
      if ruleAlts rule |>.isEmpty then
        Macro.throwErrorAt id s!"non-terminal `{id.getId}` has no alternatives, and the grammar \
          `smt.grammar!` answers cannot be extended: give it some, or use `smt.mkGrammar!` or \
          `smt.letGrammar!` to add its rules afterwards"
  let mut elems : Array (TSyntax `doElem) := #[]
  -- the parameters and the non-terminals, under names the writer never sees
  let mut paramVars := #[]
  for (id, sort) in params do
    let var ← freshId s!"param_{id.getId}"
    let mk ← if typed then `($(layer.name `BVar.mk) (α := $sort) $(quantName id))
      else `($(layer.name `BVar.mk) (← srtOf% ($sort)) $(quantName id))
    elems := elems.push (← `(doElem| let $var ← $mk:term))
    paramVars := paramVars.push var
  let mut ntVars := #[]
  for rule in rules do
    let id : Ident := ⟨rule[0]⟩
    let sort : Term := ⟨rule[2]⟩
    let var ← freshId s!"nt_{id.getId}"
    let mk ← if typed then `($(layer.name `NT.mk) (α := $sort) $(quantName id))
      else `($(layer.name `NT.mk) (← srtOf% ($sort)) $(quantName id))
    elems := elems.push (← `(doElem| let $var ← $mk:term))
    ntVars := ntVars.push var
  -- the grammar, its first non-terminal being the start symbol
  let g ← freshId "grammar"
  let start := ntVars[0]!
  let others := ntVars.extract 1 ntVars.size
  let mkGrammar ← if typed then do
      let mut bvs ← `([])
      for var in paramVars do bvs ← `($(layer.name `BVars.push) $var $bvs)
      let mut nts ← `([])
      for var in others.reverse do nts ← `($(layer.name `NTs.push) $var $nts)
      `($(layer.name `Solver.mkGrammar) $solver $bvs $start $nts)
    else `($(layer.name `Solver.mkGrammar) $solver #[$paramVars,*] $start #[$others,*])
  elems := elems.push (← `(doElem| let $g ← $mkGrammar:term))
  -- inside the rules, a name the writer gave stands for its term
  for ((id, _), var) in params.zip paramVars do
    if mentioned id then elems := elems.push (← `(doElem| let $id := ($var).toTerm))
  for (id, var) in ntIds.zip ntVars do
    if mentioned id then elems := elems.push (← `(doElem| let $id := ($var).toTerm))
  -- one rule per alternative
  let grammarNs := layer.name `Grammar
  let builder (fn : Name) : Ident := mkIdent (grammarNs.getId ++ fn)
  for (rule, var) in rules.zip ntVars do
    for alt in ruleAlts rule do
      let add ← match alt.getKind with
        | ``smtGrammarAny =>
          match alt[1].getId with
          | `const => `($(builder `addAnyConstant) $g $var)
          | `var => `($(builder `addAnyVariable) $g $var)
          | other => Macro.throwErrorAt alt[1] s!"expected `?const` or `?var`, got `?{other}`"
        | _ => withRef alt do
          let term ← deferSmt layer alt[0]
          -- typed, the alternative is ascribed its non-terminal's sort, so that a mismatch is
          -- reported at the alternative rather than at a non-terminal the writer never sees
          let term ← if typed then
              `(($term : $(mkIdent `Cvc.Env) ($(layer.name `Term) $(⟨rule[2]⟩))))
            else pure term
          `($term >>= $(builder `addRule) $g $var)
      elems := elems.push (← `(doElem| let $g ← $add:term))
  let items : Array (TSyntax ``Lean.Parser.Term.doSeqItem) :=
    elems.map fun e => ⟨mkNode ``Lean.Parser.Term.doSeqItem #[e, mkNullNode]⟩
  -- the result is ascribed: left to inference, a grammar bound over an earlier one of another
  -- index in the same `do` block leaves the inner block's type a metavariable it cannot solve
  let env := mkIdent `Cvc.Env
  let grammarTy ← if typed then do
      let mut sig : Term := ⟨(rules[0]!)[2]⟩
      for (_, sort) in params.reverse do sig ← `($sort → $sig)
      `($(layer.name `Grammar) $sig)
    else `($(layer.name `Grammar))
  if !withParts then
    return ← `((do $[$items]* pure $g : $env $grammarTy))
  -- the grammar with its parameters, then the non-terminals
  let bvarTy (sort : Term) : MacroM Term :=
    if typed then `($(layer.name `BVar) $sort) else `($(layer.name `BVar))
  let ntTy (sort : Term) : MacroM Term :=
    if typed then `($(layer.name `NT) $sort) else `($(layer.name `NT))
  let paramTys ← params.toList.mapM fun (_, sort) => bvarTy sort
  let ntTys ← rules.toList.mapM fun rule => ntTy ⟨rule[2]⟩
  let asTerm (id : Ident) : Term := ⟨id.raw⟩
  let headVal ← mkTuple (asTerm g :: paramVars.toList.map asTerm)
  let headTy ← mkProd (grammarTy :: paramTys)
  let result ← mkTuple (headVal :: ntVars.toList.map asTerm)
  let resultTy ← mkProd (headTy :: ntTys)
  `((do $[$items]* pure $result : $env ($resultTy)))

/-- The pattern `smt.letGrammar! g ← …` binds: `g`, the parameters and the non-terminals, grouped as
`smt.mkGrammar!` answers them and named as the block declares them.

The declared names are bound without a source position: the `do` element cannot see the rest of
its block, so it cannot tell which ones are used there, and positioned binders would trip the
unused-variable linter for every non-terminal that is never extended.
-/
def letGrammarPattern (g : Ident) (body : Syntax) : MacroM (TSyntax `term) := do
  let params := quantBinders body[1]
  let rules := body[3].getArgs
  let quiet (id : Syntax) : Term := ⟨(mkIdent id.getId).raw⟩
  let head ← mkTuple (⟨g.raw⟩ :: params.toList.map (fun (id, _) => quiet id))
  mkTuple (head :: rules.toList.map (fun rule => quiet rule[0]))

end Ext

@[inherit_doc grammarU]
macro_rules
  | `(grammarU! $body) => Ext.expandGrammar Ext.Layer.untyped body

@[inherit_doc mkGrammarU]
macro_rules
  | `(mkGrammarU! $body) => Ext.expandGrammar Ext.Layer.untyped body (withParts := true)

namespace Untyped

@[inherit_doc mkGrammarU]
macro_rules
  | `(doElem| smt.letGrammar! $g ← $body) => do
    let pat ← Ext.letGrammarPattern g body
    `(doElem| let $pat:term ← mkGrammarU! $body)

end Untyped

end

end Cvc
