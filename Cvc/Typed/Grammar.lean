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
import all Cvc.Typed.Core.Defs
import all Cvc.Untyped.Core.BVar
import all Cvc.Typed.Core.BVar
import all Cvc.Untyped.Grammar
-- the grammar's fields are private to the solver module that declares the type
import all Cvc.Typed.Core.Solver

public import Cvc.Typed.Core.BVar
public import Cvc.Untyped.Grammar
public import Cvc.Typed.Core.Solver
public meta import Cvc.Untyped.Grammar
public meta import Cvc.Ext



/-! # SyGuS grammars, typed

A grammar restricts the shape of a term the solver may produce, for `synthFun`, `getInterpolant` or
`getAbduct`. `smt.grammar!` writes one as a block, its first non-terminal being the start symbol:

```lean
smt.grammar! s (x y : Int) where
  start : Int  := x | y | 0 | if c then start else start
  c     : Bool := start ≤ start
```

A rule must have its non-terminal's sort, or it does not compile. A `Grammar σ` carries the
parameters it was built over, and `σ` is their sorts arrowed onto the start symbol's
(`Int → Int → Int` above), so `synthFun` needs nothing else. Any solver of the scope accepts a
grammar, but **a grammar freezes once used**: after `synthFun`, cvc5 rejects further rules.
-/
namespace Cvc.Typed public section variable [Ω]




/-! ## Non-terminal symbols -/

/-- A grammar's non-terminal symbol, at the sort its index describes.

A bound variable, but not interchangeable with one: `mkGrammar` takes the parameters and the
non-terminals separately, and only the type keeps them apart.
-/
structure NT (α : Type) where
  private ofUntyped ::
  private untyped : Untyped.NT
-- A *structure* rather than an alias, for the same reason as the sort-erased one: a `def` wrapper
-- would need `Term` exposed, and that would make the two layers the same type downstream. One
-- field, so it costs nothing at runtime.

/-- Non-terminal symbols of assorted sorts. -/
abbrev NTs := List ((α : Type) × NT α)

namespace NT

/-- A non-terminal symbol of the sort `α` describes. -/
def mk' (α : Type) [ToTyp α] (name : String) : Env (NT α) := do
  return ⟨← Untyped.NT.mk (← Srt.of α) name⟩

@[inherit_doc mk']
abbrev mk [ToTyp α] (name : String) : Env (NT α) := mk' α name

/-- Turns itself into a bound variable.

Explicit on purpose: there is no coercion, because a non-terminal is not a parameter.
-/
def toBVar (nt : NT α) : BVar α := nt.untyped.toBVar

/-- Turns itself into a term, which is how a non-terminal appears inside its own rules. -/
def toTerm (nt : NT α) : Term α := nt.untyped.toTerm

instance : Coe (NT α) (Term α) := ⟨toTerm⟩

/-- The sort-erased non-terminal it wraps, for free. -/
def toUntyped (nt : NT α) : Untyped.NT := nt.untyped

@[inherit_doc toUntyped]
abbrev erase := @toUntyped

end NT

/-- Types a sort-erased non-terminal at `α`, checking its sort against `α`'s.

The non-terminal counterpart of `Untyped.Term.toTypedAs`, so that the non-terminals a sort-erased
grammar was built with can be given rules through the typed `Grammar.addRule`. `toTyped` infers
`α` from the expected type; `typeCheckAs` and `typeCheck` are the same two functions under the
names that say what they do.
-/
def _root_.Cvc.Untyped.NT.toTypedAs (α : Type) [ToTyp α] (nt : Untyped.NT) : Env (NT α) := do
  let srt ← nt.toTerm.getSort
  let srt' ← Srt.of α
  if srt != srt' then
    throwUser s!"cannot type non-terminal `{nt}` as `{srt'}`, it has sort `{srt}`"
  return ⟨nt⟩

@[inherit_doc Untyped.NT.toTypedAs]
def _root_.Cvc.Untyped.NT.toTyped [ToTyp α] (nt : Untyped.NT) : Env (NT α) := nt.toTypedAs α

@[inherit_doc Untyped.NT.toTypedAs]
abbrev _root_.Cvc.Untyped.NT.typeCheckAs := @Untyped.NT.toTypedAs

@[inherit_doc Untyped.NT.toTypedAs]
abbrev _root_.Cvc.Untyped.NT.typeCheck := @Untyped.NT.toTyped

namespace NTs

/-- Adds a non-terminal. -/
abbrev push (nt : NT α) (nts : NTs) : NTs := ⟨α, nt⟩ :: nts

/-- The sort-erased non-terminals, in the same order. -/
def toUntyped (nts : NTs) : Untyped.NTs :=
  nts.foldr (init := Array.mkEmpty nts.length) fun ⟨_, nt⟩ acc => acc.push nt.erase

@[inherit_doc toUntyped]
abbrev erase := @toUntyped

end NTs



/-! ## Grammars -/
-- The type is declared beside `Solver`, whose interpolant and abduct queries take one; what is here
-- builds one.

namespace Solver variable (s : Solver)

/-- A grammar over the given parameters, starting at `start`.

`boundVars` are the parameters of the function the grammar will constrain, and the index is their
sorts arrowed onto `start`'s. `others` are the other non-terminals the rules may mention.
-/
def mkGrammar [ToTyp α] (boundVars : BVars) (start : NT α) (others : NTs := [])
: Env (Grammar (boundVars.signatureTo α)) := do
  return ⟨← Untyped.Solver.mkGrammar s boundVars.erase start.erase others.erase⟩

end Solver

/-- Types a sort-erased grammar at signature `σ`, checking it against what the grammar generates.

`σ` is compared with the grammar's parameters' sorts arrowed onto its start symbol's. `toTyped`
infers `σ` from the expected type; `typeCheckAs` and `typeCheck` are the same two functions.
-/
def _root_.Cvc.Untyped.Grammar.toTypedAs (σ : Type) [ToTyp σ] (g : Untyped.Grammar)
: Env (Grammar σ) := do
  let srt ← g.signatureSrt
  let srt' ← Srt.of σ
  if srt != srt' then
    throwUser s!"cannot type the following grammar as `{srt'}`, it generates `{srt}`:\n{g}"
  return ⟨g⟩
-- Arrows flatten, so a one-parameter grammar whose start symbol is a function checks against the
-- same `σ` as a grammar taking those arguments as parameters; that is harmless, cvc5 flattening a
-- function sort the same way, so the function `synthFun` declares has sort `σ` either way.

@[inherit_doc Untyped.Grammar.toTypedAs]
def _root_.Cvc.Untyped.Grammar.toTyped [ToTyp σ] (g : Untyped.Grammar) : Env (Grammar σ) :=
  g.toTypedAs σ

@[inherit_doc Untyped.Grammar.toTypedAs]
abbrev _root_.Cvc.Untyped.Grammar.typeCheckAs := @Untyped.Grammar.toTypedAs

@[inherit_doc Untyped.Grammar.toTypedAs]
abbrev _root_.Cvc.Untyped.Grammar.typeCheck := @Untyped.Grammar.toTyped

namespace Grammar variable (g : Grammar σ)

/-- Adds a production rule.

The rule's index is the non-terminal's, so a sort mismatch does not typecheck. That the
non-terminal belongs to *this* grammar is a property of a value rather than a type, so it is
checked when the rule is added.
-/
def addRule (nt : NT α) (rule : Term α) : Env (Grammar σ) := do
  return {g with untyped := ← g.untyped.addRule nt.erase rule.erase}

@[inherit_doc addRule]
def addRules (nt : NT α) (rules : Terms α) : Env (Grammar σ) := do
  return {g with untyped := ← g.untyped.addRules nt.erase (rules.map Term.erase)}

/-- Allows any constant of the non-terminal's sort. -/
def addAnyConstant (nt : NT α) : Env (Grammar σ) := do
  return {g with untyped := ← g.untyped.addAnyConstant nt.erase}

/-- Allows any of the grammar's parameters that has the non-terminal's sort. -/
def addAnyVariable (nt : NT α) : Env (Grammar σ) := do
  return {g with untyped := ← g.untyped.addAnyVariable nt.erase}

end Grammar

end

end Cvc.Typed



/-! ## `smt.grammar!`

Available under `open Cvc.Typed`. A parameter's or a non-terminal's sort is written as a Lean type.
To add rules afterwards, `smt.mkGrammar!` and `smt.letGrammar!` also hand back the parameters, as
`BVar α`, and the non-terminals, as `NT α`; there, a non-terminal may be declared with no
alternatives (`n : Int`).
-/
-- The syntax is declared beside the sort-erased grammar; this is the typed expansion.

namespace Cvc.Typed

/-- A grammar written as a block: `smt.grammar! s (x : Int) where start : Int := x | ?const`.

After the solver building it and the parameters, one line per non-terminal, the first being the
start symbol, with `|`-separated `smt!` alternatives. `?const` and `?var` allow any constant and
any parameter of the non-terminal's sort.
-/
scoped syntax "smt.grammar! " smtGrammarBody : term

macro_rules
  | `(smt.grammar! $body) => `(grammarT! $body)

/-- `smt.grammar!`, also answering the parameters and non-terminals it made.

The result is `(g, nt₁, …)`, or `((g, p₁, …), nt₁, …)` when there are parameters `p₁, …`.
-/
scoped syntax "smt.mkGrammar! " smtGrammarBody : term

macro_rules
  | `(smt.mkGrammar! $body) => `(mkGrammarT! $body)

/-- `smt.grammar!` as a `do` element, binding the grammar, its parameters and its non-terminals.

`smt.letGrammar! g ← s (x : Int) where …` binds `g`, and each parameter and non-terminal under its
own name.
-/
scoped syntax "smt.letGrammar! " ident " ← " smtGrammarBody : doElem

end Cvc.Typed

namespace Cvc

public meta section

@[inherit_doc grammarT]
macro_rules
  | `(grammarT! $body) => Ext.expandGrammar Ext.Layer.typed body

@[inherit_doc mkGrammarT]
macro_rules
  | `(mkGrammarT! $body) => Ext.expandGrammar Ext.Layer.typed body (withParts := true)

namespace Typed

macro_rules
  | `(doElem| smt.letGrammar! $g ← $body) => do
    let pat ← Ext.letGrammarPattern g body
    `(doElem| let $pat:term ← mkGrammarT! $body)

end Typed

end

end Cvc
