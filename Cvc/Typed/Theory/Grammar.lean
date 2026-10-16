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
import all Cvc.Untyped.BVar
import all Cvc.Typed.BVar
import all Cvc.Untyped.Theory.Grammar
-- the grammar's fields are private to the solver module that declares the type
import all Cvc.Typed.Solver

public import Cvc.Typed.BVar
public import Cvc.Untyped.Theory.Grammar
public import Cvc.Typed.Solver
public meta import Cvc.Untyped.Theory.Grammar
public meta import Cvc.Ext



/-! # SyGuS grammars, typed

A grammar restricts the shape of a term the solver may produce. Two things about one go wrong
easily, and both are stated in the types here.

A **rule must have its non-terminal's sort** — cvc5 answers `expected ntSymbol and rule to have the
same sort`, which `addRule` turns into a type error.

A grammar's **parameters must be the very same variables** the `synth-fun` is declared with. In
SyGuS they are one thing, `(synth-fun f ((x Int)) Int G)`, but two arguments in the API, so this
`Grammar` carries its own parameters and `synthFun` takes nothing else. Its index is the *signature*
the grammar can generate: `Grammar (bvs.signatureTo α)`, folded exactly as `Solver.defineFun`
folds its own parameters. With no parameters that is just the start symbol's sort, which is the
shape `getInterpolant` and `getAbduct` want.

A grammar is built through a solver, `s.mkGrammar`, but belongs to the scope as a term does: any
solver of the scope accepts it.

**A grammar freezes once it is used**, as in the sort-erased layer: the rule builders answer a new
`Grammar`, but the object underneath is shared and cvc5 rejects further rules after `synthFun`.
-/
namespace Cvc.Typed public section variable [Ω]




/-! ## Non-terminal symbols -/

/-- A grammar's non-terminal symbol, at the sort its index describes.

A bound variable, but not interchangeable with one: `mkGrammar` takes the parameters and the
non-terminals separately, and only the type keeps them apart.

A *structure* rather than an alias, for the same reason as the sort-erased one: a `def` wrapper
would need `Term` exposed, and that would make the two layers the same type downstream. One field,
so it costs nothing at runtime.
-/
structure NT (α : Type) where
  private ofUntyped ::
  private untyped : Untyped.NT

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

/-- Erases the sort. -/
def erase (nt : NT α) : Untyped.NT := nt.untyped

end NT

namespace NTs

/-- Adds a non-terminal. -/
abbrev push (nt : NT α) (nts : NTs) : NTs := ⟨α, nt⟩ :: nts

/-- Erases the sorts, keeping the order. -/
def erase (nts : NTs) : Untyped.NTs :=
  nts.foldr (init := Array.mkEmpty nts.length) fun ⟨_, nt⟩ acc => acc.push nt.erase

end NTs



/-! ## Grammars

The type is declared beside `Solver`, whose interpolant and abduct queries take one; what is here
builds one. Like a term, a grammar belongs to the scope rather than to the solver that built it.
-/

namespace Solver variable (s : Solver)

/-- A grammar over the given parameters, starting at `start`.

`boundVars` are the parameters of the `synth-fun` this grammar will constrain; the resulting index
is the signature those parameters and `start`'s sort describe. `others` are further non-terminals
the rules may mention.
-/
def mkGrammar [ToTyp α] (boundVars : BVars) (start : NT α) (others : NTs := [])
: Env (Grammar (boundVars.signatureTo α)) := do
  let startSrt ← Srt.of α
  let untyped ← Untyped.Solver.mkGrammar s boundVars.erase start.erase others.erase
  return ⟨untyped, boundVars.erase, startSrt⟩

end Solver

namespace Grammar variable (g : Grammar σ)

/-- Adds a production rule.

The rule's index is the non-terminal's, so a sort mismatch does not typecheck. That the
non-terminal belongs to *this* grammar is a property of a value rather than a type, so it is
checked when the rule is added.
-/
def addRule (nt : NT α) (rule : Term α) : Env (Grammar σ) := do
  return {g with toUntyped := ← g.toUntyped.addRule nt.erase rule.erase}

@[inherit_doc addRule]
def addRules (nt : NT α) (rules : Terms α) : Env (Grammar σ) := do
  return {g with toUntyped := ← g.toUntyped.addRules nt.erase (rules.map Term.erase)}

/-- Allows any constant of the non-terminal's sort. -/
def addAnyConstant (nt : NT α) : Env (Grammar σ) := do
  return {g with toUntyped := ← g.toUntyped.addAnyConstant nt.erase}

/-- Allows any of the grammar's parameters that has the non-terminal's sort. -/
def addAnyVariable (nt : NT α) : Env (Grammar σ) := do
  return {g with toUntyped := ← g.toUntyped.addAnyVariable nt.erase}

end Grammar

end

end Cvc.Typed



/-! ## `grammar!`

The syntax is declared beside the sort-erased grammar; this is the typed expansion, and the scoped
`grammar!` that `open Cvc.Typed` selects. A sort is the Lean type of the non-terminal's or the
parameter's index, and the result is `Grammar σ` with `σ` the parameters folded over the start
sort, exactly what `Solver.mkGrammar` answers.
-/

namespace Cvc.Typed

/-- Typed `grammar!`. -/
scoped syntax "grammar! " smtGrammarBody : term

macro_rules
  | `(grammar! $body) => `(grammarT! $body)

end Cvc.Typed

namespace Cvc

public meta section

@[inherit_doc grammarT]
macro_rules
  | `(grammarT! $body) => Ext.expandGrammar Ext.Layer.typed body

end

end Cvc
