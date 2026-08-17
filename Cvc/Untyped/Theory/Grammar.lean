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
import all Cvc.Untyped.BVar
-- `import all`: the solver's conversion to cvc5 is private
import all Cvc.Untyped.Solver

public import Cvc.Untyped.BVar
public import Cvc.Untyped.Solver



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

end NT



end Untyped



/-! ## Grammars

`Grammar` itself is shared: a grammar mentions no sort in its own type, so the sort-erased rule
builders attach to it directly and the typed layer wraps it rather than restating it.
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
def mkGrammar (boundVars : BVars) (start : NT) (others : NTs := #[]) : Env Grammar :=
  runUnsafe' do
    s.toUnsafe.mkGrammar (boundVars.map BVar.toTerm) (#[start.toTerm] ++ others.map NT.toTerm)

end Untyped.Solver

namespace Grammar open Untyped variable (g : Grammar)

/-- Adds a production rule.

`nt` must be one of the non-terminals this grammar was declared with, and `rule` must have its
sort. Neither is visible in a signature, so both are checked when the rule is added.
-/
def addRule (nt : NT) (rule : Term) : Env Grammar :=
  runUnsafe' do g.toUnsafe.addRule nt.toTerm rule

@[inherit_doc addRule]
def addRules (nt : NT) (rules : Terms) : Env Grammar :=
  runUnsafe' do g.toUnsafe.addRules nt.toTerm rules

/-- Allows any constant of the non-terminal's sort. -/
def addAnyConstant (nt : NT) : Env Grammar :=
  runUnsafe' do g.toUnsafe.addAnyConstant nt.toTerm

/-- Allows any of the grammar's parameters that has the non-terminal's sort. -/
def addAnyVariable (nt : NT) : Env Grammar :=
  runUnsafe' do g.toUnsafe.addAnyVariable nt.toTerm

end Grammar
