/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.BVar
public import Cvc.Ext
public meta import Cvc.Ext

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.BVar



/-! # Quantifiers, sort-erased

A quantified formula binds its variables the way a lambda does: they are `BVar`s gathered into a
variable list, and the body mentions them as ordinary terms. Two spellings are offered.

- `mkForall`/`mkExists` take the bound variables explicitly, as `BVars.lambda` does.
- `forallH`/`existsH` take the body as a Lean function of the variables, so that no `BVar` is ever
  written by hand. The `H` is for *higher-order abstract syntax*: binding is borrowed from Lean's
  own `fun`.

A quantifier binds at least one variable, cvc5 rejecting an empty variable list. Asserting a
quantified formula needs a logic with quantifiers, such as the default `ALL`; a `QF_` logic rejects
it.

cvc5's `WITNESS` binder is deliberately not wrapped: asserting a term that contains one aborts the
process rather than raising an error.
-/
namespace Cvc.Untyped.Term public section variable [Ω]

/-- A quantified formula of kind `kind`, binding `bvs` in `body`. -/
private def mkQuant (kind : cvc5.Kind) (bvs : BVars) (body : Term) : Env Term := do
  let vars ← bvs.toTerm
  runUnsafe fun tm => tm.mkTerm kind #[vars, body]

/-- Universal quantification of `body` over `bvs`. -/
def mkForall (bvs : BVars) (body : Term)
  (_nonEmpty : 0 < bvs.size := by
    (try grind) <;> fail "failed to prove a quantifier binds at least one variable")
: Env Term :=
  mkQuant .FORALL bvs body

/-- Existential quantification of `body` over `bvs`. -/
def mkExists (bvs : BVars) (body : Term)
  (_nonEmpty : 0 < bvs.size := by
    (try grind) <;> fail "failed to prove a quantifier binds at least one variable")
: Env Term :=
  mkQuant .EXISTS bvs body



/-! ## Binding through Lean functions

`Binder φ` says that `φ` is the type of a quantifier's body written as a Lean function: one `Term`
argument per bound variable, ending in `Env Term`. There is no instance for a bare `Env Term`, so a
body binding no variable does not typecheck.

Sort-erased, a variable's sort cannot come from its type, so each is given beside its name, in
order. How many are given is a runtime fact, checked against the function's arity before any
variable is made.
-/

/-- `φ` is a quantifier body taking one `Term` per bound variable. -/
class Binder (φ : Type) where
  /-- How many variables the body binds. -/
  arity : Nat
  /-- Creates one bound variable per argument of `f`, from `binders`, and applies `f` to them.

  Assumes there are exactly `arity` binders, which `bindAll` checks.
  -/
  bind : List (String × Srt) → φ → Env (BVars × Term)

/-- The binder for a body taking the last bound variable. -/
instance : Binder (Term → Env Term) where
  arity := 1
  bind
    | (name, srt) :: _, f => do
      let bv ← BVar.mk srt name
      return (#[bv], ← f bv.toTerm)
    | [], _ => throwUnreachable "`bindAll` checks there is a binder per argument"

/-- The binder for a body taking a bound variable and more. -/
instance [B : Binder ψ] : Binder (Term → ψ) where
  arity := B.arity + 1
  bind
    | (name, srt) :: binders, f => do
      let bv ← BVar.mk srt name
      let (bvs, body) ← B.bind binders (f bv.toTerm)
      return (#[bv] ++ bvs, body)
    | [], _ => throwUnreachable "`bindAll` checks there is a binder per argument"

/-- Applies `body` to fresh variables made from `binders`, failing unless there is one per argument.
-/
private def bindAll [B : Binder φ] (binders : List (String × Srt)) (body : φ)
: Env (BVars × Term) := do
  if binders.length != B.arity then
    let plural (n : Nat) (what : String) := s!"{n} {what}{if n == 1 then "" else "s"}"
    throwUser s!"the body binds {plural B.arity "variable"}, but {
      plural binders.length "binder"} {if binders.length == 1 then "was" else "were"} given"
  B.bind binders body

/-- Universal quantification of a body written as a Lean function of its variables.

`binders` names each variable and gives its sort, in the order the function takes them:

```lean
Term.forallH [("x", int), ("y", int)] fun x y => do Term.equal (← Term.add x y) (← Term.add y x)
```
-/
def forallH [Binder φ] (binders : List (String × Srt)) (body : φ) : Env Term := do
  let (bvs, body) ← bindAll binders body
  mkQuant .FORALL bvs body

/-- Existential quantification of a body written as a Lean function of its variables.

`binders` names each variable and gives its sort, in the order the function takes them.
-/
def existsH [Binder φ] (binders : List (String × Srt)) (body : φ) : Env Term := do
  let (bvs, body) ← bindAll binders body
  mkQuant .EXISTS bvs body

end

end Cvc.Untyped.Term



namespace Cvc

public meta section

open Lean

/-! ## `smt!`

`smt! ∀ (x y : s) (b : t), body` and `smt! ∃ …` are Lean's own quantifier syntax, binders in
parentheses. What follows the colon depends on the layer: here it is a Lean type (`Int`) or a `Srt`
value (`int`), as wherever the sort-erased DSL takes a sort; typed, it is the Lean type the
variable's index is, and only that.

The body extends as far right as it can, as in Lean, so a quantifier in argument position needs
parentheses. Expansion goes through `forallH`/`existsH`, binding each variable under the name the
writer gave it, which is also the name cvc5 prints.
-/

/-- Binders of an `smt!` quantifier. -/
declare_syntax_cat smtQuantBinder (behavior := symbol)

/-- Variables sharing a sort: `(x y : s)`. -/
syntax (name := smtQuantBinder) "(" ident+ " : " term ")" : smtQuantBinder

/-- Universal quantification. -/
syntax:lead (name := smtForall) "∀ " (ppSpace smtQuantBinder)+ ", " smtTerm : smtTerm

/-- Existential quantification. -/
syntax:lead (name := smtExists) "∃ " (ppSpace smtQuantBinder)+ ", " smtTerm : smtTerm

namespace Ext

/-- The variables of a quantifier's binders, in order, each with the sort it was written with. -/
def quantBinders (binders : Syntax) : Array (Ident × Term) := Id.run do
  let mut acc := #[]
  for binder in binders.getArgs do
    for id in binder[1].getArgs do
      acc := acc.push ((⟨id⟩ : Ident), (⟨binder[3]⟩ : Term))
  return acc

/-- The name cvc5 gives a bound variable: the one the writer gave it. -/
def quantName (id : Ident) : StrLit := Syntax.mkStrLit id.getId.eraseMacroScopes.toString

/-! Expansion, sort-erased; the typed one is in `Cvc.Typed.Theory.Quant`. -/

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.untyped do Macro.throwUnsupported
    let stx := t.raw
    let fn ← match stx.getKind with
      | ``smtForall => pure (layer.op `forallH)
      | ``smtExists => pure (layer.op `existsH)
      | _ => Macro.throwUnsupported
    let binders := quantBinders stx[1]
    let body ← deferSmt layer stx[3]
    let ids := binders.map (·.1)
    let tys ← binders.mapM fun _ => `($(layer.name `Term))
    -- a sort is a Lean type or a `Srt`, either way an `Env Srt` to bind first
    let srts ← binders.mapM fun (_, sort) => `(srtOf% ($sort))
    bindArgs srts (binder := "smtSrt") fun srtIds => do
      let names ← (binders.zip srtIds).mapM fun ((id, _), srt) => `(($(quantName id), $srt))
      `($fn [$names,*] (fun $[($ids : $tys)]* => $body))

end Ext

end

end Cvc
