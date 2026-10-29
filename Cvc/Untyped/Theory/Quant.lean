/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core.BVar
public import Cvc.Gen.View
public import Cvc.Untyped.Core.View
public import Cvc.Ext
public meta import Cvc.Ext

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.Core.BVar



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

The body is a Lean function of the variables, one `Term` argument per variable, as for
`Term.lambdaH`: see `Binder`, which both share.
-/

/-- Universal quantification of a body written as a Lean function of its variables.

`binders` names each variable and gives its sort, in the order the function takes them:

```lean
Term.forallH [("x", int), ("y", int)] fun x y => do Term.equal (← Term.add x y) (← Term.add y x)
```
-/
def forallH [Binder φ] (binders : List (String × Srt)) (body : φ) : Env Term := do
  let (bvs, body) ← Binder.bindAll binders body
  mkQuant .FORALL bvs body

/-- Existential quantification of a body written as a Lean function of its variables.

`binders` names each variable and gives its sort, in the order the function takes them.
-/
def existsH [Binder φ] (binders : List (String × Srt)) (body : φ) : Env Term := do
  let (bvs, body) ← Binder.bindAll binders body
  mkQuant .EXISTS bvs body

/-! ## The view of a quantifier

Written by hand, as the quantifiers are: a bound variable is not something a specification
describes. `forall` and `exists` are Lean keywords, hence the primes.
-/

/-- A quantified formula, taken apart one level, sort-erased. -/
protected inductive _root_.Cvc.Untyped.View.Quant where
  /-- `∀ x₁ … xₙ, body`, with cvc5's instantiation patterns if it has any. -/
  | forall' (vars : BVars) (body : Term) (patterns : Option Term)
  /-- `∃ x₁ … xₙ, body`, with cvc5's instantiation patterns if it has any. -/
  | exists' (vars : BVars) (body : Term) (patterns : Option Term)

/-- Takes a term apart one level, if it is a quantified formula. -/
def _root_.Cvc.Untyped.View.Quant.of? (t : Term) : Option View.Quant :=
  match t.getKind?, t.getKids.toList with
  | some .FORALL, vars :: body :: rest => some (.forall' (vars.getKids.map asBVar) body rest.head?)
  | some .EXISTS, vars :: body :: rest => some (.exists' (vars.getKids.map asBVar) body rest.head?)
  | _, _ => none

register_untyped_view% Cvc.Untyped.View.Quant [forall' FORALL, exists' EXISTS]

end

end Cvc.Untyped.Term



namespace Cvc

public meta section

open Lean

/-! ## `smt!`

`smt! ∀ (x y : s) (b : t), body` and `smt! ∃ …` are Lean's own quantifier syntax, binders in
parentheses as `fun` takes them (`smtQuantBinder`, declared in `Cvc.Ext`). What follows the colon
depends on the layer: here it is a Lean type (`Int`) or a `Srt` value (`int`), as wherever the
sort-erased DSL takes a sort; typed, it is the Lean type the variable's index is, and only that.

The body extends as far right as it can, as in Lean, so a quantifier in argument position needs
parentheses. Expansion goes through `forallH`/`existsH`, binding each variable under the name the
writer gave it, which is also the name cvc5 prints.
-/

/-- Universal quantification. -/
syntax:lead (name := smtForall) "∀ " (ppSpace smtQuantBinder)+ ", " smtTerm : smtTerm

/-- Existential quantification. -/
syntax:lead (name := smtExists) "∃ " (ppSpace smtQuantBinder)+ ", " smtTerm : smtTerm

namespace Ext

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
