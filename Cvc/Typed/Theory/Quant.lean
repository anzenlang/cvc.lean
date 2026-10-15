/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.BVar
public import Cvc.Untyped.Theory.Quant
public meta import Cvc.Untyped.Theory.Quant
public meta import Cvc.Ext

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs
import all Cvc.Untyped.BVar
import all Cvc.Typed.BVar



/-! # Quantifiers, typed

A quantified formula is a `Term Bool` whatever it binds, and so is its body. Two spellings are
offered, as sort-erased.

- `mkForall`/`mkExists` take the bound variables as a `BVars` spine, as `BVars.lambda` does.
- `forallH`/`existsH` take the body as a Lean function of the variables. Here each variable's sort
  comes from the type of its argument, so a quantifier reads like a Lean one:

  ```lean
  Term.forallH fun (x y : Term Int) => smt! x + y = y + x
  ```

A quantifier binds at least one variable: an empty spine is ruled out by an autoparam, and a body
taking no argument has no `Binder` instance.
-/
namespace Cvc.Typed.Term public section variable [Ω]

open Cvc renaming Untyped.Term → T

/-- Universal quantification of `body` over `bvs`. -/
def mkForall (bvs : BVars) (body : Term Bool)
  (_nonEmpty : bvs ≠ [] := by
    (try simp) <;> fail "failed to prove a quantifier binds at least one variable")
: Env (Term Bool) :=
  T.mkForall bvs.erase body (by cases bvs <;> simp_all [BVars.erase])

/-- Existential quantification of `body` over `bvs`. -/
def mkExists (bvs : BVars) (body : Term Bool)
  (_nonEmpty : bvs ≠ [] := by
    (try simp) <;> fail "failed to prove a quantifier binds at least one variable")
: Env (Term Bool) :=
  T.mkExists bvs.erase body (by cases bvs <;> simp_all [BVars.erase])



/-! ## Binding through Lean functions

`Binder φ` says that `φ` is the type of a quantifier's body written as a Lean function: one
`Term α` argument per bound variable, ending in `Env (Term Bool)`. The variable's sort is `α`'s.
There is no instance for a bare `Env (Term Bool)`, so a body binding no variable does not
typecheck.

The arguments' types are what the sorts come from, so they must be known: write
`fun (x : Term Int) => …` rather than `fun x => …` when nothing else in the body pins them down.
-/

/-- `φ` is a quantifier body taking one `Term α` per bound variable. -/
class Binder (φ : Type) where
  /-- Creates one bound variable per argument of `f` and applies `f` to them.

  The `i`-th variable is named `names[i]`, or `x{i}` when `names` has no such element.
  -/
  bind : List String → Nat → φ → Env (Untyped.BVars × Term Bool)

/-- The name of the `i`-th bound variable: `names[i]`, or `x{i}` when there is none. -/
def Binder.nameAt (names : List String) (i : Nat) : String := names[i]?.getD s!"x{i}"

/-- The binder for a body taking the last bound variable. -/
instance [ToTyp α] : Binder (Term α → Env (Term Bool)) where
  bind names i f := do
    let bv ← BVar.mk (α := α) (Binder.nameAt names i)
    return (#[bv.erase], ← f bv.toTerm)

/-- The binder for a body taking a bound variable and more. -/
instance [ToTyp α] [Binder ψ] : Binder (Term α → ψ) where
  bind names i f := do
    let bv ← BVar.mk (α := α) (Binder.nameAt names i)
    let (bvs, body) ← Binder.bind names (i + 1) (f bv.toTerm)
    return (#[bv.erase] ++ bvs, body)

/-- Universal quantification of a body written as a Lean function of its variables.

`names` names the variables in the order the function takes them; a variable without one is
named `x{i}`, after its position.
-/
def forallH [Binder φ] (body : φ) (names : List String := []) : Env (Term Bool) := do
  let (bvs, body) ← Binder.bind names 0 body
  if h : 0 < bvs.size then T.mkForall bvs body h
  else throwUnreachable "a binder created no variable"

/-- Existential quantification of a body written as a Lean function of its variables.

`names` names the variables in the order the function takes them; a variable without one is
named `x{i}`, after its position.
-/
def existsH [Binder φ] (body : φ) (names : List String := []) : Env (Term Bool) := do
  let (bvs, body) ← Binder.bind names 0 body
  if h : 0 < bvs.size then T.mkExists bvs body h
  else throwUnreachable "a binder created no variable"

end

end Cvc.Typed.Term



namespace Cvc.Ext

public meta section

open Lean

/-! ## `smt!`

The syntax is declared beside the sort-erased constructors; this is the typed expansion. A binder's
type is the Lean type of the variable's index, so `smt! ∀ (x : Int), x + 0 = x` binds a `Term Int`.
-/

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.typed do Macro.throwUnsupported
    let stx := t.raw
    let fn ← match stx.getKind with
      | ``smtForall => pure (layer.op `forallH)
      | ``smtExists => pure (layer.op `existsH)
      | _ => Macro.throwUnsupported
    let binders := quantBinders stx[1]
    let body ← deferSmt layer stx[3]
    let ids := binders.map (·.1)
    let tys ← binders.mapM fun (_, ty) => `($(layer.name `Term) $ty)
    let names := binders.map (quantName ·.1)
    `($fn (fun $[($ids : $tys)]* => $body) (names := [$names,*]))

end

end Cvc.Ext
