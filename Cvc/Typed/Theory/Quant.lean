/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Core.BVar
public import Cvc.Gen.TypedView
public import Cvc.Typed.Core.View
public import Cvc.Untyped.Theory.Quant
public meta import Cvc.Untyped.Theory.Quant
public meta import Cvc.Ext

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs
import all Cvc.Untyped.Core.BVar
import all Cvc.Typed.Core.BVar



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



/-! ## Viewing a quantifier

Quantifiers are hand-written rather than specified, so their view is too. The variables' sorts are a
list of `Typ`s, as an application's arguments are, and the body mentions the variables: walking into
it meets them as the aggregate's `bvar` leaf.
-/

namespace Cvc.Typed public section variable [Ω]

/-- A binder's variables, each at the denotation of its sort, in order; never empty. -/
inductive View.Quant.Vars : List Typ → Type where
  /-- The last variable. -/
  | last (x : BVar τ.Denote) : View.Quant.Vars [τ]
  /-- One more variable, in front of the others. -/
  | cons (x : BVar τ.Denote) (rest : View.Quant.Vars τs) : View.Quant.Vars (τ :: τs)

namespace View.Quant.Vars

/-- The same variables as a `BVars` list, so that a viewed binder can be rebuilt.

`BVars` collects in reverse — the variable pushed last is the binder's last — so the spine is folded
from its head onto an accumulator.
-/
def toBVars (vars : Vars doms) : BVars := go vars []
where
  /-- Pushes the variables in order onto `acc`. -/
  go {ds : List Typ} : Vars ds → BVars → BVars
    | .last x, acc => BVars.push x acc
    | .cons x rest, acc => go rest (BVars.push x acc)

/-- A binder always has a variable, so its `BVars` are never empty: what `mkForall` asks for. -/
theorem toBVars_ne_nil (vars : Vars doms) : vars.toBVars ≠ [] := by
  suffices ∀ {ds} (v : Vars ds) acc, toBVars.go v acc ≠ [] from this vars []
  intro ds v
  induction v with
  | last x => simp [toBVars.go]
  | cons x rest ih => exact fun acc => ih _

/-- The variables as cvc5 prints them, `x : Int`. -/
def toStrings : Vars doms → List String
  | .last (τ := τ) x => [s!"{x.toTerm} : {τ}"]
  | .cons (τ := τ) x rest => s!"{x.toTerm} : {τ}" :: rest.toStrings

end View.Quant.Vars

/-- A quantified formula taken apart one level; always of sort `Bool`.

`forall` and `exists` are Lean keywords, hence the primes. The instantiation patterns stay
sort-erased, a pattern mixing sorts.
-/
protected inductive View.Quant : Typ → Type where
  /-- `∀ x₁ … xₙ, body`, with cvc5's instantiation patterns if it has any. -/
  | forall' (doms : List Typ) (vars : View.Quant.Vars doms) (body : Term Bool)
    (patterns : Option Untyped.Term) : View.Quant .bool
  /-- `∃ x₁ … xₙ, body`, with cvc5's instantiation patterns if it has any. -/
  | exists' (doms : List Typ) (vars : View.Quant.Vars doms) (body : Term Bool)
    (patterns : Option Untyped.Term) : View.Quant .bool

/-- Takes a term of sort `τ` apart one level, if it is a quantified formula whose variables' sorts a
`Typ` describes. -/
def View.Quant.of (τ : Typ) (t : Term τ.Denote) : Env (Option (View.Quant τ)) :=
  match τ, Untyped.View.Quant.of? t.erase with
  | .bool, some (.forall' vars body pats) => do
    let some ⟨doms, vars⟩ ← go vars.toList | return none
    return some (.forall' doms vars (View.reindex body) pats)
  | .bool, some (.exists' vars body pats) => do
    let some ⟨doms, vars⟩ ← go vars.toList | return none
    return some (.exists' doms vars (View.reindex body) pats)
  | _, _ => return none
where
  /-- The variables, with their sorts. -/
  go : List Untyped.BVar → Env (Option ((doms : List Typ) × View.Quant.Vars doms))
    | [] => return none
    | [x] => do
      let some σ ← View.typOf? x.toTerm | return none
      return some ⟨[σ], .last (View.reindex x.toTerm).asBVar⟩
    | x :: xs => do
      let some σ ← View.typOf? x.toTerm | return none
      let some ⟨σs, rest⟩ ← go xs | return none
      return some ⟨σ :: σs, .cons (View.reindex x.toTerm).asBVar rest⟩

register_typed_view% Cvc.Typed.View.Quant [forall' FORALL, exists' EXISTS]

end

end Cvc.Typed



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
