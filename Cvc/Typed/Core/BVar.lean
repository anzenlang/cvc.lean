/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core.BVar
public import Cvc.Typed.Core.Value
public meta import Cvc.Ext

-- for the delaborator below, which reduces a signature before showing it
public meta import Lean.Meta.Basic
public meta import Lean.PrettyPrinter.Delaborator.Basic

import all Cvc.Basic.Env
import all Cvc.Untyped.Core.BVar
-- `import all` and not a plain `import`: `BVar α` is `Term α` is `Untyped.Term`, and that chain is
-- what lets a typed bound variable be built by the sort-erased constructor
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs



namespace Cvc.Typed public section variable [Ω]



/-- A bound variable. -/
def BVar (α : Type) := Term α

/-- A term as the bound variable it is. Unchecked: for a view, which has read the term's kind. -/
def Term.asBVar (t : Term α) : BVar α := t

namespace BVar


/-- A bound variable of the sort `α` describes.

Only meaningful under a binder: the bound variables of a definition's body, or of a quantifier,
lambda or witness. Each call produces a fresh variable even for the same name and sort.
-/
def mk [ToTyp α] (name : String) : Env (BVar α) := do Untyped.Term.mkBVar (← Srt.of α) name

@[inherit_doc mk]
def mkAs (α : Type) : [ToTyp α] → (name : String) → Env (BVar α) := mk

/-- Turns itself into a term. -/
def toTerm : (bv : BVar α) → Term α := id

/-- Relaxes it to the sort-erased bound variable it is, for free. -/
def relax : (bv : BVar α) → Untyped.BVar := id

@[inherit_doc Untyped.BVar.lambda]
def lambda : (bv : BVar α) → (body : Term β) → Env (Term (α → β)) := Untyped.BVar.lambda

instance : Coe (BVar α) (Term α) := ⟨toTerm⟩

end BVar

/-- A typed-list of `BVar`s. -/
abbrev BVars := List ((α : Type) × ToTyp α × BVar α)

namespace BVars

/-- An empty list of bound variables. -/
abbrev empty : BVars := []

/-- Pushes a bound variable. -/
abbrev push [ToTyp α] (bv : BVar α) (bvs : BVars) : BVars :=
  ⟨α, inferInstance, bv⟩ :: bvs

/-- Signature of the lambda with codomain `β` associated to these bound variables. -/
abbrev signatureTo (β : Type) : (bvs : BVars) → Type
  | [] => β
  | ⟨α, _, _⟩ :: bvs => signatureTo (α → β) bvs

/-! A signature is *computed*, so a term indexed by one is inferred at the application rather than
at the arrow it denotes: `Grammar (BVars.signatureTo Int (BVars.push y (BVars.push x [])))` where
`Grammar (Int → Int → Int)` is what a reader wants. Being an `abbrev` does not help — reducibility
governs unification, not printing, and Lean shows a type as inferred rather than in normal form.

The delaborator below closes that gap for every abbrev whose index goes through `signatureTo` —
`lambda`, `Solver.defineFun`, `synthAnyFun`, a `Grammar`'s own index.
-/

open Lean PrettyPrinter Delaborator SubExpr in
/-- Shows a signature in the form it computes to.

Three details are load-bearing. The first `guard` stops a signature that *cannot* reduce — one over
a variable spine — from delaborating to itself and re-entering this delaborator forever; failing it
hands the expression back to the default printer. It compares the whole expression rather than its
head, which is what lets a partly concrete spine show how far it got: `push x bvs` reduces to
`signatureTo (Int → Int) bvs`, saying that `x` is already accounted for.

The second guard is about *when* reducing is an improvement. Mid-elaboration — a hover inside a
`do` block, before the pushed variables' types are solved — the reduced form is `?m → ?m → Int`,
which says less than the application it came from, that one naming `x` and `y`. So the reduction is
shown only once it has no metavariables left in it.
-/
@[delab app.Cvc.Typed.BVars.signatureTo]
public meta def delabSignatureTo : Delab := do
  let e ← getExpr
  let e' ← instantiateMVars (← Meta.whnf e)
  guard <| e' != e
  -- a signature whose variables are not yet elaborated reduces to `?m → ?m → Int`, which says
  -- *less* than the application it came from: that at least names the variables. So the reduced
  -- form is shown only once it has something to say
  guard <| !e'.hasExprMVar
  withTheReader SubExpr (fun c => { c with expr := e' }) delab

/-- Relaxes them to sort-erased bound variables, keeping the order. -/
def relax (bvs : BVars) : Untyped.BVars :=
  bvs.foldr (init := Array.mkEmpty bvs.length) fun ⟨_, _, bv⟩ acc => acc.push bv.relax

@[inherit_doc Untyped.BVars.lambda]
def lambda (bv : BVars) : (body : Term β) → Env (Term (bv.signatureTo β)) := bv.relax.lambda

end BVars


namespace Term

@[inherit_doc BVar.mk]
abbrev mkBVar := @BVar.mk

@[inherit_doc BVar.mkAs]
abbrev mkBVarAs := @BVar.mkAs

@[inherit_doc BVars.lambda]
abbrev lambda := @BVars.lambda

@[inherit_doc BVar.lambda]
abbrev lambda1 := @BVar.lambda



/-! ## Binding through Lean functions

`LambdaBinder φ σ` says that `φ` is the type of a lambda's body written as a Lean function, one
`Term α` argument per bound variable and ending in `Env (Term β)`, and that `σ` is the sort the
lambda has: the arguments' types arrowed onto `β`. The variable's sort is `α`'s. There is no
instance for a bare `Env (Term β)`, so a body binding no variable does not typecheck.

The arguments' types are what the sorts come from, so they must be known: write
`fun (x : Term Int) => …` rather than `fun x => …` when nothing else in the body pins them down.
-/

/-- `φ` is a lambda's body taking one `Term α` per bound variable, the lambda being of sort `σ`. -/
class LambdaBinder (φ : Type) (σ : outParam Type) where
  /-- Creates one bound variable per argument of `f` and applies `f` to them.

  The `i`-th variable is named `names[i]`, or `x{i}` when `names` has no such element.
  -/
  bind : List String → Nat → φ → Env (Untyped.BVars × Untyped.Term)

/-- The name of the `i`-th bound variable: `names[i]`, or `x{i}` when there is none. -/
def LambdaBinder.nameAt (names : List String) (i : Nat) : String := names[i]?.getD s!"x{i}"

/-- The binder for a body taking the last bound variable. -/
instance [ToTyp α] : LambdaBinder (Term α → Env (Term β)) (α → β) where
  bind names i f := do
    let bv ← BVar.mk (α := α) (LambdaBinder.nameAt names i)
    return (#[bv.relax], (← f bv.toTerm).relax)

/-- The binder for a body taking a bound variable and more. -/
instance [ToTyp α] [LambdaBinder ψ σ] : LambdaBinder (Term α → ψ) (α → σ) where
  bind names i f := do
    let bv ← BVar.mk (α := α) (LambdaBinder.nameAt names i)
    let (bvs, body) ← LambdaBinder.bind names (i + 1) (f bv.toTerm)
    return (#[bv.relax] ++ bvs, body)

/-- A lambda whose body is written as a Lean function of its variables.

Its sort is the function's arguments' indices arrowed onto the body's:

```lean
Term.lambdaH fun (x y : Term Int) => smt! x + y   -- Term (Int → Int → Int)
```

`names` names the variables in the order the function takes them; a variable without one is
named `x{i}`, after its position.
-/
def lambdaH [LambdaBinder φ σ] (body : φ) (names : List String := []) : Env (Term σ) := do
  let (bvs, body) ← LambdaBinder.bind names 0 body
  bvs.lambda body

end Term

end

end Cvc.Typed



/-! ## `smt! fun`

The syntax is declared in `Cvc.Ext`; this is the typed expansion, through `Term.lambdaH`. A
binder's type is the Lean type of the variable's index, so `smt! fun (x : Int) => x + 1` is a
`Term (Int → Int)`.
-/

namespace Cvc.Ext

public meta section

open Lean

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.typed do Macro.throwUnsupported
    let stx := t.raw
    unless stx.getKind == ``Cvc.smtFun do Macro.throwUnsupported
    let binders := quantBinders stx[1]
    let body ← deferSmt layer stx[3]
    let ids := binders.map (·.1)
    let tys ← binders.mapM fun (_, ty) => `($(layer.name `Term) $ty)
    let names := binders.map (quantName ·.1)
    `($(layer.op `lambdaH) (fun $[($ids : $tys)]* => $body) (names := [$names,*]))

end

end Cvc.Ext
