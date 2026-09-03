/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.BVar
public import Cvc.Typed.Core.Bool

-- for the delaborator below, which reduces a signature before showing it
public meta import Lean.Meta.Basic
public meta import Lean.PrettyPrinter.Delaborator.Basic

import all Cvc.Basic.Env
import all Cvc.Untyped.BVar
-- `import all` and not a plain `import`: `BVar α` is `Term α` is `Untyped.Term`, and that chain is
-- what lets a typed bound variable be built by the sort-erased constructor
import all Cvc.Untyped.Core.Defs
import all Cvc.Typed.Core.Defs



namespace Cvc.Typed public section variable [Ω]



/-- A bound variable. -/
def BVar (α : Type) := Term α

namespace BVar


/-- A bound variable of the sort `α` describes.

Only meaningful under a binder: the bound variables of a definition's body, or of a quantifier,
lambda or witness. Each call produces a fresh variable even for the same name and sort.
-/
def mk [ToTyp α] (name : String) : Env (BVar α) := do Untyped.Term.mkBVar (← Srt.of α) name

@[inherit_doc mk]
def mk' (α : Type) : [ToTyp α] → (name : String) → Env (BVar α) := mk

/-- Turns itself into a term. -/
def toTerm : (bv : BVar α) → Term α := id

/-- Erases its type. -/
def erase : (bv : BVar α) → Untyped.BVar := id

@[inherit_doc Untyped.BVar.lambda]
def lambda : (bv : BVar α) → (body : Term β) → Env (Term (α → β)) := Untyped.BVar.lambda

instance : Coe (BVar α) (Term α) := ⟨toTerm⟩

end BVar

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

/-- Erases the types of the bound variables. -/
def erase (bvs : BVars) : Untyped.BVars :=
  bvs.foldr (init := Array.mkEmpty bvs.length) fun ⟨_, _, bv⟩ acc => acc.push bv.erase

@[inherit_doc Untyped.BVars.lambda]
def lambda (bv : BVars) : (body : Term β) → Env (Term (bv.signatureTo β)) := bv.erase.lambda

end BVars


namespace Term

@[inherit_doc BVar.mk]
abbrev mkBVar := @BVar.mk

@[inherit_doc BVar.mk']
abbrev mkBVar' := @BVar.mk'

@[inherit_doc BVars.lambda]
abbrev lambda := @BVars.lambda

@[inherit_doc BVar.lambda]
abbrev lambda1 := @BVar.lambda

end Term
