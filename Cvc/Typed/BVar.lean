/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.BVar
public import Cvc.Typed.Core.Bool

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

/-- Pushes a bound variable. -/
abbrev push [ToTyp α] (bv : BVar α) (bvs : BVars) : BVars :=
  ⟨α, inferInstance, bv⟩ :: bvs

/-- Signature of the lambda with codomain `β` associated to these bound variables. -/
abbrev signatureTo (β : Type) : (bvs : BVars) → Type
  | [] => β
  | ⟨α, _, _⟩ :: bvs => signatureTo (α → β) bvs

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
