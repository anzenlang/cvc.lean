/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core.Bool

import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs



namespace Cvc.Untyped public section variable [Ω]



/-- A bound variable. -/
def BVar := Term

/-- An array of bound variables. -/
abbrev BVars := Array BVar

namespace BVar

/-- A bound variable of the given sort.

Only meaningful under a binder: the bound variables of a definition's body, or of a quantifier,
lambda or witness. Each call produces a fresh variable even for the same name and sort.
-/
def mk (srt : Srt) (name : String) : Env BVar := runUnsafe fun tm => tm.mkVar srt.toUnsafe name

/-- Turns itself into a term. -/
def toTerm : (bv : BVar) → Term := id

/-- Creates a lambda from a bound variables and a body. -/
def lambda (bv : BVar) (body : Term) : Env Term := runUnsafe fun tm => do
  let bvs ← tm.mkTerm .VARIABLE_LIST #[bv]
  tm.mkTerm .LAMBDA #[bvs, body]

instance : Coe BVar Term := ⟨toTerm⟩

end BVar

namespace BVars

/-- Turns itself into a *variable list* term, used to create `Term.lambda`s. -/
def toTerm (bvs : BVars) : Env Term := runUnsafe fun tm => tm.mkTerm .VARIABLE_LIST bvs

/-- Creates a lambda from some bound variables and a body. -/
def lambda (bvs : BVars) (body : Term) : Env Term := do
  let bvs ← bvs.toTerm
  runUnsafe fun tm => tm.mkTerm .LAMBDA #[bvs, body]

end BVars

namespace Term

@[inherit_doc BVar.mk]
def mkBVar (srt : Srt) (name : String) : Env BVar := BVar.mk srt name

@[inherit_doc BVars.lambda]
def lambda (bvs : BVars) (body : Term) : Env Term := bvs.lambda body

@[inherit_doc BVar.lambda]
def lambda1 (bv : BVar) (body : Term) : Env Term := bv.lambda body

end Term
