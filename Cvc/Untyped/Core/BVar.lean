/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core.Value
public meta import Cvc.Ext

import all Cvc.Basic.Env
import all Cvc.Srt
import all Cvc.Untyped.Core.Defs



namespace Cvc.Untyped public section variable [Ω]



/-- A bound variable. -/
def BVar := Term
deriving BEq, Ord, Hashable, Inhabited

/-- An array of bound variables. -/
abbrev BVars := Array BVar

/-- A term as the bound variable it is. Unchecked: for a view, which has read the term's kind. -/
def Term.asBVar (t : Term) : BVar := t

namespace BVar

/-- A bound variable of the given sort.

Only meaningful under a binder: the bound variables of a definition's body, or of a quantifier,
lambda or witness. Each call produces a fresh variable even for the same name and sort.
-/
def mk (srt : Srt) (name : String) : Env BVar := runUnsafe fun tm => tm.mkVar srt.toUnsafe name

/-- Same as `mk` but from a lean type instead of an `Srt`. -/
def mkAs (α : Type) [ToTyp α] (name : String) : Env BVar := do mk (← Srt.of α) name

/-- Turns itself into a term. -/
def toTerm : (bv : BVar) → Term := id

/-- Creates a lambda from a bound variables and a body. -/
def lambda (bv : BVar) (body : Term) : Env Term := runUnsafe fun tm => do
  let bvs ← tm.mkTerm .VARIABLE_LIST #[bv]
  tm.mkTerm .LAMBDA #[bvs, body]

instance : Coe BVar Term := ⟨toTerm⟩

instance : ToString BVar := ⟨toString ∘ toTerm⟩

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

@[inherit_doc BVar.mkAs]
def mkBVarAs (α : Type) [ToTyp α] (name : String) : Env BVar := BVar.mkAs α name

@[inherit_doc BVars.lambda]
def lambda (bvs : BVars) (body : Term) : Env Term := bvs.lambda body

@[inherit_doc BVar.lambda]
def lambda1 (bv : BVar) (body : Term) : Env Term := bv.lambda body



/-! ## Binding through Lean functions

`Binder φ` says that `φ` is the type of a binder's body written as a Lean function: one `Term`
argument per bound variable, ending in `Env Term`. A lambda (`lambdaH`) and a quantifier
(`forallH`, `existsH`) both take one. There is no instance for a bare `Env Term`, so a body binding
no variable does not typecheck.

Sort-erased, a variable's sort cannot come from its type, so each is given beside its name, in
order. How many are given is a runtime fact, checked against the function's arity before any
variable is made.
-/

/-- `φ` is a binder's body taking one `Term` per bound variable. -/
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
def Binder.bindAll [B : Binder φ] (binders : List (String × Srt)) (body : φ)
: Env (BVars × Term) := do
  if binders.length != B.arity then
    let plural (n : Nat) (what : String) := s!"{n} {what}{if n == 1 then "" else "s"}"
    throwUser s!"the body binds {plural B.arity "variable"}, but {
      plural binders.length "binder"} {if binders.length == 1 then "was" else "were"} given"
  B.bind binders body

/-- A lambda whose body is written as a Lean function of its variables.

`binders` names each variable and gives its sort, in the order the function takes them:

```lean
Term.lambdaH [("x", int), ("y", int)] fun x y => Term.add x y
```
-/
def lambdaH [Binder φ] (binders : List (String × Srt)) (body : φ) : Env Term := do
  let (bvs, body) ← Binder.bindAll binders body
  bvs.lambda body

end Term

end

end Cvc.Untyped



/-! ## `smt! fun`

The syntax is declared in `Cvc.Ext`, beside the other forms that mention no theory; this is the
sort-erased expansion, through `Term.lambdaH`. A binder's sort is a Lean type (`Int`) or a `Srt`
value (`int`), as wherever the sort-erased DSL takes a sort.
-/

namespace Cvc.Ext

public meta section

open Lean

@[inherit_doc Cvc.Ext.expandSmt]
macro_rules
  | `(smtExpand% $l $t:smtTerm) => do
    let layer := Layer.ofIdent l
    unless layer == Layer.untyped do Macro.throwUnsupported
    let stx := t.raw
    unless stx.getKind == ``Cvc.smtFun do Macro.throwUnsupported
    let binders := quantBinders stx[1]
    let body ← deferSmt layer stx[3]
    let ids := binders.map (·.1)
    let tys ← binders.mapM fun _ => `($(layer.name `Term))
    -- a sort is a Lean type or a `Srt`, either way an `Env Srt` to bind first
    let srts ← binders.mapM fun (_, sort) => `(srtOf% ($sort))
    bindArgs srts (binder := "smtSrt") fun srtIds => do
      let names ← (binders.zip srtIds).mapM fun ((id, _), srt) => `(($(quantName id), $srt))
      `($(layer.op `lambdaH) [$names,*] (fun $[($ids : $tys)]* => $body))

end

end Cvc.Ext
