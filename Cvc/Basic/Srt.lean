/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Defs



/-! # Sort -/
namespace Cvc.Srt

def ofCvc5 : cvc5.Sort → Srt :=
  ULift.up

def toCvc5 : Srt → cvc5.Sort :=
  ULift.down

protected def toString : Srt → String :=
  cvc5.Sort.toString ∘ toCvc5

instance : ToString Srt :=
  ⟨Srt.toString⟩

protected opaque AsSort (_ : Srt) : Type u := PUnit

instance : CoeSort Srt (Type u) where
  coe sort := Srt.AsSort sort

instance (sort : Srt) : ToSrt sort.AsSort := ⟨return sort⟩



/-! ## Constructors -/

variable [Monad m]

def srtLift (code : cvc5.TermManager → cvc5.Sort) : Term.Manager → Srt :=
  ofCvc5 ∘ code ∘ ULift.down

def srtLift?
  (code : cvc5.TermManager → Except cvc5.Error cvc5.Sort)
  (tm : Term.Manager)
: Except Error Srt :=
  match code tm.down with
  | .ok sort => .ok <| ofCvc5 sort
  | .error e => .error <| Error.ofCvc5 e

@[inherit_doc cvc5.TermManager.getBooleanSort]
protected def bool : Term.ManagerM Srt :=
  (srtLift cvc5.TermManager.getBooleanSort) <$> get

instance : ToSrt Bool := ⟨Srt.bool⟩

@[inherit_doc cvc5.TermManager.getIntegerSort]
protected def int : Term.ManagerM Srt :=
  (srtLift cvc5.TermManager.getIntegerSort) <$> get

instance : ToSrt Int := ⟨Srt.int⟩
instance : ToSrt Nat := ⟨Srt.int⟩

@[inherit_doc cvc5.TermManager.getRealSort]
protected def real : Term.ManagerM Srt :=
  (srtLift cvc5.TermManager.getRealSort) <$> get

instance : ToSrt Rat := ⟨Srt.real⟩

@[inherit_doc cvc5.TermManager.getStringSort]
protected def string : Term.ManagerM Srt :=
  (srtLift cvc5.TermManager.getStringSort) <$> get

instance : ToSrt String := ⟨Srt.string⟩

@[inherit_doc cvc5.TermManager.mkArraySort]
protected def array
  (idx elm : Type u)
  [I : ToSrt idx] [E : ToSrt elm]
: Term.ManagerM Srt := do
  let (idx, elm) := (← I.srt, ← E.srt)
  srtLift? (cvc5.TermManager.mkArraySort · idx.toCvc5 elm.toCvc5) (← get)

instance [ToSrt α] : ToSrt (Array α) := ⟨Srt.array Nat α⟩

@[inherit_doc cvc5.TermManager.mkBitVectorSort]
protected def bitVec (size : UInt32) (valid : 0 < size := by simp) : Term.ManagerM Srt :=
  return srtLift (cvc5.TermManager.mkBitVectorSort · size valid) (← get)

instance {size : UInt32} (valid : 0 < size := by omega) : ToSrt (BitVec size.toNat) :=
  ⟨Srt.bitVec size valid⟩

@[inherit_doc cvc5.TermManager.mkFloatingPointSort]
protected def float
  (exp sig : UInt32)
  (valid_exp : 1 < exp)
  (valid_sig : 1 < sig)
: Term.ManagerM Srt := do
  srtLift? (cvc5.TermManager.mkFloatingPointSort · exp sig valid_exp valid_sig) (← get)

@[inherit_doc cvc5.TermManager.mkFunctionSort]
protected def function
  (sorts : Array Srt.{u})
  (codomain : Type u) [I : ToSrt.{u} codomain]
: Term.ManagerM Srt := do
  let sorts := sorts.map toCvc5
  let codomain ← I.srt
  srtLift? (cvc5.TermManager.mkFunctionSort · sorts codomain.toCvc5) (← get)

protected def cvc5Signature (self : Srt) : Term.ManagerM (Array cvc5.Sort × cvc5.Sort) := do
  let self! := self.toCvc5
  if self!.isFunction then
    let domain ← self!.getFunctionDomainSorts
    let codomain ← self!.getFunctionCodomainSort
    return (domain, codomain)
  else
    return (#[], self!)


protected def fn
  (α : Type) (β : Type)
  [A : ToSrt α] [B : ToSrt β]
: Term.ManagerM Srt := do
  let a ← A.srt
  let b ← B.srt
  let (domain, codomain) ← b.cvc5Signature
  let domain := #[a.toCvc5] ++ domain
  srtLift? (cvc5.TermManager.mkFunctionSort · domain codomain) (← get)

instance [ToSrt α] [ToSrt β] : ToSrt (α → β) :=
  ⟨Srt.fn α β⟩
