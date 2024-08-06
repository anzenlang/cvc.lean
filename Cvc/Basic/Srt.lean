/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Defs



/-! # Sort -/
namespace Cvc.Srt

protected opaque AsSort (_ : Srt) : Type u := PUnit

instance : CoeSort Srt (Type u) where
  coe sort := Srt.AsSort sort

instance (sort : Srt) : ToSrt sort.AsSort := ⟨return sort⟩



/-! ## Constructors -/

variable [Monad m]

@[inherit_doc cvc5.TermManager.getBooleanSort]
protected def bool : Term.ManagerT m Srt :=
  cvc5.TermManager.getBooleanSort <$> get

instance : ToSrt Bool := ⟨Srt.bool⟩

@[inherit_doc cvc5.TermManager.getIntegerSort]
protected def int : Term.ManagerT m Srt :=
  cvc5.TermManager.getIntegerSort <$> get

instance : ToSrt Int := ⟨Srt.int⟩
instance : ToSrt Nat := ⟨Srt.int⟩

@[inherit_doc cvc5.TermManager.getRealSort]
protected def real : Term.ManagerT m Srt :=
  cvc5.TermManager.getRealSort <$> get

instance : ToSrt Lean.Rat := ⟨Srt.real⟩

@[inherit_doc cvc5.TermManager.getStringSort]
protected def string : Term.ManagerT m Srt :=
  cvc5.TermManager.getStringSort <$> get

instance : ToSrt String := ⟨Srt.string⟩

@[inherit_doc cvc5.TermManager.mkArraySort]
protected def array
  (idx elm : Type u)
  [I : ToSrt idx] [E : ToSrt elm]
: Term.ManagerT m Srt := do
  let (idx, elm) := (← I.srt, ← E.srt)
  (cvc5.TermManager.mkArraySort · idx elm) <$> get

instance [ToSrt α] : ToSrt (Array α) := ⟨Srt.array Nat α⟩

@[inherit_doc cvc5.TermManager.mkBitVectorSort]
protected def bitVec (size : Nat) : Term.ManagerT m Srt :=
  (cvc5.TermManager.mkBitVectorSort · size) <$> get

instance : ToSrt (BitVec size) := ⟨Srt.bitVec size⟩

@[inherit_doc cvc5.TermManager.mkFloatingPointSort]
protected def float (exp sig : Nat) : Term.ManagerT m Srt :=
  (cvc5.TermManager.mkFloatingPointSort · exp sig) <$> get

@[inherit_doc cvc5.TermManager.mkFunctionSort]
protected def function
  (sorts : Array Srt)
  (codomain : Type u) [I : ToSrt codomain]
: Term.ManagerT m Srt := do
  let codomain ← I.srt
  (cvc5.TermManager.mkFunctionSort · sorts codomain) <$> get
