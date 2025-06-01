/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Defs



namespace Cvc



/-! # Individual symbol representation -/



structure Symbol (β α : Type) : Type where
  name : String
  get : β

namespace Symbol

class Getter (α β : Type) : Type where
  getInner : α → β

@[default_instance]
instance : Getter (Symbol β α) β := ⟨get⟩

protected abbrev Ident (α : Type) := Symbol String α
protected abbrev Term (α : Type) := Symbol (Term α) α
instance : Coe (Symbol.Term α) (Term α) := ⟨get⟩
protected abbrev Val (α : Type) [Term.ToVal α] := Symbol (getValType α) α

protected abbrev Repr :=
  (α : Type) → [Term.ToVal α] → Type

namespace Repr
protected abbrev Ident : Symbol.Repr := fun _ _ => String
protected abbrev Term : Symbol.Repr := (Term ·)
protected abbrev Val : Symbol.Repr := getValType
end Repr

end Symbol



abbrev ESymbol (R : Symbol.Repr := .Ident) :=
  (α : Type) ×' (inst : Term.ToVal α) × Symbol (@R α inst) α

namespace ESymbol

protected abbrev Ident := ESymbol
protected abbrev Term := ESymbol Symbol.Repr.Term
protected abbrev Val := ESymbol Symbol.Repr.Val
end ESymbol



namespace Symbol

def erase [Val : Term.ToVal α] {R : Symbol.Repr} (sym : Symbol (R α) α) : ESymbol R :=
  ⟨α, Val, sym⟩

section variable [Monad m] (sym : Symbol β α)

def mapM (f : β → m γ) : m (Symbol γ α) := do
  let val ← f sym.get
  return {sym with get := val}

def map (f : β → γ) : Symbol γ α := sym.mapM (m := Id) f

end



def mkIdent (name : String) : Symbol.Ident α := mk name name

def mkTerm : String → Term α → Symbol.Term α := mk

def mkVal [Val : Term.ToVal α] : String → Val → Symbol.Val α := mk


section ident variable (sIdent : Symbol.Ident α)

def declare [Srt.Bij α] : Smt (Symbol.Term α) := do
  let term ← Smt.declare' sIdent.name
  return ⟨sIdent.name, term⟩

namespace Ident
abbrev mk := @Symbol.mkIdent
protected def toString : String := sIdent.name
instance : ToString (Symbol.Ident α) := ⟨name⟩
end Ident

end ident



section term

def assert (sTerm : Symbol.Term Bool) : Smt Unit :=
  Smt.assert sTerm.get

/-- Retrieves the value of some symbol in a *sat* context. -/
def getValUsing (Val : Term.ToVal α) (sTerm : Symbol.Term α) : Smt.Sat (Symbol.Val α) := do
  let val ← Smt.getVal sTerm.get
  return ⟨sTerm.name, val⟩

@[inherit_doc getValUsing]
def getVal [Val : Term.ToVal α] (sTerm : Symbol.Term α) : Smt.Sat (Symbol.Val α) :=
  getValUsing Val sTerm

end term

end Symbol
