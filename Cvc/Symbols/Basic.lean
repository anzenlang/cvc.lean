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
-- `CoeSort` because `Coe` can't infer `α` from `String`
instance : CoeSort (Symbol.Ident α) String := ⟨get⟩
protected abbrev Term (α : Type) := Symbol (Term α) α
instance : Coe (Symbol.Term α) (Term α) := ⟨get⟩
protected abbrev Value (α : Type) := Symbol (Value α) α
instance : Coe (Symbol.Value α) (Value α) := ⟨get⟩

protected abbrev Repr :=
  (α : Type) → [IsSrt α] → Type

namespace Repr
protected abbrev Ident : Symbol.Repr := fun _ _ => String
protected abbrev Term : Symbol.Repr := (Term ·)
protected abbrev Value : Symbol.Repr := (Value ·)
end Repr



section variable [Monad m] (sym : Symbol β α)

def mapM (f : β → m γ) : m (Symbol γ α) := do
  let val ← f sym.get
  return {sym with get := val}

def map (f : β → γ) : Symbol γ α := sym.mapM (m := Id) f

end



def mkIdent (name : String) : Symbol.Ident α := mk name name
def mkIdent' (name : String) (α : Type) : Symbol.Ident α := mk name name

def mkTerm : String → Term α → Symbol.Term α := mk

def mkValue : String → Value α → Symbol.Value α := mk

-- def mkVal [Val : Term.ToVal α] : String → Val → Symbol.Val α := mk


section ident

def declare (ident : Symbol.Ident α) [IsSrt α] : Smt (Symbol.Term α) := do
  let term ← Smt.declare' ident.name
  return ⟨ident.name, term⟩

namespace Ident
abbrev mk := @Symbol.mkIdent
abbrev mk' := @Symbol.mkIdent'

/-- String representation. -/
protected def toString (ident : Symbol.Ident α) : String := ident.name

instance : ToString (Symbol.Ident α) := ⟨Ident.toString⟩
end Ident

end ident



section term

/-- Asserts a Boolean term-symbol.

# TODO

- Is this function actually useful?
-/
def assert (sTerm : Symbol.Term Bool) : Smt Unit :=
  Smt.assert sTerm.get

/-- Retrieves tho symbol-value of a symbol-term in a `Sat` context. -/
def getValue [IsSrt α] (term : Symbol.Term α) : Smt.Sat (Symbol.Value α) :=
  Symbol.mkValue term.name <$> term.get.getValue

namespace Term
/-- String representation. -/
protected def toString (term : Symbol.Term α) : String := toString term.get

instance : ToString (Symbol.Term α) := ⟨Term.toString⟩
end Term

end term



section value

namespace Value
/-- String representation. -/
protected def toString (value : Symbol.Value α) : String := toString value.get

instance : ToString (Symbol.Value α) := ⟨Value.toString⟩
end Value

end value

end Symbol
