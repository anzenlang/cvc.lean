/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Srt



/-! # Terms -/
namespace Cvc.Term

-- @[inherit_doc cvc5.Term.toString]
protected def toString : Term → String :=
  cvc5.Term.toString ∘ Term.toCvc5

instance : ToString Term :=
  ⟨Term.toString⟩

def getSrt (t : Term) : Srt :=
  Srt.ofCvc5 t.toCvc5.getSort

/-! ### Constructors from `cvc5` -/

variable [Monad m]

def termLift (code : cvc5.TermManager → cvc5.Term) : Term.ManagerM Term := fun tm => do
  let res := code tm.toCvc5 |> ULift.up
  return (.ok res, tm)

def termLift?
  (code : cvc5.TermManager → Except cvc5.Error cvc5.Term)
: Term.ManagerM Term := fun tm => do
  match code tm.toCvc5 with
  | .ok res => return (.ok (Term.ofCvc5 res), tm)
  | .error e => return (.error (Error.ofCvc5 e), tm)

-- @[inherit_doc cvc5.TermManager.mkBoolean]
def mkBool (b : Bool) : ManagerM Term :=
  termLift? (cvc5.TermManager.mkBoolean · b)

instance : ToTerm Bool := ⟨mkBool⟩

-- @[inherit_doc cvc5.TermManager.mkInteger]
def mkInt (i : Int) : ManagerM Term :=
  termLift? (cvc5.TermManager.mkInteger · i)

instance : ToTerm Int := ⟨mkInt⟩

instance : ToTerm Nat := ⟨mkInt ∘ Int.ofNat⟩

@[inherit_doc cvc5.TermManager.mkTerm]
def mk (kind : Kind) (children : Array Term := #[]) : ManagerM Term :=
  termLift? (cvc5.TermManager.mkTerm · kind (children.map ULift.down))

-- @[inherit_doc cvc5.Proof.getResult]
def ofProof : Proof → Term :=
  Term.ofCvc5 ∘ cvc5.Proof.getResult



/-! ### Convenience term constructors -/

def mkIte (cnd thn els : Term) : ManagerM Term :=
  mk .ITE #[cnd, thn, els]

def mkEqN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .EQUAL terms

def mkEq (lhs rhs : Term) : ManagerM Term :=
  mkEqN #[lhs, rhs]

def mkDistinct (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .DISTINCT terms



def mkNot (term : Term) : ManagerM Term :=
  mk .NOT #[term]
/-- Alias for `mkNot`. -/
abbrev not := @mkNot

def mkAndN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .AND terms

def mkAnd (lhs rhs : Term) : ManagerM Term :=
  mkAndN #[lhs, rhs]
/-- Alias for `mkAnd`. -/
abbrev and := @mkAnd

def mkImpliesN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .IMPLIES terms

def mkImplies (lhs rhs : Term) : ManagerM Term :=
  mkImpliesN #[lhs, rhs]

def mkOrN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .OR terms

def mkOr (lhs rhs : Term) : ManagerM Term :=
  mkOrN #[lhs, rhs]
/-- Alias for `mkOr`. -/
abbrev or := @mkOr

def mkXorN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .XOR terms

def mkXor (lhs rhs : Term) : ManagerM Term :=
  mkXorN #[lhs, rhs]
/-- Alias for `mkXor`. -/
abbrev xor := @mkXor



def mkAddN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .ADD terms

def mkAdd (lhs rhs : Term) : ManagerM Term :=
  mkAddN #[lhs, rhs]
/-- Alias for `mkAdd`. -/
abbrev add := @mkAdd

def mkMultN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .MULT terms

def mkMult (lhs rhs : Term) : ManagerM Term :=
  mkMultN #[lhs, rhs]
/-- Alias for `mkMult`. -/
abbrev mult := @mkMult

def mkSubN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .SUB terms

def mkSub (lhs rhs : Term) : ManagerM Term :=
  mkSubN #[lhs, rhs]
/-- Alias for `mkSub`. -/
abbrev sub := @mkSub

def mkNeg (term : Term) : ManagerM Term :=
  mk .NEG #[term]
/-- Alias for `mkNeg`. -/
abbrev neg := @mkNeg

end Term
