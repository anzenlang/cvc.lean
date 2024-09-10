/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Srt



namespace Cvc



/-- A bound variable. -/
structure BVar where
private ofTerm ::
  toTerm : Term



/-! # Terms -/
namespace Term

-- @[inherit_doc cvc5.Term.toString]
protected def toString : Term → String :=
  cvc5.Term.toString ∘ toCvc5

instance : ToString Term :=
  ⟨Term.toString⟩

/-- Yields the sort of a term. -/
def getSrt (t : Term) : Srt :=
  Srt.ofCvc5 t.toCvc5.getSort

@[inherit_doc cvc5.Term.substitute]
def substitute (term : Term) (substs : Array (Term × Term)) : Term.ManagerM Term :=
  let substs := substs.map fun (t, r) => (t.toCvc5, r.toCvc5)
  Term.ofCvc5 <$> term.toCvc5.substitute substs

/-! ### Constructors from `cvc5` -/

variable [Monad m]

protected def termLift (code : cvc5.TermManager → cvc5.Term) : Term.ManagerM Term := fun tm =>
  let res := code tm.toCvc5 |> ofCvc5
  return (.ok res, tm)

protected def termLift?
  (code : cvc5.TermManager → Except cvc5.Error cvc5.Term)
: Term.ManagerM Term := fun tm =>
  match code tm.toCvc5 with
  | .ok res => return (.ok (Term.ofCvc5 res), tm)
  | .error e => return (.error (Error.ofCvc5 e), tm)

@[inherit_doc cvc5.TermManager.mkVar]
def mkBVar (name : String) (srt : Srt) : ManagerM BVar :=
  BVar.ofTerm <$> Term.termLift (cvc5.TermManager.mkVar · srt.toCvc5 name)

@[inherit_doc cvc5.TermManager.mkBoolean]
def mkBool (b : Bool) : ManagerM Term :=
  Term.termLift (cvc5.TermManager.mkBoolean · b)

instance : ToTerm Bool := ⟨mkBool⟩
instance : ValueOfTerm Bool where
  valueOfTerm t := t.toCvc5.getBooleanValue

@[inherit_doc cvc5.TermManager.mkInteger]
def mkInt (i : Int) : ManagerM Term :=
  Term.termLift? (cvc5.TermManager.mkInteger · i)

instance : ToTerm Int := ⟨mkInt⟩
instance : ValueOfTerm Int where
  valueOfTerm t := t.toCvc5.getIntegerValue

instance : ToTerm Nat := ⟨mkInt ∘ Int.ofNat⟩

@[inherit_doc cvc5.TermManager.mkTerm]
def mk (kind : Kind) (children : Array Term := #[]) : ManagerM Term :=
  Term.termLift? (cvc5.TermManager.mkTerm · kind (children.map Term.toCvc5))

-- @[inherit_doc cvc5.Proof.getResult]
def ofProof : Proof → Term :=
  Term.ofCvc5 ∘ cvc5.Proof.getResult



/-! ### Convenience term constructors -/



/-- Creates a cvc5 term corresponding to a list of bound variables. -/
def mkBVarList (bvars : Array BVar) : ManagerM Term :=
  bvars.map BVar.toTerm |> mk .VARIABLE_LIST

/-- Existentially quantified formula. -/
def mkExists (bvars : Array BVar) (t : Term) : ManagerM Term :=
  mkBVarList bvars >>= (mk .EXISTS #[·, t])

/-- Universally quantifier formula. -/
def mkForall (bvars : Array BVar) (t : Term) : ManagerM Term :=
  mkBVarList bvars >>= (mk .FORALL #[·, t])



/-- If-then-else, `cnd : Bool` and `thn els : α`. -/
def mkIte (cnd thn els : Term) : ManagerM Term :=
  mk .ITE #[cnd, thn, els]

/-- Equality between two terms or more. -/
def mkEqN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .EQUAL terms

/-- Equality between two terms -/
def mkEq (lhs rhs : Term) : ManagerM Term :=
  mkEqN #[lhs, rhs]
@[inherit_doc mkEq]
protected abbrev eq := mkEq

/-- Pairwise distinct. -/
def mkDistinct (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .DISTINCT terms



private def arraySizeSplit
  (on0 : β) (on1 : α → β) (onMany : Array α → β)
  (array : Array α)
: β :=
  if array.size = 0 then
    on0
  else if h : array.size = 1 then
    array.get ⟨0, by simp [h]⟩
    |> on1
  else
    onMany array



/-- Boolean negation. -/
def mkNot (term : Term) : ManagerM Term :=
  mk .NOT #[term]
@[inherit_doc mkNot]
abbrev not := @mkNot

/-- N-ary conjunction. -/
def mkAndN : (terms : Array Term) → ManagerM Term :=
  arraySizeSplit (mkBool true) (return ·) (mk .AND ·)
/-- Binary conjunction. -/
def mkAnd (lhs rhs : Term) : ManagerM Term :=
  mkAndN #[lhs, rhs]
@[inherit_doc mkAnd]
abbrev and := @mkAnd

/-- N-ary implication. -/
def mkImpliesN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .IMPLIES terms
/-- Binary implication. -/
def mkImplies (lhs rhs : Term) : ManagerM Term :=
  mkImpliesN #[lhs, rhs]
@[inherit_doc mkImplies]
abbrev implies := mkImplies

/-- N-ary disjunction. -/
def mkOrN : (terms : Array Term) → ManagerM Term :=
  arraySizeSplit (mkBool false) (return ·) (mk .OR ·)
/-- Binary disjunction. -/
def mkOr (lhs rhs : Term) : ManagerM Term :=
  mkOrN #[lhs, rhs]
@[inherit_doc mkOr]
abbrev or := @mkOr

/-- N-ary exclusive disjunction. -/
def mkXorN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .XOR terms
/-- Binary exclusive disjunction. -/
def mkXor (lhs rhs : Term) : ManagerM Term :=
  mkXorN #[lhs, rhs]
@[inherit_doc mkXor]
abbrev xor := @mkXor



/-- N-ary less-than-or-equal-to. -/
def mkLeN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .LEQ terms
/-- Binary less-than-or-equal-to. -/
def mkLe (lhs rhs : Term) : ManagerM Term :=
  mkLeN #[lhs, rhs]
@[inherit_doc mkLe]
abbrev le := mkLe

/-- N-ary less-than. -/
def mkLtN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .LT terms
/-- Binary less-than. -/
def mkLt (lhs rhs : Term) : ManagerM Term :=
  mkLtN #[lhs, rhs]
@[inherit_doc mkLt]
abbrev lt := mkLt

/-- N-ary greater-than-or-equal-to. -/
def mkGeN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .GEQ terms
/-- Binary greater-than-or-equal-to. -/
def mkGe (lhs rhs : Term) : ManagerM Term :=
  mkGeN #[lhs, rhs]
@[inherit_doc mkGe]
abbrev ge := mkGe

/-- N-ary greater-than. -/
def mkGtN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .GT terms
/-- Binary greater-than. -/
def mkGt (lhs rhs : Term) : ManagerM Term :=
  mkGtN #[lhs, rhs]
@[inherit_doc mkGt]
abbrev gt := mkGt



/-- N-ary addition. -/
def mkAddN : (terms : Array Term) → ManagerM Term :=
  arraySizeSplit (mkInt 0) (return ·) (mk .ADD ·)
/-- Binary addition. -/
def mkAdd (lhs rhs : Term) : ManagerM Term :=
  mkAddN #[lhs, rhs]
@[inherit_doc mkAdd]
abbrev add := @mkAdd

/-- N-ary multiplication. -/
def mkMultN : (terms : Array Term) → ManagerM Term :=
  arraySizeSplit (mkInt 1) (return ·) (mk .MULT ·)
/-- Binary multiplication. -/
def mkMult (lhs rhs : Term) : ManagerM Term :=
  mkMultN #[lhs, rhs]
@[inherit_doc mkMult]
abbrev mult := @mkMult

/-- N-ary subtraction. -/
def mkSubN (terms : Array Term) (valid : 2 ≤ terms.size := by simp) : ManagerM Term :=
  let _ := valid
  mk .SUB terms
/-- Binary subtraction. -/
def mkSub (lhs rhs : Term) : ManagerM Term :=
  mkSubN #[lhs, rhs]
@[inherit_doc mkSub]
abbrev sub := @mkSub

/-- Arithmetic negation. -/
def mkNeg (term : Term) : ManagerM Term :=
  mk .NEG #[term]
@[inherit_doc mkNeg]
abbrev neg := @mkNeg



/-- Converts a integer/real term to an integer via the floor function. -/
def toInt (term : Term) : ManagerM Term :=
  mk .TO_INTEGER #[term]

/-- Converts a integer/real term to a real. -/
def toReal (term : Term) : ManagerM Term :=
  mk .TO_REAL #[term]



@[inherit_doc cvc5.Solver.simplify]
def simplify (term : Term) : SmtM Term :=
  Term.ofCvc5 <$> cvc5.Solver.simplify (m := Id) term.toCvc5
