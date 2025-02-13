/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic



/-! # Safe

Safe(r) term creation / solver commands. Sorts and terms are strongly-typed, and
sat/unsat/unknown-specific commands can only be invoked when the solver is in sat/unsat/unknown
mode.
-/
namespace Cvc.Safe

export Cvc (Logic)
export Cvc.Term (ManagerM ManagerT ManagerIO)

namespace Smt

export Cvc.Smt (Actlit)

end Smt



/-- A cvc sort corresponding to a lean type. -/
structure Srt (α : Type) where
private ofUnsafe ::
  toUnsafe : Cvc.Srt

/-- A cvc term of a sort corresponding to a lean type. -/
structure Term (α : Type) where
private ofUnsafe ::
  toUnsafe : Cvc.Term

namespace Term
def untype (t : Term α) : (β : Type) × Term β :=
  ⟨α, t⟩
end Term

/-- A bound variable. -/
structure BVar (α : Type) where
private ofUnsafe ::
  toUnsafe : Cvc.BVar

namespace BVar
-- def untype (bv : BVar α) : (β : Type) × BVar β :=
--   ⟨α, bv⟩
def toTerm! (bv : BVar α) : Cvc.Term :=
  bv.toUnsafe.toTerm
def toTerm (bv : BVar α) : Term α :=
  Term.ofUnsafe bv.toTerm!
end BVar


-- /-- A list of bound variables. -/
-- def BVars := Array ((α : Type) × BVar α)

-- namespace BVars
-- def push (self : BVars) (bv : BVar α) : BVars :=
--   Array.push self bv.untype

-- def toUnsafe (self : BVars) : Array Cvc.BVar :=
--   self.map fun ⟨_, bv⟩ => bv.toUnsafe
-- end BVars


/-- A list of bound variables. -/
structure BVars where
private ofUnsafe ::
  toUnsafe : Array Cvc.BVar

namespace BVars
def empty : BVars where
  toUnsafe := #[]

def push (self : BVars) (bv : BVar α) : BVars :=
  {self with toUnsafe := self.toUnsafe.push bv.toUnsafe}

protected def toString (self : BVars) : String :=

  self.toUnsafe.foldl
    (fun s bv => if s = "[" then s ++ toString bv else s ++ ", " ++ toString bv)
    "["
  |> (· ++ "]")

instance : ToString BVars := ⟨BVars.toString⟩
end BVars



/-! ## Helper typeclasses -/

/-- `α` can be seen as a `Srt β`. -/
class HToSafeSrt (α : Type) (β : Type) where
  toSrt : Term.ManagerM (Srt β)

/-- `α` can be seen as a `Srt α`. -/
class abbrev ToSafeSrt (α : Type) := HToSafeSrt α α

/-- `α`-values can be seen as `Term β`. -/
class HToSafeTerm (α : Type) (β : Type) extends HToSafeSrt α β where
  toTerm : α → Term.ManagerM (Term β)

/-- `α`-values can be seen as `Term α`. -/
class abbrev ToSafeTerm (α : Type) := HToSafeTerm α α

/-- `Term α` to `α`-value. -/
class ValueOfSafeTerm (α : Type) extends HToSafeSrt α α, ValueOfTerm α, ToString α where
  ofTerm : Term α → Term.ManagerM α

/-- Specifies that `Term α` have access to arithmetic operators like add, sub, mult, ... -/
class ArithLike (α : Type)



/-! ## Sort construction -/
namespace Srt

protected def toString : Srt α → String :=
  toString ∘ Srt.toUnsafe

instance instToString : ToString (Srt α) :=
  ⟨Srt.toString⟩



private def ofCvc5' (α : Type) : cvc5.Sort → Srt α :=
  ofUnsafe ∘ Srt.ofCvc5

private def ofCvc5 : cvc5.Sort → Srt α :=
  ofCvc5' α

def toCvc5 (srt : Srt α) : cvc5.Sort :=
  srt.toUnsafe.toCvc5

protected def cvc5Signature : Srt α → Term.ManagerM (Array cvc5.Sort × cvc5.Sort) :=
  (toUnsafe · |>.cvc5Signature)



instance instCoeSort {α : Type} : CoeSort (Srt α) Type where
  coe _ := α



instance instToSafeSrtFun [A : ToSafeSrt α] [B : ToSafeSrt β] : ToSafeSrt (α → β) where
  toSrt := do
    let a ← A.toSrt
    let b ← B.toSrt
    let a! := a.toCvc5
    let b! := b.toCvc5
    let (domain, codomain) ←
      if b!.isFunction then
        let domain ← b!.getFunctionDomainSorts
        let domain := #[a!] ++ domain
        let domain := domain.map Cvc.Srt.ofCvc5
        let codomain ← b!.getFunctionCodomainSort
        let codomain := Cvc.Srt.ofCvc5 codomain
        pure (domain, codomain)
      else
        pure (#[a.toUnsafe], b.toUnsafe)
    Srt.ofUnsafe <$> Cvc.Srt.function domain codomain



protected def bool : Term.ManagerM (Srt Bool) := do
  let srt ← Cvc.Srt.bool
  return Srt.ofUnsafe srt

instance : ToSafeSrt Bool where
  toSrt := Srt.bool

protected def int : Term.ManagerM (Srt Int) := do
  let srt ← Cvc.Srt.int
  return Srt.ofUnsafe srt

instance : ToSafeSrt Int where
  toSrt := Srt.int
instance : HToSafeSrt Nat Int where
  toSrt := Srt.int
instance : ArithLike Int := ⟨⟩

protected def real : Term.ManagerM (Srt Rat) := do
  let srt ← Cvc.Srt.real
  return Srt.ofUnsafe srt

instance : ToSafeSrt Rat where
  toSrt := Srt.real
instance : ArithLike Rat := ⟨⟩

protected def string : Term.ManagerM (Srt String) := do
  let srt ← Cvc.Srt.string
  return Srt.ofUnsafe srt

instance : ToSafeSrt String where
  toSrt := Srt.string

protected opaque Array (I : α) (E : β) : Type (max u v) :=
  PUnit

protected def array (idx elm : Type)
  [I : ToSafeSrt idx] [E : ToSafeSrt elm]
: Term.ManagerM (Srt (Srt.Array idx elm)) := do
  let idx ← I.toSrt
  let elm ← E.toSrt
  let srt ← Cvc.Srt.array idx.toUnsafe elm.toUnsafe
  return Srt.ofUnsafe srt

instance [ToSafeSrt I] [ToSafeSrt E] : ToSafeSrt (Srt.Array I E) where
  toSrt := Srt.array I E

protected def bitVec
  (size : UInt32) (valid : 0 < size)
: Term.ManagerM (Srt (BitVec size.toNat)) := do
  let srt ← Cvc.Srt.bitVec size valid
  return Srt.ofUnsafe srt

instance {size : UInt32} (valid : 0 < size) : ToSafeSrt (BitVec size.toNat) where
  toSrt := Srt.bitVec size valid

end Srt



namespace Term

-- @[inherit_doc Cvc.Term.toString]
protected def toString : Term α → String :=
  (toUnsafe · |>.toString)

instance : ToString (Term α) := ⟨Term.toString⟩



private def ofUnsafe' (α : Type) [ToSafeSrt α] (term : Cvc.Term) : Term α :=
  ofUnsafe term

def toCvc5 (self : Term α) : cvc5.Term :=
  self.toUnsafe.toCvc5

private def ofCvc5' (α : Type) [ToSafeSrt α] : cvc5.Term → Term α :=
  ofUnsafe' α ∘ Cvc.Term.ofCvc5

private def ofCvc5 [ToSafeSrt α] : cvc5.Term → Term α :=
  ofCvc5' α



@[inherit_doc Cvc.Term.isActlit]
def isActlit (t : Term Bool) : SmtM Bool :=
  Cvc.Term.isActlit t.toUnsafe

/-- The `Bool` term corresponding to an activation literal. -/
def ofActlit (actlit : Smt.Actlit) : Term Bool :=
  ofUnsafe actlit.term

@[inherit_doc Cvc.Term.assertActivation]
def assertActivation (a : Smt.Actlit) (t : Term Bool) : SmtM Unit :=
  t.toUnsafe.assertActivation a



@[inherit_doc Cvc.Term.getSrt]
def getSrt (self : Term α) : Srt α :=
  Srt.ofUnsafe self.toUnsafe.getSrt

@[inherit_doc Cvc.Term.simplify]
def simplify (term : Term α) : SmtM (Term α) :=
  Term.ofUnsafe <$> Cvc.Term.simplify term.toUnsafe

@[inherit_doc Cvc.Term.substitute]
def substitute
  [ToSafeSrt α]
  (term : Term α) (substs : Array ((β : Type) × Term β × Term β))
: Term.ManagerM (Term α) := do
  let substs := substs.map fun ⟨_, t, r⟩ => (t.toCvc5, r.toCvc5)
  Term.ofCvc5 <$> term.toCvc5.substitute substs



private partial def flattenHoApply
  (revArgs : Array Cvc.Term) (term : cvc5.Term)
: ManagerM Cvc.Term := do
  match term.getKind with
  | .HO_APPLY =>
    let args := term.getChildren
    let f := args.get! 0
    let args := args.toSubarray (start := 1)
    let revArgs := revArgs |> args.foldr fun arg acc => acc.push (Cvc.Term.ofCvc5 arg)
    flattenHoApply revArgs f
  | _ =>
    if revArgs.isEmpty then
      return Cvc.Term.ofCvc5 term
    else
      let revArgs := revArgs.push (.ofCvc5 term)
      Cvc.Term.mk cvc5.Kind.APPLY_UF revArgs.reverse

protected def apply
  (self : Term (α → β)) (arg : Term α)
: ManagerM (Term β) := do
  let term! := self.toCvc5
  let sort! := term!.getSort
  let dom ← sort!.getFunctionDomainSorts
  if 1 < dom.size then
    ofUnsafe <$> Cvc.Term.mk .HO_APPLY #[self.toUnsafe, arg.toUnsafe]
  else
    ofUnsafe <$> flattenHoApply #[arg.toUnsafe] term!

instance : CoeFun (Term (α → β)) (𝕂 $ Term α → ManagerM (Term β)) :=
  ⟨Term.apply⟩



def ofProof : Proof → Term Bool :=
  ofUnsafe ∘ Cvc.Term.ofProof



def of {α : Type} {β : outParam Type} [I : HToSafeTerm α β] (a : α) : ManagerM (Term β) :=
  I.toTerm a



def mkBVar (name : String) (α : Type) [A : ToSafeSrt α] : ManagerM (BVar α) := do
  let srt ← A.toSrt
  BVar.ofUnsafe <$> Cvc.Term.mkBVar name srt.toUnsafe

def mkBool (b : Bool) : ManagerM (Term Bool) :=
  ofUnsafe <$> Cvc.Term.mkBool b

@[default_instance]
instance : HToSafeTerm Bool Bool where
  toTerm := mkBool
instance : ValueOfSafeTerm Bool where
  ofTerm t := t.toCvc5.getBooleanValue

def mkInt (i : Int) : ManagerM (Term Int) :=
  ofUnsafe <$> Cvc.Term.mkInt i

@[default_instance]
instance : HToSafeTerm Int Int where
  toTerm := mkInt
@[default_instance]
instance : HToSafeTerm Nat Int where
  toTerm := mkInt ∘ Int.ofNat
instance : ValueOfSafeTerm Int where
  ofTerm t := t.toCvc5.getIntegerValue



/-! ### Convenience term constructors -/



@[inherit_doc Cvc.Term.mkBVarList]
private def mkBVarList (bvars : BVars) : ManagerM Cvc.Term :=
  Cvc.Term.mkBVarList bvars.toUnsafe

@[inherit_doc Cvc.Term.mkExists]
def mkExists (bvars : BVars) (t : Term Bool) : ManagerM (Term Bool) :=
  Term.ofUnsafe <$> Cvc.Term.mkExists bvars.toUnsafe t.toUnsafe

@[inherit_doc Cvc.Term.mkForall]
def mkForall (bvars : BVars) (t : Term Bool) : ManagerM (Term Bool) :=
  Term.ofUnsafe <$> Cvc.Term.mkForall bvars.toUnsafe t.toUnsafe



@[inherit_doc Cvc.Term.mkIte]
def mkIte (cnd : Term Bool) (thn els : Term α) : ManagerM (Term α) :=
  ofUnsafe <$> Cvc.Term.mkIte cnd.toUnsafe thn.toUnsafe els.toUnsafe
@[inherit_doc Cvc.Term.mkIte]
protected def ite := @mkIte

@[inherit_doc Cvc.Term.mkEqN]
def mkEqN (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp) : ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkEqN terms! (by simp [terms!, valid])

@[inherit_doc Cvc.Term.mkEq]
def mkEq (lhs rhs : Term α) : ManagerM (Term Bool) :=
  ofUnsafe <$> Cvc.Term.mkEq lhs.toUnsafe rhs.toUnsafe
@[inherit_doc Cvc.Term.mkEq]
protected def eq := @mkEq

@[inherit_doc Cvc.Term.mkDistinct]
def mkDistinct
  (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp)
: ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkDistinct terms! (by simp [terms!, valid])



@[inherit_doc Cvc.Term.mkNot]
def mkNot (self : Term Bool) : ManagerM (Term Bool) :=
  ofUnsafe <$> self.toUnsafe.mkNot
@[inherit_doc Cvc.Term.mkNot]
abbrev not := mkNot

@[inherit_doc Cvc.Term.mkAndN]
def mkAndN (terms : Array (Term Bool)) : ManagerM (Term Bool) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkAndN terms
@[inherit_doc Cvc.Term.mkAnd]
def mkAnd (self that : Term Bool) : ManagerM (Term Bool) :=
  ofUnsafe <$> self.toUnsafe.and that.toUnsafe
@[inherit_doc Cvc.Term.mkAnd]
abbrev and := mkAnd

@[inherit_doc Cvc.Term.mkImpliesN]
def mkImpliesN
  (terms : Array (Term Bool)) (valid : 2 ≤ terms.size := by simp)
: ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkImpliesN terms! (by simp [terms!, valid])
@[inherit_doc Cvc.Term.mkImplies]
def mkImplies (self that : Term Bool) : ManagerM (Term Bool) :=
  ofUnsafe <$> self.toUnsafe.implies that.toUnsafe
@[inherit_doc Cvc.Term.mkImplies]
abbrev implies := mkImplies

@[inherit_doc Cvc.Term.mkOrN]
def mkOrN (terms : Array (Term Bool)) : ManagerM (Term Bool) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkOrN terms
@[inherit_doc Cvc.Term.mkOr]
def mkOr (self that : Term Bool) : ManagerM (Term Bool) :=
  ofUnsafe <$> self.toUnsafe.or that.toUnsafe
@[inherit_doc Cvc.Term.mkOr]
abbrev or := mkOr

@[inherit_doc Cvc.Term.mkXorN]
def mkXorN (terms : Array (Term Bool)) (valid : 2 ≤ terms.size := by simp) : ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkXorN terms! (by simp [terms!, valid])
@[inherit_doc Cvc.Term.mkXor]
def mkXor (self that : Term Bool) : ManagerM (Term Bool) :=
  ofUnsafe <$> self.toUnsafe.xor that.toUnsafe
@[inherit_doc Cvc.Term.mkXor]
abbrev xor := mkXor



/-! ### Arithmetic -/



@[inherit_doc Cvc.Term.mkLeN]
def mkLeN [ArithLike α]
  (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp)
: ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkLeN terms! (by simp [terms!, valid])
@[inherit_doc Cvc.Term.mkLe]
def mkLe [ArithLike α] (lhs rhs : Term α) : ManagerM (Term Bool) :=
  ofUnsafe <$> lhs.toUnsafe.le rhs.toUnsafe
@[inherit_doc Cvc.Term.mkLe]
abbrev le := @mkLe


@[inherit_doc Cvc.Term.mkLeN]
def mkLtN [ArithLike α]
  (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp)
: ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkLtN terms! (by simp [terms!, valid])
@[inherit_doc Cvc.Term.mkLt]
def mkLt [ArithLike α] (lhs rhs : Term α) : ManagerM (Term Bool) :=
  ofUnsafe <$> lhs.toUnsafe.lt rhs.toUnsafe
@[inherit_doc Cvc.Term.mkLt]
abbrev lt := @mkLt

@[inherit_doc Cvc.Term.mkGeN]
def mkGeN [ArithLike α]
  (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp)
: ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkGeN terms! (by simp [terms!, valid])
@[inherit_doc Cvc.Term.mkGe]
def mkGe [ArithLike α] (lhs rhs : Term α) : ManagerM (Term Bool) :=
  ofUnsafe <$> lhs.toUnsafe.ge rhs.toUnsafe
@[inherit_doc Cvc.Term.mkGe]
abbrev ge := @mkGe

@[inherit_doc Cvc.Term.mkGtN]
def mkGtN [ArithLike α]
  (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp)
: ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkGtN terms! (by simp [terms!, valid])
@[inherit_doc Cvc.Term.mkGt]
def mkGt [ArithLike α] (lhs rhs : Term α) : ManagerM (Term Bool) :=
  ofUnsafe <$> lhs.toUnsafe.gt rhs.toUnsafe
@[inherit_doc Cvc.Term.mkGt]
abbrev gt := @mkGt



@[inherit_doc Cvc.Term.mkAddN]
def mkAddN [ArithLike α] (terms : Array (Term α)) : ManagerM (Term α) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkAddN terms
@[inherit_doc Cvc.Term.mkAdd]
abbrev mkAdd [ArithLike α] (a b : Term α) : ManagerM (Term α) :=
  ofUnsafe <$> a.toUnsafe.add b.toUnsafe
@[inherit_doc Cvc.Term.mkAdd]
abbrev add := @mkAdd

@[inherit_doc Cvc.Term.mkMulN]
def mkMulN [ArithLike α] (terms : Array (Term α)) : ManagerM (Term α) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkMulN terms
@[inherit_doc Cvc.Term.mkMul]
abbrev mkMul [ArithLike α] (a b : Term α) : ManagerM (Term α) :=
  ofUnsafe <$> a.toUnsafe.mul b.toUnsafe
@[inherit_doc Cvc.Term.mkMul]
abbrev mul := @mkMul

@[inherit_doc Cvc.Term.mkRatDivN]
def mkRatDivN (terms : Array (Term Rat)) : ManagerM (Term Rat) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkRatDivN terms
@[inherit_doc Cvc.Term.mkRatDiv]
abbrev mkRatDiv (a b : Term Rat) : ManagerM (Term Rat) :=
  ofUnsafe <$> a.toUnsafe.mul b.toUnsafe
@[inherit_doc Cvc.Term.mkRatDiv]
abbrev ratDiv := @mkRatDiv

@[inherit_doc Cvc.Term.mkRatDivTotalN]
def mkRatDivTotalN (terms : Array (Term Rat)) : ManagerM (Term Rat) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkRatDivTotalN terms
@[inherit_doc Cvc.Term.mkRatDivTotal]
abbrev mkRatDivTotal (a b : Term Rat) : ManagerM (Term Rat) :=
  ofUnsafe <$> a.toUnsafe.mul b.toUnsafe
@[inherit_doc Cvc.Term.mkRatDivTotal]
abbrev ratDivTotal := @mkRatDivTotal

@[inherit_doc Cvc.Term.mkIntDivN]
def mkIntDivN (terms : Array (Term Int)) : ManagerM (Term Int) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkIntDivN terms
@[inherit_doc Cvc.Term.mkIntDiv]
abbrev mkIntDiv (a b : Term Int) : ManagerM (Term Int) :=
  ofUnsafe <$> a.toUnsafe.mul b.toUnsafe
@[inherit_doc Cvc.Term.mkIntDiv]
abbrev intDiv := @mkIntDiv

@[inherit_doc Cvc.Term.mkIntDivTotalN]
def mkIntDivTotalN (terms : Array (Term Int)) : ManagerM (Term Int) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkIntDivTotalN terms
@[inherit_doc Cvc.Term.mkIntDivTotal]
abbrev mkIntDivTotal (a b : Term Int) : ManagerM (Term Int) :=
  ofUnsafe <$> a.toUnsafe.mul b.toUnsafe
@[inherit_doc Cvc.Term.mkIntDivTotal]
abbrev intDivTotal := @mkIntDivTotal

@[inherit_doc Cvc.Term.mkModN]
def mkModN (terms : Array (Term Int)) : ManagerM (Term Int) :=
  let terms := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkModN terms
@[inherit_doc Cvc.Term.mkMod]
abbrev mkMod (a b : Term Int) : ManagerM (Term Int) :=
  ofUnsafe <$> a.toUnsafe.mul b.toUnsafe
@[inherit_doc Cvc.Term.mkMod]
abbrev Mod := @mkMod

@[inherit_doc Cvc.Term.mkSubN]
def mkSubN (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp) : ManagerM (Term α) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkSubN terms! (by simp [terms!, valid])
@[inherit_doc Cvc.Term.mkSub]
def mkSub (self that : Term α) : ManagerM (Term α) :=
  ofUnsafe <$> self.toUnsafe.sub that.toUnsafe
@[inherit_doc Cvc.Term.mkSub]
abbrev sub := @mkSub

@[inherit_doc Cvc.Term.mkNeg]
def mkNeg (self : Term α) : ManagerM (Term α) :=
  ofUnsafe <$> self.toUnsafe.neg
@[inherit_doc Cvc.Term.mkNeg]
abbrev neg := @mkNeg



/-- Converts a real term to an integer one via the floor function. -/
def toInt (term : Term Rat) : ManagerM (Term Int) :=
  ofUnsafe <$> term.toUnsafe.toInt

/-- Converts an integer term to a real one. -/
def toReal (term : Term Rat) : ManagerM (Term Int) :=
  ofUnsafe <$> term.toUnsafe.toReal

end Term



/-! ## `Smt`: a term manager and a solver -/

/-- Smt state. -/
structure Smt where
private ofUnsafe ::
  private toUnsafe : Cvc.Smt

abbrev SmtT (m : Type → Type u) :=
  ExceptT Error (StateT Smt m)

abbrev SmtIO := SmtT IO

abbrev SmtM := SmtT Id

namespace SmtT
variable [Monad m]

instance instMonadLiftSmtMToSmtT : MonadLift SmtM (SmtT m) where
  monadLift code smt := do
    return code smt

private def ofUnsafe (unsafeCode : Cvc.SmtT m α) : SmtT m α :=
  fun safeSmt => do
    let (res, unsafeSmt) ← unsafeCode safeSmt.toUnsafe
    return (res, ⟨unsafeSmt⟩)

private def toUnsafe (safeCode : SmtT m α) : Cvc.SmtT m α :=
  fun unsafeSmt => do
    let (res, safeSmt) ← safeCode ⟨unsafeSmt⟩
    return (res, safeSmt.toUnsafe)

def throwInternal (msg : String) : SmtT m α :=
  .internal msg |> throw

def throwUser (msg : String) : SmtT m α :=
  .userError msg |> throw

instance instMonadLiftManagerT : MonadLift (Term.ManagerT m) (SmtT m) where
  monadLift code :=
    SmtT.ofUnsafe code

instance instMonadLiftSmtT : MonadLift (Cvc.SmtT m) (SmtT m) where
  monadLift code smt := do
    let (res, smt!) ← code smt.toUnsafe
    return (res, Smt.ofUnsafe smt!)

private instance : MonadLift (cvc5.SolverT m) (SmtT m) where
  monadLift code smt := do
    let (res, smt) ← (Cvc.SmtT.instMonadLiftCvc5.monadLift code) smt.toUnsafe
    return (res, Smt.ofUnsafe smt)



/-! ## Runners -/

@[inherit_doc Cvc.Smt.runWith]
def runWith (tm : Term.Manager) (code : SmtT m α) : m (Except Error α) :=
  code.toUnsafe.runWith tm
@[inherit_doc runWith]
def runIOWith := @runWith (m := IO)

@[inherit_doc Cvc.Smt.run]
def run [MonadLiftT BaseIO m]
  (code : SmtT m α)
: ExceptT Error m α :=
  code.toUnsafe.run
@[inherit_doc run]
def runIO := @run (m := IO)

@[inherit_doc Cvc.Smt.run!]
def run! [MonadLiftT BaseIO m] [Inhabited α]
  (code : SmtT m α)
  (handleError : Error → m α := fun e => panic! s!"{e}")
: m α :=
  code.toUnsafe.run! handleError
@[inherit_doc run!]
def runIO! := @run! (m := IO)

end SmtT



namespace Smt

@[inherit_doc SmtT.runWith]
protected def runWith := @SmtT.runWith

@[inherit_doc SmtT.run]
protected def run := @SmtT.run

@[inherit_doc SmtT.run]
protected def run! := @SmtT.run!



def setOption (opt : Opt) : SmtM PUnit := do
  Cvc.Smt.setOption opt

@[inherit_doc Cvc.Smt.declareFun]
def declareFun (symbol : String) (α : Type) [A : ToSafeSrt α] : SmtM (Term α) := do
  let a ← A.toSrt
  let (domain, codomain) ← a.cvc5Signature
  Term.ofCvc5 <$> cvc5.Solver.declareFun symbol domain codomain false (m := Id)

@[inherit_doc declareFun]
abbrev declare := @declareFun

@[inherit_doc Cvc.Smt.getInterpolant?]
def getInterpolant? (term : Term Bool) : SmtM (Option (Term Bool)) := do
  Option.map Term.ofUnsafe <$> Cvc.Smt.getInterpolant? term.toUnsafe

@[inherit_doc Cvc.Smt.getQuantifierElimination]
def getQuantifierElimination (q : Term Bool) : SmtM (Term Bool) := do
  Term.ofUnsafe <$> Cvc.Smt.getQuantifierElimination q.toUnsafe


@[inherit_doc Cvc.Smt.checkSat?]
def checkSat? (terms : Array (Term Bool) := #[]) : SmtM (Option Bool) :=
  if terms.isEmpty
  then Cvc.Smt.checkSat?
  else terms.map Term.toUnsafe |> Cvc.Smt.checkSatAssuming?

@[inherit_doc Cvc.Smt.mkActlit]
def mkActlit : SmtM Actlit :=
  Cvc.Smt.mkActlit

@[inherit_doc Cvc.Smt.assertActivation]
def assertActivation (a : Actlit) (t : Term Bool) : SmtM Unit :=
  Cvc.Smt.assertActivation a t.toUnsafe

@[inherit_doc Cvc.Smt.deActlit]
def deActlit (a : Actlit) : SmtM Unit :=
  Cvc.Smt.deActlit a



protected structure Sat where
private ofSmt ::
  private toSmt : Smt

protected abbrev SatT (m : Type → Type u) := ExceptT Error (StateT Smt.Sat m)

protected abbrev SatM := Smt.SatT Id

namespace Sat
def unexpected [Monad m] : Smt.SatT m α :=
  .userError "unexpected sat result" |> throw

instance monadLiftSatM [Monad m] : MonadLift Smt.SatM (Smt.SatT m) where
  monadLift code sat :=
    return code sat

instance monadLiftManagerT [Monad m] : MonadLift (Term.ManagerT m) (Smt.SatT m) where
  monadLift code sat := do
    let (res, smt) ← (code : SmtT m _) sat.toSmt
    return (res, ofSmt smt)
end Sat


protected structure Unsat where
private ofSmt ::
  private toSmt : Smt

protected abbrev UnsatT (m : Type → Type u) := ExceptT Error (StateT Smt.Unsat m)

protected abbrev UnsatM := Smt.UnsatT Id

namespace Unsat
def unexpected [Monad m] : Smt.UnsatT m α :=
  .userError "unexpected unsat result" |> throw

instance monadLiftUnsatM [Monad m] : MonadLift Smt.UnsatM (Smt.UnsatT m) where
  monadLift code sat :=
    return code sat

instance monadLiftManagerT [Monad m] : MonadLift (Term.ManagerT m) (Smt.UnsatT m) where
  monadLift code unsat := do
    let (res, smt) ← (code : SmtT m _) unsat.toSmt
    return (res, ofSmt smt)
end Unsat



protected structure Unknown where
private ofSmt ::
  private toSmt : Smt

protected abbrev UnknownT (m : Type → Type u) := ExceptT Error (StateT Smt.Unknown m)

protected abbrev UnknownM := Smt.UnknownT Id

namespace Unknown
def unexpected [Monad m] : Smt.UnknownT m α :=
  .userError "could not decide (un)satisfiability" |> throw

instance monadLiftUnknownM [Monad m] : MonadLift Smt.UnknownM (Smt.UnknownT m) where
  monadLift code sat :=
    return code sat

instance monadLiftManagerT [Monad m] : MonadLift (Term.ManagerT m) (Smt.UnknownT m) where
  monadLift code unknown := do
    let (res, smt) ← (code : SmtT m _) unknown.toSmt
    return (res, ofSmt smt)
end Unknown



/-- Check satisfiability and run specific sat, unsat, or unknown code.

- `ifSat`: Runs when satisfiable, produces an unexpected-style error by default.
- `ifUnsat`: Runs when unsatisfiable, produces an unexpected-style error by default.
- `ifUnknown`: Runs when (un)satisfiability cannot be established, produces an unexpected-style
  error by default.
-/
def checkSat [Monad m]
  (terms : Array (Term Bool) := #[])
  (ifSat : Smt.SatT m α := Smt.Sat.unexpected)
  (ifUnsat : Smt.UnsatT m α := Smt.Unsat.unexpected)
  (ifUnknown : Smt.UnknownT m α := Smt.Unknown.unexpected)
: SmtT m α := fun smt => do
  match checkSat? terms smt with
  | (.ok (some true), smt) =>
    let (res, smt') ← ifSat ⟨smt⟩
    return (res, smt'.toSmt)
  | (.ok (some false), smt) =>
    let (res, smt') ← ifUnsat ⟨smt⟩
    return (res, smt'.toSmt)
  | (.ok none, smt) =>
    let (res, smt') ← ifUnknown ⟨smt⟩
    return (res, smt'.toSmt)
  | (.error e, smt) =>
    return (.error e, smt)



/-! ### Sat-specific commands -/

@[inherit_doc Cvc.Smt.getValue]
def getValue {α : Type} [I : ValueOfSafeTerm α]
  (term : Term α)
: Smt.SatM α := fun smt =>
  let (res, smt!) := Cvc.Smt.getValue term.toUnsafe smt.toSmt.toUnsafe
  match res with
  | .ok value =>
    let get : Cvc.SmtM α := I.valueOfTerm value
    let (res, smt!) := get smt!
    (res, Smt.Sat.ofSmt (Smt.ofUnsafe smt!))
  | .error e =>
    (.error e, Smt.Sat.ofSmt (Smt.ofUnsafe smt!))

/-! ### Unsat-specific commands -/

@[inherit_doc Cvc.Smt.getProof]
def getProof : Smt.UnsatM (Array cvc5.Proof) := fun unsat =>
  let (res, smt) := (Cvc.Smt.getProof : SmtM _) unsat.toSmt
  (res, Smt.Unsat.ofSmt smt)

end Smt
