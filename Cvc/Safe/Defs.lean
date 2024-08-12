/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic



/-! # Safe -/
namespace Cvc.Safe



/-- A cvc sort corresponding to a lean type. -/
structure Srt (α : Type) where
private ofUnsafe ::
  toUnsafe : Cvc.Srt

/-- A cvc term of a sort corresponding to a lean type. -/
structure Term (α : Type) where
private ofUnsafe ::
  toUnsafe : Cvc.Term



/-! ## Term Manager -/
namespace Term

/-- Term manager state. -/
structure Manager : Type where
private ofUnsafe ::
  toUnsafe : Cvc.Term.Manager

/-- Term manager state constructor. -/
def Manager.mk : BaseIO Manager :=
  (Manager.ofUnsafe ∘ ULift.up) <$> Cvc.Term.Manager.mk

/-- Term manager error/state monad transformer. -/
abbrev ManagerT (m : Type → Type) :=
  ExceptT Error (StateT Manager m)

namespace ManagerT
private def toUnsafe [Monad m] (safeCode : ManagerT m α) : Cvc.Term.ManagerT m α :=
  fun unsafeTm => do
    let (res, safeTm) ← safeCode ⟨unsafeTm⟩
    return (res, safeTm.toUnsafe)

private def runUnsafe [Monad m] (unsafeCode : Cvc.Term.ManagerT m α) : ManagerT m α :=
  fun safeTm => do
    let (res, unsafeTm) ← unsafeCode safeTm.toUnsafe
    return (res, ⟨unsafeTm⟩)
end ManagerT

/-- Term manager error/state monad. -/
abbrev ManagerM := ManagerT Id

instance [Monad m] : MonadLift ManagerM (ManagerT m) where
  monadLift code tm := return code tm

private instance [Monad m] : MonadLift (Cvc.Term.ManagerT m) (ManagerT m) where
  monadLift code tm := do
    let (res, tm!) ← code tm.toUnsafe
    return (res, Manager.ofUnsafe tm!)

/-- `Manager` error/state-monad wrapped in `IO`. -/
abbrev ManagerIO :=
  ManagerT IO

end Term



/-! ## Conversion from lean types to dependent `Srt`s / `Term`s -/

class HToSafeSrt (α : Type) (β : Type) where
  toSrt : Term.ManagerM (Srt β)

class ToSafeSrt (α : Type) extends HToSafeSrt α α

class HToSafeTerm (α : Type) (β : Type) extends HToSafeSrt α β where
  toTerm : α → Term.ManagerM (Term β)

class ToSafeTerm (α : Type) extends HToSafeTerm α α



/-! ## Sort construction -/
namespace Srt

protected def toString : Srt α → String :=
  toString ∘ Srt.toUnsafe

instance instToString : ToString (Srt α) :=
  ⟨Srt.toString⟩



private def ofCvc5' (α : Type) : cvc5.Sort → Srt α :=
  ofUnsafe ∘ ULift.up

private def ofCvc5 : cvc5.Sort → Srt α :=
  ofCvc5' α

def toCvc5 (srt : Srt α) : cvc5.Sort :=
  srt.toUnsafe.down

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

protected def real : Term.ManagerM (Srt Rat) := do
  let srt ← Cvc.Srt.real
  return Srt.ofUnsafe srt

instance : ToSafeSrt Rat where
  toSrt := Srt.real

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



def getSrt (self : Term α) : Srt α :=
  Srt.ofUnsafe self.toUnsafe.getSrt



protected def apply (self : Term (α → β)) (arg : Term α) : ManagerM (Term β) := do
  ofUnsafe <$> Cvc.Term.mk .HO_APPLY #[self.toUnsafe, arg.toUnsafe]

instance : CoeFun (Term (α → β)) (fun _ => Term α → ManagerM (Term β)) :=
  ⟨Term.apply⟩



def ofProof : Proof → Term Bool :=
  ofUnsafe ∘ Cvc.Term.ofProof



def of {α : Type} {β : outParam Type} [I : HToSafeTerm α β] (a : α) : ManagerM (Term β) :=
  I.toTerm a



def mkBool (b : Bool) : ManagerM (Term Bool) :=
  ofUnsafe <$> Cvc.Term.mkBool b

@[default_instance]
instance : HToSafeTerm Bool Bool where
  toTerm := mkBool

def mkInt (i : Int) : ManagerM (Term Int) :=
  ofUnsafe <$> Cvc.Term.mkInt i

@[default_instance]
instance : HToSafeTerm Int Int where
  toTerm := mkInt
@[default_instance]
instance : HToSafeTerm Nat Int where
  toTerm := mkInt ∘ Int.ofNat



/-! ### Convenience term constructors -/

@[inherit_doc Cvc.Term.mkIte]
def mkIte (cnd : Term Bool) (thn els : Term α) : ManagerM (Term α) :=
  ofUnsafe <$> Cvc.Term.mkIte cnd.toUnsafe thn.toUnsafe els.toUnsafe
@[inherit_doc mkIte]
def ite := @mkIte

@[inherit_doc Cvc.Term.mkEqN]
def mkEqN (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp) : ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkEqN terms! (by simp [terms!, valid])

@[inherit_doc Cvc.Term.mkEq]
def mkEq (lhs rhs : Term α) : ManagerM (Term Bool) :=
  ofUnsafe <$> Cvc.Term.mkEq lhs.toUnsafe rhs.toUnsafe
@[inherit_doc mkEq]
def eq := @mkEq

@[inherit_doc Cvc.Term.mkDistinct]
def mkDistinct
  (terms : Array (Term α)) (valid : 2 ≤ terms.size := by simp)
: ManagerM (Term Bool) :=
  let terms! := terms.map toUnsafe
  ofUnsafe <$> Cvc.Term.mkDistinct terms! (by simp [terms!, valid])



@[inherit_doc Cvc.Term.mkNot]
def mkNot (self : Term Bool) : ManagerM (Term Bool) :=
  return ofUnsafe (← self.toUnsafe.mkNot)
@[inherit_doc mkNot]
abbrev not := mkNot

@[inherit_doc Cvc.Term.mkAnd]
def mkAnd (self that : Term Bool) : ManagerM (Term Bool) :=
  return ofUnsafe (← self.toUnsafe.mkAnd that.toUnsafe)
@[inherit_doc mkAnd]
abbrev and := mkAnd

@[inherit_doc Cvc.Term.mkOr]
def mkOr (self that : Term Bool) : ManagerM (Term Bool) :=
  return ofUnsafe (← self.toUnsafe.mkOr that.toUnsafe)
@[inherit_doc mkOr]
abbrev or := mkOr

@[inherit_doc Cvc.Term.mkXor]
def mkXor (self that : Term Bool) : ManagerM (Term Bool) :=
  return ofUnsafe (← self.toUnsafe.mkXor that.toUnsafe)
@[inherit_doc mkXor]
abbrev xor := mkXor

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
    SmtT.ofUnsafe code.toUnsafe

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
  code.toUnsafe.runWith tm.toUnsafe

@[inherit_doc Cvc.Smt.run]
def run [MonadLiftT BaseIO m]
  (code : SmtT m α)
: ExceptT Error m α :=
  code.toUnsafe.run

@[inherit_doc Cvc.Smt.run!]
def run! [MonadLiftT BaseIO m] [Inhabited α]
  (code : SmtT m α)
  (handleError : Error → m α := fun e => panic! s!"{e}")
: m α :=
  code.toUnsafe.run! handleError

end SmtT



namespace Smt

@[inherit_doc SmtT.runWith]
protected def runWith := @SmtT.runWith

@[inherit_doc SmtT.run]
protected def run := @SmtT.run

@[inherit_doc SmtT.run]
protected def run! := @SmtT.run!



@[inherit_doc Cvc.Smt.declareFun]
def declareFun [Monad m] (symbol : String) (α : Type) [A : ToSafeSrt α] : SmtT m (Term α) := do
  let a ← A.toSrt
  let (domain, codomain) ← a.cvc5Signature
  Term.ofCvc5 <$> cvc5.Solver.declareFun symbol domain codomain false (m := m)

@[inherit_doc declareFun]
abbrev declare := @declareFun

end Smt
