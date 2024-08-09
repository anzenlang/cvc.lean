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
structure Srt (α : Type u) where
private ofUnsafe ::
  toUnsafe : Cvc.Srt

class HToSafeSrt (α : Type u) (β : Type v) where
  toSrt : Term.ManagerM (Srt β)

class ToSafeSrt (α : Type u) extends HToSafeSrt α α

/-- A cvc term of a sort corresponding to a lean type. -/
structure Term (α : Type u) extends ToSafeSrt α where
private mkRaw ::
  toUnsafe : Cvc.Term

class ToSafeTerm (α : Type u) (β : Type v) extends HToSafeSrt α β where
  toTerm : α → Term.ManagerM (Srt β)



/-! ## Term Manager -/
namespace Term

structure Manager : Type u where
private ofUnsafe ::
  toUnsafe : Cvc.Term.Manager.{u}

def Manager.mk : BaseIO Manager :=
  (Manager.ofUnsafe ∘ ULift.up) <$> Cvc.Term.Manager.mk

/-- `Manager` error/state monad transformer. -/
abbrev ManagerT (m : Type u → Type v) :=
  ExceptT Error (StateT Manager m)

namespace ManagerT
private def toUnsafe [Monad m] (safeCode : ManagerT m α) : Cvc.Term.ManagerT m α :=
  fun unsafeTm => do
    let (res, safeTm) ← safeCode ⟨unsafeTm⟩
    return (res, safeTm.toUnsafe)

private def ofUnsafe [Monad m] (unsafeCode : Cvc.Term.ManagerT m α) : ManagerT m α :=
  fun safeTm => do
    let (res, unsafeTm) ← unsafeCode safeTm.toUnsafe
    return (res, ⟨unsafeTm⟩)
end ManagerT

/-- `Manager` error/state-monad wrapped in `IO`. -/
abbrev ManagerIO :=
  ManagerT IO

end Term



variable [Monad m]



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

end Smt



/-! ## Sort construction -/
namespace Srt

private def toCvc5 (srt : Srt α) : cvc5.Sort :=
  srt.toUnsafe.down

private def ofCvc5 : cvc5.Sort → Srt α :=
  ofUnsafe ∘ ULift.up

instance instCoeSort {α : Type u} : CoeSort (Srt α) (Type u) where
  coe _ := α

instance [A : ToSafeSrt α] [B : ToSafeSrt β] : ToSafeSrt (α → β) where
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

private instance : MonadLift (Cvc.Term.ManagerT m) (Term.ManagerT m) where
  monadLift unsafeCode tm := do
    let (res, tm) ← unsafeCode tm.toUnsafe
    return (res, ⟨tm⟩)

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

protected def array (idx elm : Type u)
  [I : ToSafeSrt idx] [E : ToSafeSrt elm]
: Term.ManagerM (Srt.{u} (Srt.Array.{u} idx elm)) := do
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

/-- Constructs a safe term from an unsafe one. -/
private def ofUnsafe [I : ToSafeSrt α] (term : Cvc.Term) : Term α :=
  mkRaw I term



variable (self : Term α)

-- @[inherit_doc Cvc.Term.toString]
protected def toString : String :=
  self.toUnsafe.toString

instance : ToString (Term α) := ⟨Term.toString⟩

-- @[inherit_doc Cvc.Term.ofProof]
def ofProof : Proof → Term Bool :=
  ofUnsafe ∘ Cvc.Term.ofProof

end Term



namespace Smt

def declareFun (symbol : String) (α : Type u) [A : ToSafeSrt α] : SmtM (Term α) := do
  let srt ← A.toSrt
  let srt! := srt.toCvc5
  if srt!.isFunction then
    let domain ← srt!.getFunctionDomainSorts
    let codomain ← srt!.getFunctionCodomainSort

  sorry

end Smt
