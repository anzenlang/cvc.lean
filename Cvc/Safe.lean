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



/-! ## Term Manager -/
namespace Term

structure Manager : Type where
private ofUnsafe ::
  toUnsafe : Cvc.Term.Manager

def Manager.mk : BaseIO Manager :=
  (Manager.ofUnsafe ∘ ULift.up) <$> Cvc.Term.Manager.mk

/-- `Manager` error/state monad transformer. -/
abbrev ManagerT (m : Type → Type) :=
  ExceptT Error (StateT Manager m)

abbrev ManagerM := ManagerT Id

instance [Monad m] : MonadLift ManagerM (ManagerT m) where
  monadLift code tm := return code tm

private instance : MonadLift Cvc.Term.ManagerM ManagerM where
  monadLift code tm :=
    let (res, tm!) := code tm.toUnsafe
    (res, Manager.ofUnsafe tm!)

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

class HToSafeSrt (α : Type) (β : Type) where
  toSrt : Term.ManagerM (Srt β)

class HToSafeFoSrt (α : Type) (β : Type) extends HToSafeSrt α β

class ToSafeSrt (α : Type) extends HToSafeSrt α α

class ToSafeFoSrt (α : Type) extends ToSafeSrt α

/-- A cvc term of a sort corresponding to a lean type. -/
structure Term (α : Type) where
private mkRaw ::
  -- private toUnsafe : Cvc.Term
  private inner : Cvc.Term
  private args : Array Cvc.Term := #[]


class ToSafeTerm (α : Type) (β : Type) extends HToSafeSrt α β where
  toTerm : α → Term.ManagerM (Srt β)



/-! ## Sort construction -/
namespace Srt

protected def toString : Srt α → String :=
  toString ∘ Srt.toUnsafe

instance : ToString (Srt α) :=
  ⟨Srt.toString⟩



private def ofCvc5' (α : Type) : cvc5.Sort → Srt α :=
  ofUnsafe ∘ ULift.up

private def ofCvc5 : cvc5.Sort → Srt α :=
  ofCvc5' α

private def toCvc5 (srt : Srt α) : cvc5.Sort :=
  srt.toUnsafe.down

protected def cvc5Signature : Srt α → Term.ManagerM (Array cvc5.Sort × cvc5.Sort) :=
  (toUnsafe · |>.cvc5Signature)

instance instCoeSort {α : Type} : CoeSort (Srt α) Type where
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

private instance [Monad m] : MonadLift (Cvc.Term.ManagerT m) (Term.ManagerT m) where
  monadLift unsafeCode tm := do
    let (res, tm) ← unsafeCode tm.toUnsafe
    return (res, ⟨tm⟩)

protected def bool : Term.ManagerM (Srt Bool) := do
  let srt ← Cvc.Srt.bool
  return Srt.ofUnsafe srt

instance : ToSafeFoSrt Bool where
  toSrt := Srt.bool

protected def int : Term.ManagerM (Srt Int) := do
  let srt ← Cvc.Srt.int
  return Srt.ofUnsafe srt

instance : ToSafeFoSrt Int where
  toSrt := Srt.int
instance : HToSafeFoSrt Nat Int where
  toSrt := Srt.int

protected def real : Term.ManagerM (Srt Rat) := do
  let srt ← Cvc.Srt.real
  return Srt.ofUnsafe srt

instance : ToSafeFoSrt Rat where
  toSrt := Srt.real

protected def string : Term.ManagerM (Srt String) := do
  let srt ← Cvc.Srt.string
  return Srt.ofUnsafe srt

instance : ToSafeFoSrt String where
  toSrt := Srt.string

protected opaque Array (I : α) (E : β) : Type (max u v) :=
  PUnit

protected def array (idx elm : Type)
  [I : ToSafeFoSrt idx] [E : ToSafeFoSrt elm]
: Term.ManagerM (Srt (Srt.Array idx elm)) := do
  let idx ← I.toSrt
  let elm ← E.toSrt
  let srt ← Cvc.Srt.array idx.toUnsafe elm.toUnsafe
  return Srt.ofUnsafe srt

instance [ToSafeFoSrt I] [ToSafeFoSrt E] : ToSafeFoSrt (Srt.Array I E) where
  toSrt := Srt.array I E

protected def bitVec
  (size : UInt32) (valid : 0 < size)
: Term.ManagerM (Srt (BitVec size.toNat)) := do
  let srt ← Cvc.Srt.bitVec size valid
  return Srt.ofUnsafe srt

instance {size : UInt32} (valid : 0 < size) : ToSafeFoSrt (BitVec size.toNat) where
  toSrt := Srt.bitVec size valid



structure Partial (Args : Type u) (Sig : Type u) where
  args : Args

end Srt

namespace Term

def ofUnsafe'
  (α : Type) [ToSafeSrt α]
  (inner : Cvc.Term) (args : Array Cvc.Term := #[])
: Term α :=
  { inner, args }

def ofUnsafe [ToSafeSrt α]
  (inner : Cvc.Term) (args : Array Cvc.Term := #[])
: Term α :=
  { inner, args }

private def finalize [ToSafeFoSrt α] (self : Term α) : ManagerM (Term α) :=
  if ¬ self.args.isEmpty then
    ManagerT.ofUnsafe do
      let term ← Cvc.Term.mk cvc5.Kind.APPLY_UF <| #[self.inner] ++ self.args
      return ofUnsafe term
  else
    return ofUnsafe self.inner

def toUnsafe [ToSafeFoSrt α] (self : Term α) : ManagerM Cvc.Term := do
  let self ← self.finalize
  return self.inner

def getSrt (self : Term α) : ManagerM (Srt α) := do
  if self.args.isEmpty then
    return Srt.ofUnsafe self.inner.getSrt
  else
    let (dom, cod) ← self.inner.getSrt.cvc5Signature
    let dom := dom.toSubarray (start := self.args.size) |>.toArray
    if dom.isEmpty then
      return Srt.ofCvc5 cod
    else
      let tm ← get
      match cvc5.TermManager.mkFunctionSort tm.toCvc5 dom cod with
      | .ok res => return Srt.ofCvc5 res
      | .error e => throw (Error.ofCvc5 e)

protected def apply [ToSafeFoSrt α]
  (self : Term (α → β)) (arg : Term α)
: ManagerM (Term β) := do
  let arg ← arg.toUnsafe
  let args := self.args.push arg
  return { inner := self.inner , args}

instance [ToSafeFoSrt α] : CoeFun (Term (α → β)) (fun _ => Term α → ManagerM (Term β)) where
  coe f := (f.apply ·)

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

instance instMonadLiftSmtT : MonadLift (Cvc.SmtT m) (SmtT m) where
  monadLift code smt := do
    let (res, smt!) ← code smt.toUnsafe
    return (res, Smt.ofUnsafe smt!)

private instance : MonadLift (cvc5.SolverT m) (SmtT m) where
  monadLift code smt := do
    let (res, smt) ← (Cvc.SmtT.instMonadLiftCvc5.monadLift code) smt.toUnsafe
    return (res, Smt.ofUnsafe smt)

instance instMonadLiftSmtMToSmtIO : MonadLift SmtM SmtIO where
  monadLift code smt := do
    return code smt



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



namespace Term

section explicit

private def ofCvc5' (α : Type) [ToSafeSrt α] : cvc5.Term → Term α :=
  ofUnsafe' α ∘ Cvc.Term.ofCvc5
end explicit

private def ofCvc5 [ToSafeSrt α] : cvc5.Term → Term α :=
  ofCvc5' α

private def toCvc5 [ToSafeFoSrt α] (self : Term α) : ManagerM cvc5.Term :=
  Cvc.Term.toCvc5 <$> self.toUnsafe



variable (self : Term α)

-- @[inherit_doc Cvc.Term.toString]
protected def toString : String :=
  if self.args.isEmpty then
    self.inner.toString
  else
    "(" ++ (
      self.inner.toString
      |> self.args.foldl fun acc arg => acc ++ " " ++ arg.toString
    ) ++ ")"

instance : ToString (Term α) := ⟨Term.toString⟩

-- @[inherit_doc Cvc.Term.ofProof]
def ofProof : Proof → Term Bool :=
  ofUnsafe ∘ Cvc.Term.ofProof

def not (self : Term Bool) : ManagerM (Term Bool) := do
  let self ← self.toUnsafe
  let t! ← self.not
  return ofUnsafe t!

def and (self that : Term Bool) : ManagerM (Term Bool) := do
  let self! ← self.toUnsafe
  let that! ← that.toUnsafe
  let t! ← self!.and that!
  return ofUnsafe t!

def or (self that : Term Bool) : ManagerM (Term Bool) := do
  let self! ← self.toUnsafe
  let that! ← that.toUnsafe
  let t! ← self!.or that!
  return ofUnsafe t!

def xor (self that : Term Bool) : ManagerM (Term Bool) := do
  let self! ← self.toUnsafe
  let that! ← that.toUnsafe
  let t! ← self!.xor that!
  return ofUnsafe t!

end Term



namespace Smt

def setLogic (logic : Logic) : SmtM Unit := do
  liftM (Cvc.Smt.setLogic logic)

def declareFun [Monad m] (symbol : String) (α : Type) [A : ToSafeSrt α] : SmtT m (Term α) := do
  let a ← A.toSrt
  let (domain, codomain) ← a.cvc5Signature
  Term.ofCvc5 <$> cvc5.Solver.declareFun symbol domain codomain false (m := m)

def assert (formula : Term Bool) : SmtM Unit := do
  Cvc.Smt.assert (← formula.toUnsafe)

def checkSat? : SmtM (Option Bool) := do
  Cvc.Smt.checkSat?

end Smt
