/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Symbols.Basic



namespace Cvc



namespace Symbols

protected abbrev Repr := Symbol.Repr → Type

end Symbols

/-- Abstraction over an heterogeneous, strongly-typed function symbol structure.

Users will typically manipulate structures dealing with heterogeneously-typed symbols so that they
can represent, for instance, the state of a transition systems. This class abstracts over such
structures so that `cvc.lean` can provide helpers for declaring function symbols, retrieving their
(strongly-typed) value, *etc.*
-/
class Symbols (Struct : Symbols.Repr) where
  /-- Monadic *map* over a `Struct _`. -/
  mapM {m : Type → Type} [Monad m] (repr : Struct R)
    (f : {α : Type} → [Term.ToVal α] → R α → m (R' α))
  : m (Struct R')
  /-- `ForIn`-like iteration/fold over `ESymbol _` elements. -/
  forIn {m : Type → Type} [Monad m] (symbols : Struct R)
    (init : β) (f : {α : Type} → [Term.ToVal α] → R α → β → m (ForInStep β))
  : m β
  /-- Symbol identifier initialization. Don't use this directly, use `idents` instead. -/
  idents' : Struct (Symbol.Ident ·)

namespace Symbols variable [Syms : Symbols Struct]

/-- Maps over the symbols in a `Struct F`. -/
def map (symbols : Struct R)
  (f : {α : Type} → [Term.ToVal α] → R α → G α)
: Struct G :=
  Syms.mapM (m := Id) symbols f

@[default_instance]
instance instForIn : ForIn m (Struct R) ((α : Type) × (_ : Term.ToVal α) × (R α)) where
  forIn symbols init f :=
    Syms.forIn symbols init
      fun repr acc => f ⟨_, inferInstance, repr⟩ acc

abbrev Idents := let _ := Syms ; Struct (Symbol.Ident ·)
abbrev Terms := let _ := Syms ; Struct (Symbol.Term ·)
abbrev Vals := let _ := Syms ; Struct (Symbol.Val ·)

def idents : Syms.Idents := idents'

abbrev FunT m α := Syms.Terms → Term.BuildT m (Term α)
abbrev FunctionT := @FunT
abbrev Fun α := Syms.FunT (m := Id) α
abbrev Function := @Fun

abbrev Pred := Syms.Fun Bool
abbrev Predicate := @Pred

abbrev Rel := Syms.Terms → Syms.Pred
abbrev Relation := @Rel



/-! ## `Ident`-specific helpers -/
namespace Idents variable (idents : Syms.Idents)

def mapM [Monad m]
  (f : {α : Type} → [Term.ToVal α] → Symbol.Ident α → m (R α))
: m (Struct R) :=
  Syms.mapM idents (fun sym => f sym)

def map (f : {α : Type} → [Term.ToVal α] → Symbol.Ident α → R α) : Struct R :=
  mapM (m := Id) idents f

def declare : Smt Syms.Terms := mapM idents (fun ident => Symbol.declare ident)

end Idents

export Idents (declare)



/-! ## `Term`-specific helpers -/
namespace Terms variable (terms : Syms.Terms)

def mapM [Monad m]
  (f : {α : Type} → [Term.ToVal α] → Symbol.Term α → m (R α))
: m (Struct R) :=
  Syms.mapM terms f

def map (f : {α : Type} → [Term.ToVal α] → Symbol.Term α → R α) : Struct R :=
  mapM (m := Id) terms f

/-- Retrieves the values of all symbols in a *sat* context. -/
def getVals : Smt.Sat Syms.Vals := mapM terms Symbol.getVal

@[inherit_doc getVals]
def getVal := @getVals

end Terms

end Symbols
