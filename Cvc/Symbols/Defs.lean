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
class Symbols.{u, v} (Struct : Symbols.Repr) where
  /-- Monadic *map* over a `Struct _`. -/
  mapM {m : Type → Type} [Monad m]
    (repr : Struct F) (f : {α : Type} → [Term.ToVal α] → Symbol α (F α) → m (Symbol α (G α)))
  : m (Struct G)
  /-- `ForIn`-like iteration function over `ESymbol _` elements. -/
  forIn {m : Type u → Type v} [Monad m]
    (symbols : Struct F) (init : β) (f : ESymbol F → β → m (ForInStep β))
  : m β
  /-- Symbol identifier initialization. Don't use this directly, use `idents` instead. -/
  idents' : Struct Symbol.Repr.default

/-- An array of `ESymbol R`-s. -/
abbrev ESymbols (Repr : Symbol.Repr) : Type 1 :=
  Array (ESymbol Repr)

namespace Symbols variable [Syms : Symbols Struct]

/-- Maps over the symbols in a `. -/
def map (symbols : Struct F)
  (f : {α : Type} → [Term.ToVal α] → Symbol α (F α) → Symbol α (G α))
: Struct G :=
  Syms.mapM (m := Id) symbols f

@[default_instance]
instance instForIn : ForIn m (Struct F) (ESymbol F) :=
  ⟨Syms.forIn⟩

def erase (symbols : Struct F) : ESymbols F := Id.run do
  let mut array := #[]
  for symbol in symbols do
    array := array.push symbol
  return array

abbrev Idents := let _ := Syms ; Struct default
abbrev Terms := let _ := Syms ; Struct Symbol.Repr.Term
abbrev Vals := let _ := Syms ; Struct Symbol.Repr.Val

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
  (f : {α : Type} → [Term.ToVal α] → Symbol.Ident α → m (Symbol α (G α)))
: m (Struct G) :=
  Syms.mapM idents f

def map (f : {α : Type} → [Term.ToVal α] → Symbol.Ident α → Symbol α (G α)) : Struct G :=
  idents.mapM (m := Id) f

def declare : Smt Syms.Terms := idents.mapM (Symbol.declare ·)

end Idents

export Idents (declare)



/-! ## `Term`-specific helpers -/
namespace Terms variable (terms : Syms.Terms)

def mapM [Monad m]
  (f : {α : Type} → [Term.ToVal α] → Symbol.Term α → m (Symbol α (G α)))
: m (Struct G) :=
  Syms.mapM terms f

def map (f : {α : Type} → [Term.ToVal α] → Symbol.Term α → Symbol α (G α)) : Struct G :=
  terms.mapM (m := Id) f

/-- Retrieves the values of all symbols in a *sat* context. -/
def getVals : Smt.Sat Syms.Vals :=
  terms.mapM Cvc.Symbol.getVal

@[inherit_doc getVals]
def getVal := @getVals

end Terms

end Symbols
