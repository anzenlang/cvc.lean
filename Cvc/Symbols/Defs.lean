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
abbrev Model := let _ := Syms ; Struct (Symbol.Val ·)
abbrev Values := let _ := Syms ; Struct (Symbol.Value ·)

abbrev FunT m α := Syms.Terms → Term.BuildT m (Term α)
abbrev FunctionT := @FunT
abbrev PredT m := Syms.FunT m Bool
abbrev PredicateT := @PredT
abbrev RelT m := Syms.Terms → Syms.PredT m
abbrev RelationT := @RelT

abbrev Fun α := Syms.FunT (m := Id) α
abbrev Function := @Fun
abbrev Pred := Syms.PredT (m := Id)
abbrev Predicate := @Pred
abbrev Rel := Syms.RelT (m := Id)
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
def getModel : Smt.Sat Syms.Model := mapM terms Symbol.getVal

/-- Retrieves the values of all symbols in a *sat* context. -/
def getVals : Smt.Sat Syms.Vals := mapM terms Symbol.getVal

/-- Retrieves the values of all symbols in a *sat* context. -/
def getValues : Smt.Sat Syms.Values := mapM terms Symbol.getValue

end Terms



namespace AliasDsl

open Lean.Parser
open Command
open Lean.Elab.Command (elabCommand)

namespace Idents
def id_Idents := Lean.mkIdent `Idents
def id_Terms := Lean.mkIdent `Terms
def id_Model := Lean.mkIdent `Model

def id_FunT := Lean.mkIdent `FunT
def id_FunctionT := Lean.mkIdent `FunctionT
def id_PredT := Lean.mkIdent `PredT
def id_PredicateT := Lean.mkIdent `PredicateT
def id_RelT := Lean.mkIdent `RelT
def id_RelationT := Lean.mkIdent `RelationT

def id_Fun := Lean.mkIdent `Fun
def id_Function := Lean.mkIdent `Function
def id_Pred := Lean.mkIdent `Pred
def id_Predicate := Lean.mkIdent `Predicate
def id_Rel := Lean.mkIdent `Rel
def id_Relation := Lean.mkIdent `Relation

def id_monad := Lean.mkIdent `m
def id_α := Lean.mkIdent `α

def idRef_Term := Lean.mkIdent ``Cvc.Term
def idRef_Term_BuildT := Lean.mkIdent ``Cvc.Term.BuildT
def idRef_Symbol := Lean.mkIdent ``Cvc.Symbol
def idRef_Symbol_Repr := Lean.mkIdent ``Cvc.Symbol.Repr
def idRef_Symbol_mkIdent := Lean.mkIdent ``Cvc.Symbol.mkIdent
def idRef_Symbols := Lean.mkIdent ``Cvc.Symbols
end Idents

/-- Generates all `Cvc.Symbols` aliases. -/
syntax (name := aliasDsl)
  "Cvc.Symbols.aliasesFor! " ident " ← " term:max
: command

open Idents in
@[command_elab aliasDsl, inherit_doc aliasDsl]
def elabAliasDsl : Lean.Elab.Command.CommandElab
| `(
  Cvc.Symbols.aliasesFor! $SymbolsIdent ← $TermsType
) => do
  let symbols := SymbolsIdent.getId
  let fullId_FunT := Lean.mkIdent <| symbols.append id_FunT.getId
  let fullId_PredT := Lean.mkIdent <| symbols.append id_PredT.getId
  let fullId_RelT := Lean.mkIdent <| symbols.append id_RelT.getId
  let stx ← `(
    protected abbrev $id_FunT $id_monad $id_α :=
      $TermsType → $idRef_Term_BuildT $id_monad ($idRef_Term $id_α)
    protected abbrev $id_FunctionT := @$fullId_FunT
    protected abbrev $id_PredT $id_monad:ident :=  $fullId_FunT $id_monad Bool
    protected abbrev $id_PredicateT $id_monad:ident := $fullId_FunT $id_monad Bool
    protected abbrev $id_RelT $id_monad:ident := $TermsType → $fullId_PredT $id_monad
    protected abbrev $id_RelationT $id_monad:ident := $TermsType → $fullId_PredT $id_monad

    protected abbrev $id_Fun $id_α:ident := $fullId_FunT ($id_monad := Id) $id_α
    protected abbrev $id_Function $id_α:ident := $fullId_FunT ($id_monad := Id) $id_α
    protected abbrev $id_Pred := $fullId_PredT ($id_monad := Id)
    protected abbrev $id_Predicate := $fullId_PredT ($id_monad := Id)
    protected abbrev $id_Rel := $fullId_RelT ($id_monad := Id)
    protected abbrev $id_Relation := $fullId_RelT ($id_monad := Id)
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax

end AliasDsl

end Symbols
