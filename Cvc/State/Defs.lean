/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Symbols.Defs



namespace Cvc

namespace Symbol



/-- Generates the unrolled version of a symbol's name.

Argument `name` should be the `Symbol.name` of a not-unrolled symbol.
-/
protected def At.mkName (name : String) (k : Nat) : String :=
  s!"{name}_unrolled_at_{k}"

/-- A symbol unrolled at some *depth* `k`, whatever *depth* means. -/
protected structure At (k : Nat) (β α : Type) : Type where
/-- Private constructor so that users don't mess up. -/
private mk ::
  /-- Private conversion to syms, not reason to use this directly currently. -/
  getSymbol : Symbol β α

/-- Type alias for a `Symbol.Ident` at some depth. -/
abbrev IdentAt k α := Symbol.At k String α
/-- Type alias for a `Symbol.Term` at some depth. -/
abbrev TermAt (k : semiOutParam Nat) α := Symbol.At k (Term α) α
/-- Type alias for a `Symbol.Val` at some depth. -/
abbrev ValueAt k α := Symbol.At k (Value α) α

instance : CoeDep (Symbol.TermAt k α) term (Term α) := ⟨term.getSymbol.get⟩



namespace At

@[default_instance]
instance : Getter (Symbol.At k β α) β := ⟨fun s => s.getSymbol.get⟩

instance [ToString β] : ToString (Symbol.At k β α) := ⟨fun s => toString s.getSymbol.get⟩

section variable [Monad m] (sym : Symbol.At k β α)

def name : String := At.mkName sym.getSymbol.name k

/-- Monadic map over the inner symbol. -/
private def mapSymbolM (f : Symbol β α → m (Symbol γ α)) : m (Symbol.At k γ α) := do
  let inner ← f sym.getSymbol
  return {sym with getSymbol := inner}
def mapM (f : β → m γ) : m (Symbol.At k γ α) :=
  sym.mapSymbolM fun s => s.mapM f
def map (sym : Symbol.At k β α) (f : β → γ) : Symbol.At k γ α :=
  sym.mapM (m := Id) f

end

end At



namespace IdentAt variable [IsSrt α] (ident : Symbol.IdentAt k α)

def ofIdent (ident : Symbol.Ident α) (k : Nat := 0) : Symbol.IdentAt k α :=
  {ident with get := At.mkName ident.name k} |> Symbol.At.mk

def getIdent : Symbol.Ident α :=
  Symbol.Ident.mk ident.name

def unroll (k' : Nat := k.succ) : Symbol.IdentAt k' α :=
  ofIdent ident.getIdent k'

def next : Symbol.IdentAt k.succ α :=
  ident.unroll

def declare : Smt (Symbol.TermAt k α) := ident.mapSymbolM (Symbol.declare ·)

end IdentAt

namespace Ident

def unroll (ident : Symbol.Ident α) (k : Nat := 0) : Symbol.IdentAt k α :=
  IdentAt.ofIdent ident k

def declareAt [IsSrt α] (ident : Symbol.Ident α) (k : Nat := 0) : Smt (Symbol.TermAt k α) :=
  ident.unroll k |>.declare

end Ident

namespace At
export IdentAt (ofIdent getIdent unroll next declare)
end At



namespace TermAt variable [IsSrt α] (term : Symbol.TermAt k α)

def getValue : Smt.Sat (Symbol.ValueAt k α) :=
  term.mapSymbolM (Symbol.getValue)

end TermAt

-- namespace At
-- export TermAt (getValue)
-- end At

end Symbol



namespace Symbols variable [Syms : Symbols Struct]

abbrev IdentsAt (k : Nat) := let _ := Syms ; Struct (Symbol.IdentAt k ·)
abbrev TermsAt (k : Nat) := let _ := Syms ; Struct (Symbol.TermAt k ·)
abbrev ModelAt (k : Nat) := let _ := Syms ; Struct (Symbol.ValueAt k ·)
abbrev ValuesAt (k : Nat) := Syms.ModelAt k

abbrev FunMAt m (k : Nat) α := Syms.TermsAt k → Term.BuildT m (Term α)
abbrev FunctionMAt := @FunMAt
abbrev FunAt k α := Syms.FunMAt Id k α
abbrev FunctionAt := @FunAt

abbrev PredAt (k : Nat) := Syms.FunAt k Bool
abbrev PredicateAt := @PredAt
abbrev StatePred := {k : Nat} → Syms.PredAt k
abbrev StatePredicate := Syms.StatePred

abbrev RelAt (k : Nat) := Syms.TermsAt k → Syms.PredAt k.succ
abbrev RelationAt := @RelAt
abbrev StateRel := {k : Nat} → Syms.RelAt k
abbrev StateRelation := Syms.StateRel

abbrev InvRelAt (k : Nat) := Syms.TermsAt k.succ → Syms.PredAt k
abbrev InvRelationAt := @InvRelAt
abbrev StateInvRel := {k : Nat} → Syms.InvRelAt k
abbrev StateInvRelation := Syms.StateInvRel

abbrev NamedPreds := RBMap String Syms.StatePred
abbrev NamedPredicates := Syms.NamedPreds

namespace IdentsAt

def mapM [Monad m] (syms : Syms.IdentsAt k)
  (f : {α : Type} → [IsSrt α] → Symbol.IdentAt k α → m (R α))
: m (Struct R) :=
  Syms.mapM syms f

def map (syms : Syms.IdentsAt k)
  (f : {α : Type} → [IsSrt α] → Symbol.IdentAt k α → R α)
: Struct R :=
  mapM (m := Id) syms f

def unroll (syms : Syms.Idents) (k : Nat := 0) : Syms.IdentsAt k :=
  Syms.map syms (Symbol.Ident.unroll · k)

def next (syms : Syms.IdentsAt k) : Syms.IdentsAt k.succ :=
  map syms .next

private def declare (syms : Syms.IdentsAt k) : Smt (Syms.TermsAt k) :=
  mapM syms Symbol.IdentAt.declare

def declareAt (syms : Syms.Idents) (k : Nat) : Smt (Syms.TermsAt k) :=
  unroll syms k |>.declare

end IdentsAt

export IdentsAt (unroll next declareAt)

namespace Idents
export IdentsAt (unroll next declareAt)
end Idents

namespace TermsAt

def mapM [Monad m] (terms : Syms.TermsAt k)
  (f : {α : Type} → [IsSrt α] → Symbol.TermAt k α → m (R α))
: m (Struct R) :=
  Syms.mapM terms f

def map (terms : Syms.TermsAt k)
  (f : {α : Type} → [IsSrt α] → Symbol.TermAt k α → R α)
: Struct R :=
  mapM (m := Id) terms f

/-- Retrieves the value of each symbol at some depth. -/
def getModel (terms : Syms.TermsAt k) : Smt.Sat (Syms.ValuesAt k) :=
  mapM terms Symbol.TermAt.getValue

@[inherit_doc getModel]
def getValues := @getModel

end TermsAt

end Symbols



namespace State



namespace AliasDsl

open Lean.Parser
open Command
open Lean.Elab.Command (elabCommand)

namespace Idents
def id_FunAtT := Lean.mkIdent `FunAtT
def id_FunctionAtT := Lean.mkIdent `FunctionAtT
def id_PredAtT := Lean.mkIdent `PredAtT
def id_PredicateAtT := Lean.mkIdent `PredicateAtT
def id_RelAtT := Lean.mkIdent `RelAtT
def id_RelationAtT := Lean.mkIdent `RelationAtT

def id_FunAt := Lean.mkIdent `FunAt
def id_FunctionAt := Lean.mkIdent `FunctionAt
def id_PredAt := Lean.mkIdent `PredAt
def id_PredicateAt := Lean.mkIdent `PredicateAt
def id_RelAt := Lean.mkIdent `RelAt
def id_RelationAt := Lean.mkIdent `RelationAt

def id_StatePredT := Lean.mkIdent `StatePredT
def id_StatePredicateT := Lean.mkIdent `StatePredicateT
def id_StateRelT := Lean.mkIdent `StateRelT
def id_StateRelationT := Lean.mkIdent `StateRelationT

def id_StatePred := Lean.mkIdent `StatePred
def id_StatePredicate := Lean.mkIdent `StatePredicate
def id_StateRel := Lean.mkIdent `StateRel
def id_StateRelation := Lean.mkIdent `StateRelation

def id_k := Lean.mkIdent `k
end Idents

/-- Generates all `Cvc.Symbols` aliases. -/
syntax (name := aliasDsl)
  "Cvc.State.aliasesFor! " ident " ← " term:max
: command

open Cvc.Symbols.AliasDsl.Idents (id_monad id_α idRef_Term_BuildT idRef_Term) in
open Idents in
@[command_elab aliasDsl, inherit_doc aliasDsl]
def elabAliasDsl : Lean.Elab.Command.CommandElab
| `(
  Cvc.State.aliasesFor! $SymbolsIdent ← $TermsAtType
) => do
  let symbols := SymbolsIdent.getId
  let fullId_FunAtT := Lean.mkIdent <| symbols.append id_FunAtT.getId
  let fullId_PredAtT := Lean.mkIdent <| symbols.append id_PredAtT.getId
  let fullId_RelAtT := Lean.mkIdent <| symbols.append id_RelAtT.getId
  let fullId_StatePredT := Lean.mkIdent <| symbols.append id_StatePredT.getId
  let fullId_StateRelT := Lean.mkIdent <| symbols.append id_StateRelT.getId
  let stx ← `(
    protected abbrev $id_FunAtT $id_monad $id_α $id_k :=
      $TermsAtType $id_k → $idRef_Term_BuildT $id_monad ($idRef_Term $id_α)
    protected abbrev $id_FunctionAtT := @$fullId_FunAtT
    protected abbrev $id_PredAtT $id_monad:ident $id_k:ident := $fullId_FunAtT $id_monad Bool $id_k
    protected abbrev $id_PredicateAtT $id_monad:ident $id_k:ident :=
      $fullId_FunAtT $id_monad Bool $id_k
    protected abbrev $id_RelAtT $id_monad:ident $id_k:ident :=
      $TermsAtType $id_k → $fullId_PredAtT $id_monad (Nat.succ $id_k)
    protected abbrev $id_RelationAtT $id_monad:ident $id_k:ident :=
      $TermsAtType $id_k → $fullId_PredAtT $id_monad (Nat.succ $id_k)

    protected abbrev $id_FunAt $id_α:ident $id_k:ident :=
      $fullId_FunAtT ($id_monad := Id) $id_α $id_k
    protected abbrev $id_FunctionAt $id_α:ident $id_k:ident :=
      $fullId_FunAtT ($id_monad := Id) $id_α $id_k
    protected abbrev $id_PredAt $id_k:ident := $fullId_PredAtT ($id_monad := Id) $id_k
    protected abbrev $id_PredicateAt $id_k:ident := $fullId_PredAtT ($id_monad := Id) $id_k
    protected abbrev $id_RelAt $id_k:ident := $fullId_RelAtT ($id_monad := Id) $id_k
    protected abbrev $id_RelationAt $id_k:ident := $fullId_RelAtT ($id_monad := Id) $id_k

-- abbrev StatePred := {k : Nat} → Syms.PredAt k
-- abbrev StatePredicate := Syms.StatePred
-- abbrev StateRel := {k : Nat} → Syms.RelAt k
-- abbrev StateRelation := Syms.StateRel

    protected abbrev $id_StatePredT $id_monad:ident :=
      {$id_k : Nat} → $fullId_PredAtT $id_monad $id_k
    protected abbrev $id_StatePredicateT $id_monad:ident :=
      {$id_k : Nat} → $fullId_PredAtT $id_monad $id_k
    protected abbrev $id_StateRelT $id_monad:ident :=
      {$id_k : Nat} → $fullId_RelAtT $id_monad $id_k
    protected abbrev $id_StateRelationT $id_monad:ident :=
      {$id_k : Nat} → $fullId_PredAtT $id_monad $id_k

    protected abbrev $id_StatePred := $fullId_StatePredT ($id_monad := Id)
    protected abbrev $id_StatePredicate := $fullId_StatePredT ($id_monad := Id)
    protected abbrev $id_StateRel := $fullId_StateRelT ($id_monad := Id)
    protected abbrev $id_StateRelation := $fullId_StateRelT ($id_monad := Id)
  )
  elabCommand stx
| _ => Lean.Elab.throwUnsupportedSyntax

end AliasDsl
