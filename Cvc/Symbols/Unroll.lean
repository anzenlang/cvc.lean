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
  private getSymbol : Symbol β α

/-- Type alias for a `Symbol.Ident` at some depth. -/
abbrev IdentAt k α := Symbol.At k String α
/-- Type alias for a `Symbol.Term` at some depth. -/
abbrev TermAt k α := Symbol.At k (Term α) α
/-- Type alias for a `Symbol.Val` at some depth. -/
abbrev ValAt k α [Val : Term.ToVal α] := Symbol.At k Val α



def unroll (symbol : Symbol.Ident α) (k : Nat := 0) : IdentAt k α :=
  {symbol with get := At.mkName symbol.name k} |> Symbol.At.mk

namespace At

@[default_instance]
instance : Getter (Symbol.At k β α) β := ⟨fun s => s.getSymbol.get⟩

instance [ToString β] : ToString (Symbol.At k β α) := ⟨fun s => toString s.getSymbol.get⟩

section variable [Monad m] (sym : Symbol.At k β α)

def getName : String := At.mkName sym.getSymbol.name k

/-- Monadic map over the inner symbol. -/
private def mapSymbolM (f : Symbol β α → m (Symbol γ α)) : m (Symbol.At k γ α) := do
  let inner ← f sym.getSymbol
  return {sym with getSymbol := inner}
def mapM (f : β → m γ) : m (Symbol.At k γ α) :=
  sym.mapSymbolM fun s => s.mapM f
def map (sym : Symbol.At k β α) (f : β → γ) : Symbol.At k γ α :=
  sym.mapM (m := Id) f

end

def unroll (sym : Symbol.IdentAt k α) (k' : Nat := 0) : Symbol.IdentAt k' α :=
  sym.getSymbol.unroll k'

def next (sym : Symbol.IdentAt k α) : Symbol.IdentAt k.succ α :=
  sym.getSymbol.unroll k.succ



/-- Declares an unrolled symbol, yielding the corresponding unrolled term.


# TODO

- users are expected to use `Symbol.declareAt`, not this function: privatize/remove?
-/
def declare [Srt.Bij α] (sIdent : Symbol.IdentAt k α) : Smt (Symbol.TermAt k α) :=
  sIdent.mapSymbolM (Symbol.declare ·)

/-- Asserts an unrolled Boolean term. -/
def assert (sTerm : Symbol.TermAt k Bool) : Smt Unit :=
  sTerm.getSymbol.assert

/-- Retrieves the value of an unrolled term. -/
def getValUsing (Val : Term.ToVal α) (sTerm : Symbol.TermAt k α) : Smt.Sat (Symbol.ValAt k α) :=
  sTerm.mapSymbolM (Symbol.getValUsing Val ·)

@[inherit_doc getValUsing]
def getVal [Val : Term.ToVal α] (sTerm : Symbol.TermAt k α) : Smt.Sat (Symbol.ValAt k α) :=
  sTerm.getValUsing Val

end At



namespace IdentsAt
export At (declare unroll next)
end IdentsAt

namespace TermsAt
export At (assert getValUsing getVal)
end TermsAt

/-- Declares a symbol at some depth, yielding the corresponding unrolled term. -/
def declareAt [Srt.Bij α] (sym : Symbol.Ident α) (k : Nat) : Smt (Symbol.TermAt k α) :=
  sym.unroll k |>.declare

@[inherit_doc Symbol.At.getValUsing]
abbrev getValAtUsing := @Symbol.At.getValUsing

@[inherit_doc Symbol.At.getVal]
abbrev getValAt := @Symbol.At.getValUsing

end Symbol



namespace Symbols variable [Syms : Symbols Struct]

abbrev IdentsAt (k : Nat) := let _ := Syms ; Struct (Symbol.IdentAt k ·)
abbrev TermsAt (k : Nat) := let _ := Syms ; Struct (Symbol.TermAt k ·)
abbrev ValsAt (k : Nat) := let _ := Syms ; Struct (Symbol.ValAt k ·)

abbrev FunAtM m (k : Nat) α := Syms.TermsAt k → Term.BuildT m (Term α)
abbrev FunctionAtM := @FunAtM
abbrev FunAt k α := Syms.FunAtM Id k α
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

namespace IdentsAt

def mapM [Monad m] (syms : Syms.IdentsAt k)
  (f : {α : Type} → [Term.ToVal α] → Symbol.IdentAt k α → m (R α))
: m (Struct R) :=
  Syms.mapM syms f

def map (syms : Syms.IdentsAt k)
  (f : {α : Type} → [Term.ToVal α] → Symbol.IdentAt k α → R α)
: Struct R :=
  mapM (m := Id) syms f

def unroll (syms : Syms.Idents) (k : Nat := 0) : Syms.IdentsAt k :=
  Syms.map syms (Symbol.unroll · k)

def next (syms : Syms.IdentsAt k) : Syms.IdentsAt k.succ :=
  map syms Symbol.At.next

def declare (syms : Syms.IdentsAt k) : Smt (Syms.TermsAt k) :=
  mapM syms Symbol.At.declare

def declareAt (syms : Syms.Idents) (k : Nat) : Smt (Syms.TermsAt k) :=
  unroll syms k |>.declare

end IdentsAt

export IdentsAt (unroll next declareAt)

namespace Idents
export IdentsAt (unroll next declareAt)
end Idents

namespace TermsAt

def mapM [Monad m] (terms : Syms.TermsAt k)
  (f : {α : Type} → [Term.ToVal α] → Symbol.TermAt k α → m (R α))
: m (Struct R) :=
  Syms.mapM terms f

def map (terms : Syms.TermsAt k)
  (f : {α : Type} → [Term.ToVal α] → Symbol.TermAt k α → R α)
: Struct R :=
  mapM (m := Id) terms f

def getVals (terms : Syms.TermsAt k) : Smt.Sat (Syms.ValsAt k) :=
  mapM terms Symbol.At.getVal

end TermsAt

def identsAt (k : Nat) : Syms.IdentsAt k :=
  Syms.unroll Syms.idents k

def declareAt (syms : Syms.Idents) (k : Nat) : Smt (Syms.TermsAt k) :=
  Syms.unroll syms k |>.declare

def getValsAt (terms : Syms.TermsAt k) : Smt.Sat (Syms.ValsAt k) :=
  Symbols.TermsAt.getVals terms

end Symbols
