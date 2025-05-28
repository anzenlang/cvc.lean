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
protected structure At (k : Nat) (α : Type) (β : Type := Unit) : Type where
/-- Private constructor so that users don't mess up. -/
private mk ::
  /-- Private conversion to symbols, should not be used directly. -/
  private toSymbol : Symbol α β
  /-- Private name to avoid users overriding conventions. -/
  private name' : String := Symbol.At.mkName toSymbol.name k

/-- Type alias for a `Symbol.Ident` at some depth. -/
abbrev IdentAt k α := Symbol.At k α
/-- Type alias for a `Symbol.Term` at some depth. -/
abbrev TermAt k α := Symbol.At k α (Term α)
/-- Type alias for a `Symbol.Val` at some depth. -/
abbrev ValAt k α [Val : Term.ToVal α] := Symbol.At k α Val



namespace At

/-- Constructor from a regular `Symbol`. -/
def ofSymbol (sym : Symbol α β) (k : Nat) : Symbol.At k α β where
  toSymbol := sym

/-- Constructor from a name, users have no reason to use this directly.

# TODO

- privatize/remove? --- see also `Symbol.mkIdentAt`
-/
def mkIdent (name : String) (k : Nat) : Symbol.IdentAt k α where
  toSymbol := Symbol.mkIdent name



section variable [Monad m] (sym : Symbol.At k α β)

/-- The name of the symbol, adds an unrolling prefix compared to the underlying `Symbol` name. -/
def name : String := sym.name'

/-- Monadic map over the inner symbol.

# TODO

- can be used to inject a bad symbol (not the same name): privatize?
-/
def mapSymbolM (f : Symbol α β → m (Symbol α γ)) : m (Symbol.At k α γ) := do
  let inner ← f sym.toSymbol
  return {sym with toSymbol := inner}

/-- Monadic map over the internal value. -/
def mapM (f : β → m γ) : m (Symbol.At k α γ) :=
  sym.mapSymbolM fun s => s.mapM f

/-- Map over the internal value. -/
def map (f : β → γ) : Symbol.At k α γ :=
  sym.mapM (m := Id) f

end



/-- Declares an unrolled symbol, yielding the corresponding unrolled term.


# TODO

- users are expected to use `Symbol.declareAt`, not this function: privatize/remove?
-/
def declare [Srt.Bij α] (sIdent : Symbol.IdentAt k α) : Smt (Symbol.TermAt k α) :=
  sIdent.mapSymbolM (Symbol.declare ·)

/-- Asserts an unrolled Boolean term. -/
def assert (sTerm : Symbol.TermAt k Bool) : Smt Unit :=
  sTerm.toSymbol.assert

/-- Retrieves the value of an unrolled term. -/
def getValUsing (Val : Term.ToVal α) (sTerm : Symbol.TermAt k α) : Smt.Sat (Symbol.ValAt k α) :=
  sTerm.mapSymbolM (Symbol.getValUsing Val ·)

@[inherit_doc getValUsing]
def getVal [Val : Term.ToVal α] (sTerm : Symbol.TermAt k α) : Smt.Sat (Symbol.ValAt k α) :=
  sTerm.getValUsing Val

end At



@[inherit_doc Symbol.At.mkIdent]
def mkIdentAt (name : String) (k : Nat) : Symbol.IdentAt k α :=
  Symbol.At.mkIdent name k

/-- Unrolls a symbol at some depth. -/
def unroll (sym : Symbol α β) (k : Nat) : Symbol.At k α β where
  toSymbol := sym

/-- Declares a symbol at some depth, yielding the corresponding unrolled term. -/
def declareAt [Srt.Bij α] (sym : Symbol α) (k : Nat) : Smt (Symbol.TermAt k α) :=
  Symbol.At.ofSymbol sym k |>.declare

@[inherit_doc Symbol.At.getValUsing]
abbrev getValAtUsing := @Symbol.At.getValUsing

@[inherit_doc Symbol.At.getVal]
abbrev getValAt := @Symbol.At.getValUsing

end Symbol



namespace Symbols
