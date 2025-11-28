/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Defs



namespace Cvc



structure Symbol [Cvc.Scope] (α : Type) where
  get : α
  sort : Srt


namespace Symbol variable [Cvc.Scope]

instance : Coe (Symbol α) α := ⟨get⟩

def Ident := Symbol String

def Term := Symbol Cvc.Term

/-- The `Cvc.Term` in a `Term`. -/
def toTerm (symbol : Term) : Cvc.Term := symbol.get

def Val := Symbol Cvc.Term

structure TermAt (k : Nat) extends Term where
private mk' ::

structure ValAt (k : Nat) extends Val

def declare (symbol : Ident) : Env Term :=
  return { symbol with get := ← Term.symbol symbol.get symbol.sort }

def declareAt (symbol : Ident) (k : Nat) : Env (TermAt k) := do
  let ident := s!"{symbol.get}__@__{k}"
  return { get := ← Term.symbol ident symbol.sort, sort := symbol.sort }

def getValue (symbol : Term) (solver : Solver) : Env.Sat Val :=
  return { symbol with get := ← solver.getValue symbol.get }

namespace TermAt variable (symbol : TermAt k)

def mk (symbol : String) (k : Nat) (sort : Srt) : Env (TermAt k) := do
  declareAt ⟨symbol, sort⟩ k

/-- The `Cvc.Term` in a `TermAt _`. -/
def toTerm : Cvc.Term := symbol.get

instance : CoeDep (TermAt k) symbol Cvc.Term := ⟨symbol.toTerm⟩

def getValue (solver : Solver) : Env.Sat (ValAt k) := do
  return ⟨← Symbol.getValue symbol.toSymbol solver⟩

end TermAt

end Symbol
