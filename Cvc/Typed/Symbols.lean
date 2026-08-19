/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Theory.Arith
public import Cvc.Typed.Solver

import all Cvc.Typed.Core.Defs



namespace Cvc.Typed public section variable [Ω]

namespace Symbols

abbrev Wrap : Type 1 := (α : Type) → [ToTyp α] → [TermToValue α] → Type

abbrev Sig : Type 1 := Wrap → Type

namespace Sig variable (sig : Sig)

abbrev Idents : Type := sig (fun _α => String)

abbrev Terms : Type := sig (Typed.Term ·)

abbrev Values : Type := sig (fun α => α)

end Sig

end Symbols

class Symbols (S : Symbols.Sig) where
  InitData : Type := Unit
  idents : InitData → S.Idents
  mapM {W W' : Symbols.Wrap} [Monad m]
    (s : S W) (f : {α : Type} → [ToTyp α] → [TermToValue α] → W α → m (W' α)) : m (S W')

section variable {S : Symbols.Sig} [inst : Symbols S]

namespace Symbols

namespace Sig
abbrev idents : inst.InitData → S.Idents := inst.idents
abbrev Idents.get := @Sig.idents

abbrev mapM := @inst.mapM

def Idents.declareIn (idents : S.Idents) (solver : Solver) : Env S.Terms :=
  S.mapM idents solver.declareFun

def Idents.declare (idents : S.Idents) : Env S.Terms :=
  S.mapM idents Term.mkSymbol

def Terms.getValues (terms : S.Terms) (solver : Solver) : EnvSat S.Values :=
  S.mapM terms solver.getValue

end Sig

end Symbols

def declareSymbols := @Symbols.Sig.Idents.declare

namespace Solver

def declareSymbols := @Symbols.Sig.Idents.declareIn

def getSymbolValues := @Symbols.Sig.Terms.getValues

end Solver

end



/-! ## Example 1

The code below is an example of the user experience for the `Symbols` API.
-/
namespace Ex1

/-- User-defined symbol structure. -/
structure MySymbols (W : Symbols.Wrap) : Type where
  myBoolVar : W Bool
  myIntVar : W Int
  myRealVar : W Rat

namespace MySymbols

/-- Idents alias. -/
abbrev Idents := Symbols.Sig.Idents MySymbols

/-- Terms alias. -/
abbrev Terms := Symbols.Sig.Terms MySymbols

/-- Values alias. -/
abbrev Values := Symbols.Sig.Values MySymbols

/-- `Symbols` instance giving access to the `Symbols` API. -/
instance : Symbols MySymbols where
  idents _ := { myBoolVar := "myBoolVar", myIntVar := "myIntVar", myRealVar := "myRealVar" }
  mapM syms f := return {
    myBoolVar := ← f syms.myBoolVar
    myIntVar := ← f syms.myIntVar
    myRealVar := ← f syms.myRealVar
  }

/-! With this instance users can very easily declare or get-value their symbols. -/

/-- Declares `MySymbols` in `solver` -/
def declare (idents : MySymbols.Idents) : Env MySymbols.Terms :=
  idents.declare

/-- Tries to extract a satisfiable `MySymbols`-assignment in `solver`. -/
def findCex (syms : MySymbols.Terms) (solver : Solver)
  (assuming : Option (Typed.Terms Bool) := none)
: Env (Option MySymbols.Values) :=
  solver.checkSat? assuming (ifSat := syms.getValues solver)

end MySymbols

end Ex1



/-! ## Example 2 -/
namespace Ex2

structure MySymbols (W : Symbols.Wrap) where
  boolVars : Array (W Bool)
  intVars : Array (W Int)
  realVars : Array (W Rat)

namespace MySymbols

abbrev Idents := Symbols.Sig.Idents MySymbols
abbrev Terms := Symbols.Sig.Terms MySymbols
abbrev Values := Symbols.Sig.Values MySymbols

instance : Symbols MySymbols where
  InitData := Idents
  idents := id
  mapM symbols f := return {
    boolVars := ← symbols.boolVars.mapM f
    intVars := ← symbols.intVars.mapM f
    realVars := ← symbols.realVars.mapM f
  }

/-- Declares `MySymbols` in `solver` -/
def declare (idents : MySymbols.Idents) : Env MySymbols.Terms :=
  idents.declare

/-- Tries to extract a satisfiable `MySymbols`-assignment in `solver`. -/
def findCex (syms : MySymbols.Terms) (solver : Solver)
  (assuming : Option (Typed.Terms Bool) := none)
: Env (Option MySymbols.Values) :=
  solver.checkSat? assuming (ifSat := syms.getValues solver)

end MySymbols

end Ex2
