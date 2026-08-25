/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Cvc.Gen.Symbols
public import Cvc.Typed.Solver




/-! # Symbols, typed

A *symbol structure* is a record of the symbols a problem is stated over, written once and read at
three different instantiations: at identifiers (`Idents`), at terms (`Terms`) and at the Lean
values a model gives them (`Values`). `Symbols.Wrap` is what makes one record serve all three, and
the `Symbols` class supplies the `mapM` that walks it.

**A symbol structure's whole obligation is its `Symbols` instance**, and `structure.symbols`
generates that, so an ordinary one is written with no boilerplate at all:

```lean
structure.symbols MySymbols where
  /-- A boolean symbol. -/
  myBoolVar : Bool
  /-- A real symbol. -/
  myRealVar : Rat
```

The structure, the aliases and the instance are generated; `declare`, `getValues` and `findCex`
are generic over the `Sig`, so they need no per-structure definition either.

**`Ω` is taken only where a term is actually mentioned.** `Wrap` takes none, so `Idents` and
`Values` take none either — only `Terms` does, along with `mapM` and the operations that build or
read terms. A caller can therefore name a structure's identifiers and read its values outside a
scope, entering one only to solve.

Worked examples, including the hand-written path for what `structure.symbols` cannot express, are
in `Cvc.Tests.Typed.Symbols`.
-/
namespace Cvc.Typed public section

namespace Symbols

abbrev Wrap : Type 1 := (α : Type) → [ToTyp α] → [TermToValue α] → Type

abbrev Sig : Type 1 := Wrap → Type

namespace Sig variable (sig : Sig)

abbrev Idents : Type := sig (fun _α => String)

abbrev Terms [Ω] : Type := sig (Typed.Term ·)

abbrev Values : Type := sig (fun α => α)

abbrev Fun (α : Type) : Type := [Ω] → sig.Terms → Env (Term α)

abbrev Pred : Type := [Ω] → sig.Fun Bool

end Sig

end Symbols

class Symbols (S : Symbols.Sig) where
  InitData : Type := Unit
  idents : InitData → S.Idents
  mapM {W W' : Symbols.Wrap} [Monad m]
    (s : S W) (f : {α : Type} → [ToTyp α] → [TermToValue α] → W α → m (W' α)) : m (S W')

section variable {S : Symbols.Sig} [inst : Symbols S]

namespace Symbols

abbrev Idents [Symbols S] := Sig.Idents S
abbrev Terms [Ω] [Symbols S] := Sig.Terms S
abbrev Values [Symbols S] := Sig.Values S
abbrev Fun [Symbols S] := Sig.Fun S
abbrev Pred [Symbols S] := Sig.Pred S

namespace Sig
abbrev idents : inst.InitData → S.Idents := inst.idents
abbrev Idents.get := @Sig.idents

abbrev mapM := @inst.mapM

def Idents.declareIn [Ω] (idents : S.Idents) (solver : Solver) : Env S.Terms :=
  S.mapM idents solver.declareFun

def Idents.declare [Ω] (idents : S.Idents) : Env S.Terms :=
  S.mapM idents Term.mkSymbol

def Terms.getValues [Ω] (terms : S.Terms) (solver : Solver) : solver.EnvSat S.Values :=
  S.mapM terms solver.getValue

/-- Checks satisfiability and, where sat, reads every symbol's value out of the model.

Needs no per-`Sig` code: `mapM` is what makes it generic, so a user's symbol structure gets this
by instancing `Symbols` and nothing else.
-/
def Terms.findCex [Ω] (terms : S.Terms) (solver : Solver)
  (assuming : Option (Typed.Terms Bool) := none)
: Env (Option S.Values) :=
  solver.checkSat? assuming (ifSat := terms.getValues solver)

end Sig

end Symbols

def declareSymbols := @Symbols.Sig.Idents.declare

namespace Solver

def declareSymbols := @Symbols.Sig.Idents.declareIn

def getSymbolValues := @Symbols.Sig.Terms.getValues

end Solver



/-! ## The `symbols structure` command

Declared `scoped`, so `open Cvc.Typed` selects the typed spelling. It is the sort-erased command
with this layer's two extra aliases: `Fun`, which a typed `Sig` parameterizes by its codomain, and
`Pred`, which is `Fun Bool`.
-/

open Lean Elab Command in
meta section

/-- Declares a symbols structure and everything a `Symbols` instance needs. -/
scoped syntax (name := symbolsStructure) atomic((docComment)? "structure.symbols ") ident
  " where" withPosition((ppLine colGe Lean.Parser.Command.structSimpleBinder)+) : command

elab_rules : command
  | `($[$doc?:docComment]? structure.symbols $id where $fields*) =>
    Cvc.Ext.elabSymbols `Cvc.Typed #[
      fun id => `(command|
        abbrev $(mkIdent (id.getId ++ `Fun)) (α : Type) := Cvc.Typed.Symbols.Sig.Fun $id α),
      fun id => `(command|
        abbrev $(mkIdent (id.getId ++ `Pred)) := Cvc.Typed.Symbols.Sig.Pred $id)
    ] doc? id fields

end

end
