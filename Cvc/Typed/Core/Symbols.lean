/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Untyped.Core.Symbols

public meta import Cvc.Gen.Symbols
public import Cvc.Untyped.Core.Symbols
public import Cvc.Typed.Core.Solver




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

**Symbols at a step.** `TermsAt k`, `ValuesAt k` and `TermValuesAt k` wrap every field in a
`Symbols.At k`, read with `get`, for the symbols of step `k` of a transition system: `declareAt k`
names a symbol `count__@__k`, and `FunAt`, `Fun2At` and their primed forms are the constraints over
one step or two. In `smt!` a state symbol is read off its own type, so `x + y` over two of them
needs no `get`. `Cvc.Typed.Extra.Sys` builds transition systems and bounded model checking on top.

Worked examples, including the hand-written path for what `structure.symbols` cannot express, are
in `Cvc.Tests.Typed.Symbols`.
-/
namespace Cvc.Typed public section

namespace Symbols

@[inherit_doc Untyped.Symbols.Wrap]
abbrev Wrap : Type 1 := (α : Type) → [ToTyp α] → [TermToValue α] → Type

@[inherit_doc Untyped.Symbols.Sig]
abbrev Sig : Type 1 := Wrap → Type

@[inherit_doc Untyped.Symbols.At]
protected structure At (k : Nat) (W : Symbols.Wrap) (α : Type) [ToTyp α] [TermToValue α] where
/-- Private constructor. -/
private mk' ::
  /-- Accessor. -/
  get : W α

namespace At

instance [ToTyp α] [TermToValue α] (value : Symbols.At k W α)
: CoeDep (Symbols.At k W α) value (W α) := ⟨value.get⟩

end At

namespace Sig variable [Ω] (S : Sig)

@[inherit_doc Untyped.Symbols.Idents]
abbrev Idents : Type := S (fun _α => String)
@[inherit_doc Untyped.Symbols.Terms]
abbrev Terms : Type := S (Typed.Term ·)
@[inherit_doc Untyped.Symbols.TermsAt]
abbrev TermsAt (k : Nat) : Type := S (Symbols.At k (Term ·))
@[inherit_doc Untyped.Symbols.BVars]
abbrev BVars : Type := S (Typed.BVar ·)
@[inherit_doc Untyped.Symbols.Values]
abbrev Values : Type := S (fun α => α)
@[inherit_doc Untyped.Symbols.TermValues]
abbrev TermValues : Type := S (Term ·)
@[inherit_doc Untyped.Symbols.ValuesAt]
abbrev ValuesAt (k : Nat) : Type := S (Symbols.At k fun α => α)
@[inherit_doc Untyped.Symbols.TermValuesAt]
abbrev TermValuesAt (k : Nat) : Type := S (Symbols.At k (Term ·))
@[inherit_doc Untyped.Symbols.Fun]
abbrev Fun (α : Type) : Type := S.Terms → Env (Term α)
@[inherit_doc Untyped.Symbols.FunAt]
abbrev FunAt (α : Type) (k : Nat) : Type := S.TermsAt k → Env (Term α)
@[inherit_doc Untyped.Symbols.FunAt']
abbrev FunAt' (α : Type) : Type := {k : Nat} → S.FunAt α k
/-- A predicate over the symbols. -/
abbrev Pred : Type := S.Fun Bool
/-- A predicate over the symbols at depth `k`. -/
abbrev PredAt (k : Nat) : Type := S.FunAt Bool k
@[inherit_doc PredAt]
abbrev PredAt' : Type := {k : Nat} → S.PredAt k
@[inherit_doc Untyped.Symbols.Fun2At]
abbrev Fun2At (α : Type) (k : Nat) (k' : Nat := k + 1) : Type :=
  S.TermsAt k → S.TermsAt k' → Env (Term α)
@[inherit_doc Untyped.Symbols.Fun2At']
abbrev Fun2At' (α : Type) : Type := {k k' : Nat} → S.Fun2At α k k'
/-- A relation between two unrolled versions of some symbols. -/
abbrev RelAt (k : Nat) (k' : Nat := k + 1) : Type := S.Fun2At Bool k (k' := k')
@[inherit_doc RelAt]
abbrev RelAt' : Type := {k k' : Nat} → S.RelAt k k'

end Sig

end Symbols

class Symbols (S : Symbols.Sig) where
  /-- Initialization data, if any (default none, *i.e.* `Unit`). -/
  InitData : Type := Unit
  /-- Identifiers. -/
  idents : InitData → S.Idents
  /-- Monadic map over the symbols. -/
  mapM {W W' : Symbols.Wrap} [Monad m]
    (s : S W) (f : {α : Type} → [ToTyp α] → [TermToValue α] → W α → m (W' α)) : m (S W')
  /-- Folds over the symbols in field order, threading a state through `f`.

  Defaults to a fold derived from `mapM`, so a hand-written instance need not define it;
  `structure.symbols` defines it directly.
  -/
  foldM {W : Symbols.Wrap} [Monad m] (s : S W) (init : σ)
    (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → W α → m σ) : m σ := do
    let (_, acc) ← (mapM (m := StateT σ m) s fun x => do set (← f (← get) x); return x).run init
    return acc

section variable [Ω] [inst : Symbols S]

namespace Symbols

export Sig
  ( Idents Terms TermsAt BVars Values TermValues ValuesAt TermValuesAt
    Fun FunAt FunAt' Pred PredAt PredAt' Fun2At Fun2At' RelAt RelAt' )

namespace Sig
@[inherit_doc Untyped.Symbols.Sig.idents]
abbrev idents : inst.InitData → S.Idents := inst.idents
@[inherit_doc Untyped.Symbols.Sig.Idents.get]
abbrev Idents.get := @Sig.idents

@[inherit_doc Symbols.mapM]
abbrev mapM := @inst.mapM
@[inherit_doc Symbols.foldM]
abbrev foldM := @inst.foldM

@[inherit_doc Symbols.foldM]
def Idents.foldM [Monad m] (idents : S.Idents) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → String → m σ)
: m σ :=
  inst.foldM (W := fun _α => String) idents init fun {α} _ _ acc x => f (α := α) acc x

/-- Folds over the symbols' terms in field order, each at its own index, threading a state. -/
def Terms.foldM [Monad m] (terms : S.Terms) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → Term α → m σ)
: m σ :=
  inst.foldM (W := (Typed.Term ·)) terms init fun {α} _ _ acc x => f (α := α) acc x

/-- Folds over the symbols' terms in field order, each at its own index, threading a state. -/
def BVars.foldM [Monad m] (bVars : S.BVars) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → BVar α → m σ)
: m σ :=
  inst.foldM (W := (Typed.BVar ·)) bVars init fun {α} _ _ acc x => f (α := α) acc x

/-- Folds over the symbols' values in field order, each at its Lean type, threading a state. -/
def Values.foldM [Monad m] (values : S.Values) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → α → m σ)
: m σ :=
  inst.foldM (W := fun α => α) values init fun {α} _ _ acc x => f (α := α) acc x

namespace Idents

@[inherit_doc Untyped.Symbols.Sig.Idents.declare]
def declare (idents : S.Idents) : Env S.Terms := S.mapM idents Term.mkSymbol

@[inherit_doc Untyped.Symbols.Sig.Idents.declareIn]
def declareIn (idents : S.Idents) (solver : Solver) : Env S.Terms :=
  S.mapM idents solver.declareFun

@[inherit_doc Untyped.Symbols.Sig.Idents.declareAt]
def declareAt (idents : S.Idents) (k : Nat) : Env (S.TermsAt k) :=
  S.mapM idents fun ident =>
    return ⟨← Term.mkSymbol (Untyped.Symbols.Sig.mkSymbolIdentAt k ident)⟩

@[inherit_doc Untyped.Symbols.Sig.Idents.declareAtIn]
def declareAtIn (k : Nat) (s : Solver) (idents : S.Idents)
  (fresh : Bool := false)
: Env (S.TermsAt k) :=
  S.mapM idents fun ident =>
    return ⟨← s.declareFun (Untyped.Symbols.Sig.mkSymbolIdentAt k ident) (fresh := fresh)⟩

@[inherit_doc Untyped.Symbols.Sig.Idents.declareBVars]
def declareBVars (idents : S.Idents) : Env S.BVars := S.mapM idents BVar.mk

end Idents

namespace Terms variable [Ω]

/-- Transforms `Term`-symbols into bound variables. -/
def toBVars (terms : S.Terms) : Env S.BVars :=
  S.mapM terms fun term => term.getSymbol >>= BVar.mk

/-- The Lean-values of some `Term`-symbols in a satisfiable instance. -/
def getValues (terms : S.Terms) (solver : Solver) : solver.EnvSat S.Values :=
  S.mapM terms solver.getValue

/-- The `Term`-values of some `Term`-symbols in a satisfiable instance. -/
def getTermValues (terms : S.Terms) (solver : Solver) : solver.EnvSat S.TermValues :=
  S.mapM terms solver.getValueTerm

/-- Checks satisfiability and, where sat, reads every symbol's value out of the model.

Needs no per-`Sig` code: `mapM` is what makes it generic, so a user's symbol structure gets this
by instancing `Symbols` and nothing else.
-/
def findCex (terms : S.Terms) (solver : Solver)
  (assuming : Option (Typed.Terms Bool) := none)
: Env (Option S.Values) :=
  solver.checkSat? assuming (ifSat := terms.getValues solver)

end Terms

namespace TermsAt variable [Ω]

/-- The Lean-values of some `Term`-symbols at depth `k`. -/
def getValues (terms : S.TermsAt k) (solver : Solver) : solver.EnvSat (S.ValuesAt k) :=
  S.mapM terms fun term => return ⟨← solver.getValue term⟩

/-- The `Term`-values of some `Term`-symbols at depth `k`. -/
def getTermValues (terms : S.TermsAt k) (solver : Solver) : solver.EnvSat (S.TermValuesAt k) :=
  S.mapM terms fun term => return ⟨← solver.getValueTerm term⟩

end TermsAt

end Sig

end Symbols

@[inherit_doc Symbols.Sig.Idents.declare]
def declareSymbols := @Symbols.Sig.Idents.declare

namespace Solver

@[inherit_doc Symbols.Sig.Idents.declareIn]
def declareSymbols := @Symbols.Sig.Idents.declareIn
@[inherit_doc Symbols.Sig.Idents.declareAtIn]
def declareSymbolsAt := @Symbols.Sig.Idents.declareAtIn
@[inherit_doc Symbols.Sig.Terms.getValues]
def getSymbolValues := @Symbols.Sig.Terms.getValues
@[inherit_doc Symbols.Sig.Terms.getTermValues]
def getSymbolTermValues := @Symbols.Sig.Terms.getTermValues

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
    Cvc.Ext.elabSymbols `Cvc.Typed
      #[(`Fun, true), (`FunAt, true), (`FunAt', true), (`Fun2At, true), (`Fun2At', true),
        (`Pred, true), (`PredAt, true), (`PredAt', true), (`RelAt, true), (`RelAt', true)]
      doc? id fields

end

end
