/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Cvc.Gen.Symbols
public import Cvc.Untyped.Core.Solver

import all Cvc.Untyped.Core.Solver




/-! # Symbols, sort-erased

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

**Symbols at a step.** `TermsAt k`, `ValuesAt k` and `ValueTermsAt k` wrap every field in a
`Symbols.At k`, read with `get`, for the symbols of step `k` of a transition system: `declareAt k`
names a symbol `count__@__k`, and `FunAt`, `Fun2At` and their primed forms are the constraints over
one step or two. `Cvc.Untyped.Extra.Sys` builds transition systems and bounded model checking
on top.

Worked examples, including the hand-written path for what `structure.symbols` cannot express, are
in `CvcTests.Untyped.Symbols`.
-/
namespace Cvc.Untyped public section

namespace Symbols

/-- Signature of the symbol wrapper. -/
abbrev Wrap : Type 1 := (α : Type) → [ToTyp α] → [TermToValue α] → Type

/-- Signature of a user-provided type representing some symbols. -/
abbrev Sig : Type 1 := Wrap → Type

/-- A `Wrap` value at some depth `k : Nat`. -/
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

/-- Some `String` identifiers over a `Sig` -/
abbrev Idents : Type := S (fun _α => String)
/-- `Term` specialization for a `Sig`. -/
abbrev Terms : Type := S (𝕂 Term)
/-- `Term` at `k` specialization for a `Sig`. -/
abbrev TermsAt (k : Nat) : Type := S (Symbols.At k (𝕂 Term))
/-- `BVar` specialization for a `Sig`. -/
abbrev BVars : Type := S (𝕂 BVar)
/-- Lean-value specialization for a `Sig`. -/
abbrev Values : Type := S (fun α => α)
/-- `Term`-value specialization for a `Sig`. -/
abbrev ValueTerms : Type := S (𝕂 Term)
/-- Lean-value at `k` specialization for a `Sig`. -/
abbrev ValuesAt (k : Nat) : Type := S (Symbols.At k fun α => α)
/-- `Term`-value specialization for a `Sig`. -/
abbrev ValueTermsAt (k : Nat) : Type := S (Symbols.At k (𝕂 Term))
/-- Function from `Term`-symbols to a `Term`. -/
abbrev Fun : Type := S.Terms → Env Term
/-- Function from `Term`-symbols at `k` to a `Term`. -/
abbrev FunAt (k : Nat) : Type := S.TermsAt k → Env Term
@[inherit_doc FunAt]
abbrev FunAt' : Type := {k : Nat} → S.FunAt k
/-- Function over some `Term`-symbols at `k` and some at `k'` (default `k + 1`). -/
abbrev Fun2At (k : Nat) (k' : Nat := k + 1) : Type := S.TermsAt k → S.TermsAt k' → Env Term
@[inherit_doc Fun2At]
abbrev Fun2At' : Type := {k k' : Nat} → S.Fun2At k k'

end Sig

end Symbols

/-- Symbols specification.

Instantiate this class on your own types to benefit from the `Symbols` framework.
-/
class Symbols (S : Symbols.Sig) where
  InitData : Type := Unit
  idents : InitData → S.Idents
  /-- Monadic map over the symbols. -/
  mapM [Ω] {W W' : Symbols.Wrap} [Monad m]
    (s : S W) (f : {α : Type} → [ToTyp α] → [TermToValue α] → W α → m (W' α)) : m (S W')
  /-- Folds over the symbols in field order, threading a state through `f`.

  Defaults to a fold derived from `mapM`, so a hand-written instance need not define it;
  `structure.symbols` defines it directly.
  -/
  foldM [Ω] {W : Symbols.Wrap} [Monad m] (s : S W) (init : σ)
    (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → W α → m σ) : m σ := do
    let (_, acc) ← (mapM (m := StateT σ m) s fun x => do set (← f (← get) x); return x).run init
    return acc

section variable [Ω] [inst : Symbols S]

namespace Symbols

@[inherit_doc Sig.Idents]
abbrev Idents := S.Idents
@[inherit_doc Sig.Terms]
abbrev Terms := S.Terms
@[inherit_doc Sig.TermsAt]
abbrev TermsAt (k : Nat) := S.TermsAt k
@[inherit_doc Sig.BVars]
abbrev BVars := S.BVars
@[inherit_doc Sig.Values]
abbrev Values := S.Values
@[inherit_doc Sig.ValueTerms]
abbrev ValueTerms := S.ValueTerms
@[inherit_doc Sig.ValuesAt]
abbrev ValuesAt (k : Nat) := S.ValuesAt k
@[inherit_doc Sig.ValueTermsAt]
abbrev ValueTermsAt (k : Nat) := S.ValueTermsAt k
@[inherit_doc Sig.Fun]
abbrev Fun := S.Fun
@[inherit_doc Sig.FunAt]
abbrev FunAt (k : Nat) := S.FunAt k
@[inherit_doc Sig.FunAt']
abbrev FunAt' := S.FunAt'
@[inherit_doc Sig.Fun2At]
abbrev Fun2At (k : Nat) (k' : Nat := k + 1) := S.Fun2At k k'
@[inherit_doc Sig.Fun2At']
abbrev Fun2At' := S.Fun2At

namespace Sig
/-- Identifiers associated with a `Sig`. -/
abbrev idents : inst.InitData → S.Idents := inst.idents
@[inherit_doc idents]
abbrev Idents.get := @Sig.idents

@[inherit_doc Symbols.mapM]
abbrev mapM := @inst.mapM
@[inherit_doc Symbols.foldM]
abbrev foldM := @inst.foldM

@[inherit_doc Symbols.foldM]
def Idents.foldM [Ω] [Monad m] (idents : S.Idents) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → String → m σ)
: m σ :=
  inst.foldM (W := fun _α => String) idents init fun {α} _ _ acc x => f (α := α) acc x

@[inherit_doc Symbols.foldM]
def Terms.foldM [Ω] [Monad m] (terms : S.Terms) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → Term → m σ)
: m σ :=
  inst.foldM (W := 𝕂 Term) terms init fun {α} _ _ acc x => f (α := α) acc x

@[inherit_doc Symbols.foldM]
def BVars.foldM [Ω] [Monad m] (bVars : S.BVars) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → BVar → m σ)
: m σ :=
  inst.foldM (W := 𝕂 Term) bVars init fun {α} _ _ acc x => f (α := α) acc x

@[inherit_doc Symbols.foldM]
def Values.foldM [Ω] [Monad m] (values : S.Values) (init : σ)
  (f : {α : Type} → [ToTyp α] → [TermToValue α] → σ → α → m σ)
: m σ :=
  inst.foldM (W := fun α => α) values init fun {α} _ _ acc x => f (α := α) acc x

/-- The identifier for symbol `symbol` at depth `k`. -/
protected def mkSymbolIdentAt (k : Nat) (symbol : String) : String :=
  s!"{symbol}__@__{k}"

namespace Idents variable [Ω]

/-- Declares some symbols. -/
def declare (idents : S.Idents) : Env S.Terms :=
  S.mapM idents fun {α} _ _ symbol => do Term.mkSymbol (← Srt.of α) symbol

/-- Declares some symbols in a solver. -/
def declareIn (idents : S.Idents) (solver : Solver) : Env S.Terms :=
  S.mapM idents fun {α} _ _ symbol => Srt.of α >>= solver.declareFun symbol #[]

/-- Declares some symbols a depth `k`. -/
def declareAt (idents : S.Idents) (k : Nat) : Env (S.TermsAt k) :=
  S.mapM idents fun {α} _ _ ident =>
    return ⟨← Term.mkSymbol (← Srt.of α) (Sig.mkSymbolIdentAt k ident)⟩

/-- Declares some symbols at depth `k` in a solver. -/
def declareAtIn (k : Nat) (s : Solver) (idents : S.Idents)
  (fresh : Bool := false)
: Env (S.TermsAt k) :=
  S.mapM idents fun {α} _ _ ident =>
    return ⟨← Srt.of α >>= s.declareFun (Sig.mkSymbolIdentAt k ident) #[] (fresh := fresh)⟩

/-- Declares some symbols as bound variables. -/
def declareBVars (idents : S.Idents) : Env S.BVars :=
  S.mapM idents fun {α} _ _ symbol => do BVar.mk (← Srt.of α) symbol

end Idents

namespace Terms

/-- Transforms `Term`-symbols into bound variables. -/
def toBVars (terms : S.Terms) : Env S.BVars :=
  S.mapM terms fun {α} _ _ term => do term.getSymbol >>= BVar.mk (← Srt.of α)

/-- The Lean-values of some `Term`-symbols in a satisfiable instance. -/
def getValues (terms : S.Terms) (solver : Solver) : solver.EnvSat S.Values :=
  S.mapM terms fun term => do
    let valueTerm ← solver.getValue term
    valueTerm.extractValue

/-- The `Term`-values of some `Term`-symbols in a satisfiable instance. -/
def getValueTerms (terms : S.Terms) (solver : Solver) : solver.EnvSat S.ValueTerms :=
  S.mapM terms fun term => solver.getValue term

/-- Checks satisfiability and, where sat, reads every symbol's value out of the model.

Needs no per-`Sig` code: `mapM` is what makes it generic, so a user's symbol structure gets this
by instancing `Symbols` and nothing else.
-/
def findCex (terms : S.Terms) (solver : Solver)
  (assuming : Option Untyped.Terms := none)
: Env (Option S.Values) :=
  solver.checkSat? assuming (ifSat := terms.getValues solver)

end Terms

namespace TermsAt

/-- The Lean-values of some `Term`-symbols at depth `k`. -/
def getValues (terms : S.TermsAt k) (solver : Solver) : solver.EnvSat (S.ValuesAt k) :=
  S.mapM terms fun {α} _ _ term => return ⟨← solver.getValueAs α term⟩

/-- The `Term`-values of some `Term`-symbols at depth `k`. -/
def getValueTerms (terms : S.TermsAt k) (solver : Solver) : solver.EnvSat (S.ValueTermsAt k) :=
  S.mapM terms fun term => return ⟨← solver.getValue term⟩

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
@[inherit_doc Symbols.Sig.Terms.getValueTerms]
def getSymbolValueTerms := @Symbols.Sig.Terms.getValueTerms

end Solver



/-! ## The `symbols structure` command

Declared `scoped`, so `open Cvc.Untyped` selects the sort-erased spelling exactly as it selects
`smt!`. What it generates is described in `Cvc.Ext.elabSymbols`.
-/

open Lean Elab Command in
meta section

/-- Declares a symbols structure and everything a `Symbols` instance needs. -/
scoped syntax (name := symbolsStructure) atomic((docComment)? "structure.symbols ") ident
  " where" withPosition((ppLine colGe Lean.Parser.Command.structSimpleBinder)+) : command

elab_rules : command
  | `($[$doc?:docComment]? structure.symbols $id where $fields*) =>
    Cvc.Ext.elabSymbols `Cvc.Untyped
      #[(`Fun, true), (`FunAt, true), (`FunAt', true), (`Fun2At, true), (`Fun2At', true)]
      doc? id fields

end

end
