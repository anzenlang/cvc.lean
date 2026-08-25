/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Symbols
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Symbols
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # Symbols, typed

The same command as the sort-erased layer, selected by which layer is open. What differs is the
index every symbol carries — `Terms` holds a `Term α` per field rather than a sort-erased one — and
the two extra aliases this layer's `Sig` has, `Fun` and `Pred`.
-/
namespace Cvc.Tests.Typed.Symbols

open Cvc Typed

variable [Ω]

/-- Symbols for a little state machine. -/
structure.symbols Machine where
  /-- Whether the machine is running. -/
  running : Bool
  /-- How many steps it has taken. -/
  steps : Int

/-! ## What is generated -/

/-- info: @Machine.running : {W : Symbols.Wrap} → Machine W → W Bool -/
#guard_msgs in #check @Machine.running

/-- Each alias at its field's own index — this is what the typed layer buys, and the reason
`Terms` is not interchangeable with the sort-erased one. -/
example (i : Machine.Idents) (t : Machine.Terms) (v : Machine.Values)
: String × Term Bool × Term Int × Bool × Int :=
  (i.running, t.running, t.steps, v.running, v.steps)

/-- The two aliases only this layer has. -/
example (_f : Machine.Fun Int) (_p : Machine.Pred) : Nat := 0

/-! ## What is not generated -/

example (idents : Machine.Idents) : Env Machine.Terms := idents.declare
example (syms : Machine.Terms) (s : Solver) : Env (Option Machine.Values) := syms.findCex s

/-! ## End to end

A symbol's term carries its index, so it is an operand of that index's operators with nothing
ascribed and nothing re-typed.
-/

/-- info: running = true, steps = 3 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let syms ← (Symbols.Sig.idents () : Machine.Idents).declareIn s
  (← smt! ![pure syms.steps] = 3) |> s.assert
  s.assert syms.running
  match ← syms.findCex s with
  | some v => println! "running = {v.running}, steps = {v.steps}"
  | none => println! "no model"


/-! ## The hand-written path

Not everything fits `structure.symbols`, and this is what instancing `Symbols` by hand is for: a
field here is an *array* of symbols rather than one, and `InitData` is the identifiers themselves
rather than the default `Unit`. The command wraps each field in the `Wrap` and names each symbol
after its field, so neither is expressible with it.

What the two paths share is the payoff: the instance is the whole obligation either way, so
`declare`, `getValues` and `findCex` work on this structure exactly as on a generated one.
-/

namespace ByHand

structure Vars (W : Symbols.Wrap) where
  boolVars : Array (W Bool)
  intVars : Array (W Int)
  realVars : Array (W Rat)

namespace Vars

abbrev Idents := Symbols.Sig.Idents Vars
abbrev Terms [Ω] := Symbols.Sig.Terms Vars
abbrev Values := Symbols.Sig.Values Vars
abbrev Fun (α : Type) := Symbols.Sig.Fun Vars α
abbrev Pred := Symbols.Sig.Pred Vars

instance : Symbols Vars where
  InitData := Idents
  idents := id
  mapM symbols f := return {
    boolVars := ← symbols.boolVars.mapM f
    intVars := ← symbols.intVars.mapM f
    realVars := ← symbols.realVars.mapM f
  }

end Vars

/-- The generic operations apply to a hand-written structure unchanged. -/
example (idents : Vars.Idents) : Env Vars.Terms := idents.declare
example (syms : Vars.Terms) (s : Solver) : Env (Option Vars.Values) := syms.findCex s

/-! An array-valued field means `InitData` cannot be `Unit`: there is no way to know how many
symbols to make, so the identifiers *are* the initialisation data. -/

/-- info: bools: #[b0, b1], ints: #[i0] -/
#guard_msgs in #eval Env.runIO do
  let idents : Vars.Idents := ⟨#["b0", "b1"], #["i0"], #[]⟩
  -- `InitData` is `Idents` here, so `Sig.idents` is the identity and `declare` takes them directly
  let terms : Vars.Terms ← idents.declare
  println! "bools: {terms.boolVars}, ints: {terms.intVars}"

end ByHand
