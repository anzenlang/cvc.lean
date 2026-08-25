/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Symbols
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Symbols
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory



/-! # Symbols, sort-erased

`structure.symbols` generates the structure the `Symbols` class wants — parameterized by the
`Wrap`, every field wrapped in it — plus the `Idents`/`Terms`/`Values` aliases and the instance.
Everything else a symbol structure can do is generic over the `Sig`, so nothing else is generated.
-/
namespace Cvc.Tests.Untyped.Symbols

open Cvc Untyped

-- the structure itself needs no `Ω` — only `Terms` does, which is why the examples below take it
variable [Ω]

/-- Symbols for a little state machine. -/
structure.symbols Machine where
  /-- Whether the machine is running. -/
  running : Bool
  /-- How many steps it has taken. -/
  steps : Int

/-! ## What is generated

The structure takes the `Wrap` the user never wrote, and each field's type is wrapped in it.
-/

/-- info: @Machine.running : {W : Symbols.Wrap} → Machine W → W Bool -/
#guard_msgs in #check @Machine.running

/-- The three aliases, at the sorts the fields named. -/
example (i : Machine.Idents) (t : Machine.Terms) (v : Machine.Values)
: String × Untyped.Term × Bool := (i.running, t.running, v.running)

/-! ## What is *not* generated

`declare`, `getValues` and `findCex` are generic over the `Sig`, so the instance is a symbol
structure's whole obligation.
-/

example (idents : Machine.Idents) : Env Machine.Terms := idents.declare
example (syms : Machine.Terms) (s : Solver) : Env (Option Machine.Values) := syms.findCex s

/-! ## A symbol is named after its field -/

/-- info: running: running, steps: steps -/
#guard_msgs in #eval Env.runIO do
  let i : Machine.Idents := Symbols.Sig.idents ()
  println! "running: {i.running}, steps: {i.steps}"

/-! ## End to end -/

/-- info: running = true, steps = 3 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let syms ← (Symbols.Sig.idents () : Machine.Idents).declareIn s
  (← Term.equal syms.steps (← Term.mkInt 3)) |> s.assert
  s.assert syms.running
  match ← syms.findCex s with
  | some v => println! "running = {v.running}, steps = {v.steps}"
  | none => println! "no model"

/-! ## `Ω` is taken only where a term is mentioned

A symbol structure, its `Idents` and its `Values` need no scope at all — only `Terms` does. That is
what lets a caller name a structure's identifiers and read its values outside `Env.run`, entering a
scope only to solve.
-/

section noOmega
/-- Declared with no `Ω` anywhere in scope. -/
structure.symbols Free where
  a : Bool
  n : Int

example (i : Free.Idents) : String := i.a
example (v : Free.Values) : Bool × Int := (v.a, v.n)
end noOmega

/-! ## `symbols` is not a keyword

The command's leading token is `structure.symbols`, so an ordinary identifier of that name is
unaffected — which matters, since the hand-written examples bind one.
-/

example (symbols : Nat) : Nat := symbols


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
abbrev Fun := Symbols.Sig.Fun Vars

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
