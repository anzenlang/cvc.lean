/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core.Symbols
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Core.Symbols
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

/-! In `smt!`, a symbol is read off the structure with Lean's own dot notation: `syms.steps` projects
the field, the structure not being a term. -/

/-- info: (and running (< steps 3)) -/
#guard_msgs in #eval Env.runIO do
  let syms ← (Symbols.Sig.idents () : Machine.Idents).declare
  println! ← smt! syms.running ∧ syms.steps < 3

/-! ## Folding

`foldM` belongs to the `Symbols` instance, beside `mapM`: `structure.symbols` defines it field by
field. It visits the symbols in field order and runs in any monad.
-/

/-- info: names: #[running, steps]
running : Bool
steps : Int
symbols counted from the model: 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let ids : Machine.Idents := Symbols.Sig.idents ()
  println! "names: {← ids.foldM #[] fun acc name => return acc.push name}"
  let syms ← ids.declareIn s
  -- each symbol with its sort, printed as the fold goes
  syms.foldM () fun {α} _ _ () t => println! "{t} : {Typ.of α}"
  s.assert syms.running
  let some v ← syms.findCex s | println! "no model"
  println! "symbols counted from the model: {← v.foldM 0 fun n _ => return n + 1}"

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

/-! A hand-written instance that defines no `foldM` gets one derived from its `mapM`, visiting the
arrays' elements in order. -/

/-- info: #[b0, b1, i0] -/
#guard_msgs in #eval Env.runIO do
  let idents : Vars.Idents := ⟨#["b0", "b1"], #["i0"], #[]⟩
  let terms : Vars.Terms ← idents.declare
  println! ← terms.foldM #[] fun acc t => return acc.push t

end ByHand



/-! ## Symbols at a step

`TermsAt k` and `ValuesAt k` wrap every field in a `Symbols.At k`, which `get` unwraps. `declareAt`
names a symbol `count__@__k`, so a step's variables are distinguishable by name and a model can say
which step a value belongs to. -/

namespace AtStep

structure.symbols Counter where
  counting : Bool
  count : Int

example (s : Counter.TermsAt 0) : Term := s.count.get
example (s : Counter.ValuesAt 3) : Bool := s.counting.get
example (s : Counter.TermsAt 0) : Env Term := smt! s.count + 1

/-- info: count__@__0 count__@__2 -/
#guard_msgs in #eval Env.runIO do
  let at0 ← Counter.idents.declareAt 0
  let at2 ← Counter.idents.declareAt 2
  println! "{at0.count.get} {at2.count.get}"

end AtStep
