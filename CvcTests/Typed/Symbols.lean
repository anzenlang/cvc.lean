/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core.Symbols
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Core.Symbols
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

/-! In `smt!`, a symbol is read off the structure with Lean's own dot notation: `syms.steps` projects
the field, the structure not being a term, and has the field's index. -/

/-- info: (and running (< steps 3)) -/
#guard_msgs in #eval Env.runIO do
  let syms ← (Symbols.Sig.idents () : Machine.Idents).declare
  println! ← smt! syms.running ∧ syms.steps < 3


/-! ## Folding

`foldM` belongs to the `Symbols` instance, beside `mapM`: `structure.symbols` defines it field by
field. It visits the symbols in field order and runs in any monad; over `Terms`, each symbol comes
at its own index.
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
  -- `t : Term α`, so the index is at hand
  syms.foldM () fun {α} _ _ () (t : Term α) => println! "{t} : {Typ.of α}"
  s.assert syms.running
  let some v ← syms.findCex s | println! "no model"
  println! "symbols counted from the model: {← v.foldM 0 fun n _ => return n + 1}"


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

/-! A hand-written instance that defines no `foldM` gets one derived from its `mapM`, visiting the
arrays' elements in order. -/

/-- info: #[b0, b1, i0] -/
#guard_msgs in #eval Env.runIO do
  let idents : Vars.Idents := ⟨#["b0", "b1"], #["i0"], #[]⟩
  let terms : Vars.Terms ← idents.declare
  println! ← terms.foldM #[] fun acc t => return acc.push t.erase

end ByHand



/-! ## State symbols in `smt!`

`smt!` reads a state symbol (`Symbols.At`) off its own type, as it does a non-terminal, so two of
them combine with nothing else to fix the index — left to the coercion, `x + y` did not elaborate.
A mismatch is still reported between the two terms. -/

namespace AtInSmt

structure.symbols Counter where
  x : Int
  y : Int

example : Counter.RelAt' := fun {x, y} {x := x', y := y'} => smt! x' = x + y ∧ y' = y + 1
example : Counter.PredAt' := fun {x, y} => smt! x * y ≤ x

/--
error: Application type mismatch: The argument
  smtArg1✝
has type
  Term Bool
but is expected to have type
  Term Int
in the application
  smtArg0✝.add smtArg1✝

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 6
-/
#guard_msgs in
example (t : Term Bool) : Counter.PredAt' := fun {x, ..} => smt! x + t ≤ x

end AtInSmt



/-! ## Symbols at a step

`TermsAt k` and `ValuesAt k` wrap every field in a `Symbols.At k`, which `get` unwraps. `declareAt`
names a symbol `count__@__k`, in both layers, the typed one naming it through the sort-erased
convention. -/

namespace AtStep

structure.symbols Counter where
  counting : Bool
  count : Int

example (s : Counter.TermsAt 0) : Term Int := s.count.get
example (s : Counter.ValuesAt 3) : Bool := s.counting.get
example (s : Counter.TermsAt 0) : Env (Term Int) := smt! s.count + 1

/-- info: count__@__0 count__@__2 -/
#guard_msgs in #eval Env.runIO do
  let at0 ← Counter.idents.declareAt 0
  let at2 ← Counter.idents.declareAt 2
  println! "{at0.count.get} {at2.count.get}"

end AtStep



/-! ## Declaring in a solver, and reading values as terms

`declareSymbolsAt` (`declareAtIn`) declares a step's symbols in a solver, answering the same symbols
when not fresh; `getSymbolValueTerms` and `getValueTerms` read a model's values back as terms, each
at its symbol's index.
-/

namespace InSolver

structure.symbols Counter where
  counting : Bool
  count : Int

/-- info:
step 1          : counting__@__1 count__@__1
again, not fresh: same true
again, fresh    : same false
values          : counting true, count 3
step 1 values   : counting false, count 4
scope constants : counting count
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let at1 ← s.declareSymbolsAt 1 Counter.idents
  println! "step 1          : {at1.counting.get} {at1.count.get}"
  let again ← Counter.idents.declareAtIn 1 s
  println! "again, not fresh: same {again.count.get.erase == at1.count.get.erase}"
  let fresh ← Counter.idents.declareAtIn 1 s (fresh := true)
  println! "again, fresh    : same {fresh.count.get.erase == at1.count.get.erase}"
  let syms ← s.declareSymbols Counter.idents
  s.assert (← smt! syms.counting ∧ syms.count = 3)
  s.assert (← smt! ¬ at1.counting ∧ at1.count = syms.count + 1)
  s.checkSat (ifSat := do
    let v ← s.getSymbolValueTerms syms
    let count : Term Int := v.count
    println! "values          : counting {v.counting}, count {count}"
    let v1 ← at1.getValueTerms s
    let count : Term Int := v1.count.get
    println! "step 1 values   : counting {v1.counting.get}, count {count}")
  let consts ← declareSymbols Counter.idents
  println! "scope constants : {consts.counting} {consts.count}"

/-! `declareBVars` makes one bound variable per field, at the field's index, which a lambda binds
into a function index. -/

/-- info: (lambda ((counting Bool) (count Int)) (ite counting (+ count 1) count)) -/
#guard_msgs in #eval Env.runIO do
  let b ← Counter.idents.declareBVars
  let body ← smt! if b.counting then b.count + 1 else b.count
  let params := BVars.push b.count (BVars.push b.counting [])
  let f : Term (Bool → Int → Int) ← BVars.lambda params body
  println! f

end InSolver
