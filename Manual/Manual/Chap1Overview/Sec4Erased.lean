/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import VersoManual

import Manual.Meta.Lean

import Cvc

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Manual

open Cvc

set_option pp.rawOnError true


#doc (Manual) "Type-Erased API" =>

%%%
tag := "chapOverview_erased"
%%%

The previous section was about defining our own strongly-typed system by creating a
symbols/state/system structure, where the fields are strongly-typed fields named after our symbols.
This is not very useful if, say, we are writing an SMT-based tools where the symbols we will
manipulate are not known statically, typically because the actual symbols are parsed at runtime.

In this context, strong-typing because a liability as we can't just build, say, a red/black map
from symbol {lean}`String` names to {lean}`Term`/{lean}`Value` as we don't know their type at
compile-time, and in general they will not all have the same type anyway.

The _erased_ part of the cvc.lean API solves this issue by providing a _type-erased_ version of
{lean}`Term`: {lean}`ETerm` (for Erased Term).

```savedLean (name := erasedDemo1)
#print ETerm
```

```leanOutput erasedDemo1
structure Cvc.ETerm : Type
number of parameters: 0
fields:
  Cvc.ETerm.srt : Srt
  Cvc.ETerm.typed : Term self.srt.toType
constructor:
  Cvc.ETerm.mk (srt : Srt) (typed : Term srt.toType) : ETerm
```

Note the use of {lean}`Srt`, which is an inductive type encoding all types a {lean}`Term` can have.
This lets us, for example, parse the type of symbol `"Int"` as {lean}`Srt.int` at runtime.

In fact, most of the types we have seen in this chapter have an _erased_ version.

```lean
#check EValue

#check ESymbol
```

There is no `ESymbols` or `ESys` class/type however. Instead, cvc.lean provides the
{lean}`ESymbols.ByName` type which is already a symbol/state-structure, and is thus compatible with
the `Sys` API from the previous section.

```lean
#check ESymbols.ByName

#check ESys.ByName
```

If we parsed the _stopwatch_ example from the previous section, we would end up with the following
symbol table.

```lean
#check ESymbols.ByName.Idents

#check ESymbols.ByName.emptyIdents

#check ESymbols.ByName.Idents.insert
#check ESymbols.ByName.Idents.insert!

open ESymbols (ByName)

def ESw.userSymbols : ByName.Idents :=
  ESymbols.ByName.emptyIdents
  |>.insert! "startStop" Srt.bool
  |>.insert! "reset" Srt.bool
  |>.insert! "isCounting" Srt.bool
  |>.insert! "counter" Srt.int
```

We would also get the `init` predicate/`step` relation, and the candidates. Notice that we get back
into strongly-typed terms as soon as we get to term-building.

```lean
open Cvc.Term.Dsl

def ESw.init : ByName.StatePredicate := fun state => do
    let isCounting ← state.findAsSrt Srt.bool "isCounting"
    let counter ← state.findAsSrt Srt.int "counter"
    smt! ¬ isCounting ∧ counter = 0

-- note that the term DSL supports erased-term
def ESw.init' : ByName.StatePredicate := smtPred! state =>
    ¬ ![state.findAsSrt .bool "isCounting"]
    ∧ ![state.findAsSrt .int "counter"] = 0

def ESw.step : ByName.StateRelation :=
  fun curr next => do
    let isCounting ← curr.findAsSrt .bool "isCounting"
    let counter ← curr.findAsSrt .int "counter"
    let startStop' ← next.findAsSrt .bool "startStop"
    let reset' ← next.findAsSrt .bool "reset"
    let isCounting' ← next.findAsSrt .bool "isCounting"
    let counter' ← next.findAsSrt .int "counter"
    smt!
      (
        isCounting' =
          if startStop' then ¬ isCounting else isCounting
      ) ∧ (
        counter' =
          if reset' then 0 else
            if isCounting' then counter + 1
            else counter
      )

def ESw.candidate1 : String × ByName.StatePredicate :=
  ("counter positive",
    smtPred! state => 0 ≤ ![state.findAsSrt .int "counter"])

def ESw.candidate2 : String × ByName.StatePredicate :=
  ("counter ≠ 2",
    smtPred! state => ![state.findAsSrt .int "counter"] ≠ 2)
```

That's enough to define our {lean}`ESys.ByName`.

```lean
#check ESys.ByName

abbrev ESw (length : Nat) := ESys.ByName (length : Nat)

namespace ESw

def mk : Res (ESw 0) :=
  ESys.ByName.mk ESw.userSymbols ESw.init ESw.step
  |>.addCandidates [ESw.candidate1, ESw.candidate2]

/-- `Sw k.succ`, in `Sw 0` candidates have no status. -/
def print {k : Nat} (sw : ESw k.succ) : IO Unit := do
  println! "candidates status at depth {k}:"
  let .mk unknown invariant falsified := sw.candidates

  if ¬ unknown.isEmpty then
    println! "- {unknown.size} unknown(s)"
    for (name, unk) in unknown do
      let baseUpTo :=
        if let some k := unk.baseValidUpTo?
        then s!", valid up to step {k}"
        else ""
      println! "  `{name}`{baseUpTo}"

  if ¬ invariant.isEmpty then
    println! "- {invariant.size} invariant(s)"
    for (name, inv) in invariant do
      println! "  `{name}`, {inv.provedAt}-inductive"

  if ¬ falsified.isEmpty then
    println! "- {falsified.size} falsified"
    for (name, fls) in falsified do
      println! "  `{name}`, \
        falsified in {fls.falsifiedAt} steps"
      for ⟨k, state⟩ in fls.cex do
        let strGet (name : String) : String :=
          state.findMapOr name toString fun _ => "???"
        println! "  - at {k}: \
          startStop := {strGet "startStop"}, \
          reset := {strGet "reset"}, \
          isCounting := {strGet "isCounting"}, \
          counter := {strGet "counter"}\
        "
end ESw
```

{lean}`ESys.ByName` is just a regular {lean}`Sys`, we can run the analysis from the previous section
right away.

```savedLean (name := erasedDemo3)
#eval Smt.runIO do
  Smt.setOption .produceModels
  -- none of the type annotations are needed
  let sw0 : ESw 0 ← ESw.mk
  let maxSteps := 2
  println! "running with `maxSteps := {maxSteps}`"
  let res : (k : Nat) × ESw k.succ ← sw0.kInduction maxSteps
  let ⟨k, sw⟩ := res
  println! "→ done at `length = {k.succ} = depth + 1`\n"
  sw.print

  if sw.isDone then
    println! "\nunexpected: no more unknown candidates"
    return ()

  println! "\nsome candidates are still unknown...\n"
  let maxSteps := 10
  println! "running with `maxSteps := {maxSteps}`"
  let res : (k : Nat) × ESw (k + 1) ← sw.kInduction maxSteps
  let ⟨k, sw⟩ := res
  println! "→ done at `length = {k.succ} = depth + 1`\n"
  sw.print
```

```leanOutput erasedDemo3
running with `maxSteps := 2`
→ done at `length = 2 = depth + 1`

candidates status at depth 1:
- 1 unknown(s)
  `counter ≠ 2`, valid up to step 1
- 1 invariant(s)
  `counter positive`, 1-inductive

some candidates are still unknown...

running with `maxSteps := 10`
→ done at `length = 3 = depth + 1`

candidates status at depth 2:
- 1 invariant(s)
  `counter positive`, 1-inductive
- 1 falsified
  `counter ≠ 2`, falsified in 2 steps
  - at 2: startStop := false, reset := false, isCounting := true, counter := 2
  - at 1: startStop := true, reset := false, isCounting := true, counter := 1
  - at 0: startStop := false, reset := false, isCounting := false, counter := 0
```

This concludes the brief overview of cvc.lean. The next chapters dive into the technical details of
the entire API.
