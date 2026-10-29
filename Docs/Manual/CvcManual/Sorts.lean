/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Defs

public import Cvc
public meta import Cvc
public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Cvc



set_option pp.rawOnError true



#doc (Manual) "Sorts" =>
%%%
tag := "sortsOverview"
htmlSplit := .never
%%%

Sort constructors live in the `Srt` namespace and are all in the `Env` monad.

```lean (name := sort_ex_basic)
#eval Env.runIO do
  let b ← Srt.bool
  let r ← Srt.real
  let mapBoolReal ← b.arrayTo r
  -- alternatively
  let mapBoolReal' ← r.arrayFrom b
  let ff ← Srt.finiteField 7
  let f1 ← Srt.function #[b] r
  let f2 ← Srt.function #[r, b] r
  println! "b            := {b}"
  println! "r            := {r}"
  println! "mapBoolReal  := {mapBoolReal}"
  println! "mapBoolReal' := {mapBoolReal'}"
  println! "ff           := {ff}"
  println! "f1           := {f1}"
  println! "f2           := {f2}"
```
```leanOutput sort_ex_basic
b            := Bool
r            := Real
mapBoolReal  := (Array Bool Real)
mapBoolReal' := (Array Bool Real)
ff           := (_ FiniteField 7)
f1           := (-> Bool Real)
f2           := (-> Real Bool Real)
```


# Lean Type to `Srt`

Cvc.lean associates some Lean types to cvc5-sorts `Srt` through the `ToTyp` class.

{docstring ToTyp}

`ToTyp α` specifies a `Typ`-value for `α` that corresponds to a `Srt`.{margin}[But is _not_ a
`Srt` as constructing one requires to be in `Env`: a `Srt` value is tied to a specific manager.]
This lets us go from compatible Lean types to `Srt` easily.

```lean (name := sort_ex_Srt_of)
#eval Env.runIO do
  let b ← Srt.of Bool
  println! "b  := {b}"
  let i ← Srt.of Int
  println! "i  := {i}"
  let r ← Srt.of Rat
  println! "r  := {r}"
  let bv ← Srt.of (BitVec 8)
  println! "bv := {bv}"
  let f1 ← Srt.of (Int → Bool → Rat)
  println! "f1 := {f1}"
```
```leanOutput sort_ex_Srt_of
b  := Bool
i  := Int
r  := Real
bv := (_ BitVec 8)
f1 := (-> Int Bool Real)
```

Some cvc5-sorts do not map nicely to builtin Lean types however, so cvc.lean has a few custom types
with `ToTyp` instance.{margin}[In the following, `Float` refers to `Cvc.Float`, not the Lean
builtin type for floating point numbers.] Here are a few examples:

```lean (name := sort_ex_Srt_of_2)
#eval Env.runIO do
  let f ← Srt.of (Float 8 24)
  println! "f := {f}"
  let arr ← Srt.of (TotalMap Int Rat)
  println! "arr := {arr}"
  let ff ← Srt.of (FiniteField 7)
  println! "ff := {ff}"
  let bag ← Srt.of (Bag (Float 8 24))
  println! "bag := {bag}"
```
```leanOutput sort_ex_Srt_of_2
f := (_ FloatingPoint 8 24)
arr := (Array Int Real)
ff := (_ FiniteField 7)
bag := (Bag (_ FloatingPoint 8 24))
```
