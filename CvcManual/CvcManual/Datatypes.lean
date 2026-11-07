/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc
public meta import Cvc
public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External



set_option pp.rawOnError true



#doc (Manual) "Datatypes and Records" =>
%%%
tag := "datatypes"
htmlSplit := .never
%%%

```lean -show
namespace Manual.Datatypes
open Cvc Typed
```

A datatype is declared in the current scope, like a sort of your own: declaring the same datatype twice gives two different sorts. A record is the opposite, a sort cvc5 builds from its fields, the same one each time.

# Declaring a Datatype

A declaration lists the constructors and their fields (_selectors_ in cvc5's terms). This one is `Lst := nil | cons (head : Int) (tail : Lst)`:

```lean
section variable [Ω]
def declareLst : Env Srt := do
  let nil ← Datatype.Ctor.Decl.mk "nil"
  let cons ← Datatype.Ctor.Decl.mk "cons"
  let cons ← cons.addSelector "head" (← Srt.int)
  let cons ← cons.addSelectorSelf "tail"
  let decl ← Datatype.Decl.mk "Lst"
  Srt.datatype (← (← decl.addCtor nil).addCtor cons)
end
```

`Srt.datatypes` declares mutually recursive datatypes together, and `Solver.declareDatatype` is a shortcut for one datatype. A name can be declared only once per scope.

# A Lean Type for a Datatype

Terms of a datatype are indexed by a Lean type that stands for it, tied to the datatype's name by a `ToTyp` instance. It is never built, only named in types.

```lean
structure Lst where private mk ::
  deriving DecidableEq, Ord, Hashable

instance : ToTyp Lst := ⟨.datatype "Lst"⟩
```

A `Term Lst` can then be built wherever `Lst` is declared; elsewhere, building its sort fails at run time. Constructors and fields are looked up by name and sort, once, and checked:

```lean (name := dt_ex)
#eval Env.runIO do
  let _ ← declareLst
  let l ← Term.mkSymbolAs Lst "l"

  let consC ← Datatype.ctor Lst "cons"
  let nilC ← Datatype.ctor Lst "nil"
  let head ← consC.field Int "head"
  let tail ← consC.field Lst "tail"

  let one ← consC.apply2 (← Term.mkInt 1) (← nilC.apply)
  println! "value   : {one}"
  println! "head    : {← head.get one}"
  println! "is cons : {← consC.is l}"

  let s ← Solver.new
  s.setOpt .smt_produceModels true
  s.assert (← consC.is l)
  s.assert (← smt! ![head.get l] = 3)
  let empty ← nilC.apply
  s.assert (← smt! ![tail.get l] = empty)
  s.checkSat (ifSat := do
    -- datatypes have no Lean values: print the term
    println! "model   : l = {← s.getValueTerm l}")
```
```leanOutput dt_ex
value   : (cons 1 nil)
head    : (head (cons 1 nil))
is cons : ((_ is cons) l)
model   : l = (cons 3 nil)
```

`smt!` matches on a datatype as Lean does. `_` is the catch-all; any other identifier names a constructor.

```lean (name := dt_match)
#eval Env.runIO do
  let _ ← declareLst
  let l ← Term.mkSymbolAs Lst "l"
  let m ← smt!
    match l with | cons h t => h * 2 | nil => 0
  println! "{m}"
```
```leanOutput dt_match
(match l (((cons h t) (* h 2)) (nil 0)))
```

# Records

A record's index lists its fields, in order: `Record [("x", Int), ("y", Bool)]`. The order is part of the sort, so `{x, y}` and `{y, x}` are different sorts. A record's model value is a Lean `Record` value.

```lean (name := dt_record)
#eval Env.runIO do
  let p ←
    Term.mkSymbolAs (Record [("x", Int), ("y", Bool)]) "p"
  let q ← smt! {p with x := p.x + 1}
  println! "q := {q}"

  let s ← Solver.new
  s.setOpt .smt_produceModels true
  s.assert (← smt! p.y ∧ q = {x := 5, y := true})
  s.checkSat (ifSat := do
    println! "p := {← s.getValue p}")
```
```leanOutput dt_record
q := ((_ update x) p (+ (x p) 1))
p := {x := 4, y := true}
```

Tuples are indexed by Lean products instead, `Term (Int × Bool)`, and built with `Term.mkTuple`.
