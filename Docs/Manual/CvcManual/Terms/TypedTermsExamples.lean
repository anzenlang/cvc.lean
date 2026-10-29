module

public import Cvc
public meta import Cvc
public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Cvc



set_option pp.rawOnError true



#doc (Manual) "Examples" =>

Examples of using term constructors follow, feel free to hover around to make sure the terms are
correctly typed.

```lean (name := terms_ex_typed_basic)
open Typed in #eval Env.runIO do
  let b1 ← Term.mkSymbolAs Bool "b1"
  let b2 ← Term.mkSymbol "b2"
  let conj ← b1.and b2
  println! "conj := {conj}"
  let i1 ← Term.mkSymbol "i1"
  let zero ← Term.mkInt 0
  let i1_pos ← zero.le i1
  println! "i1_pos := {i1_pos}"
  let i2 ← Term.mkSymbol "i2"
  let ite ← i1_pos.ite i1 i2
  println! "ite := {ite}"
```
```leanOutput terms_ex_typed_basic
conj := (and b1 b2)
i1_pos := (<= 0 i1)
ite := (ite (<= 0 i1) i1 i2)
```

Using the `smt!` extension:

```lean
open Typed in #eval Env.runIO do
  let b1 ← Term.mkSymbol "b1"
  let b2 ← Term.mkSymbol "b2"
  let conj ← smt! b1 ∧ b2
  println! "conj := {conj}"
  let i1 ← Term.mkSymbol "i1"
  let i1_pos ← smt! 0 ≤ i1
  println! "i1_pos := {i1_pos}"
  let i2 ← Term.mkSymbol "i2"
  let ite ← smt! if 0 ≤ i1 then i1 else i2
  println! "ite := {ite}"
```

Strong-typing works with functions/function application as well.

```lean (name := terms_ex_typed_fun)
open Typed in #eval Env.runIO do
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  println! "f : {← f.getSort} := {f}"
  let i ← Term.mkSymbol "i"
  let f_i ← f.apply i
  println! "f_i : {← f_i.getSort} := {f_i}"
  let b ← Term.mkSymbol "b"
  let f_i_b ← f_i.apply b
  println! "f_i_b : {← f_i_b.getSort} := {f_i_b}"
  -- alternatively
  let f_i_b' ← f.apply2 i b
  println! "f_i_b' : {← f_i_b'.getSort} := {f_i_b'}"
```
```leanOutput terms_ex_typed_fun
f : (-> Int Bool Int) := f
f_i : (-> Bool Int) := (f i)
f_i_b : Int := (f i b)
f_i_b' : Int := (f i b)
```

Using the `smt!` extension:

```lean
open Typed in #eval Env.runIO do
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  let i ← Term.mkSymbol "i"
  let f_i ← smt! f i
  println! "f_i := {f_i}"
  let b ← Term.mkSymbol "b"
  let f_i_b ← smt! f_i b
  println! "f_i_b := {f_i_b}"

  let f_i_b' ← smt! f i b
  println! "f_i_b' := {f_i_b'}"
```

Of course, type-checking catches any invalid-sort mistake we make.

```lean +error (name := terms_ex_typed_bad_1)
open Typed in #eval Env.runIO do
  let b1 ← Term.mkSymbolAs Bool "b1"
  let b2 ← Term.mkSymbolAs Int "b2"
  let conj ← b1.and b2
  println! "conj := {conj}"
```

Another type-checking error on a ill-typed function application:

```lean +error (name := terms_ex_typed_bad_2)
open Typed in #eval Env.runIO do
  let f ← Term.mkSymbolAs (Bool → String → Rat) "f"
  let b1 ← Term.mkSymbolAs Bool "b1"
  let i1 ← Term.mkSymbolAs Int "i1"
  let f_b1_i1 ← f.apply2 b1 i1
  println! "f_b1_i1 := {f_b1_i1}"
```
