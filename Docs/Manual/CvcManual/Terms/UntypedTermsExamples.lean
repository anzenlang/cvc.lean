

module

public import Cvc
public meta import Cvc
public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Cvc



set_option pp.rawOnError true
set_option verso.docstring.allowMissing true



#doc (Manual) "Examples" =>

Below is the untyped version of the first typed-term example. No type-inference can take place, so we must always specify what the sort of each symbol is.

```lean (name := term_ex_untyped_1)
open Untyped in #eval Env.runIO do
  -- specify the sort using Lean types...
  let b1 ← Term.mkSymbolAs Bool "b1"
  -- ...or using `Srt` values
  let bool ← Srt.bool
  let b2 ← Term.mkSymbol bool "b2"
  let conj ← b1.and b2
  println! "conj := {conj}"
  let i1 ← Term.mkSymbolAs Int "i1"
  let zero ← Term.mkInt 0
  let i1_pos ← zero.le i1
  println! "i1_pos := {i1_pos}"
  let i2 ← Term.mkSymbolAs Int "i2"
  let ite ← i1_pos.ite i1 i2
  println! "ite := {ite}"
```
```leanOutput term_ex_untyped_1
conj := (and b1 b2)
i1_pos := (<= 0 i1)
ite := (ite (<= 0 i1) i1 i2)
```

Using the `smt!` extension:

```lean
open Untyped in #eval Env.runIO do
  let b1 ← Term.mkSymbolAs Bool "b1"
  let b2 ← Term.mkSymbolAs Bool "b2"
  let conj ← smt! b1 ∧ b2
  println! "conj := {conj}"
  let i1 ← Term.mkSymbolAs Int "i1"
  let i1_pos ← smt! 0 ≤ i1
  println! "i1_pos := {i1_pos}"
  let i2 ← Term.mkSymbolAs Int "i2"
  let ite ← smt! if 0 ≤ i1 then i1 else i2
  println! "ite := {ite}"
```

On functions:

```lean (name := terms_ex_typed_fun)
open Untyped in #eval Env.runIO do
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  println! "f : {← f.getSort} := {f}"
  let i ← Term.mkSymbolAs Int "i"
  let f_i ← f.apply i
  println! "f_i : {← f_i.getSort} := {f_i}"
  let b ← Term.mkSymbolAs Bool "b"
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
open Untyped in #eval Env.runIO do
  let f ← Term.mkSymbolAs (Int → Bool → Int) "f"
  let i ← Term.mkSymbolAs Int "i"
  let f_i ← smt! f i
  println! "f_i := {f_i}"
  let b ← Term.mkSymbolAs Bool "b"
  let f_i_b ← smt! f_i b
  println! "f_i_b := {f_i_b}"

  let f_i_b' ← smt! f i b
  println! "f_i_b' := {f_i_b'}"
```

Since no type-checking is taking place, we can compile invalid terms without issue.

```lean
section variable [Ω] open Untyped
def badTerms : Env Unit := do
  let b1 ← Term.mkSymbolAs Bool "b1"
  let b2 ← Term.mkSymbolAs Int "b2"
  let conj ← b1.and b2
  println! "conj := {conj}"
end
```

Running that code fails with a relatively obscure error.

```lean +error (name := term_ex_untyped_bad_1)
#eval Env.runIO badTerms
```
```leanOutput term_ex_untyped_bad_1
[internal] expecting a Boolean subexpression
```
