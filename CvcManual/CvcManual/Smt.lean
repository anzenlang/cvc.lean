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



#doc (Manual) "The `smt!` Notation" =>
%%%
tag := "smt"
file := "Smt"
htmlSplit := .never
%%%

`smt! t` builds the term `t`, written in a syntax close to Lean's own, as an `Env` action: `← smt! x + 1 < y`. With `open Cvc.Typed` it builds typed terms, with `open Cvc.Untyped` sort-erased ones.

Each form is defined by the theory it belongs to, so `smt!` accepts a form only where that theory is imported; `import Cvc` imports them all.

```lean (name := smt_ex)
open Cvc Typed in
#eval Env.runIO do
  let x ← Term.mkSymbolAs Int "x"
  let b ← Term.mkSymbolAs Bool "b"
  let f ← Term.mkSymbolAs (Int → Int) "f"
  let two ← Term.mkInt 2
  println! "{← smt! if b ∧ x ≥ 0 then f (x + 1) else -x}"
  let q ← smt!
    let y ← x * 2; ∀ (z : Int), z < y → f z ≠ y
  println! "{q}"
  println! "{← smt! (fun (z : Int) => z % 2 = 1) x}"
  println! "{← smt! <[0, x, 10]}"
  println! "{← smt! ![x.intDiv two] = 1}"
```
```leanOutput smt_ex
(ite (and b (>= x 0)) (f (+ x 1)) (- x))
(forall ((z Int)) (let ((_let_1 (* x 2))) (=> (< z _let_1) (distinct (f z) _let_1))))
(@ (lambda ((z Int)) (= (mod z 2) 1)) x)
(and (< 0 x) (< x 10))
(= (div x 2) 1)
```

# Forms

:::table +header
*
  * form
  * meaning
*
  * `x`, `f a b`
  * a term in scope (a symbol, a bound variable, …), and application
*
  * `(t)`
  * grouping
*
  * `![e]`
  * any Lean term of type `Env (Term …)`
*
  * `let x ← t; u`
  * `u`, where `x` stands for `t`
*
  * `fun (x : T) => t` or `λ (x : T) => t`
  * a lambda
*
  * `∀ (x y : T), t` and `∃ (x y : T), t`
  * quantifiers
*
  * `true`, `false`, `if c then t else e`
  * Booleans and if-then-else
*
  * `1`, `1.5`, `"abc"`
  * an `Int`, a `Rat` (cvc5's `Real`), a `String`
*
  * `match t with | ctor x y => u | _ => v`
  * a match on a datatype, see {ref "datatypes"}[datatypes]
*
  * `{a := t, b := u}`, `{r with a := t}`, `r.a`, `e |>.a`
  * records, see {ref "datatypes"}[datatypes]
:::

`T` is a Lean type in the typed layer; in the sort-erased one, it may also be a `Srt`.

# Operators

Operators use Lean's symbols, at Lean's precedences.

:::table +header
*
  * operators
  * operations
*
  * `¬`, `∧`, `∨`, `→`, `⊻`
  * Boolean connectives
*
  * `=`, `≠`
  * equality and distinctness
*
  * `+`, `-`, `*`, `%`, unary `-`
  * arithmetic, `%` being integer modulus
*
  * `<`, `≤`, `>`, `≥`
  * comparisons
*
  * `&&&`, `|||`, `^^^`, `<<<`, `>>>`
  * bit-vector and, or, xor, left shift and logical right shift
*
  * `∈`, `⊆`, `∪`, `∩`, `∖`
  * sets
*
  * `⊎`
  * disjoint bag union
*
  * `++`
  * sequence concatenation
:::

The binary operators `→ = ≠ < ≤ > ≥ + - * ⊻ ∪ ∩ ∖ ⊎ ++ ∧ ∨` also have an n-ary form in brackets: `∧[a, b, c]`, `+[x, y, z]`, and `<[0, x, 10]`, which chains: `0 < x ∧ x < 10`.

An operation with no notation, such as division, is written with its term constructor and `![…]`, as in the last line of the example above.

Grammars and regular expressions have notations of their own, `smt.grammar!` and `regex!`.
