/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Gen.Term
import all Cvc.Defs

import all Cvc.Typed.Core.Bool
import all Cvc.Typed.Core.Defs
import all Cvc.Typed.Core.BVar
import all Cvc.Typed.Theory.Arith
import all Cvc.Typed.Theory.Quant

import all Cvc.Untyped.Core.Bool
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.Theory.Arith

public import VersoManual

import CvcManual.Terms.TypedTermsExamples
import CvcManual.Terms.UntypedTermsExamples
import CvcManual.Terms.Views

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Cvc



set_option pp.rawOnError true



#doc (Manual) "Terms" =>
%%%
tag := "termsOverview"
htmlSplit := .never
%%%

Cvc.lean exposes two API-s for terms: `Typed` and `Untyped`. The former provides very strong static guarantees by strongly-typing terms; the latter does not but is more flexible, allowing in particular to build lists/arrays of terms of different sorts.

> *NB:* cvc.lean enforces type-safety through definition irreducibility, which means you need to use Lean's `module` system to get any of its benefits.

Terms can be constructed by calling constructor-functions, but cvc.lean also provides a syntax extension `smt! ...` that supports Lean-like syntax to create terms. This discussion below presents both, but the rest of this document will almost always rely on the syntax extension.



# Typed Terms

{docstring Typed.Term}

Typed terms have a type parameter for the actual `Srt` of that term. We saw previously that `ToTyp` links types to `Srt`-s, and it is precisely the mechanism used here. Typing terms lets us check statically that term constructors are invoked in a valid way, and makes their signature as precise as it can be.

{docstring Typed.Term.mkBool}
{docstring Typed.Term.and}
{docstring Typed.Term.mkInt}

Some term operators are polymorphic: addition for instance works on any arithmetic terms as long as they have the same sort.

{docstring Typed.Term.add}

Notice that the type-class constraint `IsArith α` must hold, which asks for a proof that the `Typ` associated to `α` is actually arithmetic.

{docstring IsArith}

We can declare function symbols by either letting type inference figure out the type for us, or by providing it explicitly.

{docstring Typed.Term.mkSymbol}
{docstring Typed.Term.mkSymbolAs}

{include 2 CvcManual.Terms.TypedTermsExamples}



# Untyped Terms

{docstring Untyped.Term}

Untyped terms do not have a type parameter corresponding to their sort, which means untyped term constructors do not provide any static guarantee that the result is a valid term. Instead, invalid terms will fail at runtime.

{docstring Untyped.Term.mkBool}
{docstring Untyped.Term.and}
{docstring Untyped.Term.mkInt}

Unlike the typed API, the sort of an untyped term for a function symbol cannot be inferred and must be given explicitly. The first way to do so is to pass the actual sort.

{docstring Untyped.Term.mkSymbol}

The second way is to pass the Lean type that we would use to create a typed term.

{docstring Untyped.Term.mkSymbolAs}

{include 2 CvcManual.Terms.UntypedTermsExamples}



# Untyped/typed conversions

```lean -show
namespace Conversions
variable [Ω]
```

## Untyped to typed

The {lean}`Untyped.Term.typeCheckAs` type-checks at runtime an untyped term against (the sort associated to) a static type to produce a typed term.

{docstring Untyped.Term.typeCheckAs}

If the term's type can be inferred from context, `Untyped.Term.typeCheck` is more concise alternative.

{docstring Untyped.Term.typeCheck}

For example:

```lean (name := ex_Terms_typeCheckAs)
open Untyped in
#eval Env.runIO do
  let bool ← Srt.bool
  let x ← Term.mkSymbol bool "x"

  let boolTerm ← smt! x ∨ false
  println! "boolTerm:  {boolTerm}"

  let typedTerm ← boolTerm.typeCheckAs Bool
  println! "typedTerm: {typedTerm}"

  let boolToInt (t : Typed.Term Bool) :=
    smt! if t then 1 else 0
  let iteTerm ← boolTerm.typeCheck >>= boolToInt
  println! "iteTerm:   {iteTerm}"

  println! ""
  try
    let illTypedTerm ← boolTerm.typeCheckAs Int
    println! "unexpected: {illTypedTerm}"
  catch e =>
    println! "{e}"
```

```leanOutput ex_Terms_typeCheckAs
boolTerm:  (or x false)
typedTerm: (or x false)
iteTerm:   (ite (or x false) 1 0)

cannot type the following term as `Int`, term has sort `Bool`:
(or x false)
```

## Typed to untyped

This direction is simpler in that it cannot fail: a typed term already *is* a sort-erased one, and
`relax` merely forgets its index.

{docstring Typed.Term.relax}

For example:

```lean (name := ex_Terms_relax)
open Typed in
#eval Env.runIO do
  let x ← Term.mkSymbol "x"
  let typedTerm ← smt! x ∨ false
  --  ^^^^^^^^^~~~~~ `Typed.Term Bool`
  println! "typedTerm:   {typedTerm}"
  let relaxedTerm := typedTerm.relax
  --  ^^^^^^^^^^^~~~~ `Untyped.Term`
  println! "relaxedTerm: {relaxedTerm}"
```

```leanOutput ex_Terms_relax
typedTerm:   (or x false)
relaxedTerm: (or x false)
```

Every typed value that wraps a sort-erased one relaxes the same way, under the same name: a bound
variable (`Typed.BVar.relax`), a grammar and its non-terminals (`Typed.Grammar.relax`,
`Typed.NT.relax`), a separation-logic heap (`Typed.Solver.Heap.relax`), and a solver
(`Typed.Solver.relax`), which costs nothing at all since both layers share one solver type.

```lean -show
end Conversions
```

# Bound variables, lambdas, quantifiers

```lean -show
open Typed
variable [Ω]
```

Cvc.lean's typed API types bound variables just like it types terms.

{docstring Cvc.Typed.BVar}

It also provides a type for collections of {lean}`BVar`-s.

{docstring Cvc.Typed.BVars}

> The untyped API for bound variables is very similar but with no type information. {lean}`Cvc.Untyped.BVars` is thus simply an array of untyped bound variables, and all checks are performed at runtime. We only present the typed API in this section.

As long as this list of bound variables (and their type) is known statically, functions such as {lean}`Term.lambda` are able to deconstruct it and infer the type of the corresponding function.

## Lambdas

{docstring Cvc.Typed.Term.lambda}

This first example builds the bound variables list and the lambda term by hand, see below for a much more concise version using `smt!`.

```lean (name := ex_BoundVars_lambda1)
#eval Env.runIO do
  let i1 ← Term.mkSymbolAs Int "i1"
  let bv_b ← BVar.mk "b"
  let bv_i2 ← BVar.mk "i2"
  let bv_r ← BVar.mk "r"
  let bVars :=
    BVars.empty |>.push bv_b |>.push bv_i2 |>.push bv_r
  --  vvv~~~ `Term (Bool → Int → Rat → Bool)`
  let lam ← Term.lambda bVars
    (← smt! if bv_b then i1 < bv_i2 else bv_r = 0.0)
  println! "lam := {lam}"

  let b ← Term.mkSymbol "b"
  let r ← Term.mkSymbol "r"
  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  smt! lam b i1 r >>= solver.assert
  solver.checkSat (ifSat := do
    println! "sat"
    println! "- b  := {← b.getValue}"
    println! "- i1 := {← i1.getValue}"
    println! "- r  := {← r.getValue}")
```
```leanOutput ex_BoundVars_lambda1
lam := (lambda ((b Bool) (i2 Int) (r Real)) (ite b (< i1 i2) (= r 0.0)))
sat
- b  := false
- i1 := 0
- r  := 0
```

Using the `smt!` syntax extension:

```lean (name := ex_BoundVars_lambda2)
#eval Env.runIO do
  let i1 ← Term.mkSymbolAs Int "i1"
  let lam ← smt!
    -- feel free to use `λ` instead of `fun`
    fun (b : Bool) (i2 : Int) (r : Rat) =>
      if b then i1 < i2 else r = 0.0
  println! "lam := {lam}"

  let b ← Term.mkSymbol "b"
  let r ← Term.mkSymbol "r"
  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  smt! lam b i1 r >>= solver.assert
  solver.checkSat (ifSat := do
    println! "sat"
    println! "- b  := {← b.getValue}"
    println! "- i1 := {← i1.getValue}"
    println! "- r  := {← r.getValue}")
```
```leanOutput ex_BoundVars_lambda2
lam := (lambda ((b Bool) (i2 Int) (r Real)) (ite b (< i1 i2) (= r 0.0)))
sat
- b  := false
- i1 := 0
- r  := 0
```

## Quantifiers

Unlike lambdas, quantifier terms simply have sort `Bool` which makes typing much easier.

{docstring Cvc.Typed.Term.mkForall}
{docstring Cvc.Typed.Term.mkExists}

Here is an example of building quantified terms by hand, `smt!` version below.

```lean (name := ex_BoundVars_quant1)
#eval Env.runIO do
  let n ← Term.mkSymbolAs Int "n"
  let i ← Term.mkBVar "i"
  let j ← Term.mkBVar "j"
  let bVars_j := BVars.empty.push j
  let all_le ← Term.mkForall bVars_j (← smt! n < j → i < j)
  let bVars_i := BVars.empty.push i
  let exists_i ← Term.mkExists bVars_i all_le
  println! "exists_i := {exists_i}"

  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  solver.assert exists_i
  solver.checkSat (ifSat := do
    println! "sat"
    println! "- n := {← n.getValue}")
```
```leanOutput ex_BoundVars_quant1
exists_i := (exists ((i Int)) (forall ((j Int)) (=> (< n j) (< i j))))
sat
- n := -1
```

With the `smt!` extension:

```lean (name := ex_BoundVars_quant2)
#eval Env.runIO do
  let n ← Term.mkSymbolAs Int "n"
  let exists_i ← smt!
    ∃ (i : Int), ∀ (j : Int), n < j → i < j
  println! "exists_i := {exists_i}"

  let solver ← Solver.new
  solver.setOpt .smt_produceModels true
  solver.assert exists_i
  solver.checkSat (ifSat := do
    println! "sat"
    println! "- n := {← n.getValue}"
  )
```
```leanOutput ex_BoundVars_quant2
exists_i := (exists ((i Int)) (forall ((j Int)) (=> (< n j) (< i j))))
sat
- n := -1
```

{include 1 CvcManual.Terms.Views}
