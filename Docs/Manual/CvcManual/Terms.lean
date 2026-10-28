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
import all Cvc.Typed.Theory.Arith

import all Cvc.Untyped.Core.Bool
import all Cvc.Untyped.Core.Defs
import all Cvc.Untyped.Theory.Arith

public import VersoManual

import CvcManual.Terms.TypedTermsExamples
import CvcManual.Terms.UntypedTermsExamples

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

Cvc.lean exposes two API-s for terms: `Typed` and `Untyped`. The former provides very strong static
guarantees by strongly-typing terms; the latter does not but is more flexible, allowing in
particular to build lists/arrays of terms of different sorts.

> *NB:* cvc.lean enforces type-safety through definition irreducibility, which means you need to
> use Lean's `module` system to get any of its benefits.

Terms can be constructed by calling constructor-functions, but cvc.lean also provides a syntax
extension `smt! ...` that supports Lean-like syntax to create terms. This discussion below presents
both, but the rest of this document will almost always rely on the syntax extension.



# Typed Terms

{docstring Typed.Term}

Typed terms have a type parameter for the actual `Srt` of that term.
We saw previously that `ToTyp` links types to `Srt`-s, and it is precisely the mechanism used here.
Typing terms lets us check statically that term constructors are invoked in a valid way, and makes
their signature as precise as it can be.

{docstring Typed.Term.mkBool}
{docstring Typed.Term.and}
{docstring Typed.Term.mkInt}

Some term operators are polymorphic: addition for instance works on any arithmetic terms as long as
they have the same sort.

{docstring Typed.Term.add}

Notice that the type-class constraint `IsArith α` must hold, which asks for a proof that the `Typ`
associated to `α` is actually arithmetic.

{docstring IsArith}

We can declare function symbols by either letting type inference figure out the type for us, or by
providing it explicitly.

{docstring Typed.Term.mkSymbol}
{docstring Typed.Term.mkSymbolAs}

{include 2 CvcManual.Terms.TypedTermsExamples}



# Untyped Terms

{docstring Untyped.Term}

Untyped terms do not have a type parameter corresponding to their sort, which means untyped term
constructors do not provide any static guarantee that the result is a valid term. Instead, invalid
terms will fail at runtime.

{docstring Untyped.Term.mkBool}
{docstring Untyped.Term.and}
{docstring Untyped.Term.mkInt}

Unlike the typed API, the sort of an untyped term for a function symbol cannot be inferred and must
be given explicitly. The first way to do so is to pass the actual sort.

{docstring Untyped.Term.mkSymbol}

The second way is to pass the Lean type that we would use to create a typed term.

{docstring Untyped.Term.mkSymbolAs}

{include 2 CvcManual.Terms.UntypedTermsExamples}



# Conversions between typed terms and untyped terms

```lean -show
namespace Conversions
variable [Ω]
```

## Untyped to typed

The {lean}`Untyped.Term.typeCheckAs` type-checks at runtime an untyped term against (the sort
associated to) a static type to produce a typed term.

{docstring Untyped.Term.typeCheckAs}

If the term's type can be inferred from context, `Untyped.Term.typeCheck` is more concise
alternative.

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

This direction is simpler in that it cannot fail since we're simply erasing compile-time type
information.

{docstring Typed.Term.erase}

For example:

```lean (name := ex_Terms_erase)
open Typed in
#eval Env.runIO do
  let x ← Term.mkSymbol "x"
  let typedTerm ← smt! x ∨ false
  --  ^^^^^^^^^~~~~~ `Typed.Term Bool`
  println! "typedTerm:  {typedTerm}"
  let erasedTerm := typedTerm.erase
  --  ^^^^^^^^^^~~~~ `Untyped.Term`
  println! "erasedTerm: {erasedTerm}"
```

```leanOutput ex_Terms_erase
typedTerm:  (or x false)
erasedTerm: (or x false)
```

```lean -show
end Conversions
```
