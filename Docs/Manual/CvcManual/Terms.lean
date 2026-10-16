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

> *NB:* cvc.lean enforces type-safety through definition irreducibility, which means you need to use Lean's `module` system to get any of its benefits.



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

We can declare constant function symbols by either letting type inference figure out the type for
us, or by providing it explicitly.

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

{include 2 CvcManual.Terms.UntypedTermsExamples}
