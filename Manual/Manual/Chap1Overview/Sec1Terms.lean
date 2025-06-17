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


#doc (Manual) "Terms" =>

%%%
tag := "chapOverview_terms"
%%%

::::leanSection
```lean (show := false)
variable (α : Type)
```

{lean}`Cvc.Term α` represents a cvc5 term of some type {lean}`α`.
{margin}[
  In practice, most cvc.lean features expect {lean}`α` to have a {lean}`IsSrt α` instance,
  which guarantees that {lean}`α` corresponds to some SMT sort ({lean}`Srt`).
]
::::

{docstring Term}

For this introduction, we will mostly use {lean}`Term Int` and {lean}`Term Bool` for the
sake of simplicity. Note that these term variants are often mentioned through aliases:

{docstring Formula}

{docstring Term.Int}

{docstring Term.Bool}

Since cvc.lean are actually `C++`-level cvc5 terms, almost all term management relies on FFI with
the `C++` cvc5 API. Term management relies on the {lean}`Term.Build` error/state monad,
{margin}[
  For the monad *transformer* version, see {lean}`Term.BuildT`.
]
for instance for term creation.




Here are a few term-creation functions, note that they are all in the {lean}`Term` namespace but
produce results in the {lean}`Term.Build` monad.

{docstring Term.int}

{docstring Term.bool}

{docstring Term.equal}

{docstring Term.and}

{docstring Term.ite}

Let's see this in action.

```savedLean (name := termDemo1)
#eval Cvc.Term.Build.runIO do
  let seven ← Term.int 7
  let five ← Term.int 5
  let cnd ← (← Term.bool true).and (← seven.equal five)
  let ite ← cnd.ite (← Term.int 21) (← Term.int 12)
  println! "ite: {ite}"
```

```leanOutput termDemo1
ite: (ite (and true (= 7 5)) 21 12)
```

That's not great, we can see that for complex terms the syntax will become painful very fast.
Cvc.lean provides an `smt!` syntax extension so that we can write {lean}`Term`s like we would lean
propositions.

```savedLean (name := termDemo2)
open Cvc.Term.Dsl in
#eval Cvc.Term.Build.runIO do
  let seven ← smt! 7
  let five ← smt! 5
  let cnd ← smt! true ∧ seven = five
  let ite ← smt! if cnd then 21 else 12
  println! "ite: {ite}"
```

```leanOutput termDemo2
ite: (ite (and true (= 7 5)) 21 12)
```

Writing the final term as just one line is way more readable:

```savedLean (name := termDemo2)
open Cvc.Term.Dsl in
#eval Cvc.Term.Build.runIO do
  let ite ← smt! if true ∧ 7 = 5 then 21 else 12
  println! "ite: {ite}"
```

```leanOutput termDemo2
ite: (ite (and true (= 7 5)) 21 12)
```
