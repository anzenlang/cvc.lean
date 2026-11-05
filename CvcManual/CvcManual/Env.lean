/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

meta import all Cvc.Basic.Env
meta import all Cvc.Srt
meta import all Cvc.Defs

public import Cvc
public import VersoManual

public import CvcManual.Env.SafetyErrors

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Cvc



set_option pp.rawOnError true



#doc (Manual) "Environment" =>
%%%
tag := "envOverview"
htmlSplit := .never
%%%

```lean -show
open Cvc variable [inst : Ω] {α : Type}
```


The cvc5 types for terms, sorts, solvers, _etc._ are all related to a notion of _(term) manager_ {index}[manager] responsible for allocating and indexing terms and sorts. These types cannot interact and will produce a runtime error if they do not agree on their manager.

# `Ω`

This API abstracts away the term manager completely and enforces manager-consistency statically using a type-class called {lean}`Ω`. Virtually all types in this library have an implicit {lean}`Ω` argument that can be thought of as representing a specific term manager. On the sort type for instance:

```lean (name := ex_Srt)
#check Srt
```
```leanOutput ex_Srt
Cvc.Srt [Ω] : Type
```

{lean}`Ω` is a type class whose only field is itself a type, so an instance costs nothing at runtime: it compiles to a constant. It is deliberately not a {lean}`Prop`, since any two proofs of a proposition are equal, which would make every scope's sorts and terms interchangeable. You cannot build an instance yourself, as the constructor is private.

{docstring Ω}

{lean}`Ω` is tied to cvc.lean's environment monad {lean}`Env`: {lean}`Env α`, or more precisely {lean}`@Env inst α` where {lean}`(inst : Ω)`, corresponds to code that uses a specific term manager to produce a value of type `α`.
Cvc5's term manager handles term/sort perfect sharing{margin}[Also known as _hash-consing_: building the same term twice produces the same (reference to the same) term, meaning physical (reference) equality is structural equality.].

The first problem {lean}`Ω` and {lean}`Env` solve is that manipulating a value `v` tied to manager `m` after `m` has been freed is unsafe as freeing `m` frees `v`, so `v` should only live as long as `m` is alive. So most features in this library produce an {lean}`Env _` output.

Second, as mentioned above, values tied to different managers should never interact as that would cause a runtime error. By encoding a specific term manager through an {lean}`Ω`-value, cvc.lean can type-check that sorts/terms/solvers/_etc._ are compatible by making sure they agree on their {lean}`Ω`-value.

For example, the function building an array-sort makes sure the index and element sorts agree on their manager, and keeps track of the manager associated to the resulting sort by having all of them agree on their {lean}`Ω`.

{docstring Srt.arrayTo}



# Environment

Most functions in this library are in the {lean}`Env` monad, built on top of the {lean}`EnvT` monad transformer.

```lean (name := env_ex_EnvT)
#check EnvT
```
```leanOutput env_ex_EnvT
Cvc.EnvT [Ω] (m : Type → Type) (α : Type) : Type
```

Be careful that, in practice, {lean}`EnvT` works on monads that lift {lean}`BaseIO` so that it can call the cvc5 C++ API.{margin}[Also for maintaining its state efficiently as a mutable reference.] {lean}`Env` is simply {lean}`EnvT BaseIO`.

{docstring Env}

The only way to run {lean}`Env`-code is through its `run`-like functions. The simplest one is `Env.run` and produces a {lean}`BaseIO (Res α)` where {lean}`Res` is {lean}`Except` specialized to cvc.lean's {lean}`Error` type.

```lean (name := check_Env_run)
#check Env.run
```
```leanOutput check_Env_run
Cvc.Env.run {α : Type} (code : [inst : Ω] → Env α) : BaseIO (Res α)
```

```lean -show
section var_code variable (code : [inst : Ω] → Env α)
```

Notice that this function quantifies the {lean}`Ω`-instance {lean}`inst` for {lean}`code`. This guarantees that whatever {lean}`α` is, it _cannot_ mention {lean}`inst` in any way, so it is not possible for {lean}`code` to return, say, an {lean}`Srt`-value as it would require {lean}`inst` to escape its scope.{margin}[This design is heavily inspired by Lean's [`ST`/`ST.Ref`][lean_ST].]

```lean -show
end var_code
```

Now, to manipulate {lean}`Env` or virtually any type from the cvc.lean we need to have an {lean}`Ω`-instance in scope. We could have {lean}`[Ω]` as an argument of all our definitions, but it is often easier to have it as a variable.

```lean
variable [Ω]
```

We can now forget about {lean}`Ω` completely and write a few {lean}`Srt`-using {lean}`Env` functions:{margin}[The only time you should be reminded of {lean}`Ω` is when you are doing something memory-unsafe such as mixing terms/sorts/solvers.]

```lean
def mkArrayBoolTo (srt : Srt) : Env Srt := do
  srt.arrayFrom (← Srt.bool)

def codeInEnv : Env Unit := do
  let real ← Srt.real
  let array ← mkArrayBoolTo real
  println! "array sort := {array}"
```

Next we can use `Env.run` to actually run this code.

```lean (name := eval_Env_demo1)
def test1 : IO Unit := do
  match ← Env.run codeInEnv with
  | .ok () => println! "success"
  | .error e => println! "an error occurred:\n{e}"

#eval test1
```
```leanOutput eval_Env_demo1
array sort := (Array Bool Real)
success
```

Running with `Env.runIO` lifts cvc.lean's errors to `IO` and makes this simple test much more straightforward.

```lean (name := eval_Env_demo2)
#eval Env.runIO codeInEnv
```
```leanOutput eval_Env_demo2
array sort := (Array Bool Real)
```


{include 1 CvcManual.Env.SafetyErrors}



[lean_ST]: https://leanprover-community.github.io/mathlib4_docs/Init/System/ST.html#ST
