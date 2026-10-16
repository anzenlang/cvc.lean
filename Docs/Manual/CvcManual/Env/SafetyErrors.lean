module

public import Cvc
public meta import Cvc
public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Cvc


set_option pp.rawOnError true


namespace Cvc.Manual.Env.SafetyErrors


#doc (Manual) "Safety errors" =>
%%%
tag := "envOverview.safetyErrors"
htmlSplit := .never
%%%


```lean -show
variable [Ω]
```


Using a cvc.lean type after its manager has been freed is rejected due to the quantification of the
{lean}`Ω` instance. While this guarantees no use-after-free, the error message is a regular lean
type-error and its meaning is pretty obscure.

```lean +error (name := env_ex_dangling)
def mkSort : Env Srt := Srt.int

#eval do
  let sortWithDeadTermManager ← Env.runIO mkSort
  println! "dangling pointer: {sortWithDeadTermManager}"
```
```leanOutput env_ex_dangling
Type mismatch
  mkSort
has type
  Env Srt
but is expected to have type
  Env ?m.6

Note: The following definitions were not unfolded because their definition is not exposed:
  Srt ↦ 2
```

Using a sort from in an environment different from its native one is also a type error.

```lean +error (name := env_ex_unsafe_mix)
def mkBoolSort : Env Srt := Srt.bool

#eval Env.runIO do
  -- let's call `ω` the current environment
  let int ← Srt.int
  Env.runIO do
    -- we're now in a different environment `ω'`
    let bool ← mkBoolSort
    let array ← int.arrayTo bool
```
```leanOutput env_ex_unsafe_mix
Application type mismatch: The argument
  bool
has type
  @Srt inst✝
but is expected to have type
  @Srt inst✝¹
in the application
  int.arrayTo bool

Note: The following definitions were not unfolded because their definition is not exposed:
  Srt ↦ 6
```
