/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Srt
import Cvc.Untyped.Theory.Arith

public meta import Cvc.Srt
public meta import Cvc.Untyped.Theory.Arith



/-! # Scopes

Every `Env.run` makes its own term manager, and `Ω` is what keeps one scope's sorts and terms out
of another. These pin that it does so statically, nested runs included: a sort cannot leave its
scope, and cannot meet a sort of another scope, even when both scopes are open at once.
-/
namespace Cvc.Tests.Scope

open Cvc

/-! Within one scope, nothing changes. -/

/-- info: (Array Int Bool) -/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  println! "{← int.arrayTo bool}"

/-! A sort cannot leave its scope: the result type is chosen where no instance exists, so the type
of a sort cannot even be written there. -/

/--
error: failed to synthesize instance of type class
  Ω

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : IO Srt := Env.runIO Srt.int

/-! Nor can it escape into an *enclosing* scope, where an instance does exist: the inner run's sort
is of the inner scope, which is not the outer one. This compiled while `Ω` was a `Prop`, any two of
whose instances are equal, and was a use-after-free: the inner term manager is gone by then. -/

/--
error: Type mismatch
  Srt.int
has type
  EnvT BaseIO Srt
but is expected to have type
  Env ?m.3

Note: The following definitions were not unfolded because their definition is not exposed:
  Srt ↦ 1
the following variables have been introduced by the implicit lambda feature
  inst✝ : Ω
you can disable implicit lambdas using `@` or writing a lambda expression with `{}` or `[]` binder annotations.
-/
#guard_msgs in
example : IO Unit := Env.runIO do
  let _ : Srt ← Env.runIO Srt.int
  pure ()

/-! And two scopes open at once do not mix: a sort of the outer one is not a sort of the inner.
This also compiled while `Ω` was a `Prop`, cvc5 rejecting it at runtime. -/

/--
error: Application type mismatch: The argument
  bool
has type
  @Srt inst✝
but is expected to have type
  @Srt inst✝¹
in the application
  int.arrayTo bool

Note: The following definitions were not unfolded because their definition is not exposed:
  Srt ↦ 6
---
error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  inst✝
inferred
  inst✝¹
-/
#guard_msgs in
example : IO Unit := Env.runIO do
  let int ← Srt.int
  Env.runIO do
    let bool ← Srt.bool
    discard <| int.arrayTo bool
