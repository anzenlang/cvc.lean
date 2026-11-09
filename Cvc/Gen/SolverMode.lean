/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command

public import Cvc.Basic
public import Cvc.Gen.Term



/-! # Solver-mode monadic environments

An answer from the solver splits the world, and the queries that make sense differ in each branch:
a model exists only where the answer was sat, a synthesis solution only where one was found. Each
branch gets its own monad, privately wrapping `EnvT`.

`env_gen%` fills one in: the `Monad`, `MonadExcept` and lifting instances, including a **private**
lift from `EnvT`. That lift being private is the whole mechanism — user code cannot run arbitrary
`EnvT` code, a check in particular, inside a block that only holds because of an earlier answer.
Private means private *to the module the macro is expanded in*, so a module declaring mode monads
keeps the ability to lift into them and no one else gets it.

A mode monad is declared in two steps, the structure and then the macro:

```lean
/-- Code running where the solver last answered sat. -/
structure EnvSatT (solver : Solver) (m : Type → Type) (α : Type) where
private wrap ::
  private toEnv : EnvT m α

env_gen% EnvSatT / EnvSat
```
-/
namespace Cvc.Untyped public section

section variable [Ω] [Monad m]

/-- Fills in the mode monad `envT` and its `BaseIO` version `env`, as `Cvc.Gen.SolverMode` says. -/
macro "env_gen% " envT:ident " / " env:ident : command =>
  let pureId := Lean.mkIdent `pure
  let bindId := Lean.mkIdent `bind
  let throwId := Lean.mkIdent `throw
  let tryCatchId := Lean.mkIdent `tryCatch
  let baseIOIdent := Lean.mkIdent ``BaseIO
  let solverIdent := Lean.mkIdent `Solver
  `(
@[inherit_doc $envT]
abbrev $env (s : $solverIdent) := $envT s $baseIOIdent

namespace $envT variable {α β : Type} {m : Type → Type} [Monad m] {s : $solverIdent}

/-- Returns `a`. -/
protected def $pureId (a : α) : $envT s m α := ⟨return a⟩
/-- Runs `a`, then `f` on its result. -/
protected def $bindId (a : $envT s m α) (f : α → $envT s m β) : $envT s m β :=
  ⟨a.toEnv.bind (fun a => f a |>.toEnv)⟩

instance [Monad m] : Monad ($envT s m) where
  pure := .$pureId
  bind := .$bindId

/-- Fails with `e`. -/
protected def $throwId (e : Error) : $envT s m α := ⟨throw e⟩
/-- Runs `code`, handing any error it fails with to `errorDo`. -/
protected def $tryCatchId (code : $envT s m α) (errorDo : Error → $envT s m α) : $envT s m α :=
  ⟨code.toEnv.tryCatch fun e => errorDo e |>.toEnv⟩

instance : MonadExcept Error ($envT s m) where
  throw := .$throwId
  tryCatch := .$tryCatchId

/-- Lifts code of the underlying monad. -/
def transformLift (code : m α) : $envT s m α := ⟨code⟩

instance : MonadLift m ($envT s m) := ⟨transformLift⟩

/-- Lifts `IO` code, such as printing. -/
def liftIO [MonadLiftT BaseIO m] (ioCode : IO α) : $envT s m α := .wrap ioCode

instance [MonadLiftT BaseIO m] : MonadLift IO ($envT s m) := ⟨liftIO⟩

/-- Lifts `EnvT` code. -/
private def lift : EnvT m α → $envT s m α := .wrap
-- Private on purpose: it would let a check-sat run inside a block that only holds because of an
-- earlier answer.

private instance : MonadLift (EnvT m) ($envT s m) := ⟨lift⟩

/-- Lifts the `BaseIO` version of this mode into one over another monad. -/
def liftMonadVersion [Monad m] [MonadLiftT BaseIO m] (code : $env s α) : $envT s m α :=
  ⟨liftM code.toEnv⟩
instance [Monad m] [MonadLiftT BaseIO m] : MonadLift ($env s) ($envT s m) := ⟨liftMonadVersion⟩
end $envT
  )

end

end
