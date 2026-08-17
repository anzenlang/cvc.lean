/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Error
public import Cvc.Basic.Error
public import cvc5
public import Std.Data.HashMap.Basic



/-! # `Ω` class and environment monad

The scope's state carries a **registry of declared sorts** alongside the term manager. That is what
makes a datatype nameable by `ToTyp`: see `State`.

## `Ω` class

Most of the types and functions in this library have an implicit `Ω`-class parameter. Under the hood
cvc5 has a notion of *term manager*, and term/sort/solver/*etc.* can only be used with
term/sort/solver/*etc.* if they user/are managed by the same term manager. Values of class `Ω`
encode belonging to a specific term manager, causing compilation errors when two quantities are not
guaranteed to agree on their manager.

> Note that this library does not expose term managers directly, precisely to avoid runtime errors
> related to using different term managers.

`Ω`'s design is heavily inspired by `ST.Ref` and `StateRefT'`, and it provides the same *scoping*
property: it is not possible to use an `Ω`-sort/term/solver/*etc.* after its underlying manager has
been destroyed (which would cause a runtime error); see `Env.run` for details.

## Environment monad

Almost all sort/term/solver operations happen in the `Env` monad (and/or its transformer, `EnvT`).
An `Ω`-`Env` allows creating and operating on `Ω`-sorts, `Ω`-terms, `Ω`-solvers, *etc.* which are
guaranteed to be compatible.

-/
namespace Cvc public section

open cvc5 renaming Error → Error5, TermManager → Tm, Env → Env5, EnvT → Env5T



namespace Error
/-- Conversion to `cvc5` errors. -/
private def toUnsafe : Error → cvc5.Error
| .internal "a value is missing" => .missingValue
| .internal msg => .error s!"[internal] {msg}"
| .unsupported msg => .unsupported msg
| .user msg => .error msg
| .io msg => .error s!"[io] {msg}"

/-- Constructor from `cvc5` errors. -/
private def ofUnsafe : cvc5.Error → Error
| .missingValue => .internal "a value is missing"
| .error msg => .internal s!"{msg}"
| .option msg => .internal s!"option error: {msg}"
| .unsupported msg => .unsupported msg
| .recoverable msg => .internal s!"recoverable: {msg}"

private instance : MonadLift (Except cvc5.Error) (Except Error) where
  monadLift
  | .ok res => .ok res
  | .error e => .error (ofUnsafe e)
end Error

private def liftRes5 (code : Except Error5 α) : Except Error α := code.mapError Error.ofUnsafe



class Ω : Prop where private mk ::

/-- What an `Env` threads.

The term manager, plus the sorts that had to be **declared** rather than built. cvc5 makes a
*fresh* sort every time one is declared, even from an identical declaration, so a datatype sort
cannot be recovered by rebuilding it — see `Typ.toSrt`. Keeping it here is what lets `ToTyp` name a
datatype: the `Typ` carries the name, and the sort is looked up.

Keyed by name. Two datatypes declared under one name in the same scope therefore alias, which is
why the declaration functions reject a name already taken.
-/
structure State where
  private mk ::
  /-- The term manager every sort and term of this scope belongs to. -/
  private tm : Tm
  /-- Sorts that were declared, by name. -/
  private declaredSorts : Std.HashMap String cvc5.Sort := {}

structure EnvT [Ω] (m : Type → Type) (α : Type) : Type where private mk ::
  private runOn : StateRefT' IO.RealWorld State (ResT m) α

@[expose]
def Env [Ω] : (α : Type) → Type := EnvT BaseIO

namespace EnvT variable [Ω] [M : Monad m]

protected def pure (a : α) : EnvT m α := ⟨fun _ => M.pure (.ok a)⟩

protected def bind (code : EnvT m α) (f : α → EnvT m β) : EnvT m β where
  runOn state := do
    let a ← code.runOn state
    f a |>.runOn state

instance : Monad (EnvT m) where
  pure := EnvT.pure
  bind := EnvT.bind

def liftBaseIO [MonadLiftT BaseIO m] (code : BaseIO α) : EnvT m α where runOn _ := code

instance [MonadLiftT BaseIO m] : MonadLift BaseIO (EnvT m) := ⟨liftBaseIO⟩

def liftIO [MonadLiftT BaseIO m] (code : IO α) : EnvT m α where runOn _ := do
  match ← code.toBaseIO with
  | .ok a => return a
  | .error e => throwIO e

instance [MonadLiftT BaseIO m] : MonadLift IO (EnvT m) := ⟨liftIO⟩

def liftEnv [L : MonadLiftT BaseIO m] (code : Env α) : EnvT m α where
  runOn := L.monadLift ∘ code.runOn

instance [MonadLiftT BaseIO m] : MonadLift Env (EnvT m) := ⟨liftEnv⟩

def liftResT (a? : ResT m α) : EnvT m α where
  runOn _state := a?

instance : MonadLift (ResT m) (EnvT m) := ⟨liftResT⟩
example [L : MonadLiftT BaseIO m] : MonadLift Env (EnvT m) where
  monadLift code := ⟨L.monadLift ∘ code.runOn⟩



section sanity
example : MonadLiftT Res (EnvT m) := inferInstance
end sanity

protected def throw (e : Error) : EnvT m α where
  runOn _state := throw e

protected def tryCatch (code : EnvT m α) (errorDo : Error → EnvT m α) : EnvT m α where
  runOn state := try code.runOn state catch e => errorDo e |>.runOn state

instance : MonadExceptOf Error (EnvT m) where
  throw := EnvT.throw
  tryCatch := EnvT.tryCatch

instance : Inhabited (EnvT m α) where
  default := throwInternal "`Inhabited` witness"

instance : Inhabited (Env α) := inferInstanceAs (Inhabited (EnvT BaseIO α))

private def liftRes5T : Except Error5 α → EnvT m α
  | .ok a => ⟨fun _ => return a⟩
  | .error e => ⟨fun _ => Error.ofUnsafe e |> throw⟩

private def lift5 [MonadLiftT BaseIO m] (code : Env5T m α) : EnvT m α where
  runOn state := do liftRes5T (← code.run) |>.runOn state

end EnvT

namespace Env variable [Ω]

def liftBaseIO (code : BaseIO α) : Env α := EnvT.liftBaseIO code

instance : MonadLift BaseIO Env := ⟨liftBaseIO⟩

def liftIO (code : IO α) : Env α := EnvT.liftIO code

instance : MonadLift IO Env := ⟨liftIO⟩

export EnvT (lift5)

instance : Monad Env := EnvT.instMonad

instance : MonadLift (ResT BaseIO) Env := EnvT.instMonadLiftResT
instance : MonadExceptOf Error Env := EnvT.instMonadExceptOfError

instance : MonadLift (EnvT BaseIO) Env := ⟨id⟩

-- private instance : MonadLift Env5 Env := EnvT.instMonadLiftEnvTOfMonadLiftTBaseIO

section sanity
example : MonadLiftT Res Env := inferInstance
-- private example : MonadLiftT (Except Error5) Env := inferInstance
end sanity

end Env



namespace EnvT

def run [Monad m] [MonadLiftT BaseIO m] (code : [Ω] → EnvT m α) : m (Res α) := do
  let _scope := Ω.mk
  match ← Tm.new.run with
  | .ok tm => IO.mkRef {tm} >>= code.runOn
  | .error e => return Error.ofUnsafe e |> .error

end EnvT

namespace Env

def run (code : [Ω] → Env α) : BaseIO (Res α) := EnvT.run code

def runIO (code : [Ω] → Env α) : IO α := do
  match ← run code with
  | .ok a => return a
  | .error e => IO.Error.userError e.toString |> throw

end Env



section variable [Ω]

private def getManager : Env Tm := ⟨fun ref => return (← ref.get).tm⟩

/-! ### The declared-sort registry

`private`, like `runUnsafe`: only the sort layer registers and looks sorts up, and it does so
through `Srt`-level functions that state what they mean.
-/

/-- Remembers a declared sort under a name, failing if the name is taken. -/
private def registerSort (name : String) (srt : cvc5.Sort) : Env Unit :=
  ⟨fun ref => do
    let state ← ref.get
    if state.declaredSorts.contains name then
      throw <| .user s!"a sort named `{name}` has already been declared in this scope"
    ref.set {state with declaredSorts := state.declaredSorts.insert name srt}⟩

/-- The sort declared under a name, if any. -/
private def getRegisteredSort? (name : String) : Env (Option cvc5.Sort) :=
  ⟨fun ref => return (← ref.get).declaredSorts[name]?⟩


-- private def runUnsafe [Monad m'] [MonadLiftT BaseIO m] [Monad m] [MonadLiftT m' (EnvT m)]
--   (code : cvc5.TermManager → m' α)
-- : EnvT m α := do
--   code (← getManager)

-- private def runUnsafe' [Monad m'] [MonadLiftT BaseIO m] [Monad m] [MonadLiftT m' (EnvT m)]
--   (code : m' α)
-- : EnvT m α := runUnsafe fun _ => code


private def runUnsafe [Monad m] [MonadLiftT BaseIO m]
  (code : cvc5.TermManager → cvc5.EnvT m α)
: EnvT m α := do EnvT.lift5 <| code (← getManager)

private def runUnsafe' [Monad m] [MonadLiftT BaseIO m] (code : cvc5.EnvT m α) : EnvT m α :=
  EnvT.lift5 code
