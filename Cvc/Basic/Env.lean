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
-- Not used here: imported publicly at the root of the library, so that every user can manipulate
-- tree maps and sets, as the library does, without importing them. Lean itself is visible to them
-- only at the meta phase, through the library's macros, where `Std.TreeMap` would resolve and then
-- refuse to be used in ordinary code.
public import Std.Data.TreeMap
public import Std.Data.TreeSet



/-! # Scopes and the environment monad

cvc5 creates sorts, terms and solvers through a *term manager*, and objects of two managers must
never meet. This library hides term managers behind the class `Ω`: an instance stands for "the term
manager of the current scope", and nearly every type and function takes one implicitly.

Work happens in the `Env` monad (`EnvT` for another base monad), and `Env.run`/`Env.runIO` run it
in a fresh scope. As with `runST`, nothing mentioning the scope can escape the run, and two scopes'
sorts and terms cannot be mixed, nested runs included.
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


/-- The current scope: an instance stands for one term manager.

Only `Env.run` and its variants make one, so a sort, term or solver cannot leave the run it was
made in, nor meet one made in another run, nested runs included.
-/
@[nospecialize]
class Ω : Type 1 where private mk :: private scope : Type
-- A `Type`, deliberately not a `Prop`. Any two proofs of a `Prop` are definitionally equal, so a
-- `Prop`-valued `Ω` made a sort of one scope the same type as a sort of any other, and nested
-- `Env.run`s could mix, or leak into each other, their sorts and terms.
--
-- Its one field is a *type*, and that is load-bearing twice over. A structure with no field, or a
-- field of type `Unit`, would be distinct in name only: structure eta makes all its values equal,
-- as proof irrelevance did. And a field holding a type is erased by the compiler, so an instance is
-- represented as a constant scalar — no allocation, no reference counting — and is dropped entirely
-- from the body of every function that does not use it.
--
-- `@[nospecialize]` because, as data, an instance would otherwise be a specialization candidate
-- like any other: the compiler would copy bodies from this module — private helpers included,
-- which other modules may not reference — into its callers, to specialize them on an argument
-- every scope gives the same constant value.

/-- What an `Env` threads: the scope's term manager and the sorts declared in it. -/
structure State where
  private mk ::
  /-- The term manager every sort and term of this scope belongs to. -/
  private tm : Tm
  /-- Sorts that were declared, by name. -/
  private declaredSorts : Std.HashMap String cvc5.Sort := {}
-- Declared sorts are kept because cvc5 makes a *fresh* sort every time one is declared, even from
-- an identical declaration, so a datatype sort cannot be recovered by rebuilding it. This is what
-- lets `ToTyp` name a datatype: the `Typ` carries the name, and `Typ.toSrt` looks the sort up.
-- Keyed by name, so the declaration functions reject a name already taken.

/-- The environment monad transformer. -/
structure EnvT [Ω] (m : Type → Type) (α : Type) : Type where private mk ::
  private runOn : StateRefT' IO.RealWorld State (ResT m) α

/-- The environment monad. -/
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

/-- Runs `code` in a fresh scope, with a term manager of its own, answering its result or error.

`α` is chosen outside the scope, so nothing mentioning the scope can escape the run.
-/
def run [Monad m] [MonadLiftT BaseIO m] (code : [Ω] → EnvT m α) : m (Res α) := do
  let _scope : Ω := ⟨Unit⟩
  match ← Tm.new.run with
  | .ok tm => IO.mkRef {tm} >>= code.runOn
  | .error e => return Error.ofUnsafe e |> .error

end EnvT

namespace Env

@[inherit_doc EnvT.run]
def run (code : [Ω] → Env α) : BaseIO (Res α) := EnvT.run code

/-- `Env.run`, raising an error as an `IO` exception. -/
def runIO (code : [Ω] → Env α) : IO α := do
  match ← run code with
  | .ok a => return a
  | .error e => IO.Error.userError e.toString |> throw

end Env



section variable [Ω]

private def getManager : Env Tm := ⟨fun ref => return (← ref.get).tm⟩

-- The declared-sort registry. `private`, like `runUnsafe`: only the sort layer registers and
-- looks sorts up, and it does so through `Srt`-level functions that state what they mean.

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
