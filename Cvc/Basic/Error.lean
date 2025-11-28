/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import cvc5

import Cvc.Basic.Basic



namespace Cvc



/-- Cvc's error type -/
inductive Error : Type
/-- Internal error. -/
| internal (msg : String)
/-- Unsupported feature. -/
| unsupported (msg : String)
/-- User-input error. -/
| user (msg : String)
/-- Input/output error. -/
| io (msg : String)
deriving Inhabited


namespace Error

/-- Used to allow `String` and `Unit → String` as context messages. -/
class AsString (α : Type) : Type where
  /-- Conversion to strings. -/
  asString : α → String

instance : AsString String := ⟨id⟩
instance : AsString (Unit → String) := ⟨fun f => f ()⟩

/-- Map over an error's internal message -/
def mapMsg (f : String → String) : Error → Error
| .internal msg => f msg |> .internal
| .unsupported msg => f msg |> .unsupported
| .user msg => f msg |> .user
| .io msg => f msg |> .io

/-- Appends some text to an error's internal message. -/
def append (self : Error) (txt : String) (newline := true) : Error :=
  let txt := if newline then "\n"++txt else txt
  self.mapMsg (· ++ txt)

/-- Conversion to `cvc5` errors. -/
def toUnsafe : Error → cvc5.Error
| .internal "a value is missing" => .missingValue
| .internal msg => .error s!"[internal] {msg}"
| .unsupported msg => .unsupported msg
| .user msg => .error msg
| .io msg => .error s!"[io] {msg}"

/-- Constructor from `cvc5` errors. -/
def ofUnsafe : cvc5.Error → Error
| .missingValue => .internal "a value is missing"
| .error msg => .internal s!"{msg}"
| .option msg => .internal s!"option error: {msg}"
| .unsupported msg => .unsupported msg
| .recoverable msg => .internal s!"recoverable: {msg}"

instance : MonadLift (Except cvc5.Error) (Except Error) where
  monadLift
  | .ok res => .ok res
  | .error e => .error (ofUnsafe e)

instance : Coe cvc5.Error Error := ⟨ofUnsafe⟩

/-- String representation. -/
protected def toString : Error → String
| .user msg => msg
| .internal msg => s!"[internal] {msg}"
| .unsupported msg => s!"[unsupported] {msg}"
| .io msg => s!"[io] {msg}"

instance instToString : ToString Error :=
  ⟨Error.toString⟩

section variable [Monad m] [MonadExcept Error m] (msg : String)

/-- Throws an `Error.user`. -/
def throwUser : m α := do
  throw <| Error.user msg

/-- Throws an `Error.internal`. -/
def throwInternal : m α := do
  throw <| Error.internal msg

/-- Throws an `Error.internal`. -/
def throwUnreachable (msg : String := "") : m α := do
  let sep := if msg.isEmpty then "" else ": "
  throw <| Error.internal s!"reached unreachable code{sep}{msg}"

/-- Throws an `Error.io`. -/
def throwIO (e : IO.Error) : m α := do
  throw <| Error.io <| toString e

end

end Error

export Error (throwUser throwInternal throwUnreachable throwIO)



/-- Sets an error context as a lazy string to newline-append after `code`'s error, if any. -/
def errorContext [Monad m] [MonadExcept Error m] (s : Unit → String) (code : m α) : m α :=
  try code catch e => e.mapMsg (s!"{·}\n{s ()}") |> throw



/-- `Error`-result monad transformer. -/
abbrev ResT (m : Type → Type) (α : Type) : Type := ExceptT Error m α

/-- `Error` monad. -/
abbrev Res (α : Type) : Type := ResT Id α

namespace ResT

-- sanity
example [Monad m] : Monad (ResT m) := inferInstance
example [Monad m] : MonadExcept Error (ResT m) := inferInstance
example [Monad m] : MonadLift m (ResT m) := inferInstance

end ResT

namespace Res

@[inherit_doc Except.ok]
abbrev ok (a : α) : Res α := return a

@[inherit_doc Except.error]
abbrev error (e : Error) : Res α := throw e

-- sanity
example : Monad Res := inferInstance
example : MonadExcept Error Res := inferInstance

instance [Monad m] : MonadLift Res (ResT m) :=
  ⟨fun | .ok a => return a | .error e => throw e⟩

end Res
