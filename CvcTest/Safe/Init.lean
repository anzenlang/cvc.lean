/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe
import CvcTest.Init

namespace Cvc.Safe.Test

export Cvc.Test (fail assertEq assertNe)

def assertOk
  (code : SmtIO α)
  (hint : String := "")
: SmtIO α := fun solver => do
  match ← code solver with
  | (.ok res, solver) => return (.ok res, solver)
  | (.error e, _) =>
    IO.eprintln s!"{Test.pref hint}expected `.ok` result, got `{e}`"
    fail "assertion failed"

def assertOkDiscard
  (result : SmtIO α)
  (hint : String := "")
: SmtIO Unit := do
  let _ ← assertOk result hint
  return ()

def assertError
  (expected : String)
  (errorDo : Error → SmtIO Unit)
  (result : SmtIO α)
  (hint : String := "")
: SmtIO Unit := fun solver => do
  match ← result solver with
  | (.ok _, _) =>
    IO.eprintln s!"{Test.pref hint}expected {expected}, got `.ok` result"
    fail "assertion failed"
  | (.error e, solver) => errorDo e solver

def assertInternalError
  (expected : String)
  (result : SmtIO α)
  (hint : String := "")
: SmtIO Unit :=
  assertError s!"cvc5 error `{expected}`"
    (fun
    | .internal err => do
      if err = expected then
        return ()
      else
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got cvc5 error `{err}`"
        fail "assertion failed"
    | .userError err => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got user error `{err}`"
        fail "assertion failed"
    | .unsupported err => do
        IO.eprintln s!"{Test.pref hint}expected cvc5 error `{expected}`, got unsupported `{err}`"
        fail "assertion failed"
    )
    result hint



scoped syntax docComment ? ("#test " <|> "#test? ") term : command

macro_rules
| `(command| $outputComment:docComment #test $code:term) => `(
  $outputComment:docComment
  #guard_msgs in #eval Cvc.Test.IO.run do
    Smt.run! (handleError := fun e => IO.throwServerError e.toString) do
      $code:term
)
| `(command| #test $code:term) => `(
  /-- info: -/
  #test $code
)
| `(command| $[$outputComment]? #test? $code:term) => `(
  #eval Cvc.Test.IO.run do
    Smt.run! (handleError := fun e => IO.throwServerError e.toString) do
      $code:term
)
end Test
