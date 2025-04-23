/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Lean.Server.Utils

import Cvc

namespace Cvc.Test

def IO.run : IO Unit → IO Unit :=
  id

def fail {α : outParam Type} (msg : String) : IO α :=
  IO.throwServerError msg

protected def pref (hint : String) : String :=
  if hint.isEmpty then "" else "[" ++ hint ++ "] "

def assertEq [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft != rgt then
    IO.eprintln s!"{Test.pref hint}comparison failed: `{lft}` is different from `{rgt}`"
    fail "assertion failed"

def assertNe [ToString α] [BEq α] (lft rgt : α) (hint := "") : IO Unit := do
  if lft == rgt then
    IO.eprintln s!"{Test.pref hint}comparison failed: `{lft}` is the same as `{rgt}`"
    fail "assertion failed"
