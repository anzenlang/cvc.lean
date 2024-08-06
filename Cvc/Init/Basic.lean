/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import cvc5



/-! # Library setup: re-exports and helpers -/
namespace Cvc



/-! ## Re-exports from `cvc5` -/

inductive Error
| internal (msg : String)
| userError (msg : String)

namespace Error

def toCvc5 : Error → cvc5.Error
| .internal "a value is missing" => .missingValue
| .internal msg => .user_error msg
| .userError msg => .user_error msg

def ofCvc5 : cvc5.Error → Error
| .missingValue => .internal "a value is missing"
| .user_error msg => .userError msg

instance : Coe cvc5.Error Error := ⟨ofCvc5⟩

protected def toString : Error → String
| .internal msg => "internal error: " ++ msg
| .userError msg => "user error: " ++ msg

instance instToString : ToString Error :=
  ⟨Error.toString⟩

end Error



/-! ## Helpers -/

namespace Test

variable [Repr α] [BEq α]

/-- Crashes with an explanation if `expected ≠ value`. -/
def check! (expected value : α) : IO Unit :=
  if expected != value then do
    println! "expected `{repr expected}`, got `{repr value}`"
    panic! "check failed"
  else return ()

/-- Crashes with an explanation if `expected ≠ value`. -/
def checkNe! (lhs rhs : α) : IO Unit :=
  if lhs == rhs then do
    println! "`{repr lhs}` should be different from `{repr rhs}`, but is not"
    panic! "check failed"
  else return ()

end Test
