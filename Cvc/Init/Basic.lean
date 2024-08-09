/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import cvc5



/-! # Library setup: re-exports and helpers -/
namespace Cvc



export Lean (Rat)



/-! ## Re-exports from `cvc5` -/

inductive Error : Type u
| internal (msg : String)
| userError (msg : String)

namespace Error

def toCvc5 : Error → cvc5.Error
| .internal "a value is missing" => .missingValue
| .internal msg => .userError msg
| .userError msg => .userError msg

def ofCvc5 : cvc5.Error → Error
| .missingValue => .internal "a value is missing"
| .cvc5Error msg => .internal msg
| .userError msg => .userError msg

instance : Coe cvc5.Error Error := ⟨ofCvc5⟩

protected def toString : Error → String
| .internal msg => "internal error: " ++ msg
| .userError msg => "user error: " ++ msg

instance instToString : ToString Error :=
  ⟨Error.toString⟩

end Error



/-! ## Helpers -/
