/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import cvc5



/-! # Basic helpers -/
namespace Cvc

export cvc5 (Kind SortKind)



/-- The constant combinator. -/
abbrev 𝕂 (val : α) (_ : β) : α := val



/-- Lazy string interpolation: `fun () => s!<interp>`. -/
macro:max "ls!" str:interpolatedStr(term) : term
  => `( (fun () => s!$str : Unit → String)  )



/-- A check-sat result.-/
inductive CheckSat
/-- Formulas asserted are satisfiable, *i.e.* a model exists. -/
| sat
/-- Formulas are unsatisfiable, no assignment of the symbols makes them true. -/
| unsat
/-- Solver returned unknown. -/
| unknown (desc : String)
/-- Solver returned some unexpected, non-error result. -/
| other (desc : String)

namespace CheckSat

/-- Conversion to a simple *is sat?* flag, `none` on unknown/unexpected results. -/
def isSat? : CheckSat → Option Bool
| sat => true
| unsat => false
| unknown _ | other _ => none

/-- True iff the result is sat. -/
def isSat (res : CheckSat) : Bool := res.isSat?.getD false

/-- Conversion to a simple *is unsat?* flag, `none` on unknown/unexpected results. -/
def isUnsat? (cs : CheckSat) : Option Bool :=
  Bool.not <$> cs.isSat?

/-- True iff the result is sat. -/
def isUnsat (res : CheckSat) : Bool := res.isUnsat?.getD false

/-- Conversion from a `cvc5` result. -/
def ofUnsafe (result : cvc5.Result) : CheckSat :=
  if result.isSat then .sat
  else if result.isUnsat then .unsat
  else if let some unkTxt := result.getUnknownExplanation? then .unknown unkTxt.toString
  else .other s!"could not extract any information from cvc5 result"

/-- String representation. -/
protected def toString : CheckSat → String
| sat => "sat"
| unsat => "unsat"
| unknown msg => s!"unknown[{msg}]"
| other msg => s!"?[{msg}]?"

instance : ToString CheckSat := ⟨CheckSat.toString⟩

end CheckSat
