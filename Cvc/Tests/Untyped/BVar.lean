/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.BVar
import Cvc.Untyped.Theory
import Cvc.Untyped.Solver

public meta import Cvc.Untyped.BVar
public meta import Cvc.Untyped.Theory
public meta import Cvc.Untyped.Solver



/-! # Bound variables, sort-erased

A bound variable is only meaningful under a binder — the parameters of a definition, or of a
quantifier, lambda or witness. It is therefore a type of its own rather than a `Term`, so that a
signature can require one where a free constant would be wrong.
-/
namespace Cvc.Tests.Untyped.BVar

open Cvc
open Cvc.Untyped



/-! ## Construction

`Term.mkBVar` is the constructor; `BVar.mk` is the same function reached from the type.
-/

/-- info:
mkBVar : v
BVar.mk: w
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.of Int
  println! "mkBVar : {(← Term.mkBVar int "v").toTerm}"
  println! "BVar.mk: {(← Cvc.Untyped.BVar.mk int "w").toTerm}"

-- each call is a fresh variable, even at the same name and sort, so two of them are distinguishable
/-- info: distinct : true -/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.of Int
  let x ← Term.mkBVar int "x"
  let x' ← Term.mkBVar int "x"
  println! "distinct : {!(x.toTerm.beq x'.toTerm)}"



/-! ## Use under a binder

The only thing a bound variable is for: standing in for a parameter in a definition's body.
-/

/-- info:
define-fun : dbl
applied    : 42
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let int ← Srt.int

  let x ← Term.mkBVar int "x"
  let two ← Term.mkInt 2
  let dbl ← s.defineFun "dbl" #[x] int (← Term.mul x two)
  println! "define-fun : {dbl}"

  -- the definition is a function symbol like any other, so it applies
  let n ← s.declareConst "n" int
  (do Term.equal n (← Term.mkInt 21)) >>= s.assert
  let applied ← Term.apply dbl n
  let value ← s.checkSat (ifSat := do s.getValue applied)
  println! "applied    : {value}"



/-! ## The type is distinct from `Term`

`BVar` is a `def`, so a plain `import` keeps it opaque: a bound variable does not silently pass
where a term is expected. `toTerm` is the way across, and it is `id`, so crossing costs nothing.
-/

section discipline
variable [Ω] (bv : BVar) (t : Term)

/-- A bound variable converts to a term explicitly… -/
example : Term := bv.toTerm

/-- …or through the coercion, which is the same function. -/
example : Term := bv

example : bv.toTerm = bv := rfl

/-- info: @Term.mkBVar : [inst : Ω] → Srt → String → Env BVar -/
#guard_msgs in #check @Cvc.Untyped.Term.mkBVar

end discipline
