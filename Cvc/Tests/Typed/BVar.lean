/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.BVar
import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Solver

public meta import Cvc.Typed.BVar
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Solver



/-! # Bound variables, typed

A bound variable is only meaningful under a binder — the parameters of a definition, or of a
quantifier, lambda or witness. It is therefore a type of its own rather than a `Term`, so that a
signature can require one where a free constant would be wrong.

The index carries the sort, so `mkBVar` takes no `Srt`: it computes one from `α`.
-/
namespace Cvc.Tests.Typed.BVar

open Cvc
open Cvc
open Cvc.Typed



/-! ## Construction

`Term.mkBVar'` takes the type explicitly, `Term.mkBVar` infers it from the expected index, and
`BVar.mk` is the same function reached from the type.
-/

/-- info:
mkBVar' : v
mkBVar  : w
BVar.mk : z
-/
#guard_msgs in #eval Env.runIO do
  println! "mkBVar' : {(← Term.mkBVar' Int "v").toTerm}"
  println! "mkBVar  : {(← (Term.mkBVar "w" : Env (Typed.BVar Int))).toTerm}"
  println! "BVar.mk : {(← (Typed.BVar.mk "z" : Env (Typed.BVar Rat))).toTerm}"

-- each call is a fresh variable, even at the same name and index
/-- info: distinct : true -/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkBVar' Int "x"
  let x' ← Term.mkBVar' Int "x"
  println! "distinct : {!(x.toTerm.beq x'.toTerm)}"

-- the index decides the sort, and nothing else does: a variable at a `Rat` index is usable where a
-- `Rat` term is expected, and only there
/-- info: sum : (+ x y) -/
#guard_msgs in #eval Env.runIO do
  let x ← Term.mkBVar' Rat "x"
  let y ← Term.mkBVar' Rat "y"
  println! "sum : {(← Term.add x.toTerm y.toTerm).erase}"



/-! ## `declareFun`

The index decides the split between domain and codomain: an arrow index declares a function
symbol, anything else declares a constant.
-/

-- applying the symbol is the evidence the split was right: a wrong domain is a runtime error from
-- cvc5, and a wrong codomain would not typecheck against the index
/-- info:
unary    : (f 2)
2-ary    : (g 2 true)
constant : x
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let two ← Term.mkInt 2

  let f ← s.declareFun (α := Int → Int) "f"
  println! "unary    : {(← Term.apply f two).erase}"

  let g ← s.declareFun (α := Int → Bool → Int) "g"
  println! "2-ary    : {(← Term.apply2 g two (← Term.mkTrue)).erase}"

  -- a non-function index has an empty domain, so this is `declareConst`
  let x ← s.declareFun (α := Int) "x"
  println! "constant : {x.erase}"

-- and it solves: an uninterpreted function constrained at a point reads back at that point
/-- info: f 2 = 7 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let f ← s.declareFun (α := Int → Int) "f"
  let two ← Term.mkInt 2
  let fTwo ← Term.apply f two
  (do Term.equal fTwo (← Term.mkInt 7)) >>= s.assert

  let value ← s.checkSat (ifSat := do s.getValue (α := Int) fTwo)
  println! "f 2 = {value}"



/-! ## `defineFun`

The parameters are bound variables, collected right to left by `BVars.push`, so the array handed
to the solver comes out in declaration order.

`BVars.signatureTo` folds them into the definition's index, which is the same arrow a function
symbol carries, so a definition applies exactly like a declared symbol does.
-/

/-- info:
define-fun : dbl
dbl 21     : 42
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← Term.mkBVar' Int "x"
  let dbl ← s.defineFun "dbl" (BVars.push x []) (← Term.mul x.toTerm (← Term.mkInt 2))
  println! "define-fun : {dbl.erase}"

  let applied ← Term.apply dbl (← Term.mkInt 21)
  println! "dbl 21     : {← s.checkSat (ifSat := do s.getValue (α := Int) applied)}"

-- two parameters. The erased array is in declaration order even though `push` prepends, so a
-- non-commutative body is the test: `sub 10 4` distinguishes the right order from the reversed one
/-- info:
define-fun : sub
sub 10 4   : 6
sub 4 10   : -6
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← Term.mkBVar' Int "x"
  let y ← Term.mkBVar' Int "y"
  let sub ← s.defineFun "sub" (BVars.push y (BVars.push x [])) (← Term.sub x.toTerm y.toTerm)
  println! "define-fun : {sub.erase}"

  let ten ← Term.mkInt 10
  let four ← Term.mkInt 4
  let fst ← Term.apply2 sub ten four
  let snd ← Term.apply2 sub four ten
  s.checkSat (ifSat := do
    println! "sub 10 4   : {← s.getValue (α := Int) fst}"
    println! "sub 4 10   : {← s.getValue (α := Int) snd}")

-- three parameters, at mixed sorts: the index threads them in order, and the body only typechecks
-- because each bound variable carries its own
/-- info:
define-fun : pick
pick true 7 2  : 9
pick false 7 2 : 5
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let b ← Term.mkBVar' Bool "b"
  let x ← Term.mkBVar' Int "x"
  let y ← Term.mkBVar' Int "y"
  let bvs := BVars.push y (BVars.push x (BVars.push b []))
  let body ← Term.ite b.toTerm (← Term.add x.toTerm y.toTerm) (← Term.sub x.toTerm y.toTerm)
  let pick ← s.defineFun "pick" bvs body
  println! "define-fun : {pick.erase}"

  let seven ← Term.mkInt 7
  let two ← Term.mkInt 2
  let onTrue ← Term.apply3 pick (← Term.mkTrue) seven two
  let onFalse ← Term.apply3 pick (← Term.mkFalse) seven two
  s.checkSat (ifSat := do
    println! "pick true 7 2  : {← s.getValue (α := Int) onTrue}"
    println! "pick false 7 2 : {← s.getValue (α := Int) onFalse}")

-- a definition is a definition, not an assumption: the solver knows `dbl n = 2 * n` for every `n`,
-- so contradicting it at an unconstrained argument is unsat
/-- info: dbl n ≠ 2 * n → unsat -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new

  let x ← Term.mkBVar' Int "x"
  let dbl ← s.defineFun "dbl" (BVars.push x []) (← Term.mul x.toTerm (← Term.mkInt 2))

  let n ← s.declareConst Int "n"
  let lft ← Term.apply dbl n
  let rgt ← Term.mul n (← Term.mkInt 2)
  (do Term.distinct lft rgt) >>= s.assert

  println! "dbl n ≠ 2 * n → {← s.checkSat (ifUnsat := do return "unsat")}"

-- no parameters at all: the index is the body's own, so this is a plain definition
/-- info:
define-fun : c
c          : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let c ← s.defineFun "c" [] (← Term.mkInt 7)
  println! "define-fun : {c.erase}"
  println! "c          : {← s.checkSat (ifSat := do s.getValue (α := Int) c)}"



/-! ## Signatures -/

section signatures
variable [Ω]

/-- info: @Term.mkBVar' : [inst : Ω] → (α : Type) → [ToTyp α] → String → Env (BVar α) -/
#guard_msgs in #check @Cvc.Typed.Term.mkBVar'

/-- info: @Solver.declareFun : [inst : Ω] → Solver → {α : Type} → [ToTyp α] → String → Env (Term α) -/
#guard_msgs in #check @Cvc.Typed.Solver.declareFun

/-- info: @Solver.defineFun : [inst : Ω] →
  Solver → {β : Type} → [ToTyp β] → String → (bvs : BVars) → Term β → Env (Term (BVars.signatureTo β bvs)) -/
#guard_msgs in #check @Cvc.Typed.Solver.defineFun

-- `signatureTo` folds the bound variables into the definition's index, and reduces definitionally
example (s : Solver) (x : BVar Int) (body : Term Bool)
: Env (Term (Int → Bool)) := s.defineFun "p" (BVars.push x []) body

example (s : Solver) (x : BVar Int) (y : BVar Bool) (body : Term Rat)
: Env (Term (Int → Bool → Rat)) := s.defineFun "f" (BVars.push y (BVars.push x [])) body

end signatures



/-! ## The type is distinct from `Term`

`BVar` is a `def`, so a plain `import` keeps it opaque: a bound variable does not silently pass
where a term is expected. `toTerm` is the way across, and it is `id`, so crossing costs nothing.
-/

section discipline
variable [Ω] (bv : Typed.BVar Int)

/-- A bound variable converts to a term explicitly… -/
example : Term Int := bv.toTerm

/-- …or through the coercion, which is the same function. -/
example : Term Int := bv

example : bv.toTerm = bv := rfl

end discipline
