/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core.Solver
import Cvc.Untyped.Theory.Arith
import Cvc.Untyped.Theory.Fun

meta import Cvc.Untyped.Core.Solver
meta import Cvc.Untyped.Theory.Arith
meta import Cvc.Untyped.Theory.Fun



/-! # The solver, sort-erased

Only the functions shared by both layers are covered here: the ones mentioning a term belong to
whichever layer states their sorts.
-/
namespace Cvc.Tests.Untyped.Solver

open Cvc
open Cvc.Untyped

/-! ## Options and information -/

/-- info:
option set  : true
option unset: false
info set    : ok
names       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new

  s.setOption "produce-models" "true"
  println! "option set  : {← s.getOption "produce-models"}"
  s.setOption "produce-models" "false"
  println! "option unset: {← s.getOption "produce-models"}"

  s.setInfo "status" "sat"
  println! "info set    : ok"

  let names ← s.getOptionNames
  println! "names       : {!names.isEmpty}"



/-! ## The logic -/

/-- info:
before : false
after  : true
name   : QF_LIA
parsed : QF_LIA
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  println! "before : {← s.isLogicSet}"
  s.setLogic Cvc.Logic.qf_lia
  println! "after  : {← s.isLogicSet}"
  println! "name   : {← s.getLogicString}"
  println! "parsed : {(← s.getLogic).toSmtLib}"



/-! ## Assertion scopes and sorts -/

/-- info:
pushed  : ok
popped  : ok
reset   : ok
sort    : U
sort 2  : Pair
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new

  s.push
  println! "pushed  : ok"
  s.pop
  println! "popped  : ok"
  s.reset
  println! "reset   : ok"

  println! "sort    : {← s.declareSrt "U" 0}"
  println! "sort 2  : {← s.declareSrt "Pair" 2}"



/-! ## Version -/

/-- info: version : true -/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  let version ← s.getVersion
  println! "version : {!version.isEmpty}"

/-! ## Asserting and checking

From here the signatures mention terms, so the two layers differ: this one takes and returns
sort-erased terms.
-/

/-- info:
assertions : 2
sat        : x = 1, y = 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  let three ← Term.mkInt 3

  Term.equal (← Term.add x y) three >>= s.assert
  Term.lt x y >>= s.assert
  println! "assertions : {(← s.getAssertions).size}"

  s.checkSat (ifSat := do
    println! "sat        : x = {← s.getValue x}, y = {← s.getValue y}")

/-- info: unsat core : 2 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-cores" "true"

  let bool ← Srt.bool
  let b ← s.declareConst "b" bool
  s.assert b
  Term.not b >>= s.assert

  let core ← s.checkSat (ifUnsat := do return (← s.getUnsatCore).size)
  println! "unsat core : {core}"

/-- info: unexpected : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let bool ← Srt.bool
  let b ← s.declareConst "b" bool
  s.assert b
  -- only an unsat branch is given, and the solver answers sat
  let outcome ←
    try
      let _ ← s.checkSat (ifUnsat := do return "unsat")
      pure "no error"
    catch _ => pure "caught"
  println! "unexpected : {outcome}"



/-! ## Recursive definitions

A recursive definition is an assertion, a universally quantified equation between the function's
application and its body, so solving over one is solving over a quantified formula. Three things
follow, each pinned below:

- an `unsat` answer is found by unfolding the definition, with no option needed;
- a `sat` answer needs a model of the function, which cvc5 only attempts under `fmf-fun`, and
  answers `unknown` without it;
- under `fmf-fun` the definition is only enforced on the applications the assertions mention, so a
  value is read off an asserted equation, never off an application nothing constrains — `getValue`
  of one answers whatever the finite model happened to pick.

`defineFunRec` names the function by a string and returns it, so its body cannot mention it: it is
for a definition that only *may* be recursive. A self-reference goes through `defineFunRecTerm`,
over a function declared first, and mutual recursion through `defineFunsRec`, which defines every
function at once.
-/

/-- Declares `even` and `odd` and defines them mutually recursively over the integers. -/
def evenOdd [Ω] (s : Solver) : Env (Term × Term) := do
  let int ← Srt.of Int
  let bool ← Srt.of Bool
  let even ← s.declareFun "even" #[int] bool
  let odd ← s.declareFun "odd" #[int] bool
  let n ← Term.mkBVar int "n"
  let m ← Term.mkBVar int "m"
  s.defineFunsRec #[even, odd] #[#[n], #[m]]
    #[← smt! if n ≤ 0 then n = 0 else odd (n - 1), ← smt! if m ≤ 0 then false else even (m - 1)]
  return (even, odd)

/-- Declares `fact` and defines it as the factorial, through its own application. -/
def fact [Ω] (s : Solver) (global : Bool := false) : Env Term := do
  let int ← Srt.of Int
  let fact ← s.declareFun "fact" #[int] int
  let n ← Term.mkBVar int "n"
  s.defineFunRecTerm fact #[n] (← smt! if n ≤ 0 then 1 else n * fact (n - 1)) global

/-- A solver that can answer `sat` over recursive definitions, and give a model. -/
def fmfSolver [Ω] : Env Solver := do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  s.setOption "fmf-fun" "true"
  return s

-- each definition is asserted, as a quantified equation, in the order given
/-- info:
assertions :
  (forall ((n Int)) (= (even n) (ite (<= n 0) (= n 0) (odd (- n 1)))))
  (forall ((m Int)) (= (odd m) (ite (<= m 0) false (even (- m 1)))))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let _ ← evenOdd s
  println! "assertions :"
  for a in ← s.getAssertions do println! "  {a}"

/-- info:
even 10 ∧ odd 7     : sat
even 7              : unsat
odd x, 3 < x < 6    : x = 5
-/
#guard_msgs in #eval Env.runIO do
  let s ← fmfSolver
  let (even, odd) ← evenOdd s
  let check (f : Term) : Env String := do
    s.push
    s.assert f
    let res ← s.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
    s.pop
    return res
  println! "even 10 ∧ odd 7     : {← check (← smt! even 10 ∧ odd 7)}"
  println! "even 7              : {← check (← smt! even 7)}"
  let x ← s.declareConst "x" (← Srt.of Int)
  s.assert (← smt! odd x ∧ 3 < x ∧ x < 6)
  println! "odd x, 3 < x < 6    : x = {← s.checkSat (ifSat := s.getValue x)}"

/-- info:
fact 5 : 120
dbl 21 : 42
-/
#guard_msgs in #eval Env.runIO do
  let s ← fmfSolver
  let int ← Srt.of Int
  let r ← s.declareConst "r" int
  s.assert (← smt! r = ![fact s] 5)
  -- defined by name, so the body cannot mention it: a definition that only *may* recurse
  let n ← Term.mkBVar int "n"
  let dbl ← s.defineFunRec "dbl" #[n] int (← smt! n + n)
  let d ← s.declareConst "d" int
  s.assert (← smt! d = dbl 21)
  let (r, d) ← s.checkSat (ifSat := return (← s.getValue r, ← s.getValue d))
  println! "fact 5 : {r}"
  println! "dbl 21 : {d}"

-- without `fmf-fun`, an unsat answer is still found by unfolding, but a sat one is not attempted
/-- info:
even 7              : unsat
even 10             : unknown (Cvc.Unknown.Explanation.incomplete)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let (even, _) ← evenOdd s
  let check (f : Term) : Env String := do
    s.push
    s.assert f
    let res ← s.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
      (ifUnknown := fun e => return s!"unknown ({e})")
    s.pop
    return res
  println! "even 7              : {← check (← smt! even 7)}"
  println! "even 10             : {← check (← smt! even 10)}"

-- a global definition survives the scope it was made in, a local one does not
/-- info:
local, after pop  : 0 assertions
global, after pop : 1 assertions
global fact 5     : 120
-/
#guard_msgs in #eval Env.runIO do
  let s ← fmfSolver
  s.push
  let _ ← fact s
  s.pop
  println! "local, after pop  : {(← s.getAssertions).size} assertions"
  s.push
  let f ← fact s (global := true)
  s.pop
  println! "global, after pop : {(← s.getAssertions).size} assertions"
  let r ← s.declareConst "r" (← Srt.of Int)
  s.assert (← smt! r = f 5)
  println! "global fact 5     : {← s.checkSat (ifSat := s.getValue r)}"

-- one body per function and one variable list per body, both checked statically
section defineFunsRecArity
variable [Ω] (s : Solver) (f g : Term) (n : BVar)

/--
error: could not synthesize default value for parameter '_oneBodyPerFun' using tactics
---
error: failed to prove there are as many bodies as functions
inst✝ : Ω
s : Solver
f g : Term
n : BVar
⊢ #[f, g].size = #[n.toTerm].size
-/
#guard_msgs in
example : Env Unit := s.defineFunsRec #[f, g] #[#[n]] #[n.toTerm]

/--
error: could not synthesize default value for parameter '_oneBvsPerBody' using tactics
---
error: failed to prove there are as many bound-variable lists as bodies
inst✝ : Ω
s : Solver
f g : Term
n : BVar
⊢ #[#[n], #[n]].size = #[n.toTerm].size
-/
#guard_msgs in
example : Env Unit := s.defineFunsRec #[f] #[#[n], #[n]] #[n.toTerm]

end defineFunsRecArity



/-! ## Interpolants

An interpolant of assertions `A` and a conjecture `C` is a formula `I` over the symbols both
mention, such that `A → I` and `I → C`. The first test checks both implications with a second
solver rather than trusting the answer's shape, so it pins what an interpolant *is* and not only
how cvc5 prints this one.

cvc5 answers the null term when there is no interpolant, and when an enumeration runs out; that is
`none` here.
-/

/-- Whether `hyps` entail `concl`, by refuting `hyps ∧ ¬concl` on a fresh solver. -/
def entails [Ω] (hyps : Array Term) (concl : Term) : Env Bool := do
  let s ← Solver.new
  for h in hyps do s.assert h
  Term.not concl >>= s.assert
  return !(← s.checkIsSat)

/-- info:
interpolant : (and (= a (+ 1 (+ 1 c))) true)
A → I       : true
I → C       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let int ← Srt.int
  let a ← s.declareConst "a" int
  let b ← s.declareConst "b" int
  let c ← s.declareConst "c" int
  let one ← Term.mkInt 1
  -- `b` is not shared with the conjecture, so the interpolant has to eliminate it
  let hyps := #[← Term.equal a (← Term.add b one), ← Term.equal b (← Term.add c one)]
  for h in hyps do s.assert h
  let conj ← Term.gt a c

  let some i ← s.getInterpolant conj
    | println! "no interpolant"
  println! "interpolant : {i}"
  println! "A → I       : {← entails hyps i}"
  println! "I → C       : {← entails #[i] conj}"

/-- info: not entailed : none -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let int ← Srt.int
  let a ← s.declareConst "a" int
  let c ← s.declareConst "c" int
  Term.gt a c >>= s.assert
  -- the assertions do not entail the conjecture, so nothing can sit between them
  println! "not entailed : {← s.getInterpolant (← Term.lt a c)}"

/-- info:
first  : (<= 1 y)
next   : (not (<= y 1))
next   : (or (= y 1) (<= 1 y))
all distinct : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  s.setOption "incremental" "true"

  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  let z ← s.declareConst "z" int
  let zero ← Term.mkInt 0
  Term.gt (← Term.add x y) zero >>= s.assert
  Term.lt x zero >>= s.assert
  let conj ← Term.or (← Term.gt (← Term.add y z) zero) (← Term.lt z zero)

  let some first ← s.getInterpolant conj
    | println! "no interpolant"
  println! "first  : {first}"
  let mut seen := #[first]
  for _ in [0:2] do
    let some next ← s.getNextInterpolant
      | println! "exhausted"
    println! "next   : {next}"
    seen := seen.push next
  println! "all distinct : {seen.all fun t => (seen.filter (· == t)).size == 1}"

/-- info: next, not incremental : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  s.setOption "incremental" "false"

  let int ← Srt.int
  let a ← s.declareConst "a" int
  let c ← s.declareConst "c" int
  Term.gt a c >>= s.assert
  let _ ← s.getInterpolant (← Term.ge a c)
  let outcome ←
    try
      let _ ← s.getNextInterpolant
      pure "no error"
    catch _ => pure "caught"
  println! "next, not incremental : {outcome}"

/-- info: without the option : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let int ← Srt.int
  let a ← s.declareConst "a" int
  let outcome ←
    try
      let _ ← s.getInterpolant (← Term.equal a a)
      pure "no error"
    catch _ => pure "caught"
  println! "without the option : {outcome}"
