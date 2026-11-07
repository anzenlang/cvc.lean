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
import Cvc.Untyped.Theory.Quant

meta import Cvc.Untyped.Core.Solver
meta import Cvc.Untyped.Theory.Arith
meta import Cvc.Untyped.Theory.Fun
meta import Cvc.Untyped.Theory.Quant



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

/-! `getInfo` answers SMT-LIB's `get-info` flags, rendered as cvc5 prints them. -/

/-- info:
name           : "cvc5"
levels         : 0
levels, 2 push : 2
levels, 1 pop  : 1
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Untyped.Solver.new
  println! "name           : {← s.getInfo "name"}"
  println! "levels         : {← s.getInfo "assertion-stack-levels"}"
  s.push 2
  println! "levels, 2 push : {← s.getInfo "assertion-stack-levels"}"
  s.pop
  println! "levels, 1 pop  : {← s.getInfo "assertion-stack-levels"}"



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

/-! `checkIsSat?` is the three-way answer: `.inl true` sat, `.inl false` unsat, `.inr` unknown. -/

/-- info:
x < 0         : inl true
x < 0 ∧ 0 < x : inl false
∀ n, n < f n  : inr Cvc.Unknown.Explanation.incomplete
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let f ← s.declareFun "f" #[int] int
  let render : Solver.Result.Sat? → String
    | .inl b => s!"inl {b}"
    | .inr e => s!"inr {e}"
  println! "x < 0         : {render (← s.checkIsSat? (assuming := #[← smt! x < 0]))}"
  println! "x < 0 ∧ 0 < x : {render (← s.checkIsSat? (assuming := #[← smt! x < 0 ∧ 0 < x]))}"
  -- satisfiable (`f n = n + 1`), but cvc5 does not find a model of a quantified formula here
  s.assert (← smt! ∀ (n : Int), n < f n)
  println! "∀ n, n < f n  : {render (← s.checkIsSat?)}"

/-! `getUnsatAssumptions` answers the assumptions an unsat answer rests on, and only those: neither
the assertions nor an assumption the refutation does not use. -/

/-- info: unsat assumptions : #[(< x 0)] -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-assumptions" "true"
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  s.assert (← smt! 0 < x)
  let assumptions := #[← smt! 0 < y, ← smt! x < 0, ← smt! y < 5]
  let core ← s.checkSat (assuming := assumptions) (ifUnsat := s.getUnsatAssumptions)
  println! "unsat assumptions : {core}"

/-! `defineConst` names a term: the constant is asserted equal to its body. -/

/-- info:
constant   : c
assertions : #[(= c (+ 2 3)), (= x (* c 2))]
x          : 10
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let int ← Srt.int
  let c ← s.defineConst "c" int (← smt! 2 + 3)
  let x ← s.declareConst "x" int
  s.assert (← smt! x = c * 2)
  println! "constant   : {c}"
  println! "assertions : {← s.getAssertions}"
  println! "x          : {← s.checkSat (ifSat := s.getValue x)}"



/-! ## Models

What can be asked where the answer was sat, beyond `getValue`.
-/

/-! `getValuesAs` converts every value, `getValueAs` one value of any term, not only a constant. -/

/-- info:
values : #[1, 2]
x + y  : 3
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  s.assert (← smt! x = 1 ∧ y = 2)
  let sum ← smt! x + y
  s.checkSat (ifSat := do
    println! "values : {← s.getValuesAs Int #[x, y]}"
    println! "x + y  : {← s.getValueAs Int sum}")

/-! `blockModelValues` makes the next check find other values for the terms given, so asking again
until unsat enumerates them. -/

/-- info: values of x : #[0, 1, 2], then unsat -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst "x" (← Srt.int)
  s.assert (← smt! 0 ≤ x ∧ x ≤ 2)
  let mut seen := #[]
  for _ in [0:4] do
    let some v ← s.checkSat? (ifSat := do
        let v ← s.getValueAs Int x
        s.blockModelValues #[x]
        return some v)
      | break
    seen := seen.push v
  println! "values of x : {seen}, then unsat"

/-! `blockModel .values` blocks the values of every free constant, so `a ∨ b` has three models.
`blockModel .literals` blocks the literals that made the assertions true, so a model where `a`
holds excludes every other model where it does, and only two come out. -/

/-- info:
values   : #[#[true, false], #[true, true], #[false, true]]
literals : #[#[true, false], #[false, true]]
-/
#guard_msgs in #eval Env.runIO do
  let models (mode : Model.BlockMode) : Env (Array (Array Bool)) := do
    let s ← Solver.new
    s.setOption "produce-models" "true"
    let a ← s.declareConst "a" (← Srt.bool)
    let b ← s.declareConst "b" (← Srt.bool)
    s.assert (← smt! a ∨ b)
    let mut models := #[]
    for _ in [0:4] do
      let some m ← s.checkSat? (ifSat := do
          let m ← s.getValuesAs Bool #[a, b]
          s.blockModel mode
          return some m)
        | break
      models := models.push m
    return models
  println! "values   : {← models .values}"
  println! "literals : {← models .literals}"

/-! `getModelDomainElements` answers the finite interpretation the model gives an uninterpreted
sort, which every constant of that sort takes its value in. -/

/-- info:
domain : #[(as @U_0 U), (as @U_1 U), (as @U_2 U)]
a b c  : #[(as @U_0 U), (as @U_1 U), (as @U_2 U)]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let u ← Srt.uninterpreted "U"
  let a ← s.declareConst "a" u
  let b ← s.declareConst "b" u
  let c ← s.declareConst "c" u
  s.assert (← Term.distinctN #[a, b, c])
  s.checkSat (ifSat := do
    println! "domain : {← s.getModelDomainElements u}"
    println! "a b c  : {← s.getValues #[a, b, c]}")

/-! Under `model-cores`, `isModelCoreSymbol` says which constants the model needs: `x = 1` alone
satisfies `x = 1 ∨ y = 2`, so `y` is not essential, and `getModelAsString` leaves it out. Without
the option every constant is essential. -/

/-- info:
model-cores simple:
  values     : #[1, 0]
  essential  : x true, y false
  model      : (
(define-fun x () Int 1)
)
no model cores:
  essential  : x true, y true
  model      : (
(define-fun x () Int 1)
(define-fun y () Int 0)
)
-/
#guard_msgs in #eval Env.runIO do
  let run (cores : Bool) : Env Unit := do
    let s ← Solver.new
    s.setOption "produce-models" "true"
    if cores then s.setOption "model-cores" "simple"
    let x ← s.declareConst "x" (← Srt.int)
    let y ← s.declareConst "y" (← Srt.int)
    s.assert (← smt! x = 1 ∨ y = 2)
    s.checkSat (ifSat := do
      if cores then println! "  values     : {← s.getValuesAs Int #[x, y]}"
      println! "  essential  : x {← s.isModelCoreSymbol x}, y {← s.isModelCoreSymbol y}"
      println! "  model      : {(← s.getModelAsString #[] #[x, y]).trimAsciiEnd}")
  println! "model-cores simple:"
  run true
  println! "no model cores:"
  run false



/-! ## Learned literals and instantiations -/

/-! `getLearnedLiterals` answers the literals the solver found to hold globally, by kind: here `x`
cannot be below 3, so `y` must be negative. -/

/-- info:
input      : #[(not (>= y 0)), (>= x 3)]
preprocess : #[(>= x 6)]
solved     : #[]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-learned-literals" "true"
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  s.assert (← smt! 5 < x ∧ (x < 3 ∨ y < 0))
  let _ ← s.checkIsSat
  println! "input      : {← s.getLearnedLiterals}"
  println! "preprocess : {← s.getLearnedLiterals .preprocess}"
  println! "solved     : {← s.getLearnedLiterals .preprocessSolved}"

/-! `getInstantiations` prints the instances of each quantified formula the refutation used. -/

/-- info:
sat            : false
instantiations : (instantiations (forall ((n Int)) (>= (f n) 1))
  ( 3 )
)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let int ← Srt.int
  let f ← s.declareFun "f" #[int] int
  s.assert (← smt! ∀ (n : Int), 0 < f n)
  s.assert (← smt! f 3 < 0)
  println! "sat            : {← s.checkIsSat}"
  println! "instantiations : {← s.getInstantiations}"



/-! ## Timeout cores

`getTimeoutCoreAssuming` is only reachable where the answer was unknown, here because cvc5 finds
no model of a satisfiable quantified formula. It checks again under the assumptions given: with
one contradicting the assertions the answer is unsat, and the core is that assumption alone.
-/

/-- info:
unknown, then : unsat #[(< x 0)]
unchecked     : unsat #[(< x 0)]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-cores" "true"
  let int ← Srt.int
  let f ← s.declareFun "f" #[int] int
  let x ← s.declareConst "x" int
  s.assert (← smt! ∀ (n : Int), n < f n)
  s.assert (← smt! 0 < x)
  let assumptions := #[← smt! x < 5, ← smt! x < 0]
  let (res, core) ← s.checkSat (ifUnknown := fun _ => s.getTimeoutCoreAssuming assumptions)
  println! "unknown, then : {res} {core}"
  -- the unchecked twin answers the same
  let (res, core) ← s.getTimeoutCoreAssuming! assumptions
  println! "unchecked     : {res} {core}"



/-! ## Unchecked queries

Each modal query has a `!` twin in `Env`, which answers what the modal one would where the answer
allows it. Where it does not, cvc5 still refuses some of them.
-/

/-- info:
sat    : 1 #[1] 1 #[1] #[(as @U_0 U)] true (
(define-fun x () Int 1)
)
sat!   : 1 #[1] 1 #[1] #[(as @U_0 U)] true (
(define-fun x () Int 1)
)
unsat  : #[(and (< 0 x) (< x 2)), (< x 0)] #[(< x 0)]
unsat! : #[(and (< 0 x) (< x 2)), (< x 0)] #[(< x 0)]
value after unsat : [internal] cannot get value unless after a SAT or UNKNOWN response.
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  s.setOption "produce-unsat-cores" "true"
  s.setOption "produce-unsat-assumptions" "true"
  let u ← Srt.uninterpreted "U"
  let x ← s.declareConst "x" (← Srt.int)
  let _ ← s.declareConst "a" u
  s.assert (← smt! 0 < x ∧ x < 2)
  let render (v : Term) (vs : Terms) (n : Int) (ns : Array Int) (dom : Terms) (core : Bool)
      (model : String) : String :=
    s!"{v} {vs} {n} {ns} {dom} {core} {model.trimAsciiEnd}"
  let modal ← s.checkSat (ifSat := do
    return render (← s.getValue x) (← s.getValues #[x]) (← s.getValueAs Int x)
      (← s.getValuesAs Int #[x]) (← s.getModelDomainElements u) (← s.isModelCoreSymbol x)
      (← s.getModelAsString #[] #[x]))
  println! "sat    : {modal}"
  let unchecked := render (← s.getValue! x) (← s.getValues! #[x]) (← s.getValueAs! Int x)
    (← s.getValuesAs! Int #[x]) (← s.getModelDomainElements! u) (← s.isModelCoreSymbol! x)
    (← s.getModelAsString! #[] #[x])
  println! "sat!   : {unchecked}"
  let neg ← smt! x < 0
  let modal ← s.checkSat (assuming := #[neg])
    (ifUnsat := do return s!"{← s.getUnsatCore} {← s.getUnsatAssumptions}")
  println! "unsat  : {modal}"
  println! "unsat! : {← s.getUnsatCore!} {← s.getUnsatAssumptions!}"
  try println! "value after unsat : {← s.getValue! x}"
  catch e => println! "value after unsat : {e}"



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

/-! `getInterpolant!` answers the interpolant itself, and fails where `getInterpolant` answers
`none`. -/

/-- info:
entailed     : (and (<= c (+ a 1)) (not (= a (- c 1))))
not entailed : cvc5 found no interpolant of the assertions and `(< a c)`
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  let int ← Srt.int
  let a ← s.declareConst "a" int
  let c ← s.declareConst "c" int
  Term.gt a c >>= s.assert
  println! "entailed     : {← s.getInterpolant! (← Term.ge a c)}"
  try println! "not entailed : {← s.getInterpolant! (← Term.lt a c)}"
  catch e => println! "not entailed : {e}"



/-! ## Abducts

An abduct of assertions `A` and a conjecture `C` is a formula `B` consistent with `A` such that
`A ∧ B → C`. Asked for one that does not exist, cvc5 may search forever rather than answer, so no
`none` case is pinned here; `getAbduct!` fails on `none` exactly as `getInterpolant!` does.
-/

/-- info:
abduct      : (some (= y x))
abduct!     : (= y x)
A ∧ B → C   : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-abducts" "true"
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  let hyp ← Term.gt x (← Term.mkInt 0)
  s.assert hyp
  let conj ← Term.gt (← Term.add x y) (← Term.mkInt 0)
  println! "abduct      : {← s.getAbduct conj}"
  let b ← s.getAbduct! conj
  println! "abduct!     : {b}"
  println! "A ∧ B → C   : {← entails #[hyp, b] conj}"

/-! `getNextAbduct` enumerates further abducts, each different and each an abduct. It needs
`incremental`. -/

/-- info:
abduct : (= y x), A ∧ B → C: true
next   : (= y 1), A ∧ B → C: true
next   : (<= x y), A ∧ B → C: true
next!  : (= y (- x 1)), A ∧ B → C: true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-abducts" "true"
  s.setOption "incremental" "true"
  let int ← Srt.int
  let x ← s.declareConst "x" int
  let y ← s.declareConst "y" int
  let hyp ← smt! 0 < x
  s.assert hyp
  let conj ← smt! 0 < x + y
  let report (b : Term) : Env String := return s!"{b}, A ∧ B → C: {← entails #[hyp, b] conj}"
  println! "abduct : {← report (← s.getAbduct! conj)}"
  for _ in [0:2] do
    let some b ← s.getNextAbduct
      | println! "exhausted"
    println! "next   : {← report b}"
  println! "next!  : {← report (← s.getNextAbduct!)}"
