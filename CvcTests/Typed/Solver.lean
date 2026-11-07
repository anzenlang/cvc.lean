/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Core.Solver
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Core.Solver
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # The solver, typed

Only the functions shared by both layers are covered here: the ones mentioning a term belong to
whichever layer states their sorts.
-/
namespace Cvc.Tests.Typed.Solver

open Cvc
open Cvc.Typed

/-! ## Options and information -/

/-- info:
option set  : true
option unset: false
info set    : ok
names       : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Typed.Solver.new

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
  let s ← Cvc.Typed.Solver.new
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
  let s ← Cvc.Typed.Solver.new

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
  let s ← Cvc.Typed.Solver.new
  let version ← s.getVersion
  println! "version : {!version.isEmpty}"

/-! ## Asserting and checking

From here the signatures mention terms, so the two layers differ: this one takes `Bool`-indexed
formulas, and reads a model value back as the Lean value its index describes.
-/

/-- info:
assertions : 2
sat        : x = 1, y = 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  let three ← Term.mkInt 3

  Term.equal (← Term.add x y) three >>= s.assert
  Term.lt x y >>= s.assert
  println! "assertions : {(← s.getAssertions).size}"

  s.checkSat (ifSat := do
    let vx : Int ← s.getValue x
    let vy : Int ← s.getValue y
    println! "sat        : x = {vx}, y = {vy}")

/-- info: unsat core : 2 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-cores" "true"

  let b ← s.declareConstAs Bool "b"
  s.assert b
  Term.not b >>= s.assert

  let core ← s.checkSat (ifUnsat := do return (← s.getUnsatCore).size)
  println! "unsat core : {core}"

/-- info: unexpected : caught -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let b ← s.declareConstAs Bool "b"
  s.assert b
  let outcome ←
    try
      let _ ← s.checkSat (ifUnsat := do return "unsat")
      pure "no error"
    catch _ => pure "caught"
  println! "unexpected : {outcome}"

/-! `getUnsatAssumptions` answers the assumptions the refutation used, as formulas. -/

/-- info: unsat assumptions : #[(< x 0)] -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-assumptions" "true"
  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  s.assert (← smt! 0 < x)
  let assumptions := #[← smt! 0 < y, ← smt! x < 0, ← smt! y < 5]
  let core : Terms Bool ← s.checkSat (assuming := assumptions) (ifUnsat := s.getUnsatAssumptions)
  println! "unsat assumptions : {core}"

/-! `defineConst` takes its sort from its body's index, and answers a constant at that index. -/

/-- info:
constant : c
x        : 10
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let c : Term Int ← s.defineConst "c" (← smt! 2 + 3)
  let x ← s.declareConstAs Int "x"
  s.assert (← smt! x = c * 2)
  println! "constant : {c}"
  let vx : Int ← s.checkSat (ifSat := s.getValue x)
  println! "x        : {vx}"



/-! ## Models

The sort-erased tests cover what these do; these pin that the typed forms take and answer terms at
their index.
-/

/-! `blockModelValues` takes terms of one index; asking again until unsat enumerates their values,
here read back as terms (`getValueTerms`) and as Lean values. -/

/-- info:
values : #[0, 1, 2], then unsat
terms  : #[#[0, 0], #[1, 1], #[2, 2]]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  s.assert (← smt! 0 ≤ x ∧ x ≤ 2 ∧ x ≤ y ∧ y ≤ x + 1)
  let mut values : Array Int := #[]
  let mut terms : Array (Terms Int) := #[]
  for _ in [0:4] do
    let some (v, ts) ← s.checkSat? (ifSat := do
        let v : Int ← s.getValue x
        let ts ← s.getValueTerms #[x, y]
        s.blockModelValues #[x]
        return some (v, ts))
      | break
    values := values.push v
    terms := terms.push ts
  println! "values : {values}, then unsat"
  println! "terms  : {terms}"

/-- A Lean type denoting the uninterpreted sort `U`, which has to be declared before use. -/
structure U

instance : ToTyp U := ⟨.uninterpreted "U"⟩

/-! `getModelDomainElements` takes the uninterpreted sort as an index, and answers terms of it. -/

/-- info:
domain : #[(as @U_0 U), (as @U_1 U)]
a b    : #[(as @U_0 U), (as @U_1 U)]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let _ ← Srt.uninterpreted "U"
  let a ← s.declareConstAs U "a"
  let b ← s.declareConstAs U "b"
  s.assert (← smt! a ≠ b)
  s.checkSat (ifSat := do
    let domain : Terms U ← s.getModelDomainElements U
    println! "domain : {domain}"
    println! "a b    : {← s.getValueTerms #[a, b]}")

/-! Under `model-cores`, `isModelCoreSymbol` tells the essential constants from the others. -/

/-- info: essential : x true, y false -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  s.setOption "model-cores" "simple"
  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  s.assert (← smt! x = 1 ∨ y = 2)
  s.checkSat (ifSat := do
    println! "essential : x {← s.isModelCoreSymbol x}, y {← s.isModelCoreSymbol y}")

/-! The unchecked twins answer what the modal queries do: `getValue!` a Lean value, as
`getValue` does. -/

/-- info:
sat    : 1 #[1, 2] 1 #[(as @U_0 U)]
sat!   : 1 #[1, 2] 1 #[(as @U_0 U)]
unsat  : #[(< x 0)] #[(and (< 0 x) (and (< x 2) (= y (+ x 1)))), (< x 0)]
unsat! : #[(< x 0)] #[(and (< 0 x) (and (< x 2) (= y (+ x 1)))), (< x 0)]
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  s.setOption "produce-unsat-cores" "true"
  s.setOption "produce-unsat-assumptions" "true"
  let _ ← Srt.uninterpreted "U"
  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  let _ ← s.declareConstAs U "a"
  s.assert (← smt! 0 < x ∧ x < 2 ∧ y = x + 1)
  let render (v : Int) (vs : Array Int) (t : Term Int) (dom : Terms U) : String :=
    s!"{v} {vs} {t} {dom}"
  let modal ← s.checkSat (ifSat := do
    return render (← s.getValue x) (← s.getValues #[x, y]) (← s.getValueTerm x)
      (← s.getModelDomainElements U))
  println! "sat    : {modal}"
  let unchecked := render (← s.getValue! x) (← s.getValues! #[x, y]) (← s.getValueTerm! x)
    (← s.getModelDomainElements! U)
  println! "sat!   : {unchecked}"
  let neg ← smt! x < 0
  let modal ← s.checkSat (assuming := #[neg])
    (ifUnsat := do return s!"{← s.getUnsatAssumptions} {← s.getUnsatCore}")
  println! "unsat  : {modal}"
  println! "unsat! : {← s.getUnsatAssumptions!} {← s.getUnsatCore!}"

/-! `getTimeoutCoreAssuming` takes formulas and answers the core as formulas. cvc5 answers unknown
on this satisfiable quantified formula, and the assumption contradicting the assertions is the
core. -/

/-- info: unknown, then : unsat #[(< x 0)] -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-unsat-cores" "true"
  let f ← s.declareFunAs (Int → Int) "f"
  let x ← s.declareConstAs Int "x"
  s.assert (← smt! ∀ (n : Int), n < f n)
  s.assert (← smt! 0 < x)
  let assumptions := #[← smt! x < 5, ← smt! x < 0]
  let (res, core) ← s.checkSat (ifUnknown := fun _ => s.getTimeoutCoreAssuming assumptions)
  let core : Terms Bool := core
  println! "unknown, then : {res} {core}"



/-! ## Interpolants

The sort-erased tests cover the semantics; these pin that the same answers come back indexed at
`Bool`, an interpolant being a formula, and that the absence of one is `none` here too.
-/

/-- Whether `hyps` entail `concl`, by refuting `hyps ∧ ¬concl` on a fresh solver. -/
def entails [Ω] (hyps : Array (Term Bool)) (concl : Term Bool) : Env Bool := do
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

  let a ← s.declareConstAs Int "a"
  let b ← s.declareConstAs Int "b"
  let c ← s.declareConstAs Int "c"
  let one ← Term.mkInt 1
  let hyps := #[← Term.equal a (← Term.add b one), ← Term.equal b (← Term.add c one)]
  for h in hyps do s.assert h
  let conj ← Term.gt a c

  let some (i : Term Bool) ← s.getInterpolant conj
    | println! "no interpolant"
  println! "interpolant : {i}"
  println! "A → I       : {← entails hyps i}"
  println! "I → C       : {← entails #[i] conj}"

/-- info: not entailed : none -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let a ← s.declareConstAs Int "a"
  let c ← s.declareConstAs Int "c"
  Term.gt a c >>= s.assert
  println! "not entailed : {← s.getInterpolant (← Term.lt a c)}"

/-! The `!` forms answer a `Term Bool` and fail where the `Option` ones answer `none`. -/

/-- info:
interpolant! : (and (<= c (+ a 1)) (not (= a (- c 1))))
not entailed : cvc5 found no interpolant of the assertions and `(< a c)`
abduct!      : (= y x)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  s.setOption "produce-abducts" "true"
  let a ← s.declareConstAs Int "a"
  let c ← s.declareConstAs Int "c"
  Term.gt a c >>= s.assert
  let i : Term Bool ← s.getInterpolant! (← Term.ge a c)
  println! "interpolant! : {i}"
  try println! "not entailed : {← s.getInterpolant! (← Term.lt a c)}"
  catch e => println! "not entailed : {e}"
  let s ← Solver.new
  s.setOption "produce-abducts" "true"
  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  Term.gt x (← Term.mkInt 0) >>= s.assert
  let b : Term Bool ← s.getAbduct! (← Term.gt (← Term.add x y) (← Term.mkInt 0))
  println! "abduct!      : {b}"

/-- info:
first  : (<= 1 y)
next   : (not (<= y 1))
next   : (or (= y 1) (<= 1 y))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"
  s.setOption "incremental" "true"

  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  let z ← s.declareConstAs Int "z"
  let zero ← Term.mkInt 0
  Term.gt (← Term.add x y) zero >>= s.assert
  Term.lt x zero >>= s.assert
  let conj ← Term.or (← Term.gt (← Term.add y z) zero) (← Term.lt z zero)

  let some first ← s.getInterpolant conj
    | println! "no interpolant"
  println! "first  : {first}"
  for _ in [0:2] do
    let some next ← s.getNextInterpolant
      | println! "exhausted"
    println! "next   : {next}"

/-! `getNextAbduct` answers further abducts, as formulas. -/

/-- info:
abduct : (= y x)
next   : (some (= y 1))
next!  : (<= x y)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-abducts" "true"
  s.setOption "incremental" "true"
  let x ← s.declareConstAs Int "x"
  let y ← s.declareConstAs Int "y"
  s.assert (← smt! 0 < x)
  println! "abduct : {← s.getAbduct! (← smt! 0 < x + y)}"
  let next : Option (Term Bool) ← s.getNextAbduct
  println! "next   : {next}"
  let next : Term Bool ← s.getNextAbduct!
  println! "next!  : {next}"


/-! ## The signatures state the sorts -/

section signatures
variable [Ω]

/-- info: @Solver.assert : [inst : Ω] → Solver → Term Bool → Env Unit -/
#guard_msgs in #check @Cvc.Typed.Solver.assert

/-- info: @Untyped.Solver.assert : [inst : Ω] → Untyped.Solver → Untyped.Term → Env Unit -/
#guard_msgs in #check @Cvc.Untyped.Solver.assert

/-- info: @Solver.getUnsatCore : [inst : Ω] → (s : Solver) → s.EnvUnsat (Terms Bool) -/
#guard_msgs in #check @Cvc.Typed.Solver.getUnsatCore

/-- info: @Solver.getInterpolant : [inst : Ω] →
  Solver → Term Bool → optParam (Option (Grammar Bool)) none → Env (Option (Term Bool)) -/
#guard_msgs in #check @Cvc.Typed.Solver.getInterpolant

/-- info: @Solver.getNextInterpolant : [inst : Ω] → Solver → Env (Option (Term Bool)) -/
#guard_msgs in #check @Cvc.Typed.Solver.getNextInterpolant

/-- info: @Solver.getUnsatAssumptions : [inst : Ω] → (s : Solver) → s.EnvUnsat (Terms Bool) -/
#guard_msgs in #check @Cvc.Typed.Solver.getUnsatAssumptions

/-- info: @Solver.getTimeoutCoreAssuming : [inst : Ω] → (s : Solver) → Terms Bool → s.EnvUnknown (Result × Terms Bool) -/
#guard_msgs in #check @Cvc.Typed.Solver.getTimeoutCoreAssuming

/-- info: @Solver.defineConst : [inst : Ω] →
  Solver → {α : Type} → [ToTyp α] → String → Term α → optParam Bool false → Env (Term α) -/
#guard_msgs in #check @Cvc.Typed.Solver.defineConst

/-- info: @Solver.getModelDomainElements : [inst : Ω] → (s : Solver) → (α : Type) → [ToTyp α] → s.EnvSat (Terms α) -/
#guard_msgs in #check @Cvc.Typed.Solver.getModelDomainElements

/-- info: @Solver.blockModelValues : [inst : Ω] → {α : Type} → (s : Solver) → Terms α → s.EnvSat Unit -/
#guard_msgs in #check @Cvc.Typed.Solver.blockModelValues

/-- info: @Solver.getValue! : [inst : Ω] → Solver → {α : Type} → [TermToValue α] → Term α → Env α -/
#guard_msgs in #check @Cvc.Typed.Solver.getValue!

/-- info: @Solver.getLearnedLiterals : [inst : Ω] → Solver → optParam LearnedLitType LearnedLitType.input → Env (Terms Bool) -/
#guard_msgs in #check @Cvc.Typed.Solver.getLearnedLiterals

end signatures
