/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc
public meta import Cvc

public import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External



set_option pp.rawOnError true



#doc (Manual) "Overview" =>
%%%
tag := "overview"
htmlSplit := .never
%%%

```lean -show
namespace Section.Overview
```

This section showcases various features of cvc.lean for new users to get an idea of what it can do. It is light on technical details which are provided in the rest of this manual. For now just know that cvc.lean has two APIs that differ in how `Term`s (and a few other types) are encoded and the static guarantees they provide:

- `Cvc.Typed` strongly-types terms so that the cvc5-level sort of a term appears in its type, making ill-formed terms (and most solver queries) fail at compile-times. For instance:
  - `Term Bool`, `Term String`, *etc.*
  - asserting a formula in a solver takes a `Term Bool`.

- `Cvc.Untyped` just has a simple type `Term` for terms and you are responsible for creating well-formed terms and querying the solver correctly; failure to do so will result in a runtime error.

The examples below use the typed API.

```lean
open Cvc Typed
```

Also, we need an instance of type-class {lean}`Ω` in scope to manipulate sorts, terms, solvers, *etc.*

```lean
variable [Ω]
```

Think of it as a *"cvc5 world"* which we need to do anything, in particular to write code in cvc.lean's {lean}`Env` monad.



# Solver and basic term creation

```lean (name := intro_ex_setup)
def setup : Env (Solver × Term Bool × Term Int) := do
  -- all solvers share the same environment
  let solver ← Solver.new
  solver.setOption "produce-models" "true"

  -- declare a symbol in the environment, type is inferred
  let b1 ← Term.mkSymbol "b1"
  -- any solver in the current environment will know about
  -- this symbol; writing `solver.declareConst "b1"` works
  -- too and has the same effect

  -- you can also state the symbol's type explicitly
  let i1 ← Term.mkSymbolAs Int "i1"

  -- term creation with `smt!` syntax extension
  let formula ← smt! ¬ b1 ∨ (b1 ∧ 0 < i1)

  -- term creation without `smt!`
  let formula_by_hand ← do
    let zero ← Term.mkInt 0
    let i1_pos ← zero.lt i1
    let conj ← b1.and i1_pos
    (← b1.not).or conj

  -- terms are perfectly shared, both formulas are the same
  if formula != formula_by_hand then
    panic! "not perfectly shared 🙀"

  solver.assert formula

  return (solver, b1, i1)
```

Use {lean}`Env.runIO` to run {lean}`Env` code in {lean}`IO`.

```lean (name := intro_ex_setup)
#eval Env.runIO do
  let (solver, b1, i1) ← setup
  println! "b1 : {b1}, i1 : {i1}"
  println! "assertions:"
  for f in ← solver.getAssertions do
    println! "- {f}"
```
```leanOutput intro_ex_setup
b1 : b1, i1 : i1
assertions:
- (or (not b1) (and b1 (< 0 i1)))
```

# Simple check-sat

The result of a check-sat is either _sat_, _unsat_, or _unknown_. The `Solver.checkSat` function takes a optional continuation for each (`ifSat`, `ifUnsat`, `ifUnknown`); the defaults fail and report the result as unexpected.

```lean (name := intro_ex_checksat)
#eval Env.runIO do
  let (solver, b1, i1) ← setup
  println! "check-sat"
  for f in ← solver.getAssertions do println! "∧ {f}"
  solver.checkSat
    (ifSat := do
      println! "→ sat"
      -- notice `b1`'s type is lean's `Bool`
      let b1Val ← solver.getValue b1
      -- notice `i1`'s type is lean's `Int`
      let i1Val ← solver.getValue i1
      println! "  values : b1 ↦ {b1Val}, i1 ↦ {i1Val}"
      -- alternatively you can ask for value as `Term _`
      let b1ValTerm ← solver.getValueTerm b1
      let i1ValTerm ← solver.getValueTerm i1
      println!
        "  terms  : b1 ↦ {b1ValTerm}, i1 ↦ {i1ValTerm}")
```
```leanOutput intro_ex_checksat
check-sat
∧ (or (not b1) (and b1 (< 0 i1)))
→ sat
  values : b1 ↦ false, i1 ↦ 0
  terms  : b1 ↦ false, i1 ↦ 0
```

# Check-sat with assumptions

`Solver.checkSat` actually has a fourth optional parameter `assuming` that accepts {lean}`Array (Term Bool)` values. It adds constraints to that check-sat without changing the solver's actual assertions.

```lean (name := intro_ex_assuming)
#eval Env.runIO do
  let (solver, b1, i1) ← setup
  println! "check-sat assuming {b1}"
  solver.checkSat (assuming := #[b1])
    (ifSat := do
      let b1 ← solver.getValue b1
      let i1 ← solver.getValue i1
      println! "→ sat: b1 := {b1}, i1 := {i1}")

  let i1_eq_zero ← smt! i1 = 0
  println! "check-sat assuming {b1} and {i1_eq_zero}"
  solver.checkSat (assuming := #[b1, i1_eq_zero])
    (ifSat := println! "→ sat, unexpected!")
    (ifUnsat := println! "→ unsat")
    (ifUnknown := fun explain =>
      println! "→ solver could not decide 😥:\n  {explain}")
```
```leanOutput intro_ex_assuming
check-sat assuming b1
→ sat: b1 := true, i1 := 1
check-sat assuming b1 and (= i1 0)
→ unsat
```

# Synthesis

This example uses the `smt.grammar!` syntax extension for grammars, but they can also be built using the {lean}`Grammar` API.

```lean (name := intro_ex_synth)
#eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"

  let g ← smt.grammar! s (x y : Int) where
    start : Int  := x | y | if cnd then start else start
    cnd   : Bool := start ≤ start

  let mx ← s.synthFun "max" g
  let a ← s.declareSygusVar Int "a"
  let b ← s.declareSygusVar Int "b"
  let mab ← smt! mx a b
  s.addSygusConstraint (← smt! mab ≥ a)
  s.addSygusConstraint (← smt! mab ≥ b)
  s.addSygusConstraint (← smt! mab = a ∨ mab = b)

  s.checkSynth (ifSolved := do
    println! "max := {(← s.getSynthSolution mx).relax}")
```
```leanOutput intro_ex_synth
max := (lambda ((x Int) (y Int)) (ite (<= y x) x y))
```

# Quantifier elimination

```lean (name := intro_ex_qe)
#eval Env.runIO do
  let solver ← Solver.new
  let y ← Term.mkSymbol "y"
  let f ← smt! ∃ (x : Int), 0 < x ∧ x < 5 ∧ 2 * y = x - 1
  let elim ← solver.qe f
  println! "elim := {elim}"
```
```leanOutput intro_ex_qe
elim := (and (>= y 0) (not (>= y 2)))
```

# Interpolation: free and constrained by a grammar

```lean (name := intro_ex_interpolation)
#eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-interpolants" "true"

  let x ← Term.mkSymbolAs Int "x"
  let y ← Term.mkSymbolAs Int "y"
  smt! y = 6*x + 3 >>= s.assert
  smt!    0 ≤ x    >>= s.assert
  let goal ← smt! ¬ (y = 5) ∧ ¬ (y = 6)

  -- interpolate freely (no grammar)
  let some i ← s.getInterpolant goal
    | println! "no free interpolant"
  println! "free        : {i}"

  let g ← smt.grammar! s where
    start : Bool := atom | atom ∧ start
    atom  : Bool := y % k = r
    k     : Int  := 2 | 3 | 4 | 5
    r     : Int  := 0 | 1 | 2

  -- interpolate with grammar [g]
  let some i ← s.getInterpolant goal g
    | println! "no constrained interpolant"
  println! "constrained : {i}"
```
```leanOutput intro_ex_interpolation
free        : (= y (ite (<= y 6) 3 y))
constrained : (and (= (mod y 2) 1) (= (mod y 3) 0))
```

# String/regex

```lean (name := intro_ex_theories)
#eval Env.runIO do
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  let zero ← smt! 0
  let someString ← smt! "cvc.lean"
  let s1 ← Term.mkSymbol "s1"

  s1.strContains someString >>= solver.assert
  let s1Len ← s1.strLength
  smt! s1Len = 11 >>= solver.assert
  let s1Char0 ← s1.strCharAt zero
  smt! s1Char0 = "!" >>= solver.assert

  solver.checkSat (ifSat := do
    let s1 ← solver.getValue s1
    println! "s1 : `{s1}`")

  let regex1 ← regex! . "cvc" .* ['0'-'9']{2}
  s1.strInRegex regex1 >>= solver.assert
  solver.checkSat
    (ifSat := do
      let s1 ← solver.getValue s1
      println! "s1 : `{s1}`")

  let regex2 ← regex! . "cvc" .* ['0'-'9']{3}
  s1.strInRegex regex2 >>= solver.assert
  solver.checkSat (ifUnsat := println! "unsat")
```
```leanOutput intro_ex_theories
s1 : `!AAcvc.lean`
s1 : `!cvc.lean00`
unsat
```

# Bit-vectors

A bit-vector's width is part of its type, `Term (BitVec 8)`, and its model value is Lean's own `BitVec 8`. Operations that change the width say so in their types.

```lean (name := intro_ex_bitvec)
#eval Env.runIO do
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  let x ← Term.mkSymbolAs (BitVec 8) "x"
  let one ← Term.mkBitVec 8 1
  let zero ← Term.mkBitVec 8 0
  let n64 ← Term.mkBitVec 8 64

  -- a power of two: exactly one bit set
  let xPred ← x.bvSub one
  smt! x &&& xPred = zero ∧ ¬ (x = zero)
    >>= solver.assert
  -- above 64 unsigned, yet negative signed
  x.bvUgt n64 >>= solver.assert
  x.bvSlt zero >>= solver.assert
  -- two `BitVec 8` concatenate to a `BitVec 16`
  let half ← x.bvLshr one
  let wide : Term (BitVec 16) ← x.bvConcat half

  solver.checkSat (ifSat := do
    let x ← solver.getValue x
    println! "x    : {x}"
    println! "     : {x.toNat} unsigned, {x.toInt} signed"
    println! "wide : {← solver.getValue wide}")

  -- incrementing the largest value wraps around
  let y ← Term.mkSymbolAs (BitVec 8) "y"
  let ySucc ← y.bvAdd one
  solver.checkSat (assuming := #[← ySucc.bvUlt y])
    (ifSat := do
      let y ← solver.getValue y
      println! "y + 1 < y for y = {y}")
```
```leanOutput intro_ex_bitvec
x    : 0x80#8
     : 128 unsigned, -128 signed
wide : 0x8040#16
y + 1 < y for y = 0xff#8
```

# Floating-point

`Cvc.Float exp sig` is SMT-LIB's `(_ FloatingPoint exp sig)`, so `Cvc.Float 11 53` is double precision. Arithmetic takes a rounding mode, and floating-point equality `fpEq` is not `=`.

```lean (name := intro_ex_float)
abbrev Double := Cvc.Float 11 53

/-- A real, as the nearest double in rounding mode `rm`. -/
def double (rm : Float.RoundingMode) (r : Rat)
: Env (Term Double) := do
  let rm ← Term.mkRoundingMode rm
  Term.fpOfReal 11 53 rm (← Term.mkReal r)

#eval Env.runIO do
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  let rne := Float.RoundingMode.nearestTiesToEven

  -- the classic
  let a ← double rne 0.1
  let b ← double rne 0.2
  let c ← double rne 0.3
  let sum ← Term.fpAdd (← Term.mkRoundingMode rne) a b
  solver.checkSat (assuming := #[← sum.fpGt c])
    (ifSat := println! "0.1 + 0.2 > 0.3")

  -- rounding modes matter
  let down ← double .towardNegative (1 / 3)
  let up ← double .towardPositive (1 / 3)
  solver.checkSat (assuming := #[← down.fpLt up])
    (ifSat := println! "1/3 rounded: down < up")

  -- NaN is `=` to itself, but not `fpEq` to itself
  let n ← Term.mkSymbolAs Double "n"
  smt! n = n ∧ ¬ ![n.fpEq n] >>= solver.assert
  let nIsNan ← n.fpIsNan
  solver.checkSat (ifSat := do
    println! "n := {← solver.getValue n}"
    println! "n is NaN: {← solver.getValue nIsNan}")
```
```leanOutput intro_ex_float
0.1 + 0.2 > 0.3
1/3 rounded: down < up
n := Float[11, 53, 0x7ff8000000000000#64]
n is NaN: true
```

# Arrays

An SMT array is total, so its Lean counterpart is `Cvc.TotalMap ι κ`: a default element plus the indices that differ from it. Constant arrays need cvc5's `arrays-exp` option.

```lean (name := intro_ex_array)
abbrev IntArray := TotalMap Int Int

#eval Env.runIO do
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  solver.setOption "arrays-exp" "true"
  let a ← Term.mkSymbolAs IntArray "a"
  let zero ← Term.mkInt 0
  let zeros : Term IntArray ←
    Term.mkConstArray zero
  let three ← Term.mkInt 3

  -- `a` is all zeros, except perhaps at index 3...
  let forceZeroAt3 ← a.store three zero
  smt! forceZeroAt3 = zeros >>= solver.assert
  -- ...where it is `17`
  let at3 ← a.select three
  smt! at3 = 17 >>= solver.assert
  solver.checkSat (ifSat := do
    println! "a := {← solver.getValue a}")

  -- reading back what was just written succeeds
  let i ← Term.mkSymbolAs Int "i"
  let v ← Term.mkSymbolAs Int "v"
  let read ← (← a.store i v).select i
  solver.checkSat (assuming := #[← smt! ¬ (read = v)])
    (ifUnsat := println! "{read} = {v}")
```
```leanOutput intro_ex_array
a := { 3 ↦ 17, _ ↦ 0 }
(select (store a i v) i) = v
```

# Separation logic

A solver's heap is declared once, at the Lean types of its locations and data, and `pto` (points-to) hangs off the handle that declaration returns, so a mismatched location or datum is a type error.
The separating conjunction `sepStar` splits the heap into disjoint parts, which is what sets it apart from `∧`.

```lean (name := intro_ex_sep)
/-- Runs `query` on a fresh solver with an `Int ↦ Int` heap.

A heap can only be declared once a logic is set, and
separation logic is not supported incrementally, so each
query gets a solver of its own.
-/
def withHeap
  (query : (s : Solver) → s.Heap Int Int → Env Unit)
: Env Unit := do
  let s ← Solver.new
  s.setLogic Logic.all.qf
  s.setOption "incremental" "false"
  s.setOption "produce-models" "true"
  query s (← s.declareSepHeap Int Int)

#eval Env.runIO do
  let x ← Term.mkSymbol "x"
  let y ← Term.mkSymbol "y"
  let one ← Term.mkInt 1
  let two ← Term.mkInt 2

  -- `x ↦ 1 ∗ y ↦ 2`: two disjoint cells
  withHeap fun s heap => do
    let xTo1 ← heap.pto x one
    let yTo2 ← heap.pto y two
    Term.sepStar xTo1 yTo2 >>= s.assert
    s.checkSat (ifSat := do
      let x ← s.getValue x
      let y ← s.getValue y
      println! "x = {x}, y = {y}"
      println! "heap : {← s.getValueSepHeap}")

  -- disjoint cells cannot share a location
  withHeap fun s heap => do
    let xTo1 ← heap.pto x one
    let yTo2 ← heap.pto y two
    Term.sepStar xTo1 yTo2 >>= s.assert
    smt! x = y >>= s.assert
    s.checkSat (ifUnsat := println! "∗ with x = y : unsat")

  -- `∧` asks one heap to be both cells at once
  withHeap fun s heap => do
    let xTo1 ← heap.pto x one
    let yTo2 ← heap.pto y two
    Term.and xTo1 yTo2 >>= s.assert
    s.checkSat (ifUnsat := println! "∧ : unsat")
```
```leanOutput intro_ex_sep
x = 0, y = 1
heap : (sep (pto 0 1) (pto 1 2))
∗ with x = y : unsat
∧ : unsat
```

# Relations and tables: verifying query rewrites

A relation is a set of tuples and a table a bag of them, typed by their columns: `Rel [String] Int` holds `(String, Int)` rows. That makes the solver a tool for checking query rewrites against every possible database, and for producing one where a rewrite is wrong.

Take a company whose staff, `(employee, project)`, is sharded between a `paris` and a `berlin` database, and whose `budgets` are `(project, budget)`. The query maps each employee to the budget of their project: a join, which composes the two relations.

```lean (name := intro_ex_rel)
#eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  -- relations have no Lean value type: print the model term
  let valueOf {α : Type} (t : Term α) := do
    let v ← Untyped.Solver.getValue s t.relax
    return toString v

  let paris ←
    Term.mkSymbolAs (Rel [String] String) "paris"
  let berlin ←
    Term.mkSymbolAs (Rel [String] String) "berlin"
  let budgets ←
    Term.mkSymbolAs (Rel [String] Int) "budgets"
  -- employee ↦ budget of their project
  let query (staff : Term (Rel [String] String)) :=
    Term.relJoin staff budgets

  -- run the query per shard and merge the answers
  let merged ← Term.relUnion paris berlin >>= query
  let perShard ←
    Term.relUnion (← query paris) (← query berlin)
  let differ ← smt! ¬ (merged = perShard)
  s.checkSat (assuming := #[differ])
    (ifUnsat := println! "∪ pushes through the join")

  -- staff in both offices, computed per shard: wrong
  let both ← Term.relInter paris berlin >>= query
  let bothPerShard ←
    Term.relInter (← query paris) (← query berlin)
  let differ ← smt! ¬ (both = bothPerShard)
  s.checkSat (assuming := #[differ]) (ifSat := do
    println! "∩ does not, counterexample:"
    println! "  paris   = {← valueOf paris}"
    println! "  berlin  = {← valueOf berlin}"
    println! "  budgets = {← valueOf budgets}")
```
```leanOutput intro_ex_rel
∪ pushes through the join
∩ does not, counterexample:
  paris   = (set.singleton (tuple "" "A"))
  berlin  = (set.singleton (tuple "" ""))
  budgets = (set.union (set.singleton (tuple "A" 0)) (set.singleton (tuple "" 0)))
```

Employee `""` works on a different project in each office, so the offices share no staff row; but both projects have budget `0`, so both answers map `""` to `0`.

Tables count rows, so the same question about SQL's `UNION ALL` (`tableUnionDisjoint`) and `UNION` (`tableUnionMax`) has a different answer.

```lean (name := intro_ex_tab)
#eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  -- relations have no Lean value type: print the model term
  let valueOf {α : Type} (t : Term α) := do
    let v ← Untyped.Solver.getValue s t.relax
    return toString v

  let paris ←
    Term.mkSymbolAs (Tab [String] String) "paris"
  let berlin ←
    Term.mkSymbolAs (Tab [String] String) "berlin"
  let budgets ←
    Term.mkSymbolAs (Tab [String] Int) "budgets"
  -- equi-join on `staff.project = budgets.project`
  let query (staff : Term (Tab [String] String)) :=
    Term.tableJoin #[(1, 0)] staff budgets

  let all ← Term.tableUnionDisjoint paris berlin >>= query
  let perShard ← Term.tableUnionDisjoint
    (← query paris) (← query berlin)
  let differ ← smt! ¬ (all = perShard)
  s.checkSat (assuming := #[differ])
    (ifUnsat :=
      println! "UNION ALL pushes through the join")

  -- does deduplicating the shards change the answer?
  let dedup ← Term.tableUnionMax paris berlin >>= query
  let differ ← smt! ¬ (all = dedup)
  s.checkSat (assuming := #[differ]) (ifSat := do
    println! "UNION ≠ UNION ALL, counterexample:"
    println! "  paris   = {← valueOf paris}"
    println! "  berlin  = {← valueOf berlin}"
    println! "  budgets = {← valueOf budgets}")
```
```leanOutput intro_ex_tab
UNION ALL pushes through the join
UNION ≠ UNION ALL, counterexample:
  paris   = (bag (tuple "A" "") 2)
  berlin  = (bag (tuple "A" "") 1)
  budgets = (bag (tuple "" (- 2)) 2)
```
