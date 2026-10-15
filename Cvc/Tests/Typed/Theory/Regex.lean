/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Regex
import Cvc.Typed.Core.Bool
import Cvc.Typed.Theory.String
import Cvc.Typed.Theory.Arith
import Cvc.Typed.Solver

public meta import Cvc.Typed.Theory.Regex
public meta import Cvc.Typed.Core.Bool
public meta import Cvc.Typed.Theory.String
public meta import Cvc.Typed.Theory.Arith
public meta import Cvc.Typed.Solver



/-! # Generated Regex constructors, typed -/
namespace Cvc.Tests.Typed.Term.Regex

open Cvc
open Cvc.Typed.Term

/-- info:
concat    : (re.++ re re)
union     : (re.union re re)
inter     : (re.inter re re)
diff      : (re.diff re re)
star      : (re.* re)
plus      : (re.+ re)
opt       : (re.opt re)
range     : (re.range s t)
complement: (re.comp re)
loop      : ((_ re.loop 2 5) re)
repeat    : ((_ re.^ 3) re)
-/
#guard_msgs in #eval Env.runIO do
  let re ← Cvc.Typed.Term.mkSymbolAs (Cvc.Regex) "re"
  let s ← Cvc.Typed.Term.mkSymbolAs (String) "s"
  let t ← Cvc.Typed.Term.mkSymbolAs (String) "t"

  println! "concat    : {← reConcat re re}"
  println! "union     : {← reUnion re re}"
  println! "inter     : {← reInter re re}"
  println! "diff      : {← reDiff re re}"
  println! "star      : {← reStar re}"
  println! "plus      : {← rePlus re}"
  println! "opt       : {← reOpt re}"
  println! "range     : {← reRange s t}"
  println! "complement: {← reComplement re}"
  println! "loop      : {← reLoop 2 5 re}"
  println! "repeat    : {← reRepeat 3 re}"

/-! ## Constants

These take no sort: their result is `RegLan` in every context.
-/

/-- info:
all     : re.all
allChar : re.allchar
none    : re.none
-/
#guard_msgs in #eval Env.runIO do
  println! "all     : {← reAll}"
  println! "allChar : {← reAllChar}"
  println! "none    : {← reNone}"



/-! # Solving

The same constraints as sort-erased. A regex is a `Term Regex`, so handing one where a string is
expected — or the reverse — does not typecheck, and the model values come back as `String` and
`Int` without being asked for.
-/

section solving
open Cvc.Typed

/-- A literal string term, without escape sequences. -/
def lit [Ω] (s : String) : Env (Term String) := mkString s false

/-- The regex matching exactly the literal string `s`. -/
def reLit [Ω] (s : String) : Env (Term Cvc.Regex) := do strToRegex (← lit s)

/-- info:
repeat, range  : "042"
plus           : "ababab"
concat, opt    : "abc"
loop           : "zzz"
star, inter    : "q"
union, diff    : "b"
allChar        : "yz"
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let digit ← reRange (← lit "0") (← lit "9")
  let lower ← reRange (← lit "a") (← lit "z")

  let x₁ ← s.declareConst String "x₁"
  strInRegex x₁ (← reRepeat 3 digit) >>= s.assert
  equal (← strToInt x₁) (← mkInt 42) >>= s.assert
  let x₂ ← s.declareConst String "x₂"
  strInRegex x₂ (← rePlus (← reLit "ab")) >>= s.assert
  equal (← strLength x₂) (← mkInt 6) >>= s.assert
  let x₃ ← s.declareConst String "x₃"
  strInRegex x₃ (← reConcat (← reLit "a") (← reConcat (← reOpt (← reLit "b")) (← reLit "c")))
    >>= s.assert
  distinct x₃ (← lit "ac") >>= s.assert
  let x₄ ← s.declareConst String "x₄"
  strInRegex x₄ (← reLoop 2 3 (← reLit "z")) >>= s.assert
  gt (← strLength x₄) (← mkInt 2) >>= s.assert
  let x₅ ← s.declareConst String "x₅"
  strInRegex x₅ (← reInter (← reStar lower) (← reConcat (← reAll) (← reLit "q"))) >>= s.assert
  equal (← strLength x₅) (← mkInt 1) >>= s.assert
  let x₆ ← s.declareConst String "x₆"
  strInRegex x₆ (← reDiff (← reUnion (← reLit "a") (← reLit "b")) (← reLit "a")) >>= s.assert
  let x₇ ← s.declareConst String "x₇"
  strInRegex x₇ (← reConcat (← reAllChar) (← reAllChar)) >>= s.assert
  strPrefix (← lit "y") x₇ >>= s.assert
  strSuffix (← lit "z") x₇ >>= s.assert

  s.checkSat (ifSat := do
    let str (t : Term String) : s.EnvSat String := do return repr (← s.getValue t) |>.pretty
    println! "repeat, range  : {← str x₁}"
    println! "plus           : {← str x₂}"
    println! "concat, opt    : {← str x₃}"
    println! "loop           : {← str x₄}"
    println! "star, inter    : {← str x₅}"
    println! "union, diff    : {← str x₆}"
    println! "allChar        : {← str x₇}")

/-- info:
in re.none         : unsat
in R and in comp R : unsat
"aab" in b+        : unsat
-/
#guard_msgs in #eval Env.runIO do
  let check (name : String) (f : Solver → Term String → Env Unit) : Env Unit := do
    let s ← Solver.new
    let x ← s.declareConst String "x"
    f s x
    println! "{name} : {if ← s.checkIsSat then "sat" else "unsat"}"
  check "in re.none        " fun s x => do
    strInRegex x (← reNone) >>= s.assert
  check "in R and in comp R" fun s x => do
    let r ← reStar (← reLit "ab")
    strInRegex x r >>= s.assert
    strInRegex x (← reComplement r) >>= s.assert
  check "\"aab\" in b+       " fun s _ => do
    strInRegex (← lit "aab") (← rePlus (← reLit "b")) >>= s.assert

/-- info:
indexofRe    : 2
replaceRe    : "a#b2"
replaceReAll : "a#b#"
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let digit ← reRange (← lit "0") (← lit "9")
  let bind {α : Type} [ToTyp α] (name : String) (value : Term α) : Env (Term α) := do
    let c ← s.declareConst α name
    equal c value >>= s.assert
    return c
  let indexofRe ← bind "indexofRe" (← strIndexofRe (← lit "ab12cd") (← rePlus digit) (← mkInt 0))
  let replaceRe ← bind "replaceRe" (← strReplaceRe (← lit "a1b2") digit (← lit "#"))
  let replaceReAll ← bind "replaceReAll" (← strReplaceReAll (← lit "a1b2") digit (← lit "#"))

  s.checkSat (ifSat := do
    println! "indexofRe    : {← s.getValue indexofRe}"
    println! "replaceRe    : {repr (← s.getValue replaceRe)}"
    println! "replaceReAll : {repr (← s.getValue replaceReAll)}")

/-- A regex is not a string: membership takes them in that order, and swapping them is a type
error. -/
example [Ω] (x : Term String) (r : Term Cvc.Regex) : Env (Term Bool) := strInRegex x r

/--
error: Application type mismatch: The argument
  r
has type
  Term Regex
but is expected to have type
  Term String
in the application
  r.strInRegex

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example [Ω] (x : Term String) (r : Term Cvc.Regex) : Env (Term Bool) := strInRegex r x

end solving


/-! # `regex!`

The same notation, answering a `Term Regex`; a regex in scope must be one.
-/

section regexNotation
open Cvc.Typed

/-- info:
union    : (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c"))))
in scope : (let ((_let_1 (re.+ (re.range "0" "9")))) (re.++ _let_1 (re.opt (re.++ (str.to_re ".") _let_1))))
-/
#guard_msgs in #eval Env.runIO do
  println! "union    : {← regex! "a" | "b" "c"*}"
  let digit ← regex! ['0'-'9']
  println! "in scope : {← regex! digit+ ("." digit+)?}"

/-- The result is a `Term Regex`. -/
example [Ω] : Env (Term Cvc.Regex) := regex! ['a'-'z']+ ("." ['a'-'z']+)*

/-! A term in scope at another sort is refused where it is used. -/

/--
error: Type mismatch
  s
has type
  Term String
but is expected to have type
  Term Regex

Note: The following definitions were not unfolded because their definition is not exposed:
  Term ↦ 4
-/
#guard_msgs in
example [Ω] (s : Term String) : Env (Term Cvc.Regex) := regex! s*

/-- info: number : "1.5" -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst String "x"
  let digit ← regex! ['0'-'9']
  Term.strInRegex x (← regex! digit+ ("." digit+)?) >>= s.assert
  Term.equal (← Term.strLength x) (← Term.mkInt 3) >>= s.assert
  Term.strContains x (← lit ".") >>= s.assert
  Term.strPrefix (← lit "1") x >>= s.assert
  Term.strSuffix (← lit "5") x >>= s.assert
  s.checkSat (ifSat := do println! "number : {repr (← s.getValue x)}")

end regexNotation
