/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Regex
import Cvc.Untyped.Core.Bool
import Cvc.Untyped.Theory.String
import Cvc.Untyped.Theory.Arith
import Cvc.Untyped.Core.Solver

public meta import Cvc.Untyped.Theory.Regex
public meta import Cvc.Untyped.Core.Bool
public meta import Cvc.Untyped.Theory.String
public meta import Cvc.Untyped.Theory.Arith
public meta import Cvc.Untyped.Core.Solver



/-! # Generated Regex constructors, sort-erased -/
namespace Cvc.Tests.Untyped.Term.Regex

open Cvc
open Cvc.Untyped.Term

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
  let re ← Cvc.Untyped.Term.mkSymbolAs (Cvc.Regex) "re"
  let s ← Cvc.Untyped.Term.mkSymbolAs (String) "s"
  let t ← Cvc.Untyped.Term.mkSymbolAs (String) "t"

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

A regex only means something through string membership, so these tests go through `strInRegex` and
the string operators that take a regex. Each membership constraint is paired with enough to leave a
single string, which is read back out of the model, and every regex constructor appears in one.
-/

section solving
open Cvc.Untyped

/-- A literal string term, without escape sequences. -/
def lit [Ω] (s : String) : Env Term := mkString s false

/-- The regex matching exactly the literal string `s`. -/
def reLit [Ω] (s : String) : Env Term := do strToRegex (← lit s)

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
  let str ← Srt.string
  let digit ← reRange (← lit "0") (← lit "9")
  let lower ← reRange (← lit "a") (← lit "z")

  -- three digits denoting 42
  let x₁ ← s.declareConst "x₁" str
  strInRegex x₁ (← reRepeat 3 digit) >>= s.assert
  equal (← strToInt x₁) (← mkInt 42) >>= s.assert
  -- "ab" one or more times, six characters long
  let x₂ ← s.declareConst "x₂" str
  strInRegex x₂ (← rePlus (← reLit "ab")) >>= s.assert
  equal (← strLength x₂) (← mkInt 6) >>= s.assert
  -- "a", an optional "b", then "c" — and not "ac"
  let x₃ ← s.declareConst "x₃" str
  strInRegex x₃ (← reConcat (← reLit "a") (← reConcat (← reOpt (← reLit "b")) (← reLit "c")))
    >>= s.assert
  distinct x₃ (← lit "ac") >>= s.assert
  -- two or three "z", more than two characters long
  let x₄ ← s.declareConst "x₄" str
  strInRegex x₄ (← reLoop 2 3 (← reLit "z")) >>= s.assert
  gt (← strLength x₄) (← mkInt 2) >>= s.assert
  -- lowercase letters only, ending in "q", one character long
  let x₅ ← s.declareConst "x₅" str
  strInRegex x₅ (← reInter (← reStar lower) (← reConcat (← reAll) (← reLit "q"))) >>= s.assert
  equal (← strLength x₅) (← mkInt 1) >>= s.assert
  -- "a" or "b", but not "a"
  let x₆ ← s.declareConst "x₆" str
  strInRegex x₆ (← reDiff (← reUnion (← reLit "a") (← reLit "b")) (← reLit "a")) >>= s.assert
  -- any two characters, the first "y" and the last "z"
  let x₇ ← s.declareConst "x₇" str
  strInRegex x₇ (← reConcat (← reAllChar) (← reAllChar)) >>= s.assert
  strPrefix (← lit "y") x₇ >>= s.assert
  strSuffix (← lit "z") x₇ >>= s.assert

  s.checkSat (ifSat := do
    let str (t : Term) : s.EnvSat String := do return repr (← s.getValueAs String t) |>.pretty
    println! "repeat, range  : {← str x₁}"
    println! "plus           : {← str x₂}"
    println! "concat, opt    : {← str x₃}"
    println! "loop           : {← str x₄}"
    println! "star, inter    : {← str x₅}"
    println! "union, diff    : {← str x₆}"
    println! "allChar        : {← str x₇}")

/-! Unsatisfiable memberships: the empty language, a language and its complement together, and a
ground membership that does not hold. -/

/-- info:
in re.none         : unsat
in R and in comp R : unsat
"aab" in b+        : unsat
-/
#guard_msgs in #eval Env.runIO do
  let str ← Srt.string
  let check (name : String) (f : Solver → Term → Env Unit) : Env Unit := do
    let s ← Solver.new
    let x ← s.declareConst "x" str
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

/-! The string operators that take a regex, evaluated on ground arguments. -/

/-- info:
indexofRe    : 2
replaceRe    : "a#b2"
replaceReAll : "a#b#"
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let digit ← reRange (← lit "0") (← lit "9")
  let bind (name : String) (srt : Srt) (value : Term) : Env Term := do
    let c ← s.declareConst name srt
    equal c value >>= s.assert
    return c
  let indexofRe ← bind "indexofRe" (← Srt.int)
    (← strIndexofRe (← lit "ab12cd") (← rePlus digit) (← mkInt 0))
  let replaceRe ← bind "replaceRe" (← Srt.string) (← strReplaceRe (← lit "a1b2") digit (← lit "#"))
  let replaceReAll ← bind "replaceReAll" (← Srt.string)
    (← strReplaceReAll (← lit "a1b2") digit (← lit "#"))

  s.checkSat (ifSat := do
    println! "indexofRe    : {← s.getValueAs Int indexofRe}"
    println! "replaceRe    : {repr (← s.getValueAs String replaceRe)}"
    println! "replaceReAll : {repr (← s.getValueAs String replaceReAll)}")

end solving


/-! # `regex!`

The usual regex notation, building the same terms as the constructors above. Printing pins what
each form expands to, precedence included; then a membership written with it is solved.
-/

section regexNotation
open Cvc.Untyped

/-- info:
literal  : (str.to_re "a.b")
any      : (re.++ (str.to_re "a") (re.++ re.allchar (str.to_re "b")))
class    : (re.union (re.range "a" "z") (str.to_re "_"))
negated  : (re.diff re.allchar (re.range "0" "9"))
postfix  : (re.++ (re.* (str.to_re "a")) (re.++ (re.+ (str.to_re "b")) (re.opt (str.to_re "c"))))
counts   : (re.++ ((_ re.^ 2) (str.to_re "ab")) ((_ re.loop 1 3) (str.to_re "c")))
union    : (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c"))))
inter    : (re.union (re.inter (re.* re.allchar) (re.comp (str.to_re "x"))) re.none)
diff     : (re.diff (re.+ (re.range "a" "z")) (str.to_re "if"))
in scope : (let ((_let_1 (re.+ (re.range "0" "9")))) (re.++ _let_1 (re.opt (re.++ (str.to_re ".") _let_1))))
escape   : (re.++ re.all (str.to_re "x"))
-/
#guard_msgs in #eval Env.runIO do
  -- a literal is Lean's string, so its dot is a dot; `.` alone is any character
  println! "literal  : {← regex! "a.b"}"
  println! "any      : {← regex! 'a' . 'b'}"
  println! "class    : {← regex! ['a'-'z' '_']}"
  println! "negated  : {← regex! [^ '0'-'9']}"
  println! "postfix  : {← regex! "a"* "b"+ "c"?}"
  println! "counts   : {← regex! "ab"{2} 'c'{1,3}}"
  -- postfix, then complement, then juxtaposition, then `∩`/`∖`, then `|`
  println! "union    : {← regex! "a" | "b" "c"*}"
  println! "inter    : {← regex! .* ∩ ¬ "x" | ∅}"
  println! "diff     : {← regex! ['a'-'z']+ ∖ "if"}"
  let digit ← regex! ['0'-'9']
  println! "in scope : {← regex! digit+ ("." digit+)?}"
  println! "escape   : {← regex! ![Term.reAll] "x"}"

/-! A decimal number written with `regex!`, solved: three characters with a dot, starting with 1 and
ending with 5, leave one string. -/

/-- info: number : "1.5" -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConst "x" (← Srt.string)
  let digit ← regex! ['0'-'9']
  Term.strInRegex x (← regex! digit+ ("." digit+)?) >>= s.assert
  Term.equal (← Term.strLength x) (← Term.mkInt 3) >>= s.assert
  Term.strContains x (← lit ".") >>= s.assert
  Term.strPrefix (← lit "1") x >>= s.assert
  Term.strSuffix (← lit "5") x >>= s.assert
  s.checkSat (ifSat := do println! "number : {repr (← s.getValueAs String x)}")

end regexNotation
