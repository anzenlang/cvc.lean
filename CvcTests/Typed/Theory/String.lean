/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.String
import Cvc.Typed.Core.Bool
import Cvc.Typed.Theory.Arith
import Cvc.Typed.Core.Solver

public meta import Cvc.Typed.Theory.String
public meta import Cvc.Typed.Core.Bool
public meta import Cvc.Typed.Theory.Arith
public meta import Cvc.Typed.Core.Solver



/-! # Generated String constructors, typed -/
namespace Cvc.Tests.Typed.Term.String

open Cvc
open Cvc.Typed.Term

/-- info:
contains  : (str.contains s t)
prefix    : (str.prefixof s t)
suffix    : (str.suffixof s t)
isDigit   : (str.is_digit s)
lt        : (str.< s t)
le        : (str.<= s t)
inRegex   : (str.in_re s re)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Cvc.Typed.Term.mkSymbolAs (String) "s"
  let t ← Cvc.Typed.Term.mkSymbolAs (String) "t"
  let re ← Cvc.Typed.Term.mkSymbolAs (Cvc.Regex) "re"

  println! "contains  : {← strContains s t}"
  println! "prefix    : {← strPrefix s t}"
  println! "suffix    : {← strSuffix s t}"
  println! "isDigit   : {← strIsDigit s}"
  println! "lt        : {← strLt s t}"
  println! "le        : {← strLe s t}"
  println! "inRegex   : {← strInRegex s re}"

/-! ## The rest of the theory -/

/-- info:
concat      : (str.++ s t)
length      : (str.len s)
substr      : (str.substr s i i)
charAt      : (str.at s i)
indexof     : (str.indexof s t i)
indexofRe   : (str.indexof_re s re i)
replace     : (str.replace s t s)
replaceAll  : (str.replace_all s t s)
replaceRe   : (str.replace_re s re t)
replaceReAll: (str.replace_re_all s re t)
rev         : (str.rev s)
update      : (str.update s i t)
toLower     : (str.to_lower s)
toUpper     : (str.to_upper s)
toCode      : (str.to_code s)
fromCode    : (str.from_code i)
toInt       : (str.to_int s)
fromInt     : (str.from_int i)
toRegex     : (str.to_re s)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs (Int) "i"
  let s ← Cvc.Typed.Term.mkSymbolAs (String) "s"
  let t ← Cvc.Typed.Term.mkSymbolAs (String) "t"
  let re ← Cvc.Typed.Term.mkSymbolAs (Cvc.Regex) "re"

  println! "concat      : {← strConcat s t}"
  println! "length      : {← strLength s}"
  println! "substr      : {← strSubstr s i i}"
  println! "charAt      : {← strCharAt s i}"
  println! "indexof     : {← strIndexof s t i}"
  println! "indexofRe   : {← strIndexofRe s re i}"
  println! "replace     : {← strReplace s t s}"
  println! "replaceAll  : {← strReplaceAll s t s}"
  println! "replaceRe   : {← strReplaceRe s re t}"
  println! "replaceReAll: {← strReplaceReAll s re t}"
  println! "rev         : {← strRev s}"
  println! "update      : {← strUpdate s i t}"
  println! "toLower     : {← strToLower s}"
  println! "toUpper     : {← strToUpper s}"
  println! "toCode      : {← strToCode s}"
  println! "fromCode    : {← strFromCode i}"
  println! "toInt       : {← strToInt s}"
  println! "fromInt     : {← strFromInt i}"
  println! "toRegex     : {← strToRegex s}"

/-! ## Constructors -/

/-- info:
mkString: "hi"
-/
#guard_msgs in #eval Env.runIO do
  println! "mkString: {← mkString "hi" false}"


/-! # The `smt!` DSL, string literals

These notations come from this theory's `op%` entries and are emitted beside its constructors, so
they exist exactly where the theory does. What the typed layer adds is the *index* the expansion
carries, pinned by the `example`s below.
-/

open Cvc.Typed in
/-- info:
string   : "hello"
-/
#guard_msgs in #eval Env.runIO do
  println! "string   : {← smt! "hello"}"



/-! # Solving

The same constraints as sort-erased. Here a model value comes back as the Lean type the term's index
says — a `String` or an `Int` — with no target type to name.
-/

section solving
open Cvc.Typed

/-- A literal string term, without escape sequences. -/
def lit [Ω] (s : String) : Env (Term String) := mkString s false

/-- info:
y        : " world"
len y    : 6
abc      : "abc"
digits   : "42"
in regex : "abc"
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let x ← s.declareConstAs String "x"
  let y ← s.declareConstAs String "y"
  let z ← s.declareConstAs String "z"
  let w ← s.declareConstAs String "w"
  let v ← s.declareConstAs String "v"

  equal (← strConcat x y) (← lit "hello world") >>= s.assert
  equal x (← lit "hello") >>= s.assert
  equal (← strLength z) (← mkInt 3) >>= s.assert
  strPrefix (← lit "ab") z >>= s.assert
  strSuffix (← lit "c") z >>= s.assert
  equal (← strToInt w) (← mkInt 42) >>= s.assert
  equal (← strLength w) (← mkInt 2) >>= s.assert
  strInRegex v (← strToRegex (← lit "abc")) >>= s.assert
  let lenY ← strLength y

  s.checkSat (ifSat := do
    -- no target type: `getValue` answers what the index says
    let vy ← s.getValue y
    let len ← s.getValue lenY
    println! "y        : {repr vy}"
    println! "len y    : {len}"
    println! "abc      : {repr (← s.getValue z)}"
    println! "digits   : {repr (← s.getValue w)}"
    println! "in regex : {repr (← s.getValue v)}")

/-- info:
contains, too short : unsat
b < x < a           : unsat
digit, not a digit  : unsat
-/
#guard_msgs in #eval Env.runIO do
  let check (name : String) (f : Solver → Term String → Env Unit) : Env Unit := do
    let s ← Solver.new
    let x ← s.declareConstAs String "x"
    f s x
    println! "{name} : {if ← s.checkIsSat then "sat" else "unsat"}"
  check "contains, too short" fun s x => do
    strContains x (← lit "abc") >>= s.assert
    lt (← strLength x) (← mkInt 3) >>= s.assert
  check "b < x < a          " fun s x => do
    strLt (← lit "b") x >>= s.assert
    strLt x (← lit "a") >>= s.assert
  check "digit, not a digit " fun s x => do
    strIsDigit x >>= s.assert
    equal (← strToInt x) (← mkInt (-1)) >>= s.assert

/-- info:
replace    : "a+b-c"
replaceAll : "a+b+c"
indexof    : 3
substr     : "ell"
charAt     : "e"
rev        : "cba"
update     : "jello"
toUpper    : "ABC"
toLower    : "abc"
toCode     : 65
fromCode   : "a"
fromInt    : "17"
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let bind {α : Type} [ToTyp α] (name : String) (value : Term α) : Env (Term α) := do
    let c ← s.declareConstAs α name
    equal c value >>= s.assert
    return c
  let replace ← bind "replace" (← strReplace (← lit "a-b-c") (← lit "-") (← lit "+"))
  let replaceAll ← bind "replaceAll" (← strReplaceAll (← lit "a-b-c") (← lit "-") (← lit "+"))
  let indexof ← bind "indexof" (← strIndexof (← lit "a-b-c") (← lit "-") (← mkInt 2))
  let substr ← bind "substr" (← strSubstr (← lit "hello") (← mkInt 1) (← mkInt 3))
  let charAt ← bind "charAt" (← strCharAt (← lit "hello") (← mkInt 1))
  let rev ← bind "rev" (← strRev (← lit "abc"))
  let update ← bind "update" (← strUpdate (← lit "hello") (← mkInt 0) (← lit "j"))
  let toUpper ← bind "toUpper" (← strToUpper (← lit "aBc"))
  let toLower ← bind "toLower" (← strToLower (← lit "aBc"))
  let toCode ← bind "toCode" (← strToCode (← lit "A"))
  let fromCode ← bind "fromCode" (← strFromCode (← mkInt 97))
  let fromInt ← bind "fromInt" (← strFromInt (← mkInt 17))

  s.checkSat (ifSat := do
    let str (t : Term String) : s.EnvSat String := do return repr (← s.getValue t) |>.pretty
    println! "replace    : {← str replace}"
    println! "replaceAll : {← str replaceAll}"
    println! "indexof    : {← s.getValue indexof}"
    println! "substr     : {← str substr}"
    println! "charAt     : {← str charAt}"
    println! "rev        : {← str rev}"
    println! "update     : {← str update}"
    println! "toUpper    : {← str toUpper}"
    println! "toLower    : {← str toLower}"
    println! "toCode     : {← s.getValue toCode}"
    println! "fromCode   : {← str fromCode}"
    println! "fromInt    : {← str fromInt}")

end solving
