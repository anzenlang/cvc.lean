/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Term.String
import Cvc.Typed.Term.Bool

public meta import Cvc.Typed.Term.String
public meta import Cvc.Typed.Term.Bool



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
