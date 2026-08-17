/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Regex
import Cvc.Untyped.Core.Bool

public meta import Cvc.Untyped.Theory.Regex
public meta import Cvc.Untyped.Core.Bool



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
