/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Seq
import Cvc.Typed.Core.Bool

public meta import Cvc.Typed.Theory.Seq
public meta import Cvc.Typed.Core.Bool



/-! # Generated Seq constructors, typed -/
namespace Cvc.Tests.Typed.Term.Seq

open Cvc
open Cvc.Typed.Term

/-- info:
unit      : (seq.unit i)
concat    : (seq.++ q r)
concatN   : (seq.++ q r q)
length    : (seq.len q)
at        : (seq.at q i)
nth       : (seq.nth q i)
extract   : (seq.extract q i j)
update    : (seq.update q i r)
indexof   : (seq.indexof q r i)
replace   : (seq.replace q r q)
replaceAll: (seq.replace_all q r q)
rev       : (seq.rev q)
contains  : (seq.contains q r)
prefix    : (seq.prefixof q r)
suffix    : (seq.suffixof q r)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Typed.Term.mkSymbolAs (Int) "j"
  let q ← Cvc.Typed.Term.mkSymbolAs (Array Int) "q"
  let r ← Cvc.Typed.Term.mkSymbolAs (Array Int) "r"

  println! "unit      : {← seqUnit i}"
  println! "concat    : {← seqConcat q r}"
  println! "concatN   : {← seqConcatN #[q, r, q]}"
  println! "length    : {← seqLength q}"
  println! "at        : {← seqAt q i}"
  println! "nth       : {← seqNth q i}"
  println! "extract   : {← seqExtract q i j}"
  println! "update    : {← seqUpdate q i r}"
  println! "indexof   : {← seqIndexof q r i}"
  println! "replace   : {← seqReplace q r q}"
  println! "replaceAll: {← seqReplaceAll q r q}"
  println! "rev       : {← seqRev q}"
  println! "contains  : {← seqContains q r}"
  println! "prefix    : {← seqPrefix q r}"
  println! "suffix    : {← seqSuffix q r}"

/-! ## Constructors

`mkEmptySequence` takes the sequence's *element* sort, which the typed layer supplies from the
index and the sort-erased one is given directly.
-/

/-- info: mkEmptySeq : (as seq.empty (Seq Int)) -/
#guard_msgs in #eval Env.runIO do
  println! "mkEmptySeq : {← (mkEmptySeq : Env (Cvc.Typed.Term (Array Int)))}"
