/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Theory.Seq
import Cvc.Untyped.Core.Bool

public meta import Cvc.Untyped.Theory.Seq
public meta import Cvc.Untyped.Core.Bool



/-! # Generated Seq constructors, sort-erased -/
namespace Cvc.Tests.Untyped.Term.Seq

open Cvc
open Cvc.Untyped.Term

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
  let i ← Cvc.Untyped.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Untyped.Term.mkSymbolAs (Int) "j"
  let q ← Cvc.Untyped.Term.mkSymbolAs (Array Int) "q"
  let r ← Cvc.Untyped.Term.mkSymbolAs (Array Int) "r"

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
  println! "mkEmptySeq : {← Srt.of Int >>= mkEmptySeq}"
