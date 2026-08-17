/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Theory.Bag
import Cvc.Typed.Core.Bool

public meta import Cvc.Typed.Theory.Bag
public meta import Cvc.Typed.Core.Bool



/-! # Generated Bag constructors, typed -/
namespace Cvc.Tests.Typed.Term.Bag

open Cvc
open Cvc.Typed.Term

/-- info:
member    : (bag.member i b)
subbag    : (bag.subbag b c)
make      : (bag i j)
count     : (bag.count i b)
card      : (bag.card b)
setof     : (bag.setof b)
choose    : (bag.choose b)
unionMax  : (bag.union_max b c)
unionDisj : (bag.union_disjoint b c)
interMin  : (bag.inter_min b c)
diffSub   : (bag.difference_subtract b c)
diffRemove: (bag.difference_remove b c)
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Typed.Term.mkSymbolAs (Int) "i"
  let j ← Cvc.Typed.Term.mkSymbolAs (Int) "j"
  let b ← Cvc.Typed.Term.mkSymbolAs (Cvc.Bag Int) "b"
  let c ← Cvc.Typed.Term.mkSymbolAs (Cvc.Bag Int) "c"

  println! "member    : {← bagMember i b}"
  println! "subbag    : {← bagSubbag b c}"
  println! "make      : {← bagMake i j}"
  println! "count     : {← bagCount i b}"
  println! "card      : {← bagCard b}"
  println! "setof     : {← bagSetof b}"
  println! "choose    : {← bagChoose b}"
  println! "unionMax  : {← bagUnionMax b c}"
  println! "unionDisj : {← bagUnionDisjoint b c}"
  println! "interMin  : {← bagInterMin b c}"
  println! "diffSub   : {← bagDifferenceSubtract b c}"
  println! "diffRemove: {← bagDifferenceRemove b c}"

/-! ## Higher-order operators -/

/-- info:
map   : (bag.map m b)
filter: (bag.filter p b)
fold  : (bag.fold acc z b)
all   : (bag.all p b)
some  : (bag.some p b)
partition: (bag.partition eq b)
-/
#guard_msgs in #eval Env.runIO do
  let p ← Cvc.Typed.Term.mkSymbolAs ((Int → Bool)) "p"
  let m ← Cvc.Typed.Term.mkSymbolAs ((Int → Int)) "m"
  let acc ← Cvc.Typed.Term.mkSymbolAs ((Int → Int → Int)) "acc"
  let eq ← Cvc.Typed.Term.mkSymbolAs ((Int → Int → Bool)) "eq"
  let z ← Cvc.Typed.Term.mkSymbolAs (Int) "z"
  let b ← Cvc.Typed.Term.mkSymbolAs (Cvc.Bag Int) "b"

  println! "map   : {← bagMap m b}"
  println! "filter: {← bagFilter p b}"
  println! "fold  : {← bagFold acc z b}"
  println! "all   : {← bagAll p b}"
  println! "some  : {← bagSome p b}"
  println! "partition: {← bagPartition eq b}"

/-! ## Constants

The sort-erased constructor takes the sort it builds; the typed one recovers it from its index.
-/

/-- info:
empty    : (as bag.empty (Bag Int))
-/
#guard_msgs in #eval Env.runIO do
  println! "empty    : {← (bagEmpty : Env (Cvc.Typed.Term (Cvc.Bag Int)))}"
