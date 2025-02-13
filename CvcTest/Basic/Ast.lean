/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Basic.Init



namespace Cvc.Test



open Smt

def getTerm : SmtIO Term := do
  let n ← declareFun "n" Int
  assertEq n.getSrt.toString "Int"

  let f ← declareFun "f" (Int → Int → Bool)
  assertEq f.getSrt.toString "(-> Int Int Bool)"

  let seven ← Term.mkInt 7
  let app ← f.apply #[n, seven]
  let term ← (← Term.mkBool false).and app
  return term

/-- info:
term = (and false (f n 7))
- ast = .and #[false, (f n 7)]

traversing
- inspectDown (and false (f n 7))
- inspectDown false
- leafDo false
- inspectDown (f n 7)
- inspectDown f
- leafDo f
- inspectDown n
- leafDo n
- inspectDown 7
- leafDo 7
- goUp (f n 7)
- goUp (and false (f n 7))
-/
test! do
  let term ← getTerm

  println! "term = {term}"
  match ← term.toAst with
  | .and kids => println! "- ast = .and {kids}"
  | _ => IO.throwServerError "unexpected ast"
  println! ""

  println! "traversing"
  term.traverse
    (inspectDown := fun term _ast => do
      println! "- inspectDown {term}"
      return .down)
    (leafDo := fun term _leaf => do
      println! "- leafDo {term}"
      return .up ())
    (goUp := fun term _res => do
      println! "- goUp {term}"
      return .up ())

/-- info:
bottom-up for-traversal (and false (f n 7))
- false
- f
- n
- 7
- (f n 7)
- (and false (f n 7))
-/
test! do
  let term ← getTerm
  println! "bottom-up for-traversal {term}"
  for sub in term.iterUp do
    println! "- {sub}"

/-- info:
top-down for-traversal (and false (f n 7))
- (and false (f n 7))
- false
- (f n 7)
- f
- n
- 7
-/
test! do
  let term ← getTerm
  println! ""
  println! "top-down for-traversal {term}"
  for sub in term.iterDown do
    println! "- {sub}"

/-- info:
2 free symbol(s) (and false (f n 7))
- `n` | n
- `f` | f
-/
test! do
  let term ← getTerm
  println! ""
  let freeSyms ← term.freeSyms
  println! "{freeSyms.size} free symbol(s) {term}"
  for (term, symbol) in freeSyms do
    println! "- `{symbol}` | {term}"
