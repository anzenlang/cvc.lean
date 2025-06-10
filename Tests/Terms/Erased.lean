/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Defs
import Tests.Basic



namespace Cvc.Test


open scoped Cvc.Term.Dsl



def declareTerms : Smt ESymbols.ByName.Terms := do
  let mut syms := ESymbols.ByName.emptyIdents
  syms ← syms.insertIdent Bool "isCounting"
  syms ← syms.insertIdent Int "counter"
  syms.declare



Smt.test! [ETerm.basic1]
  let terms ← declareTerms

  let counter ← terms.get "counter" >>= (ETerm.as · Int)
  println! s!"counter term: {counter}"
  let counter ← terms.getAs Int "counter"
  println! s!"counter term again: {counter}"

  let iteTerm ← smt!
    if ?[ terms.get "isCounting" : Bool ]
    then ?[ terms.get "counter" : Int ] + 1 else 0
  println! "ite term: {iteTerm}"
/-- info:
counter term: counter
counter term again: counter
ite term: (ite isCounting (+ counter 1) 0)
-/



Smt.test! [ETerm.basic2]
  let terms ← declareTerms

  let counter ← terms.get "counter" >>= (ETerm.as · Int)
  println! s!"counter term: {counter}"
  let counter ← terms.getAs Int "counter"
  println! s!"counter term again: {counter}"

  let iteTerm ← smt!
    if ![ terms.getAs Bool "isCounting" ]
    then ![ terms.getAs Int "counter" ] + 1 else 0
  println! "ite term: {iteTerm}"
/-- info:
counter term: counter
counter term again: counter
ite term: (ite isCounting (+ counter 1) 0)
-/



Smt.test! [ETerm.bad1]
  let terms ← declareTerms
  let iteTerm ← smt!
    if ?[ terms.get "isCounting" : Bool ]
    then ?[ terms.get "isCounting" : Int ] + 1 else 0
  println! "ite term: {iteTerm}"
/-- info:
user error: erased term of type `Bool` cannot be typed as `Int`
--- error:
user error: erased term of type `Bool` cannot be typed as `Int`
-/



Smt.test! [ETerm.bad2]
  let terms ← declareTerms
  let iteTerm ← smt!
    if ![ terms.getAs Bool "isCounting" ]
    then ![ terms.getAs Int "isCounting" ] + 1 else 0
  println! "ite term: {iteTerm}"
/-- info:
user error: symbol `isCounting : Bool` cannot be typed as `Int`
--- error:
user error: symbol `isCounting : Bool` cannot be typed as `Int`
-/
