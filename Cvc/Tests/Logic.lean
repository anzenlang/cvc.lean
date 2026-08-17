/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Logic
import Cvc.Typed.Core
import Cvc.Typed.Theory
import Cvc.Typed.Solver

public meta import Cvc.Logic
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory
public meta import Cvc.Typed.Solver



/-! # SMT-LIB logic names

`ALL` is a special case in both directions: the printer stops after it and the parser recognises it
whole. The prefixes that may still precede it are `HO_` and `QF_`, so `HO_ALL`, `QF_ALL` and
`HO_QF_ALL` are legal and have to be handled on both sides — printing them in that order, and
parsing them ahead of the bare `ALL`.

`HO_` is not cosmetic. cvc5 refuses a **function-sorted term** outside a higher-order logic, and a
partial application produces one, so anything built by applying a multi-argument function to fewer
arguments than its arity needs it. The last test here is that consequence end to end.
-/
namespace Cvc.Tests.Logic

open Cvc
open Cvc
open Cvc.Typed (Term Solver)
open Cvc.Typed.Term



/-! ## Printing, and round-tripping through the parser

Each line is the SMT-LIB name a logic prints as, then that name parsed back and printed again. The
two agreeing is what says the parser accepts everything the printer emits.
-/

/-- info:
ALL       → ALL
HO_ALL    → HO_ALL
QF_ALL    → QF_ALL
HO_QF_ALL → HO_QF_ALL
LIA       → LIA
QF_LIA    → QF_LIA
HO_LIA    → HO_LIA
HO_QF_LIA → HO_QF_LIA
-/
#guard_msgs in #eval do
  let roundTrip (label : String) (l : Cvc.Logic) : IO Unit := do
    let printed := l.toSmtLib
    match Cvc.Logic.ofSmtLib printed with
    | .ok back => println! "{label} → {back.toSmtLib}"
    | .error e => println! "{label} → PARSE ERROR {e}"

  -- `ALL` and the two prefixes it admits
  roundTrip "ALL      " Cvc.Logic.all
  roundTrip "HO_ALL   " Cvc.Logic.all.ho
  roundTrip "QF_ALL   " Cvc.Logic.all.qf
  roundTrip "HO_QF_ALL" Cvc.Logic.all.ho.qf
  -- an ordinary logic takes the same prefixes, and must not have regressed
  roundTrip "LIA      " Cvc.Logic.lia.toLogic
  roundTrip "QF_LIA   " Cvc.Logic.qf_lia.toLogic
  roundTrip "HO_LIA   " Cvc.Logic.lia.ho.toLogic
  roundTrip "HO_QF_LIA" Cvc.Logic.qf_lia.ho.toLogic

/-! The prefixes print in a fixed order — `HO_` before `QF_` — whichever order they were added in.
-/

/-- info:
all.ho.qf : HO_QF_ALL
all.qf.ho : HO_QF_ALL
-/
#guard_msgs in #eval do
  println! "all.ho.qf : {Cvc.Logic.all.ho.qf.toSmtLib}"
  println! "all.qf.ho : {Cvc.Logic.all.qf.ho.toSmtLib}"

/-! Parsing accepts what cvc5 writes and rejects what it does not.

Trailing input is the case worth pinning: `ALL` and its prefixed forms are matched whole, so
nothing may follow them. That has to be checked separately from the ordinary path, which reaches
the end-of-input check by a different route.
-/

/-- info:
ALL         : ok ALL
HO_ALL      : ok HO_ALL
QF_ALL      : ok QF_ALL
HO_QF_ALL   : ok HO_QF_ALL
ALLX        : error
HO_ALLX     : error
QF_ALLZZ    : error
HO_QF_ALL!! : error
LIAX        : error
QF_LIAX     : error
NOPE        : error
-/
#guard_msgs in #eval do
  let parse (label input : String) : IO Unit := do
    match Cvc.Logic.ofSmtLib input with
    | .ok l => println! "{label} : ok {l.toSmtLib}"
    | .error _ => println! "{label} : error"

  -- the whole `ALL` family parses
  parse "ALL        " "ALL"
  parse "HO_ALL     " "HO_ALL"
  parse "QF_ALL     " "QF_ALL"
  parse "HO_QF_ALL  " "HO_QF_ALL"
  -- and nothing may follow it: these matched and discarded the tail before
  parse "ALLX       " "ALLX"
  parse "HO_ALLX    " "HO_ALLX"
  parse "QF_ALLZZ   " "QF_ALLZZ"
  parse "HO_QF_ALL!!" "HO_QF_ALL!!"
  -- the ordinary path rejects a tail too, by its own end-of-input check
  parse "LIAX       " "LIAX"
  parse "QF_LIAX    " "QF_LIAX"
  -- and a name that is no logic at all
  parse "NOPE       " "NOPE"

/-! A bare prefix, and the empty string, still parse — every component of the ordinary path is
optional, so nothing forces a logic to name a theory. Pinned as current behaviour rather than as
something desirable; whether these should be rejected is a separate question.
-/

/-- info:
HO_ : ok HO_
QF_ : ok QF_
""  : ok
-/
#guard_msgs in #eval do
  let parse (label input : String) : IO Unit := do
    match Cvc.Logic.ofSmtLib input with
    | .ok l => println! "{label} : ok {l.toSmtLib}"
    | .error _ => println! "{label} : error"
  parse "HO_" "HO_"
  parse "QF_" "QF_"
  parse "\"\" " ""

/-! ## The solver agrees

`setLogic` sends the printed name, so `getLogicString` reading it back is the printer checked
against cvc5 rather than against itself.
-/

/-- info:
ALL       → ALL
HO_ALL    → HO_ALL
QF_ALL    → QF_ALL
HO_QF_ALL → HO_QF_ALL
-/
#guard_msgs in #eval Env.runIO do
  let roundTrip (label : String) (l : Cvc.Logic) : Env Unit := do
    let s ← Solver.new
    s.setLogic l
    println! "{label} → {← s.getLogicString}"
  roundTrip "ALL      " Cvc.Logic.all
  roundTrip "HO_ALL   " Cvc.Logic.all.ho
  roundTrip "QF_ALL   " Cvc.Logic.all.qf
  roundTrip "HO_QF_ALL" Cvc.Logic.all.ho.qf



/-! ## What `HO_` buys

`APPLY_UF` application no longer needs it: the constructors flatten, so applying an already-applied
term appends to its children and no function-sorted intermediate is ever built. `applyHo` is the
one that still does — it is `HO_APPLY`, consumes a single argument whatever the arity, and so
*does* produce a partially applied, function-sorted term.
-/

/-- info:
default : ERR [internal] Function terms are only supported with higher-order logic. Try adding the logic prefix HO_.
ALL     : ERR [internal] Function terms are only supported with higher-order logic. Try adding the logic prefix HO_.
HO_ALL  : sat
-/
#guard_msgs in #eval Env.runIO do
  let attempt (logic : Option Cvc.Logic) : Env String := do
    let s ← Solver.new
    if let some l := logic then s.setLogic l
    let f ← s.declareFun (α := Int → Bool → Int) "f"
    let i ← s.declareConst Int "i"
    let b ← s.declareConst Bool "b"
    try
      -- one argument at a time, so `applyHo f i` is function-sorted
      let applied ← applyHo (← applyHo f i) b
      (do equal applied (← mkInt 1)) >>= s.assert
      pure (if ← s.checkIsSat then "sat" else "unsat")
    catch e => pure s!"ERR {e}"

  println! "default : {← attempt none}"
  println! "ALL     : {← attempt (some Cvc.Logic.all)}"
  println! "HO_ALL  : {← attempt (some Cvc.Logic.all.ho)}"

/-! The `APPLY_UF` spellings need none of that, however they are reached — one flat term either
way, so they solve under the default logic.
-/

/-- info:
applyN     : sat
coe chain  : sat
-/
#guard_msgs in #eval Env.runIO do
  let attempt (build : Term (Int → Bool → Int) → Term Int → Term Bool → Env (Term Int))
  : Env String := do
    let s ← Solver.new
    let f ← s.declareFun (α := Int → Bool → Int) "f"
    let i ← s.declareConst Int "i"
    let b ← s.declareConst Bool "b"
    (do equal (← build f i b) (← mkInt 1)) >>= s.assert
    pure (if ← s.checkIsSat then "sat" else "unsat")

  println! "applyN     : {← attempt fun f i b => applyN f (.cons i (.last b))}"
  println! "coe chain  : {← attempt fun f i b => f i b}"
