/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Grammar
import Cvc.Untyped.Term

public meta import Cvc.Untyped.Grammar
public meta import Cvc.Untyped.Term



/-! # SyGuS grammars, sort-erased -/
namespace Cvc.Tests.Untyped.Grammar

open Cvc
open Cvc.Untyped



/-! ## Building a grammar

`toString` is the SyGuS pre-declaration followed by the rules, so it is a faithful picture of what
the grammar actually is.
-/

/-- info:
empty   : 
rules   : ((start Int) )((start Int (x 0 (+ start start))))
addRules: ((start Int) )((start Int (0 1 2)))
anyConst: ((start Int) )((start Int ((Constant Int) 0)))
anyVar   : ((start Int) )((start Int (x)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let x ← BVar.mk int "x"
  let start ← NT.mk int "start"

  -- a grammar with no rules yet prints as nothing at all, not even its pre-declaration
  println! "empty   : {← s.mkGrammar #[x] start}"

  -- a non-terminal coerces to a term, which is how it appears inside its own rules
  let g ← s.mkGrammar #[x] start
  let g ← g.addRule start x.toTerm
  let g ← g.addRule start (← Term.mkInt 0)
  let g ← g.addRule start (← Term.add start start)
  println! "rules   : {g}"

  let g ← s.mkGrammar #[] start
  let g ← g.addRules start #[← Term.mkInt 0, ← Term.mkInt 1, ← Term.mkInt 2]
  println! "addRules: {g}"

  println! "anyConst: {← (← s.mkGrammar #[] start).addAnyConstant start}"
  println! "anyVar   : {← (← s.mkGrammar #[x] start).addAnyVariable start}"

-- several non-terminals: the first is the start symbol, so order is meaningful
/-- info: ((start Int) (cnd Bool) )((start Int (0 (ite cnd start start)))(cnd Bool (true))) -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let start ← NT.mk (← Srt.int) "start"
  let cnd ← NT.mk (← Srt.bool) "cnd"

  let g ← s.mkGrammar #[] start #[cnd]
  let g ← g.addRule start (← Term.mkInt 0)
  let g ← g.addRule start (← Term.ite cnd start start)
  let g ← g.addRule cnd (← Term.mkTrue)
  println! "{g}"



/-! ## What is checked when

A non-terminal belongs to one grammar, and a rule must have its non-terminal's sort. Neither shows
in a signature at this layer, so both are caught when the rule is added.
-/

/-- info:
foreign nt : caught
wrong sort : caught
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let int ← Srt.int
  let start ← NT.mk int "start"
  let stranger ← NT.mk int "stranger"
  let g ← s.mkGrammar #[] start

  let caught (code : Env Cvc.Grammar) : Env String :=
    try let _ ← code ; pure "no error" catch _ => pure "caught"

  println! "foreign nt : {← caught (g.addRule stranger (← Term.mkInt 0))}"
  println! "wrong sort : {← caught (g.addRule start (← Term.mkTrue))}"

-- the start symbol is an argument of its own, not the head of an array. cvc5 takes the first
-- non-terminal as the start symbol and silently drops whatever is unreachable from it, so an array
-- would let a swapped order produce a grammar missing half its rules and no error at all
section discipline
variable [Ω] (s : Solver) (start cnd : NT)

/-- A grammar always has a start symbol; there is no empty case to reject. -/
example : Env Cvc.Grammar := s.mkGrammar #[] start

/-- Auxiliary non-terminals are separate, and cannot be mistaken for the start symbol. -/
example : Env Cvc.Grammar := s.mkGrammar #[] start #[cnd]

/-- info: @Solver.mkGrammar : [inst : Ω] → Solver → BVars → NT → optParam NTs #[] → Env Grammar -/
#guard_msgs in #check @Cvc.Untyped.Solver.mkGrammar

end discipline
