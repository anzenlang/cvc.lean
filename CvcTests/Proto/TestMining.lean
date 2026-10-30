/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed
public import Cvc.Typed.Extra.Sys
public import CvcTests.Proto.Mining
public import Cvc.Typed.Synth
public meta import Cvc.Typed
public meta import Cvc.Typed.Extra.Sys
public meta import CvcTests.Proto.Mining



namespace Cvc.Test.Proto.Mining.Test open Cvc Typed variable [Ω]

/-

# S1

I | `x = 0 ∧ y = 0`
T | `(x' = x + 1 ∧ y' = y + 2) ∨ (x' = x - 2 ∧ y' = y - 1)`
P | `x + y ≠ 2`
S | `(x + y) % 3 = 0`

state variables: `x : Int`, `y : Int`
- init: `x = 0 ∧ y = 0`
- next: `(x' = x + 1 ∧ y' = y + 2) ∨ (x' = x - 2 ∧ y' = y - 1)`
- property: `x + y ≠ 2`
- strengthening invariant: `(x + y) % 3 = 0`

# S2

I | `x = 0 ∧ y = 0`
T | `x' = x + y ∧ y' = y + 1`
P | `0 ≤ x`
S | `0 ≤ y`

-/

structure.symbols Vars where
  x : Int
  y : Int

abbrev Sys := Typed.Sys Vars



namespace S1

def property : Vars.PredAt' := fun {x, y} => smt! x + y ≠ 2

def s1 : Sys where
  idents := Vars.idents
  init := fun {x, y} => smt! x = 0 ∧ y = 0
  next := fun {x, y} {x := x', y := y'} =>
    smt! (x' = x + 1 ∧ y' = y + 2) ∨ (x' = x - 2 ∧ y' = y - 1)
  candidates := #[ ("P1", property) ]


def infer [Ω] : Env (Option (Term (Int → Int → Bool))) := do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let sv0 ← s1.idents.declareSygusAtIn 0 s
  let init_0 ← s1.init sv0
  let sv1 ← s1.idents.declareSygusAtIn 1 s
  let next_0_1 ← s1.next sv0 sv1
  let p_1 ← property sv1

  let mut miner := Miner.empty
  miner ← miner.addTypedSymbols s1.idents
  miner ← miner.scanTypedTerm init_0
  miner ← miner.scanTypedTerm next_0_1
  miner ← miner.scanTypedTerm p_1
  let int_mod ← smt! sv1.x % sv1.y = 3
  miner ← miner.scanTypedTerm int_mod

  let some g ← miner.extractTypedGrammar (Int → Int → Bool)
    | throwInternal "failed to extract grammar"
  println! "grammar:\n{g}\n"
  let str ← s.synthFun "STR" g
  let str_0 ← str.apply2 sv0.x.get sv0.y.get
  let str_1 ← str.apply2 sv1.x.get sv1.y.get

  let c1 ← init_0.implies str_0
  -- println! "c1: {c1}"
  s.addSygusConstraint c1
  let c2 ← (← str_0.and next_0_1).implies str_1
  -- println! "c1: {c2}"
  s.addSygusConstraint c2
  let c3 ← str_1.implies p_1
  -- println! "c1: {c3}"
  s.addSygusConstraint c3

  s.checkSynth? (ifSolved := do return (← some <$> s.getSynthSolution str))

/--
info:
grammar:
((miner_NT_for__Bool Bool) (miner_NT_for__Int Int) )((miner_NT_for__Bool Bool ((and miner_NT_for__Bool miner_NT_for__Bool) (= miner_NT_for__Int miner_NT_for__Int) (or miner_NT_for__Bool miner_NT_for__Bool) (distinct miner_NT_for__Int miner_NT_for__Int)))(miner_NT_for__Int Int (x y 0 (- miner_NT_for__Int miner_NT_for__Int) 1 2 (+ miner_NT_for__Int miner_NT_for__Int) 3 (mod miner_NT_for__Int miner_NT_for__Int))))

strengthening invariant: (lambda ((x Int) (y Int)) (= 0 (mod (+ x y) 3)))
-/
#guard_msgs in #eval Env.runIO do
  match ← infer with
  | none => println! "no strengthening invariant found"
  | some inv => println! "strengthening invariant: {inv}"

end S1



namespace S2

def property : Vars.PredAt' := fun {x, ..} => smt! 0 ≤ x

def s2 : Sys where
  idents := Vars.idents
  init := fun {x, y} => smt! x = 0 ∧ y = 0
  next := fun {x, y} {x := x', y := y'} => smt! x' = x + y ∧ y' = y + 1
  candidates := #[ ("P2", property) ]


def infer [Ω] : Env (Option (Term (Int → Int → Bool))) := do
  let s ← Solver.new
  s.setOption "sygus" "true"
  let sv0 ← s2.idents.declareAt 0
  let init_0 ← s2.init sv0
  let sv1 ← s2.idents.declareAt 1
  let sv2 ← s2.idents.declareAt 2
  let next_1_2 ← s2.next sv1 sv2
  let p_2 ← property sv2

  let mut miner := Miner.empty
  miner ← miner.addTypedSymbols s2.idents
  miner ← miner.scanTypedTerm init_0
  miner ← miner.scanTypedTerm next_1_2
  miner ← miner.scanTypedTerm p_2

  let some g ← miner.extractTypedGrammar (Int → Int → Bool)
    | throwInternal "failed to extract grammar"
  println! "grammar:\n{g}\n"
  let str ← s.synthFun "STR" g
  let str_0 ← str.apply2 sv0.x sv0.y
  let str_1 ← str.apply2 sv1.x sv1.y
  let str_2 ← str.apply2 sv2.x sv2.y

  init_0.implies str_0 >>= s.addSygusConstraint
  (← str_1.and next_1_2).implies str_2 >>= s.addSygusConstraint
  str_2.implies p_2 >>= s.addSygusConstraint

  s.checkSynth? (ifSolved := do return (← some <$> s.getSynthSolution str))

/--
info:
grammar:
((miner_NT_for__Bool Bool) (miner_NT_for__Int Int) )((miner_NT_for__Bool Bool ((and miner_NT_for__Bool miner_NT_for__Bool) (= miner_NT_for__Int miner_NT_for__Int) (<= miner_NT_for__Int miner_NT_for__Int)))(miner_NT_for__Int Int (x y 0 (+ miner_NT_for__Int miner_NT_for__Int) 1)))

strengthening invariant: (lambda ((x Int) (y Int)) (and (<= 0 x) (<= 0 y)))
-/
#guard_msgs in #eval Env.runIO do
  match ← infer with
  | none => println! "no strengthening invariant found"
  | some inv => println! "strengthening invariant: {inv}"




-- namespace Sw

-- structure.stateVars Vars where
--   count : Int
--   counting : Bool
--   startStop : Bool
--   reset : Bool

-- abbrev Sys := Typed.Sys Vars

-- def sw.property : SVars.Pred (S := Vars) := fun vars =>
--   smt! vars.count ≠ -7

-- def sw : Sys where
--   idents := Vars.idents
--   init := fun vars => smt! 0 ≤ vars.count ∧ vars.counting = vars.startStop
--   next := fun vars vars' =>
--     smt! vars'.counting = if vars'.startStop then ¬ vars.counting else vars.counting
--       ∧ vars'.count = if vars'.reset then 0 else vars.count + (if vars'.counting then 1 else 0)
--   candidates := #[ ("P", sw.property) ]


-- def infer [Ω] : Env (Option (Term (Int → Bool → Bool → Bool → Bool))) := do
--   let bool ← Srt.bool
--   let s ← Solver.new
--   s.setOption "sygus" "true"
--   s.setOption "tlimit-per" "5000"
--   let sv0 ← sw.idents.declareAt 0
--   let init_0 ← sw.init sv0
--   let sv1 ← sw.idents.declareAt 1
--   let next_0_1 ← sw.next sv0 sv1
--   let p_1 ← sw.property sv1

--   let mut miner := Miner.empty
--   println! "add typed symbols"
--   miner ← miner.addTypedSymbols sw.idents
--   miner ← miner.scanTypedTerm init_0
--   miner ← miner.scanTypedTerm next_0_1
--   miner ← miner.scanTypedTerm p_1

--   println! "about to extract grammar"
--   println! "- bVars"
--   for bVar in miner.bVars do
--     println! "  → {bVar}"
--   for (sort, (nt, rules)) in miner.sortedNTs do
--     println! "- {nt} : {sort}"
--     for rule in rules do
--       println! "  → {rule}"

--   let some g ← miner.extractGrammarFor bool
--     | throwInternal "failed to extract grammar"
--   let s := s.relax
--   let str ← s.synthFun "STR" miner.bVars bool g
--   let str_0 ← str.apply4 sv0.count.relax sv0.counting.relax sv0.startStop.relax sv0.reset.relax
--   let str_1 ← str.apply4 sv1.count.relax sv1.counting.relax sv1.startStop.relax sv1.reset.relax
--   -- let str_2 ← str.apply4 sv2.count.relax sv2.counting.relax sv2.startStop.relax sv2.reset.relax

--   init_0.relax.implies str_0 >>= s.addSygusConstraint
--   (← str_1.and next_0_1.relax).implies str_1 >>= s.addSygusConstraint
--   str_1.implies p_1.relax >>= s.addSygusConstraint

--   let str? ← s.checkSynth? (ifSolved := do return (← some <$> s.getSynthSolution str))
--   str?.mapM fun str => str.typeCheckAs (Int → Bool → Bool → Bool → Bool)

-- #eval Env.runIO do
--   match ← infer with
--   | none => println! "no strengthening invariant found"
--   | some inv => println! "strengthening invariant: {inv}"

end S2
