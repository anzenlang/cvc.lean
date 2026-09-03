/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Typed.Extra.SVars



namespace Cvc.Typed public section variable [Ω]

namespace SVars

abbrev Candidates [sv : SVars S] := Array (String × sv.Pred)

end SVars

namespace Sys

inductive Trace (α : Nat → Type) : (k : Nat) → Type
| zero : α 0 → Trace α 0
| cons : α (k + 1) → Trace α k → Trace α (k + 1)

namespace Trace

def iterM [Monad m] (f : {k : Nat} → α k → m Unit) : Trace α k → m Unit
| zero val => f val
| cons val tl => do tl.iterM f ; f val

def getCurrent : Trace α k → α k
| zero val => val
| cons val _ => val

def getZero : Trace α k → α 0
| zero val => val
| cons _ tl => tl.getZero

end Trace

end Sys

namespace SVars variable [sv : SVars S]

abbrev TermTrace := Sys.Trace (sv.TermsAt)

abbrev Cex := Sys.Trace (sv.ValuesAt)

namespace Cex

def extract {s : Solver} : sv.TermTrace k → s.EnvSat (sv.Cex k)
| .zero terms => .zero <$> terms.getValues s
| .cons terms tl => do
  let values ← terms.getValues s
  .cons values <$> extract tl

end Cex

namespace TermTrace

def getCex := @Cex.extract

end TermTrace

end SVars



structure Sys (S : SVars.Sig) [sv : SVars S] where
  idents : sv.Idents
  init : sv.Pred
  next : sv.Rel
  candidates : Array (String × sv.Pred)

abbrev SVars.Sys := @Typed.Sys

namespace Sys variable [sv : SVars S] (sys : sv.Sys) (solver : Solver)

def initAt (solver : Solver) (k : Nat) : Env (Term Bool) := do
  let svs_k ← solver.declareSymbolsAt k sys.idents
  sys.init svs_k

def nextAt (curr : sv.TermsAt k) (next : sv.TermsAt k') : Env (Term Bool) := do
  sys.next curr next



structure Bmc (S : SVars.Sig) [sv : SVars S] (k : Nat) extends sv.Sys where
private mk' ::
  solver : Solver
  sVars : sv.TermTrace k
  falsified : List ((k : Nat) × sv.Cex k × Array String)
  actlitCounter : Nat

abbrev _root_.Cvc.Typed.SVars.Bmc := @Cvc.Typed.Sys.Bmc

namespace Bmc variable [sv : SVars S] {k : Nat}

def mk (sys : sv.Sys) : Env (sv.Bmc S 0) := do
  let sVars0 ← sys.idents.declareAt 0
  let init0 ← sys.init sVars0
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  solver.assert init0
  return { toSys := sys, solver, falsified := [], sVars := Trace.zero sVars0, actlitCounter := 0 }

def isDone (bmc : sv.Bmc S k) : Bool := bmc.candidates.isEmpty

def check (bmc : sv.Bmc S k) : Env (Option <| Array String × sv.Bmc S k) := do
  if bmc.isDone then return none
  let state := bmc.sVars.getCurrent
  let candidates ← bmc.candidates.mapM fun (name, pred) => return (name, ← pred state)
  let orArgs ← bmc.candidates.mapM (fun (_, pred) => pred state >>= Term.not)
  let assuming ← Term.orN' orArgs
  let satRes? ← bmc.solver.checkSat? #[assuming]
    (ifSat := do
      let falsified ← candidates.filterMapM fun (name, pred) => do
        let isTrue ← bmc.solver.getValue pred
        if isTrue then return none else return some name
      let cex ← bmc.sVars.getCex
      return some (falsified, cex))
  if let some (falsifiedCandidates, cex) := satRes? then
    let candidates := bmc.candidates.filter fun (name, _) => name ∉ falsifiedCandidates
    let falsified := ⟨k, cex, falsifiedCandidates⟩ :: bmc.falsified
    return some (falsifiedCandidates, {bmc with candidates, falsified})
  else return none

def unroll (bmc : sv.Bmc S k) : Env (sv.Bmc S k.succ) := do
  let nextState ← bmc.idents.declareAt k.succ
  let next ← bmc.next bmc.sVars.getCurrent nextState
  -- println! "asserting {next}"
  bmc.solver.assert next
  return { bmc with sVars := .cons nextState bmc.sVars }

end Bmc


end Sys
