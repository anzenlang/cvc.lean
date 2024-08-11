/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Term



/-! # Interactions with the solver: SMT-LIB(-like) commands -/
namespace Cvc.Smt



/-! ## Solver commands -/

open cvc5 (Solver)

variable [Monad m]



@[inherit_doc Solver.parse]
def parseSmtLib (smtLib : String) : SmtT m Unit :=
  Solver.parse (m := m) smtLib



/-! ### Getters -/

@[inherit_doc Solver.getVersion]
def getVersion : SmtT m String :=
  Solver.getVersion (m := m)

/-! ### Setters -/

@[inherit_doc Solver.setOption]
def setOption (key val : String) : SmtT m Unit :=
  Solver.setOption (m := m) key val

@[inherit_doc Solver.setLogic]
def setLogic (logic : Logic) : SmtT m Unit :=
  Solver.setLogic (m := m) logic.toSmtLib

/-! ### Declare/define -/


@[inherit_doc Solver.declareFun]
def declareFun' (symbol : String) (sorts : Array Srt) (codomain : Srt) : SmtT m Term :=
  ULift.up <$> Solver.declareFun symbol (sorts.map ULift.down) codomain.down false (m := m)

@[inherit_doc Solver.declareFun]
def declareFun (symbol : String) (α : Type) [A : ToSrt α] : SmtT m Term := do
  let a ← A.srt
  let (domain, codomain) ← a.cvc5Signature
  ULift.up <$> Solver.declareFun symbol domain codomain false (m := m)

@[inherit_doc Solver.declareSort]
def declareSort (symbol : String) (arity : Nat) : SmtT m Srt :=
  ULift.up <$> Solver.declareSort symbol arity false (m := m)

/-! ### Assert-like -/

@[inherit_doc Solver.assertFormula]
def assert (formula : Term) : SmtT m Unit :=
  Solver.assertFormula (m := m) formula.down

/-! ### Check-sat-like -/

-- @[inherit_doc Solver.checkSat]
def checkSat : SmtT m cvc5.Result :=
  Solver.checkSat (m := m)

/-- True if *sat*, false if *unsat*, none if *unknown*, error otherwise. -/
def checkSat? : SmtT m (Option Bool) := do
  let res ← checkSat
  if res.isSat then
    return true
  else if res.isUnsat then
    return false
  else if res.isUnknown then
    return none
  else
    SmtT.throwInternal "checkSat result is none of *sat*, *unsat*, and *unknown*"

/-! ### Sat mode commands -/



/-! ### Unsat mode commands -/

-- @[inherit_doc Solver.getProof]
def getProof : SmtT m (Array cvc5.Proof) :=
  Solver.getProof (m := m)

end Smt
