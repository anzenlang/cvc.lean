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
def parseSmtLib (smtLib : String) : SmtM Unit :=
  Solver.parse (m := Id) smtLib



/-! ### Getters -/

@[inherit_doc Solver.getVersion]
def getVersion : SmtM String :=
  Solver.getVersion (m := Id)

/-! ### Setters -/

@[inherit_doc Solver.setOption]
def setOption (key val : String) : SmtM Unit :=
  Solver.setOption (m := Id) key val

@[inherit_doc Solver.setLogic]
def setLogic (logic : Logic) : SmtM Unit :=
  Solver.setLogic (m := Id) logic.toSmtLib

/-! ### Declare/define -/


@[inherit_doc Solver.declareFun]
def declareFun' (symbol : String) (sorts : Array Srt) (codomain : Srt) : SmtM Term :=
  ULift.up <$> Solver.declareFun symbol (sorts.map ULift.down) codomain.down false (m := Id)

@[inherit_doc Solver.declareFun]
def declareFun (symbol : String) (α : Type) [A : ToSrt α] : SmtM Term := do
  let a ← A.srt
  let (domain, codomain) ← a.cvc5Signature
  ULift.up <$> Solver.declareFun symbol domain codomain false (m := Id)

@[inherit_doc Solver.declareSort]
def declareSort (symbol : String) (arity : Nat) : SmtM Srt :=
  ULift.up <$> Solver.declareSort symbol arity false (m := Id)

/-! ### Assert-like -/

@[inherit_doc Solver.assertFormula]
def assert (formula : Term) : SmtM Unit :=
  Solver.assertFormula (m := Id) formula.down

/-! ### Check-sat-like -/

-- @[inherit_doc Solver.checkSat]
def checkSat : SmtM cvc5.Result :=
  Solver.checkSat (m := Id)

/-- True if *sat*, false if *unsat*, none if *unknown*, error otherwise. -/
def checkSat? : SmtM (Option Bool) := do
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
def getProof : SmtM (Array cvc5.Proof) :=
  Solver.getProof (m := Id)

end Smt
