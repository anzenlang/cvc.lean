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

/-! ### Simplify, interpolants, QE -/

@[inherit_doc Solver.getInterpolant?]
def getInterpolant? (term : Term) : SmtM (Option Term) := do
  if let some term! ← Solver.getInterpolant? (m := Id) term.toCvc5 then
    return Term.ofCvc5 term!
  else
    return none

@[inherit_doc Solver.getQuantifierElimination]
def getQuantifierElimination (q : Term) : SmtM Term :=
  Term.ofCvc5 <$> Solver.getQuantifierElimination (m := Id) q.toCvc5

/-! ### Declare/define -/

@[inherit_doc Solver.declareFun]
def declareFun' (symbol : String) (sorts : Array Srt) (codomain : Srt) : SmtM Term :=
  Term.ofCvc5 <$> Solver.declareFun symbol (sorts.map Srt.toCvc5) codomain.toCvc5 false (m := Id)

@[inherit_doc Solver.declareFun]
def declareFun (symbol : String) (α : Type) [A : ToSrt α] : SmtM Term := do
  let a ← A.srt
  let (domain, codomain) ← a.cvc5Signature
  Term.ofCvc5 <$> Solver.declareFun symbol domain codomain false (m := Id)

@[inherit_doc Solver.declareSort]
def declareSort (symbol : String) (arity : Nat) : SmtM Srt :=
  Srt.ofCvc5 <$> Solver.declareSort symbol arity false (m := Id)

/-! ### Assert-like -/

@[inherit_doc Solver.assertFormula]
def assert (formula : Term) : SmtM Unit :=
  Solver.assertFormula (m := Id) formula.toCvc5

/-! ### Check-sat-like -/

@[inherit_doc Solver.checkSat]
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

@[inherit_doc Solver.getValue]
def getValue (term : Term) : SmtM Term := do
  let value ← Solver.getValue term.toCvc5 (m := Id)
  return Term.ofCvc5 value

@[inherit_doc Solver.getValues]
def getValues (terms : Array Term) : SmtM (Array Term) := do
  let values ← Solver.getValues (terms.map Term.toCvc5) (m := Id)
  return values.map Term.ofCvc5

@[inherit_doc Solver.getModelDomainElements]
def getModelDomainElements (srt : Srt) : SmtM (Array Term) := do
  let values ← Solver.getModelDomainElements srt.toCvc5 (m := Id)
  return values.map Term.ofCvc5

/-! ### Unsat mode commands -/

@[inherit_doc Solver.getProof]
def getProof : SmtM (Array cvc5.Proof) :=
  Solver.getProof (m := Id)

end Smt
