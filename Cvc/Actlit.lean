/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/



import Cvc.Defs



namespace Cvc



structure Actlit where
private mk' ::
  getTerm : Formula

namespace Actlit

instance : Coe Actlit Formula := ⟨getTerm⟩

protected def reservedIdentPref := "__cvc_reserved_actlit__"

protected def mkSymbol (n : Nat) := s!"{Actlit.reservedIdentPref}{n}__"

def isActlitIdent (s : String) := s.startsWith Actlit.reservedIdentPref

def isActlitTerm (term : Formula) : Bool :=
  term.getSymbol?.map isActlitIdent |>.getD false

def fresh : Smt Actlit := do
  let symbol ← Actlit.mkSymbol <$> Smt.nextActlitIdx
  Actlit.mk' <$> Smt.declare symbol Bool

section variable (a : Actlit)

def activate (a : Actlit) (term : Formula) : Smt Unit := do
  Smt.assert (← a.getTerm.implies term)

def deactivate (a : Actlit) : Smt Unit := do
  Smt.assert (← a.getTerm.not)

end

end Actlit

namespace Smt

def freshActlit : Smt Actlit := Actlit.fresh

export Actlit (activate deactivate)

end Smt



namespace Term

def isActlit : Formula → Bool := Actlit.isActlitTerm

export Actlit (activate deactivate)

end Term

namespace Formula

def isActlit : Formula → Bool := Actlit.isActlitTerm

export Actlit (activate deactivate)

end Formula
