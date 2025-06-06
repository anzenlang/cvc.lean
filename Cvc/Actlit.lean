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

protected structure Ident where
private mk' ::
  getIdent : String

namespace Ident

protected def reservedPref := "__cvc_reserved_actlit__"

protected def identOfIdx (idx : Nat) := s!"{Actlit.Ident.reservedPref}{idx}"

def ofIdx (idx : Nat) : Actlit.Ident := ⟨Ident.identOfIdx idx⟩

instance : Coe Actlit.Ident String := ⟨getIdent⟩
instance : ToString Actlit.Ident := ⟨getIdent⟩

def declare (ident : Actlit.Ident) : Smt Actlit :=
  return ⟨← Smt.declare ident Bool⟩

end Ident

def ofIdx (idx : Nat) : Smt Actlit :=
  Actlit.Ident.ofIdx idx |>.declare

def isActlitIdent (s : String) := s.startsWith Actlit.Ident.reservedPref

def isActlitTerm (term : Formula) : Bool :=
  term.getSymbol?.map isActlitIdent |>.getD false

def fresh : Smt Actlit := Smt.nextActlitIdx >>= Actlit.ofIdx

section variable (a : Actlit)

def activate (a : Actlit) (term : Formula) : Smt Unit := do
  Smt.assert (← a.getTerm.implies term)

def equate (a : Actlit) (term : Formula) : Smt Unit := do
  Smt.assert (← a.getTerm.equal term)

def deactivate (a : Actlit) : Smt Unit := do
  Smt.assert (← a.getTerm.not)

end

end Actlit

namespace Smt

def freshActlit : Smt Actlit := Actlit.fresh

export Actlit (activate equate deactivate)

end Smt



namespace Term

def isActlit : Formula → Bool := Actlit.isActlitTerm

export Actlit (activate equate deactivate)

end Term

namespace Formula

def isActlit : Formula → Bool := Actlit.isActlitTerm

export Actlit (activate equate deactivate)

end Formula
