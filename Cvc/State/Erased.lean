/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Symbols.Erased
import Cvc.State.Defs



namespace Cvc



namespace ESymbol

abbrev IdentAt k := ESymbol (Symbol.IdentAt k ·)
abbrev TermAt k := ESymbol (Symbol.TermAt k ·)
abbrev ValueAt k := ESymbol (Symbol.ValueAt k ·)

def unrollAt (ident : ESymbol.Ident) (k : Nat := 0) : ESymbol.IdentAt k :=
  ident.map (Symbol.Ident.unroll · k)

instance : ToString (IdentAt k) := ⟨fun id => toString id.getData⟩
instance : ToString (TermAt k) := ⟨fun id => toString id.getData⟩
instance : ToString (ValueAt k) := ⟨fun id => toString id.getData⟩

end ESymbol



namespace ESymbols.ByName

abbrev instState := instSymbols

protected abbrev IdentsAt (k : Nat) := ByName (Symbol.IdentAt k ·)
protected abbrev TermsAt (k : Nat) := ByName (Symbol.TermAt k ·)
protected abbrev ValuesAt (k : Nat) := ByName (Symbol.ValueAt k ·)

Cvc.State.aliasesFor! ByName ← ByName.TermsAt

namespace TermsAt variable (terms : ByName.TermsAt k)



end TermsAt

end ESymbols.ByName
