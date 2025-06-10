/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.State.Erased
import Cvc.Sys.Defs



namespace Cvc



namespace ESys

abbrev ByName (depth : Nat := 0) :=
  Sys Cvc.ESymbols.ByName.instState depth

namespace ByName

def mk (idents : ESymbols.ByName.Idents)
  (init : ESymbols.ByName.StatePred) (step : ESymbols.ByName.StateRel)
: ByName := Sys.mk idents init step

end ByName
