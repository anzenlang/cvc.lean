/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Safe.Defs



/-! # Safe -/
namespace Cvc.Safe



namespace Smt



@[inherit_doc Cvc.Smt.setLogic]
def setLogic (logic : Logic) : SmtM Unit := do
  Cvc.Smt.setLogic logic

@[inherit_doc Cvc.Smt.assert]
def assert (formula : Term Bool) : SmtM Unit := do
  Cvc.Smt.assert formula.toUnsafe


end Smt
