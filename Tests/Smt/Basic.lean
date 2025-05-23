/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/
import Tests.Basic



namespace Cvc.Test


Smt.test!

[Term.apply.partialApply]
  let n ← Smt.declare "n" Int
  let f ← Smt.declare "f" (Bool → Int → Int → Int)
  let tru ← Term.bool true
  show[n, f]

  let f_true ← f.apply tru
  let f_true_n ← f_true.apply n
  let f_true_n_5 ← f_true_n.apply (← Term.int 5)
  show[f_true, f_true_n, f_true_n_5]

  Smt.assert (← f_true_n_5.equal n)
  let sat? ← Smt.checkSat?
  show[sat?]
/-- info:
n ↦ n
f ↦ f

f_true ↦ (@ f true)
f_true_n ↦ (@ (@ f true) n)
f_true_n_5 ↦ (f true n 5)

sat? ↦ (some true)
-/
