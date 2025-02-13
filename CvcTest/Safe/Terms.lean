/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Safe.Init



namespace Cvc.Safe.Test



/-- error: application type mismatch
  b1.mkIte i1 b1
argument
  b1
has type
  Term Bool : Type
but is expected to have type
  Term Int : Type
---
error: cannot evaluate expression that depends on the `sorry` axiom.
Use `#eval!` to evaluate nevertheless (which may cause lean to crash).
-/
#test do
  let b1 ← Term.mkBool true
  let i1 ← Term.mkInt 7
  let bad ← b1.mkIte i1 b1

/-- error: application type mismatch
  b1.eq i1
argument
  i1
has type
  Term Int : Type
but is expected to have type
  Term Bool : Type
---
error: cannot evaluate expression that depends on the `sorry` axiom.
Use `#eval!` to evaluate nevertheless (which may cause lean to crash).
-/
#test do
  let b1 ← Term.mkBool true
  let i1 ← Term.mkInt 7
  let bad ← b1.eq i1
