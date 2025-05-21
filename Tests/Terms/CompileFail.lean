/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/
import Cvc.Defs
import Tests.Basic



namespace Cvc.Test



Term.test!


[Term.mkEqual.noArg]
  Term.mkEqual #[]
/-- error: could not synthesize default value for parameter 'h_size' using tactics
---
error: expected an array of **at least** two terms
⊢ 2 ≤ #[].size
-/

[Term.mkDistinct.oneArg]
  let seven ← Term.int 7
  -- all of type `Term Bool`
  Term.mkEqual #[seven]
/--
error: could not synthesize default value for parameter 'h_size' using tactics
---
error: expected an array of **at least** two terms
seven : Term.Int
⊢ 2 ≤ #[seven].size
-/

[Term.mkAdd.nonArith]
  let b1 ← Term.bool true
  let b2 ← Term.bool false
  let b3 ← Term.bool false
  let b4 ← Term.bool false
  -- all of type `Term Bool`
  Term.mkAdd #[b1, b2, b3, b4]
/--
error: could not synthesize default value for parameter 'h_arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.Srt.Bij.Arith`
b1 b2 b3 b4 : Term.Bool
⊢ Cvc.is_arith Bool
-/

[Term.add.nonArith]
  let b1 ← Term.bool true
  let b2 ← Term.bool false
  -- all of type `Term Bool`
  b1.add b2
/--
error: could not synthesize default value for parameter 'h_arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.Srt.Bij.Arith`
b1 b2 : Term.Bool
⊢ Cvc.is_arith Bool
-/
