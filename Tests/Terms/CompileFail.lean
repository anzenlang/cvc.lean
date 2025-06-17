/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/
import Cvc.Defs
import Tests.Basic



namespace Cvc.Test



Term.test! [Term.mkEqual.noArg]
  Term.mkEqual #[]
/-- error: could not synthesize default value for parameter 'h_size' using tactics
---
error: expected an array of **at least** two terms
⊢ 2 ≤ #[].size
-/

Term.test! [Term.mkDistinct.oneArg]
  let seven ← Term.int 7
  Term.mkEqual #[seven]
/--
error: could not synthesize default value for parameter 'h_size' using tactics
---
error: expected an array of **at least** two terms
seven : Term.Int
⊢ 2 ≤ #[seven].size
-/

Term.test!

with
  let b1 ← Term.bool true
  let b2 ← Term.bool false
  let b3 ← Term.bool false
  let b4 ← Term.bool false
  -- all of type `Term Bool`

[Term.mkMul.nonArith]
  let _bad1 ← Term.mkMul #[b1, b2, b3, b4]
  let _bad2 ← b1.mul b2
/--
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
⊢ IsSrt.Arith Bool
---
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
_bad1 : Term Bool
⊢ IsSrt.Arith Bool
-/

[Term.mkAdd.nonArith]
  let _bad1 ← Term.mkAdd #[b1, b2, b3, b4]
  let _bad2 ← b1.add b2
/--
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
⊢ IsSrt.Arith Bool
---
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
_bad1 : Term Bool
⊢ IsSrt.Arith Bool
-/

[Term.mkDiv!.nonArith]
  let _bad1 ← Term.mkDiv! #[b1, b2, b3, b4]
  let _bad2 ← b1.div! b2
/--
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
⊢ IsSrt.Arith Bool
---
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
_bad1 : Term Bool
⊢ IsSrt.Arith Bool
-/

[Term.mkDivTotal.nonArith]
  let _bad1 ← Term.mkDivTotal b1 b2
  let _bad2 ← b1.divTotal b2
/--
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
⊢ IsSrt.Arith Bool
---
error: could not synthesize default value for parameter 'Arith' using tactics
---
error: expected arithmetic type `Int` or `Rat`, see `Cvc.is_arith` and `Cvc.IsSrt.Arith`
b1 b2 b3 b4 : Term.Bool
_bad1 : Term Bool
⊢ IsSrt.Arith Bool
-/
