/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Extra.Sys
import Cvc.Untyped.Theory.Arith

public meta import Cvc.Untyped.Extra.Sys
public meta import Cvc.Untyped.Theory.Arith



/-! # State variables, sort-erased

`structure.stateVars` is `structure.symbols` for symbols read at a *step*. Two things differ, both
forced by `Symbol.At`: a field is **stored** under its `raw` name, and beside it comes a projection
under the name the writer used, which unwraps the `At`.
-/
namespace Cvc.Tests.Untyped.SVars

open Cvc Untyped

variable [Ω]

/-- State variables of a little counter. -/
structure.stateVars Counter where
  /-- Whether it is counting. -/
  counting : Bool
  count : Int

/-! ## What is generated

The stored field carries the wrap; the projection takes the `At` off it and is **generic in the
wrap**, which is what lets one projection serve every instantiation.
-/

/-- info: @Counter.rawCount : {W : Symbols.Wrap} → Counter W → W Int -/
#guard_msgs in #check @Counter.rawCount

/-- info:
@Counter.count : {W : Symbols.Wrap} → {k : Nat} → Counter (Symbol.At k W) → W Int
-/
#guard_msgs in #check @Counter.count

/-! ## One projection, every instantiation

At terms it answers a term, at values a Lean value — and neither needs `.get`.
-/

example (s : Counter.TermsAt 0) : Term := s.count
example (s : Counter.ValuesAt 0) : Int := s.count
example (s : Counter.ValuesAt 3) : Bool := s.counting

/-! It is reached through the *generic* type a transition system hands over, which is the whole
reason the projection lives in the structure's namespace rather than an alias'. Dot notation
resolves against the head constant after unfolding, and `ι.TermsAt k` unfolds to
`Counter (Symbol.At k …)` — so Lean looks in `Counter`, never in `Counter.TermsAt`. -/

example {ι : SVars Counter} (s : ι.TermsAt 0) : Env Term := smt! s.count + 1
example {ι : SVars Counter} (s : ι.ValuesAt 0) : Bool := s.counting

/-! ## Symbols are named per step -/

/-- info: count__@__0 count__@__2 -/
#guard_msgs in #eval Env.runIO do
  let at0 ← Counter.idents.declareAt 0
  let at2 ← Counter.idents.declareAt 2
  println! "{at0.count} {at2.count}"
