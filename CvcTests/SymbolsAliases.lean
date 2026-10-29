/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Core.Symbols
import Cvc.Untyped.Theory.Arith
import Cvc.Typed.Core.Symbols
import Cvc.Typed.Theory.Arith



/-! # The aliases `structure.symbols` generates

One per `Symbols.Sig` alias of the layer, applied to the structure. No `Ω` is in scope in this
module: an alias that mentions a term binds the scope itself.
-/
namespace Cvc.Tests.SymbolsAliases

namespace Erased

open Cvc Untyped

structure.symbols Machine where
  running : Bool
  steps : Int

/-- info: Machine.Idents : Type -/
#guard_msgs in #check @Machine.Idents
/-- info: Machine.Values : Type -/
#guard_msgs in #check @Machine.Values
/-- info: Machine.ValuesAt : Nat → Type -/
#guard_msgs in #check @Machine.ValuesAt
/-- info: @Machine.Terms : [Ω] → Type -/
#guard_msgs in #check @Machine.Terms
/-- info: @Machine.TermsAt : [Ω] → Nat → Type -/
#guard_msgs in #check @Machine.TermsAt
/-- info: @Machine.BVars : [Ω] → Type -/
#guard_msgs in #check @Machine.BVars
/-- info: @Machine.ValueTerms : [Ω] → Type -/
#guard_msgs in #check @Machine.ValueTerms
/-- info: @Machine.ValueTermsAt : [Ω] → Nat → Type -/
#guard_msgs in #check @Machine.ValueTermsAt
/-- info: @Machine.Fun : [Ω] → Type -/
#guard_msgs in #check @Machine.Fun
/-- info: @Machine.FunAt : [Ω] → Nat → Type -/
#guard_msgs in #check @Machine.FunAt
/-- info: @Machine.FunAt' : [Ω] → Type -/
#guard_msgs in #check @Machine.FunAt'
/-- info: @Machine.Fun2At : [Ω] → (k : Nat) → optParam Nat (k + 1) → Type -/
#guard_msgs in #check @Machine.Fun2At
/-- info: @Machine.Fun2At' : [Ω] → Type -/
#guard_msgs in #check @Machine.Fun2At'

/-- The second depth of a two-state alias defaults to the next one, and can be given. -/
example [Ω] : Machine.Fun2At 0 = Machine.Fun2At 0 1 := rfl
example [Ω] (f : Machine.Fun2At 0 5) : Machine.TermsAt 0 → Machine.TermsAt 5 → Env Term := f

/-- Only the layer's own aliases are reserved: this layer generates no `PredAt`. -/
structure.symbols Free where
  PredAt : Bool

end Erased

namespace Indexed

open Cvc Typed

structure.symbols Machine where
  running : Bool
  steps : Int

/-- info: Machine.Idents : Type -/
#guard_msgs in #check @Machine.Idents
/-- info: Machine.Values : Type -/
#guard_msgs in #check @Machine.Values
/-- info: Machine.ValuesAt : Nat → Type -/
#guard_msgs in #check @Machine.ValuesAt
/-- info: @Machine.Terms : [Ω] → Type -/
#guard_msgs in #check @Machine.Terms
/-- info: @Machine.TermsAt : [Ω] → Nat → Type -/
#guard_msgs in #check @Machine.TermsAt
/-- info: @Machine.BVars : [Ω] → Type -/
#guard_msgs in #check @Machine.BVars
/-- info: @Machine.ValueTerms : [Ω] → Type -/
#guard_msgs in #check @Machine.ValueTerms
/-- info: @Machine.ValueTermsAt : [Ω] → Nat → Type -/
#guard_msgs in #check @Machine.ValueTermsAt
/-- info: @Machine.Fun : [Ω] → Type → Type -/
#guard_msgs in #check @Machine.Fun
/-- info: @Machine.FunAt : [Ω] → Type → Nat → Type -/
#guard_msgs in #check @Machine.FunAt
/-- info: @Machine.FunAt' : [Ω] → Type → Type -/
#guard_msgs in #check @Machine.FunAt'
/-- info: @Machine.Fun2At : [Ω] → Type → (k : Nat) → optParam Nat (k + 1) → Type -/
#guard_msgs in #check @Machine.Fun2At
/-- info: @Machine.Fun2At' : [Ω] → Type → Type -/
#guard_msgs in #check @Machine.Fun2At'
/-- info: @Machine.Pred : [Ω] → Type -/
#guard_msgs in #check @Machine.Pred
/-- info: @Machine.PredAt : [Ω] → Nat → Type -/
#guard_msgs in #check @Machine.PredAt
/-- info: @Machine.PredAt' : [Ω] → Type -/
#guard_msgs in #check @Machine.PredAt'
/-- info: @Machine.RelAt : [Ω] → (k : Nat) → optParam Nat (k + 1) → Type -/
#guard_msgs in #check @Machine.RelAt
/-- info: @Machine.RelAt' : [Ω] → Type -/
#guard_msgs in #check @Machine.RelAt'

example [Ω] : Machine.RelAt 0 = Machine.RelAt 0 1 := rfl
example [Ω] (r : Machine.RelAt 0 5) : Machine.TermsAt 0 → Machine.TermsAt 5 → Env (Term Bool) := r

/-! A field named as one of this layer's aliases is refused. -/

/-- error: `PredAt` is generated beside a symbols structure, so a symbol cannot be called that -/
#guard_msgs in
structure.symbols Clash where
  PredAt : Bool

end Indexed
