/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Theory
public import Cvc.Untyped.Core.Solver

public meta import Cvc.Untyped.Theory
public meta import Cvc.Untyped.Core.Solver



/-! # Sort-erased views

Every theory's view is registered by importing the theory, and `def.term_view V` gathers them.
-/
namespace Cvc.Tests.Untyped.View

open Cvc
open Cvc.Untyped

/-! ## What each theory has no constructor for

Values and declared symbols are the aggregate's leaves; a `tm` constructor taking arguments builds a
value too. Everything else has a constructor.
-/

/-- info: Array: 3 operators
  no constructor for mkConstArray: a value, the `.value` leaf
Arith: 39 operators
  no constructor for mkInt: a value, the `.value` leaf
  no constructor for mkIntOfString: a value, the `.value` leaf
  no constructor for mkReal: a value, the `.value` leaf
  no constructor for mkRealOfString: a value, the `.value` leaf
Bag: 19 operators
BitVec: 54 operators
  no constructor for mkBitVec: a value, the `.value` leaf
  no constructor for mkBitVecOfString: a value, the `.value` leaf
Bool: 8 operators
  no constructor for mkTrue: a value, the `.value` leaf
  no constructor for mkFalse: a value, the `.value` leaf
  no constructor for mkBool: a value, the `.value` leaf
  no constructor for mkSymbol: a declared symbol, the `.symbol` leaf
Datatype: 4 operators
FiniteField: 4 operators
Float: 33 operators
  no constructor for mkFloatNaN: a value, the `.value` leaf
  no constructor for mkFloatPosInf: a value, the `.value` leaf
  no constructor for mkFloatNegInf: a value, the `.value` leaf
  no constructor for mkFloatPosZero: a value, the `.value` leaf
  no constructor for mkFloatNegZero: a value, the `.value` leaf
  no constructor for mkFloat: a value, the `.value` leaf
Fun: 1 operators
Apply: 1 operators
String: 26 operators
  no constructor for mkString: a value, the `.value` leaf
Regex: 14 operators
Seq: 14 operators
  no constructor for mkEmptySeq: a value, the `.value` leaf
Set: 19 operators
Quant: 2 operators
Sep: 3 operators
-/
#guard_msgs in #untyped_views

/-! ## The aggregate -/

public section variable [Ω]

def.term_view V

end

/-- info: @V.lt : [inst : Ω] → Kids → V -/
#guard_msgs in #check @V.lt

/-- info: @V.bvExtract : [inst : Ω] → Nat → Nat → Term → V -/
#guard_msgs in #check @V.bvExtract

/-- info: @V.setEmpty : [inst : Ω] → V -/
#guard_msgs in #check @V.setEmpty

/-- info: @V.forall' : [inst : Ω] → BVars → Term → Option Term → V -/
#guard_msgs in #check @V.forall'

/-! ## Taking terms apart -/

section variable [Ω]

/-- One line per term: the operator, and what it holds. -/
def describe (t : Term) : String :=
  match V.of t with
  | .value t => s!"a value: {t}"
  | .symbol name => s!"the symbol {name}"
  | .bvar x => s!"the bound variable {x.toTerm}"
  | .lt ks => s!"a `<` of {ks.val.size} operands"
  | .bvExtract hi lo bv => s!"bits {hi} to {lo} of {bv}"
  | .setEmpty => "the empty set"
  | .forall' vars body _ => s!"a ∀ over {vars.size} variable(s), of body {body}"
  | .apply f args => s!"{f} applied to {args.val.size} argument(s)"
  | .construct ctor args => s!"built by {ctor} from {args}"
  | .other t => s!"something else: {t}"
  | _ => "an operator this test does not describe"

end

/-- info: a value: 3
the symbol x
a `<` of 2 operands
bits 3 to 0 of b
the empty set
a ∀ over 1 variable(s), of body (< n x)
f applied to 1 argument(s)
built by __cvc5_record_a_Int_ctor from #[x]
an operator this test does not describe
-/
#guard_msgs in #eval Env.runIO do
  let int ← Srt.int
  let x ← Term.mkSymbol int "x"
  let y ← Term.mkSymbol int "y"
  let f ← Term.mkSymbol (← Srt.function #[int] int) "f"
  let b ← Term.mkSymbol (← Srt.bitVec 8) "b"
  for t in [
    ← Term.mkInt 3,
    x,
    ← Term.lt x y,
    ← Term.bvExtract 3 0 b,
    ← Term.setEmpty int,
    ← Term.forallH [("n", int)] fun n => Term.lt n x,
    ← Term.apply f x,
    ← Term.mkRecord (← Srt.record #[("a", int)]) #[("a", x)],
    ← Term.add x y
  ] do
    println! describe t



/-! ## Kind ownership

A kind is taken apart by one view only. `def.term_view` refuses to route a kind to two, naming both,
before it emits anything: here a second view claiming `ITE`.
-/

public section variable [Ω]

/-- A second view of `ITE`. -/
inductive Clash where
  /-- An if-then-else. -/
  | ite2 (c a b : Term)

/-- Takes nothing apart: only its registration matters here. -/
def Clash.of? (_ : Term) : Option Clash := none

end

register_untyped_view% Cvc.Tests.Untyped.View.Clash [ite2 ITE]

public section variable [Ω]

/-- error: `Clashing`: kind `ITE` is owned by both `Cvc.Untyped.View.Bool` and `Cvc.Tests.Untyped.View.Clash` -/
#guard_msgs in
def.term_view Clashing

end
