/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

namespace Cvc



/-! # Logic -/
namespace Logic



/-! ## Specification for the arithmetic (`Int`/`Real`) part of the logic -/
namespace Arith



/-- Difference logic / linearity / transcendental numbers. -/
inductive Kind
/-- Only permits difference logic (implies linear). -/
| diff
/-- Arithmetic.

- `linear`: only allows linear terms if true, allows non-linear terms if false.
- `transcendental`: (dis)allows non-algebraic numbers ([wikipedia][trans]).

[trans]: https://en.wikipedia.org/wiki/Transcendental_number
-/
| nonDiff (linear : Bool) (transcendental : Bool)

namespace Kind

def simplest : Kind :=
  .diff

def setNonDiff : Kind → Kind
| .diff => .nonDiff true false
| k@(.nonDiff ..) => k

def setNonLinear : Kind → Kind
| .diff => .nonDiff false true
| .nonDiff _ t => .nonDiff false t

def setTranscendental : Kind → Kind
| .diff => .nonDiff true true
| .nonDiff l _ => .nonDiff l true

end Kind



/-- `Int`, `Real`, or both. -/
inductive IntReal
/-- Only `Int`s. -/
| int
/-- Only `Real`s. -/
| real
/-- `Int`s and `Real`s. -/
| both

namespace IntReal

def simplest : IntReal := .int

/-- Gives the `I`, `R`, or `IR` part of the logic, *e.g.* `IR` in `LIRA`. -/
def toSmtLib : IntReal → String
| int => "I" | real => "R" | both => "IR"

def setInt : IntReal → IntReal
| real => both
| l@int | l@both => l

def setReal : IntReal → IntReal
| int => both
| l@real | l@both => l

end IntReal



end Arith



/-- Full arithmetic (`Int`/`Real`) specification. -/
structure Arith where
  /-- Difference logic / linearity / transcendental numbers. -/
  kind : Arith.Kind
  /-- `Int`, `Real`, or both. -/
  intReal : Arith.IntReal

namespace Arith

def simplest : Arith := ⟨.simplest, .simplest⟩

section variable (self : Arith)

def setNonDiff := {self with kind := self.kind.setNonDiff}

def setNonLinear := {self with kind := self.kind.setNonLinear}

def setTranscendental := {self with kind := self.kind.setTranscendental}

def setInt := {self with intReal := self.intReal.setInt}

def setReal := {self with intReal := self.intReal.setReal}

end

/-- Generates the arithmetic part of an SMT-LIB logic, *e.g.* `NIRA`. -/
def toSmtLib (self : Arith) : String :=
  let (pref, suff) :=
    match self.kind with
    | .diff => ("", "DL")
    | .nonDiff l t => (if l then "L" else "N", if t then "AT" else "A")
  pref ++ self.intReal.toSmtLib ++ suff

/-- `LIA`. -/
def lia : Arith := ⟨.nonDiff true false, .int⟩
/-- `LRA`. -/
def lra : Arith := ⟨.nonDiff true false, .real⟩
/-- `LIRA`. -/
def lira : Arith := ⟨.nonDiff true false, .both⟩

/-- `NIA`. -/
def nia : Arith := ⟨.nonDiff false false, .int⟩
/-- `NRA`. -/
def nra : Arith := ⟨.nonDiff false false, .real⟩
/-- `NIRA`. -/
def nira : Arith := ⟨.nonDiff false false, .both⟩

/-- `LIAT`. -/
def liat : Arith := ⟨.nonDiff true true, .int⟩
/-- `LRAT`. -/
def lrat : Arith := ⟨.nonDiff true true, .real⟩
/-- `LIRAT`. -/
def lirat : Arith := ⟨.nonDiff true true, .both⟩

/-- `NIAT`. -/
def niat : Arith := ⟨.nonDiff false true, .int⟩
/-- `NRAT`. -/
def nrat : Arith := ⟨.nonDiff false true, .real⟩
/-- `NIRAT`. -/
def nirat : Arith := ⟨.nonDiff false true, .both⟩

/-- `IDL`. -/
def idl : Arith := ⟨.diff, .int⟩
/-- `RDL`. -/
def rdl : Arith := ⟨.diff, .real⟩
/-- `IRDL`. -/
def irdl : Arith := ⟨.diff, .both⟩

/-- info:
LIA,  LRA,  LIRA,  NIA,  NRA,  NIRA
LIAT, LRAT, LIRAT, NIAT, NRAT, NIRAT
IDL, RDL, IRDL
-/
#guard_msgs in #eval do
  println! "\
    {Arith.lia.toSmtLib},  {Arith.lra.toSmtLib},  {Arith.lira.toSmtLib},  \
    {Arith.nia.toSmtLib},  {Arith.nra.toSmtLib},  {Arith.nira.toSmtLib}\
  "
  println! "\
    {Arith.liat.toSmtLib}, {Arith.lrat.toSmtLib}, {Arith.lirat.toSmtLib}, \
    {Arith.niat.toSmtLib}, {Arith.nrat.toSmtLib}, {Arith.nirat.toSmtLib}\
  "
  println! "{Arith.idl.toSmtLib}, {Arith.rdl.toSmtLib}, {Arith.irdl.toSmtLib}"
end Arith

end Logic



/-- An SMT-LIB logic.

Based on [cvc5's `logic_info.cpp`][cpp].

[cpp] https://github.com/cvc5/cvc5/blob/7ee7051df025e6db566fc67086a7aa4e1023c8f2/src/theory/logic_info.cpp#L270-L367
-/
structure Logic : Type where private mkRaw ::
  /-- Trumps the rest of the specification and turns everything on.

  You should probably not use this, tailoring the logic to the terms you actually use allows the
  solver to use the best approach available and is crucial for performance.
  -/
  -- #TODO with logic in either the `Build`/`Term` type we could drop this maybe
  private all? : Bool := false
  /-- Higher-order, for reasoning about functions that take functions as arguments. -/
  private ho? : Bool := false
  /-- Quantifier-free, terms cannot use quantifiers. -/
  private qf? : Bool := false
  /-- [Separation logic], typically to reason about program memory.

  [Separation logic](https://en.wikipedia.org/wiki/Separation_logic)
  -/
  private sep? : Bool := false
  /-- For reasoning about arrays. -/
  private array? : Bool := false
  /-- Uninterpreted functions, terms can use symbols of a function-sort. -/
  private uf? : Bool := false
  /-- Cardinality constraints, *a.k.a* pseudo-boolean constraints.

  A cardinality constraint, as a term, is an `Int`-arithmetic relation with `Bool`-sorted symbols.
  These symbols are coerced into `Int` as `false ↦ 0, true ↦ 1`. So, assuming `a b : Bool` we can
  write `a + b ≥ 1` for `a ∨ b`, or `a * b = 1` for `a ∧ b`.
  -/
  private card? : Bool := false
  /-- Bit-vectors. -/
  private bitvec? : Bool := false
  /-- [Finite fields theory][ff].

  [ff]: https://en.wikipedia.org/wiki/Finite_field
  -/
  private ff? : Bool := false
  /-- Floating point numbers. -/
  private float? : Bool := false
  /-- User-defined potentially-recursive datatypes. -/
  private datatype? : Bool := false
  /-- Theory of strings. -/
  private string? : Bool := false
  /-- Specification of the `Int`/`Real` arithmetic theory. -/
  private arith? : Option Logic.Arith := none

namespace Logic

/-- **[private]** True if the SMT-LIB logic's string has letters after the `_` separator.

- `ignoreArray`: if true, don't count `Logic.array?`, *i.e.* return `false` if `array?` was the only
  letter after the `_`. This is used to know whether we need to show array as
  - `A` when there's nothing after in logic's string, or
  - `AX` if there's more.

If `oneTrailing? false` yields false, then either `Logic.all?` or *the logic is ill-formed*.
-/
@[local simp]
private
def oneTrailing? (ignoreArray : Bool) : Logic → Bool
| { array?, uf?, card?, bitvec?, ff?, float?, datatype?, string?, arith?, .. } =>
  (¬ ignoreArray ∧ array?)
  ∨ uf? ∨ card? ∨ bitvec? ∨ ff? ∨ float? ∨ datatype? ∨ string?
  ∨ arith?.isSome



section variable (self : Logic)

/-- True if the SMT-LIB logic's string has letters after the `A`rray letter(s). -/
private def oneAfterArray? : Bool :=
  self.oneTrailing? true

/-- SMT-LIB string representation. -/
def toSmtLib : String :=
  if let {
    all? := false,
    ho?, qf?, sep?, array?, uf?, card?, bitvec?, ff?, float?, datatype?, string?, arith?
  } := self
  then Id.run do
    let mut s := ""
    if ho? then s := s ++ "HO_"
    if qf? then s := s ++ "QF_"
    if sep? then s := s ++ "SEP_"
    if array? then
      s := s ++ if self.oneAfterArray? then "A" else "AX"
    if uf? then s := s ++ "UF"
    if card? then s := s ++ "C"
    if bitvec? then s := s ++ "BV"
    if ff? then s := s ++ "FF"
    if float? then s := s ++ "FP"
    if datatype? then s := s ++ "DT"
    if string? then s := s ++ "S"
    if let some arith := arith? then
      s := s ++ arith.toSmtLib
    s
  else "ALL"

/-- Either `Logic.all?` or at least one actual fragment is active. -/
@[simp]
def isValid : Bool :=
  self.all? ∨ self.oneTrailing? false

@[inherit_doc isValid, simp]
def valid : Prop :=
  self.isValid

instance : Decidable self.valid :=
  inferInstanceAs <| Decidable <| self.isValid

end



structure Builder extends toLogic : Logic
where private mk' ::

namespace Builder

def mk : Builder where
  toLogic := {}

variable (self : Builder)

def ho : Builder := {self with ho? := true}
def qf : Builder := {self with qf? := true}
def sep : Builder := {self with sep? := true}
def array : Builder := {self with array? := true}
def uf : Builder := {self with uf? := true}

def card : Builder := {self with card? := true}
theorem card_valid {b : Builder} : b.card.valid := by
  simp [Builder.card]

def bitvec : Builder := {self with bitvec? := true}
theorem bitvec_valid {b : Builder} : b.bitvec.valid := by
  simp [Builder.bitvec]

def ff : Builder := {self with ff? := true}
theorem ff_valid {b : Builder} : b.ff.valid := by
  simp [Builder.ff]

def float : Builder := {self with float? := true}
theorem float_valid {b : Builder} : b.float.valid := by
  simp [Builder.float]

def datatype : Builder := {self with datatype? := true}
theorem datatype_valid {b : Builder} : b.datatype.valid := by
  simp [Builder.datatype]

def string : Builder := {self with string? := true}
theorem string_valid {b : Builder} : b.string.valid := by
  simp [Builder.string]

def arith (arith : Arith) : Builder := {self with arith? := arith}
theorem arith_valid {b : Builder} {a : Arith} : (b.arith a).valid := by
  simp [Builder.arith]

private
def getArith : Arith := self.arith?.getD .simplest

def nonDiff : Builder := {self with arith? := self.getArith.setNonDiff}
def nonLinear : Builder := {self with arith? := self.getArith.setNonLinear}
def transcendental : Builder := {self with arith? := self.getArith.setTranscendental}
def int : Builder := {self with arith? := self.getArith.setInt}
def real : Builder := {self with arith? := self.getArith.setReal}

end Builder




def all : Logic where
  all? := true
theorem all_valid : all.valid := by simp [all]

def mk : Builder := ⟨{}⟩

variable (self : Logic)

def ho : Logic := {self with ho? := true}
theorem ho_valid {l : Logic} : l.valid → l.ho.valid := by
  simp [ho]

def qf : Logic := {self with qf? := true}
theorem qf_valid {l : Logic} : l.valid → l.qf.valid := by
  simp [qf]

def sep : Logic := {self with sep? := true}
theorem sep_valid {l : Logic} : l.valid → l.sep.valid := by
  simp [sep]

def array : Logic := {self with array? := true}
theorem array_valid {l : Logic} : l.valid → l.array.valid := by
  simp [array]

def uf : Logic := {self with uf? := true}
theorem uf_valid {l : Logic} : l.valid → l.uf.valid := by
  simp [uf]


def card : Logic := {self with card? := true}
theorem card_valid {l : Logic} : l.card.valid := by
  simp [card]

def bitvec : Logic := {self with bitvec? := true}
theorem bitvec_valid {l : Logic} : l.bitvec.valid := by
  simp [bitvec]

def ff : Logic := {self with ff? := true}
theorem ff_valid {l : Logic} : l.ff.valid := by
  simp [ff]

def float : Logic := {self with float? := true}
theorem float_valid {l : Logic} : l.float.valid := by
  simp [float]

def datatype : Logic := {self with datatype? := true}
theorem datatype_valid {l : Logic} : l.datatype.valid := by
  simp [datatype]

def string : Logic := {self with string? := true}
theorem string_valid {l : Logic} : l.string.valid := by
  simp [string]

def arith (arith : Arith) : Logic := {self with arith? := arith}
theorem arith_valid {l : Logic} {a : Arith} : (l.arith a).valid := by
  simp [arith]



/-! ### Convenient `Logic` constructors for `Arith` -/

def lia := mk |>.arith .lia
def lra := mk |>.arith .lra
def lira := mk |>.arith .lira

def nia := mk |>.arith .nia
def nra := mk |>.arith .nra
def nira := mk |>.arith .nira

def liat := mk |>.arith .liat
def lrat := mk |>.arith .lrat
def lirat := mk |>.arith .lirat

def niat := mk |>.arith .niat
def nrat := mk |>.arith .nrat
def nirat := mk |>.arith .nirat

def idl := mk |>.arith .idl
def rdl := mk |>.arith .rdl
def irdl := mk |>.arith .irdl

/-! ### Ubiquitous logics -/

def qf_lia := lia.qf
def qf_lra := lra.qf
def qf_lira := lira.qf

def qf_nia := nia.qf
def qf_nra := nra.qf
def qf_nira := nira.qf

end Logic
