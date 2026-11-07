/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module




public import Cvc.Basic.Error
import Std.Internal.Parsec.String



namespace Std.Internal.Parsec

def opt? (p : Parsec ι α) : Parsec ι (Option α) := fun input =>
  match p input with
  | .success input res => .success input (some res)
  | .error _ _ => .success input none

def opt {α : Type} (p : Parsec ι α) : Parsec ι Bool := Option.isSome <$> p.opt?

def String.tryChar (c : Char) : Parser Bool := pchar c |>.opt
def String.tryString (s : String) : Parser Bool := pstring s |>.opt

def context (txt : String) (code : Parsec ι α) : Parsec ι α := fun input =>
  match code input with
  | res@(.success _ _) | res@(.error _ .eof) => res
  | .error pos (.other desc) => .other s!"{desc}\n{txt}" |> .error pos

end Std.Internal.Parsec



namespace Cvc public section



/-! # SMT-LIB logics

A `Logic` names the fragment a solver should expect, as `Solver.setLogic` takes it: `QF_LIA`,
`UFBV`, `ALL`… Start from a named logic and extend it, or build one from nothing with `Logic.mk`:

```lean
s.setLogic Logic.qf_lia.uf                        -- QF_UFLIA
s.setLogic (Logic.mk.uf.arith .lia).toLogic.qf    -- QF_UFLIA
```

`Logic.ofSmtLib` parses a logic's name, and `Logic.toSmtLib` prints one.
-/
namespace Logic open Std.Internal (Parsec) open Std.Internal.Parsec.String (Parser)



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
| .diff => .nonDiff false false
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

open Std.Internal.Parsec.String in
private def parseSmtLib : Parser IntReal :=
  .context "failed to parse int/real logic bit" do
  if ← tryChar 'I' then
    if ← tryChar 'R' then return both
    else return int
  if ← tryChar 'R' then return real
  Parsec.fail "expected `I`, `R`, or `IR`"


def ofSmtLib : String → Res IntReal
  | "I" => return int | "R" => return real | "IR" => return both
  | s => throwUser s!"illegal int/real bit `{s}`, expected `I`, `R`, or `IR`"

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

open Std.Internal.Parsec.String in
private def parseSmtLib? : Parser (Option Arith) :=
  .context "failed to parse arithmetic logic bit" do
  let mut nonDiff_l? := none
  if ← tryChar 'L' then
    nonDiff_l? := some true
  else if ← tryChar 'N' then
    nonDiff_l? := some false
  let intReal? ←
    if nonDiff_l?.isNone then IntReal.parseSmtLib |>.opt? else some <$> IntReal.parseSmtLib
  let some intReal := intReal?
    | return none
  if let some l := nonDiff_l? then
    if ← tryString "AT" then return some { kind := Kind.nonDiff l true, intReal }
    else if ← tryChar 'A' then return some { kind := Kind.nonDiff l false, intReal }
    else Parsec.fail "expected `AT` or `A` because `L`/`N` prefix"
  else
    if ← tryString "DL" then return some { kind := Kind.diff, intReal}
    else Parsec.fail "expected `DL` because of the absence of `L`/`N` prefix"

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



/-- An SMT-LIB logic, such as `QF_LIA`. -/
-- Based on cvc5's `src/theory/logic_info.cpp`, at commit 7ee7051df025e6db566fc67086a7aa4e1023c8f2,
-- lines 270 to 367.
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
  private bitVec? : Bool := false
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
| { array?, uf?, card?, bitVec?, ff?, float?, datatype?, string?, arith?, .. } =>
  (¬ ignoreArray ∧ array?)
  ∨ uf? ∨ card? ∨ bitVec? ∨ ff? ∨ float? ∨ datatype? ∨ string?
  ∨ arith?.isSome



section variable (self : Logic)

/-- True if the SMT-LIB logic's string has letters after the `A`rray letter(s). -/
private def oneAfterArray? : Bool :=
  self.oneTrailing? true

/-- Whether the logic is `ALL` or enables at least one theory. -/
@[simp]
def isValid : Bool :=
  self.all? ∨ self.oneTrailing? false

@[inherit_doc isValid, simp]
def valid : Prop :=
  self.isValid

instance : Decidable self.valid :=
  inferInstanceAs <| Decidable <| self.isValid

end



/-- A logic built from nothing, started by `Logic.mk` and finished by `toLogic`. -/
structure Builder extends toLogic : Logic
where private mk' ::

namespace Builder

/-- The empty logic, to add theories to. -/
def mk : Builder where
  toLogic := {}

variable (self : Builder)

/-- Adds higher-order reasoning, `HO_`. -/
def ho : Builder := {self with ho? := true}
/-- Makes the logic quantifier-free, `QF_`. -/
def qf : Builder := {self with qf? := true}
/-- Adds separation logic, `SEP_`. -/
def sep : Builder := {self with sep? := true}
/-- Adds arrays, `A` or `AX`. -/
def array : Builder := {self with array? := true}
/-- Adds uninterpreted functions, `UF`. -/
def uf : Builder := {self with uf? := true}

/-- Adds cardinality constraints, `C`. -/
def card : Builder := {self with card? := true}
theorem card_valid {b : Builder} : b.card.valid := by
  simp [Builder.card]

/-- Adds bit-vectors, `BV`. -/
def bitVec : Builder := {self with bitVec? := true}
theorem bitVec_valid {b : Builder} : b.bitVec.valid := by
  simp [Builder.bitVec]

/-- Adds finite fields, `FF`. -/
def ff : Builder := {self with ff? := true}
theorem ff_valid {b : Builder} : b.ff.valid := by
  simp [Builder.ff]

/-- Adds floating-point arithmetic, `FP`. -/
def float : Builder := {self with float? := true}
theorem float_valid {b : Builder} : b.float.valid := by
  simp [Builder.float]

/-- Adds datatypes, `DT`. -/
def datatype : Builder := {self with datatype? := true}
theorem datatype_valid {b : Builder} : b.datatype.valid := by
  simp [Builder.datatype]

/-- Adds strings, `S`. -/
def string : Builder := {self with string? := true}
theorem string_valid {b : Builder} : b.string.valid := by
  simp [Builder.string]

/-- Sets the arithmetic part, such as `Arith.lia`. -/
def arith (arith : Arith) : Builder := {self with arith? := arith}
theorem arith_valid {b : Builder} {a : Arith} : (b.arith a).valid := by
  simp [Builder.arith]

private
def getArith : Arith := self.arith?.getD .simplest

/-- Makes the arithmetic linear rather than difference logic. -/
def nonDiff : Builder := {self with arith? := self.getArith.setNonDiff}
/-- Makes the arithmetic non-linear. -/
def nonLinear : Builder := {self with arith? := self.getArith.setNonLinear}
/-- Adds transcendental functions to the arithmetic. -/
def transcendental : Builder := {self with arith? := self.getArith.setTranscendental}
/-- Adds integers to the arithmetic. -/
def int : Builder := {self with arith? := self.getArith.setInt}
/-- Adds reals to the arithmetic. -/
def real : Builder := {self with arith? := self.getArith.setReal}
-- Each starts from integer difference logic when no arithmetic was set yet.

end Builder


/-- `ALL`: every theory cvc5 supports. -/
def all : Logic where
  all? := true
theorem all_valid : all.valid := by simp [all]

/-- Starts building a logic from nothing. -/
def mk : Builder := ⟨{}⟩

variable (self : Logic)

/-- Adds higher-order reasoning, `HO_`. -/
def ho : Logic := {self with ho? := true}
theorem ho_valid {l : Logic} : l.valid → l.ho.valid := by
  simp [ho]

/-- Makes the logic quantifier-free, `QF_`. -/
def qf : Logic := {self with qf? := true}
theorem qf_valid {l : Logic} : l.valid → l.qf.valid := by
  simp [qf]

/-- Adds separation logic, `SEP_`. -/
def sep : Logic := {self with sep? := true}
theorem sep_valid {l : Logic} : l.valid → l.sep.valid := by
  simp [sep]

/-- Adds arrays, `A` or `AX`. -/
def array : Logic := {self with array? := true}
theorem array_valid {l : Logic} : l.valid → l.array.valid := by
  simp [array]

/-- Adds uninterpreted functions, `UF`. -/
def uf : Logic := {self with uf? := true}
theorem uf_valid {l : Logic} : l.valid → l.uf.valid := by
  simp [uf]


/-- Adds cardinality constraints, `C`. -/
def card : Logic := {self with card? := true}
theorem card_valid {l : Logic} : l.card.valid := by
  simp [card]

/-- Adds bit-vectors, `BV`. -/
def bitVec : Logic := {self with bitVec? := true}
theorem bitVec_valid {l : Logic} : l.bitVec.valid := by
  simp [bitVec]

/-- Adds finite fields, `FF`. -/
def ff : Logic := {self with ff? := true}
theorem ff_valid {l : Logic} : l.ff.valid := by
  simp [ff]

/-- Adds floating-point arithmetic, `FP`. -/
def float : Logic := {self with float? := true}
theorem float_valid {l : Logic} : l.float.valid := by
  simp [float]

/-- Adds datatypes, `DT`. -/
def datatype : Logic := {self with datatype? := true}
theorem datatype_valid {l : Logic} : l.datatype.valid := by
  simp [datatype]

/-- Adds strings, `S`. -/
def string : Logic := {self with string? := true}
theorem string_valid {l : Logic} : l.string.valid := by
  simp [string]

/-- Sets the arithmetic part, such as `Arith.lia`. -/
def arith (arith : Arith) : Logic := {self with arith? := arith}
theorem arith_valid {l : Logic} {a : Arith} : (l.arith a).valid := by
  simp [arith]



/-! ### Pure arithmetic logics

Each is the logic of its name: `Logic.lira` is `LIRA`, `Logic.qf_nia` is `QF_NIA`.
-/

def lia := mk |>.arith .lia |>.toLogic
def lra := mk |>.arith .lra |>.toLogic
def lira := mk |>.arith .lira |>.toLogic

def nia := mk |>.arith .nia |>.toLogic
def nra := mk |>.arith .nra |>.toLogic
def nira := mk |>.arith .nira |>.toLogic

def liat := mk |>.arith .liat |>.toLogic
def lrat := mk |>.arith .lrat |>.toLogic
def lirat := mk |>.arith .lirat |>.toLogic

def niat := mk |>.arith .niat |>.toLogic
def nrat := mk |>.arith .nrat |>.toLogic
def nirat := mk |>.arith .nirat |>.toLogic

def idl := mk |>.arith .idl |>.toLogic
def rdl := mk |>.arith .rdl |>.toLogic
def irdl := mk |>.arith .irdl |>.toLogic


def qf_lia := lia.qf
def qf_lra := lra.qf
def qf_lira := lira.qf

def qf_nia := nia.qf
def qf_nra := nra.qf
def qf_nira := nira.qf

/-! ### Conversion from/to strings -/

/-- SMT-LIB string representation. -/
def toSmtLib : Logic → String
| self@{
  all?, ho?, qf?, sep?, array?, uf?, card?, bitVec?, ff?, float?, datatype?, string?, arith?
} => Id.run do
  let mut s := ""
  if ho? then s := s ++ "HO_"
  if qf? then s := s ++ "QF_"
  if all? then s!"{s}ALL" else
    if sep? then s := s ++ "SEP_"
    if array? then s := s ++ if self.oneAfterArray? then "A" else "AX"
    if uf? then s := s ++ "UF"
    if card? then s := s ++ "C"
    if bitVec? then s := s ++ "BV"
    if ff? then s := s ++ "FF"
    if float? then s := s ++ "FP"
    if datatype? then s := s ++ "DT"
    if string? then s := s ++ "S"
    if let some arith := arith? then
      s := s ++ arith.toSmtLib
    s

@[inherit_doc toSmtLib]
protected abbrev toString := toSmtLib

instance : ToString Logic := ⟨Logic.toString⟩

open Std.Internal.Parsec.String in
private def parseSmtLib (thenEoi : Bool := false) : Parser Logic := do
  let logic ← aux
  if thenEoi then if ← not <$> .isEof then
    .fail s!"expected end-of-input after logic `{logic.toSmtLib}`"
  return logic
where
  aux :=
    .context "failed to parse SMT-LIB logic" do
    if ← tryString "ALL" then return all
    if ← tryString "HO_ALL" then return all.ho
    if ← tryString "QF_ALL" then return all.qf
    if ← tryString "HO_QF_ALL" then return all.ho.qf
    let mut builder1 ←
      parseBit "HO_" .ho Builder.mk
      >>= parseBit "QF_" .qf
      >>= parseBit "SEP_" .sep
    if ← tryChar 'A' then
      builder1 := builder1.array
      if ← tryChar 'X' then return builder1.toLogic
    let mut builder2 ←
      parseBit "UF" .uf builder1
      >>= parseBit "C" .card
      >>= parseBit "BV" .bitVec
      >>= parseBit "FF" .ff
      >>= parseBit "FP" .float
      >>= parseBit "DT" .datatype
      >>= parseBit "S" .string
    if let some arith ← Arith.parseSmtLib? then
      builder2 := builder2.arith arith
    return builder2.toLogic
  parseBit (tag : String) (f : Builder → Builder) (builder : Builder) : Parser Builder := do
    if ← pstring tag |>.opt then return f builder else return builder

/-- Parses an SMT-LIB logic name, such as `QF_UFLIA`. -/
def ofSmtLib (s : String) : Res Logic :=
  parseSmtLib (thenEoi := true) |>.run s |>.mapError Error.user

end Logic
