/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.BuiltinCommand

public import Cvc.Basic.Env



/-! # Zero-cost wrappers over lean-cvc5, and the sort type

`def0%`–`def3%` declare a `def` equal to a cvc5 type, with `private` conversions either way, so
that a wrapper costs nothing at runtime while staying opaque to a user who imports it plainly. The
level says which instances come with it: `1` adds `ToString`, `2` adds `BEq`/`Hashable`, `3` adds
`Ord`/`LT`/`LE`/`compare`. An optional `( ofId / toId )` suffix renames the conversions.

The tokens are `wrap*%` rather than `def*%` because a syntax category and its command are global:
`Cvc.Untyped.Defs` already claims `def*%`, and two commands matching the same syntax make every use
ambiguous.

On top of the machinery this declares `Srt` — an SMT-LIB sort — along with `Srts`, the abstract
sort kinds, the pure Lean description `Typ` and the `ToTyp` class mapping a Lean type to one. Sort
*constructors* are in `Cvc/Srt.lean`; only the types are here, so that the macros and the
types they declare stay separable.
-/
namespace Cvc



public meta section codeGen open Lean Syntax Elab Command

structure TypeGen where mk' ::
  mainId : Ident
  tParam? : Option Ident
  subId : Ident
  ofSubId : Ident
  toSubId : Ident
  idTerm : Term
  idSig : Term
  idDef : Term

namespace TypeGen variable (tg : TypeGen)

def mk (mainId : Ident) (subId : Ident)  (tParam? ofSubId? toSubId? : Option Ident)
: CommandElabM TypeGen := do
  let mut ofSubId := mkIdent `ofUnsafe
  let mut toSubId := mkIdent `toUnsafe
  if let (some ofSubId', some toSubId') := (ofSubId?, toSubId?) then
    ofSubId := ofSubId'
    toSubId := toSubId'
  let mut idDef ← `($subId)
  let mut idSig ← ``(Type)
  let mut idTerm ← `($mainId)
  if let some tParam := tParam? then
    idDef ← `(fun _ => $idDef)
    idSig ← `( (_ : Type) → $idSig )
    idTerm ← `($idTerm $tParam)
  return {
    mainId, tParam?, subId, ofSubId, toSubId
    idTerm, idSig, idDef
  }

def namespaced (code : CommandElabM α) : CommandElabM α :=
  Lean.Elab.Command.withNamespace tg.mainId.getId code

def elaborate (stx : CommandElabM (TSyntax `command)) : CommandElabM Unit := do
  let stx ← stx
  elabCommand stx

def elab0 : CommandElabM Unit := do
  elaborate `(
    @[inherit_doc $tg.subId]
    def $tg.mainId [Ω] : $tg.idSig := $tg.idDef
  )
  tg.namespaced do elaborate `(
    instance : Nonempty $tg.idTerm := inferInstanceAs (Nonempty $tg.subId)
    @[inline] private def $tg.ofSubId : $tg.subId → $tg.idTerm := id
    @[inline] private def $tg.toSubId : $tg.idTerm → $tg.subId := id
  )

def elab1 : CommandElabM Unit := do
  tg.elab0
  let toStringId := `toString |> mkIdent
  let toStringSubId := tg.subId.getId |>.append `toString |> mkIdent
  tg.namespaced do elaborate `(
    instance : ToString $tg.idTerm := inferInstanceAs (ToString $tg.subId)
    @[inherit_doc $toStringSubId]
    protected def $toStringId : $tg.idTerm → String := $toStringSubId
  )

def elab2 : CommandElabM Unit := do
  tg.elab1
  let beqId := `beq |> mkIdent
  let beqSubId := tg.subId.getId |>.append `beq |> mkIdent
  let hashId := `hash |> mkIdent
  let hashSubId := tg.subId.getId |>.append `hash |> mkIdent
  tg.namespaced do elaborate `(
    instance : BEq $tg.idTerm := inferInstanceAs (BEq $tg.subId)
    @[inherit_doc $beqSubId]
    protected def $beqId : $tg.idTerm → $tg.idTerm → Bool := $beqSubId
    instance : Hashable $tg.idTerm := inferInstanceAs (Hashable $tg.subId)
    @[inherit_doc $hashSubId]
    protected def $hashId : $tg.idTerm → UInt64 := $hashSubId
  )

def elab3 : CommandElabM Unit := do
  tg.elab2
  let bltId := `blt |> mkIdent
  let bltSrc := tg.subId.getId |>.append `blt |> mkIdent
  let bleId := `ble |> mkIdent
  let bleSrc := tg.subId.getId |>.append `ble |> mkIdent
  let bgtId := `bgt |> mkIdent
  let bgtSrc := tg.subId.getId |>.append `bgt |> mkIdent
  let bgeId := `bge |> mkIdent
  let bgeSrc := tg.subId.getId |>.append `bge |> mkIdent
  let compareId := `compare |> mkIdent
  let compareSrc := tg.subId.getId |>.append `compare |> mkIdent
  tg.namespaced do elaborate `(
    instance : LT $tg.idTerm := inferInstanceAs (LT $tg.subId)
    instance : DecidableLT $tg.idTerm := inferInstanceAs (DecidableLT $tg.subId)
    instance : LE $tg.idTerm := inferInstanceAs (LE $tg.subId)
    instance : DecidableLE $tg.idTerm := inferInstanceAs (DecidableLE $tg.subId)

    @[inherit_doc $bltSrc]
    protected def $bltId : $tg.idTerm → $tg.idTerm → Bool := $bltSrc
    @[inherit_doc $bleSrc]
    protected def $bleId : $tg.idTerm → $tg.idTerm → Bool := $bleSrc
    @[inherit_doc $bgtSrc]
    protected def $bgtId : $tg.idTerm → $tg.idTerm → Bool := $bgtSrc
    @[inherit_doc $bgeSrc]
    protected def $bgeId : $tg.idTerm → $tg.idTerm → Bool := $bgeSrc

    instance : Ord $tg.idTerm := inferInstanceAs (Ord $tg.subId)

    @[inherit_doc $compareSrc]
    protected def $compareId : $tg.idTerm → $tg.idTerm → Ordering := $compareSrc
  )

end TypeGen

declare_syntax_cat cvcCustomDefKw

syntax "def0% " : cvcCustomDefKw
syntax "def1% " : cvcCustomDefKw
syntax "def2% " : cvcCustomDefKw
syntax "def3% " : cvcCustomDefKw

syntax (name := cvcCustomDef)
  cvcCustomDefKw ident (ident)? " ← " ident
    ("( " ident " / " ident " )")?
: command

@[command_elab cvcCustomDef]
def elab_cvcCustomDef : CommandElab
| `( $kw:cvcCustomDefKw $id $[ $tParam? ]? ← $subId $[ ( $ofSubId? / $toSubId? ) ]? ) => do
  let tg ← TypeGen.mk id subId tParam? ofSubId? toSubId?
  match kw with
  | `(cvcCustomDefKw| def0%) => tg.elab0
  | `(cvcCustomDefKw| def1%) => tg.elab1
  | `(cvcCustomDefKw| def2%) => tg.elab2
  | `(cvcCustomDefKw| def3%) => tg.elab3
  | _ => throwUnsupportedSyntax
| _ => throwUnsupportedSyntax

end codeGen



/-! ## Re-exported from lean-cvc5

Three enums and one type are used raw rather than wrapped: `Kind` and `SortKind` because restating
a 320- or 23-variant enum buys nothing, `Op` because it is only ever produced and consumed by the
term API. They are re-exported here so that naming one does not mean reaching into `cvc5`.
-/

public section variable [Ω]

export cvc5 (Kind SortKind Op ProofRule ProofRewriteRule)

def1% Command ← cvc5.Command

def2% Datatype.Decl ← cvc5.DatatypeDecl
def2% Datatype ← cvc5.Datatype
def2% Datatype.Constructor.Decl ← cvc5.DatatypeConstructorDecl
def2% Datatype.Constructor ← cvc5.DatatypeConstructor
def2% Datatype.Selector ← cvc5.DatatypeSelector
def2% Grammar ← cvc5.Grammar



def3% Srt ← cvc5.Sort

namespace Srt

inductive Abstract
| array
| bitVec
| float
| finiteField
| function
| bag
| set
| seq
deriving Inhabited, DecidableEq, BEq, Ord, Hashable, Repr

namespace Abstract

protected def toString : (a : Srt.Abstract) → String
| array => "Array _ _"
| bitVec => "BitVec _"
| float => "Float _ _"
| finiteField => "FiniteField _"
| function => "_ → _"
| bag => "Bag _"
| set => "Set _"
| seq => "Seq _"

instance : ToString Srt.Abstract := ⟨Abstract.toString⟩

private def ofKind : (k : cvc5.SortKind) → Res Abstract
  | .ARRAY_SORT => return array
  | .BITVECTOR_SORT => return bitVec
  | .FLOATINGPOINT_SORT => return float
  | .FINITE_FIELD_SORT => return finiteField
  | .FUNCTION_SORT => return function
  | .BAG_SORT => return bag
  | k => throwInternal s!"sort kind `{k}` is not abstract-able"

def toKind : (a : Abstract) → cvc5.SortKind
  | array => .ARRAY_SORT
  | bitVec => .BITVECTOR_SORT
  | float => .FLOATINGPOINT_SORT
  | finiteField => .FINITE_FIELD_SORT
  | function => .FUNCTION_SORT
  | bag => .BAG_SORT
  | set => .SET_SORT
  | seq => .SEQUENCE_SORT

instance : Ord Abstract := ⟨fun a1 a2 => compare a1.ctorIdx a2.ctorIdx⟩

section variable (a1 a2 : Abstract)

protected def ble : Bool := a1.ctorIdx ≤ a2.ctorIdx
protected def blt : Bool := a1.ctorIdx < a2.ctorIdx

end

instance : LE Abstract := ⟨(Abstract.ble · ·)⟩
instance : DecidableLE Abstract := fun a1 a2 => if h : a1.ble a2 then isTrue h else isFalse h
instance : LT Abstract := ⟨(Abstract.blt · ·)⟩
instance : DecidableLT Abstract := fun a1 a2 => if h : a1.blt a2 then isTrue h else isFalse h

end Abstract
end Srt

/-- An array of `Srt`s. -/
abbrev Srts := Array Srt

namespace Srts

private def toUnsafe : Srts → Array cvc5.Sort := id
private def ofUnsafe : Array cvc5.Sort → Srts := id

end Srts



inductive Typ
| bool | int | real | string | regex | roundingMode
| bitVec (size : Nat)
| float (exp sig : Nat)
| finiteField (size : Nat)
| arrayTo (idx elm : Typ)
| bag (elm : Typ) | set (elm : Typ) | seq (elm : Typ)
/-- cvc5's `Nullable`, denoted Lean-side by `Option`.

A *structural* sort constructor like `set` or `seq`, not a declared datatype: building it twice
gives the same sort, so `toSrt` rebuilds it rather than looking it up. cvc5 implements it as a
monomorphized datatype underneath, one per element sort, which is invisible from here.
-/
| nullable (elm : Typ)
| prod (args : List Typ)
/-- A datatype, by the name it was declared under.

Only the name, because a declared sort cannot be rebuilt: cvc5 makes a *fresh* sort every time,
even from an identical declaration. `Typ.toSrt` therefore looks this up in the scope's registry
rather than reconstructing it, which is also why the case carries no constructors.
-/
| datatype (name : String)
| abstract (a : Srt.Abstract)
| function (dom : Typ) (cod : Typ)
| uninterpreted (name : String)
deriving Ord, Hashable

namespace Typ

/-! ### Decidable equality

`prod` makes `Typ` a *nested* inductive — it recurses through `List` — and no `deriving` handler
covers that, so equality is decided by hand: a boolean equality by mutual structural recursion,
proved reflexive and sound, then transported onto `DecidableEq`.

Two things shape the proofs. Reflexivity matches a single argument, so every case is diagonal and
there is nothing else to discharge. Soundness matches only the *first* argument and splits the
second with `cases`, because a catch-all in a dependent match is elaborated once against generic
scrutinees, where it cannot know the two constructors differ.
-/

mutual

/-- Structural equality. -/
protected def beq : Typ → Typ → Bool
  | bool, bool | int, int | real, real | string, string
  | regex, regex | roundingMode, roundingMode => true
  | bitVec s₁, bitVec s₂ => s₁ == s₂
  | float e₁ s₁, float e₂ s₂ => e₁ == e₂ && s₁ == s₂
  | finiteField s₁, finiteField s₂ => s₁ == s₂
  | arrayTo i₁ e₁, arrayTo i₂ e₂ => Typ.beq i₁ i₂ && Typ.beq e₁ e₂
  | bag e₁, bag e₂ | set e₁, set e₂ | seq e₁, seq e₂
  | nullable e₁, nullable e₂ => Typ.beq e₁ e₂
  | prod as₁, prod as₂ => Typ.beqList as₁ as₂
  | datatype n₁, datatype n₂ => n₁ == n₂
  -- `decide` rather than `==`: `Srt.Abstract` derives both `BEq` and `DecidableEq`, and nothing
  -- says the two agree, so `simp` cannot turn the boolean back into an equality
  | abstract a₁, abstract a₂ => decide (a₁ = a₂)
  | function d₁ c₁, function d₂ c₂ => Typ.beq d₁ d₂ && Typ.beq c₁ c₂
  | uninterpreted name₁, uninterpreted name₂ => name₁ == name₂
  | _, _ => false
-- `structural` and not the well-founded default: only a structural definition reduces, and
-- `decide` on a `Typ` equation needs it to
termination_by structural t => t

@[inherit_doc Typ.beq]
protected def beqList : List Typ → List Typ → Bool
  | [], [] => true
  | hd₁ :: tl₁, hd₂ :: tl₂ => Typ.beq hd₁ hd₂ && Typ.beqList tl₁ tl₂
  | _, _ => false
termination_by structural ts => ts

end

section
omit [Ω]

mutual

/-- `Typ.beq` is reflexive. -/
protected theorem beq_refl : (t : Typ) → Typ.beq t t = true
  | bool | int | real | string | regex | roundingMode => by simp [Typ.beq]
  | bitVec _ | finiteField _ | abstract _ | datatype _ => by simp [Typ.beq]
  | float _ _ => by simp [Typ.beq]
  | arrayTo i e => by simp [Typ.beq, Typ.beq_refl i, Typ.beq_refl e]
  | bag e | set e | seq e | nullable e => by simp [Typ.beq, Typ.beq_refl e]
  | prod ts => by simp [Typ.beq, Typ.beqList_refl ts]
  | function d c => by simp [Typ.beq, Typ.beq_refl d, Typ.beq_refl c]
  | uninterpreted name => by simp [Typ.beq]

@[inherit_doc Typ.beq_refl]
protected theorem beqList_refl : (ts : List Typ) → Typ.beqList ts ts = true
  | [] => by simp [Typ.beqList]
  | hd :: tl => by simp [Typ.beqList, Typ.beq_refl hd, Typ.beqList_refl tl]

end

mutual

/-- `Typ.beq` holds only of equals. -/
protected theorem eq_of_beq : (t₁ t₂ : Typ) → Typ.beq t₁ t₂ = true → t₁ = t₂
  | bool, t₂, h | int, t₂, h | real, t₂, h | string, t₂, h
  | regex, t₂, h | roundingMode, t₂, h => by cases t₂ <;> simp_all [Typ.beq]
  | bitVec _, t₂, h | finiteField _, t₂, h | abstract _, t₂, h | datatype _, t₂, h => by
    cases t₂ <;> simp_all [Typ.beq]
  | float _ _, t₂, h => by cases t₂ <;> simp_all [Typ.beq]
  | arrayTo _ _, t₂, h => by
    cases t₂ <;> simp_all [Typ.beq]
    exact ⟨Typ.eq_of_beq _ _ h.left, Typ.eq_of_beq _ _ h.right⟩
  | bag _, t₂, h | set _, t₂, h | seq _, t₂, h | nullable _, t₂, h => by
    cases t₂ <;> simp_all [Typ.beq]
    exact Typ.eq_of_beq _ _ h
  | prod _, t₂, h => by
    cases t₂ <;> simp_all [Typ.beq]
    exact Typ.eq_of_beqList _ _ h
  | function _ _, t₂, h => by
    cases t₂ <;> simp_all [Typ.beq]
    exact ⟨Typ.eq_of_beq _ _ h.left, Typ.eq_of_beq _ _ h.right⟩
  | uninterpreted name, t₂, h => by cases t₂ <;> simp_all [Typ.beq]

@[inherit_doc Typ.eq_of_beq]
protected theorem eq_of_beqList : (ts₁ ts₂ : List Typ) → Typ.beqList ts₁ ts₂ = true → ts₁ = ts₂
  | [], ts₂, h => by cases ts₂ <;> simp_all [Typ.beqList]
  | _ :: _, ts₂, h => by
    cases ts₂ <;> simp_all [Typ.beqList]
    exact ⟨Typ.eq_of_beq _ _ h.left, Typ.eq_of_beqList _ _ h.right⟩

end

instance instDecidableEq : DecidableEq Typ := fun t₁ t₂ =>
  decidable_of_iff (Typ.beq t₁ t₂ = true)
    ⟨Typ.eq_of_beq t₁ t₂, fun h => h ▸ Typ.beq_refl t₁⟩

end


protected def toString (t : Typ) (paren : Bool := false) : String :=
  let paren (s : String) := if paren then s!"({s})" else s
  match t with
  | bool => "Bool" | int => "Int" | real => "Real" | string => "String"
  | regex => "Regex" | roundingMode => "RoundingMode"
  | bitVec size => paren s!"BitVec {size}"
  | float exp sig => paren s!"Float {exp} {sig}"
  | finiteField size => paren s!"FiniteField {size}"
  | arrayTo idx elm => paren s!"Array {idx.toString true} {elm.toString true}"
  | bag elm => paren s!"Bag {elm.toString true}"
  | set elm => paren s!"Set {elm.toString true}"
  | seq elm => paren s!"Seq {elm.toString true}"
  | nullable elm => paren s!"Option {elm.toString true}"
  | prod [] => "Unit"
  | prod [α] => s!"(× {α.toString})"
  | prod args => paren (tupleArgsFold args)
  | datatype name => name
  | abstract a => paren s!"Abstract {a}"
  | function dom cod => paren s!"{dom.toString false} → {cod.toString false}"
  | uninterpreted name => paren s!"Uninterpreted `{name}`"
where
  tupleArgsFold : (args : List Typ) → (acc : String := "") → String
    | [], "" => "Unit"
    | [ty], "" => s!"(× {ty.toString})"
    | [], acc => acc
    | hd::tl, acc =>
      if acc.isEmpty then tupleArgsFold tl (hd.toString true)
      else tupleArgsFold tl s!"{acc} × {hd.toString true}"

instance : ToString Typ := ⟨Typ.toString⟩

end Typ

class ToTyp (α : Type) where
  /-- `Typ` associated to a type through `ToTyp`. -/
  typ : Typ
