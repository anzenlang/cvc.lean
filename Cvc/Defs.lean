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
def2% Datatype.Ctor.Decl ← cvc5.DatatypeConstructorDecl
def2% Datatype.Ctor ← cvc5.DatatypeConstructor
def2% Datatype.Selector ← cvc5.DatatypeSelector
def2% Grammar ← cvc5.Grammar



def3% Srt ← cvc5.Sort

namespace Srt

/-- A sort abstracted over its parameters, of a known kind.

Only the four kinds cvc5 really keeps abstract. An abstract *container* is not one of them:
`mkAbstractSort SET_SORT` is literally `mkSetSort ?`, of sort kind `SET_SORT`, so it is
`Typ.set .any` rather than an abstract sort — verified, not assumed.
-/
inductive Abstract
| bitVec
| float
| finiteField
| function
deriving Inhabited, DecidableEq, BEq, Ord, Hashable, Repr

namespace Abstract

protected def toString : (a : Srt.Abstract) → String
| bitVec => "BitVec _"
| float => "Float _ _"
| finiteField => "FiniteField _"
| function => "_ → _"

instance : ToString Srt.Abstract := ⟨Abstract.toString⟩

private def ofKind : (k : cvc5.SortKind) → Res Abstract
  | .BITVECTOR_SORT => return bitVec
  | .FLOATINGPOINT_SORT => return float
  | .FINITE_FIELD_SORT => return finiteField
  | .FUNCTION_SORT => return function
  | k => throwInternal s!"sort kind `{k}` is not abstract-able"

def toKind : (a : Abstract) → cvc5.SortKind
  | bitVec => .BITVECTOR_SORT
  | float => .FLOATINGPOINT_SORT
  | finiteField => .FINITE_FIELD_SORT
  | function => .FUNCTION_SORT

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



/-! ## Sort descriptions

`Typ` describes a sort purely Lean-side, and `Typ?` is `Typ` plus the sorts cvc5 calls *abstract*.

The split is cvc5's own **first-class** distinction, not a convention of ours. A non-first-class
sort — the fully abstract `?`, or one of `?BITVECTOR_TYPE`, `?FLOATINGPOINT_TYPE`,
`?FINITE_FIELD_TYPE`, `?->` — is accepted as a set, bag or sequence element, as either parameter of
an array, and as a function *codomain*. cvc5 rejects it everywhere else: as a nullable element, a
tuple component, or a function *domain*. So `Typ?` sits at exactly the first set of positions and
`Typ` at the second, and a `Typ` that cvc5 would refuse cannot be written.

Two consequences worth knowing:

- **No `Typ` denotes a sort cvc5 would reject as ill-sorted**, which is what the split buys.
  `Typ.toSrt` can still fail, but only on `datatype`/`uninterpreted`, whose name has to be in the
  scope's registry — a fact about the scope, not about the description.
- an abstract *container* is not an abstract sort to cvc5: `mkAbstractSort SET_SORT` is literally
  `(Set ?)`, of sort kind `SET_SORT`. So it is `Typ.set .any` here, and `Abstract` carries only the
  four kinds cvc5 really keeps abstract.
-/

mutual

/-- A sort, described Lean-side. Every `Typ` is a *first-class* sort. -/
inductive Typ
| bool | int | real | string | regex | roundingMode
| bitVec (size : Nat)
| float (exp sig : Nat)
| finiteField (size : Nat)
| arrayTo (idx elm : Typ?)
| bag (elm : Typ?) | set (elm : Typ?) | seq (elm : Typ?)
/-- cvc5's `Nullable`, denoted Lean-side by `Option`.

A *structural* sort constructor like `set` or `seq`, not a declared datatype: building it twice
gives the same sort, so `toSrt` rebuilds it rather than looking it up. cvc5 implements it as a
mono-morphized datatype underneath, one per element sort, which is invisible from here.

The element is a `Typ`: cvc5 rejects `(Nullable ?)`.
-/
| nullable (elm : Typ)
/-- A tuple. The components are `Typ`s: cvc5 rejects an abstract component. -/
| prod (args : List Typ)
/-- A record: named, ordered, first-class fields.

*Structural*, like `set` or `prod` and unlike a datatype: cvc5 builds the same sort from the same
fields, so `toSrt` rebuilds it rather than looking it up. The order is part of the sort —
`{a : Int, b : Bool}` and `{b : Bool, a : Int}` are **different** — which is why this is a list and
not a map. The fields are `Typ`s: cvc5 refuses a field that is not first-class.

cvc5 implements it as a mono-morphized datatype with one constructor and one selector per field,
named after the fields, which is how `Srt.toTyp` reads one back.
-/
| record (fields : List (String × Typ))
/-- A datatype, by the name it was declared under.

Only the name, because a declared sort cannot be rebuilt: cvc5 makes a *fresh* sort every time,
even from an identical declaration. `Typ.toSrt` therefore looks this up in the scope's registry
rather than reconstructing it, which is also why the case carries no constructors.
-/
| datatype (name : String)
/-- A function. The domain is a `Typ` and the codomain a `Typ?`: cvc5 accepts `(-> Int ?)` and
rejects `(-> ? Int)`. -/
| function (dom : Typ) (cod : Typ?)
/-- An uninterpreted sort, by the name it was declared under — see `datatype`. -/
| uninterpreted (name : String)

/-- A `Typ`, or one of the sorts cvc5 calls abstract.

Only where cvc5 permits a non-first-class sort; see the module note above.
-/
inductive Typ?
/-- An ordinary, first-class sort. -/
| typ (t : Typ)
/-- cvc5's fully abstract sort `?`. -/
| any
/-- An abstract sort of a known kind, `?BITVECTOR_TYPE` and friends. -/
| abstract (a : Srt.Abstract)

end

/-- Lexicographic order on pairs, which core does not provide.

`local`, and only so that `Ord` derives: `record`'s fields are a `List (String × Typ)`, and while
`Ord (List ·)` exists, `Ord (· × ·)` does not — that, and not any circularity, is what stops the
derivation. Keeping it local means the library does not impose an orphan instance on its users.
-/
local instance [Ord α] [Ord β] : Ord (α × β) where
  compare | (a₁, b₁), (a₂, b₂) => match compare a₁ a₂ with | .eq => compare b₁ b₂ | o => o

deriving instance Ord for Typ, Typ?
deriving instance Hashable for Typ, Typ?

/-- Every `Typ` is a `Typ?`, so the wrapping is implicit. -/
instance : Coe Typ Typ? := ⟨.typ⟩

namespace Typ?

/-! ### `Typ`'s constructors, mirrored

Dot notation resolves against the expected type, so `.set .int` would look for `Typ?.int` and fail.
These restore it, and `@[match_pattern]` makes them usable in patterns as well as in terms.
-/

@[match_pattern] abbrev bool : Typ? := .typ .bool
@[match_pattern] abbrev int : Typ? := .typ .int
@[match_pattern] abbrev real : Typ? := .typ .real
@[match_pattern] abbrev string : Typ? := .typ .string
@[match_pattern] abbrev regex : Typ? := .typ .regex
@[match_pattern] abbrev roundingMode : Typ? := .typ .roundingMode
@[match_pattern] abbrev bitVec (size : Nat) : Typ? := .typ (.bitVec size)
@[match_pattern] abbrev float (exp sig : Nat) : Typ? := .typ (.float exp sig)
@[match_pattern] abbrev finiteField (size : Nat) : Typ? := .typ (.finiteField size)
@[match_pattern] abbrev arrayTo (idx elm : Typ?) : Typ? := .typ (.arrayTo idx elm)
@[match_pattern] abbrev bag (elm : Typ?) : Typ? := .typ (.bag elm)
@[match_pattern] abbrev set (elm : Typ?) : Typ? := .typ (.set elm)
@[match_pattern] abbrev seq (elm : Typ?) : Typ? := .typ (.seq elm)
@[match_pattern] abbrev nullable (elm : Typ) : Typ? := .typ (.nullable elm)
@[match_pattern] abbrev prod (args : List Typ) : Typ? := .typ (.prod args)
@[match_pattern] abbrev record (fields : List (String × Typ)) : Typ? := .typ (.record fields)
@[match_pattern] abbrev datatype (name : String) : Typ? := .typ (.datatype name)
@[match_pattern] abbrev function (dom : Typ) (cod : Typ?) : Typ? := .typ (.function dom cod)
@[match_pattern] abbrev uninterpreted (name : String) : Typ? := .typ (.uninterpreted name)

end Typ?



/-! ### Decidable equality

`prod` makes `Typ` a *nested* inductive — it recurses through `List` — and it is mutual with
`Typ?` besides, so no `deriving` handler covers equality: it is decided by hand, as a boolean
equality by mutual structural recursion, proved reflexive and sound, then transported onto
`DecidableEq`.

Two things shape the proofs. Reflexivity matches a single argument, so every case is diagonal and
there is nothing else to discharge. Soundness matches only the *first* argument and splits the
second with `cases`, because a catch-all in a dependent match is elaborated once against generic
scrutinees, where it cannot know the two constructors differ.
-/

mutual

/-- Structural equality. -/
protected def Typ.beq : Typ → Typ → Bool
  | .bool, .bool | .int, .int | .real, .real | .string, .string
  | .regex, .regex | .roundingMode, .roundingMode => true
  | .bitVec s₁, .bitVec s₂ => s₁ == s₂
  | .float e₁ s₁, .float e₂ s₂ => e₁ == e₂ && s₁ == s₂
  | .finiteField s₁, .finiteField s₂ => s₁ == s₂
  | .arrayTo i₁ e₁, .arrayTo i₂ e₂ => Cvc.Typ?.beq i₁ i₂ && Cvc.Typ?.beq e₁ e₂
  | .bag e₁, .bag e₂ | .set e₁, .set e₂ | .seq e₁, .seq e₂ => Cvc.Typ?.beq e₁ e₂
  | .nullable e₁, .nullable e₂ => Cvc.Typ.beq e₁ e₂
  | .prod as₁, .prod as₂ => Cvc.Typ.beqList as₁ as₂
  | .record fs₁, .record fs₂ => Cvc.Typ.beqFields fs₁ fs₂
  | .datatype n₁, .datatype n₂ => n₁ == n₂
  | .function d₁ c₁, .function d₂ c₂ => Cvc.Typ.beq d₁ d₂ && Cvc.Typ?.beq c₁ c₂
  | .uninterpreted name₁, .uninterpreted name₂ => name₁ == name₂
  | _, _ => false
-- `structural` and not the well-founded default: only a structural definition reduces, and
-- `decide` on a `Typ` equation needs it to
termination_by structural t => t

@[inherit_doc Cvc.Typ.beq]
protected def Typ.beqList : List Typ → List Typ → Bool
  | [], [] => true
  | hd₁ :: tl₁, hd₂ :: tl₂ => Cvc.Typ.beq hd₁ hd₂ && Cvc.Typ.beqList tl₁ tl₂
  | _, _ => false
termination_by structural ts => ts

@[inherit_doc Cvc.Typ.beq]
protected def Typ.beqFields : List (String × Typ) → List (String × Typ) → Bool
  | [], [] => true
  | (n₁, t₁) :: r₁, (n₂, t₂) :: r₂ => n₁ == n₂ && Cvc.Typ.beq t₁ t₂ && Cvc.Typ.beqFields r₁ r₂
  | _, _ => false
termination_by structural fs => fs

@[inherit_doc Cvc.Typ.beq]
protected def Typ?.beq : Typ? → Typ? → Bool
  | .typ t₁, .typ t₂ => Cvc.Typ.beq t₁ t₂
  | .any, .any => true
  -- `decide` rather than `==`: `Srt.Abstract` derives both `BEq` and `DecidableEq`, and nothing
  -- says the two agree, so `simp` cannot turn the boolean back into an equality
  | .abstract a₁, .abstract a₂ => decide (a₁ = a₂)
  | _, _ => false
termination_by structural t => t

end

section
omit [Ω]

mutual

/-- `Cvc.Typ.beq` is reflexive. -/
protected theorem Typ.beq_refl : (t : Typ) → Cvc.Typ.beq t t = true
  | .bool | .int | .real | .string | .regex | .roundingMode => by simp [Cvc.Typ.beq]
  | .bitVec _ | .finiteField _ | .datatype _ => by simp [Cvc.Typ.beq]
  | .float _ _ => by simp [Cvc.Typ.beq]
  | .arrayTo i e => by simp [Cvc.Typ.beq, Cvc.Typ?.beq_refl i, Cvc.Typ?.beq_refl e]
  | .bag e | .set e | .seq e => by simp [Cvc.Typ.beq, Cvc.Typ?.beq_refl e]
  | .nullable e => by simp [Cvc.Typ.beq, Cvc.Typ.beq_refl e]
  | .prod ts => by simp [Cvc.Typ.beq, Cvc.Typ.beqList_refl ts]
  | .record fs => by simp [Cvc.Typ.beq, Cvc.Typ.beqFields_refl fs]
  | .function d c => by simp [Cvc.Typ.beq, Cvc.Typ.beq_refl d, Cvc.Typ?.beq_refl c]
  | .uninterpreted name => by simp [Cvc.Typ.beq]

@[inherit_doc Cvc.Typ.beq_refl]
protected theorem Typ.beqList_refl : (ts : List Typ) → Cvc.Typ.beqList ts ts = true
  | [] => by simp [Cvc.Typ.beqList]
  | hd :: tl => by simp [Cvc.Typ.beqList, Cvc.Typ.beq_refl hd, Cvc.Typ.beqList_refl tl]

@[inherit_doc Cvc.Typ.beq_refl]
protected theorem Typ.beqFields_refl : (fs : List (String × Typ)) → Cvc.Typ.beqFields fs fs = true
  | [] => by simp [Cvc.Typ.beqFields]
  | (_, t) :: tl => by simp [Cvc.Typ.beqFields, Cvc.Typ.beq_refl t, Cvc.Typ.beqFields_refl tl]

@[inherit_doc Cvc.Typ.beq_refl]
protected theorem Typ?.beq_refl : (t : Typ?) → Cvc.Typ?.beq t t = true
  | .typ t => by simp [Cvc.Typ?.beq, Cvc.Typ.beq_refl t]
  | .any => by simp [Cvc.Typ?.beq]
  | .abstract _ => by simp [Cvc.Typ?.beq]

end

mutual

/-- `Cvc.Typ.beq` holds only of equals. -/
protected theorem Typ.eq_of_beq : (t₁ t₂ : Typ) → Cvc.Typ.beq t₁ t₂ = true → t₁ = t₂
  | .bool, t₂, h | .int, t₂, h | .real, t₂, h | .string, t₂, h
  | .regex, t₂, h | .roundingMode, t₂, h => by cases t₂ <;> simp_all [Cvc.Typ.beq]
  | .bitVec _, t₂, h | .finiteField _, t₂, h | .datatype _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ.beq]
  | .float _ _, t₂, h => by cases t₂ <;> simp_all [Cvc.Typ.beq]
  | .arrayTo _ _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ.beq]
    exact ⟨Cvc.Typ?.eq_of_beq _ _ h.left, Cvc.Typ?.eq_of_beq _ _ h.right⟩
  | .bag _, t₂, h | .set _, t₂, h | .seq _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ.beq]
    exact Cvc.Typ?.eq_of_beq _ _ h
  | .nullable _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ.beq]
    exact Cvc.Typ.eq_of_beq _ _ h
  | .prod _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ.beq]
    exact Cvc.Typ.eq_of_beqList _ _ h
  | .record _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ.beq]
    exact Cvc.Typ.eq_of_beqFields _ _ h
  | .function _ _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ.beq]
    exact ⟨Cvc.Typ.eq_of_beq _ _ h.left, Cvc.Typ?.eq_of_beq _ _ h.right⟩
  | .uninterpreted name, t₂, h => by cases t₂ <;> simp_all [Cvc.Typ.beq]

@[inherit_doc Cvc.Typ.eq_of_beq]
protected theorem Typ.eq_of_beqList
: (ts₁ ts₂ : List Typ) → Cvc.Typ.beqList ts₁ ts₂ = true → ts₁ = ts₂
  | [], ts₂, h => by cases ts₂ <;> simp_all [Cvc.Typ.beqList]
  | _ :: _, ts₂, h => by
    cases ts₂ <;> simp_all [Cvc.Typ.beqList]
    exact ⟨Cvc.Typ.eq_of_beq _ _ h.left, Cvc.Typ.eq_of_beqList _ _ h.right⟩

@[inherit_doc Cvc.Typ.eq_of_beq]
protected theorem Typ.eq_of_beqFields
: (fs₁ fs₂ : List (String × Typ)) → Cvc.Typ.beqFields fs₁ fs₂ = true → fs₁ = fs₂
  | [], fs₂, h => by cases fs₂ <;> simp_all [Cvc.Typ.beqFields]
  -- the head pair is destructured rather than projected: `t₁` has to be a genuine subterm for the
  -- recursion to be structural, `Typ` being nested through `List (String × ·)` here
  | (n₁, t₁) :: r₁, fs₂, h => by
    cases fs₂ with
    | nil => simp_all [Cvc.Typ.beqFields]
    | cons hd r₂ =>
      obtain ⟨n₂, t₂⟩ := hd
      simp_all [Cvc.Typ.beqFields]
      refine ⟨?_, Cvc.Typ.eq_of_beqFields _ _ h.right⟩
      have := Cvc.Typ.eq_of_beq _ _ h.left.right
      simp_all

@[inherit_doc Cvc.Typ.eq_of_beq]
protected theorem Typ?.eq_of_beq : (t₁ t₂ : Typ?) → Cvc.Typ?.beq t₁ t₂ = true → t₁ = t₂
  | .typ _, t₂, h => by
    cases t₂ <;> simp_all [Cvc.Typ?.beq]
    exact Cvc.Typ.eq_of_beq _ _ h
  | .any, t₂, h => by cases t₂ <;> simp_all [Cvc.Typ?.beq]
  | .abstract _, t₂, h => by cases t₂ <;> simp_all [Cvc.Typ?.beq]

end

instance Typ.instDecidableEq : DecidableEq Typ := fun t₁ t₂ =>
  decidable_of_iff (Cvc.Typ.beq t₁ t₂ = true)
    ⟨Cvc.Typ.eq_of_beq t₁ t₂, fun h => h ▸ Cvc.Typ.beq_refl t₁⟩

instance Typ?.instDecidableEq : DecidableEq Typ? := fun t₁ t₂ =>
  decidable_of_iff (Cvc.Typ?.beq t₁ t₂ = true)
    ⟨Cvc.Typ?.eq_of_beq t₁ t₂, fun h => h ▸ Cvc.Typ?.beq_refl t₁⟩

end



mutual

/-- String representation. -/
protected def Typ.toString (t : Typ) (paren : Bool := false) : String :=
  let paren (s : String) := if paren then s!"({s})" else s
  match t with
  | .bool => "Bool" | .int => "Int" | .real => "Real" | .string => "String"
  | .regex => "Regex" | .roundingMode => "RoundingMode"
  | .bitVec size => paren s!"BitVec {size}"
  | .float exp sig => paren s!"Float {exp} {sig}"
  | .finiteField size => paren s!"FiniteField {size}"
  | .arrayTo idx elm => paren s!"Array {Cvc.Typ?.toString idx true} {Cvc.Typ?.toString elm true}"
  | .bag elm => paren s!"Bag {Cvc.Typ?.toString elm true}"
  | .set elm => paren s!"Set {Cvc.Typ?.toString elm true}"
  | .seq elm => paren s!"Seq {Cvc.Typ?.toString elm true}"
  | .nullable elm => paren s!"Option {Cvc.Typ.toString elm true}"
  | .prod [] => "Unit"
  | .prod [α] => s!"(× {Cvc.Typ.toString α})"
  | .prod args => paren (Cvc.Typ.tupleArgsFold args "")
  | .record fields => paren s!"\{{Cvc.Typ.fieldsFold fields ""}}"
  | .datatype name => name
  | .function dom cod => paren s!"{Cvc.Typ.toString dom true} → {Cvc.Typ?.toString cod false}"
  | .uninterpreted name => paren s!"Uninterpreted `{name}`"

@[inherit_doc Cvc.Typ.toString]
protected def Typ?.toString (t : Typ?) (paren : Bool := false) : String :=
  match t with
  | .typ t => Cvc.Typ.toString t paren
  | .any => "?"
  | .abstract a => if paren then s!"(Abstract {a})" else s!"Abstract {a}"

@[inherit_doc Cvc.Typ.toString]
protected def Typ.fieldsFold : (fields : List (String × Typ)) → (acc : String) → String
  | [], acc => acc
  | (name, ty) :: tl, acc =>
    let field := s!"{name} : {Cvc.Typ.toString ty}"
    Cvc.Typ.fieldsFold tl (if acc.isEmpty then field else s!"{acc}, {field}")

@[inherit_doc Cvc.Typ.toString]
protected def Typ.tupleArgsFold : (args : List Typ) → (acc : String) → String
  | [], "" => "Unit"
  | [ty], "" => s!"(× {Cvc.Typ.toString ty})"
  | [], acc => acc
  | hd::tl, acc =>
    if acc.isEmpty then Cvc.Typ.tupleArgsFold tl (Cvc.Typ.toString hd true)
    else Cvc.Typ.tupleArgsFold tl s!"{acc} × {Cvc.Typ.toString hd true}"

end

instance : ToString Typ := ⟨(Cvc.Typ.toString · )⟩
instance : ToString Typ? := ⟨(Cvc.Typ?.toString · )⟩

class ToTyp (α : Type) where
  /-- `Typ` associated to a type through `ToTyp`. -/
  typ : Typ
