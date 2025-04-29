/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Init.Init
import Cvc.Init.Logic
import Cvc.Init.Option



namespace Cvc


-- open Res renaming failInternal → fail


-- inductive Srt
-- | bool | int
-- | bitVec (size : Nat)
-- | array (idx elm : Srt)
-- | tuple (srts : Array Srt)
-- | function (dom : Array Srt) (cod : Srt)
-- deriving Inhabited, Hashable

-- namespace Srt

-- mutual

-- instance instDecidableEqListSrt : DecidableEq (List Srt)
-- | hd1::tl1, hd2::tl2 => by
--   cases hd1.instDecidableEq hd2
--   case isFalse h => exact isFalse (by simp only [List.cons.injEq, h, false_and, not_false_eq_true])
--   cases instDecidableEqListSrt tl1 tl2
--   case isFalse h => exact isFalse (by simp only [List.cons.injEq, h, and_false, not_false_eq_true])
--   exact isTrue (by simp [*])
-- | [], _::_ | _::_, [] => isFalse (by simp only [reduceCtorEq, not_false_eq_true])
-- | [], [] => isTrue rfl

-- instance instDecidableEqArraySrt : DecidableEq (Array Srt)
-- | ⟨l1⟩, ⟨l2⟩ => by
--   cases instDecidableEqListSrt l1 l2
--   · apply isFalse ; simp only [Array.mk.injEq, not_false_eq_true, *]
--   · apply isTrue ; simp only [*]

-- instance instDecidableEq : DecidableEq Srt
-- | .bool => fun s2 => by
--   cases s2 <;> try (apply isFalse ; simp only [reduceCtorEq, not_false_eq_true] ; done)
--   case bool => exact isTrue rfl
-- | .int => fun s2 => by
--   cases s2 <;> try (apply isFalse ; simp only [reduceCtorEq, not_false_eq_true] ; done)
--   case int => exact isTrue rfl
-- | .bitVec n1 => fun s2 => by
--   cases s2 <;> try (apply isFalse ; simp only [reduceCtorEq, not_false_eq_true] ; done)
--   case bitVec n2 =>
--     if h : n1 = n2
--     then apply isTrue ; simp [h]
--     else apply isFalse ; simp [h]
-- | .array idx1 elm1 => fun s2 => by
--   cases s2 <;> try (apply isFalse ; simp only [reduceCtorEq, not_false_eq_true] ; done)
--   case array idx2 elm2 =>
--   cases instDecidableEq idx1 idx2
--   <;> cases instDecidableEq elm1 elm2
--   <;> try (
--     apply isFalse
--     simp only [array.injEq, and_false, false_and, not_false_eq_true, *]
--     done
--   )
--   apply isTrue ; simp only [*]
-- | .tuple prod1 => fun s2 => by
--   cases s2 <;> try (apply isFalse ; simp only [reduceCtorEq, not_false_eq_true] ; done)
--   case tuple prod2 =>
--   cases instDecidableEqArraySrt prod1 prod2
--   · apply isFalse ; simp only [tuple.injEq, not_false_eq_true, *]
--   · apply isTrue ; simp only [*]
-- | .function dom1 elm1 => fun s2 => by
--   cases s2 <;> try (apply isFalse ; simp only [reduceCtorEq, not_false_eq_true] ; done)
--   case function dom2 elm2 =>
--   cases instDecidableEqArraySrt dom1 dom2
--   <;> cases instDecidableEq elm1 elm2
--   <;> try (
--     apply isFalse
--     simp only [function.injEq, and_false, false_and, not_false_eq_true, *]
--     done
--   )
--   apply isTrue ; simp only [*]

-- end



-- protected
-- def toString : Srt → String
-- | .bool => "Bool"
-- | .int => "Int"
-- | .bitVec n => s!"BitVec {n}"
-- | .array idx elm => s!"Array ({idx.toString}) ({elm.toString})"
-- | .tuple prod => Id.run do
--   let mut s := ""
--   for srt in prod do
--     if s.isEmpty
--     then s := srt.toString
--     else s := s!"{s} × {srt.toString}"
--   s
-- | .function dom cod =>
--   if dom.isEmpty then cod.toString
--   else
--     let dom :=
--       "" |> dom.foldl fun s d => if s.isEmpty then d.toString else s!"{s} × ({d.toString})"
--     s!"({dom}) → ({cod.toString})"

-- instance : ToString Srt := ⟨Srt.toString⟩

-- def ofUnsafe (s : cvc5.Sort) : (maxDepth : Nat := 100_000) → Res Srt
-- | maxDepth + 1 => do
--   let ofUnsafe := ofUnsafe (maxDepth := maxDepth)
--   match s.getKind with
--   | .ARRAY_SORT =>
--     let idx ← s.getArrayIndexSort >>= ofUnsafe
--     let elm ← s.getArrayElementSort >>= ofUnsafe
--     return .array idx elm
--   | .BOOLEAN_SORT => return .bool
--   | .BITVECTOR_SORT =>
--     let size ← s.getBitVectorSize
--     return .bitVec size.toNat
--   | .FUNCTION_SORT =>
--     let doms ← s.getFunctionDomainSorts >>= Array.mapM ofUnsafe
--     let cod ← s.getFunctionCodomainSort >>= ofUnsafe
--     return .function doms cod
--   | .INTEGER_SORT => return .int
--   | k => fail s!"unexpected/unsupported sort-kind `{k}`"
-- | 0 => fail "maximum depth reached during `cvc5.Sort → Srt` conversion"

-- def FArray (Idx : Type) (Elm : Type) : Type :=
--   List (Idx × Elm)

-- namespace FArray

-- def ofList : List (Idx × Elm) → FArray Idx Elm := id

-- def empty : FArray Idx Elm := ofList []

-- def store [DecidableEq Idx] (key : Idx) (val : Elm) : (a : FArray Idx Elm) → FArray Idx Elm
-- | (key', val') :: tail =>
--   if key = key' then
--     (key, val) :: tail
--   else
--     (key', val') :: store key val tail
-- | [] => [(key, val)]

-- def select [DecidableEq Idx] [Inhabited Elm] (key : Idx) : (a : FArray Idx Elm) → Elm
-- | (key', val) :: tail =>
--   if key = key' then val else select key tail
-- | [] => default

-- end FArray


-- protected
-- class OfType (α : Type) where
--   srt : Srt

-- abbrev ofType (α : Type) [T : Srt.OfType α] : Srt :=
--   T.srt

-- instance : Srt.OfType Bool := ⟨.bool⟩
-- instance : Srt.OfType Int := ⟨.int⟩
-- instance : Srt.OfType (BitVec n) := ⟨.bitVec n⟩
-- instance [Srt.OfType Idx] [Srt.OfType Elm] : Srt.OfType (FArray Idx Elm) :=
--   ⟨.array (ofType Idx) (ofType Elm)⟩
-- instance [Srt.OfType Dom] [Srt.OfType Cod] : Srt.OfType (Dom → Cod) :=
--   ⟨.function #[(ofType Dom)] (ofType Cod)⟩

-- end Srt



-- open cvc5 renaming TermManager → Tm

-- structure Term (α : Type) : Type extends Srt.OfType α where
-- private ofUnsafe'' ::
--   toUnsafe : cvc5.Term

-- namespace Term

-- private
-- def ofUnsafe' (α : Type) [I : Srt.OfType α] (toUnsafe : cvc5.Term) : Term α :=
--   ofUnsafe'' I toUnsafe

-- private
-- def ofUnsafe [I : Srt.OfType α] (toUnsafe : cvc5.Term) : Term α :=
--   ofUnsafe' α toUnsafe

-- def mkBool (tm : Tm) (b : Bool) : Term Bool :=
--   ofUnsafe <| tm.mkBoolean b

-- def mkEq (tm : Tm) (lft rgt : Term α) : Res (Term Bool) := do
--   let term ← tm.mkTerm .EQUAL #[lft.toUnsafe, rgt.toUnsafe]
--   return ofUnsafe term

-- def kind (t : Term α) : cvc5.Kind := t.toUnsafe.getKind
-- def kids (t : Term α) : Array cvc5.Term := t.toUnsafe.getChildren

-- inductive Variant : Srt → Type
-- | funSym (name : String) (srt : Srt) (t : cvc5.Term) : Variant srt
-- | bool (b : Bool) : Variant .bool
-- | int (i : Int) : Variant .int
-- | equal (lft rhs : Variant α) : Variant .bool
-- | store (arr : Variant (.array idx elm))
--   (key : Variant idx) (val : Variant elm)
-- : Variant (.array idx elm)
-- | select (arr : Variant (.array idx elm))
--   (val : Variant idx)
-- : Variant elm
-- deriving Hashable -- , DecidableEq

-- namespace Variant

-- protected
-- def toString : Variant srt → String
-- | .funSym name srt _ => s!"{name}"
-- | .bool b => toString b
-- | .int i => toString i
-- | .equal lhs rhs => s!"{lhs.toString} = {rhs.toString}"
-- | .store arr key val => s!"({arr.toString}).store ({key.toString}) ({val.toString})"
-- | .select arr key => s!"({arr.toString}).select ({key.toString})"

-- instance : ToString (Variant srt) := ⟨Variant.toString⟩

-- end Variant


-- open Res renaming failInternal → fail in
-- def unsafeToVariant (t : cvc5.Term) : (maxDepth : Nat := 100_000) → Res ((α : Srt) × Variant α)
-- | maxDepth + 1 =>
--   match t.getKind with
--   | .CONST_BOOLEAN => do
--     let b ← t.getBooleanValue
--     return ⟨.bool, .bool b⟩
--   | .CONST_INTEGER => do
--     let i ← t.getIntegerValue
--     return ⟨.int, .int i⟩
--   | .CONSTANT => do
--     let name ← t.getSymbol
--     let srt ← Srt.ofUnsafe t.getSort
--     return ⟨srt, .funSym name srt t⟩
--   | .EQUAL => do
--     let kids := t.getChildren
--     let ⟨lftSrt, lft⟩ ← unsafeToVariant kids[0]! maxDepth
--     let ⟨rgtSrt, rgt⟩ ← unsafeToVariant kids[1]! maxDepth
--     if h_Srt : rgtSrt = lftSrt then
--       return ⟨.bool, .equal lft <| h_Srt ▸ rgt⟩
--     else fail s!"illegal equality between\n- `{lft} : {lftSrt}`\n- `{rgt} : {rgtSrt}`"
--   | .STORE => do
--     let kids := t.getChildren
--     let ⟨arrSrt, arr⟩ ← unsafeToVariant kids[0]! maxDepth
--     if let .array idx elm := arrSrt then
--       let ⟨keySrt, key⟩ ← unsafeToVariant kids[1]! maxDepth
--       if h_key : keySrt = idx then
--         let ⟨valSrt, val⟩ ← unsafeToVariant kids[2]! maxDepth
--         if h_val : valSrt = elm then
--           return ⟨.array idx elm, .store arr (h_key ▸ key) (h_val ▸ val)⟩
--         else fail s!"expected elem-sort `{elm}` for `store`, got `{valSrt}`"
--       else fail s!"expected index-sort `{idx}` for `store`, got `{keySrt}`"
--     else fail s!"expected array-sort for `store` term-kind, got `{arrSrt}`"
--   | .SELECT => do
--     let kids := t.getChildren
--     let ⟨arrSrt, arr⟩ ← unsafeToVariant kids[0]! maxDepth
--     let ⟨keySrt, key⟩ ← unsafeToVariant kids[1]! maxDepth
--     if let .array idx elm := arrSrt then
--       if h_key : keySrt = idx then
--         return ⟨elm, .select arr (h_key ▸ key)⟩
--       else fail s!"expected index-sort `{idx}` for `select`, got `{keySrt}`"
--     else fail s!"expected array-sort for `store` term-kind, got `{arrSrt}`"
--   | k => fail s!"unsupported/unexpected term-kind `{k}`"
-- | 0 => fail "maximum depth reached during `Term → Term.Variant` conversion"

-- def toVariant (t : Term α) : Res (Variant t.srt) := do
--   let ⟨srt, variant⟩ ← unsafeToVariant t.toUnsafe
--   if h : srt = t.srt
--   then return h ▸ variant
--   else Res.failInternal s!"conversion to variant failed: expected sort `{t.srt}`, got `{srt}`"

-- end Term
