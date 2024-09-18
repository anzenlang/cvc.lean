/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import CvcTest.Tactic.Init



namespace Cvc.Tactic.Test


abbrev injective (f : α → β) : Prop :=
  ∀ (a1 a2 : α), f a1 = f a2 → a1 = a2



section bitvec

/--
warning: goal seems falsifiable, **it might not be provable**
---
info: goal is **not** falsifiable ✅
-/
#test
theorem bv_toFin_injective : injective (BitVec.toFin : BitVec n → _) := by
  falsifiable? -- (verbose)
  intro a1 a2 h
  cases a1 ; cases a2
  falsifiable? -- (verbose)
  simp at h
  simp [h]

end bitvec



section algebra

class Comm (α : Type) (law : α → α → α) where
  comm : ∀ (a1 a2 : α), law a1 a2 = law a2 a1

class Assoc (α : Type) (law : α → α → α) where
  assoc : ∀ (a1 a2 a3 : α), law (law a1 a2) a3 = law a1 (law a2 a3)

class CommAssoc (α : Type) (law : α → α → α) extends Comm α law, Assoc α law

/--
warning: goal seems falsifiable, **it might not be provable**
---
info: goal is **not** falsifiable ✅
---
info: goal is **not** falsifiable ✅
-/
#test
theorem algebra0 [I : CommAssoc α law]
: ∀ (a1 a2 a3 : α), law (law a1 a2) a3 = law a2 (law a1 a3) := by
  falsifiable? --

  falsifiable? [I.assoc, I.comm] --

  let _assoc := I.assoc
  let _comm := I.comm
  falsifiable? --

  intro a1 a2 a3
  simp [I.comm a1 a2, I.assoc]

end algebra



section custom

structure DArray (len : Nat) (α : Type) where
  array : Array α
  h_size : array.size = len

namespace DArray
abbrev size (_self : DArray len α) := len

variable (self : DArray len α)

/-- info: goal is **not** falsifiable ✅ -/
#test
def push (val : α) : DArray len.succ α where
  array := self.array.push val
  h_size := by
    falsifiable? [Array.size_push, self.h_size]
    simp [self.h_size]

/-- info: goal is **not** falsifiable ✅ -/
#test
def append (that : DArray len' α) : DArray (len + len') α where
  array := self.array ++ that.array
  h_size := by
    falsifiable? [Array.size_append, self.h_size, that.h_size]
    simp [Array.size_append, self.h_size, that.h_size]
end DArray
