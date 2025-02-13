/-
Copyright (c) 2023-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Cvc.Basic.Term



namespace Cvc.Term

/-- A constant for `Ast`. -/
inductive Ast.Cst
| bool (b : Bool)
| rat (r : Rat)
| int (i : Int)
| string (s : String)

inductive Ast.Leaf (α : Type := Term)
| cst (t : α) (c : Ast.Cst)
| cstSym (t : α) (sym : String)

/-- Enumeration of what a term can be, useful for pattern-matching. -/
inductive Ast (α : Type := Term)
| leaf (l : Ast.Leaf)

| eq (args : ArrayMin 2 α)
| distinct (args : ArrayMin 2 α)

| not (t : α)
| and (args : ArrayMin 2 α)
| or (args : ArrayMin 2 α)
| xor (args : ArrayMin 2 α)
| implies (lft : α) (rgt : α)

| ite (cnd thn els : α)

| applyUF (args : ArrayMin 2 α)
| applyHO (args : ArrayMin 2 α)

| lt (args : ArrayMin 2 α)
| gt (args : ArrayMin 2 α)
| le (args : ArrayMin 2 α)
| ge (args : ArrayMin 2 α)

| add (args : ArrayMin 2 α)
| mul (args : ArrayMin 2 α)
| sub (args : ArrayMin 2 α)
| neg (arg : α)
| idiv (total : Bool) (args : ArrayMin 2 α)
deriving Inhabited

namespace Ast
/-- Extracts the top-level kind and children of an AST. -/
def destruct : Ast → cvc5.Kind × Array Term
| eq args => (.EQUAL, args.toArray)
| distinct args => (.DISTINCT, args.toArray)
| leaf (.cst t _)
| leaf (.cstSym t _) => (t.toCvc5.getKind, t.toCvc5.getChildren.map ofCvc5)

| not t => (.NOT, #[t])
| and args => (.AND, args.toArray)
| or args => (.OR, args.toArray)
| xor args => (.XOR, args.toArray)
| implies lft rgt => (.IMPLIES, #[lft, rgt])

| ite cnd thn els => (.ITE, #[cnd, thn, els])

| applyUF args => (.APPLY_UF, #[args.getN 0] ++ args.drainFirst.2.toArray)
| applyHO args => (.HO_APPLY, #[args.getN 0] ++ args.drainFirst.2.toArray)

| lt args => (.LT, args.toArray)
| gt args => (.GT, args.toArray)
| le args => (.LEQ, args.toArray)
| ge args => (.GEQ, args.toArray)

| add args => (.ADD, args.toArray)
| mul args => (.MULT, args.toArray)
| sub args => (.SUB, args.toArray)
| neg t => (.NEG, #[t])
| idiv true args => (.INTS_DIVISION_TOTAL, args.toArray)
| idiv false args => (.INTS_DIVISION, args.toArray)

/-- Generates the term corresponding to an AST. -/
def toTerm (ast : Ast) : ManagerM Term :=
  let (k, args) := ast.destruct
  Term.mk k args

/-- Turns a term into an AST. -/
def ofTerm (term : Term) : Except Error Ast := do
  let term! := term.toCvc5
  let k := term!.getKind
  match k with
  | .EQUAL => return .eq (← arrayMin 2)
  | .DISTINCT => return .distinct (← arrayMin 2)
  | .CONST_BOOLEAN =>
    let b ← term!.getBooleanValue
    return .leaf (.cst term (.bool b))
  | .CONST_INTEGER =>
    let i ← term!.getIntegerValue
    return .leaf (.cst term (.int i))
  | .CONST_RATIONAL =>
    let r ← term!.getRationalValue
    return .leaf (.cst term (.rat r))
  | .CONST_STRING =>
    -- #TODO need cleaner symbol string retrieval
    let s := term!.toString
    return .leaf (.cst term (.string s))
  | .CONSTANT =>
    return .leaf (.cstSym term (← term!.getSymbol))

  | .NOT =>
    return .not (← getOne)
  | .AND => return .and (← arrayMin 2)
  | .OR => return .or (← arrayMin 2)
  | .XOR => return .xor (← arrayMin 2)
  | .IMPLIES =>
    let (lft, rgt) ← getTwo
    return .implies lft rgt

  | .ITE =>
    let (cnd, thn, els) ← getThree
    return .ite cnd thn els

  | .APPLY_UF => return .applyUF (← arrayMin 2)
  | .HO_APPLY => return .applyHO (← arrayMin 2)

  | .LT => return .lt (← arrayMin 2)
  | .GT => return .gt (← arrayMin 2)
  | .LEQ => return .le (← arrayMin 2)
  | .GEQ => return .ge (← arrayMin 2)

  | .ADD => return .add (← arrayMin 2)
  | .MULT => return .mul (← arrayMin 2)
  | .SUB => return .sub (← arrayMin 2)
  | .NEG => return .neg (← getOne)
  | .INTS_DIVISION =>
    return .idiv false (← arrayMin 2)
  | .INTS_DIVISION_TOTAL =>
    return .idiv true (← arrayMin 2)

  | k =>
    Error.unsupported s!"term kind `{k}`"
    |> throw
where
  arityFail {α : Type} (desc : String) : Except Error α :=
    let term := term.toCvc5
    Error.internal
      s!"on term kind `{term.getKind}`: expected arity {desc}, got {term.getNumChildren}"
    |> throw
  getOne : Except Error Term :=
    if h : term.toCvc5.getNumChildren = 1 then
      return term.toCvc5.get ⟨0, by simp [h]⟩ |> ofCvc5
    else arityFail "= 1"
  getTwo : Except Error (Term × Term) :=
    if h : term.toCvc5.getNumChildren = 2 then
      return (
        term.toCvc5.get ⟨0, by simp [h]⟩ |> ofCvc5,
        term.toCvc5.get ⟨1, by simp [h]⟩ |> ofCvc5
      )
    else arityFail "= 2"
  getThree : Except Error (Term × Term × Term) :=
    if h : term.toCvc5.getNumChildren = 3 then
      return (
        term.toCvc5.get ⟨0, by simp [h]⟩ |> ofCvc5,
        term.toCvc5.get ⟨1, by simp [h]⟩ |> ofCvc5,
        term.toCvc5.get ⟨2, by simp [h]⟩ |> ofCvc5
      )
    else arityFail "= 2"
  arrayMin (n : Nat) : Except Error (ArrayMin n Term) := do
    let term := term.toCvc5
    let kidCount := term.getNumChildren
    let mut pref := #[]
    let mut suff := #[]
    for h : i in [0:kidCount] do
      let term := ofCvc5 <| term.get ⟨i, by
        simp [Membership.mem] at h
        exact h
      ⟩
      if i < n then
        pref := pref.push term
      else
        suff := suff.push term
    if h : pref.size = n then
      return h ▸ ArrayMin.mk pref suff
    else
      arityFail "> 1"
end Ast


@[inherit_doc Ast.toTerm]
def ofAst := Ast.toTerm

@[inherit_doc Ast.ofTerm]
def toAst := Ast.ofTerm



namespace Ast

inductive Frame.Raw (α : Type)
| eq (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| distinct (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)

| not
| and (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| or (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| xor (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| impliesLft (rgt : Term)
| impliesRgt (lft : α)

| iteCnd (thn els : Term)
| iteThn (cnd : α) (els : Term)
| iteEls (cnd thn : α)

| applyUF (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| applyHO (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)

| lt (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| gt (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| le (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| ge (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)

| add (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| mul (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| sub (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
| neg
| idiv (total : Bool) (rgt : ArrayMin.Frame 2 α) (args : ArrayMin.Iter 2 Term)
deriving Inhabited

namespace Frame.Raw
def push [Inhabited α] : Raw α → α → Term × Raw α ⊕ Ast α
| eq rgt args, a => arrayMin rgt args a .eq .eq
| distinct rgt args, a => arrayMin rgt args a .distinct .distinct

| and rgt args, a => arrayMin rgt args a .and .and
| or rgt args, a => arrayMin rgt args a .or .or
| xor rgt args, a => arrayMin rgt args a .xor .xor

| lt rgt args, a => arrayMin rgt args a .lt .lt
| gt rgt args, a => arrayMin rgt args a .gt .gt
| le rgt args, a => arrayMin rgt args a .le .le
| ge rgt args, a => arrayMin rgt args a .ge .ge

| add rgt args, a => arrayMin rgt args a .add .add
| mul rgt args, a => arrayMin rgt args a .mul .mul
| sub rgt args, a => arrayMin rgt args a .sub .sub
| idiv total rgt args, a => arrayMin rgt args a (.idiv total) (.idiv total)

| applyUF rgt args, a => arrayMin rgt args a .applyUF .applyUF
| applyHO rgt args, a => arrayMin rgt args a .applyHO .applyHO

| not, a => .inr (.not a)
| impliesLft rgt, lft => .inl (rgt, impliesRgt lft)
| impliesRgt lft, rgt => .inr (.implies lft rgt)

| iteCnd thn els, cnd => .inl (thn, iteThn cnd els)
| iteThn cnd els, thn => .inl (els, iteEls cnd thn)
| iteEls cnd thn, els => .inr (.ite cnd thn els)

| neg, a => .inr (.neg a)
where
  arrayMin {n : Nat}
    (rgt : ArrayMin.Frame n α) (args : ArrayMin.Iter n Term)
    (a : α)
    (fRaw : ArrayMin.Frame n α → ArrayMin.Iter n Term → Raw α)
    (fAst : ArrayMin n α → Ast α)
  : Term × Raw α ⊕ Ast α :=
    let (next?, args) := args.next?
    let rgt := rgt.push a
    if let some next := next? then
      .inl (next, fRaw rgt args)
    else
      let args := rgt.finalize
      .inr (fAst args)
end Frame.Raw

structure Frame (α : Type) where
private mk ::
  original : Term
  get : Frame.Raw α
deriving Inhabited

namespace Frame
def push [Inhabited α]
  (self : Frame α) (a : α)
: Term × Frame α ⊕ Ast α :=
  match self.get.push a with
  | .inl (next, raw) => .inl (next, {self with get := raw})
  | .inr ast => .inr ast

private def ofTerm (t : Term) : Ast → Term × Frame α ⊕ Leaf
| .leaf l => .inr l
| .eq args => arrayMin args .eq
| .distinct args => arrayMin args .distinct
| .and args => arrayMin args .and
| .or args => arrayMin args .or
| .xor args => arrayMin args .xor
| .lt args => arrayMin args .lt
| .gt args => arrayMin args .gt
| .le args => arrayMin args .le
| .ge args => arrayMin args .ge
| .add args => arrayMin args .add
| .mul args => arrayMin args .mul
| .sub args => arrayMin args .sub
| .idiv (total : Bool) args => arrayMin args (.idiv total)

| .applyUF args => arrayMin args .applyUF
| .applyHO args => arrayMin args .applyHO

| .not arg => .inl (arg, ⟨t, .not⟩)
| .implies lft rgt => .inl (lft, ⟨t, .impliesLft rgt⟩)

| .ite cnd thn els => .inl (cnd, ⟨t, .iteCnd thn els⟩)
| .neg arg => .inl (arg, ⟨t, .neg⟩)
where
  arrayMin {n : Nat}
    (args : ArrayMin n.succ Term)
    (f : ArrayMin.Frame n.succ α → ArrayMin.Iter n.succ Term → Ast.Frame.Raw α)
  : Term × Ast.Frame α ⊕ Ast.Leaf :=
    let fst := args.getN 0 (by simp only [Nat.succ_eq_add_one, Nat.zero_lt_succ])
    let (_, iter) := args.iter.next?
    .inl (fst, ⟨t, f args.newFrame iter⟩)
end Frame

end Ast



namespace Ast

inductive InspectDownRes (α : Type)
| done (res : α)
| subst (term : Term)
| down

inductive GoUpRes (α : Type)
| done (res : α)
| subst (term : Term)
| up (res : α)

end Ast

partial def traverse [Monad m] [MonadExcept Error m] [Inhabited α]
  (term : Term)
  (leafDo : Term → Ast.Leaf → m (Ast.GoUpRes α))
  (goUp : Term → Ast α → m (Ast.GoUpRes α))
  (inspectDown : Term → Ast → m (Ast.InspectDownRes α) := fun _ _ => return .down)
: m α :=
  goDownTerm [] term
where
  goDownTerm (stack : List (Ast.Frame α)) (term : Term) : m α := do
    match term.toAst with
    | .ok ast =>
      match ← inspectDown term ast with
      | .done res => return res
      | .subst term => goDownTerm stack term
      | .down =>
        match Ast.Frame.ofTerm term ast with
        | .inl (next, frame) => goDownTerm (frame :: stack) next
        | .inr leaf =>
          match ← leafDo term leaf with
          | .done res => return res
          | .subst term => goDownTerm stack term
          | .up a => goUpVal stack a
    | .error e => throw e
  goUpVal : List (Ast.Frame α) → α → m α
  | [], a => return a
  | frame :: stack, a => do
    match frame.push a with
    | .inl (next, frame) => goDownTerm (frame :: stack) next
    | .inr ast =>
      match ← goUp frame.original ast with
      | .done res => return res
      | .subst term => goDownTerm stack term
      | .up res => goUpVal stack res

/-- ## Bottom-up for-traversal -/

structure Iter.BottomUp where
  term : Term

def iterUp : Term → Iter.BottomUp := .mk


namespace Iter.BottomUp

instance [MonadExcept Error m] : ForIn m Iter.BottomUp Term where
  forIn {β} := fun ⟨term⟩ init f => do
    let code : ExceptT Error (StateT β m) Unit :=
      term.traverse (m := ExceptT Error (StateT β m))
        (inspectDown := fun _ _ => return Ast.InspectDownRes.down)
        (leafDo := fun term _ => do
          let acc ← get
          match ← f term acc with
          | .done res =>
            set res
            return .done ()
          | .yield res =>
            set res
            return .up ())
        (goUp := fun term _ => do
          let acc ← get
          match ← f term acc with
          | .done res =>
            set res
            return .done ()
          | .yield res =>
            set res
            return .up ())
    match ← code init with
    | (.ok _, res) => return res
    | (.error e, _) => throw e

def foldM [Monad m] [MonadExcept Error m]
  (self : Iter.BottomUp) (init : α) (f : α → Term → m α)
: m α := do
  let mut acc := init
  for sub in self do
    acc ← f acc sub
  return acc

def fold (self : Iter.BottomUp) (init : α) (f: α → Term → α) : Except Error α :=
  self.foldM init fun acc term => return f acc term

end Iter.BottomUp

/-- ## Top-down for-traversal -/

structure Iter.TopDown where
  term : Term

def iterDown : Term → Iter.TopDown := .mk

namespace Iter.TopDown

instance [MonadExcept Error m] : ForIn m Iter.TopDown Term where
  forIn {β} := fun ⟨term⟩ init f => do
    let code : ExceptT Error (StateT β m) Unit :=
      term.traverse (m := ExceptT Error (StateT β m))
        (inspectDown := fun term _ => do
          let acc ← get
          match ← f term acc with
          | .done res =>
            set res
            return .done ()
          | .yield res =>
            set res
            return .down)
        (leafDo := fun _ _ => return .up ())
        (goUp := fun _ _ => return .up ())
    match ← code init with
    | (.ok _, res) => return res
    | (.error e, _) => throw e

def foldM [Monad m] [MonadExcept Error m]
  (self : Iter.TopDown) (init : α) (f : α → Term → m α)
: m α := do
  let mut acc := init
  for sub in self do
    acc ← f acc sub
  return acc

def fold (self : Iter.TopDown) (init : α) (f: α → Term → α) : Except Error α :=
  self.foldM init fun acc term => return f acc term

end Iter.TopDown


abbrev FreeSyms :=
  Lean.RBTree (Term × String) (fun (t1, _) (t2, _) => Ord.compare t1 t2)

def freeSyms [Monad m] [MonadExcept Error m]
  (term : Term)
: m FreeSyms := do
  let mut syms := Lean.RBTree.empty
  for subTerm in term.iterDown do
    match subTerm.toAst with
    | .ok (.leaf (.cstSym _ name)) =>
      syms := syms.insert (subTerm, name)
    | .ok _ => pure ()
    | .error e => throw e
  return syms

def findSub [Monad m] [MonadExcept Error m]
  (term : Term) (f : Term → m Bool)
: m (Option Term) := do
  let mut res := none
  for subTerm in term.iterDown do
    if ← f subTerm then
      res := some subTerm
      break
    else continue
  return res
