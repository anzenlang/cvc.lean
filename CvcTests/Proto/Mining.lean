/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Untyped.Core
public import Cvc.Untyped.Theory.Arith
public import Cvc.Untyped.Grammar
public import Cvc.Typed.Grammar
public import Cvc.Typed.Core.Symbols



namespace Cvc.Test.Proto.Mining public section variable [Ω]

open Untyped
open Std (TreeMap TreeSet)



structure Miner.Conf where
  scanSymbols? : Bool := false

structure Miner extends Miner.Conf where private mk' ::
  bVars : BVars
  known : TreeSet Term
  sortedNTs : TreeMap Srt (NT × Terms)

namespace Miner variable (miner : Miner)

namespace Conf

instance : Inhabited Miner.Conf := ⟨{}⟩

end Conf

private def mkNT (srt : Srt) : Env NT := NT.mk srt s!"miner_NT_for__{srt}"

private def insertNewNT (srt : Srt) (rules : Terms := #[]) : Env Miner := do
  let nt ← mkNT srt
  let mut rules := rules
  rules ← rules.push <$> smt! nt = nt
  rules ← rules.push <$> smt! nt ≠ nt
  if srt.isInt ∨ srt.isReal then
    rules ← rules.push <$> smt! nt % nt
  return {miner with sortedNTs := miner.sortedNTs.insert srt (nt, rules)}

def empty : Miner := ⟨default, #[], TreeSet.empty, TreeMap.empty⟩

instance : Inhabited Miner := ⟨empty⟩

def ruleCount : Int := miner.sortedNTs.foldl (init := 0) fun sum _ (_, rules) => sum + rules.size

def addRulesFor (srt : Srt) (rules : Terms) (skipIfNewSort : Bool := false) : Env Miner := do
  let rules := rules.filter (· ∉ miner.known)
  if rules.isEmpty then return miner
  if let some (nt, oldRules) := miner.sortedNTs.get? srt then
    return {miner with
      known := rules.foldl (init := miner.known) TreeSet.insert
      sortedNTs := miner.sortedNTs.insert srt (nt, oldRules ++ rules)}
  else if ¬ skipIfNewSort then
    let nt ← mkNT srt
    return {miner with
      known := rules.foldl (init := miner.known) TreeSet.insert
      sortedNTs := miner.sortedNTs.insert srt (nt, rules)}
  else return miner

def addRuleFor (srt : Srt) (rule : Term) (skipIfNewSort : Bool := false) : Env Miner :=
  miner.addRulesFor srt #[rule] (skipIfNewSort := skipIfNewSort)

def addRule (rule : Term) (skipIfNewSort : Bool := false) : Env Miner := do
  let srt ← rule.getSort
  miner.addRuleFor srt rule (skipIfNewSort := skipIfNewSort)

def ntFor? (srt : Srt) (createIfNew : Bool := false) : Env (Miner × Option NT) := do
  if let some (nt, _rules) := miner.sortedNTs.get? srt then return (miner, nt)
  else if createIfNew then
    let nt ← mkNT srt
    return ({miner with sortedNTs := miner.sortedNTs.insert srt (nt, #[])}, nt)
  else return (miner, none)

def ntForTerm? (term : Term) (createIfNewSort : Bool := false) : Env (Miner × Option NT) :=
  term.getSort >>= miner.ntFor? (createIfNew := createIfNewSort)

def scanSymbols [Symbols S]
  (symbols : S.Terms) (filter : Term → Bool := 𝕂 true)
: Env Miner :=
  S.foldM symbols miner fun {α} _ _ miner symbol =>
    if filter symbol then do
      let srt ← Srt.of α
      miner.addRuleFor srt symbol
    else return miner

def addBVar (bv : BVar) : Miner := {miner with bVars := miner.bVars.push bv}

def addSymbols [Symbols S] (idents : S.Idents) : Env Miner := do
  let bVars ← S.foldM idents #[] fun {α} _ _ bVars ident => do
    let srt ← Srt.of α
    bVars.push <$> BVar.mk srt ident
  return {miner with bVars := miner.bVars ++ bVars}

def addTypedSymbols [Typed.Symbols S] (idents : S.Idents) : Env Miner := do
  let bVars ← S.foldM idents #[] fun {α} _ _ bVars ident => do
    let srt ← Srt.of α
    bVars.push <$> BVar.mk srt ident
  return {miner with bVars := miner.bVars ++ bVars}

def withSorts (sorts : Array Srt) : Env Miner := do
  let mut sortedNTs := miner.sortedNTs
  for sort in sorts do
    if ¬ sortedNTs.contains sort then
      let nt ← mkNT sort
      sortedNTs := sortedNTs.insert sort (nt, #[])
  return { miner with sortedNTs }

partial def scanTerm (t : Term) (skipNewSorts : Bool := false) : Env Miner :=
  loop miner [#[t]]
where loop miner : List Terms → Env Miner
  | [] => return miner
  | terms :: tail => if h : terms.size = 0 then loop miner tail else do
    let mut miner := miner
    let term := terms.back
    let mut tail := terms.pop :: tail
    let kids := term.getKids
    if kids.isEmpty then
      if ¬ (← term.hasSymbol) then
        -- no kids, term is a leaf, add as a rule and loop
        miner ← miner.addRule term (skipIfNewSort := skipNewSorts)
    else
      -- make sure we visit `term`'s kids
      tail := kids :: tail
      let mut ruleKids : Terms := Array.mkEmpty kids.size
      -- replace each kid with the right non-terminal:
      -- this loops exits with `ruleKids = #[]` if the current term cannot be expressed with the
      -- non-terminals available when `skipNewSorts`
      for kid in kids do
        let (miner', kid?) ← miner.ntForTerm? kid (createIfNewSort := ¬ skipNewSorts)
        miner := miner'
        if let some kid := kid? then ruleKids := ruleKids.push kid
        else
          -- skip `term`
          ruleKids := #[]
          break
      -- rewrite `term` as a rule?
      if ¬ ruleKids.isEmpty then
        let rule ← term.replaceKids ruleKids
        miner ← miner.addRule rule (skipIfNewSort := skipNewSorts)
      -- note that regardless of whether `term` became a rule, we recurse on its kids
    loop miner tail

def scanTypedTerm (t : Typed.Term α) (skipNewSorts : Bool := false) : Env Miner :=
  miner.scanTerm t.erase (skipNewSorts := skipNewSorts)

def extractGrammarFor (srt : Srt)
  (allowAnyConstant : Srt → Bool := 𝕂 false)
: Env (Option Grammar) := do
  let mut start? := none
  let mut nts := Array.mkEmpty miner.sortedNTs.size.pred
  for (srt', (nt, _)) in miner.sortedNTs do
    if srt' == srt then start? := some nt
    else nts := nts.push nt
  let some start := start?
    | return none
  let mut g ← Grammar.mk miner.bVars start nts
  for (srt, (nt, rules)) in miner.sortedNTs do
    g ← g.addAnyVariable nt
    if allowAnyConstant srt then g ← g.addAnyConstant nt
    g ← rules.foldlM (init := g) fun g => g.addRule nt
  return g

/-- The start sort a grammar over the miner's parameters needs to generate `σ`.

That is `σ`'s sort with one domain sort dropped per parameter: `σ` itself without parameters, its
codomain when it takes exactly as many arguments as there are parameters, and the function sort of
the remaining arguments when it takes more. Fewer arguments than parameters is an error.
-/
private def startSrtFor (σ : Type) [ToTyp σ] : Env Srt := do
  let srt ← Srt.of σ
  let n := miner.bVars.size
  if n = 0 then return srt
  let mismatch := s!"cannot generate `{srt}` over {n} parameter(s)"
  if ¬ srt.isFunction then throwUser mismatch
  let dom ← srt.getFunctionDomainSorts
  let cod ← srt.getFunctionCodomainSort
  if n = dom.size then return cod
  else if h : n < dom.size then Srt.function (dom.extract n dom.size) cod
  else throwUser mismatch

/-- A typed grammar generating `σ` over the miner's parameters.

The typed counterpart of `extractGrammarFor`: the start sort is read off `σ` by `startSrtFor`, and
the grammar is then checked against `σ` with `Untyped.Grammar.typeCheckAs`, which also catches
parameters whose sorts disagree with `σ`'s domain. `none` when the miner has no non-terminal of
the start sort.
-/
def extractTypedGrammar (σ : Type) [ToTyp σ]
  (allowAnyConstant : Srt → Bool := 𝕂 false)
: Env (Option (Typed.Grammar σ)) := do
  let some g ← miner.extractGrammarFor (← miner.startSrtFor σ) allowAnyConstant
    | return none
  return some (← g.typeCheckAs σ)

end Miner
