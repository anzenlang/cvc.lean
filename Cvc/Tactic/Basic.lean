import Cvc.Basic

import Auto



namespace Cvc.Tactic



section
open Term (ManagerM)
open Auto (Lemma)
open Auto.IR.SMT

namespace Srt
def ofSSort : SSort → ManagerM Srt
| .bvar n =>
  throw (.internal s!"[Srt.ofSSort] unexpected bound type-variable #{n}")
| .app id args =>
  if ¬ args.isEmpty then
    throw (.internal s!"[Srt.ofSSort] type constructors are not supported yet")
  else
    match id.toString with
    | "Int" => Srt.int
    | "Real" => Srt.real
    | "String" => Srt.string
    | srt => throw (.internal
      s!"[Srt.ofSSort] only sorts `Int`, `Real`, and `String` are supported: `{srt}`"
    )

open Auto.Embedding.Lam in
def ofLamBaseSort : LamBaseSort → ManagerM (Option Srt)
| .prop | .bool => Srt.bool
| .nat => Srt.int
| .int => Srt.int
| .isto0 _ => return none
| .bv n =>
  let n := n.toUInt32
  if valid : 0 < n then
    Srt.bitVec n valid
  else
    throw (.internal "illegal 0-length bitvector sort from `auto`")

open Auto.Embedding.Lam in
def ofLamSort (ls : LamSort) : ManagerM (Option Srt) := do
  if let some (cod, dom) ← aux ls then
    if cod.isEmpty then
      return dom
    else
      Srt.function cod dom
  else
    return none
where
  aux
  | .atom _ => return none
  | .base s => do
    if let some s ← ofLamBaseSort s then
      return some (#[], s)
    else
      return none
  | .func dom cod => do
    if let some (argDoms, argCod) ← aux dom then
      let arg ← Srt.function argDoms argCod
      if let some (doms, cod) ← aux cod then
        let doms := #[arg] ++ doms
        return (doms, cod)
    return none
end Srt

def Name.root : Lean.Name → (last : Option String := none) → Option String
| .anonymous, last => last
| .str pref name, _ => root pref name
| .num pref _, _ => root pref

inductive Res
| unknown
| unsat
| sat (model : Array (Lean.Expr × Term × String))

namespace Res
def isSat? : Res → Option Bool
| unknown => none
| unsat => false
| sat _ => true
end Res

def Dumb.checkSat
  (commands : Array String)
  (env : Array (Lean.Expr × String × Srt))
: Term.Manager → Except Error Res :=
  let script : SmtM Res := do
    Smt.setLogic Logic.all
    Smt.setOption .produceModels
    let str :=
      commands.foldl (init := "(set-option :fresh-declarations true)") fun str c => s!"{str}\n{c}"
    let mut nuEnv := #[]
    for (e, n, s) in env do
      let var ← Smt.declareFun n s
      nuEnv := nuEnv.push (e, var, n, s)
    Smt.parseSmtLib str
    let res ← Smt.checkSat
    if res.isSat then
      let mut model := #[]
      for (expr, var, n, _srt) in nuEnv do
        let val ← Smt.getValue var
        model := model.push (expr, val, n)
      return .sat model
      -- return .sat #[]
    else if res.isUnsat then
      return .unsat
    else if res.isUnknown then
      return .unknown
    else
      throw (.internal s!"[falsifiable?] unexpected check-sat result `{res}`")
  script.runWith

structure Opts where
  verbose : Bool
  timed : Bool

namespace Opts
protected def default : Opts where
  verbose := false
  timed := false
end Opts

open Auto Embedding.Lam in
def checkSat
  (exportFacts : Array REntry)
  (exportInds : Array MutualIndInfo)
  (tm : Term.Manager)
  (opts : Opts)
: LamReif.ReifM (Except Error Res) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "[falsifiable?] unexpected error")
  let sni : SMT.SMTNamingInfo := {
    tyVal := (← LamReif.getTyVal)
    varVal := (← LamReif.getVarVal)
    lamEVarTy := (← LamReif.getLamEVarTy)
  }
  let ((commands, _validFacts), _state) ←
    (lamFOL2SMT sni lamVarTy lamEVarTy exportLamTerms exportInds).run
  -- println! "h2lMap:"
  -- for (k, v) in _state.h2lMap.toArray do
  --   println! "- {k} ↦ {v}"
  -- println! "l2hMap:"
  -- for (k, v) in _state.l2hMap.toArray do
  --   println! "- {k} ↦ {v}"
  -- println! "var val:"
  -- for (e, s) in sni.varVal do
  --   println! "- {e} : {s}"
  -- println! "evar ty:"
  -- for s in sni.lamEVarTy do
  --   println! "- ... {s}"
  -- println! "used names:"
  -- for (name, count) in _state.usedNames.toArray do
  --   println! "- {name} ({count})"
  let mut env := #[]
  for (name, _) in _state.usedNames.toArray do
    let name :=
      if name.startsWith "_" then name else "_" ++ name
    -- println! "working on `{name}`"
    match _state.l2hMap.find? name with
    | some (.term n) =>
      -- println! "→ {n}"
      let (e, s) := sni.varVal[n]!
      if let (.ok (some s), _) := Srt.ofLamSort s tm then
        env := env.push (e, name, s)
    | _ => pure ()
  -- println! "env:"
  -- for (e, name, s) in env do
  --   println! "- {name} : {s} = {e}"
  let commands := commands.map toString
  let res := Dumb.checkSat commands env tm
  if opts.verbose then
    let resStr :=
      match res with
      | .ok (.sat _) => s!"; sat"
      | .ok .unsat => s!"; unsat"
      | .ok .unknown => s!"; unknown"
      | .error e => s!"; {e}"
    let dump : String :=
      commands.foldr (init := s!"(check-sat)\n{resStr}")
        (fun cmd acc => cmd ++ "\n" ++ acc)
    Lean.logInfo dump
  return res

end



open Lean
open Elab
open Tactic



open Auto in
def runSat?
  (_declName? : Option Name) (lemmas : Array Lemma) (inhFacts : Array Lemma)
  (opts : Opts)
: MetaM Res := do
  -- logInfo s!"{lemmas.size} lemma(s), {inhFacts.size} inh fact(s)"
  -- Simplify `ite`
  let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
  -- Simplify `decide`
  let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem decide_simp_lem)
  let afterReify
    (uvalids : Array UMonoFact)
    (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal))
  : LamReif.ReifM Res := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let _exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    let tm ← Term.Manager.mk
    match ← checkSat exportFacts exportInds tm opts with
    | .ok res => return res
    | .error e => throwError s!"[falsifiable?] {e}"
  let (res, _) ← Monomorphization.monomorphize lemmas inhFacts (
    @id (Reif.ReifM Res) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (afterReify s.facts s.inhTys s.inds).run' {u := u}
    )
  return res

declare_syntax_cat falsifiableOpt (behavior := symbol)

syntax "verbose" : falsifiableOpt
syntax "timed" : falsifiableOpt

def Opts.parseOpt (self : Opts) : TSyntax `falsifiableOpt → TacticM Opts
| `(falsifiableOpt| verbose) => return {self with verbose := true}
| `(falsifiableOpt| timed) => return {self with timed := true}
| _ => throwUnsupportedSyntax

syntax (name := falsifiable?)
  "falsifiable?"
    ( "(" falsifiableOpt,* ")" )?
    Auto.hints (Auto.uord)*
: tactic

def discardWithLog
  (options : Option (Syntax.TSepArray `falsifiableOpt ","))
  (action : Opts → TacticM Unit)
: TacticM Unit := do
  let state ← saveState
  let mut opts := Opts.default
  if let some options := options then
    for opt in options.getElems do
      opts ← opts.parseOpt opt
  let startTime? ←
    if opts.timed then
      pure $ some (← IO.monoMsNow)
    else pure none

  action opts

  if let some startTime := startTime? then
    let time := (← IO.monoMsNow) - startTime
    logInfo s!"done in {time}ms"

  let log ← Core.getMessageLog
  restoreState state
  Core.setMessageLog log

def evalSatDo
  (options : Option (Syntax.TSepArray `falsifiableOpt ","))
  (hints : TSyntax `Auto.hints)
  (uords : Array (TSyntax `Auto.uord))
  (action : Opts → Res → TacticM Unit)
: TacticM Unit :=
  discardWithLog options fun opts => do
    let mainGoal ← getMainGoal
    let (goalBinders, newGoal) ← mainGoal.intros
    let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
      | throwError "[falsifiable?] unexpected result after applying `Classical.byContradiction`"
    let (ngoal, absurd) ← MVarId.intro1 nngoal
    let declName? ← Elab.Term.getDeclName?
    replaceMainGoal [absurd]
    withMainContext do
      let (lemmas, inhFacts) ← Auto.collectAllLemmas hints uords (goalBinders.push ngoal)
      replaceMainGoal [newGoal]
      let res ← runSat? declName? lemmas inhFacts opts
      action opts res

@[tactic falsifiable?]
unsafe def evalSat? : Tactic
| `(falsifiable?| falsifiable? $[($options,*)]? $hints $[$uords]*) => do
  evalSatDo options hints uords fun
    | _, .unsat => logInfo "goal is **not** falsifiable ✅"
    | opts, .sat model => do
      let mut msg := "goal seems falsifiable, **it might not be provable**"
      for (expr, valTerm, name) in model do
        let mut var := toString expr
        match expr with
        | .fvar fv => do
          let name ← fv.getUserName
          if let some name := Name.root name then
            var := name
          else
            var := toString name
        | .mvar mv => do
          let name := mv.name
          if let some name := Name.root name then
            var := name
          else
            var := toString name
        | _ => pure ()
        if opts.verbose then
          msg := s!"{msg}\n- [{name}] {var} = {valTerm}"
        else
          msg := s!"{msg}\n- {var} = {valTerm}"
      logWarning msg
    | _, .unknown => throwError "failed to decide (un)satifiability"
| _ => throwUnsupportedSyntax

syntax (name := falsifiableTerm?)
  "falsifiableTerm?"
    ( "(" falsifiableOpt,* ")" )?
    Auto.hints (Auto.uord)*
: tactic

@[tactic falsifiableTerm?]
unsafe def evalSatTerm? : Tactic
| `(falsifiableTerm?| falsifiableTerm? $[($options,*)]? $hints $[$uords]*) => do
  evalSatDo options hints uords fun
    | _, .unsat => logInfo "this term is not falsifiable ✅"
    | opts, .sat model => do
      let mut msg := ""
      for (expr, valTerm, name) in model do
        let mut var := toString expr
        match expr with
        | .fvar fv => do
          let name ← fv.getUserName
          if let some name := Name.root name then
            var := name
          else
            var := toString name
        | .mvar mv => do
          let name := mv.name
          if let some name := Name.root name then
            var := name
          else
            var := toString name
        | _ => pure ()
        if opts.verbose then
          msg := s!"{msg}\n- [{name}] {var} = {valTerm}"
        else
          msg := s!"{msg}\n- {var} = {valTerm}"
      if ¬ msg.isEmpty then
        msg := " with" ++ msg
      logWarning s!"this term seems falsifiable{msg}"
    | _, .unknown =>
      logWarning "failed to assess falsifiability, the solver gave up"
| _ => throwUnsupportedSyntax


-- example (n : Nat) : n ≠ 3 := by
--   falsifiable? (verbose)

-- example (n1 n2 n3 : Nat) (h : n1 + n2 ≤ n3) : 4*n1 + 4*n2 ≤ 4*n3 := by
--   falsifiable? (verbose)
--   rw [← Nat.left_distrib]
--   exact Nat.mul_le_mul (Nat.le_refl 4) h

-- example : ∀ (n m : Int), n % 3 = m → ∃ (k : Int), n = m + 3 * k := by
--   falsifiable?
--   sorry

-- example : ∃ (k : Nat), 0 = 0 + 3 * k := by
--   falsifiable?
--   sorry

open Lean.Parser.Tactic (tacticSeq1Indented) in
scoped syntax (name := try_with_log)
  "try_with_log" tacticSeq1Indented
: tactic

@[tactic try_with_log]
def elab_try_with_log : Tactic
| `(tactic| try_with_log $[$tacs]*) => do
  let state ← saveState
  loop 0 tacs
  let log ← Core.getMessageLog
  restoreState state
  Core.setMessageLog log
| _ => throwUnsupportedSyntax
where loop (i : Nat) (tacs : Array Syntax) := do
  if _isLt : i < tacs.size then
    try
      evalTactic tacs[i]
      loop i.succ tacs
    catch
    | e =>
      if i = tacs.size - 1
      then return ()
      else throw e
  else return ()

syntax (name := findCex)
  withPosition(
    "#findCex "
      ( "(" falsifiableOpt,* ")" )?
      Auto.hints (Auto.uord)*
      (colGt term)
    ";"?
  )
  ppLine
  term
: term

example (P : Prop) : True := by
  try_with_log
    apply (by simp only [implies_true] : P → True) ; falsifiableTerm? [stnahoeusnthao]
  trivial

@[term_elab findCex]
def evalFindCex : Term.TermElab
| `(#findCex $[($options,*)]? $hints $[$uords]* $t:term $[;]? $andThen), exp? => do
  -- make sure `t` can be elaborated, otherwise the error will be invisible
  let _ ← Lean.Elab.Term.elabTerm t none
  let findCex ← `(
      by
        try_with_log
          apply (by simp only [implies_true] : $t → True)
          falsifiableTerm? $[($options,*)]? $hints $[$uords]*
          trivial
        trivial
    )
  let tru ← `(True)
  let tru ← Lean.Elab.Term.elabTerm tru none
  let _ ← Lean.Elab.Term.elabByTactic findCex tru
  Term.elabTerm andThen exp?
| _, _ => throwUnsupportedSyntax


/--
warning: this term seems falsifiable with
- n2 = 0
- n3 = 0
-/
#guard_msgs in
def test1 (n1 n2 n3 : Nat) : Nat :=
  let d := n2 - n3
  #findCex d ≠ 0
  n1 / d

/--
warning: failed to assess falsifiability, the solver gave up
-/
#guard_msgs in
def testArray1 (a : α) (l : Array α) : Array α :=
  let l' := l.push a
  #findCex l'.size = l.size + 1
  l'

/--
info: this term is not falsifiable ✅
-/
#guard_msgs in
def testArray2 (a : α) (l : Array α) : Array α :=
  let l' := l.push a
  #findCex [l.size_push a]
    l'.size = l.size + 1
  l'

/--
warning: failed to assess falsifiability, the solver gave up
-/
#guard_msgs in
def testList1 (a : α) (l : List α) : List α :=
  let l' := l.cons a
  #findCex l'.length = l.length + 1
  l'

/--
info: this term is not falsifiable ✅
-/
#guard_msgs in
def testList2 (a : α) (l : List α) : List α :=
  let l' := l.cons a
  #findCex [l.length_cons a]
    l'.length = l.length + 1
  l'
