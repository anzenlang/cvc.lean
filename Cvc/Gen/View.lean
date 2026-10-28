/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command
public import Cvc.Spec.Defs
import all Cvc.Spec.Defs



/-! # Generating views

A **view** takes a term apart one level: its operator, as a constructor, and its kids. Each theory
has its own view, generated from its specification beside its constructors — or, for what no
specification describes, written by hand and registered — and `def.term_view V` gathers the views
of every theory the current module imports into one inductive.

- `gen_untyped_view% from <Spec module>` generates a theory's sort-erased view, an inductive with
  one constructor per operator, and its viewer `of?`, then registers it.
- `register_untyped_view% <View> [ctor KIND, …]` registers a hand-written one.
- `def.untyped_term_view V` — `def.term_view V` under `open Cvc.Untyped` — generates the
  aggregate `V`: the leaves, a variant `of<Theory>` per registered view, a catch-all `other`, one
  `@[match_pattern]` abbreviation per operator so that a pattern can skip the theory, a viewer
  `V.of`, and a `TermView` instance.

Which theories `def.term_view` gathers is decided by the registry, which holds exactly the views of
the modules imported: importing a theory is what makes its operators visible.

Like `Cvc.Gen.Term`, this module imports neither layer: every name the generated code mentions is
built with `mkIdent`, fully qualified.
-/

namespace Cvc public meta section

open Lean Elab Command



/-! ## The registry -/

/-- A registered sort-erased view. -/
structure UntypedView where
  /-- The theory, `Arith`: the aggregate's variant holding the view is `ofArith`. -/
  theory : Name
  /-- The view's inductive. -/
  view : Name
  /-- Each constructor, and the kind it owns. -/
  ctors : Array (Name × Name)
  /-- The specification's entries the view has no constructor for, and why. -/
  skipped : Array (Name × String) := #[]
deriving Inhabited

/-- The registered sort-erased views, imported ones included. -/
initialize untypedViewExt : SimplePersistentEnvExtension UntypedView (Array UntypedView) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

/-- Every registered sort-erased view. -/
def untypedViews [Monad m] [MonadEnv m] : m (Array UntypedView) :=
  return untypedViewExt.getState (← getEnv)



/-! ## Emitted names

Built with `mkIdent` and spliced, never written in a quotation: a name written there resolves
against this module's environment, which imports neither layer.
-/

/-- `Cvc.Untyped.Term`. -/
def viewTermId : Ident := mkIdent `Cvc.Untyped.Term
/-- `Cvc.Untyped.Kids`. -/
def viewKidsId : Ident := mkIdent `Cvc.Untyped.Kids
/-- `Cvc.Untyped.Kids.of?`. -/
def viewKidsOfId : Ident := mkIdent `Cvc.Untyped.Kids.of?
/-- `Cvc.Untyped.Term.getKids`. -/
def viewGetKidsId : Ident := mkIdent `Cvc.Untyped.Term.getKids
/-- `Cvc.Untyped.Term.getKind?`. -/
def viewGetKindId : Ident := mkIdent `Cvc.Untyped.Term.getKind?
/-- `Cvc.Untyped.Term.indexAt?`. -/
def viewIndexAtId : Ident := mkIdent `Cvc.Untyped.Term.indexAt?
/-- `Cvc.Untyped.Term.getSymbol`. -/
def viewGetSymbolId : Ident := mkIdent `Cvc.Untyped.Term.getSymbol
/-- `Cvc.Untyped.BVar`. -/
def viewBVarId : Ident := mkIdent `Cvc.Untyped.BVar
/-- `Cvc.Untyped.Term.asBVar`. -/
def viewAsBVarId : Ident := mkIdent `Cvc.Untyped.Term.asBVar
/-- `Cvc.Untyped.TermView`. -/
def viewTermViewId : Ident := mkIdent `Cvc.Untyped.TermView
/-- `cvc5.Kind.<k>`. -/
def viewKindId (k : Name) : Ident := mkIdent (`cvc5.Kind ++ k)

/-- The kinds of values: the leaves own them, so no view does. -/
def viewValueKinds : Array Name := #[`CONST_BOOLEAN, `CONST_INTEGER, `CONST_RATIONAL,
  `CONST_STRING, `CONST_ROUNDINGMODE, `CONST_BITVECTOR, `CONST_FLOATINGPOINT, `CONST_FINITE_FIELD,
  `CONST_SEQUENCE, `CONST_ARRAY, `UNINTERPRETED_SORT_VALUE]

/-- A docstring node. -/
def viewDoc (s : String) : TSyntax ``Lean.Parser.Command.docComment :=
  mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]



/-! ## A theory's sort-erased view -/

/-- A view's constructor, and its viewer's alternative. -/
abbrev ViewCtor := TSyntax ``Lean.Parser.Command.ctor × TSyntax ``Lean.Parser.Term.matchAlt

/-- One entry's constructor in its theory's view, and the viewer's alternative for it. -/
def genUntypedCtor (spec : OpSpec) (view : Name) : MacroM (Except String ViewCtor) := do
  let fail (why : String) := return .error why
  if viewValueKinds.contains spec.kind then return ← fail "a value, the `.value` leaf"
  if spec.kind == `CONSTANT then return ← fail "a declared symbol, the `.symbol` leaf"
  if spec.tmFn.isSome && !(spec.args.isEmpty && spec.valArgs.isEmpty && spec.indices.isEmpty) then
    return ← fail "a `tm` constructor taking arguments"
  if !spec.valArgs.isEmpty then return ← fail "takes Lean values"
  let ctorId := mkIdent (view ++ spec.id)
  let nary := !(spec.nary matches .never) && spec.args.size == 2
    && spec.args[0]!.shape == spec.args[1]!.shape
  -- the fields: indices, then the kids
  let idxIds := spec.indices.map mkIdent
  let mut binders ← idxIds.mapM fun i => `(bracketedBinder| ($i : Nat))
  let kidIds := if nary then #[mkIdent `kids] else spec.args.map (mkIdent ·.name)
  binders := binders ++ (← kidIds.mapM fun k =>
    if nary then `(bracketedBinder| ($k : $viewKidsId)) else `(bracketedBinder| ($k : $viewTermId)))
  let ctor ← `(Lean.Parser.Command.ctor|
    $(viewDoc spec.doc):docComment | $(mkIdent spec.id):ident $binders*)
  -- the viewer's alternative: the kids, matched against the arity, then the indices
  let t := mkIdent `viewed
  let app ← `($ctorId $idxIds* $kidIds*)
  let mut rhs ←
    -- the lambda binds the very identifier the application uses: written in the quotation, it
    -- would be hygienic and miss
    if nary then `(($viewKidsOfId ($viewGetKidsId $t)).map fun $(kidIds[0]!) => $app)
    else if kidIds.isEmpty then `(if ($viewGetKidsId $t).isEmpty then some $app else none)
    else `(match ($viewGetKidsId $t).toList with
      | [$[$kidIds],*] => some $app
      | _ => none)
  for (i, n) in idxIds.zipIdx.reverse do
    rhs ← `(($viewIndexAtId $t $(Syntax.mkNumLit (toString n))).bind fun $i => $rhs)
  let alt ← `(Lean.Parser.Term.matchAltExpr| | some $(viewKindId spec.kind) => $rhs)
  return .ok (ctor, alt)

/-- Generates and registers a theory's sort-erased view from its specification module. -/
syntax (name := genUntypedViewStx) "gen_untyped_view% " "from " ident : command

@[command_elab genUntypedViewStx]
def elabGenUntypedView : CommandElab
  | `(gen_untyped_view% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    let theory := mod.getId.components.getLast!
    let view := `Cvc.Untyped.View ++ theory
    let mut ctors := #[]
    let mut alts := #[]
    let mut owned : Array (Name × Name) := #[]
    let mut skipped := #[]
    for spec in specs do
      match ← liftMacroM (genUntypedCtor spec view) with
      | .error why => skipped := skipped.push (spec.id, why)
      | .ok (ctor, alt) =>
        if let some (other, _) := owned.find? (·.2 == spec.kind) then
          skipped := skipped.push (spec.id, s!"its kind `{spec.kind}` is `{other}`'s")
        else
          ctors := ctors.push ctor
          alts := alts.push alt
          owned := owned.push (spec.id, spec.kind)
    if ctors.isEmpty then return
    -- declared from the root, whatever namespace the generation site is in
    let viewId := mkIdent view
    let doc := viewDoc s!"`{theory}`'s operators, taken apart one level, sort-erased."
    let declId := mkIdent (`_root_ ++ view)
    elabCommand (← `($doc:docComment protected inductive $declId where $ctors*))
    let t := mkIdent `viewed
    let ofDoc := viewDoc s!"Takes a term apart one level, if `{theory}` owns its operator."
    elabCommand (← `(
      $ofDoc:docComment
      def $(mkIdent (`_root_ ++ view ++ `of?)) ($t : $viewTermId) : Option $viewId :=
        match ($viewGetKindId $t) with
        $[$alts:matchAlt]*
        | _ => none))
    modifyEnv (untypedViewExt.addEntry · { theory, view, ctors := owned, skipped })
  | _ => throwUnsupportedSyntax

/-- Registers a hand-written sort-erased view: its inductive, and each constructor with the kind it
owns. The theory is the inductive's last component. -/
syntax (name := registerUntypedViewStx)
  "register_untyped_view% " ident "[" (ident ident),* "]" : command

@[command_elab registerUntypedViewStx]
def elabRegisterUntypedView : CommandElab
  | `(register_untyped_view% $view [$[$ctors $kinds],*]) => do
    let view ← liftCoreM (realizeGlobalConstNoOverload view)
    let owned := (ctors.zip kinds).map fun (c, k) => (c.getId, k.getId)
    let entry := { theory := view.components.getLast!, view, ctors := owned }
    modifyEnv (untypedViewExt.addEntry · entry)
  | _ => throwUnsupportedSyntax

/-- Lists the registered sort-erased views: each theory, how many operators it takes apart, and the
specification entries it has no constructor for. -/
syntax (name := untypedViewsStx) "#untyped_views" : command

@[command_elab untypedViewsStx]
def elabUntypedViews : CommandElab
  | `(#untyped_views) => do
    let mut lines := #[]
    for v in ← untypedViews do
      lines := lines.push s!"{v.theory}: {v.ctors.size} operators"
      for (id, why) in v.skipped do lines := lines.push s!"  no constructor for {id}: {why}"
    logInfo ("\n".intercalate lines.toList)
  | _ => throwUnsupportedSyntax



/-! ## The sort-erased aggregate -/

/-- The aggregate's variant holding a theory's view: `ofArith`, which no operator's name can clash
with. -/
def theoryVariant (theory : Name) : Name := Name.mkSimple s!"of{theory}"

/-- Generates the sort-erased aggregate `V` from every registered view. -/
syntax (name := untypedTermViewStx) "def.untyped_term_view " ident : command

@[command_elab untypedTermViewStx]
def elabUntypedTermView : CommandElab
  | `(def.untyped_term_view $v:ident) => do
    let views ← untypedViews
    let agg := v.getId
    let aggId := mkIdent agg
    let leaves := #[`value, `symbol, `bvar, `other, `of, `instTermView]
    -- a kind is routed to one theory, and an abbreviation names one operator
    let mut owners : Array (Name × Name) := #[]
    let mut names : Array (Name × Name) :=
      leaves.map (·, agg) ++ views.map (theoryVariant ·.theory, agg)
    for vw in views do
      for (c, k) in vw.ctors do
        if viewValueKinds.contains k || k == `CONSTANT || k == `VARIABLE then
          throwError m!"`{agg}`: kind `{k}` is owned by a leaf and by `{vw.view}`"
        if let some (_, other) := owners.find? (·.1 == k) then
          throwError m!"`{agg}`: kind `{k}` is owned by both `{other}` and `{vw.view}`"
        owners := owners.push (k, vw.view)
        if let some (_, other) := names.find? (·.1 == c) then
          throwError m!"`{agg}`: `{c}` names an operator of `{vw.view}` and something of `{other}`"
        names := names.push (c, vw.view)
    -- the aggregate
    let mut variants := #[
      ← `(Lean.Parser.Command.ctor| | $(mkIdent `value):ident (t : $viewTermId)),
      ← `(Lean.Parser.Command.ctor| | $(mkIdent `symbol):ident (name : _root_.String)),
      ← `(Lean.Parser.Command.ctor| | $(mkIdent `bvar):ident (x : $viewBVarId))]
    for vw in views do
      variants := variants.push (← `(Lean.Parser.Command.ctor|
        | $(mkIdent (theoryVariant vw.theory)):ident (v : $(mkIdent vw.view))))
    variants := variants.push
      (← `(Lean.Parser.Command.ctor| | $(mkIdent `other):ident (t : $viewTermId)))
    let doc := viewDoc "A sort-erased term, taken apart one level."
    elabCommand (← `($doc:docComment inductive $aggId where $variants*))
    -- one abbreviation per operator, its binders read off the view's constructor
    for vw in views do
      for (c, _) in vw.ctors do
        let ctorName := vw.view ++ c
        let fields ← liftTermElabM do
          let info ← getConstInfoCtor ctorName
          Meta.forallTelescope info.type fun xs _ =>
            xs.toList.drop info.numParams |>.toArray.mapM fun x => do
              let d ← x.fvarId!.getDecl
              return (d.userName, d.binderInfo)
        let binders ← fields.mapM fun (n, bi) =>
          if bi.isExplicit then `(bracketedBinder| ($(mkIdent n) : _))
          else `(bracketedBinder| {$(mkIdent n) : _})
        -- no result type: with one, the binders' holes would be resolved before the body is seen
        elabCommand (← `(
          @[match_pattern] abbrev $(mkIdent (agg ++ c)) $binders* :=
            $(mkIdent (agg ++ theoryVariant vw.theory))
              (@$(mkIdent ctorName) _ $(fields.map (mkIdent ·.1))*)))
    -- the viewer: the kind, routed to its owner
    let t := mkIdent `viewed
    let other := mkIdent (agg ++ `other)
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for k in viewValueKinds do
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
        | some $(viewKindId k) => $(mkIdent (agg ++ `value)) $t))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
      | some $(viewKindId `CONSTANT) =>
        match ($viewGetSymbolId $t) with
        | .ok name => $(mkIdent (agg ++ `symbol)) name
        | .error _ => @panic _ ⟨$other $t⟩ s!"a constant with no symbol: {$t}"))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr|
      | some $(viewKindId `VARIABLE) => $(mkIdent (agg ++ `bvar)) ($viewAsBVarId $t)))
    for vw in views do
      let variant := mkIdent (agg ++ theoryVariant vw.theory)
      let rhs ← `(match ($(mkIdent (vw.view ++ `of?)) $t) with
        | some v => $variant v
        | none => @panic _ ⟨$other $t⟩ s!"an ill-formed term: {$t}")
      for (_, k) in vw.ctors do
        alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | some $(viewKindId k) => $rhs))
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $other $t))
    let ofDoc := viewDoc "Takes a sort-erased term apart one level."
    elabCommand (← `(
      $ofDoc:docComment
      def $(mkIdent (agg ++ `of)) ($t : $viewTermId) : $aggId :=
        match ($viewGetKindId $t) with $[$alts:matchAlt]*))
    elabCommand (← `(
      instance $(mkIdent (agg ++ `instTermView)):ident : $viewTermViewId $aggId :=
        ⟨$(mkIdent (agg ++ `of))⟩))
  | _ => throwUnsupportedSyntax

end

namespace Untyped

/-- Generates the sort-erased view `V` of every imported theory, `def.untyped_term_view` under
`open Cvc.Untyped`; see `Cvc.Gen.View`. -/
scoped syntax "def.term_view " ident : command

macro_rules
  | `(def.term_view $v) => `(def.untyped_term_view $v)

end Untyped

end Cvc
