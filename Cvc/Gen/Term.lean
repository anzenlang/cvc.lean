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



/-! # Term-constructor generators

Two commands, each taking the identifiers of the specification entries to generate constructors
for. They are meant to be invoked from per-theory modules, so that a user compiles only the
theories and the layer they actually import.

```lean
-- Cvc/Untyped/BitVec.lean
namespace Cvc.Untyped.Term variable [Ω]
gen_untyped% bvAdd, bvSub, bvConcat

-- Cvc/Typed/BitVec.lean
namespace Cvc.Typed.Term open Cvc.Untyped renaming Term → T variable [Ω]
gen_typed% bvAdd, bvSub, bvConcat
```

`gen_untyped%` emits the sort-erased constructor, going straight to `runUnsafe`; `gen_typed%`
emits the re-typed constructor, delegating to its untyped counterpart through the alias `T`. The
alias keeps the generator independent of where the untyped constructors live.

Requirements on a generation site:

- both layers: `import all Cvc.Basic.Env`, since the emitted bodies use the private `runUnsafe`
  bridge;
- typed only: `import all Cvc.Typed.Term.Defs`, because delegation typechecks by
  `Typed.Term α` being definitionally `Untyped.Term`, and a plain `import` keeps that body opaque;
- typed only: an alias `T` bound to the untyped term namespace, as shown above.
-/
namespace Cvc public meta section

open Lean Elab Command



/-! ## Emitted names

Every name the generated code refers to is built with `mkIdent` rather than written literally
inside a quotation. Identifiers written literally are resolved against *this* module's environment
at quotation time, and this module deliberately imports neither layer, so such a reference would
be emitted unresolved and fail at the generation site.
-/

/-- `Cvc.Env`. -/
def envId : Ident := mkIdent `Cvc.Env
/-- `runUnsafe`, the private bridge into lean-cvc5. -/
def runUnsafeId : Ident := mkIdent `runUnsafe
/-- `Cvc.ToTyp`. -/
def toTypId : Ident := mkIdent `Cvc.ToTyp
/-- `Cvc.Untyped.Term`. -/
def untypedTermId : Ident := mkIdent `Cvc.Untyped.Term
/-- `Cvc.Untyped.Terms`. -/
def untypedTermsId : Ident := mkIdent `Cvc.Untyped.Terms
/-- `Cvc.Typed.Term`. -/
def typedTermId : Ident := mkIdent `Cvc.Typed.Term
/-- `Cvc.Typed.Terms`. -/
def typedTermsId : Ident := mkIdent `Cvc.Typed.Terms
/-- `Cvc.Srt`. -/
def srtId : Ident := mkIdent `Cvc.Srt
/-- `Cvc.Srt.of`, which turns a Lean index into the sort it denotes. -/
def srtOfId : Ident := mkIdent `Cvc.Srt.of
/-- The `Cvc.Srt` constructor of the given name. -/
def srtConId (id : Name) : Ident := mkIdent (`Cvc.Srt ++ id)



/-! ## Building a sort from its element sorts

A constructor whose sort its arguments do not fix has to be handed one. It takes the sorts of its
**element** type variables, never the sort of the term it builds — `setEmpty` takes the element
sort, exactly as Lean's own `∅ : Set α` is polymorphic in `α`. The sort cvc5's method wants is
built from those here.

That sort is usually the result's, but not always: `mkEmptySequence` takes the element sort where
`mkEmptySet` takes the set sort, which is what an entry's `tmSortOf` clause records.
-/

/-- Emits an `Env Srt` expression building the sort a shape describes.

`ofVar` says where a type variable's sort comes from: a parameter for one the caller supplies, and
an argument's `getSort` for one already fixed by an argument.
-/
partial def Shape.buildSrt (ofVar : Name → MacroM (TSyntax `term)) : Shape → MacroM (TSyntax `term)
  | var name => ofVar name
  | bool => `($(srtConId `bool))
  | int => `($(srtConId `int))
  | real => `($(srtConId `real))
  | string => `($(srtConId `string))
  | regex => `($(srtConId `regex))
  | roundingMode => `($(srtConId `roundingMode))
  | seq elm => do `($(← elm.buildSrt ofVar) >>= $(srtConId `seq))
  | set elm => do `($(← elm.buildSrt ofVar) >>= $(srtConId `set))
  | bag elm => do `($(← elm.buildSrt ofVar) >>= $(srtConId `bag))
  | array idx elm => do
    `($(← idx.buildSrt ofVar) >>= fun i => $(← elm.buildSrt ofVar) >>= fun e =>
      $(srtConId `arrayTo) i e)
  | shape =>
    Macro.throwError s!"cannot build the sort of shape `{repr shape}` from its elements"



/-! ## Rendering shapes as Lean types -/

/-- Renders a size expression as a `Nat`-valued term. -/
partial def SizeExpr.render (arityStx : TSyntax `term) : SizeExpr → MacroM (TSyntax `term)
  | lit n => return Syntax.mkNumLit (toString n)
  | var n => return mkIdent n
  | add lft rgt => do `($(← lft.render arityStx) + $(← rgt.render arityStx))
  | sub lft rgt => do `($(← lft.render arityStx) - $(← rgt.render arityStx))
  | mul lft rgt => do `($(← lft.render arityStx) * $(← rgt.render arityStx))
  | .arity => return arityStx

/-- Renders a sort shape as the Lean type indexing a `Typed.Term`.

Names are emitted fully qualified so that generation sites are free to sit in whichever namespace
suits them. `arityStx` is what `SizeExpr.arity` renders to: a literal in a fixed-arity signature,
the term array's size in an n-ary one.
-/
partial def Shape.render (arityStx : TSyntax `term) : Shape → MacroM (TSyntax `term)
  | var n => return mkIdent n
  | bool => return mkIdent `Bool
  | int => return mkIdent `Int
  | real => return mkIdent `Rat
  | string => return mkIdent `String
  | regex => return mkIdent `Cvc.Regex
  | roundingMode => return mkIdent `Cvc.Float.RoundingMode
  | bitVec w => do `($(mkIdent `BitVec) $(← w.render arityStx))
  | float e s => do `($(mkIdent `Cvc.Float) $(← e.render arityStx) $(← s.render arityStx))
  | finiteField s => do `($(mkIdent `Cvc.FiniteField) $(← s.render arityStx))
  | seq e => do `($(mkIdent `Array) $(← e.render arityStx))
  | set e => do `($(mkIdent `Cvc.Set) $(← e.render arityStx))
  | bag e => do `($(mkIdent `Cvc.Bag) $(← e.render arityStx))
  | array i e => do `($(mkIdent `Cvc.TotalMap) $(← i.render arityStx) $(← e.render arityStx))
  | fn d c => do `($(← d.render arityStx) → $(← c.render arityStx))



/-! ## Shared pieces -/

/-- The `cvc5.Kind` constructor a specification builds its terms with. -/
def OpSpec.kindIdent (spec : OpSpec) : TSyntax `term :=
  mkIdent (`cvc5 ++ `Kind ++ spec.kind)

/-- Name of the n-ary variant of an operator: `<id>N`, or the spec's own choice. -/
def OpSpec.naryId (spec : OpSpec) : Ident :=
  mkIdent (spec.naryName.getD (spec.id.appendAfter "N"))

/-- Name of the defaulting n-ary variant of an operator, the n-ary name primed. -/
def OpSpec.naryPrimeId (spec : OpSpec) : Ident :=
  mkIdent ((spec.naryName.getD (spec.id.appendAfter "N")).appendAfter "'")

/-- Docstring for the `N` variant. -/
def OpSpec.naryDoc (spec : OpSpec) : String :=
  s!"N-ary version of `{spec.id}`, requires at least two elements."

/-- Docstring for the `N'` variant. -/
def OpSpec.naryPrimeDoc (spec : OpSpec) : String :=
  s!"N-ary version of `{spec.id}` with defaults for zero- and one-element arrays."

/-- Name of the nullable-lifted operator: the operator's own, suffixed with `?`. -/
def OpSpec.liftId (spec : OpSpec) : Ident := mkIdent (spec.id.appendAfter "?")

/-- Name of the nullable-lifted n-ary operator. -/
def OpSpec.liftNaryId (spec : OpSpec) : Ident := mkIdent (spec.naryId.getId.appendAfter "?")

/-- Docstring for a lifted operator. -/
def OpSpec.liftDoc (spec : OpSpec) : String :=
  s!"`{spec.id}` lifted over nullables, **strictly**: `none` unless every argument is `some`."

/-- Name of the nullable-lifted defaulting n-ary operator. -/
def OpSpec.liftNaryPrimeId (spec : OpSpec) : Ident :=
  mkIdent (spec.naryPrimeId.getId.appendAfter "?")

/-- Docstring for a lifted n-ary operator. -/
def OpSpec.liftNaryDoc (spec : OpSpec) : String :=
  s!"N-ary version of `{spec.liftId.getId}`, requires at least two elements."

/-- Docstring for a lifted defaulting n-ary operator. -/
def OpSpec.liftNaryPrimeDoc (spec : OpSpec) : String :=
  s!"N-ary version of `{spec.liftId.getId}` with defaults for zero- and one-element arrays."

/-- Creates a `docComment` node from a docstring. -/
def mkDocComment (s : String) : TSyntax ``Lean.Parser.Command.docComment :=
  mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]

/-- Looks a specification up, failing with a located error if it is not registered. -/
def getOpSpec (id : Ident) : CommandElabM OpSpec := do
  match ← findOpSpec? id.getId with
  | some spec => return spec
  | none => throwErrorAt id s!"no operator specification named `{id.getId}`; declare it with `op%`"



/-! ## Untyped generation -/

/-- Emits the sort-erased constructors for one specification entry.

Every argument and the result erase to `Untyped.Term`, so the shapes play no part beyond fixing
the arity: a pure operator kind infers its sort from its arguments, which `op%` checks.
-/
def genUntyped (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  let kind := spec.kindIdent
  let argIds := spec.args.map (mkIdent ·.name)
  -- an antiquotation inside `$[ … ]*` is iterated, so a constant emitted there has to be an array
  -- of the same length as the one it is spliced alongside
  let argTys := argIds.map (fun _ => untypedTermId)
  let indexIds := spec.indices.map mkIdent
  let indexTys := indexIds.map (fun _ => mkIdent `Nat)
  let doc := mkDocComment spec.doc
  -- a constructor takes the sorts of the type variables its arguments leave free, one each — the
  -- *element* sorts, never the sort of the term it builds
  let freeVars := if spec.tmFn.isSome then spec.unboundRetVars else #[]
  let srtIds := freeVars.map mkIdent
  let srtTys := srtIds.map (fun _ => srtId)
  let valIds := spec.valArgs.map (mkIdent ·.name)
  let valTys := spec.valArgs.map (mkIdent ·.type)
  -- a `TermManager` method takes cvc5's sizes as `UInt32`, whereas `mkOpOfIndices` takes `Nat`
  let idxArgs ← indexIds.mapM fun id => `(($id).toUInt32)
  -- three ways to build: a `TermManager` method, an `Op` carrying indices, or the kind itself
  let body ← match spec.tmFn with
    | some fn =>
      let fnId := mkIdent (`cvc5.TermManager ++ fn)
      if freeVars.isEmpty then
        `($runUnsafeId fun tm => $fnId tm $[ $idxArgs ]* $[ $valIds ]* $[ $argIds ]*)
      else
        -- a free variable's sort is a parameter; one an argument fixes comes off that argument
        let ofVar (name : Name) : MacroM (TSyntax `term) :=
          if freeVars.contains name then `(pure $(mkIdent name))
          else match spec.args.find? (·.shape == .var name) with
            | some arg => `(($(mkIdent arg.name)).getSort)
            | none => Macro.throwError
              s!"`{spec.id}` cannot recover the sort of `{name}`: no argument has it as its shape"
        let wanted ← (spec.sortArg.getD spec.ret).buildSrt ofVar
        let srtId := mkIdent (← MonadQuotation.addMacroScope `builtSrt)
        `($wanted >>= fun $srtId =>
          $runUnsafeId fun tm => $fnId tm $[ $idxArgs ]* $srtId $[ $valIds ]* $[ $argIds ]*)
    | none =>
      if spec.indices.isEmpty then
        `($runUnsafeId fun tm => tm.mkTerm $kind #[ $argIds,* ])
      else
        `($runUnsafeId fun tm => do
          tm.mkTermOfOp (← tm.mkOpOfIndices $kind #[ $indexIds,* ]) #[ $argIds,* ])
  let mut cmds := #[
    ← `(
      $doc:docComment
      def $(mkIdent spec.id):ident $[ ($indexIds : $indexTys) ]* $[ ($srtIds : $srtTys) ]*
        $[ ($valIds : $valTys) ]* $[ ($argIds : $argTys) ]*
      : $envId $untypedTermId :=
        $body
    )
  ]

  if spec.nary matches .never then return cmds

  let termsId := mkIdent `terms
  let validId := mkIdent `atLeastTwoElements
  let naryDoc := mkDocComment spec.naryDoc
  cmds := cmds.push <| ← `(
    $naryDoc:docComment
    def $(spec.naryId):ident ($termsId : $untypedTermsId)
      ($validId : 2 ≤ $(termsId).size := by
        (try grind) <;> fail "failed to prove term array has at least two elements")
    : $envId $untypedTermId :=
      let _ := $validId
      $runUnsafeId fun tm => tm.mkTerm $kind $termsId
  )

  if let .arrayWithUnit unit := spec.nary then
    let unitTerm ← match unit with
      | .bool b =>
        let lit := mkIdent (if b then `Bool.true else `Bool.false)
        `($(mkIdent `Cvc.Untyped.Term.mkBool) $lit)
      | .int i => `($(mkIdent `Cvc.Untyped.Term.mkInt) $(Syntax.mkNumLit (toString i)))
    let naryPrimeDoc := mkDocComment spec.naryPrimeDoc
    cmds := cmds.push <| ← `(
      $naryPrimeDoc:docComment
      def $(spec.naryPrimeId):ident ($termsId : $untypedTermsId)
        (on0 : $envId $untypedTermId := $unitTerm)
        (on1 : $untypedTermId → $envId $untypedTermId := pure)
      : $envId $untypedTermId :=
        if $(termsId).size = 0 then on0
        else if h : $(termsId).size = 1 then on1 $(termsId)[0]
        else $runUnsafeId fun tm => tm.mkTerm $kind $termsId
    )

  return cmds

/-! ## Nullable lifting, sort-erased

`nullable.lift` applies an operator to the values inside its nullable arguments, answering `none`
unless every one of them is `some`. It takes a `Kind` and the terms, so the lifted body is shorter
than the plain one — there is no sort to build and no `Op` to make.

Arity is right by construction here, which it would not be if a `Kind` were exposed to a caller:
cvc5 validates nothing, and `mkNullableLift .NOT #[x, y]` cheerfully builds the malformed
`(nullable.lift (lambda (a b) (not a b)) x y)`. Generating from the specification means the
argument count and the n-ary form both come from the entry that already knows them.
-/

/-- Emits the sort-erased nullable-lifted constructors for one entry, if it has any. -/
def genUntypedNullable (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  unless spec.isLiftable do return #[]
  let kind := spec.kindIdent
  let argIds := spec.args.map (mkIdent ·.name)
  let argTys := argIds.map (fun _ => untypedTermId)
  let doc := mkDocComment spec.liftDoc
  let mut cmds := #[
    ← `(
      $doc:docComment
      def $(spec.liftId):ident $[ ($argIds : $argTys) ]* : $envId $untypedTermId :=
        $runUnsafeId fun tm => tm.mkNullableLift $kind #[ $argIds,* ]
    )
  ]

  if spec.nary matches .never then return cmds

  let termsId := mkIdent `terms
  let validId := mkIdent `atLeastTwoElements
  let naryDoc := mkDocComment spec.liftNaryDoc
  cmds := cmds.push <| ← `(
    $naryDoc:docComment
    def $(spec.liftNaryId):ident ($termsId : $untypedTermsId)
      ($validId : 2 ≤ $(termsId).size := by
        (try grind) <;> fail "failed to prove term array has at least two elements")
    : $envId $untypedTermId :=
      let _ := $validId
      $runUnsafeId fun tm => tm.mkNullableLift $kind $termsId
  )

  if let .arrayWithUnit unit := spec.nary then
    -- the unit of a *lifted* operator is the unit wrapped in `some`, since every argument and the
    -- result of the lifted form are nullable
    let someId := mkIdent `Cvc.Untyped.Term.nullableSome
    let unitTerm ← match unit with
      | .bool b =>
        let lit := mkIdent (if b then `Bool.true else `Bool.false)
        `($(mkIdent `Cvc.Untyped.Term.mkBool) $lit >>= $someId)
      | .int i =>
        `($(mkIdent `Cvc.Untyped.Term.mkInt) $(Syntax.mkNumLit (toString i)) >>= $someId)
    let primeDoc := mkDocComment spec.liftNaryPrimeDoc
    cmds := cmds.push <| ← `(
      $primeDoc:docComment
      def $(spec.liftNaryPrimeId):ident ($termsId : $untypedTermsId)
        (on0 : $envId $untypedTermId := $unitTerm)
        (on1 : $untypedTermId → $envId $untypedTermId := pure)
      : $envId $untypedTermId :=
        if $(termsId).size = 0 then on0
        else if h : $(termsId).size = 1 then on1 $(termsId)[0]
        else $runUnsafeId fun tm => tm.mkNullableLift $kind $termsId
    )

  return cmds

/-- Emits the sort-erased lifted constructors for one entry. -/
def emitUntypedNullable (spec : OpSpec) : CommandElabM Unit := do
  for cmd in ← liftMacroM (genUntypedNullable spec) do
    elabCommand cmd

/-- Generates the sort-erased lifted constructors for the named entries. -/
syntax (name := genUntypedNullableStx) "gen_untyped_nullable% " ident,+ : command

/-- Generates the sort-erased lifted constructors for every entry a module declares. -/
syntax (name := genUntypedNullableFromStx) "gen_untyped_nullable% " "from " ident : command

@[command_elab genUntypedNullableStx]
def elabGenUntypedNullable : CommandElab
  | `(gen_untyped_nullable% $ids,*) => do
    for id in ids.getElems do
      emitUntypedNullable (← getOpSpec id)
  | _ => throwUnsupportedSyntax

@[command_elab genUntypedNullableFromStx]
def elabGenUntypedNullableFrom : CommandElab
  | `(gen_untyped_nullable% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then
      throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    for spec in specs do emitUntypedNullable spec
  | _ => throwUnsupportedSyntax



/-! ## DSL grammar generation

The `smtTerm` grammar rule of an operator is emitted alongside its *untyped* constructor,
and only there: the typed constructors delegate to the untyped ones, so a typed theory module
always imports its untyped counterpart and inherits the grammar. Emitting from both layers would
declare the same rule twice.

Rules are named `smtOp.<shape>.<id>`, which under the enclosing namespace becomes
`…Term.smtOp.binary.and` and so on. `Cvc.expandSmt` dispatches on those trailing
three components, so it needs no knowledge of where generation happened.
-/

/-- Name of an operator's generated grammar rule, relative to the generation site's namespace. -/
def smtRuleId (shape id : Name) : Ident :=
  mkIdent (`smtOp ++ shape ++ id)

/-- Emits the `smtTerm` grammar rules for one specification entry's notation. -/
def genSmtSyntax (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  let cat := mkIdent `smtTerm
  match spec.smtNotation with
  | .none => return #[]
  | .pref sym prec argPrec =>
    let prec := Syntax.mkNumLit (toString prec)
    let argPrec := Syntax.mkNumLit (toString argPrec)
    let atom := Syntax.mkStrLit s!"{sym} "
    return #[← `(command|
      syntax:$prec (name := $(smtRuleId `prefix spec.id)) $atom:str $cat:ident:$argPrec : $cat
    )]
  | .inf sym prec assoc =>
    -- left-associative binds its right operand tighter, right-associative its left one
    let lftPrec := Syntax.mkNumLit (toString (if assoc matches .left then prec else prec + 1))
    let rgtPrec := Syntax.mkNumLit (toString (if assoc matches .left then prec + 1 else prec))
    let precStx := Syntax.mkNumLit (toString prec)
    let atom := Syntax.mkStrLit s!" {sym} "
    let mut cmds := #[← `(command|
      syntax:$precStx (name := $(smtRuleId `binary spec.id))
        $cat:ident:$lftPrec $atom:str $cat:ident:$rgtPrec : $cat
    )]
    -- the bracket form exists only when there is an n-ary function to expand to
    unless spec.nary matches .never do
      let bracket := Syntax.mkStrLit s!"{sym}["
      cmds := cmds.push <| ← `(command|
        syntax (name := $(smtRuleId `nary spec.id)) $bracket:str $cat:ident,+,? "]" : $cat
      )
    return cmds

/-- Emits the sort-erased constructors, and the DSL grammar, for one entry. -/
def emitUntyped (spec : OpSpec) : CommandElabM Unit := do
  for cmd in ← liftMacroM (genUntyped spec) do
    elabCommand cmd
  for cmd in ← liftMacroM (genSmtSyntax spec) do
    elabCommand cmd

/-- Generates the sort-erased constructors for the named specification entries. -/
syntax (name := genUntypedStx) "gen_untyped% " ident,+ : command

/-- Generates the sort-erased constructors for every entry a specification module declares. -/
syntax (name := genUntypedFromStx) "gen_untyped% " "from " ident : command

@[command_elab genUntypedStx]
def elabGenUntyped : CommandElab
  | `(gen_untyped% $ids,*) => do
    for id in ids.getElems do
      emitUntyped (← getOpSpec id)
  | _ => throwUnsupportedSyntax

@[command_elab genUntypedFromStx]
def elabGenUntypedFrom : CommandElab
  | `(gen_untyped% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then
      throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    for spec in specs do emitUntyped spec
  | _ => throwUnsupportedSyntax



/-! ## Typed generation -/

/-- Emits the binders a typed constructor needs: type, size, `Ord` and refinement classes.

A type variable carrying refinement classes also gets a `ToTyp` binder, since a refinement such as
`IsArith` is stated over the variable's `Typ` and so takes `ToTyp` as an instance argument.
-/
def typedBinders (spec : OpSpec) : MacroM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut binders := #[]
  for tyVar in spec.tyVars do
    binders := binders.push <| ← `(bracketedBinder| { $(mkIdent tyVar.name) : Type })
  for sizeVar in spec.sizeVars do
    binders := binders.push <| ← `(bracketedBinder| { $(mkIdent sizeVar) : Nat })
  for ordVar in spec.ordVars do
    binders := binders.push <| ← `(bracketedBinder| [ $(mkIdent `Ord) $(mkIdent ordVar) ])
  -- a constructor computes its own sort with `Srt.of`, so it needs `ToTyp` on every variable
  let needsToTyp := spec.tmFn.isSome && !spec.unboundRetVars.isEmpty
  for tyVar in spec.tyVars do
    unless tyVar.classes.isEmpty && !needsToTyp do
      binders := binders.push <| ← `(bracketedBinder| [ $toTypId $(mkIdent tyVar.name) ])
    for cls in tyVar.classes do
      binders := binders.push <| ← `(bracketedBinder| [ $(mkIdent cls) $(mkIdent tyVar.name) ])
  return binders

/-- Emits the re-typed constructors for one specification entry, delegating to the untyped ones. -/
def genTyped (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  let binders ← typedBinders spec
  let argIds := spec.args.map (mkIdent ·.name)
  -- `SizeExpr.arity` means the number of term arguments: a literal here, `terms.size` below
  let fixedArity := Syntax.mkNumLit (toString spec.args.size)
  let argTypes ← spec.args.mapM (Shape.render fixedArity ·.shape)
  let typedTermIds := argTypes.map (fun _ => typedTermId)
  let retType ← spec.ret.render fixedArity
  let untypedId := mkIdent (`T ++ spec.id)
  let indexIds := spec.indices.map mkIdent
  let indexTys := indexIds.map (fun _ => mkIdent `Nat)
  let doc := mkDocComment spec.doc
  -- a constructor whose sort is not fixed by its arguments recovers it from the result's index
  let valIds := spec.valArgs.map (mkIdent ·.name)
  let valTys := spec.valArgs.map (mkIdent ·.type)
  -- the sort-erased constructor takes one *element* sort per type variable the arguments leave
  -- free, so the index supplies exactly those and never the sort of the term built
  let freeVars := if spec.tmFn.isSome then spec.unboundRetVars else #[]
  let body ← if freeVars.isEmpty then
      `($untypedId $[ $indexIds ]* $[ $valIds ]* $[ $argIds ]*)
    else
      let srtIds ← freeVars.mapM fun v =>
        return mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple s!"srtOf{v}"))
      let mut call ← `($untypedId $[ $srtIds ]* $[ $valIds ]* $[ $argIds ]*)
      for idx in [0 : freeVars.size] do
        let jdx := freeVars.size - 1 - idx
        call ← `($srtOfId $(mkIdent freeVars[jdx]!) >>= fun $(srtIds[jdx]!) => $call)
      pure call
  let mut cmds := #[
    ← `(
      $doc:docComment
      def $(mkIdent spec.id):ident $[ ($indexIds : $indexTys) ]* $[ $binders ]*
        $[ ($valIds : $valTys) ]* $[ ($argIds : $typedTermIds $argTypes) ]*
      : $envId ($typedTermId $retType) :=
        $body
    )
  ]

  if spec.nary matches .never then return cmds

  -- the n-ary variants take a homogeneous term array, so they need every *argument* to share one
  -- shape; the result shape is free, which is what `equal`/`lt`/… (`α → α → bool`) rely on
  let some firstArg := spec.args[0]? | return cmds
  unless spec.args.all (·.shape == firstArg.shape) do
    return cmds
  let termsId := mkIdent `terms
  let validId := mkIdent `atLeastTwoElements
  -- in the n-ary signature the arity is the array's size, so a result that depends on it depends
  -- on a runtime value
  let naryArity ← `(($termsId).size)
  let naryRetType ← spec.ret.render naryArity
  let naryArgType ← firstArg.shape.render naryArity
  let naryDoc := mkDocComment spec.naryDoc
  cmds := cmds.push <| ← `(
    $naryDoc:docComment
    def $(spec.naryId):ident $[ $binders ]* ($termsId : $typedTermsId $naryArgType)
      ($validId : 2 ≤ $(termsId).size := by
        (try grind) <;> fail "failed to prove term array has at least two elements")
    : $envId ($typedTermId $naryRetType) :=
      $(mkIdent (`T ++ spec.naryId.getId)) $termsId $validId
  )

  if spec.nary matches .arrayWithUnit _ then
    let naryPrimeDoc := mkDocComment spec.naryPrimeDoc
    cmds := cmds.push <| ← `(
      $naryPrimeDoc:docComment
      def $(spec.naryPrimeId):ident $[ $binders ]* ($termsId : $typedTermsId $naryArgType)
      : $envId ($typedTermId $naryRetType) :=
        $(mkIdent (`T ++ spec.naryPrimeId.getId)) $termsId
    )

  return cmds

/-- Emits the re-typed constructors for one entry. -/
def emitTyped (spec : OpSpec) : CommandElabM Unit := do
  for cmd in ← liftMacroM (genTyped spec) do
    elabCommand cmd

/-- Generates the re-typed constructors for the named specification entries. -/
syntax (name := genTypedStx) "gen_typed% " ident,+ : command

/-- Generates the re-typed constructors for every entry a specification module declares. -/
syntax (name := genTypedFromStx) "gen_typed% " "from " ident : command

@[command_elab genTypedStx]
def elabGenTyped : CommandElab
  | `(gen_typed% $ids,*) => do
    for id in ids.getElems do
      emitTyped (← getOpSpec id)
  | _ => throwUnsupportedSyntax

@[command_elab genTypedFromStx]
def elabGenTypedFrom : CommandElab
  | `(gen_typed% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then
      throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    for spec in specs do emitTyped spec
  | _ => throwUnsupportedSyntax



/-! ## Nullable lifting, typed

Every term argument and the result gain an `Option`; everything else is the plain operator's
signature unchanged — type and size variables, `Ord` binders, and the refinement classes. The body
delegates, as the plain typed constructors do.

`Option (Option α)` needs no special case: `add?` at `α := Option Int` would demand
`IsArith (Option Int)`, and no such instance exists.
-/

/-- Emits the re-typed nullable-lifted constructors for one entry, if it has any. -/
def genTypedNullable (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  unless spec.isLiftable do return #[]
  let binders ← typedBinders spec
  let argIds := spec.args.map (mkIdent ·.name)
  let fixedArity := Syntax.mkNumLit (toString spec.args.size)
  let argTypes ← spec.args.mapM fun arg => do
    `($(mkIdent `Option) $(← arg.shape.render fixedArity))
  let typedTermIds := argTypes.map (fun _ => typedTermId)
  let retType ← do `($(mkIdent `Option) $(← spec.ret.render fixedArity))
  let untypedId := mkIdent (`T ++ spec.liftId.getId)
  let doc := mkDocComment spec.liftDoc
  let mut cmds := #[
    ← `(
      $doc:docComment
      def $(spec.liftId):ident $[ $binders ]* $[ ($argIds : $typedTermIds $argTypes) ]*
      : $envId ($typedTermId $retType) :=
        $untypedId $[ $argIds ]*
    )
  ]

  if spec.nary matches .never then return cmds

  -- as for the plain n-ary variants, a homogeneous term array needs every argument to share a shape
  let some firstArg := spec.args[0]? | return cmds
  unless spec.args.all (·.shape == firstArg.shape) do
    return cmds
  let termsId := mkIdent `terms
  let validId := mkIdent `atLeastTwoElements
  let naryArity ← `(($termsId).size)
  let naryRetType ← do `($(mkIdent `Option) $(← spec.ret.render naryArity))
  let naryArgType ← do `($(mkIdent `Option) $(← firstArg.shape.render naryArity))
  let naryDoc := mkDocComment spec.liftNaryDoc
  cmds := cmds.push <| ← `(
    $naryDoc:docComment
    def $(spec.liftNaryId):ident $[ $binders ]* ($termsId : $typedTermsId $naryArgType)
      ($validId : 2 ≤ $(termsId).size := by
        (try grind) <;> fail "failed to prove term array has at least two elements")
    : $envId ($typedTermId $naryRetType) :=
      $(mkIdent (`T ++ spec.liftNaryId.getId)) $termsId $validId
  )

  if spec.nary matches .arrayWithUnit _ then
    let primeDoc := mkDocComment spec.liftNaryPrimeDoc
    cmds := cmds.push <| ← `(
      $primeDoc:docComment
      def $(spec.liftNaryPrimeId):ident $[ $binders ]* ($termsId : $typedTermsId $naryArgType)
      : $envId ($typedTermId $naryRetType) :=
        $(mkIdent (`T ++ spec.liftNaryPrimeId.getId)) $termsId
    )

  return cmds

/-- Emits the re-typed lifted constructors for one entry. -/
def emitTypedNullable (spec : OpSpec) : CommandElabM Unit := do
  for cmd in ← liftMacroM (genTypedNullable spec) do
    elabCommand cmd

/-- Generates the re-typed lifted constructors for the named entries. -/
syntax (name := genTypedNullableStx) "gen_typed_nullable% " ident,+ : command

/-- Generates the re-typed lifted constructors for every entry a module declares. -/
syntax (name := genTypedNullableFromStx) "gen_typed_nullable% " "from " ident : command

@[command_elab genTypedNullableStx]
def elabGenTypedNullable : CommandElab
  | `(gen_typed_nullable% $ids,*) => do
    for id in ids.getElems do
      emitTypedNullable (← getOpSpec id)
  | _ => throwUnsupportedSyntax

@[command_elab genTypedNullableFromStx]
def elabGenTypedNullableFrom : CommandElab
  | `(gen_typed_nullable% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then
      throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    for spec in specs do emitTypedNullable spec
  | _ => throwUnsupportedSyntax
