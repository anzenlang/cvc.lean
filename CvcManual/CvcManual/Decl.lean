/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import VersoManual
public meta import VersoManual

/-! # `{decl}`: a declaration's documentation, with a body the reader can fold away

`{docstring X}` renders a box holding `X`'s signature, then its docstring followed by its fields,
methods or constructors. `{decl X}` renders the same box, except that everything below the signature
is a block the reader can fold and unfold, and that it can hold a definition's **equations**, one
per equation theorem Lean generates for it: `f x = body` for a plain definition, one per case for
one defined by pattern matching.

What the body holds and whether it starts folded depend on the declaration:

| declaration | body starts | equations |
|---|---|---|
| a type: a definition whose type ends in a sort, such as an alias | open | if its body is exposed |
| a structure or class | folded beyond two fields | — |
| an inductive type | folded beyond two constructors | — |
| anything else: a function, a value, a theorem | folded | no |

`+folded` and `-folded` override where the body starts, `+equations` and `-equations` whether the
equations are shown. An **unexposed** body is never shown, even with `+equations`, which is then an
error: a definition whose body a plain import of its module does not see — `Cvc.Typed.Term`,
`Cvc.Srt` — is opaque to the library's users, and the manual keeps it so. A body is only available
at all where the page has `import all` of the module declaring it, as for the docstring.
-/

open Lean Elab Meta
open Verso Doc Elab ArgParse
open Verso.Genre Manual

namespace CvcManual

public section

/-- The body of a documentation box, which a reader can fold and unfold, `folded` to begin with.

`summary` is the line a folded body shows.
-/
def Block.foldable (folded : Bool) (summary : String) : Block where
  name := `CvcManual.Block.foldable
  data := ToJson.toJson (folded, summary)

/-- The style of a foldable body. -/
def foldableCss : String := r#"
.namedocs .text > details.cvc-fold > summary {
  cursor: pointer;
  margin: var(--verso--box-padding) 0;
  color: #57606a;
}
.namedocs .text > details.cvc-fold[open] > summary {
  margin-bottom: 0;
}
"#

@[block_extension Block.foldable]
def foldable.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _info contents => do
    return .seq (← contents.mapM goB)
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (folded, summary) := FromJson.fromJson? (α := Bool × String) info
        | do reportError "Failed to deserialize a foldable body"; return .empty
      let attrs := #[("class", "cvc-fold")] ++ if folded then #[] else #[("open", "")]
      return .tag "details" attrs <| .seq #[
        .tag "summary" #[] (.text true summary),
        .seq (← contents.mapM goB)
      ]
  extraCss := [foldableCss]

/-- What `{decl}` takes: the declaration, and how to present its body. -/
structure DeclConfig where
  /-- The declaration. -/
  name : Ident × Name
  /-- Label to show instead of the default one, such as `def` or `inductive type`. -/
  label : Option String
  /-- Everything else: the flags `+folded`/`-folded` and `+equations`/`-equations`. -/
  flags : Array Doc.Arg

section
variable [Monad m] [MonadOptions m] [MonadEnv m] [MonadLiftT CoreM m] [MonadLiftT MetaM m]
variable [MonadError m] [MonadLog m] [AddMessageContext m] [Elab.MonadInfoTree m]

meta def DeclConfig.parse : ArgParse m DeclConfig :=
  DeclConfig.mk <$>
    .positional `name .documentableName <*>
    .named `label .string true <*>
    .remaining

meta instance : FromArgs DeclConfig m := ⟨DeclConfig.parse⟩

end

/-- The value of each flag given, `none` for one left out; anything else is an error. -/
meta def DeclConfig.flagValues (cfg : DeclConfig) : DocElabM (Option Bool × Option Bool) := do
  let mut folded := none
  let mut equations := none
  for arg in cfg.flags do
    match arg with
    | .flag _ id v =>
      match id.getId with
      | `folded => folded := some v
      | `equations => equations := some v
      | other => throwErrorAt arg.syntax m!"unknown flag `{other}`: `\{decl}` takes `folded` and \
          `equations`"
    | _ => throwErrorAt arg.syntax "unexpected argument: `\{decl}` takes a declaration, the flags \
        `+folded`/`-folded` and `+equations`/`-equations`, and `label`"
  return (folded, equations)
-- Read by hand rather than with `ArgParse.flag`, whose default is fixed: a flag left out has to be
-- told apart from one given, since the default depends on the declaration.

/-- Highlighted code for a pretty-printed expression, with the hovers and links Verso gives code. -/
meta def renderCode (fmt : FormatWithInfos) : MetaM SubVerso.Highlighting.Highlighted := do
  let ctx : Elab.ContextInfo := {
    env           := ← getEnv
    mctx          := ← getMCtx
    options       := ← getOptions
    currNamespace := ← getCurrNamespace
    openDecls     := ← getOpenDecls
    fileMap       := default
    ngen          := ← getNGen
  }
  let tagged := Lean.Widget.TaggedText.prettyTagged (w := 72) fmt.fmt
  let code ← Lean.Widget.tagCodeInfos ctx fmt.infos tagged
  let hlCtx : SubVerso.Highlighting.Context := ⟨{}, false, false, [], false, (← IO.mkRef {})⟩
  (SubVerso.Highlighting.renderTagged none code : ReaderT SubVerso.Highlighting.Context MetaM _)
    hlCtx

/-- A definition's equations, as Lean states them in its equation theorems, `#[]` if it has none.

An equation is shown as `lhs = rhs` over the variables it quantifies, or as the whole statement when
it holds only under hypotheses — a case of an overlapping match, say.
-/
meta def equationsOf (name : Name) : MetaM (Array SubVerso.Highlighting.Highlighted) := do
  let some eqns ← getEqnsFor? name | return #[]
  eqns.mapM fun eqn => do
    let type := (← getConstInfo eqn).type
    forallTelescope type fun xs body => do
      let conditional ← xs.anyM fun x => do isProp (← inferType x)
      let fmt ← withOptions (·.setBool `pp.tagAppFns true) <|
        PrettyPrinter.ppExprWithInfos (if conditional then type else body)
      renderCode fmt

/-- The sections Verso's `{docstring}` adds below a docstring: a structure's constructor, parents
and fields, an inductive type's constructors; nothing for any other declaration. -/
meta def extrasOf (name : Name) (declType : Block.Docstring.DeclType) : DocElabM (Array Term) :=
  match declType with
  | .structure isClass constructor? _ fieldInfo parents _ => do
    let ctorRow : Option Term ← constructor?.mapM fun constructor => do
      let header := if isClass then "Instance Constructor" else "Constructor"
      let sigDesc : Array Term ←
        if let some docs := constructor.docstring? then
          let some mdAst := MD4Lean.parse docs
            | throwError "Failed to parse docstring as Markdown"
          mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
        else pure (#[] : Array Term)
      let sig ← ``(Verso.Doc.Block.other
        (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
      ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])
    let parentsRow : Option Term ← do
      if parents.isEmpty then pure none
      else
        let inh ← ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
        some <$> ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.docstringSection "Extends") #[$inh])
    let fieldsRow : Option Term ← do
      let header := if isClass then "Methods" else "Fields"
      let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
      let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
        let inheritedFrom : Option Nat :=
          i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
        let sigDesc : Array Term ←
          if let some docs := i.docString? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM
              (blockFromMarkdownWithLean <| name :: (constructor?.map ([·.name])).getD [])
          else pure (#[] : Array Term)
        ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.fieldSignature $(quote i.visibility) $(quote i.fieldName)
            $(quote i.type) $(quote inheritedFrom) $(quote <| parents.map (·.parent)))
          #[$sigDesc,*])
      if fieldSigs.isEmpty then pure none
      else some <$> ``(Verso.Doc.Block.other
        (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])
    pure <| ctorRow.toArray ++ parentsRow.toArray ++ fieldsRow.toArray
  | .inductive ctors .. => do
    let ctorSigs : Array Term ←
      -- constructor docs are elaborated in the type's namespace
      ctors.mapM fun c => withTheReader Core.Context ({· with currNamespace := name}) do
        let sigDesc ←
          if let some docs := c.docstring? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (blockFromMarkdownWithLean [name, c.name])
          else pure (#[] : Array Term)
        ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
    pure #[← ``(Verso.Doc.Block.other
      (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
  | _ => pure #[]
-- A copy of the `getExtras` helper of Verso's `docstring` block command, which Verso does not
-- export.

/-- `n` things, `noun` pluralized as needed. -/
meta def countOf (n : Nat) (noun : String) : String :=
  s!"{n} {noun}{if n == 1 then "" else "s"}"

/-- The line a folded body shows: what unfolding it reveals. -/
meta def summaryOf (documented : Bool) (declType : Block.Docstring.DeclType) (equations : Nat)
: String :=
  let parts :=
    (if documented then ["documentation"] else []) ++
    (match declType with
      | .structure isClass _ _ fields .. =>
        let fields := fields.filter (·.subobject?.isNone)
        if fields.isEmpty then [] else [countOf fields.size (if isClass then "method" else "field")]
      | .inductive ctors .. => if ctors.isEmpty then [] else [countOf ctors.size "constructor"]
      | _ => []) ++
    (if equations == 0 then [] else [countOf equations "equation"])
  let text := match parts.reverse with
    | [] => "details"
    | [one] => one
    | last :: rest => ", ".intercalate rest.reverse ++ " and " ++ last
  text.capitalize

/-- Whether a declaration is a type: its type, past the binders, is a sort. -/
meta def isTypeValued (name : Name) : MetaM Bool := do
  forallTelescope (← getConstInfo name).type fun _ body => return body.isSort

/-- Whether a definition exposes its body, that is, whether a plain import of its module sees it.

Lean answers through the page's public scope, which holds only what the page imports publicly, so a
declaration missing from it is an error rather than an unexposed one.
-/
meta def exposesBody (x : Ident) (name : Name) : DocElabM Bool := do
  let some info := (← getEnv).setExporting true |>.find? name
    | throwErrorAt x "cannot tell whether `{name}` exposes its body: the page must import its \
        module publicly, through `public import Cvc` for instance"
  return info.hasValue

/-- Whether a declaration's body starts folded when no flag says: a type's body starts open, a
structure's or an inductive type's only up to two fields or constructors, anything else's folded. -/
meta def foldedByDefault (declType : Block.Docstring.DeclType) (typeValued : Bool) : Bool :=
  match declType with
  | .structure _ _ _ fields .. => (fields.filter (·.subobject?.isNone)).size > 2
  | .inductive ctors .. => ctors.size > 2
  | .def _ => !typeValued
  | _ => true

/-- A declaration's documentation box, whose body — docstring, fields or constructors, equations —
the reader can fold and unfold.

Whether the body starts folded, and whether a definition's equations are shown, depend on the
declaration; `+folded`/`-folded` and `+equations`/`-equations` override that, and `label` replaces
the box's label, as for `{docstring}`. An unexposed definition's equations are never shown.
-/
@[block_command]
meta def decl : BlockCommandOf DeclConfig
  | cfg@⟨(x, name), customLabel, _⟩ => do
    let (folded?, equations?) ← cfg.flagValues
    Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")
    let docs? ← getDocString? (← getEnv) name
    let docBlocks ← match docs? with
      | none => pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwErrorAt x "Failed to parse docstring as Markdown"
        ast.blocks.mapM (blockFromMarkdownWithLean [name])
    let declType ← Block.Docstring.DeclType.ofName name
    let signature ← Signature.forName name
    let extras ← extrasOf name declType
    let typeValued ← isTypeValued name
    let isDef := declType matches .def _
    let equations ← match equations? with
      | some true =>
        unless isDef do throwErrorAt x "`{name}` is not a definition, so it has no equations"
        unless ← exposesBody x name do
          throwErrorAt x "`{name}` does not expose its body, so its equations are not shown"
        pure true
      | some false => pure false
      | none => if isDef && typeValued then exposesBody x name else pure false
    let folded := folded?.getD (foldedByDefault declType typeValued)
    let eqns ←
      if equations then
        try equationsOf name
        catch e =>
          throwErrorAt x m!"cannot show the equations of `{name}`: {e.toMessageData}\n\n\
            The page may need `import all` of the module declaring it; `-equations` leaves them \
            out."
      else pure #[]
    let eqnSection : Array Term ←
      if eqns.isEmpty then pure #[]
      else
        let eqnBlocks ← eqns.mapM fun hl =>
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.leanFromMarkdown $(quote hl)) #[])
        pure #[← ``(Verso.Doc.Block.other
          (Verso.Genre.Manual.Block.docstringSection "Equations") #[$eqnBlocks,*])]
    let summary := summaryOf docs?.isSome declType eqns.size
    let altNames ← getStoredSuggestions name
    ``(Verso.Doc.Block.other
        (Verso.Genre.Manual.Block.docstring
          $(quote name) $(quote declType) $(quote signature) $(quote customLabel)
          $(quote altNames.toArray))
        #[Verso.Doc.Block.other (CvcManual.Block.foldable $(quote folded) $(quote summary))
          #[$(docBlocks ++ extras ++ eqnSection),*]])
-- Mirrors Verso's own `docstring` block command, which builds the same box with the same parts, so
-- that cross-references, hovers and the index treat the two alike; the body is what differs.

end

end CvcManual
