import Lean
import Assay.Collect

/-!
Reading the source of a declaration, and elaborating an edited copy of it under a new name.

A mutant of `f` is elaborated as a new declaration `f_assay` next to `f`, from `f`'s source text
with the edit applied and every reference to a renamed function rewritten. Functions that call
`f` are copied the same way, so that they call the mutant.
-/

open Lean Meta Elab Command Parser

namespace Assay

/-- A parsed source file. -/
structure SourceFile where
  /-- The file's text. -/
  text : String
  /-- The commands after the header, with positions into `text`. -/
  commands : Array Syntax
  deriving Inhabited

/-- The `.lean` file of a module: on `LEAN_SRC_PATH`, or next to the package that built its
`.olean`. -/
def sourcePathOf (mod : Name) : IO System.FilePath := do
  if let some p ← (← getSrcSearchPath).findModuleWithExt "lean" mod then
    return p
  let olean ← findOLean mod
  let mut root := olean
  for _ in [0:mod.components.length + 3] do
    root := root.parent.getD root
  let p := mod.components.foldl (fun p c => p / c.toString) (root.parent.getD root)
  let p := p.withExtension "lean"
  if ← p.pathExists then return p
  throw <| IO.userError s!"cannot find the source of module {mod}"

/-- Parses a file into its commands. -/
def parseSource (fileName text : String) : CommandElabM SourceFile := do
  let inputCtx := mkInputContext text fileName
  let (_, state, _) ← liftM (m := IO) <| parseHeader inputCtx
  let env ← getEnv
  let pmctx : ParserModuleContext := { env, options := ← getOptions }
  let mut state := state
  let mut cmds := #[]
  let mut log := {}
  repeat
    let (cmd, s, l) := parseCommand inputCtx pmctx state log
    state := s
    log := l
    if isTerminalCommand cmd then break
    cmds := cmds.push cmd
  return { text, commands := cmds }

/-- The source of the module or file that declares `n`. -/
def sourceOf (n : Name) : CommandElabM SourceFile := do
  let env ← getEnv
  if env.getModuleIdxFor? n |>.isNone then
    let ctx ← read
    return ← parseSource ctx.fileName ctx.fileMap.source
  let path ← sourcePathOf (moduleOf env n)
  parseSource path.toString (← IO.FS.readFile path)

/-- The command of a source file that declares `n`. -/
def commandOf (src : SourceFile) (n : Name) : CommandElabM Syntax := do
  let some ranges ← findDeclarationRanges? n
    | throwError "no source position for {n}"
  let fileMap := FileMap.ofString src.text
  let pos := fileMap.ofPosition ranges.range.pos
  for cmd in src.commands do
    let some s := cmd.getPos? | continue
    let some e := cmd.getTailPos? | continue
    if s ≤ pos && pos < e then return cmd
  throwError "cannot find the command that declares {n}"

/-- The text of a syntax node. -/
def textOf (src : SourceFile) (stx : Syntax) : String :=
  match stx.getPos?, stx.getTailPos? with
  | some s, some e => String.Pos.Raw.extract src.text s e
  | _, _ => ""

/-- A replacement of the text between two positions. -/
structure Edit where
  start : String.Pos.Raw
  stop : String.Pos.Raw
  replacement : String
  deriving Inhabited

/-- Applies non-overlapping edits to a span of a text. -/
def applyEdits (text : String) (start stop : String.Pos.Raw) (edits : Array Edit) : String := Id.run do
  let edits := edits.qsort (fun a b => a.start < b.start)
  let mut out := ""
  let mut cur := start
  for e in edits do
    out := out ++ String.Pos.Raw.extract text cur e.start ++ e.replacement
    cur := e.stop
  return out ++ String.Pos.Raw.extract text cur stop

/-- The name with `suffix` added to its last component. -/
def suffixed (n : Name) (suffix : String) : Name :=
  match n with
  | .str p s => .str p (s ++ suffix)
  | _ => n

/-- The suffix of the names mutants are elaborated under. -/
def mutantSuffix : String := "_assay"

/-- The name the copy of `n` gets when its source is elaborated in the current module: `n` with
`mutantSuffix`, and for a private `n`, private to the current module. -/
def mutantName (env : Environment) (n : Name) : Name :=
  match privateToUserName? n with
  | some u => mkPrivateName env (suffixed u mutantSuffix)
  | none => suffixed n mutantSuffix

/-- Edits that rename every identifier whose last component is the last component of a renamed
declaration. -/
partial def renameEdits (renamed : Array Name) (suffix : String) (stx : Syntax) : Array Edit :=
  let lasts := renamed.filterMap fun n => match n with | .str _ s => some s | _ => none
  go lasts stx #[]
where
  go (lasts : Array String) (stx : Syntax) (acc : Array Edit) : Array Edit :=
    match stx with
    | .ident _ raw val _ =>
      match val, stx.getPos?, stx.getTailPos? with
      | .str _ s, some p, some e =>
        if lasts.contains s then acc.push { start := p, stop := e, replacement := raw.toString ++ suffix }
        else acc
      | _, _, _ => acc
    | .node _ _ args => args.foldl (fun acc a => go lasts a acc) acc
    | _ => acc

/-- The namespace a declaration was written in: its name without the name written in its
`declId`. -/
partial def declNamespace (cmd : Syntax) (n : Name) : Name := Id.run do
  let some declId := findDeclId cmd | return n.getPrefix
  let written := declId[0].getId
  let mut ns := n
  for _ in written.components do
    ns := ns.getPrefix
  return ns
where
  findDeclId (stx : Syntax) : Option Syntax :=
    if stx.isOfKind ``Command.declId then some stx
    else stx.getArgs.findSome? findDeclId

/-- The `open` commands of a source file. -/
def opensOf (src : SourceFile) : Array String :=
  src.commands.filter (·.isOfKind ``Command.open) |>.map (textOf src)

/-- Wraps a command's text in its namespace and the file's `open` commands. -/
def wrap (src : SourceFile) (ns : Name) (body : String) : String :=
  let opens := "\n".intercalate (opensOf src).toList
  if ns.isAnonymous then s!"{opens}\n{body}\n"
  else s!"namespace {ns}\n{opens}\n{body}\nend {ns}\n"

/-- Elaborates the commands in a text. Returns whether any of them logged an error. -/
partial def elabText (text : String) : CommandElabM Bool := do
  let inputCtx := mkInputContext text "<assay>"
  let before := (← get).messages
  let infoBefore := (← get).infoState
  modify fun s => { s with messages := {} }
  let parseFailed ← withScope (fun sc => { sc with opts := sc.opts.setBool `Elab.async false }) do
    withReader ({ · with fileMap := FileMap.ofString text, fileName := "<assay>" }) do
      loop inputCtx {} {}
  let failed := parseFailed || (← get).messages.hasErrors
  modify fun s => { s with messages := before, infoState := infoBefore }
  return failed
where
  loop (inputCtx : InputContext) (state : ModuleParserState) (log : MessageLog) : CommandElabM Bool := do
    let (cmd, state, log) := parseCommand inputCtx { env := ← getEnv, options := ← getOptions } state log
    if isTerminalCommand cmd then return log.hasErrors
    elabCommand cmd
    loop inputCtx state log

end Assay
