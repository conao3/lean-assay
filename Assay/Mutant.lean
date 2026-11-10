import Lean
import Assay.Source

/-!
The ways `#assay` breaks a function.

* Replacing the whole function by an obviously wrong one: a constant (`default`, `none`, `[]`, a
  constructor), one of its arguments returned unchanged, or a list argument cut short.
* Editing the body: swapping an operator, moving a numeric literal by one, giving a match arm
  another arm's result, adding an arm before the catch-all arm, and swapping the branches of an
  `if`.
-/

open Lean Meta Elab Command

namespace Assay

/-- How a mutant differs from the function. -/
inductive Change where
  /-- Edits to the text of the function's command. -/
  | edits (es : Array Edit)
  /-- The function replaced by a closed term of its type. -/
  | replace (value : Expr)
  deriving Inhabited

/-- A broken version of an audited function. -/
structure Mutant where
  fn : Name
  label : String
  change : Change
  deriving Inhabited

/-! ## Replacing the whole function -/

/-- Constants of a type: `default`, and each constructor without fields or with a single field
that is itself a constructor without fields (`some .ended`). -/
def constantsOf (ty : Expr) : MetaM (Array (String × Expr)) := do
  let mut out := #[]
  if let .some inst ← trySynthInstance (← mkAppM ``Inhabited #[ty]) then
    out := out.push ("default", ← mkAppOptM ``Inhabited.default #[ty, inst])
  let ty' ← whnfR ty
  let .const n us := ty'.getAppFn | return out
  let some (.inductInfo info) := (← getEnv).find? n | return out
  let params := ty'.getAppArgs
  if params.size != info.numParams || info.numIndices != 0 then return out
  for c in info.ctors do
    let ctor := mkAppN (mkConst c us) params
    let cty ← inferType ctor
    match cty with
    | .forallE _ _ (.forallE ..) _ => continue
    | .forallE _ fty body _ =>
      if body.hasLooseBVars then continue
      if let some vals ← enumValues? fty then
        for v in vals do
          out := out.push (s!"{c.componentsRev.head!} {v.constName!.componentsRev.head!}", mkApp ctor v)
    | _ => out := out.push (s!"{c.componentsRev.head!}", ctor)
  return out

/-- Obviously wrong functions of the same type as `fn`. -/
def replacements (fn : Name) : MetaM (Array (String × Expr)) := do
  let info ← getConstInfo fn
  if !info.levelParams.isEmpty then return #[]
  forallTelescope info.type fun xs ret => do
    if xs.isEmpty || (← isProp ret) then return #[]
    let holes := xs.map fun _ => "_"
    let mut out := #[]
    let mut seen : Std.HashSet String := {}
    for (s, v) in ← constantsOf ret do
      let e ← instantiateMVars v
      if seen.contains s || e.hasFVar then continue
      seen := seen.insert s
      out := out.push (s, e)
    for x in xs, i in [0:xs.size] do
      let ty ← inferType x
      if ← isDefEq ty ret then
        let shown := holes.set! i "x"
        out := out.push (s!"fun {" ".intercalate shown.toList} => x", x)
      if ty.isAppOfArity ``List 1 && (← isDefEq ty ret) then
        let shown := holes.set! i "xs"
        out := out.push (s!"fun {" ".intercalate shown.toList} => xs.take 1", ← mkAppM ``List.take #[toExpr 1, x])
        out := out.push (s!"fun {" ".intercalate shown.toList} => xs.reverse", ← mkAppM ``List.reverse #[x])
    out.mapM fun (s, body) => do
      let label := if s.startsWith "fun" then s else s!"fun {" ".intercalate holes.toList} => {s}"
      return (label, ← mkLambdaFVars xs body)

/-! ## Editing the body -/

/-- Operators and what each one is swapped for. -/
def swaps : List (String × List String) := [
  ("<", ["≤", ">"]), ("≤", ["<", "≥"]), (">", ["≥", "<"]), ("≥", [">", "≤"]),
  ("<=", ["<", ">="]), (">=", [">", "<="]),
  ("==", ["!="]), ("!=", ["=="]), ("=", ["≠"]), ("≠", ["="]),
  ("+", ["-"]), ("-", ["+"]), ("*", ["+"]), ("/", ["*"]), ("%", ["/"]),
  ("&&", ["||"]), ("||", ["&&"]), ("∧", ["∨"]), ("∨", ["∧"])]

/-- Functions that are swapped for each other wherever they are called. -/
def identSwaps : List (String × String) := [
  ("take", "drop"), ("drop", "take"), ("min", "max"), ("max", "min"),
  ("succ", "pred"), ("pred", "succ"), ("all", "any"), ("any", "all"),
  ("head", "getLast"), ("getLast", "head"), ("takeWhile", "dropWhile"), ("dropWhile", "takeWhile")]

/-- Operators whose operands are swapped. -/
def operandSwaps : List String := ["++", "-", "/", "%", "<", "≤", "^"]

/-- The part of a declaration after its signature. -/
partial def bodyOf (cmd : Syntax) : Option Syntax :=
  if cmd.isOfKind ``Parser.Command.declValSimple || cmd.isOfKind ``Parser.Command.declValEqns then
    some cmd
  else cmd.getArgs.findSome? bodyOf

/-- A one-line form of a piece of source text. -/
def oneLine (s : String) : String :=
  " ".intercalate (s.splitOn "\n" |>.map (fun l => l.trimAscii.toString) |>.filter (· ≠ ""))

/-- The line and column of a position in the source text, as `line:column` from 1. -/
def posOf (src : SourceFile) (p : String.Pos.Raw) : String :=
  let pos := (FileMap.ofString src.text).toPosition p
  s!"{pos.line}:{pos.column + 1}"

/-- A one-line form of a piece of source text, cut at 40 characters. -/
def short (s : String) : String :=
  let s := oneLine s
  if s.length ≤ 40 then s else (s.take 39).toString ++ "…"

/-- An edit that replaces a node's text. -/
def replaceNode (stx : Syntax) (replacement : String) : Option Edit := do
  return { start := ← stx.getPos?, stop := ← stx.getTailPos?, replacement }

/-- Whether a pattern only matches anything: `_` or a variable. -/
def isWildcard (pat : Syntax) : Bool :=
  pat.isOfKind ``Parser.Term.hole || (pat.isIdent && pat.getId.isAtomic && pat.getId.toString.front.isLower)

/-- Mutants from the arms of one `match` (or of a definition by pattern matching). -/
def armMutants (src : SourceFile) (fn : Name) (alts : Array Syntax) : Array Mutant := Id.run do
  let arms := alts.filterMap fun alt =>
    let pats := alt[1].getArgs
    if pats.size != 1 then none
    else some (pats[0]!.getArgs.filter (fun p => !p.isAtom), alt[3]!)
  let results := arms.map fun (_, rhs) => textOf src rhs
  let mut out := #[]
  for (pats, rhs) in arms do
    let mine := textOf src rhs
    let mut tried : Array String := #[mine]
    for other in results do
      if tried.contains other then continue
      tried := tried.push other
      if let some e := replaceNode rhs other then
        let patText := ", ".intercalate (pats.toList.map (textOf src))
        out := out.push {
          fn, change := .edits #[e]
          label := s!"{posOf src (rhs.getPos?.getD 0)}: | {short patText} => {short mine} ↦ {short other}" }
  let some catchAll := arms.findIdx? (fun (pats, _) => pats.all isWildcard) | return out
  if arms.isEmpty then return out
  let width := arms[0]!.1.size
  if !arms.all (·.1.size == width) then return out
  let columns := (List.range width).toArray.map fun c =>
    arms.foldl (fun acc (pats, _) =>
      let p := pats[c]!
      let t := textOf src p
      if isWildcard p || acc.contains t then acc else acc.push t) #[]
  let existing := arms.map fun (pats, _) => pats.map (textOf src)
  let combos := columns.foldl (fun acc col =>
    acc.flatMap fun pre => col.map (pre.push ·)) #[#[]]
  let catchRhs := textOf src arms[catchAll]!.2
  let some at_ := alts[catchAll]!.getPos? | return out
  for combo in combos do
    if combo.size != width || existing.contains combo then continue
    let mut tried : Array String := #[catchRhs]
    for r in results do
      if tried.contains r then continue
      tried := tried.push r
      let arm := s!"| {", ".intercalate combo.toList} => {r}\n  "
      out := out.push {
        fn, change := .edits #[{ start := at_, stop := at_, replacement := arm }]
        label := s!"{posOf src at_}: add | {", ".intercalate combo.toList} => {short r}" }
  return out

/-- Mutants from editing the body of `fn`'s command. -/
partial def editMutants (src : SourceFile) (fn : Name) (cmd : Syntax) : Array Mutant := Id.run do
  let some body := bodyOf cmd | return #[]
  go body #[]
where
  go (stx : Syntax) (acc : Array Mutant) : Array Mutant := Id.run do
    let mut acc := acc
    match stx with
    | .atom _ val =>
      if let some (_, tos) := swaps.find? (·.1 == val) then
        for t in tos do
          if let some e := replaceNode stx t then
            acc := acc.push { fn, change := .edits #[e], label := s!"{posOf src e.start}: {val} ↦ {t}" }
      return acc
    | .ident _ raw val _ =>
      if let .str _ s := val then
        if let some (_, t) := identSwaps.find? (·.1 == s) then
          let rawS := raw.toString
          let new := (rawS.dropEnd s.length).toString ++ t
          if let some e := replaceNode stx new then
            acc := acc.push { fn, change := .edits #[e], label := s!"{posOf src e.start}: {rawS} ↦ {new}" }
      return acc
    | .node _ kind args =>
      if args.size == 3 && args[1]!.isAtom && operandSwaps.contains args[1]!.getAtomVal then
        let l := args[0]!
        let r := args[2]!
        if let (some el, some er) := (replaceNode l (textOf src r), replaceNode r (textOf src l)) then
          acc := acc.push { fn, change := .edits #[el, er], label := s!"{posOf src (args[1]!.getPos?.getD el.start)}: swap the operands of {args[1]!.getAtomVal}" }
      if let some n := stx.isNatLit? then
        let line := posOf src (stx.getPos?.getD 0)
        for m in (if n == 0 then [1] else [n + 1, n - 1]) do
          if let some e := replaceNode stx (toString m) then
            acc := acc.push { fn, change := .edits #[e], label := s!"{line}: {textOf src stx} ↦ {m}" }
        return acc
      if kind == ``Parser.Term.matchAlts then
        acc := acc ++ armMutants src fn stx[0].getArgs
      if kind == ``termIfThenElse then
        let t := stx[3]
        let f := stx[5]
        if let (some et, some ef) := (replaceNode t (textOf src f), replaceNode f (textOf src t)) then
          acc := acc.push { fn, change := .edits #[et, ef], label := s!"{posOf src et.start}: swap the branches of if" }
      return args.foldl (fun acc a => go a acc) acc
    | _ => return acc

end Assay
