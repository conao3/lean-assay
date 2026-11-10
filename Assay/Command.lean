import Lean
import Assay.Mutant

/-!
The `#assay` command.

`#assay f g …` breaks each of the functions in every way `Assay.Mutant` knows, and runs every
theorem that mentions them against each broken version. A broken version that changes the
function's output but satisfies every theorem is a hole in the theorems.
-/

open Lean Meta Elab Command

namespace Assay

register_option assay.failOnHole : Bool := {
  defValue := false
  descr := "report holes as errors, so that a build that runs `#assay` fails"
}

register_option assay.timeout : Nat := {
  defValue := 30000
  descr := "milliseconds a mutant may spend running the theorems before it is reported as timed out"
}

/-- The suffix of the names mutants are elaborated under. -/
def mutantSuffix : String := "_assay"

/-- How one clause ran against a mutant. -/
inductive Cell where
  | killed (counterexample : List String)
  | held
  | untested
  | skipped
  deriving Inhabited

def Cell.symbol : Cell → String
  | .killed _ => "✗"
  | .held => "·"
  | .untested => "?"
  | .skipped => "-"

/-- What a mutant came to. -/
inductive Verdict' where
  | stillborn
  | equivalent
  | killed
  | hole (theorem_ : String) (differs : List String)
  | inconclusive
  | timeout
  deriving Inhabited

structure MutantResult where
  mutant : Mutant
  verdict : Verdict'
  cells : Array Cell
  deriving Inhabited

/-- Whether a run tried enough inputs that satisfied the hypotheses. -/
def enoughTested (s : Summary) (minSatisfied : Nat) : Bool :=
  s.held > 0 && (s.exhaustive || s.held ≥ minSatisfied)

/-- The definitions in `mods` that use `f`, directly or through each other, including `f`. -/
def dependentsOf (mods : Array Name) (f : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let defs := env.constants.toList.filterMap fun (n, info) =>
    match info with
    | .defnInfo d =>
      if mods.contains (moduleOf env n) then some (n, d.value.getUsedConstants) else none
    | _ => none
  let mut out := #[f]
  let mut changed := true
  while changed do
    changed := false
    for (n, used) in defs do
      if out.contains n then continue
      if used.any out.contains then
        out := out.push n
        changed := true
  return out.filter (fun n => n == f || !n.isInternalDetail)

/-- Renames identifiers in a command text by reparsing it. -/
def renameText (renamed : Array Name) (text : String) : CommandElabM String := do
  let src ← parseSource "<assay>" text
  let mut edits := #[]
  for cmd in src.commands do
    edits := edits ++ renameEdits renamed mutantSuffix cmd
  return applyEdits text 0 text.rawEndPos edits

/-- Substitutes the mutant names in a statement. -/
def substitute (renamed : Array Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if renamed.contains n then some (.const (suffixed n mutantSuffix) us) else none
    | _ => none

/-- The applications of the renamed functions in an expression that do not depend on a bound
variable. -/
partial def appsOf (renamed : Array Name) (acc : Array Expr) (e : Expr) : Array Expr :=
  let acc :=
    match e.getAppFn with
    | .const n _ =>
      if renamed.contains n && !e.hasLooseBVars && !acc.contains e then acc.push e else acc
    | _ => acc
  match e with
  | .app f a => appsOf renamed (appsOf renamed acc f) a
  | .lam _ t b _ | .forallE _ t b _ => appsOf renamed (appsOf renamed acc t) b
  | .letE _ t v b _ => appsOf renamed (appsOf renamed (appsOf renamed acc t) v) b
  | .mdata _ b | .proj _ _ b => appsOf renamed acc b
  | _ => acc

/-- For a clause `∀ xs, H xs → C xs`, the statement `∀ xs, H xs → g' a = g a ∧ …` over every
application `g a` of a renamed function in the hypotheses and the conclusion whose output type has
decidable equality. A counterexample is an input that satisfies the theorem's hypotheses on which the
mutant changes the output. -/
def differsUnder (renamed : Array Name) (stmt : Expr) : MetaM (Option Expr) := do
  forallTelescope stmt fun xs body => do
    let apps := ((← xs.mapM inferType).push body).foldl (appsOf renamed) #[]
    let mut eqs := #[]
    for a in apps do
      let eq ← mkEq (substitute renamed a) a
      if (← observing? (mkDecide eq)).isSome then
        eqs := eqs.push eq
    if eqs.isEmpty then return none
    return some (← mkForallFVars xs (mkAndN eqs.toList))

/-- `∀ xs, f' xs = f xs`. -/
def sameOutput (f : Name) : MetaM Expr := do
  let info ← getConstInfo f
  forallTelescope info.type fun xs _ => do
    let us := info.levelParams.map mkLevelParam
    let lhs := mkAppN (.const (suffixed f mutantSuffix) us) xs
    let rhs := mkAppN (.const f us) xs
    mkForallFVars xs (← mkEq lhs rhs)

/-- Elaborates a mutant and the functions that depend on it. Returns `false` if it does not
typecheck. -/
def elabMutant (m : Mutant) (renamed : Array Name) : CommandElabM Bool := do
  let src ← sourceOf m.fn
  let cmd ← commandOf src m.fn
  match m.change with
  | .replace value =>
    let info ← getConstInfo m.fn
    try
      liftCoreM <| addAndCompile <| .defnDecl {
        name := suffixed m.fn mutantSuffix, levelParams := info.levelParams, type := info.type,
        value, hints := .opaque, safety := .safe }
    catch _ => return false
  | .edits es =>
    let some s := cmd.getPos? | return false
    let some e := cmd.getTailPos? | return false
    let text ← renameText renamed (applyEdits src.text s e es)
    if ← elabText (wrap src (declNamespace cmd m.fn) text) then return false
  for g in renamed do
    if g == m.fn then continue
    let gsrc ← sourceOf g
    let gcmd ← commandOf gsrc g
    let text ← renameText renamed (textOf gsrc gcmd)
    if ← elabText (wrap gsrc (declNamespace gcmd g) text) then return false
  return true

/-- Pads a string with spaces to a width. -/
def pad (s : String) (w : Nat) : String :=
  s ++ "".pushn ' ' (w - s.length)

/-- Runs a clause until the monotonic clock passes `deadline` (milliseconds). -/
def runClause (stmt : Expr) (count deadline : Nat) : CommandElabM Outcome :=
  liftTermElabM <| runStatement stmt count deadline

/-- The number of random inputs for a clause: enough that `minSatisfied` inputs are expected to
satisfy its hypotheses four times over, judging by how many satisfied them on the original functions. -/
def countFor (samples maxSamples minSatisfied : Nat) (s : Summary) : Nat :=
  let tried := s.held + s.discarded
  if s.exhaustive || tried == 0 || s.held ≥ 4 * minSatisfied then samples
  else min maxSamples (4 * minSatisfied * tried / max s.held 1)

/-- Runs every mutant of the functions against the theorems about them and reports the result. -/
def assay (fns : Array Name) (ref : Syntax) : CommandElabM Unit := do
  let opts ← getOptions
  let minSatisfied := assay.minSatisfied.get opts
  let env ← getEnv
  let mods := fns.map (moduleOf env)
  let mut affected := #[]
  for f in fns do
    for g in ← liftCoreM <| dependentsOf mods f do
      if !affected.contains g then affected := affected.push g
  let thms ← liftTermElabM <| theoremsAbout affected
  let propDefs ← liftTermElabM <| propDefsIn mods
  let statements ← thms.mapM fun t => liftTermElabM <| statementOf propDefs t
  if thms.isEmpty then
    throwErrorAt ref "no theorem mentions {fns}"
  for ty in statements ++ (← fns.mapM fun f => return (← getConstInfo f).type) do
    for i in ← liftCoreM <| localInductives mods ty do
      ensureInstances i
  let mut clauses := #[]
  for t in thms, s in statements do
    clauses := clauses ++ (← liftTermElabM <| clausesOf t s)
  let timeout := assay.timeout.get opts
  let samples := assay.samples.get opts
  let maxSamples := assay.maxSamples.get opts
  let mut baseline := #[]
  let mut counts := #[]
  for c in clauses do
    let first ← runClause c.statement samples ((← IO.monoMsNow) + timeout)
    let count := match first with
      | .ran s => countFor samples maxSamples minSatisfied s
      | .untestable _ => samples
    counts := counts.push count
    baseline := baseline.push (← if count == samples then pure first else runClause c.statement count ((← IO.monoMsNow) + timeout))
  let mut lines := #["theorems, run on the original functions:"]
  let mut warnings := #[]
  for c in clauses, o in baseline, i in [0:clauses.size] do
    let note := match o with
      | .untestable r => s!"not executable: {r}"
      | .ran s =>
        match s.counterexample with
        | some cex => s!"FAILS on the original: {", ".intercalate cex}"
        | none =>
          let satisfied := s.held
          let tried := s.held + s.discarded
          let how := if s.exhaustive then "all" else "random"
          if s.timedOut then s!"timed out after {tried} inputs, {satisfied} of them satisfying the hypotheses"
          else if satisfied == 0 then s!"no input satisfies the hypotheses ({tried} {how} inputs)"
          else s!"{satisfied}/{tried} {how} inputs satisfy the hypotheses"
    lines := lines.push s!"  T{i + 1} {c.label}: {note}"
    match o with
    | .ran s =>
      if s.counterexample.isSome then warnings := warnings.push m!"{c.label} fails on the original functions"
      else if s.held == 0 && !s.timedOut then warnings := warnings.push m!"{c.label}: no input satisfies the hypotheses; the theorem may be vacuous"
    | .untestable _ => pure ()
  let mut results := #[]
  for f in fns do
    let src ← sourceOf f
    let cmd ← commandOf src f
    let renamed ← liftCoreM <| dependentsOf mods f
    let reps ← liftTermElabM <| replacements f
    let mutants := reps.map (fun (l, v) => { fn := f, label := s!"{f.componentsRev.head!} := {l}", change := .replace v : Mutant })
      ++ (editMutants src f cmd).map fun m => { m with label := s!"{f.componentsRev.head!}: {m.label}" }
    for m in mutants do
      let r : MutantResult ← withoutModifyingEnv do
        if !(← elabMutant m renamed) then
          return { mutant := m, verdict := .stillborn, cells := #[] }
        let deadline := (← IO.monoMsNow) + timeout
        let same ← runClause (← liftTermElabM <| sameOutput f) samples deadline
        if let .ran s := same then
          if s.counterexample.isNone && enoughTested s minSatisfied then
            return { mutant := m, verdict := .equivalent, cells := #[] }
        let mut cells := #[]
        let mut timedOut := false
        for c in clauses, b in baseline, count in counts do
          let usable := match b with | .ran s => s.counterexample.isNone | _ => false
          if !usable || !c.statement.getUsedConstants.any renamed.contains then
            cells := cells.push Cell.skipped
            continue
          let cell ← match ← runClause (substitute renamed c.statement) count deadline with
            | .ran s =>
              if s.timedOut then timedOut := true
              match s.counterexample with
              | some cex => pure (Cell.killed cex)
              | none => pure (if enoughTested s minSatisfied then Cell.held else Cell.untested)
            | .untestable _ => pure Cell.untested
          cells := cells.push cell
        if cells.any (· matches .killed _) then
          return { mutant := m, verdict := .killed, cells }
        if timedOut then
          return { mutant := m, verdict := .timeout, cells }
        let held := cells.all fun c => c matches .held | .skipped
        if !held || !cells.any (· matches .held) then
          return { mutant := m, verdict := .inconclusive, cells }
        let mut differs := none
        for c in clauses, b in baseline, count in counts do
          let usable := match b with | .ran s => s.counterexample.isNone | _ => false
          if !usable || differs.isSome then continue
          let some stmt ← liftTermElabM <| differsUnder renamed c.statement | continue
          if let .ran s ← runClause stmt count deadline then
            if s.timedOut then timedOut := true
            differs := s.counterexample.map (c.label, ·)
        match differs with
        | some (t, d) => return { mutant := m, verdict := .hole t d, cells }
        | none => return { mutant := m, verdict := if timedOut then .timeout else .equivalent, cells }
      results := results.push r
  let shown := results.filter fun r => r.verdict matches .killed | .hole _ _ | .inconclusive | .timeout
  let width := shown.foldl (fun w r => max w r.mutant.label.length) 6
  lines := lines.push ""
  let header := pad "mutant" width ++ "  " ++ " ".intercalate ((List.range clauses.size).map fun i => pad s!"T{i + 1}" 3) ++ "  verdict"
  lines := lines.push header
  for r in shown do
    let cells := " ".intercalate (r.cells.toList.map fun c => pad c.symbol 3)
    let v := match r.verdict with
      | .killed => "killed"
      | .hole _ _ => "HOLE"
      | .inconclusive => "untested"
      | .timeout => "timeout"
      | _ => ""
    lines := lines.push s!"{pad r.mutant.label width}  {cells}  {v}"
  let count (p : Verdict' → Bool) := results.filter (p ·.verdict) |>.size
  let holes := results.filter (·.verdict matches .hole _ _)
  lines := lines.push ""
  lines := lines.push s!"{results.size} mutants: {count (· matches .killed)} killed, {holes.size} holes, {count (· matches .inconclusive)} untested, {count (· matches .equivalent)} equivalent, {count (· matches .timeout)} timed out, {count (· matches .stillborn)} stillborn"
  logInfoAt ref (MessageData.ofFormat (Std.Format.text ("\n".intercalate lines.toList)))
  for w in warnings do
    logWarningAt ref w
  for h in holes do
    let differs := match h.verdict with
      | .hole t d => s!"{t}: {", ".intercalate d}"
      | _ => ""
    let msg := m!"hole: `{h.mutant.label}` satisfies every theorem but changes the output on an input that satisfies the hypotheses of {differs}"
    if assay.failOnHole.get opts then logErrorAt ref msg else logWarningAt ref msg

/-- `#assay f g …` runs broken versions of `f`, `g`, … against the theorems about them. -/
syntax (name := assayCmd) "#assay " ident+ : command

@[command_elab assayCmd]
def elabAssay : CommandElab := fun stx => do
  let fns ← stx[1].getArgs.mapM fun i => liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
  assay fns stx

end Assay
