import Lean
import Assay.Check

/-!
Finding the theorems about the audited functions, and giving the types they quantify over the
instances a check needs (`Repr`, `DecidableEq`, plausible's `Arbitrary` and `Shrinkable`).
-/

open Lean Meta Elab Command

namespace Assay

/-- The module a constant comes from, or the current module. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Whether a theorem is one that Lean generated (equation lemmas, induction principles, …). -/
def isGenerated (env : Environment) (fns : Array Name) (n : Name) : Bool :=
  n.isInternalDetail || fns.contains n.getPrefix || isAuxRecursor env n || isNoConfusion env n

/-- The definitions of propositions (`def P : Prop`, `def Q (x : α) : Prop`) in the given modules. -/
def propDefsIn (mods : Array Name) : MetaM NameSet := do
  let env ← getEnv
  let mut out : NameSet := {}
  for (n, info) in env.constants.toList do
    let .defnInfo d := info | continue
    if n.isInternalDetail || !mods.contains (moduleOf env n) then continue
    if ← forallTelescope d.type fun _ ret => return ret.isProp then
      out := out.insert n
  return out

/-- Unfolds the propositions defined in the audited modules that a statement's conclusion is,
under its binders and hypotheses, so that `theorem p_proven : P` with `def P : Prop := ∀ x, …`
states `∀ x, …`. The propositions inside the conclusion are left folded, so that their `Decidable`
instances still apply. -/
partial def unfoldHead (propDefs : NameSet) (e : Expr) : MetaM Expr :=
  forallTelescope e fun xs body => do
    let body := body.headBeta
    let .const c us := body.getAppFn | mkForallFVars xs body
    let some (.defnInfo d) := (← getEnv).find? c | mkForallFVars xs body
    if !propDefs.contains c then return ← mkForallFVars xs body
    let v := (d.value.instantiateLevelParams d.levelParams us).beta body.getAppArgs
    mkForallFVars xs (← unfoldHead (propDefs.erase c) v)

/-- A theorem's statement with its conclusion unfolded as `unfoldHead` does. -/
def statementOf (propDefs : NameSet) (thm : Name) : MetaM Expr := do
  unfoldHead propDefs (← getConstInfo thm).type

/-- The theorems in the audited functions' modules whose statement, with the modules' propositions
unfolded, mentions one of the functions, in the order they were declared. -/
def theoremsAbout (fns : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mods := fns.map (moduleOf env)
  let propDefs ← propDefsIn mods
  let mut found : Array (Name × Nat) := #[]
  for (n, info) in env.constants.toList do
    let .thmInfo _ := info | continue
    if isGenerated env fns n || !mods.contains (moduleOf env n) then continue
    let expanded ← deltaExpand (← getConstInfo n).type propDefs.contains
    if !expanded.getUsedConstants.any fns.contains then continue
    let line := (← findDeclarationRanges? n).map (·.range.pos.line) |>.getD 0
    found := found.push (n, line)
  return found.qsort (fun a b => a.2 < b.2 || (a.2 == b.2 && a.1.lt b.1)) |>.map (·.1)

/-- The inductive types of data (not propositions, without indices), declared in modules whose
root is one of `roots`, that occur in an expression. -/
def localInductives (roots : Array Name) (e : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  return e.getUsedConstants.filter fun c =>
    match env.find? c with
    | some (.inductInfo i) =>
      let ret := i.type.getForallBody
      i.numIndices == 0 && ret.isSort && !ret.isProp && roots.contains (moduleOf env c).getRoot
    | _ => false

/-- The inductive types that `localInductives` finds in the expressions, and those in the types of
their constructors, each after the types of its fields. -/
partial def inductiveClosure (roots : Array Name) (es : Array Expr) : CoreM (Array Name) := do
  let mut out := #[]
  let mut seen : NameSet := {}
  for e in es do
    for i in ← localInductives roots e do
      (out, seen) ← visit i out seen
  return out
where
  visit (i : Name) (out : Array Name) (seen : NameSet) : CoreM (Array Name × NameSet) := do
    if seen.contains i then return (out, seen)
    let mut seen := seen.insert i
    let mut out := out
    let .inductInfo info ← getConstInfo i | return (out, seen)
    for c in info.ctors do
      for j in ← localInductives roots (← getConstInfo c).type do
        if j != i then (out, seen) ← visit j out seen
    return (out.push i, seen)

/-- Derives `Repr`, `DecidableEq`, `Arbitrary` and `Shrinkable` for a type that lacks them, where a
deriving handler applies. A type left without an instance makes the checks that need it not
executable, which the report says. -/
def ensureInstances (ty : Name) : CommandElabM Unit := do
  let id := mkIdent ty
  let missing (cls : Name) : CommandElabM Bool := liftTermElabM do
    try
      let inst ← mkAppM cls #[mkConst ty]
      return (← trySynthInstance inst) matches .none
    catch _ => return true
  for (cls, cmd) in [
      (``Repr, ← `(deriving instance Repr for $id)),
      (``DecidableEq, ← `(deriving instance DecidableEq for $id)),
      (``Plausible.Arbitrary, ← `(deriving instance Plausible.Arbitrary for $id)),
      (``Plausible.Shrinkable, ← `(instance : Plausible.Shrinkable $id := {}))] do
    if ← missing cls then
      let before := (← get).messages
      let env ← getEnv
      modify fun s => { s with messages := {} }
      elabCommand cmd
      if (← get).messages.hasErrors then setEnv env
      modify fun s => { s with messages := before }

end Assay
