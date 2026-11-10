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

/-- The theorems in the audited functions' modules whose statement mentions one of the functions,
in the order they were declared. -/
def theoremsAbout (fns : Array Name) : CoreM (Array Name) := do
  let env ← getEnv
  let mods := fns.map (moduleOf env)
  let mut found : Array (Name × Nat) := #[]
  for (n, info) in env.constants.toList do
    let .thmInfo thm := info | continue
    if isGenerated env fns n || !mods.contains (moduleOf env n) then continue
    if !thm.type.getUsedConstants.any fns.contains then continue
    let line := (← findDeclarationRanges? n).map (·.range.pos.line) |>.getD 0
    found := found.push (n, line)
  return found.qsort (fun a b => a.2 < b.2 || (a.2 == b.2 && a.1.lt b.1)) |>.map (·.1)

/-- The inductive types declared in the given modules that occur in an expression. -/
def localInductives (mods : Array Name) (e : Expr) : CoreM (Array Name) := do
  let env ← getEnv
  return e.getUsedConstants.filter fun c =>
    (env.find? c matches some (.inductInfo _)) && mods.contains (moduleOf env c)

/-- Derives `Repr`, `DecidableEq`, `Arbitrary` and `Shrinkable` for a type that lacks them. -/
def ensureInstances (ty : Name) : CommandElabM Unit := do
  let id := mkIdent ty
  let missing (cls : Name) : CommandElabM Bool := liftTermElabM do
    let inst ← mkAppM cls #[mkConst ty]
    return (← trySynthInstance inst) matches .none
  for (cls, cmd) in [
      (``Repr, ← `(deriving instance Repr for $id)),
      (``DecidableEq, ← `(deriving instance DecidableEq for $id)),
      (``Plausible.Arbitrary, ← `(deriving instance Plausible.Arbitrary for $id)),
      (``Plausible.Shrinkable, ← `(instance : Plausible.Shrinkable $id := {}))] do
    if ← missing cls then
      elabCommand cmd

end Assay
