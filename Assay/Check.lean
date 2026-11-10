import Lean
import Assay.Runtime
import Assay.Sample

/-!
Turning a theorem into executable checks.

A theorem `∀ xs, H₁ → … → Hₘ → C₁ ∧ … ∧ Cₖ` becomes one clause per conjunct `Cᵢ`. A clause is run
by drawing values for the data binders `xs`, deciding the hypotheses and the conjunct, and counting
the inputs that satisfied the hypotheses. When every binder has a small finite type, every input is
tried instead of a random sample.
-/

open Lean Meta Elab Plausible

namespace Assay

/-- Options of `#assay`. -/
register_option assay.samples : Nat := {
  defValue := 1000
  descr := "number of random inputs tried per clause"
}

register_option assay.seed : Nat := {
  defValue := 0
  descr := "seed of the random inputs, fixed so that a run is reproducible"
}

register_option assay.maxSize : Nat := {
  defValue := 30
  descr := "the largest size passed to the generators"
}

register_option assay.minSatisfied : Nat := {
  defValue := 20
  descr := "inputs satisfying the hypotheses needed before a clause counts as tested"
}

register_option assay.maxSamples : Nat := {
  defValue := 30000
  descr := "the most random inputs tried for a clause whose hypotheses are rarely satisfied"
}

register_option assay.enumLimit : Nat := {
  defValue := 4096
  descr := "the largest number of inputs tried exhaustively instead of sampled"
}

/-- One conjunct of a theorem's conclusion, with the theorem's binders and hypotheses. -/
structure Clause where
  /-- The theorem the clause comes from. -/
  theorem_ : Name
  /-- The position of the conjunct, from 1, or 0 when the conclusion is not a conjunction. -/
  index : Nat
  /-- `∀ xs, H₁ → … → Hₘ → Cᵢ`, closed. -/
  statement : Expr
  deriving Inhabited

/-- The column header of a clause. -/
def Clause.label (c : Clause) : String :=
  let n := c.theorem_.componentsRev.head!.toString
  if c.index == 0 then n else s!"{n}.{c.index}"

/-- Splits nested conjunctions. -/
partial def splitAnd (e : Expr) : Array Expr :=
  match e.and? with
  | some (a, b) => splitAnd a ++ splitAnd b
  | none => #[e]

/-- The clauses of a theorem. -/
def clausesOf (thm : Name) : MetaM (Array Clause) := do
  let info ← getConstInfo thm
  forallTelescope info.type fun xs body => do
    let conjuncts := splitAnd body
    if conjuncts.size == 1 then
      return #[{ theorem_ := thm, index := 0, statement := info.type }]
    conjuncts.mapIdxM fun i c => do
      return { theorem_ := thm, index := i + 1, statement := ← mkForallFVars xs c }

/-- How a clause ran. -/
inductive Outcome where
  /-- The clause could not be run; the string says why. -/
  | untestable (reason : String)
  | ran (summary : Summary)
  deriving Inhabited

/-- The values of a type when it is an enumeration (every constructor has no fields) or `Bool`. -/
def enumValues? (ty : Expr) : MetaM (Option (Array Expr)) := do
  let ty ← whnfR ty
  let .const n _ := ty | return none
  let some (.inductInfo info) := (← getEnv).find? n | return none
  if info.numParams != 0 || info.numIndices != 0 then return none
  let mut vals := #[]
  for c in info.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? c | return none
    if ci.numFields != 0 then return none
    vals := vals.push (mkConst c)
  return some vals

/-- `decide p`, or an error naming the proposition that is not decidable. -/
def decideOf (p : Expr) : MetaM Expr := do
  try
    mkDecide p
  catch _ =>
    throwError "`{← ppExpr p}` is not decidable"

/-- The pair `(verdict hyps concl, thunk of the shown binders)` for fixed binder values. -/
def resultOf (binders : Array Expr) (hyps : Array Expr) (concl : Expr) : MetaM Expr := do
  let mut hypsB := toExpr true
  for h in hyps do
    hypsB := mkApp2 (mkConst ``and) hypsB (← decideOf (← inferType h))
  let conclB ← decideOf concl
  let v := mkApp2 (mkConst ``Assay.verdict) hypsB conclB
  let mut shown ← mkListLit (mkConst ``String) []
  let names ← binders.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  let unique := names.toList.eraseDups.length == names.size
  for x in binders.reverse, i in (List.range binders.size).reverse do
    let name := if unique then names[i]! else s!"#{i + 1}"
    let s ← try mkAppM ``Assay.showBinder #[toExpr name, x]
      catch _ => throwError "no `Repr` instance for `{← ppExpr (← inferType x)}`"
    shown ← mkAppM ``List.cons #[s, shown]
  let strs := mkApp (mkConst ``List [0]) (mkConst ``String)
  let thunk := mkApp2 (mkConst ``Thunk.mk [0]) strs (.lam `_ (mkConst ``Unit) shown .default)
  mkAppM ``Prod.mk #[v, thunk]

unsafe def evalSummaryImpl (e : Expr) : MetaM Summary :=
  evalExpr Summary (mkConst ``Assay.Summary) e

/-- Evaluates an expression of type `Summary`. -/
@[implemented_by evalSummaryImpl]
opaque evalSummary (e : Expr) : MetaM Summary

/-- Builds and runs the check of a closed proposition `∀ xs, H₁ → … → Hₘ → C`. -/
def runStatement (stmt : Expr) (count : Nat) : MetaM Outcome := do
  let opts ← getOptions
  try
    forallTelescope stmt fun xs body => do
      let mut binders := #[]
      let mut hyps := #[]
      for x in xs do
        let ty ← inferType x
        if ← isProp ty then hyps := hyps.push x else
          if !hyps.isEmpty then
            throwError "a data binder follows a hypothesis"
          binders := binders.push x
      if body.hasAnyFVar (fun f => hyps.any (·.fvarId! == f)) then
        throwError "the conclusion uses a proof of a hypothesis"
      for h in hyps do
        if (← inferType h).hasAnyFVar (fun f => hyps.any (·.fvarId! == f)) then
          throwError "a hypothesis uses a proof of another hypothesis"
      let res ← resultOf binders hyps body
      let pairTy ← inferType res
      let mut enums : Array (Array Expr) := #[]
      let mut total := 1
      for x in binders do
        match ← enumValues? (← inferType x) with
        | some vs => enums := enums.push vs; total := total * vs.size
        | none => break
      if enums.size == binders.size && total ≤ assay.enumLimit.get opts then
        let mut acc ← mkListLit pairTy [res]
        for x in binders.reverse, vs in enums.reverse do
          let lst ← mkListLit (← inferType x) vs.toList
          acc ← mkAppM ``List.flatMap #[← mkLambdaFVars #[x] acc, lst]
        let run ← mkAppM ``Assay.runAll #[acc]
        return .ran (← evalSummary (← instantiateMVars run))
      let gen ← mkAppOptM ``Pure.pure #[mkConst ``Plausible.Gen [0], none, none, res]
      let mut acc := gen
      for x in binders.reverse do
        let s ← try mkAppOptM ``Assay.sample #[← inferType x, none]
          catch _ => throwError "no `SampleableExt` instance for `{← ppExpr (← inferType x)}`"
        acc ← mkAppM ``Bind.bind #[s, ← mkLambdaFVars #[x] acc]
      let run := mkApp4 (mkConst ``Assay.runRandom) acc
        (toExpr count) (toExpr (assay.maxSize.get opts)) (toExpr (assay.seed.get opts))
      return .ran (← evalSummary run)
  catch e =>
    return .untestable (← e.toMessageData.toString)

end Assay
