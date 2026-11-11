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

/-- Splits nested conjunctions, also under binders and hypotheses: `H → A ∧ B` gives `H → A` and
`H → B`. -/
partial def splitAnd (e : Expr) : MetaM (Array Expr) := do
  match e.and? with
  | some (a, b) => return (← splitAnd a) ++ (← splitAnd b)
  | none =>
    let .forallE _ _ b _ := e | return #[e]
    if !b.hasLooseBVars && b.and?.isNone && !b.isForall then return #[e]
    forallBoundedTelescope e (some 1) fun xs body => do
      let parts ← splitAnd body
      if parts.size == 1 then return #[e]
      parts.mapM (mkForallFVars xs ·)

/-- The clauses of a theorem with the given statement, after unfolding its `let` and `have`. -/
def clausesOf (thm : Name) (stmt : Expr) : MetaM (Array Clause) := do
  let stmt ← zetaReduce stmt
  forallTelescope stmt fun xs body => do
    let conjuncts ← splitAnd body
    if conjuncts.size == 1 then
      return #[{ theorem_ := thm, index := 0, statement := stmt }]
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

/-- The conjuncts of a proposition. -/
partial def conjuncts (e : Expr) : Array Expr :=
  match e.consumeMData.and? with
  | some (a, b) => conjuncts a ++ conjuncts b
  | none => #[e]

/-- The conjunction of propositions, `True` for none. -/
def mkAnds (ps : Array Expr) : Expr :=
  if ps.isEmpty then mkConst ``True else mkAndN ps.toList

/-- The `Bool` that is `k i fields` when `e` is built by the `i`-th constructor of its type, by
`casesOn` on `e`. -/
def casesBool (e : Expr) (k : Nat → Array Expr → MetaM Expr) : MetaM Expr := do
  let ty ← whnfD (← inferType e)
  let .const ind us := ty.getAppFn | throwError "not an inductive type"
  let .inductInfo info ← getConstInfo ind | throwError "not an inductive type"
  if info.numIndices != 0 then throwError "an inductive family"
  let params := ty.getAppArgs.extract 0 info.numParams
  let motive := Expr.lam `x ty (mkConst ``Bool) .default
  let mut app := mkAppN (mkConst (mkCasesOnName ind) (levelOne :: us)) (params ++ #[motive, e])
  for ctor in info.ctors, i in [0:info.ctors.length] do
    let cty ← instantiateForall (← getConstInfo ctor).type params
    let minor ← forallTelescope cty fun fields _ => do mkLambdaFVars fields (← k i fields)
    app := mkApp app minor
  return app

/-- The `Bool` that is `k fields` when `e` is built by the constructor `c` and `false` otherwise. -/
def ctorCase (e : Expr) (c : Name) (k : Array Expr → MetaM Expr) : MetaM Expr := do
  let .ctorInfo ci ← getConstInfo c | throwError "not a constructor"
  casesBool e fun i fields => if i == ci.cidx then k fields else pure (toExpr false)

/-- The body of the definition at the head of `p` applied to its arguments, when that definition
is not recursive. -/
def unfoldOnce? (p : Expr) : MetaM (Option Expr) := do
  let .const c us := p.getAppFn | return none
  let some (.defnInfo d) := (← getEnv).find? c | return none
  let v := d.value.instantiateLevelParams d.levelParams us
  let isRec (e : Expr) : Bool := match e with
    | .const n _ => n == ``WellFounded.fix || n.componentsRev.head? == some (.str .anonymous "brecOn")
    | _ => false
  if (v.find? isRec).isSome then return none
  return some (v.beta p.getAppArgs)

mutual

/-- A `Bool` that is `true` when `p` holds: `decide p` when `p` has a `Decidable` instance, and
otherwise computed part by part. `∧`, `∨`, `¬`, `→` and `↔` are computed from their parts,
`∃ xs, e = c … xs ∧ Q xs` by matching `e` on the constructor `c`, `∃ x, x ∈ l ∧ Q x` with
`List.any`, `∀ x, x ∈ l → Q x` with `List.all`, a `match` on a value of a non-recursive type
by matching it, and a non-recursive definition by unfolding it.
The error names a part that is not decidable. -/
partial def boolOf (p : Expr) : MetaM Expr := do
  let mut p := (← instantiateMVars p).consumeMData
  while p.isHeadBetaTarget do p := p.headBeta
  if let some b ← observing? (mkDecide p) then return b
  if let some (a, b) := p.and? then return mkApp2 (mkConst ``and) (← boolOf a) (← boolOf b)
  if p.isAppOfArity ``Or 2 then
    return mkApp2 (mkConst ``or) (← boolOf p.appFn!.appArg!) (← boolOf p.appArg!)
  if p.isAppOfArity ``Not 1 then return mkApp (mkConst ``not) (← boolOf p.appArg!)
  if p.isAppOfArity ``Iff 2 then
    return mkApp (mkConst ``not) (mkApp2 (mkConst ``xor) (← boolOf p.appFn!.appArg!) (← boolOf p.appArg!))
  if p.isAppOfArity ``Exists 2 then
    if let some b ← existsOf p then return b
  if let .forallE n ty body bi := p then
    if !body.hasLooseBVars && (← isProp ty) then
      return mkApp2 (mkConst ``or) (mkApp (mkConst ``not) (← boolOf ty)) (← boolOf body)
    let r ← withLocalDecl n bi ty fun x => do
      let b := body.instantiate1 x
      let .forallE _ h q _ := b | return none
      if q.hasLooseBVars then return none
      let some l := memOf x h | return none
      return some (← mkAppM ``List.all #[l, ← mkLambdaFVars #[x] (← boolOf q)])
    if let some b := r then return b
  if let .const r _ := p.getAppFn then
    if let some (.recInfo ri) := (← getEnv).find? r then
      let args := p.getAppArgs
      let some (.inductInfo ii) := (← getEnv).find? ri.getMajorInduct | pure ()
      if ri.numMotives == 1 && ri.numIndices == 0 && !ii.isRec
          && args.size == ri.numParams + 1 + ri.numMinors + 1 then
        let minors := args.extract (ri.numParams + 1) (ri.numParams + 1 + ri.numMinors)
        return ← casesBool args.back! fun i fields => boolOf (minors[i]!.beta fields)
  if let some v ← unfoldOnce? p then return ← boolOf v
  throwError "`{← ppExpr p}` is not decidable"

/-- `∃ xs, e = c … xs ∧ Q xs` or `∃ x, x ∈ l ∧ Q x` as a `Bool`, or `none` for another form. -/
partial def existsOf (p : Expr) : MetaM (Option Expr) :=
  go p #[]
where
  go (p : Expr) (xs : Array Expr) : MetaM (Option Expr) := do
    let p := p.consumeMData
    if p.isAppOfArity ``Exists 2 then
      let .lam n ty body bi := p.appArg!.consumeMData | return none
      return ← withLocalDecl n bi ty fun x => go (body.instantiate1 x) (xs.push x)
    let cs := conjuncts p
    let mentions (e : Expr) := xs.any fun x => e.containsFVar x.fvarId!
    if xs.size == 1 && cs.size ≥ 1 then
      if let some l := memOf xs[0]! cs[0]! then
        if !mentions l then
          return some (← mkAppM ``List.any #[l, ← mkLambdaFVars xs (← boolOf (mkAnds (cs.extract 1 cs.size)))])
    for c in cs, i in [0:cs.size] do
      let some (_, a, b) := c.eq? | continue
      for (e, built) in [(a, b), (b, a)] do
        if mentions e then continue
        let .const ctor _ := built.getAppFn | continue
        let some (.ctorInfo ci) := (← getEnv).find? ctor | continue
        let args := built.getAppArgs
        if args.size != ci.numParams + ci.numFields || (args.extract 0 ci.numParams).any mentions then
          continue
        let fieldArgs := args.extract ci.numParams args.size
        let mut binds : Array (Option Expr) := #[]
        let mut usable := true
        for arg in fieldArgs do
          if arg.isFVar && xs.contains arg && !binds.contains (some arg) then binds := binds.push (some arg)
          else if mentions arg then usable := false
          else binds := binds.push none
        if !usable || (binds.filterMap id).size != xs.size then continue
        let rest := (cs.extract 0 i) ++ (cs.extract (i + 1) cs.size)
        return some (← ctorCase e ctor fun fields => do
          let mut from_ := #[]
          let mut to := #[]
          let mut extra := #[]
          for f in fields, arg in fieldArgs, bnd in binds do
            match bnd with
            | some x => from_ := from_.push x; to := to.push f
            | none => extra := extra.push (← mkEq f arg)
          boolOf ((mkAnds (extra ++ rest)).replaceFVars from_ to))
    return none

/-- `l` when `h` is `x ∈ l` for a list `l`. -/
partial def memOf (x h : Expr) : Option Expr :=
  let h := h.consumeMData
  if h.isAppOfArity ``Membership.mem 5 && h.appArg! == x then
    let l := h.appFn!.appArg!
    if h.getAppArgs[0]!.isAppOfArity ``List 1 then some l else none
  else none

end

/-- `decide p`, computed as `boolOf` does, or an error naming a part of `p` that is not
decidable. -/
def decideOf (p : Expr) : MetaM Expr := boolOf p

/-- The pair `(verdict hyps concl, thunk of the shown binders)` for fixed binder values, from the
types of the hypotheses and the conclusion. -/
def resultOf (binders : Array Expr) (hyps : Array Expr) (concl : Expr) : MetaM Expr := do
  let mut hypsB := toExpr true
  for h in hyps do
    hypsB := mkApp2 (mkConst ``and) hypsB (← decideOf h)
  let conclB := .lam `_ (mkConst ``Unit) (← decideOf concl) .default
  let v := mkApp2 (mkConst ``Assay.verdict) hypsB conclB
  let mut shown ← mkListLit (mkConst ``String) []
  let names ← binders.mapM fun x => return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  let unique := names.toList.eraseDups.length == names.size
  for x in binders.reverse, i in (List.range binders.size).reverse do
    let name := if unique then names[i]! else s!"#{i + 1}"
    let s ← try mkAppM ``Assay.showBinder #[toExpr name, x]
      catch _ => pure (toExpr s!"{name} := <no Repr>")
    shown ← mkAppM ``List.cons #[s, shown]
  let strs := mkApp (mkConst ``List [0]) (mkConst ``String)
  let thunk := mkApp2 (mkConst ``Thunk.mk [0]) strs (.lam `_ (mkConst ``Unit) shown .default)
  mkAppM ``Prod.mk #[v, thunk]

unsafe def evalSummaryImpl (e : Expr) : MetaM (IO Summary) :=
  evalExpr (IO Summary) (mkApp (mkConst ``IO) (mkConst ``Assay.Summary)) e

/-- Evaluates an expression of type `IO Summary`. -/
@[implemented_by evalSummaryImpl]
opaque evalSummary (e : Expr) : MetaM (IO Summary)

/-- Replaces the proofs of hypotheses by `Assay.assumed`, which the compiler erases. Code that takes a
proof argument (a precondition) runs with it, since a check only reaches the conclusion when the
hypotheses hold. -/
def eraseProofs (hyps : Array Expr) (e : Expr) : MetaM Expr := do
  let mut e := e
  for h in hyps.reverse do
    if e.containsFVar h.fvarId! then
      let ty ← inferType h
      e := e.replaceFVar h (mkApp (mkConst ``Assay.assumed) ty)
  return e

/-- A statement over one type: its universe parameters set to 0, its binders of type `Type` set to
`Int`, and its instance binders given the instances found for `Int`. -/
partial def specialize (stmt : Expr) : MetaM Expr := do
  let ps := (collectLevelParams {} stmt).params.toList
  go (stmt.instantiateLevelParams ps (ps.map fun _ => levelZero))
where
  go (e : Expr) : MetaM Expr := do
    let .forallE n d b bi := e | return e
    let d ← instantiateMVars d
    if (← whnfR d).isType && (← whnfR d) == mkSort levelOne then
      return ← go (b.instantiate1 (mkConst ``Int))
    if bi.isInstImplicit then
      if let .some inst ← trySynthInstance d then return ← go (b.instantiate1 inst)
    withLocalDecl n bi d fun x => do mkForallFVars #[x] (← go (b.instantiate1 x))

/-- Builds and runs the check of a closed proposition `∀ xs, H₁ → … → Hₘ → C`, stopping when the
monotonic clock passes `deadline` (milliseconds). -/
def runStatement (stmt : Expr) (count deadline : Nat) : MetaM Outcome := do
  let opts ← getOptions
  try
    forallTelescope (← specialize stmt) fun xs body => do
      let mut binders := #[]
      let mut hyps := #[]
      let mut hypTypes := #[]
      for x in xs do
        let ty ← inferType x
        if ← isProp ty then
          hyps := hyps.push x
          hypTypes := hypTypes.push (← eraseProofs hyps.pop ty)
        else
          if ty.hasAnyFVar (fun f => hyps.any (·.fvarId! == f)) then
            throwError "the type of a binder uses a proof of a hypothesis"
          binders := binders.push x
      let res ← resultOf binders hypTypes (← eraseProofs hyps body)
      let pairTy ← inferType res
      let mut enums : Array (Array Expr) := #[]
      let mut total := 1
      for x in binders do
        match ← enumValues? (← inferType x) with
        | some vs => enums := enums.push vs; total := total * vs.size
        | none => break
      if enums.size == binders.size && total ≤ assay.enumLimit.get opts then
        let thunkTy ← mkArrow (mkConst ``Unit) pairTy
        let mut acc ← mkListLit thunkTy [.lam `_ (mkConst ``Unit) res .default]
        for x in binders.reverse, vs in enums.reverse do
          let lst ← mkListLit (← inferType x) vs.toList
          acc ← mkAppM ``List.flatMap #[← mkLambdaFVars #[x] acc, lst]
        let run := mkApp2 (mkConst ``Assay.runAll) acc (toExpr deadline)
        return .ran (← (← evalSummary (← instantiateMVars run)))
      let gen ← mkAppOptM ``Pure.pure #[mkConst ``Plausible.Gen [0], none, none, res]
      let mut acc := gen
      for x in binders.reverse do
        let s ← try mkAppOptM ``Assay.sample #[← inferType x, none]
          catch _ => throwError "no `SampleableExt` instance for `{← ppExpr (← inferType x)}`"
        acc ← mkAppM ``Bind.bind #[s, ← mkLambdaFVars #[x] acc]
      let run := mkApp5 (mkConst ``Assay.runRandom) acc
        (toExpr count) (toExpr (assay.maxSize.get opts)) (toExpr (assay.seed.get opts)) (toExpr deadline)
      return .ran (← (← evalSummary (← instantiateMVars run)))
  catch e =>
    return .untestable (← e.toMessageData.toString)

end Assay
