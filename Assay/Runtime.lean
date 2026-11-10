import Plausible

/-!
The run-time half of `#assay`: the values a generated check returns, and the loops that run a
check over random samples or over every value of a small type.
-/

open Plausible

namespace Assay

/-- The result of one input: the hypotheses did not hold, the conclusion held, or it did not. -/
inductive Verdict where
  | discarded
  | held
  | broke
  deriving Repr, BEq, Inhabited

/-- `verdict hyps concl` is `discarded` unless `hyps`, and then `held` or `broke` by `concl ()`. The
conclusion is computed only when the hypotheses hold. -/
def verdict (hyps : Bool) (concl : Unit → Bool) : Verdict :=
  if !hyps then .discarded else if concl () then .held else .broke

/-- Stands for the proof of a hypothesis in a check. A check computes its conclusion only when the
hypotheses hold, and the compiler erases proofs, so code that takes a precondition runs on inputs
that satisfy it. -/
axiom assumed (p : Prop) : p

/-- What running a clause over many inputs found. -/
structure Summary where
  /-- Inputs that satisfied every hypothesis and the conclusion. -/
  held : Nat := 0
  /-- Inputs that did not satisfy the hypotheses. -/
  discarded : Nat := 0
  /-- The first input that satisfied every hypothesis but not the conclusion, one string per binder. -/
  counterexample : Option (List String) := none
  /-- Whether every value of the input types was tried. -/
  exhaustive : Bool := false
  /-- Whether the run stopped at its deadline before trying every input. -/
  timedOut : Bool := false
  deriving Repr, Inhabited

/-- Prints a value for a counterexample. -/
def showValue {α : Type} [Repr α] (a : α) : String :=
  toString (repr a)

/-- Prints a binder and its value for a counterexample. -/
def showBinder {α : Type} [Repr α] (name : String) (a : α) : String :=
  s!"{name} := {repr a}"

/-- Adds one input's verdict to a summary; the first failure is kept as the counterexample. -/
def Summary.add (s : Summary) (v : Verdict) (shown : Thunk (List String)) : Summary :=
  match v with
  | .discarded => { s with discarded := s.discarded + 1 }
  | .held => { s with held := s.held + 1 }
  | .broke => if s.counterexample.isSome then s else { s with counterexample := some shown.get }

/-- Runs every input of a finite enumeration, stopping at the first counterexample or when the
monotonic clock passes `deadline` (milliseconds). -/
def runAll (inputs : List (Unit → Verdict × Thunk (List String))) (deadline : Nat) : IO Summary := do
  let mut s : Summary := { exhaustive := true }
  for input in inputs do
    if (← IO.monoMsNow) ≥ deadline then return { s with exhaustive := false, timedOut := true }
    let (v, shown) := input ()
    s := s.add v shown
    if s.counterexample.isSome then return s
  return s

/-- Runs `count` random inputs from `gen` with a fixed `seed`, growing the size from 0 to `maxSize`,
and stops at the first counterexample or when the monotonic clock passes `deadline`
(milliseconds). -/
def runRandom (gen : Gen (Verdict × Thunk (List String))) (count maxSize seed deadline : Nat) :
    IO Summary := do
  let mut stdGen := mkStdGen seed
  let mut s : Summary := {}
  for i in [0:count] do
    if (← IO.monoMsNow) ≥ deadline then return { s with timedOut := true }
    let size := i * maxSize / (max count 1)
    match ReaderT.run (StateT.run gen (ULift.up stdGen)) ⟨size⟩ with
    | Except.ok ((v, shown), g) =>
      stdGen := g.down
      s := s.add v shown
      if s.counterexample.isSome then return s
    | Except.error _ =>
      s := { s with discarded := s.discarded + 1 }
  return s

/-- Draws one value of a sampleable type. -/
def sample (α : Type) [SampleableExt α] : Gen α :=
  SampleableExt.interp <$> (Arbitrary.arbitrary : Gen (SampleableExt.proxy α))

end Assay
