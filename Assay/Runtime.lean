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

/-- `verdict hyps concl` is `discarded` unless `hyps`, and then `held` or `broke` by `concl`. -/
def verdict (hyps concl : Bool) : Verdict :=
  if !hyps then .discarded else if concl then .held else .broke

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

/-- Runs every input of a finite enumeration. -/
def runAll (inputs : List (Verdict × Thunk (List String))) : Summary :=
  inputs.foldl (fun s (v, shown) => s.add v shown) { exhaustive := true }

/-- Runs `count` random inputs from `gen` with a fixed `seed`, growing the size from 0 to `maxSize`,
and stops at the first counterexample. -/
def runRandom (gen : Gen (Verdict × Thunk (List String))) (count maxSize seed : Nat) : Summary := Id.run do
  let mut stdGen := mkStdGen seed
  let mut s : Summary := {}
  for i in [0:count] do
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
