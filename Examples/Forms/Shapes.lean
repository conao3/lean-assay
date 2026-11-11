namespace Forms.Shapes

variable {α : Type} [BEq α]

def indexOf (x : α) : List α → Option Nat
  | [] => none
  | y :: ys => if y == x then some 0 else (indexOf x ys).map (· + 1)

def IndexFound : Prop :=
  ∀ (α : Type) [BEq α] (x : α) (xs : List α), (∃ i, indexOf x xs = some i) ↔ xs.any (· == x) = true

theorem indexFound_proven : IndexFound := by
  sorry

def toNatOk (n : Int) : Except String Nat :=
  if n < 0 then .error "negative" else .ok n.toNat

theorem toNatOk_ok (n : Int) : 0 ≤ n → ∃ m, toNatOk n = .ok m ∧ (m : Int) = n := by
  sorry

theorem toNatOk_cases (n : Int) :
    match toNatOk n with
    | .ok _ => 0 ≤ n
    | .error _ => n < 0 := by
  sorry

end Forms.Shapes
