namespace Forms

def clampU8 (n : Int) : Nat :=
  if n < 0 then 0 else if n > 255 then 255 else n.toNat

def ClampInRange : Prop := ∀ n : Int, clampU8 n ≤ 255

theorem clampInRange_proven : ClampInRange := by
  intro n
  unfold clampU8
  split
  · omega
  · split <;> omega

end Forms
