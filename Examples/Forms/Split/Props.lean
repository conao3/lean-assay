import Examples.Forms.Split.Model

namespace Forms.Split

def addTwice (a b : Nat) : Nat := clampAdd (clampAdd a b) b

def AddTwiceBounded : Prop := ∀ a b : Nat, addTwice a b ≤ 10

theorem addTwiceBounded_proven : AddTwiceBounded := by
  intro a b
  unfold addTwice clampAdd
  generalize cap (a + b) + b = m
  unfold cap
  split <;> omega

end Forms.Split
