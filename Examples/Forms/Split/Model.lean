namespace Forms.Split

def cap (n : Nat) : Nat :=
  if n < 10 then n else 10

def clampAdd (a b : Nat) : Nat := cap (a + b)

end Forms.Split
