namespace Forms

def headOr_precond (xs : List Nat) : Prop := xs ≠ []

def headOr (xs : List Nat) (h : headOr_precond xs) : Nat :=
  match xs with
  | [] => 0
  | x :: _ => x

def headOr_postcond (xs : List Nat) (result : Nat) (_ : headOr_precond xs) : Prop :=
  xs.head? = some result

theorem headOr_spec_satisfied (xs : List Nat) (h : headOr_precond xs) :
    headOr_postcond xs (headOr xs h) h := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs => rfl

def maxOf_precond (xs : List Nat) : Prop := xs ≠ []

def maxOf (xs : List Nat) (h : maxOf_precond xs) : Nat :=
  xs.foldl max (xs.head h)

def maxOf_postcond (xs : List Nat) (result : Nat) (_ : maxOf_precond xs) : Prop :=
  ∀ x ∈ xs, x ≤ result

theorem maxOf_spec_satisfied (xs : List Nat) (h : maxOf_precond xs) :
    maxOf_postcond xs (maxOf xs h) h := by
  sorry

def lastOf_precond (xs : List Nat) : Prop := xs ≠ []

def lastOf (xs : List Nat) (h : lastOf_precond xs) : Nat :=
  xs.getLast h

def lastOf_postcond (xs : List Nat) (result : Nat) (_ : lastOf_precond xs) : Prop :=
  result ∈ xs

theorem lastOf_spec_satisfied (xs : List Nat) (h : lastOf_precond xs) :
    lastOf_postcond xs (lastOf xs h) h :=
  List.getLast_mem h

end Forms
