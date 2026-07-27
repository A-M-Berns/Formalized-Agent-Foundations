import Mathlib.Data.List.TakeDrop
#check @List.take_append
#check @List.take_of_length_le
#check @List.take_succ_cons
#check @List.take_length
example (l₁ l₂ : List ℕ) (j : ℕ) :
    (l₁ ++ l₂).take j = l₁.take j ++ l₂.take (j - l₁.length) := by
  exact? says exact List.take_append l₁ l₂ j
