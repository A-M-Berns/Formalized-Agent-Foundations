import Mathlib.Algebra.BigOperators.Intervals

/-!
# Palomar smoke-test solution — NEVER SUBMIT THIS

Discharges the single `sorry` in `Palomar.SmokeTest.Challenge`.  See that module's
docstring; this pair exists to validate the Comparator harness, not to state
mathematics anyone needs.
-/

/-- Gauss's sum.  Mathlib proves this outright. -/
theorem palomar_smoke_gauss (n : ℕ) :
    (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) :=
  Finset.sum_range_id_mul_two n
