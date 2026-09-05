import Mathlib.Algebra.BigOperators.Intervals

/-!
# Palomar smoke-test challenge — NEVER SUBMIT THIS

This is **not** a Palomar entry and must never be registered as one.  It exists only to
prove that the Comparator harness is correctly installed and invoked, so that the first
real entry debugs mathematics rather than plumbing.

It states one small Mathlib-only lemma (Gauss's sum) as a `sorry`, exactly as a real
challenge module does.  `Palomar/SmokeTest/Solution.lean` discharges it.

See `Palomar/README.md`, *Comparator smoke test*, for the exact invocation.
-/

/-- Gauss's sum, stated as a challenge: twice the sum of `0, …, n-1` is `n * (n - 1)`. -/
theorem palomar_smoke_gauss (n : ℕ) :
    (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) := sorry
