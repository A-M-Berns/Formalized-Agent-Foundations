/-
# Brouwer fixed-point theorem (`lem:fpl` dependency)

⚠ AXIOMATIZED via `sorry`. The installed Mathlib has **no** Brouwer/Kakutani fixed-point
theorem (see `PROGRESS.md`, OPEN RISK 2). This file states the form `lem:fpl` needs — a
continuous self-map of a compact convex set has a fixed point — so the construction can be
built against a stable interface now, and the `sorry` discharged later by contributing the
theorem upstream (or porting a proof). Track it as the project's one mathematical axiom
until then.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic

open Set Metric

namespace LogicalInduction

theorem brouwer_fixed_point {d : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (_hK_compact : IsCompact K) (_hK_convex : Convex ℝ K)
    (_hK_nonempty : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (_hf_cont : ContinuousOn f K) (_hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  sorry

end LogicalInduction
