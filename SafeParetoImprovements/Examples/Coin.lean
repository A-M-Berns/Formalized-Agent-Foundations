import SafeParetoImprovements.Representatives
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# The fair coin

A two-point probability space shared by the examples that need a genuinely random `Π`
(the random Demand-Game representatives of `ProgramGameWitnesses.lean`, the Table 7
representatives of `Chicken.lean`).
-/

namespace SafeParetoImprovements

namespace Examples

open MeasureTheory Filter
open scoped ENNReal

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := ⟨by
  simp [coin, Measure.smul_apply, Measure.add_apply]
  rw [ENNReal.inv_two_add_inv_two]⟩

lemma integral_coin (f : Bool → ℝ) : (∫ ω, f ω ∂coin) = 2⁻¹ * (f true + f false) := by
  rw [coin, integral_smul_measure,
    integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_dirac, integral_dirac]
  simp

/-- Both faces carry positive mass, so "almost surely" is "surely". -/
lemma ae_coin_iff (P : Bool → Prop) : (∀ᵐ ω ∂coin, P ω) ↔ P true ∧ P false := by
  classical
  rw [ae_iff, coin, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
    Measure.dirac_apply, smul_eq_mul, mul_eq_zero, add_eq_zero]
  simp [Set.indicator_apply]

end Examples

end SafeParetoImprovements
