/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is **FAF-authored**, mathematics included; see the header of
`ShannonInformation/FiniteEntropy/Summable.lean`.
-/
module

public import PFR.ForMathlib.Entropy.Basic
public import ShannonInformation.FiniteEntropy.Defs
public import Mathlib.Probability.Distributions.Geometric

/-!
# The separating witness: a geometric law on `ℕ`

`FiniteEntropyOf` is worth its weight only if it is *strictly* weaker than PFR's
`FiniteRange`.  This module constructs the witness that separates them and computes it: the
geometric law on `ℕ` with success probability `1/2` has entropy `2 log 2` and does **not**
have finite range.

It lives in the library rather than in `APITests/ShannonInformationFiniteEntropy.lean`
because it has two clients — that test file, and `Condensation/Examples.lean`, where
`Condensation.Example.geomModel` is the random variable model that Definition 3.1 admits and
the retired `dd:finite-range` narrowing excluded.  Duplicating fifty lines of geometric
series across a test and a library would be the wrong trade.

`ShannonInformation/API.lean` deliberately does **not** re-export this module: a client that
merely wants the entropy corpus should not pay for `Mathlib.Probability.Distributions.Geometric`.
Import `ShannonInformation.FiniteEntropy.Examples` directly if you want the witness.

Note on imports: `Mathlib.Probability.Distributions.Geometric` co-imports with the vendored
PFR shims without trouble.  The clash recorded in `ShannonInformation/README.md` ("Known
constraint") is specific to importing *all* of Mathlib; targeted imports are fine.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace ShannonInformation

/-! ### The construction -/

/-- Success probability `1/2`, as a point of the unit interval. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num⟩

lemma half_ne_zero : half ≠ 0 := by
  intro h
  simpa [half] using congrArg Subtype.val h

/-- The geometric law on `ℕ` with success probability `1/2`: the number of failures before
the first success of a fair coin. -/
noncomputable def geom : Measure ℕ := geometricMeasure half

instance : IsProbabilityMeasure geom := by
  unfold geom; infer_instance

/-- The point masses of the witness: `geom {n} = 2 ^ (-(n + 1))`. -/
lemma geom_real_singleton (n : ℕ) : geom.real {n} = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [geom, geometricMeasure_real_singleton half_ne_zero n]
  norm_num [half, pow_succ]

/-- The entropy series of the witness, in closed form. -/
lemma negMulLog_geom_real_singleton (n : ℕ) :
    negMulLog (geom.real {n}) = ((n : ℝ) + 1) * Real.log 2 * (1 / 2 : ℝ) ^ (n + 1) := by
  have hlog : Real.log ((1 / 2 : ℝ) ^ (n + 1)) = -(((n : ℝ) + 1) * Real.log 2) := by
    rw [Real.log_pow, one_div, Real.log_inv]
    push_cast
    ring
  rw [geom_real_singleton, negMulLog, hlog]
  ring

/-- The entropy series converges: an arithmetico-geometric series with ratio `1/2`. -/
lemma summable_negMulLog_geom : Summable fun n : ℕ ↦ negMulLog (geom.real {n}) := by
  have h1 : Summable fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1 / 2)
      (by rw [Real.norm_eq_abs]; norm_num)
  have h2 : Summable fun n : ℕ ↦ (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine ((h1.add h2).mul_left (Real.log 2 / 2)).congr fun n ↦ ?_
  rw [negMulLog_geom_real_singleton]
  ring

/-- **The witness has finite entropy.** -/
instance finiteEntropyMeasure_geom : FiniteEntropyMeasure geom :=
  FiniteEntropyMeasure.of_summable_real summable_negMulLog_geom

/-- …and so does the identity variable that reads it off, which is the form the closure
lemmas are stated in.  (`geom.map id` is not `geom` by `rfl`, so this needs its own
instance rather than falling out of the previous one.) -/
instance finiteEntropyOf_id_geom : FiniteEntropyOf (id : ℕ → ℕ) geom := by
  show FiniteEntropyMeasure (geom.map id)
  rw [Measure.map_id]
  infer_instance

/-- **The witness does not have finite range**, so every `FiniteRange`-tagged theorem in the
vendored library is unavailable for it. -/
lemma not_finiteRange_id : ¬ FiniteRange (id : ℕ → ℕ) := fun h ↦
  Set.infinite_range_of_injective Function.injective_id h.finite

/-- **`FiniteEntropyOf` is strictly weaker than `FiniteRange`.**  This is the claim
`ShannonInformation/SCOPE.md` §2 makes informally, discharged on a constructed witness. -/
lemma finiteEntropyOf_strictly_weaker :
    FiniteEntropyOf (id : ℕ → ℕ) geom ∧ ¬ FiniteRange (id : ℕ → ℕ) :=
  ⟨inferInstance, not_finiteRange_id⟩

/-! ### The witness is informative

The facts above would all hold of a variable whose entropy happened to be `0`, so they do
not by themselves show that the generalization has any content.  This does: the entropy is
computed, and it is `2 * log 2` — two bits, the textbook value for `Geometric(1/2)`. -/

/-- Reading `H[X ; μ]` as its defining series.  This is PFR's `entropy_eq_sum` with
`Measure.map_id`; there is no new mathematics in it, and none is needed. -/
lemma entropy_geom_eq_tsum :
    H[(id : ℕ → ℕ) ; geom] = ∑' n, negMulLog (geom.real {n}) := by
  rw [entropy_eq_sum, Measure.map_id]

lemma entropy_geom : H[(id : ℕ → ℕ) ; geom] = 2 * Real.log 2 := by
  have h1 : Summable fun n : ℕ ↦ (n : ℝ) * (1 / 2 : ℝ) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1 / 2)
      (by rw [Real.norm_eq_abs]; norm_num)
  have h2 : Summable fun n : ℕ ↦ (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hv1 : (∑' n : ℕ, (n : ℝ) * (1 / 2 : ℝ) ^ n) = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ))
      (by rw [Real.norm_eq_abs]; norm_num)]
    norm_num
  have hv2 : (∑' n : ℕ, (1 / 2 : ℝ) ^ n) = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [entropy_geom_eq_tsum, tsum_congr negMulLog_geom_real_singleton]
  have hrw : ∀ n : ℕ, ((n : ℝ) + 1) * Real.log 2 * (1 / 2 : ℝ) ^ (n + 1)
      = Real.log 2 / 2 * ((n : ℝ) * (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n) := fun n ↦ by ring
  rw [tsum_congr hrw, (h1.add h2).tsum_mul_left, h1.tsum_add h2, hv1, hv2]
  ring

lemma entropy_geom_pos : 0 < H[(id : ℕ → ℕ) ; geom] := by
  rw [entropy_geom]
  positivity

end ShannonInformation
