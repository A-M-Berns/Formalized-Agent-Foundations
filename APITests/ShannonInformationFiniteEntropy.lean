import ShannonInformation.API
import ShannonInformation.FiniteEntropy.Defs
import Mathlib.Probability.Distributions.Geometric

/-! # Client-style tests for the finite-entropy generalization layer

`ShannonInformation/FiniteEntropy/` introduces `FiniteEntropyMeasure` / `FiniteEntropyOf`
as the hypothesis PFR's `FiniteRange` ought eventually to be relaxed to.  A generalization
is only worth its weight if it is *strictly* more general, and if it does not disturb what
already worked.  This file checks both, from outside the layer:

* the existing `FiniteRange` instance graph still discharges the new class by
  `infer_instance`, so no client that worked before has to change;
* a **constructed** witness — the geometric law on `ℕ` with success probability `1/2` —
  has finite entropy and does **not** have finite range.  That pair of facts is the content
  of `ShannonInformation/SCOPE.md` §2, which until now asserted it only informally.

The witness is genuinely computed, not asserted: its point masses, its entropy series and
its entropy `2 * log 2` are all derived from `ProbabilityTheory.geometricMeasure`.

Note on imports: `Mathlib.Probability.Distributions.Geometric` co-imports with
`ShannonInformation.API` without trouble.  The clash recorded in
`ShannonInformation/README.md` ("Known constraint") is specific to importing *all* of
Mathlib; targeted imports are fine, and this file is the standing evidence of that. -/

open MeasureTheory ProbabilityTheory Real ShannonInformation

namespace APITests.ShannonInformationFiniteEntropy

/-! ### Coexistence: the `FiniteRange` instance graph feeds the new class

Nothing here is proved by hand.  Each `infer_instance` goes
`FiniteRange → FiniteSupport → FiniteEntropyMeasure`, which is what makes the new
hypothesis a drop-in weakening rather than a fork of the API. -/

example {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → S) (μ : Measure Ω) :
    FiniteEntropyOf X μ := by infer_instance

example {S : Type*} [MeasurableSpace S] (μ : Measure S) [FiniteSupport μ] :
    FiniteEntropyMeasure μ := by infer_instance

/-- A derived member of the `FiniteRange` graph — `f ∘ X` — also lands in the new class
with no user input, which is the property that keeps the graph useful. -/
example {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSingletonClass T]
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → S) (f : S → T) (μ : Measure Ω) [FiniteRange X] :
    FiniteEntropyOf (f ∘ X) μ := by infer_instance

/-! ### The witness: a geometric variable on `ℕ` -/

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

/-! ### The closure lemmas apply to it

The pair closure is the one that needed new mathematics (a termwise bound summed over a
product index), so exercising it on an infinite-range variable — where `FiniteRange` cannot
help — is the test that it actually bought something. -/

/-- The diagonal pair of the witness with itself has finite entropy — via
`finiteEntropyOf_pair`, not via any `FiniteRange` instance. -/
lemma finiteEntropyOf_geom_diag : FiniteEntropyOf (fun n : ℕ ↦ (id n, id n)) geom :=
  finiteEntropyOf_pair measurable_id measurable_id

/-- …and the marginal of that pair comes back, via `finiteEntropyOf_fst`. -/
example : FiniteEntropyOf (id : ℕ → ℕ) geom :=
  haveI := finiteEntropyOf_geom_diag
  finiteEntropyOf_fst (Y := (id : ℕ → ℕ)) measurable_id measurable_id

end APITests.ShannonInformationFiniteEntropy
