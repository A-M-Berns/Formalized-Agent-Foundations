import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Prefix sums, weighted averages and weighted bias

The averaging vocabulary the §4.3–4.4 statistical arguments are stated in.  This module
renders no paper node of its own: it declares four objects — `prefixSum`,
`DivergentWeighting`, `weightedAverage` and `weightedBias` — and everything proved about them
is a `lemma`; nothing here carries a `Paper node` line.

`prefixSum x n` is the inclusive sum of days `0` through `n`, with the Abel summation
identity `prefixSum_mul_eq_abel` and the lower bound `prefixSum_mul_lower_of_prefixSum_lower`
that the weighted arguments run on.

`DivergentWeighting W P` is the market-generated weighting condition: realized values in
`[0,1]` and prefix sums tending to infinity — the denominator hypothesis every weighted
average needs.

`weightedAverage w x n` is the normalized average `Σ wᵢxᵢ / Σ wᵢ` (with a total zero branch,
irrelevant eventually under a divergent weighting), and `weightedBias w market truth` its
market-minus-truth instance.  The algebra `weightedAverage_add` / `_sub` / `_const_mul`, the
range lemmas `weightedAverage_mem_Icc` and `weightedAverage_mem_Icc_of_support`, and the
step-vanishing lemma `weightedAverage_step_tendsto_zero` are what the calibration and
recurring-unbiasedness proofs consume.
-/

namespace LogicalInduction

open Filter Topology Set

/-- Inclusive prefix sum: `prefixSum x n` sums days `0` through `n`. -/
noncomputable def prefixSum (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), x i

@[simp] lemma prefixSum_zero (x : ℕ → ℝ) : prefixSum x 0 = x 0 := by
  simp [prefixSum]

lemma prefixSum_succ (x : ℕ → ℝ) (n : ℕ) :
    prefixSum x (n + 1) = prefixSum x n + x (n + 1) := by
  simp [prefixSum, Finset.sum_range_succ]

/-- Removing a fixed finite prefix and scaling by a positive constant preserves
divergence of inclusive prefix sums.  The explicit identity is useful for launched
trader families, whose `k`th member must be syntactically empty before day `k`. -/
lemma prefixSum_gate_mul_eq (x : ℕ → ℝ) (c : ℝ) (k n : ℕ) (hkn : k ≤ n) :
    prefixSum (fun i => if k ≤ i then c * x i else 0) n =
      c * (prefixSum x n - ∑ i ∈ Finset.range k, x i) := by
  induction n, hkn using Nat.le_induction with
  | base =>
      rw [prefixSum, Finset.sum_range_succ]
      have hz : ∑ i ∈ Finset.range k, (if k ≤ i then c * x i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg]
        exact Nat.not_le.mpr (Finset.mem_range.mp hi)
      rw [hz, if_pos le_rfl, prefixSum, Finset.sum_range_succ]
      ring
  | succ n hkn ih =>
      rw [prefixSum_succ, ih, prefixSum_succ,
        if_pos (hkn.trans (Nat.le_succ n))]
      ring

lemma prefixSum_gate_mul_tendsto_atTop (x : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hdiv : Tendsto (prefixSum x) atTop atTop) (k : ℕ) :
    Tendsto (prefixSum (fun i => if k ≤ i then c * x i else 0)) atTop atTop := by
  let C : ℝ := ∑ i ∈ Finset.range k, x i
  have hscaled : Tendsto (fun n => c * prefixSum x n) atTop atTop :=
    hdiv.const_mul_atTop hc
  have hshifted : Tendsto (fun n => c * prefixSum x n + -(c * C)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-(c * C)) hscaled
  apply Tendsto.congr' _ hshifted
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [prefixSum_gate_mul_eq x c k n hn]
  dsimp only [C]
  ring

/-- Finite Abel summation in inclusive-prefix notation. -/
lemma prefixSum_mul_eq_abel (β y : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => β i * y i) n =
      β n * prefixSum y n +
        ∑ i ∈ Finset.range n, (β i - β (i + 1)) * prefixSum y i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prefixSum_succ, prefixSum_succ, Finset.sum_range_succ, ih]
      ring

lemma abel_coefficients_sum (β : ℕ → ℝ) (n : ℕ) :
    β n + ∑ i ∈ Finset.range n, (β i - β (i + 1)) = β 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith

/-- A nonnegative decreasing cap cannot turn a stream whose every cumulative sum is at
least `-δ` into weighted cumulative loss below `-δ · β₀`.  This is the Abel/Cesàro bridge
needed by the continuous fractional cap. -/
lemma prefixSum_mul_lower_of_prefixSum_lower
    (β y : ℕ → ℝ) (δ : ℝ)
    (hβ0 : ∀ n, 0 ≤ β n) (hβanti : Antitone β)
    (hy : ∀ n, -δ ≤ prefixSum y n) (n : ℕ) :
    -δ * β 0 ≤ prefixSum (fun i => β i * y i) n := by
  rw [prefixSum_mul_eq_abel]
  have hlast : β n * (-δ) ≤ β n * prefixSum y n :=
    mul_le_mul_of_nonneg_left (hy n) (hβ0 n)
  have hsum :
      ∑ i ∈ Finset.range n, (β i - β (i + 1)) * (-δ) ≤
        ∑ i ∈ Finset.range n, (β i - β (i + 1)) * prefixSum y i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hy i)
      (sub_nonneg.mpr (hβanti (Nat.le_succ i)))
  calc
    -δ * β 0 = β n * (-δ) +
        ∑ i ∈ Finset.range n, (β i - β (i + 1)) * (-δ) := by
          rw [← Finset.sum_mul]
          rw [← add_mul, abel_coefficients_sum]
          ring
    _ ≤ β n * prefixSum y n +
        ∑ i ∈ Finset.range n, (β i - β (i + 1)) * prefixSum y i :=
          add_le_add hlast hsum

/-- A market-generated weighting is divergent when its realized values lie in `[0,1]`
and its inclusive prefix sums tend to positive infinity. -/
def DivergentWeighting (W : ℕ → EF) (P : History) : Prop :=
  (∀ n, 0 ≤ (W n).denote P ∧ (W n).denote P ≤ 1) ∧
    Tendsto (prefixSum (fun n => (W n).denote P)) atTop atTop

lemma DivergentWeighting.eventually_prefixSum_pos {W : ℕ → EF} {P : History}
    (h : DivergentWeighting W P) :
    ∀ᶠ n in atTop, 0 < prefixSum (fun i => (W i).denote P) n :=
  h.2.eventually (eventually_gt_atTop 0)

/-! ## Weighted averages and bias -/

/-- Normalized weighted average through day `n`.  The zero branch is irrelevant
eventually for divergent weightings, but makes the definition total. -/
noncomputable def weightedAverage (w x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if prefixSum w n = 0 then 0
  else prefixSum (fun i => w i * x i) n / prefixSum w n

lemma weightedAverage_eq_div {w x : ℕ → ℝ} {n : ℕ}
    (hden : prefixSum w n ≠ 0) :
    weightedAverage w x n =
      prefixSum (fun i => w i * x i) n / prefixSum w n := by
  simp [weightedAverage, hden]

lemma prefixSum_add (x y : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => x i + y i) n = prefixSum x n + prefixSum y n := by
  simp only [prefixSum, Finset.sum_add_distrib]

lemma prefixSum_sub (x y : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => x i - y i) n = prefixSum x n - prefixSum y n := by
  simp only [prefixSum, Finset.sum_sub_distrib]

lemma weightedAverage_sub (w x y : ℕ → ℝ) {n : ℕ}
    (hden : prefixSum w n ≠ 0) :
    weightedAverage w (fun i => x i - y i) n =
      weightedAverage w x n - weightedAverage w y n := by
  simp only [weightedAverage_eq_div hden]
  rw [show prefixSum (fun i => w i * (x i - y i)) n =
      prefixSum (fun i => w i * x i) n - prefixSum (fun i => w i * y i) n by
    rw [← prefixSum_sub]
    congr 1
    funext i
    ring]
  field_simp

lemma weightedAverage_add (w x y : ℕ → ℝ) {n : ℕ}
    (hden : prefixSum w n ≠ 0) :
    weightedAverage w (fun i => x i + y i) n =
      weightedAverage w x n + weightedAverage w y n := by
  simp only [weightedAverage_eq_div hden]
  rw [show prefixSum (fun i => w i * (x i + y i)) n =
      prefixSum (fun i => w i * x i) n + prefixSum (fun i => w i * y i) n by
    rw [← prefixSum_add]
    congr 1
    funext i
    ring]
  field_simp

/-- Fixed scalar multiplication commutes with the weighted average, including its
zero-denominator branch. -/
lemma weightedAverage_const_mul (w x : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    weightedAverage w (fun i => c * x i) n = c * weightedAverage w x n := by
  by_cases hden : prefixSum w n = 0
  · simp [weightedAverage, hden]
  · rw [weightedAverage_eq_div hden, weightedAverage_eq_div hden]
    have hnum : prefixSum (fun i => w i * (c * x i)) n =
        c * prefixSum (fun i => w i * x i) n := by
      simp only [prefixSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hnum]
    ring

lemma weightedAverage_mem_Icc {w x : ℕ → ℝ} {a b : ℝ} {n : ℕ}
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, x i ∈ Icc a b)
    (hden : 0 < prefixSum w n) :
    weightedAverage w x n ∈ Icc a b := by
  rw [weightedAverage_eq_div (ne_of_gt hden)]
  constructor
  · apply (le_div_iff₀ hden).2
    calc
      a * prefixSum w n = prefixSum (fun i => w i * a) n := by
        simp only [prefixSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ prefixSum (fun i => w i * x i) n := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hx i).1 (hw i)
  · apply (div_le_iff₀ hden).2
    calc
      prefixSum (fun i => w i * x i) n ≤ prefixSum (fun i => w i * b) n := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hx i).2 (hw i)
      _ = b * prefixSum w n := by
        simp only [prefixSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Weighted averages only need the value bound on the support of the weighting.  This is
the form calibration uses: the continuous indicator is zero whenever the quoted price is
outside the target interval. -/
lemma weightedAverage_mem_Icc_of_support {w x : ℕ → ℝ} {a b : ℝ} {n : ℕ}
    (hw : ∀ i, 0 ≤ w i)
    (hsupport : ∀ i, 0 < w i → x i ∈ Icc a b)
    (hden : 0 < prefixSum w n) :
    weightedAverage w x n ∈ Icc a b := by
  rw [weightedAverage_eq_div (ne_of_gt hden)]
  constructor
  · apply (le_div_iff₀ hden).2
    calc
      a * prefixSum w n = prefixSum (fun j => w j * a) n := by
        simp only [prefixSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ prefixSum (fun j => w j * x j) n := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : w j = 0
        · simp [hj]
        · exact mul_le_mul_of_nonneg_left
            ((hsupport j (lt_of_le_of_ne (hw j) (Ne.symm hj))).1) (hw j)
  · apply (div_le_iff₀ hden).2
    calc
      prefixSum (fun j => w j * x j) n ≤ prefixSum (fun j => w j * b) n := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : w j = 0
        · simp [hj]
        · exact mul_le_mul_of_nonneg_left
            ((hsupport j (lt_of_le_of_ne (hw j) (Ne.symm hj))).2) (hw j)
      _ = b * prefixSum w n := by
        simp only [prefixSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- The paper's normalized bias: market assessment minus determined value. -/
noncomputable def weightedBias (w market truth : ℕ → ℝ) (n : ℕ) : ℝ :=
  weightedAverage w (fun i => market i - truth i) n

lemma weightedBias_eq_market_sub_truth (w market truth : ℕ → ℝ) {n : ℕ}
    (hden : prefixSum w n ≠ 0) :
    weightedBias w market truth n =
      weightedAverage w market n - weightedAverage w truth n := by
  exact weightedAverage_sub w market truth hden

/-- Negating both the affine price and its determined value negates normalized bias,
including the harmless zero-denominator branch. -/
lemma weightedBias_neg (w market truth : ℕ → ℝ) (n : ℕ) :
    weightedBias w (fun i => -market i) (fun i => -truth i) n =
      -weightedBias w market truth n := by
  simp only [weightedBias, weightedAverage]
  split <;> rename_i hden
  · simp
  · have hnum :
        prefixSum (fun i => w i * (-market i - -truth i)) n =
          -prefixSum (fun i => w i * (market i - truth i)) n := by
      simp only [prefixSum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hnum]
    ring

/-- Scaling both market assessment and determined truth scales normalized bias exactly. -/
lemma weightedBias_const_mul (w market truth : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    weightedBias w (fun i => c * market i) (fun i => c * truth i) n =
      c * weightedBias w market truth n := by
  unfold weightedBias
  rw [show (fun i => c * market i - c * truth i) =
      fun i => c * (market i - truth i) by funext i; ring,
    weightedAverage_const_mul]

/-- Normalized weighted averages of a bounded stream have vanishing adjacent jumps when
the nonnegative weights have divergent total mass.  This discharges the analytic premise
used by the recurring-unbiasedness crossing argument; it is not assumed as a regularity
condition on the bias. -/
lemma weightedAverage_step_tendsto_zero
    (w x : ℕ → ℝ) (C : ℝ)
    (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1)
    (hx : ∀ n, |x n| ≤ C)
    (hdiv : Tendsto (prefixSum w) atTop atTop) :
    Tendsto (fun n => weightedAverage w x (n + 1) - weightedAverage w x n)
      atTop (𝓝 0) := by
  have hC : 0 ≤ C := (abs_nonneg (x 0)).trans (hx 0)
  have hpos : ∀ᶠ n in atTop, 0 < prefixSum w n :=
    hdiv.eventually (eventually_gt_atTop 0)
  have hbound : ∀ᶠ n in atTop,
      |weightedAverage w x (n + 1) - weightedAverage w x n| ≤
        (2 * C) / prefixSum w (n + 1) := by
    filter_upwards [hpos] with n hn
    have hns : 0 < prefixSum w (n + 1) := by
      rw [prefixSum_succ]
      exact add_pos_of_pos_of_nonneg hn (hw0 (n + 1))
    have havg : weightedAverage w x n ∈ Icc (-C) C := by
      apply weightedAverage_mem_Icc hw0 (fun i => ?_) hn
      rw [mem_Icc, ← abs_le]
      exact hx i
    have hformula :
        weightedAverage w x (n + 1) - weightedAverage w x n =
          w (n + 1) * (x (n + 1) - weightedAverage w x n) /
            prefixSum w (n + 1) := by
      rw [weightedAverage_eq_div (ne_of_gt hns),
        weightedAverage_eq_div (ne_of_gt hn), prefixSum_succ, prefixSum_succ]
      have hsumne : prefixSum w n + w (n + 1) ≠ 0 := by
        have := hw0 (n + 1)
        linarith
      field_simp [ne_of_gt hn, hsumne]
      ring
    rw [hformula, abs_div, abs_mul, abs_of_nonneg (hw0 (n + 1)),
      abs_of_pos hns]
    apply div_le_div_of_nonneg_right _ hns.le
    have hdiff : |x (n + 1) - weightedAverage w x n| ≤ 2 * C := by
      rw [abs_le]
      have hxn := (abs_le.mp (hx (n + 1)))
      constructor <;> linarith [havg.1, havg.2]
    calc
      w (n + 1) * |x (n + 1) - weightedAverage w x n|
          ≤ 1 * (2 * C) :=
            mul_le_mul (hw1 (n + 1)) hdiff (abs_nonneg _) (by linarith)
      _ = 2 * C := one_mul _
  have hdenShift : Tendsto (fun n => prefixSum w (n + 1)) atTop atTop :=
    hdiv.comp (tendsto_add_atTop_nat 1)
  have hmajorant : Tendsto (fun n => (2 * C) / prefixSum w (n + 1))
      atTop (𝓝 0) := hdenShift.const_div_atTop (2 * C)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hmajorant

end LogicalInduction
