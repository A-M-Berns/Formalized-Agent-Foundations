/-
# Recurring calibration and unbiasedness

This file begins the statistical tail of the paper.  It keeps three layers separate:

* the exact representation of a weighting generable from the market;
* normalized weighted averages and their limit-point analysis; and
* the operational weighted-bias trader theorem (developed below this analytic spine).

In particular, a zero denominator is assigned value zero, but every theorem which uses
division proves that the denominator is eventually positive from divergence.  This avoids
silently strengthening the paper's divergent-weighting hypothesis.
-/
import LogicalInduction.Properties.AffineCoherence
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact

namespace LogicalInduction

open Filter Topology Set
open scoped BigOperators

/-! ## Generated divergent weightings -/

/-- A sequence of expressible features generated uniformly in polynomial time and legal
on its own day.  Its denotation may depend continuously on the market prefix, exactly as
in the paper's notion “generable from `P`”. -/
structure PGenerableWeighting (W : ℕ → EF) : Prop where
  polySeg : PolySegStream (fun n => (W n).serialize)
  rank_le : ∀ n, (W n).rank ≤ n
  closed : ∀ n ρ V, (W n).denoteWith ρ V = (W n).denote V

/-- Operational certificate for the paper's efficiently computable positive calibration
widths.  The inverse-code field records closure under rational inversion in the repository's
fuel model; semantically it adds nothing beyond positivity and computability of `δ`. -/
structure PolyPositiveWidths (δ : ℕ → ℚ) : Prop where
  codes : PolyRatCodes δ
  inverse_codes : PolyRatCodes (fun n => 1 / δ n)
  positive : ∀ n, 0 < (δ n : ℝ)

/-- Lower continuous indicator `ctsInd[δₙ](a < Pₙ(φₙ))`. -/
def calibrationLower (φ : ℕ → Sentence) (a : ℚ) (δ : ℕ → ℚ) (n : ℕ) : EF :=
  clip01 (EF.mul
    (EF.add (EF.price (φ n) n) (EF.const (-a)))
    (EF.const (1 / δ n)))

/-- Upper continuous indicator `ctsInd[δₙ](Pₙ(φₙ) < b)`. -/
def calibrationUpper (φ : ℕ → Sentence) (b : ℚ) (δ : ℕ → ℚ) (n : ℕ) : EF :=
  clip01 (EF.mul
    (EF.add (EF.const b) (EF.mul (EF.const (-1)) (EF.price (φ n) n)))
    (EF.const (1 / δ n)))

/-- The paper's fuzzy selector `ctsInd[δₙ](a < Pₙ(φₙ) < b)`. -/
def calibrationIndicator (φ : ℕ → Sentence) (a b : ℚ)
    (δ : ℕ → ℚ) (n : ℕ) : EF :=
  efMin (calibrationLower φ a δ n) (calibrationUpper φ b δ n)

theorem calibrationIndicator_pgenerable
    (φ : ℕ → Sentence) (a b : ℚ) (δ : ℕ → ℚ)
    (hφ : PolySentenceCodes φ) (hδ : PolyPositiveWidths δ) :
    PGenerableWeighting (calibrationIndicator φ a b δ) := by
  obtain ⟨cφ, hφc⟩ := hφ
  have hpriceTok : PolyTokenStream (fun n => (EF.price (φ n) n).serialize) := by
    simpa [EF.serialize, List.append_assoc] using
      ((PolyTokenStream.const 0).append
        ((PolyTokenStream.polyTok hφc).append (PolyTokenStream.polyTok PolyFueled.id)))
  have hprice := PolySegStream.ofTokenStream hpriceTok
  have hinv : PolySegStream (fun n => (EF.const (1 / δ n)).serialize) :=
    PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp hδ.inverse_codes)
  have hlowerRaw := PolySegStream.serialize_mul
    (PolySegStream.serialize_add hprice
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-a)))) hinv
  have hupperRaw := PolySegStream.serialize_mul
    (PolySegStream.serialize_add
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const b))
      (PolySegStream.serialize_mul
        (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) hprice)) hinv
  refine
    { polySeg := PolySegStream.serialize_efMin
        (PolySegStream.serialize_clip01 hlowerRaw)
        (PolySegStream.serialize_clip01 hupperRaw)
      rank_le := ?_
      closed := ?_ }
  · intro n
    simp [calibrationIndicator, calibrationLower, calibrationUpper, EF.rank]
  · intro n ρ V
    simp [calibrationIndicator, calibrationLower, calibrationUpper, clip01, efMin,
      EF.denoteWith, EF.denote]

theorem calibrationIndicator_mem (φ : ℕ → Sentence) (a b : ℚ)
    (δ : ℕ → ℚ) (P : History) (n : ℕ) :
    0 ≤ (calibrationIndicator φ a b δ n).denote P ∧
      (calibrationIndicator φ a b δ n).denote P ≤ 1 := by
  rw [calibrationIndicator, efMin_denote]
  constructor
  · exact le_min
      (by rw [calibrationLower, clip01_denote]; exact clipVal_nonneg _)
      (by rw [calibrationUpper, clip01_denote]; exact clipVal_nonneg _)
  · exact (min_le_left _ _).trans
      (by rw [calibrationLower, clip01_denote]; exact clipVal_le_one _)

/-- The calibration selector has no false positives: positive weight implies the quoted
probability lies strictly inside the requested interval. -/
theorem calibrationIndicator_pos_imp
    (φ : ℕ → Sentence) (a b : ℚ) (δ : ℕ → ℚ)
    (hδ : ∀ n, 0 < (δ n : ℝ)) (P : History) (n : ℕ)
    (hpos : 0 < (calibrationIndicator φ a b δ n).denote P) :
    (P n (φ n) : ℝ) ∈ Ioo (a : ℝ) (b : ℝ) := by
  rw [calibrationIndicator, efMin_denote] at hpos
  have hlo : 0 < (calibrationLower φ a δ n).denote P :=
    lt_of_lt_of_le hpos (min_le_left _ _)
  have hhi : 0 < (calibrationUpper φ b δ n).denote P :=
    lt_of_lt_of_le hpos (min_le_right _ _)
  rw [calibrationLower, clip01_denote] at hlo
  rw [calibrationUpper, clip01_denote] at hhi
  have hloRaw := clipVal_pos_imp hlo
  have hhiRaw := clipVal_pos_imp hhi
  simp only [EF.denote_mul, EF.denote_add, EF.denote_price, EF.denote_const,
    Pi.mul_apply, Pi.add_apply, Rat.cast_neg, neg_mul] at hloRaw hhiRaw
  have hinv : 0 < ((1 / δ n : ℚ) : ℝ) := by
    push_cast
    exact one_div_pos.mpr (hδ n)
  have hleft : 0 < P n (φ n) + -(a : ℝ) := by
    rcases (mul_pos_iff.mp hloRaw) with h | h
    · exact h.1
    · exfalso; linarith [h.2, hinv]
  have hright : 0 < (b : ℝ) + -(((1 : ℚ) : ℝ) * P n (φ n)) := by
    rcases (mul_pos_iff.mp hhiRaw) with h | h
    · exact h.1
    · exfalso; linarith [h.2, hinv]
  norm_num at hright
  constructor <;> linarith

/-- Inclusive prefix sum, matching the repository's day-zero indexing convention. -/
noncomputable def prefixSum (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), x i

@[simp] theorem prefixSum_zero (x : ℕ → ℝ) : prefixSum x 0 = x 0 := by
  simp [prefixSum]

theorem prefixSum_succ (x : ℕ → ℝ) (n : ℕ) :
    prefixSum x (n + 1) = prefixSum x n + x (n + 1) := by
  simp [prefixSum, Finset.sum_range_succ]

/-- Removing a fixed finite prefix and scaling by a positive constant preserves
divergence of inclusive prefix sums.  The explicit identity is useful for launched
trader families, whose `k`th member must be syntactically empty before day `k`. -/
theorem prefixSum_gate_mul_eq (x : ℕ → ℝ) (c : ℝ) (k n : ℕ) (hkn : k ≤ n) :
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

theorem prefixSum_gate_mul_tendsto_atTop (x : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
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
theorem prefixSum_mul_eq_abel (β y : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => β i * y i) n =
      β n * prefixSum y n +
        ∑ i ∈ Finset.range n, (β i - β (i + 1)) * prefixSum y i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prefixSum_succ, prefixSum_succ, Finset.sum_range_succ, ih]
      ring

theorem abel_coefficients_sum (β : ℕ → ℝ) (n : ℕ) :
    β n + ∑ i ∈ Finset.range n, (β i - β (i + 1)) = β 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith

/-- A nonnegative decreasing cap cannot turn a stream whose every cumulative sum is at
least `-δ` into weighted cumulative loss below `-δ · β₀`.  This is the Abel/Cesàro bridge
needed by the continuous fractional cap. -/
theorem prefixSum_mul_lower_of_prefixSum_lower
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

theorem DivergentWeighting.eventually_prefixSum_pos {W : ℕ → EF} {P : History}
    (h : DivergentWeighting W P) :
    ∀ᶠ n in atTop, 0 < prefixSum (fun i => (W i).denote P) n :=
  h.2.eventually (eventually_gt_atTop 0)

/-! ## Weighted averages and bias -/

/-- Normalized weighted average through day `n`.  The zero branch is irrelevant
eventually for divergent weightings, but makes the definition total. -/
noncomputable def weightedAverage (w x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if prefixSum w n = 0 then 0
  else prefixSum (fun i => w i * x i) n / prefixSum w n

theorem weightedAverage_eq_div {w x : ℕ → ℝ} {n : ℕ}
    (hden : prefixSum w n ≠ 0) :
    weightedAverage w x n =
      prefixSum (fun i => w i * x i) n / prefixSum w n := by
  simp [weightedAverage, hden]

theorem prefixSum_add (x y : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => x i + y i) n = prefixSum x n + prefixSum y n := by
  simp only [prefixSum, Finset.sum_add_distrib]

theorem prefixSum_sub (x y : ℕ → ℝ) (n : ℕ) :
    prefixSum (fun i => x i - y i) n = prefixSum x n - prefixSum y n := by
  simp only [prefixSum, Finset.sum_sub_distrib]

theorem weightedAverage_sub (w x y : ℕ → ℝ) {n : ℕ}
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

theorem weightedAverage_add (w x y : ℕ → ℝ) {n : ℕ}
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

/-- Fixed scalar multiplication commutes with the repository's total weighted average,
including its zero-denominator branch. -/
theorem weightedAverage_const_mul (w x : ℕ → ℝ) (c : ℝ) (n : ℕ) :
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

theorem weightedAverage_mem_Icc {w x : ℕ → ℝ} {a b : ℝ} {n : ℕ}
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
theorem weightedAverage_mem_Icc_of_support {w x : ℕ → ℝ} {a b : ℝ} {n : ℕ}
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

theorem weightedBias_eq_market_sub_truth (w market truth : ℕ → ℝ) {n : ℕ}
    (hden : prefixSum w n ≠ 0) :
    weightedBias w market truth n =
      weightedAverage w market n - weightedAverage w truth n := by
  exact weightedAverage_sub w market truth hden

/-- Negating both the affine price and its determined value negates normalized bias,
including the harmless zero-denominator branch. -/
theorem weightedBias_neg (w market truth : ℕ → ℝ) (n : ℕ) :
    weightedBias w (fun i => -market i) (fun i => -truth i) n =
      -weightedBias w market truth n := by
  simp only [weightedBias, weightedAverage]
  split <;> rename_i hden
  · simp [hden]
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
theorem weightedBias_const_mul (w market truth : ℕ → ℝ) (c : ℝ) (n : ℕ) :
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
theorem weightedAverage_step_tendsto_zero
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

/-! ## Limit points -/

/-- “`x` is a limit point of the sequence `f`”, in the standard subsequential sense.
This is Mathlib's map-cluster-point notion along `atTop`; first countability makes it
equivalent to the existence of a strictly increasing convergent subsequence. -/
abbrev HasLimitPoint (f : ℕ → ℝ) (x : ℝ) : Prop :=
  MapClusterPt x atTop f

/-- A nonzero fixed scale does not change whether zero is a subsequential limit. -/
theorem hasLimitPoint_zero_of_const_mul
    {f : ℕ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : HasLimitPoint (fun n => c * f n) 0) : HasLimitPoint f 0 := by
  let g : ℝ → ℝ := fun x => x / c
  have hg : ContinuousAt g 0 := by fun_prop
  have hmapped := h.continuousAt_comp hg
  have hfun : (g ∘ fun n => c * f n) = f := by
    funext n
    exact mul_div_cancel_left₀ (f n) hc
  rw [hfun] at hmapped
  simpa only [g, zero_div] using hmapped

/-- A sequence has a limit point in `s`. -/
def HasLimitPointIn (f : ℕ → ℝ) (s : Set ℝ) : Prop :=
  ∃ x ∈ s, HasLimitPoint f x

theorem HasLimitPoint.exists_subseq {f : ℕ → ℝ} {x : ℝ}
    (h : HasLimitPoint f x) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (f ∘ ψ) atTop (𝓝 x) :=
  TopologicalSpace.FirstCountableTopology.tendsto_subseq h

theorem hasLimitPoint_of_convergesTo {f : ℕ → ℝ} {x : ℝ}
    (h : ConvergesTo f x) : HasLimitPoint f x :=
  h.mapClusterPt

theorem convergesTo_eq_of_hasLimitPoint {f : ℕ → ℝ} {x y : ℝ}
    (hy : ConvergesTo f y) (hx : HasLimitPoint f x) : x = y := by
  obtain ⟨ψ, hψ, hψx⟩ := hx.exists_subseq
  have hψy : Tendsto (f ∘ ψ) atTop (𝓝 y) :=
    hy.comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hψx hψy

/-- If a real sequence returns arbitrarily late to both sides of zero and its adjacent
jumps vanish, it has zero as a limit point.  This is the exact crossing argument used in
the paper after the two one-sided recurring-unbiasedness trader contradictions. -/
theorem hasLimitPoint_zero_of_two_sided_recurring (f : ℕ → ℝ)
    (hstep : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0))
    (hlower : ∀ ε > 0, ∃ᶠ n in atTop, -ε < f n)
    (hupper : ∀ ε > 0, ∃ᶠ n in atTop, f n < ε) :
    HasLimitPoint f 0 := by
  have habs : ∀ ε > 0, ∃ᶠ n in atTop, |f n| < ε := by
    intro ε hε
    have hstep' := (Metric.tendsto_atTop.1 hstep) (ε / 2) (by linarith)
    obtain ⟨Ns, hNs⟩ := hstep'
    refine frequently_atTop.2 (fun N => ?_)
    let N₀ := max N Ns
    by_cases hnear : |f N₀| < ε
    · exact ⟨N₀, le_max_left _ _, hnear⟩
    have hfar : ε ≤ |f N₀| := le_of_not_gt hnear
    rcases le_total (f N₀) 0 with hneg | hpos
    · have hNneg : f N₀ ≤ -ε := by
        rw [abs_of_nonpos hneg] at hfar
        linarith
      obtain ⟨m₁, hmN, hmval⟩ :=
        (frequently_atTop.1 (hlower (ε / 2) (by linarith))) N₀
      have hmval' : -ε / 2 < f m₁ := by linarith
      let existsCross : ∃ m : ℕ, N₀ ≤ m ∧ -ε / 2 < f m := ⟨m₁, hmN, hmval'⟩
      let m := Nat.find existsCross
      have hm := Nat.find_spec existsCross
      have hmgt : N₀ < m := by
        apply lt_of_le_of_ne hm.1
        intro heq
        rw [← heq] at hm
        linarith
      have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le N₀) hmgt
      have hprevN : N₀ ≤ m - 1 := by omega
      have hprev : f (m - 1) ≤ -ε / 2 := by
        by_contra hbad
        have hbad' : -ε / 2 < f (m - 1) := lt_of_not_ge hbad
        exact Nat.find_min existsCross (show m - 1 < m by omega)
          ⟨hprevN, hbad'⟩
      have hstepm : |f m - f (m - 1)| < ε / 2 := by
        have hs := hNs (m - 1) (by
          exact (le_max_right N Ns).trans hprevN)
        rw [Real.dist_eq, sub_zero] at hs
        have hsucc : m - 1 + 1 = m := by omega
        rw [hsucc] at hs
        exact hs
      refine ⟨m, (le_max_left N Ns).trans hm.1, ?_⟩
      rw [abs_lt]
      constructor
      · linarith [hm.2]
      · rw [abs_lt] at hstepm
        linarith
    · have hNpos : ε ≤ f N₀ := by
        rw [abs_of_nonneg hpos] at hfar
        exact hfar
      obtain ⟨m₁, hmN, hmval⟩ :=
        (frequently_atTop.1 (hupper (ε / 2) (by linarith))) N₀
      let existsCross : ∃ m : ℕ, N₀ ≤ m ∧ f m < ε / 2 := ⟨m₁, hmN, hmval⟩
      let m := Nat.find existsCross
      have hm := Nat.find_spec existsCross
      have hmgt : N₀ < m := by
        apply lt_of_le_of_ne hm.1
        intro heq
        rw [← heq] at hm
        linarith
      have hprevN : N₀ ≤ m - 1 := by omega
      have hprev : ε / 2 ≤ f (m - 1) := by
        by_contra hbad
        have hbad' : f (m - 1) < ε / 2 := lt_of_not_ge hbad
        exact Nat.find_min existsCross (show m - 1 < m by omega)
          ⟨hprevN, hbad'⟩
      have hstepm : |f m - f (m - 1)| < ε / 2 := by
        have hs := hNs (m - 1) (by
          exact (le_max_right N Ns).trans hprevN)
        rw [Real.dist_eq, sub_zero] at hs
        have hsucc : m - 1 + 1 = m := by omega
        rw [hsucc] at hs
        exact hs
      refine ⟨m, (le_max_left N Ns).trans hm.1, ?_⟩
      rw [abs_lt]
      constructor
      · rw [abs_lt] at hstepm
        linarith
      · linarith [hm.2]
  change MapClusterPt 0 atTop f
  rw [mapClusterPt_iff_frequently]
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  exact (habs ε hε).mono (fun n hn => hball (by
    simpa [Metric.mem_ball, Real.dist_eq] using hn))

/-! ## The analytic calibration transfer -/

/-- A zero bias limit point transfers to a truth-frequency limit point inside every
eventual interval containing the corresponding weighted market averages.  This is the
compactness/subsequence argument in the proof of `thm:simcal`, isolated from the choice
of calibration indicator.

The truth stream is allowed to be any `[0,1]` stream here; sentence truth values are the
important downstream instance. -/
theorem calibration_limitPoint_transfer
    (w market truth : ℕ → ℝ) (a b : ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (htruth : ∀ n, truth n ∈ Icc (0 : ℝ) 1)
    (hden : ∀ᶠ n in atTop, prefixSum w n ≠ 0)
    (hmarket : ∀ᶠ n in atTop,
      weightedAverage w market n ∈ Icc a b)
    (hbias : HasLimitPoint (weightedBias w market truth) 0) :
    HasLimitPointIn (weightedAverage w truth) (Icc a b) := by
  obtain ⟨ψ, hψmono, hψbias⟩ := hbias.exists_subseq
  have hdenψ : ∀ᶠ k in atTop, prefixSum w (ψ k) ≠ 0 :=
    hden.filter_mono hψmono.tendsto_atTop
  have htruthAvg : ∀ᶠ k in atTop,
      weightedAverage w truth (ψ k) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hdenψ] with k hk
    have hpos : 0 < prefixSum w (ψ k) := by
      have hw0 : 0 ≤ prefixSum w (ψ k) := by
        exact Finset.sum_nonneg (fun i _ => hw i)
      exact lt_of_le_of_ne hw0 (Ne.symm hk)
    exact weightedAverage_mem_Icc hw htruth hpos
  obtain ⟨x, hx01, hxcluster⟩ :=
    isCompact_Icc.exists_mapClusterPt_of_frequently
      (htruthAvg.frequently)
  obtain ⟨χ, hχmono, hχtruth⟩ :=
    TopologicalSpace.FirstCountableTopology.tendsto_subseq hxcluster
  let θ : ℕ → ℕ := ψ ∘ χ
  have hθmono : StrictMono θ := hψmono.comp hχmono
  have hbiasθ : Tendsto (weightedBias w market truth ∘ θ) atTop (𝓝 0) := by
    exact hψbias.comp hχmono.tendsto_atTop
  have htruthθ : Tendsto (weightedAverage w truth ∘ θ) atTop (𝓝 x) := by
    exact hχtruth
  have hdenθ : ∀ᶠ k in atTop, prefixSum w (θ k) ≠ 0 :=
    hden.filter_mono hθmono.tendsto_atTop
  have hmarketEq :
      (fun k => weightedAverage w market (θ k)) =ᶠ[atTop]
        (fun k => weightedAverage w truth (θ k) +
          weightedBias w market truth (θ k)) := by
    filter_upwards [hdenθ] with k hk
    rw [weightedBias_eq_market_sub_truth w market truth hk]
    ring
  have hmarketθ : Tendsto (fun k => weightedAverage w market (θ k)) atTop (𝓝 x) := by
    apply Tendsto.congr' hmarketEq.symm
    simpa only [Function.comp_apply, add_zero] using htruthθ.add hbiasθ
  have hmarketMem : ∀ᶠ k in atTop,
      weightedAverage w market (θ k) ∈ Icc a b :=
    hmarket.filter_mono hθmono.tendsto_atTop
  have hx : x ∈ Icc a b := isClosed_Icc.mem_of_tendsto hmarketθ hmarketMem
  refine ⟨x, hx, ?_⟩
  exact MapClusterPt.of_comp hθmono.tendsto_atTop htruthθ.mapClusterPt

/-- Convergent half of the same transfer: if weighted truth frequency converges, its
limit lies in the calibration interval. -/
theorem calibration_convergent_limit_mem
    (w market truth : ℕ → ℝ) (a b x : ℝ)
    (hden : ∀ᶠ n in atTop, prefixSum w n ≠ 0)
    (hmarket : ∀ᶠ n in atTop,
      weightedAverage w market n ∈ Icc a b)
    (hbias : HasLimitPoint (weightedBias w market truth) 0)
    (hconv : ConvergesTo (weightedAverage w truth) x) :
    x ∈ Icc a b := by
  obtain ⟨ψ, hψmono, hψbias⟩ := hbias.exists_subseq
  have htruthψ : Tendsto (weightedAverage w truth ∘ ψ) atTop (𝓝 x) :=
    hconv.comp hψmono.tendsto_atTop
  have hdenψ : ∀ᶠ k in atTop, prefixSum w (ψ k) ≠ 0 :=
    hden.filter_mono hψmono.tendsto_atTop
  have hmarketEq :
      (fun k => weightedAverage w market (ψ k)) =ᶠ[atTop]
        (fun k => weightedAverage w truth (ψ k) +
          weightedBias w market truth (ψ k)) := by
    filter_upwards [hdenψ] with k hk
    rw [weightedBias_eq_market_sub_truth w market truth hk]
    ring
  have hmarketψ : Tendsto (fun k => weightedAverage w market (ψ k)) atTop (𝓝 x) := by
    apply Tendsto.congr' hmarketEq.symm
    simpa only [Function.comp_apply, add_zero] using htruthψ.add hψbias
  exact isClosed_Icc.mem_of_tendsto hmarketψ
    (hmarket.filter_mono hψmono.tendsto_atTop)

/-- Exact analytic consumer for `thm:simcal`.  Once recurring unbiasedness supplies zero
as a limit point of the weighted bias for the paper's continuous calibration selector,
both clauses of recurring calibration follow: an interval-valued limit point always
exists, and every global limit belongs to the interval. -/
theorem simcal_of_recurring_unbiasedness
    (P : History) (φ : ℕ → Sentence) (truth : ℕ → ℝ)
    (a b : ℚ) (δ : ℕ → ℚ)
    (hδ : PolyPositiveWidths δ)
    (htruth : ∀ n, truth n = 0 ∨ truth n = 1)
    (hdiv : DivergentWeighting (calibrationIndicator φ a b δ) P)
    (hbias : HasLimitPoint
      (weightedBias
        (fun n => (calibrationIndicator φ a b δ n).denote P)
        (fun n => P n (φ n)) truth) 0) :
    HasLimitPointIn
        (weightedAverage
          (fun n => (calibrationIndicator φ a b δ n).denote P) truth)
        (Icc (a : ℝ) (b : ℝ)) ∧
      ∀ x, ConvergesTo
          (weightedAverage
            (fun n => (calibrationIndicator φ a b δ n).denote P) truth) x →
        x ∈ Icc (a : ℝ) (b : ℝ) := by
  let w : ℕ → ℝ := fun n => (calibrationIndicator φ a b δ n).denote P
  let market : ℕ → ℝ := fun n => P n (φ n)
  have hw0 : ∀ n, 0 ≤ w n := fun n => (hdiv.1 n).1
  have htruth01 : ∀ n, truth n ∈ Icc (0 : ℝ) 1 := by
    intro n
    rcases htruth n with h | h <;> simp [h]
  have hdenpos : ∀ᶠ n in atTop, 0 < prefixSum w n :=
    hdiv.eventually_prefixSum_pos
  have hden : ∀ᶠ n in atTop, prefixSum w n ≠ 0 :=
    hdenpos.mono (fun _ hn => ne_of_gt hn)
  have hmarket : ∀ᶠ n in atTop,
      weightedAverage w market n ∈ Icc (a : ℝ) (b : ℝ) := by
    filter_upwards [hdenpos] with n hn
    apply weightedAverage_mem_Icc_of_support hw0 (fun i hi => ?_) hn
    have hs := calibrationIndicator_pos_imp φ a b δ hδ.positive P i hi
    exact ⟨hs.1.le, hs.2.le⟩
  constructor
  · exact calibration_limitPoint_transfer w market truth (a : ℝ) (b : ℝ)
      hw0 htruth01 hden hmarket hbias
  · intro x hx
    exact calibration_convergent_limit_mem w market truth (a : ℝ) (b : ℝ) x
      hden hmarket hbias hx

/-! ## The weighted-bias forcing estimate -/

/-- Persistent negative normalized bias forces divergent weighted exposure whenever
the exposure dominates the pointwise truth-minus-market payoff.  This is the quantitative
heart of the recurring-unbiasedness trader: it converts a normalized statistical failure
into unbounded attempted affine risk without making any settlement assumption. -/
theorem weightedExposure_tendsto_atTop_of_eventually_negative_bias
    (w market truth exposure : ℕ → ℝ) (ε : ℝ)
    (hw0 : ∀ n, 0 ≤ w n)
    (hdom : ∀ n, truth n - market n ≤ exposure n)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hε : 0 < ε)
    (hbias : ∀ᶠ n in atTop, weightedBias w market truth n < -ε) :
    Tendsto (prefixSum (fun n => w n * exposure n)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  have hlarge : ∀ᶠ n in atTop, B / ε < prefixSum w n :=
    hdiv.eventually (eventually_gt_atTop (B / ε))
  have hpos : ∀ᶠ n in atTop, 0 < prefixSum w n :=
    hdiv.eventually (eventually_gt_atTop 0)
  apply eventually_atTop.1
  filter_upwards [hlarge, hpos, hbias] with n hnlarge hnpos hnbias
  have hweightedDom :
      prefixSum (fun i => w i * (truth i - market i)) n ≤
        prefixSum (fun i => w i * exposure i) n := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hdom i) (hw0 i)
  have hbiasDiv :
      prefixSum (fun i => w i * (market i - truth i)) n /
          prefixSum w n < -ε := by
    simpa [weightedBias, weightedAverage_eq_div (ne_of_gt hnpos)] using hnbias
  have hpayoff :
      ε * prefixSum w n <
        prefixSum (fun i => w i * (truth i - market i)) n := by
    have hneg :
        prefixSum (fun i => w i * (truth i - market i)) n =
          -prefixSum (fun i => w i * (market i - truth i)) n := by
      simp only [prefixSum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg]
    have := (div_lt_iff₀ hnpos).1 hbiasDiv
    nlinarith
  have hB : B < ε * prefixSum w n := by
    have := (div_lt_iff₀ hε).1 hnlarge
    nlinarith
  exact le_of_lt (hB.trans (hpayoff.trans_le hweightedDom))

/-! ## Determination via the deductive theory -/

/-- A concrete value stream witnesses that every member of an affine sequence is
determined via the completed theory.  Quantifying the value stream explicitly makes the
paper's notation `ThmValue(Aₙ)` usable without choice and exposes exactly what later
trader proofs may rely on. -/
def AffineCombination.DeterminedViaTheory
    (As : ℕ → AffineCombination) (P : History) (DP : DeductiveProcess)
    (truth : ℕ → ℝ) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (As n).value P v.payout = truth n

/-- Determination in every completed-theory world becomes uniform approximate
determination over all sufficiently late finite-stage plausible worlds.  This compactness
bridge is what turns a finite capped run of weighted affine purchases into an actual ROI
component; no settlement schedule is assumed. -/
theorem AffineCombination.DeterminedViaTheory.eventually_close
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth)
    (i : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      |(As i).value P v.payout - truth i| < ε := by
  have hlo := eventually_affineValue_gt_of_theory DP (As i) P (truth i - ε)
    (fun v hv => by rw [h i v hv]; linarith)
  have hhi := eventually_affineValue_gt_of_theory DP (As i).neg P (-truth i - ε)
    (fun v hv => by rw [AffineCombination.neg_value, h i v hv]; linarith)
  filter_upwards [hlo, hhi] with n hnlo hnhi
  intro v hv
  have hl := hnlo v hv
  have hu := hnhi v hv
  rw [AffineCombination.neg_value] at hu
  rw [abs_lt]
  constructor <;> linarith

/-! ### Exact finite-stage settlement

`eventually_close` gives only *approximate* finite-stage determination, but the paper's
patient selector (`app:prandaff`) needs **exact** settlement: a stage `m` at which every
plausible world already values `As i` at exactly `truth i`.  The gap closes because an
affine combination has *finitely many* terms, so its value depends on a world only through
finitely many `{0,1}` payouts and therefore ranges over a finite set.  Pick `δ` below the
smallest nonzero gap to `truth i` and approximate determination becomes exact. -/

open Classical in
/-- The payout-sum of a fixed term list ranges over a finite set of reals: each term
contributes one of two values (`0`, or its coefficient). -/
private theorem AffineCombination.exists_termsSum_finset (P : History) :
    ∀ terms : List (EF × Sentence),
      ∃ S : Finset ℝ, ∀ v : PCWorld,
        (terms.map (fun p => p.1.denote P * v.payout p.2)).sum ∈ S
  | [] => ⟨{0}, by intro v; simp⟩
  | (e, φ) :: rest => by
      obtain ⟨S, hS⟩ := AffineCombination.exists_termsSum_finset P rest
      refine ⟨Finset.image (fun p : ℝ × ℝ => p.1 + p.2)
        (({0, e.denote P} : Finset ℝ) ×ˢ S), ?_⟩
      intro v
      simp only [List.map_cons, List.sum_cons]
      refine Finset.mem_image.mpr ⟨(e.denote P * v.payout φ, _), ?_, rfl⟩
      refine Finset.mem_product.mpr ⟨?_, hS v⟩
      by_cases h : v.Holds φ <;> simp [PCWorld.payout, h]

/-- An affine combination's value ranges over a finite set of reals, uniformly in the
world.  Finiteness of `terms` is what makes this true — it is the fact that upgrades
approximate determination to exact settlement. -/
theorem AffineCombination.exists_valueSet (A : AffineCombination) (P : History) :
    ∃ S : Finset ℝ, ∀ v : PCWorld, A.value P v.payout ∈ S := by
  classical
  obtain ⟨S, hS⟩ := AffineCombination.exists_termsSum_finset P A.terms
  exact ⟨S.image (fun x => A.const.denote P + x), fun v => Finset.mem_image_of_mem _ (hS v)⟩

/-- **Exact finite-stage settlement.**  If the completed theory determines `As i`, then
some finite stage already pins its value to `truth i` in *every* plausible world.

This is the realizability core of `PatientSettlementClock.eventually_inactive`: it is what
guarantees the settlement checker eventually fires, so the clock can be sound (inactive ⇒
settled) and still eventually go inactive.  Purely semantic — no computability claim. -/
theorem AffineCombination.DeterminedViaTheory.exists_settled_stage
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth) (i : ℕ) :
    ∃ m, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      (As i).value P v.payout = truth i := by
  classical
  obtain ⟨S, hS⟩ := AffineCombination.exists_valueSet (As i) P
  by_cases hB : (S.filter (fun x => x ≠ truth i)).Nonempty
  · -- `δ` = smallest gap from an achievable wrong value to `truth i`; it is positive.
    have hδpos :
        0 < (S.filter (fun x => x ≠ truth i)).inf' hB (fun x => |x - truth i|) := by
      rw [Finset.lt_inf'_iff]
      intro x hx
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hx).2)
    obtain ⟨m, hm⟩ := (h.eventually_close i _ hδpos).exists
    refine ⟨m, fun v hv => ?_⟩
    by_contra hne
    exact absurd (hm v hv)
      (not_lt.mpr (Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hS v, hne⟩)))
  · -- No achievable value differs from `truth i`, so every stage settles — take `0`.
    refine ⟨0, fun v _ => ?_⟩
    by_contra hne
    exact hB ⟨_, Finset.mem_filter.mpr ⟨hS v, hne⟩⟩

/-- **The settlement test does not need to know `truth`.**  Provided the theory is
consistent, `As i` is settled at stage `m` — every world plausible at `m` values it at
exactly `truth i` — **iff** the worlds plausible at `m` merely *agree with each other*.

This is what makes the paper's `settled` machine (`app:prandaff`) implementable, and the
paper does not spell it out: a checker cannot compute `truth i` (it is defined by a limit
over the completed theory), but it *can* test agreement across the finitely many relevant
assignments.  The forward direction is trivial; the reverse leans on completed-theory
worlds being a nonempty subset of the stage-`m` plausible worlds, which is exactly where
consistency (`hworld`) is used. -/
theorem AffineCombination.DeterminedViaTheory.settled_iff_agree
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i m : ℕ) :
    (∀ v : PCWorld, v.ConsistentWith (DP.D m) → (As i).value P v.payout = truth i) ↔
      (∀ v w : PCWorld, v.ConsistentWith (DP.D m) → w.ConsistentWith (DP.D m) →
        (As i).value P v.payout = (As i).value P w.payout) := by
  constructor
  · intro hs v w hv hw
    rw [hs v hv, hs w hw]
  · intro hagree v hv
    obtain ⟨v₀, hv₀⟩ := exists_consistentWithTheory DP hworld
    rw [hagree v v₀ hv (hv₀ m), h i v₀ hv₀]

/-! ### Deciding settlement (`M7-PATIENT-CLOCK`, step 2b)

`settled_iff_agree` reduces settlement to *agreement* among plausible worlds and
`exists_settled_stage` guarantees agreement eventually holds.  What remains is to decide
agreement.  Two facts make it decidable, and both are exactly what the `ℝ`-valued
`History` hides:

* against a **rational** market every coefficient is rational (`EF.denoteRat`), so values
  compare exactly.  Over an arbitrary `History` this is equality of reals — undecidable,
  which is why no clock exists at that generality.
* an affine combination and a deductive stage each mention finitely many atoms, so world
  quantification collapses onto the finite type `BoolPCWorld.FiniteWorld`.

This mirrors the maturity checker (`unitMaturityCheckAtFuel`) below. -/

/-- Executable rational value of an affine combination under a rational price table and a
rational payout table. -/
def AffineCombination.valueRat (A : AffineCombination) (Q : ℕ → Sentence → ℚ)
    (w : Sentence → ℚ) : ℚ :=
  A.const.denoteRat Q + (A.terms.map (fun p => p.1.denoteRat Q * w p.2)).sum

private theorem AffineCombination.termsSum_eq_ratCast
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (wR : Sentence → ℝ) (wQ : Sentence → ℚ) (hw : ∀ φ, wR φ = (wQ φ : ℝ)) :
    ∀ terms : List (EF × Sentence),
      (terms.map (fun p => p.1.denote P * wR p.2)).sum
        = ((terms.map (fun p => p.1.denoteRat Q * wQ p.2)).sum : ℝ)
  | [] => by simp
  | p :: rest => by
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul]
      rw [EF.denote_eq_ratCast p.1 P Q hQ, hw p.2,
        AffineCombination.termsSum_eq_ratCast P Q hQ wR wQ hw rest]

/-- Rational affine value agrees exactly with the real semantics of an exact rational
market whenever the payout tables agree pointwise. -/
theorem AffineCombination.value_eq_ratCast (A : AffineCombination)
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (wR : Sentence → ℝ) (wQ : Sentence → ℚ) (hw : ∀ φ, wR φ = (wQ φ : ℝ)) :
    A.value P wR = (A.valueRat Q wQ : ℝ) := by
  unfold AffineCombination.value AffineCombination.valueRat
  rw [Rat.cast_add, EF.denote_eq_ratCast A.const P Q hQ,
    AffineCombination.termsSum_eq_ratCast P Q hQ wR wQ hw A.terms]

private theorem AffineCombination.termsSum_congr (Q : ℕ → Sentence → ℚ)
    (w w' : Sentence → ℚ) :
    ∀ terms : List (EF × Sentence), (∀ p ∈ terms, w p.2 = w' p.2) →
      (terms.map (fun p => p.1.denoteRat Q * w p.2)).sum
        = (terms.map (fun p => p.1.denoteRat Q * w' p.2)).sum
  | [], _ => rfl
  | p :: rest, h => by
      simp only [List.map_cons, List.sum_cons]
      rw [h p (by simp),
        AffineCombination.termsSum_congr Q w w' rest
          (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- The rational value only inspects the payouts of the combination's own sentences. -/
theorem AffineCombination.valueRat_congr (A : AffineCombination) (Q : ℕ → Sentence → ℚ)
    (w w' : Sentence → ℚ) (h : ∀ p ∈ A.terms, w p.2 = w' p.2) :
    A.valueRat Q w = A.valueRat Q w' := by
  unfold AffineCombination.valueRat
  rw [AffineCombination.termsSum_congr Q w w' A.terms h]

/-- Support bound covering every sentence the stage-`m` settlement test inspects: the
stage's own sentences and the combination's traded sentences.  Sums rather than maxima
keep the membership proofs elementary; only the upper bound matters. -/
def AffineCombination.settlementAtomLimit (A : AffineCombination)
    (stage : Finset Sentence) : ℕ :=
  stage.sum BoolPCWorld.atomBound +
    (A.terms.map (fun p => BoolPCWorld.atomBound p.2)).sum

theorem AffineCombination.settlementAtomLimit_stage_bounded (A : AffineCombination)
    (stage : Finset Sentence) : ∀ φ ∈ stage,
      BoolPCWorld.atomBound φ ≤ A.settlementAtomLimit stage := by
  intro φ hφ
  have hsingle : BoolPCWorld.atomBound φ ≤ stage.sum BoolPCWorld.atomBound :=
    Finset.single_le_sum (fun ψ _ => Nat.zero_le (BoolPCWorld.atomBound ψ)) hφ
  unfold AffineCombination.settlementAtomLimit
  omega

theorem AffineCombination.settlementAtomLimit_terms_bounded (A : AffineCombination)
    (stage : Finset Sentence) : ∀ p ∈ A.terms,
      BoolPCWorld.atomBound p.2 ≤ A.settlementAtomLimit stage := by
  intro p hp
  have hlocal : BoolPCWorld.atomBound p.2 ≤
      (A.terms.map (fun q => BoolPCWorld.atomBound q.2)).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  unfold AffineCombination.settlementAtomLimit
  omega

/-- Restricting a plausible world to the settlement support keeps it plausible. -/
private theorem AffineCombination.restrict_plausible (A : AffineCombination)
    (stage : Finset Sentence) (v : PCWorld) (hv : v.ConsistentWith stage) :
    ∀ φ ∈ stage, BoolPCWorld.eval
      (BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld v)
        (A.settlementAtomLimit stage)).toBoolPCWorld φ = true := by
  intro φ hφ
  rw [BoolPCWorld.eval_toBoolPCWorld_restrict _ _ φ
    (A.settlementAtomLimit_stage_bounded stage φ hφ)]
  have heval := BoolPCWorld.eval_eq_true_iff_holds (BoolPCWorld.ofPCWorld v) φ
  rw [BoolPCWorld.ofPCWorld_toPCWorld] at heval
  exact heval.mpr (hv φ hφ)

/-- **The settlement test is decidable, on a rational market.**  If every pair of
*finite* plausible worlds assigns `A` the same rational value, then every pair of genuine
plausible worlds assigns it the same real value.

The finite quantifier on the left is over `BoolPCWorld.FiniteWorld B = Fin B → Bool`, a
`Fintype` with decidable rational equality — so the left side is a `decide`-able Boolean
test.  This is the step that needs `P` rational, and it is the whole reason
`PatientSettlementClock` is realizable at `liaHistory` but not at an arbitrary
`History`. -/
theorem AffineCombination.agree_of_finiteWorlds_agree (A : AffineCombination)
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (stage : Finset Sentence)
    (h : ∀ u u' : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage),
      (∀ φ ∈ stage, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
      (∀ φ ∈ stage, BoolPCWorld.eval u'.toBoolPCWorld φ = true) →
        A.valueRat Q u.payoutRat = A.valueRat Q u'.payoutRat)
    (v w : PCWorld) (hv : v.ConsistentWith stage) (hw : w.ConsistentWith stage) :
    A.value P v.payout = A.value P w.payout := by
  classical
  have hrestrict (x : PCWorld) :
      A.valueRat Q
          (BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld x)
            (A.settlementAtomLimit stage)).payoutRat
        = A.valueRat Q x.payoutRat :=
    A.valueRat_congr Q _ _ (fun p hp =>
      BoolPCWorld.FiniteWorld.payoutRat_restrict_ofPCWorld x _ p.2
        (A.settlementAtomLimit_terms_bounded stage p hp))
  rw [A.value_eq_ratCast P Q hQ v.payout v.payoutRat (PCWorld.payout_eq_ratCast v),
    A.value_eq_ratCast P Q hQ w.payout w.payoutRat (PCWorld.payout_eq_ratCast w),
    ← hrestrict v, ← hrestrict w]
  exact congrArg _ (h _ _ (A.restrict_plausible stage v hv) (A.restrict_plausible stage w hw))

/-- The converse of `agree_of_finiteWorlds_agree`: genuine agreement restricts to finite
agreement.  Every plausible *finite* world extends to a genuine plausible `PCWorld` with
the same payouts, so the finite test cannot be stricter than the real condition.  This is
what makes the concrete test **complete**, not merely sound. -/
theorem AffineCombination.finiteWorlds_agree_of_agree (A : AffineCombination)
    (P : History) (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (stage : Finset Sentence)
    (h : ∀ v w : PCWorld, v.ConsistentWith stage → w.ConsistentWith stage →
      A.value P v.payout = A.value P w.payout) :
    ∀ u u' : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage),
      (∀ φ ∈ stage, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
      (∀ φ ∈ stage, BoolPCWorld.eval u'.toBoolPCWorld φ = true) →
        A.valueRat Q u.payoutRat = A.valueRat Q u'.payoutRat := by
  classical
  intro u u' hu hu'
  have hcons (x : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage))
      (hx : ∀ φ ∈ stage, BoolPCWorld.eval x.toBoolPCWorld φ = true) :
      x.toBoolPCWorld.toPCWorld.ConsistentWith stage :=
    fun φ hφ => (BoolPCWorld.eval_eq_true_iff_holds x.toBoolPCWorld φ).1 (hx φ hφ)
  have htransfer (x : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage)) :
      A.valueRat Q x.payoutRat = A.valueRat Q x.toBoolPCWorld.toPCWorld.payoutRat :=
    A.valueRat_congr Q _ _ (fun p _ => BoolPCWorld.FiniteWorld.payoutRat_eq_toPCWorld x p.2)
  have hreal := h _ _ (hcons u hu) (hcons u' hu')
  rw [A.value_eq_ratCast P Q hQ _ _ (PCWorld.payout_eq_ratCast _),
    A.value_eq_ratCast P Q hQ _ _ (PCWorld.payout_eq_ratCast _)] at hreal
  rw [htransfer u, htransfer u']
  exact_mod_cast hreal

/-- **The concrete settlement test.**  Decidable: a `Fintype` quantifier over
`BoolPCWorld.FiniteWorld B = Fin B → Bool` with exact rational equality.  This is the
object the paper's `settled` Turing machine (`app:prandaff`) decides — stated here so that
a checker's correctness is a *theorem* rather than an assumption. -/
def AffineCombination.SettlementTest (A : AffineCombination) (Q : ℕ → Sentence → ℚ)
    (stage : Finset Sentence) : Prop :=
  ∀ u u' : BoolPCWorld.FiniteWorld (A.settlementAtomLimit stage),
    (∀ φ ∈ stage, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
    (∀ φ ∈ stage, BoolPCWorld.eval u'.toBoolPCWorld φ = true) →
      A.valueRat Q u.payoutRat = A.valueRat Q u'.payoutRat

instance AffineCombination.SettlementTest.decidable (A : AffineCombination)
    (Q : ℕ → Sentence → ℚ) (stage : Finset Sentence) :
    Decidable (A.SettlementTest Q stage) := by
  unfold AffineCombination.SettlementTest
  infer_instance

/-- **The concrete test is exactly settlement.**  Both directions: sound (a passing test
implies every plausible world values `As i` at `truth i`) and complete (settlement implies
the test passes).  Consistency (`hworld`) and rationality of the market (`hQ`) are the two
hypotheses that carry it; neither is dispensable. -/
theorem AffineCombination.DeterminedViaTheory.settlementTest_iff_settled
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : AffineCombination.DeterminedViaTheory As P DP truth)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ d φ, P d φ = (Q d φ : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i j : ℕ) :
    (As i).SettlementTest Q (DP.D j) ↔
      ∀ v : PCWorld, v.ConsistentWith (DP.D j) → (As i).value P v.payout = truth i := by
  rw [hdet.settled_iff_agree hworld i j]
  exact ⟨fun htest v w hv hw =>
      (As i).agree_of_finiteWorlds_agree P Q hQ (DP.D j) htest v w hv hw,
    fun hagree => (As i).finiteWorlds_agree_of_agree P Q hQ (DP.D j) hagree⟩

theorem AffineCombination.DeterminedViaTheory.unique
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {x y : ℕ → ℝ}
    (hx : AffineCombination.DeterminedViaTheory As P DP x)
    (hy : AffineCombination.DeterminedViaTheory As P DP y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    x = y := by
  funext n
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  rw [← hx n v hv, hy n v hv]

/-- Completed-theory determination is closed under pointwise affine negation. -/
theorem AffineCombination.DeterminedViaTheory.neg
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ}
    (h : AffineCombination.DeterminedViaTheory As P DP truth) :
    AffineCombination.DeterminedViaTheory (fun n => (As n).neg) P DP
      (fun n => -truth n) := by
  intro n v hv
  rw [AffineCombination.neg_value, h n v hv]

/-! ## Capped weighted affine runs -/

namespace AffineCombination

/-- Canonical slowly varying run rate.  `scale` is chosen once from the alleged bias
gap; the `k+1` denominator makes the finite-prefix charge vanish uniformly in the family
index while remaining exactly rational and polynomially codeable. -/
def biasRunRate (scale k : ℕ) : ℚ :=
  1 / (((scale + 1) * (k + 1) : ℕ) : ℚ)

theorem biasRunRate_codes (scale : ℕ) : PolyRatCodes (biasRunRate scale) := by
  obtain ⟨cinv, hinv⟩ := encode_inv_nat_polyFueled
  obtain ⟨cmul, hmul⟩ := mulc_polyFueled (scale + 1)
  have harg := hmul.comp PolyFueled.id.succ_comp
  refine ⟨_, (hinv.comp harg).of_eq (fun n => ?_)⟩
  simp [biasRunRate, Nat.mul_comm]

theorem biasRunRate_pos (scale k : ℕ) : 0 < (biasRunRate scale k : ℝ) := by
  simp [biasRunRate]
  positivity

theorem biasRunRate_le_one (scale k : ℕ) : (biasRunRate scale k : ℝ) ≤ 1 := by
  simp only [biasRunRate, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  have hden : (1 : ℝ) ≤ (((scale + 1) * (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact (div_le_one (zero_lt_one.trans_le hden)).2 hden

theorem biasRunRate_mul_index_le (scale k : ℕ) :
    (biasRunRate scale k : ℝ) * k ≤ 1 / (scale + 1 : ℝ) := by
  simp only [biasRunRate, Rat.cast_div, Rat.cast_one,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hs : 0 < (scale : ℝ) + 1 := by positivity
  have hk : 0 < (k : ℝ) + 1 := by positivity
  push_cast
  field_simp [ne_of_gt hs, ne_of_gt hk]
  nlinarith

/-- Family-uniform version of the audited fractional-weight emitter.  The existing ROI
lemma emits one recurrence with a fixed attempted-weight stream; here the family index is
carried through every recurrence body, yielding one program for all pairs `⟨k,n⟩`. -/
theorem fractionalFamilyFeatureWeight_polySeg
    (occupancy : ℕ → ℕ → EF) (α : ℕ → ℕ → EF)
    (hα : PolySegStream (fun z => (α z.unpair.1 z.unpair.2).serialize))
    (hocc : PolySegStream (fun z =>
      (occupancy z.unpair.2 z.unpair.1).serialize)) :
    PolySegStream (fun z =>
      (ROIBudget.fractionalSharedFeatureWeight occupancy (α z.unpair.1)
        z.unpair.2).serialize) := by
  let family : ℕ → ℕ := fun z => z.unpair.1.unpair.1
  let day : ℕ → ℕ := fun z => z.unpair.1.unpair.2
  let component : ℕ → ℕ := fun z => z.unpair.2
  have hfamily := PolyFueled.left.comp PolyFueled.left
  have hday := PolyFueled.right.comp PolyFueled.left
  have hcomponent := PolyFueled.right
  let term : ℕ → EF := fun z =>
    EF.mul
      (EF.mul (EF.var (day z - 1 - component z))
        (α (family z) (component z)))
      (occupancy (component z) (day z))
  have hidxRaw := subc_polyFueled.comp
    ((predc_polyFueled.comp hday).pair hcomponent)
  have hidx := hidxRaw.of_eq (f' := fun z => day z - 1 - component z) (fun z => by
    simp [day, component, Nat.pred_eq_sub_one])
  have hvar : PolySegStream
      (fun z => (EF.var (day z - 1 - component z)).serialize) :=
    PolySegStream.serialize_var hidx
  have hαterm : PolySegStream
      (fun z => (α (family z) (component z)).serialize) :=
    PolySegStream.of_eq (hα.comp (hfamily.pair hcomponent)) (fun z => by
      simp [family, component])
  have hoccterm : PolySegStream
      (fun z => (occupancy (component z) (day z)).serialize) :=
    PolySegStream.of_eq (hocc.comp (hday.pair hcomponent)) (fun z => by
      simp [day, component])
  have hterm : PolySegStream (fun z => (term z).serialize) :=
    PolySegStream.serialize_mul (PolySegStream.serialize_mul hvar hαterm) hoccterm
  have hterms : PolySegStream (fun u =>
      (List.range u.unpair.2).flatMap
        (fun i => (term (Nat.pair u i)).serialize)) :=
    PolySegStream.concatVar hterm PolyFueled.right
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have haddTags : PolySegStream (fun u => List.replicate u.unpair.2 2) :=
    PolySegStream.repeatTag 2 PolyFueled.right
  have hsumRaw := (hterms.append hzero).append haddTags
  have hsum : PolySegStream (fun u =>
      (ROIBudget.sumFeatures (List.ofFn (fun i : Fin u.unpair.2 =>
        term (Nat.pair u i)))).serialize) := by
    refine PolySegStream.of_eq hsumRaw ?_
    intro u
    rw [ROIBudget.serialize_sumFeatures]
    simp only [List.length_ofFn]
    congr 2
    rw [← List.map_coe_finRange_eq_range]
    rw [List.flatMap_map]
    simp only [List.ofFn_eq_map, List.flatMap_map]
  have hone : PolySegStream (fun _ => (EF.const 1).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)
  have hnegone : PolySegStream (fun _ => (EF.const (-1)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
  have hbodyRaw := PolySegStream.serialize_add hone
    (PolySegStream.serialize_mul hnegone hsum)
  have hbody : PolySegStream (fun u =>
      (ROIBudget.fractionalWeightBody occupancy (α u.unpair.1) u.unpair.2).serialize) := by
    refine PolySegStream.of_eq hbodyRaw ?_
    intro u
    simp only [ROIBudget.fractionalWeightBody, term, family, day, component,
      Nat.unpair_pair]
  have hcanonical :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hbodies : PolySegStream (fun z =>
      (List.range (z.unpair.2 + 1)).flatMap (fun j =>
        (ROIBudget.fractionalWeightBody occupancy (α z.unpair.1) j).serialize)) := by
    refine PolySegStream.of_eq
      (PolySegStream.concatVar (hbody.comp hcanonical)
        PolyFueled.right.succ_comp) ?_
    intro z
    simp only [Nat.unpair_pair]
  have hvar0 : PolySegStream (fun _ => (EF.var 0).serialize) :=
    PolySegStream.serialize_var (PolyFueled.const 0)
  have htags : PolySegStream (fun z => List.replicate (z.unpair.2 + 1) 8) :=
    PolySegStream.repeatTag 8 PolyFueled.right.succ_comp
  refine PolySegStream.of_eq ((hbodies.append hvar0).append htags) ?_
  intro z
  rw [ROIBudget.fractionalSharedFeatureWeight,
    ROIBudget.fractionalSharedWeights_serialize]
  rw [List.range_eq_range']

/-- The attempted purchase weight for family member `k` on day `n`: zero before launch,
then `rateₖ · Wₙ`. -/
def biasRunAttempt (W : ℕ → EF) (rate : ℕ → ℚ) (k n : ℕ) : EF :=
  if k ≤ n then EF.mul (EF.const (rate k)) (W n) else EF.const 0

theorem biasRunAttempt_family_polySeg {W : ℕ → EF}
    (hW : PGenerableWeighting W) (rate : ℕ → ℚ) (hrate : PolyRatCodes rate) :
    PolySegStream (fun z =>
      (biasRunAttempt W rate z.unpair.1 z.unpair.2).serialize) := by
  have hrateSeg : PolySegStream (fun z => (EF.const (rate z.unpair.1)).serialize) :=
    (PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp hrate)).comp PolyFueled.left
  have hWSeg : PolySegStream (fun z => (W z.unpair.2).serialize) :=
    hW.polySeg.comp PolyFueled.right
  have hlive := PolySegStream.serialize_mul hrateSeg hWSeg
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have htest := subc_polyFueled.comp
    (PolyFueled.right.succ_comp.pair PolyFueled.left)
  refine PolySegStream.of_eq (PolySegStream.ifZero hzero hlive htest) ?_
  intro z
  simp only [Nat.unpair_pair]
  by_cases hkn : z.unpair.1 ≤ z.unpair.2
  · rw [if_neg (by omega)]
    simp [biasRunAttempt, hkn]
  · rw [if_pos (by omega)]
    simp [biasRunAttempt, hkn]

/-- Constant occupancy of a purchased affine bundle: because these run components buy and
hold, the tied-up fraction is its share magnitude on every later day. -/
def biasRunOccupancy (As : ℕ → AffineCombination) (i _n : ℕ) : EF :=
  (As i).magnitudeFeature

/-- Realized attempted purchase weight. -/
noncomputable def biasRunAttemptValue (W : ℕ → EF) (rate : ℕ → ℚ)
    (P : History) (k n : ℕ) : ℝ :=
  (biasRunAttempt W rate k n).denote P

/-- The capped purchase coefficient.  `fractionalWeight` is the existing audited
straight-line capital recurrence; multiplying it by the attempted weight gives the actual
number of copies bought on day `n`. -/
def biasRunCoefficient (As : ℕ → AffineCombination) (W : ℕ → EF)
    (rate : ℕ → ℚ) (k n : ℕ) : EF :=
  EF.mul
    (ROIBudget.fractionalSharedFeatureWeight (biasRunOccupancy As)
      (biasRunAttempt W rate k) n)
    (biasRunAttempt W rate k n)

theorem biasRunCoefficient_family_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (hrate : PolyRatCodes rate) :
    PolySegStream (fun z =>
      (biasRunCoefficient As W rate z.unpair.1 z.unpair.2).serialize) := by
  have hattempt := biasRunAttempt_family_polySeg hW rate hrate
  have hocc : PolySegStream (fun z =>
      (biasRunOccupancy As z.unpair.2 z.unpair.1).serialize) := by
    simpa [biasRunOccupancy] using h.magnitudeFeature_polySeg.comp PolyFueled.right
  have hweight := fractionalFamilyFeatureWeight_polySeg
    (biasRunOccupancy As) (biasRunAttempt W rate) hattempt hocc
  exact PolySegStream.serialize_mul hweight hattempt

/-- Semantic form of the actual capped purchase coefficient. -/
noncomputable def biasRunGamma (As : ℕ → AffineCombination) (W : ℕ → EF)
    (rate : ℕ → ℚ) (P : History) (k n : ℕ) : ℝ :=
  ROIBudget.fractionalWeight
      (fun i _d => (As i).magnitude P)
      (biasRunAttemptValue W rate P k) n *
    biasRunAttemptValue W rate P k n

theorem biasRunAttempt_rank_le {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) :
    (biasRunAttempt W rate k n).rank ≤ n := by
  by_cases hkn : k ≤ n
  · simp [biasRunAttempt, hkn, EF.rank, hW.rank_le n]
  · simp [biasRunAttempt, hkn]

theorem biasRunAttempt_closed {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) (ρ : List ℝ) (P : History) :
    (biasRunAttempt W rate k n).denoteWith ρ P =
      (biasRunAttempt W rate k n).denote P := by
  by_cases hkn : k ≤ n
  · simp only [biasRunAttempt, hkn, if_true, EF.denoteWith, EF.denote_mul,
      EF.denote_const, Pi.mul_apply]
    rw [hW.closed n ρ P]
  · simp [biasRunAttempt, hkn, EF.denote]

theorem biasRunOccupancy_rank_le {As : ℕ → AffineCombination}
    (h : PolySequence As) (i n : ℕ) (hin : i ≤ n) :
    (biasRunOccupancy As i n).rank ≤ n := by
  exact ((As i).magnitudeFeature_rank_le (h.terms_rank i)).trans hin

theorem biasRunOccupancy_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (i n : ℕ) (ρ : List ℝ) (P : History) :
    (biasRunOccupancy As i n).denoteWith ρ P =
      (biasRunOccupancy As i n).denote P :=
  h.magnitudeFeature_closed i ρ P

theorem biasRunCoefficient_rank_le {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) :
    (biasRunCoefficient As W rate k n).rank ≤ n := by
  simp only [biasRunCoefficient, EF.rank]
  apply Nat.max_le.mpr
  constructor
  · exact ROIBudget.fractionalSharedFeatureWeight_rank_le
      (biasRunOccupancy As) (biasRunAttempt W rate k)
      (fun i => biasRunAttempt_rank_le hW rate k i)
      (fun i d hid => biasRunOccupancy_rank_le h i d hid) n
  · exact biasRunAttempt_rank_le hW rate k n

theorem biasRunCoefficient_denote {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (P : History) (k n : ℕ) :
    (biasRunCoefficient As W rate k n).denote P =
      biasRunGamma As W rate P k n := by
  simp only [biasRunCoefficient, EF.denote_mul, Pi.mul_apply]
  rw [ROIBudget.fractionalSharedFeatureWeight_denote
      (biasRunOccupancy As) (biasRunAttempt W rate k)
      (fun i ρ V => biasRunAttempt_closed hW rate k i ρ V)
      (fun i d ρ V => biasRunOccupancy_closed h i d ρ V)]
  simp only [biasRunGamma, biasRunOccupancy, magnitudeFeature_denote]
  congr 2

theorem biasRunAttemptValue_nonneg
    {W : ℕ → EF} {P : History} (hW : DivergentWeighting W P)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ)) (k n : ℕ) :
    0 ≤ biasRunAttemptValue W rate P k n := by
  by_cases hkn : k ≤ n
  · simp [biasRunAttemptValue, biasRunAttempt, hkn, EF.denote_mul,
      mul_nonneg (hrate0 k) (hW.1 n).1]
  · simp [biasRunAttemptValue, biasRunAttempt, hkn, EF.denote]

theorem biasRunAttemptValue_le_one
    {W : ℕ → EF} {P : History} (hW : DivergentWeighting W P)
    (rate : ℕ → ℚ) (hrate1 : ∀ k, (rate k : ℝ) ≤ 1) (k n : ℕ) :
    biasRunAttemptValue W rate P k n ≤ 1 := by
  by_cases hkn : k ≤ n
  · simp only [biasRunAttemptValue, biasRunAttempt, hkn, if_true,
      EF.denote_mul, EF.denote_const, Pi.mul_apply]
    calc
      (rate k : ℝ) * (W n).denote P ≤ 1 * 1 :=
        mul_le_mul (hrate1 k) (hW.1 n).2 (hW.1 n).1 zero_le_one
      _ = 1 := one_mul _
  · simp [biasRunAttemptValue, biasRunAttempt, hkn, EF.denote]

/-- Launching at a finite family index and multiplying by a positive run rate preserves
divergence of weighted affine magnitude. -/
theorem biasRunAttemptedRisk_tendsto_atTop
    (As : ℕ → AffineCombination) {W : ℕ → EF} (rate : ℕ → ℚ)
    (P : History) (k : ℕ) (hrate : 0 < (rate k : ℝ))
    (hdiv : Tendsto
      (prefixSum (fun i => (W i).denote P * (As i).magnitude P)) atTop atTop) :
    Tendsto
      (prefixSum (fun i =>
        biasRunAttemptValue W rate P k i * (As i).magnitude P)) atTop atTop := by
  have hgate := prefixSum_gate_mul_tendsto_atTop
    (fun i => (W i).denote P * (As i).magnitude P)
    (rate k : ℝ) hrate hdiv k
  apply Tendsto.congr' _ hgate
  exact Eventually.of_forall (fun n => by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hki : k ≤ i
    · simp [biasRunAttemptValue, biasRunAttempt, hki, EF.denote_mul, mul_assoc]
    · simp [biasRunAttemptValue, biasRunAttempt, hki, EF.denote])

/-- The capped run never commits more than one unit of share magnitude through any day.
This is a non-vacuous capital bound derived from the actual fractional recurrence. -/
theorem biasRun_magnitudePrefix_le_one
    {As : ℕ → AffineCombination} {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1)
    (k n : ℕ) :
    prefixSum (fun i => biasRunGamma As W rate P k i * (As i).magnitude P) n ≤ 1 := by
  let occupancy : ℕ → ℕ → ℝ := fun i _d => (As i).magnitude P
  let α : ℕ → ℝ := biasRunAttemptValue W rate P k
  have hocc : ROIBudget.DecreasingOccupancy occupancy :=
    { nonneg := fun i _ => (As i).magnitude_nonneg P
      le_one := fun i _ => hmag i
      antitone := fun _ _ => le_rfl }
  have hbudget :=
    (ROIBudget.fractionalWeight_nonneg_and_postAllocation_le occupancy α hocc
      (fun i => biasRunAttemptValue_nonneg hW rate hrate0 k i)
      (fun i => biasRunAttemptValue_le_one hW rate hrate1 k i) n).2
  rw [prefixSum, ← Fin.sum_univ_eq_sum_range, Fin.sum_univ_castSucc]
  change
    (∑ i : Fin n,
        ROIBudget.fractionalWeight occupancy α i * α i * occupancy i n) +
      ROIBudget.fractionalWeight occupancy α n * α n * occupancy n n ≤ 1
  have hβ0 : 0 ≤ ROIBudget.fractionalWeight occupancy α n :=
    ROIBudget.fractionalWeight_nonneg occupancy α hocc
      (fun i => biasRunAttemptValue_nonneg hW rate hrate0 k i)
      (fun i => biasRunAttemptValue_le_one hW rate hrate1 k i) n
  have hα0 : 0 ≤ α n := biasRunAttemptValue_nonneg hW rate hrate0 k n
  have hcur :
      ROIBudget.fractionalWeight occupancy α n * α n * occupancy n n ≤
        ROIBudget.fractionalWeight occupancy α n * α n := by
    exact mul_le_of_le_one_right (mul_nonneg hβ0 hα0) (hmag n)
  calc
    (∑ i : Fin n,
        ROIBudget.fractionalWeight occupancy α i * α i * occupancy i n) +
          ROIBudget.fractionalWeight occupancy α n * α n * occupancy n n
        ≤ (∑ i : Fin n,
            ROIBudget.fractionalWeight occupancy α i * α i * occupancy i n) +
              ROIBudget.fractionalWeight occupancy α n * α n :=
          add_le_add (le_refl _) hcur
    _ ≤ 1 := by
      simpa [ROIBudget.fractionalOutstanding] using hbudget

theorem biasRunGamma_nonneg
    {As : ℕ → AffineCombination} {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1) (k n : ℕ) :
    0 ≤ biasRunGamma As W rate P k n := by
  let occupancy : ℕ → ℕ → ℝ := fun i _d => (As i).magnitude P
  let α : ℕ → ℝ := biasRunAttemptValue W rate P k
  have hocc : ROIBudget.DecreasingOccupancy occupancy :=
    { nonneg := fun i _ => (As i).magnitude_nonneg P
      le_one := fun i _ => hmag i
      antitone := fun _ _ => le_rfl }
  exact mul_nonneg
    (ROIBudget.fractionalWeight_nonneg occupancy α hocc
      (fun i => biasRunAttemptValue_nonneg hW rate hrate0 k i)
      (fun i => biasRunAttemptValue_le_one hW rate hrate1 k i) n)
    (biasRunAttemptValue_nonneg hW rate hrate0 k n)

theorem biasRunGamma_le_one
    {As : ℕ → AffineCombination} {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1) (k n : ℕ) :
    biasRunGamma As W rate P k n ≤ 1 := by
  let O : ℕ → ℕ → ℝ := fun i _d => (As i).magnitude P
  let α : ℕ → ℝ := biasRunAttemptValue W rate P k
  have hocc : ROIBudget.DecreasingOccupancy O :=
    { nonneg := fun i _ => (As i).magnitude_nonneg P
      le_one := fun i _ => hmag i
      antitone := fun _ _ => le_rfl }
  have hα0 : ∀ i, 0 ≤ α i :=
    fun i => biasRunAttemptValue_nonneg hW rate hrate0 k i
  have hα1 : ∀ i, α i ≤ 1 :=
    fun i => biasRunAttemptValue_le_one hW rate hrate1 k i
  have hβ0 := ROIBudget.fractionalWeight_nonneg O α hocc hα0 hα1 n
  have hβ1 := ROIBudget.fractionalWeight_le_one O α hocc hα0 hα1 n
  change ROIBudget.fractionalWeight O α n * α n ≤ 1
  calc
    ROIBudget.fractionalWeight O α n * α n ≤ 1 * 1 :=
      mul_le_mul hβ1 (hα1 n) (hα0 n) zero_le_one
    _ = 1 := one_mul _

theorem biasRun_magnitudePrefix_eq_one_sub_weight
    (As : ℕ → AffineCombination) (W : ℕ → EF) (rate : ℕ → ℚ)
    (P : History) (k n : ℕ) :
    prefixSum (fun i => biasRunGamma As W rate P k i * (As i).magnitude P) n =
      1 - ROIBudget.fractionalWeight
        (fun i _d => (As i).magnitude P)
        (biasRunAttemptValue W rate P k) (n + 1) := by
  rw [ROIBudget.fractionalWeight_eq, prefixSum,
    ← Fin.sum_univ_eq_sum_range, ROIBudget.fractionalOutstanding]
  ring_nf
  apply Finset.sum_congr rfl
  intro i _
  simp [biasRunGamma, mul_assoc]

theorem biasRun_weight_succ
    (As : ℕ → AffineCombination) (W : ℕ → EF) (rate : ℕ → ℚ)
    (P : History) (k n : ℕ) :
    ROIBudget.fractionalWeight
        (fun i _d => (As i).magnitude P)
        (biasRunAttemptValue W rate P k) (n + 1) =
      ROIBudget.fractionalWeight
          (fun i _d => (As i).magnitude P)
        (biasRunAttemptValue W rate P k) n *
        (1 - biasRunAttemptValue W rate P k n * (As n).magnitude P) := by
  let O : ℕ → ℕ → ℝ := fun i _d => (As i).magnitude P
  let α : ℕ → ℝ := biasRunAttemptValue W rate P k
  change ROIBudget.fractionalWeight O α (n + 1) =
    ROIBudget.fractionalWeight O α n * (1 - α n * O n n)
  have hrnext : ROIBudget.fractionalWeight O α (n + 1) =
      1 - ((∑ i : Fin n,
        ROIBudget.fractionalWeight O α i * α i * O i (n + 1)) +
          ROIBudget.fractionalWeight O α n * α n * O n (n + 1)) := by
    rw [ROIBudget.fractionalWeight_eq O α (n + 1),
      ROIBudget.fractionalOutstanding, Fin.sum_univ_castSucc]
    simp
  have hrn : ROIBudget.fractionalWeight O α n =
      1 - ∑ i : Fin n,
        ROIBudget.fractionalWeight O α i * α i * O i n := by
    rw [ROIBudget.fractionalWeight_eq O α n,
      ROIBudget.fractionalOutstanding]
  rw [hrnext]
  rw [hrn]
  dsimp only [O]
  ring

/-- Abel lower bound for the realized truth payoff of the fractional cap.  If every
uncapped cumulative surplus above rate `ρ` is at least `-δ`, then the capped run loses at
most `δ` relative to `ρ` times its realized share magnitude. -/
theorem biasRun_truthProfitPrefix_lower_of_surplus
    {As : ℕ → AffineCombination} {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1)
    (truth : ℕ → ℝ) (ρ δ : ℝ) (k : ℕ)
    (hsurplus : ∀ n,
      -δ ≤ prefixSum (fun i =>
        biasRunAttemptValue W rate P k i *
          ((truth i - (As i).price P i) - ρ * (As i).magnitude P)) n)
    (n : ℕ) :
    ρ * prefixSum (fun i =>
        biasRunGamma As W rate P k i * (As i).magnitude P) n - δ ≤
      prefixSum (fun i =>
        biasRunGamma As W rate P k i *
          (truth i - (As i).price P i)) n := by
  let O : ℕ → ℕ → ℝ := fun i _d => (As i).magnitude P
  let α : ℕ → ℝ := biasRunAttemptValue W rate P k
  let β : ℕ → ℝ := ROIBudget.fractionalWeight O α
  let y : ℕ → ℝ := fun i => α i *
    ((truth i - (As i).price P i) - ρ * (As i).magnitude P)
  have hocc : ROIBudget.DecreasingOccupancy O :=
    { nonneg := fun i _ => (As i).magnitude_nonneg P
      le_one := fun i _ => hmag i
      antitone := fun _ _ => le_rfl }
  have hα0 : ∀ i, 0 ≤ α i :=
    fun i => biasRunAttemptValue_nonneg hW rate hrate0 k i
  have hα1 : ∀ i, α i ≤ 1 :=
    fun i => biasRunAttemptValue_le_one hW rate hrate1 k i
  have hβ0 : ∀ i, 0 ≤ β i :=
    ROIBudget.fractionalWeight_nonneg O α hocc hα0 hα1
  have hβanti : Antitone β := antitone_nat_of_succ_le (fun i => by
    change ROIBudget.fractionalWeight O α (i + 1) ≤
      ROIBudget.fractionalWeight O α i
    rw [show ROIBudget.fractionalWeight O α (i + 1) =
        ROIBudget.fractionalWeight O α i *
          (1 - α i * O i i) from biasRun_weight_succ As W rate P k i]
    exact mul_le_of_le_one_right (hβ0 i)
      (by have := mul_nonneg (hα0 i) (hocc.nonneg i i); linarith))
  have hy : ∀ i, -δ ≤ prefixSum y i := by
    intro i
    simpa only [y, α] using hsurplus i
  have hab := prefixSum_mul_lower_of_prefixSum_lower β y δ hβ0 hβanti hy n
  have hβzero : β 0 = 1 := by
    change ROIBudget.fractionalWeight O α 0 = 1
    rw [ROIBudget.fractionalWeight]
    simp
  rw [hβzero, mul_one] at hab
  have hid : prefixSum (fun i => β i * y i) n =
      prefixSum (fun i =>
        biasRunGamma As W rate P k i *
          (truth i - (As i).price P i)) n -
      ρ * prefixSum (fun i =>
        biasRunGamma As W rate P k i * (As i).magnitude P) n := by
    simp only [prefixSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [biasRunGamma, β, y, α, O]
    ring
  rw [hid] at hab
  linarith

/-- If the uncapped attempted risk has divergent total mass, the audited fractional cap
uses its entire unit budget: actual run magnitude tends to one.  The proof is elementary:
the remaining budget is antitone; if it stayed above `ε`, actual allocation would dominate
`ε` times a divergent attempted-risk sum, contradicting the unit cap. -/
theorem biasRun_magnitudePrefix_tendsto_one
    {As : ℕ → AffineCombination} {W : ℕ → EF} {P : History}
    (hW : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1) (k : ℕ)
    (hrisk : Tendsto
      (prefixSum (fun i =>
        biasRunAttemptValue W rate P k i * (As i).magnitude P)) atTop atTop) :
    Tendsto
      (prefixSum (fun i =>
        biasRunGamma As W rate P k i * (As i).magnitude P)) atTop (𝓝 1) := by
  let O : ℕ → ℕ → ℝ := fun i _d => (As i).magnitude P
  let α : ℕ → ℝ := biasRunAttemptValue W rate P k
  let r : ℕ → ℝ := ROIBudget.fractionalWeight O α
  let q : ℕ → ℝ := fun i => α i * O i i
  have hocc : ROIBudget.DecreasingOccupancy O :=
    { nonneg := fun i _ => (As i).magnitude_nonneg P
      le_one := fun i _ => hmag i
      antitone := fun _ _ => le_rfl }
  have hα0 : ∀ i, 0 ≤ α i :=
    fun i => biasRunAttemptValue_nonneg hW rate hrate0 k i
  have hα1 : ∀ i, α i ≤ 1 :=
    fun i => biasRunAttemptValue_le_one hW rate hrate1 k i
  have hr0 : ∀ i, 0 ≤ r i :=
    ROIBudget.fractionalWeight_nonneg O α hocc hα0 hα1
  have hq0 : ∀ i, 0 ≤ q i := fun i =>
    mul_nonneg (hα0 i) ((As i).magnitude_nonneg P)
  have hsucc : ∀ n, r (n + 1) = r n * (1 - q n) := by
    intro n
    exact biasRun_weight_succ As W rate P k n
  have hrAnti : Antitone r := antitone_nat_of_succ_le (fun n => by
    rw [hsucc n]
    exact mul_le_of_le_one_right (hr0 n) (by dsimp only [q]; linarith [hq0 n]))
  have hrzero : Tendsto r atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev : ∀ᶠ n in atTop, 1 / ε < prefixSum q n := by
      have hraw := hrisk.eventually (eventually_gt_atTop (1 / ε))
      simpa [q, α, O] using hraw
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have hqN : 1 / ε < prefixSum q N := hN N le_rfl
    have hrN : r N < ε := by
      by_contra hnot
      have hεr : ε ≤ r N := le_of_not_gt hnot
      have hlower : ε * prefixSum q N ≤
          prefixSum (fun i =>
            biasRunGamma As W rate P k i * (As i).magnitude P) N := by
        simp only [prefixSum, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hri : ε ≤ r i := hεr.trans (hrAnti hiN)
        simp only [biasRunGamma]
        calc
          ε * q i ≤ r i * q i := mul_le_mul_of_nonneg_right hri (hq0 i)
          _ = ROIBudget.fractionalWeight
                (fun j _d => (As j).magnitude P)
                (biasRunAttemptValue W rate P k) i *
              biasRunAttemptValue W rate P k i * (As i).magnitude P := by
                simp only [r, q, α, O]
                ring
      have hu := biasRun_magnitudePrefix_le_one hW hmag rate hrate0 hrate1 k N
      have hone : 1 < ε * prefixSum q N := by
        have hεne : ε ≠ 0 := ne_of_gt hε
        calc
          1 = ε * (1 / ε) := by field_simp
          _ < ε * prefixSum q N := mul_lt_mul_of_pos_left hqN hε
      linarith
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hr0 n)]
    exact (hrAnti hn).trans_lt hrN
  have hrshift : Tendsto (fun n => r (n + 1)) atTop (𝓝 0) :=
    hrzero.comp (tendsto_add_atTop_nat 1)
  have honeSub : Tendsto (fun n => 1 - r (n + 1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hrshift
  apply Tendsto.congr' _ honeSub
  exact Eventually.of_forall (fun n => by
    change 1 - ROIBudget.fractionalWeight
        (fun i _d => (As i).magnitude P)
        (biasRunAttemptValue W rate P k) (n + 1) = _
    exact (biasRun_magnitudePrefix_eq_one_sub_weight As W rate P k n).symm)

/-- Family member `k` buys its capped run of affine bundles and makes no syntactic trade
before day `k` (the latter is required by the uniform-emulation interface). -/
def biasRunTrader {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k : ℕ) : Trader where
  strat n := if hkn : k ≤ n then
      ((As n).scale (biasRunCoefficient As W rate k n)).buy n
        ((As n).scale_terms_rank_le _
          (biasRunCoefficient_rank_le h hW rate k n) (h.terms_rank n))
    else ⟨[], by simp⟩

def biasRunTradeCount {As : ℕ → AffineCombination}
    (h : PolySequence As) (z : ℕ) : ℕ :=
  if z.unpair.1 ≤ z.unpair.2 then h.termCount z.unpair.2 else 0

def biasRunTradeCoefficient {As : ℕ → AffineCombination}
    (h : PolySequence As) (W : ℕ → EF) (rate : ℕ → ℚ) (z : ℕ) : EF :=
  EF.mul
    (biasRunCoefficient As W rate z.unpair.1.unpair.1 z.unpair.1.unpair.2)
    (h.coefficient (Nat.pair z.unpair.1.unpair.2 z.unpair.2))

def biasRunTradeSentence {As : ℕ → AffineCombination}
    (h : PolySequence As) (z : ℕ) : Sentence :=
  h.sentence (Nat.pair z.unpair.1.unpair.2 z.unpair.2)

theorem biasRunTradeCount_poly {As : ℕ → AffineCombination}
    (h : PolySequence As) : ∃ c, PolyFueled c (biasRunTradeCount h) := by
  obtain ⟨ccount, hcount⟩ := h.termCount_poly
  have htest := subc_polyFueled.comp
    (PolyFueled.right.succ_comp.pair PolyFueled.left)
  have hraw := ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair (hcount.comp PolyFueled.right)).pair htest)
  refine ⟨_, hraw.of_eq (fun z => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn, biasRunTradeCount]
  by_cases hkn : z.unpair.1 ≤ z.unpair.2
  · rw [if_pos hkn, if_neg (by omega)]
  · rw [if_neg hkn, if_pos (by omega)]

theorem biasRunTradeCoefficient_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (hrate : PolyRatCodes rate) :
    PolySegStream (fun z =>
      (biasRunTradeCoefficient h W rate z).serialize) := by
  have hk := PolyFueled.left.comp PolyFueled.left
  have hn := PolyFueled.right.comp PolyFueled.left
  have hj := PolyFueled.right
  have hrun : PolySegStream (fun z =>
      (biasRunCoefficient As W rate z.unpair.1.unpair.1
        z.unpair.1.unpair.2).serialize) := by
    simpa only [Nat.unpair_pair] using
      (biasRunCoefficient_family_polySeg h hW rate hrate).comp (hk.pair hn)
  have hbase : PolySegStream (fun z =>
      (h.coefficient (Nat.pair z.unpair.1.unpair.2 z.unpair.2)).serialize) := by
    simpa only [Nat.unpair_pair] using h.coefficient_poly.comp (hn.pair hj)
  simpa only [biasRunTradeCoefficient] using
    PolySegStream.serialize_mul hrun hbase

theorem biasRunTradeSentence_poly {As : ℕ → AffineCombination}
    (h : PolySequence As) :
    ∃ c, PolyFueled c (fun z => Encodable.encode (biasRunTradeSentence h z)) := by
  obtain ⟨cs, hs⟩ := h.sentence_poly
  have hn := PolyFueled.right.comp PolyFueled.left
  have hj := PolyFueled.right
  exact ⟨_, (hs.comp (hn.pair hj)).of_eq (fun _ => rfl)⟩

theorem biasRunTrader_trades_eq {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) :
    ((biasRunTrader h hW rate k).strat n).trades =
      (List.range (biasRunTradeCount h (Nat.pair k n))).map (fun j =>
        let z := Nat.pair (Nat.pair k n) j
        (biasRunTradeCoefficient h W rate z, biasRunTradeSentence h z)) := by
  by_cases hkn : k ≤ n
  · simp only [biasRunTrader, hkn, dif_pos, AffineCombination.buy_trades,
      AffineCombination.scale, h.terms_eq]
    simp [biasRunTradeCount, hkn, biasRunTradeCoefficient,
      biasRunTradeSentence, List.map_map, Function.comp_apply]
  · simp [biasRunTrader, hkn, biasRunTradeCount]

/-- The complete capped-run family has one uniform polynomial token emitter. -/
noncomputable def biasRunTrader_polyTrade {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (hrate : PolyRatCodes rate) :
    PolyTradeEmulatable (biasRunTrader h hW rate) := by
  let ccount := Classical.choose (biasRunTradeCount_poly h)
  have hcount := Classical.choose_spec (biasRunTradeCount_poly h)
  let csentence := Classical.choose (biasRunTradeSentence_poly h)
  have hsentence := Classical.choose_spec (biasRunTradeSentence_poly h)
  have hcoeff := biasRunTradeCoefficient_polySeg h hW rate hrate
  have htag : PolySegStream (fun _ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  have hsentenceSeg : PolySegStream (fun z =>
      [Encodable.encode (biasRunTradeSentence h z)]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok hsentence)
  have hone : PolySegStream (fun z => serializeTrades
      [(biasRunTradeCoefficient h W rate z, biasRunTradeSentence h z)]) := by
    refine PolySegStream.of_eq ((hcoeff.append htag).append hsentenceSeg) ?_
    intro z
    simp [serializeTrades, List.append_assoc]
  have hserialized : PolySegStream (fun z => serializeTrades
      (((biasRunTrader h hW rate) z.unpair.1).strat z.unpair.2).trades) := by
    refine PolySegStream.of_eq (PolySegStream.concatVar hone hcount) ?_
    intro z
    rw [biasRunTrader_trades_eq]
    rw [serializeTrades_map_singleton]
    simp only [Nat.pair_unpair]
  have hzero : ∀ k n, n < k →
      (((biasRunTrader h hW rate) k).strat n).trades = [] := by
    intro k n hnk
    simp [biasRunTrader, Nat.not_le.mpr hnk]
  refine
    { emulatable := EfficientlyEmulatable.of_polySeg hzero hserialized
      tradeCount := biasRunTradeCount h
      coefficient := biasRunTradeCoefficient h W rate
      sentence := biasRunTradeSentence h
      tradeCount_poly := ⟨ccount, hcount⟩
      coefficient_poly := hcoeff
      sentence_poly := ⟨csentence, hsentence⟩
      trades_eq := biasRunTrader_trades_eq h hW rate }

@[simp] theorem biasRunTrader_before {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) (hnk : n < k) :
    ((biasRunTrader h hW rate k).strat n).trades = [] := by
  simp [biasRunTrader, Nat.not_le.mpr hnk]

theorem biasRunTrader_value {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (P : History) (w : Valuation)
    (k n : ℕ) (hkn : k ≤ n) :
    ((biasRunTrader h hW rate k).strat n).value P w =
      biasRunGamma As W rate P k n *
        ((As n).value P w - (As n).price P n) := by
  simp only [biasRunTrader, dif_pos hkn]
  rw [AffineCombination.buy_value,
    AffineCombination.scale_value, AffineCombination.scale_price,
    biasRunCoefficient_denote h hW]
  ring

theorem biasRunTrader_netWorth {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    (rate : ℕ → ℚ) (P : History) (v : PCWorld) (k n : ℕ) :
    (biasRunTrader h hWgen rate k).netWorth P v n =
      prefixSum (fun i => biasRunGamma As W rate P k i *
        ((As i).value P v.payout - (As i).price P i)) n := by
  rw [Trader.netWorth]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hki : k ≤ i
  · exact biasRunTrader_value h hWgen rate P v.payout k i hki
  · have hgamma : biasRunGamma As W rate P k i = 0 := by
      rw [biasRunGamma]
      have ha : biasRunAttemptValue W rate P k i = 0 := by
        simp [biasRunAttemptValue, biasRunAttempt, hki, EF.denote]
      rw [ha, mul_zero]
    simp [biasRunTrader, hki, Strategy.value, hgamma]

theorem biasRunTrader_dayMagnitude {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1) (k n : ℕ) :
    ((biasRunTrader h hWgen rate k).strat n).magnitude P =
      biasRunGamma As W rate P k n * (As n).magnitude P := by
  by_cases hkn : k ≤ n
  · simp only [biasRunTrader, dif_pos hkn]
    rw [AffineCombination.buy_magnitude,
      AffineCombination.scale_magnitude, biasRunCoefficient_denote h hWgen,
      abs_of_nonneg (biasRunGamma_nonneg hWdiv hmag rate hrate0 hrate1 k n)]
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    simp only [biasRunTrader, dif_neg hkn]
    have hzero : biasRunGamma As W rate P k n = 0 := by
      rw [biasRunGamma]
      have ha : biasRunAttemptValue W rate P k n = 0 := by
        simp [biasRunAttemptValue, biasRunAttempt, hkn, EF.denote]
      rw [ha, mul_zero]
    simp [Strategy.magnitude, hzero]

/-- Every capped run has genuinely summable day magnitudes and total magnitude at most
one.  This rules out the `tsum = 0` non-summability loophole before ROI is discussed. -/
theorem biasRunTrader_summable_and_magnitude_le_one
    {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1) (k : ℕ) :
    Summable (fun n => ((biasRunTrader h hWgen rate k).strat n).magnitude P) ∧
      (biasRunTrader h hWgen rate k).magnitude P ≤ 1 := by
  have hterm0 : ∀ n,
      0 ≤ ((biasRunTrader h hWgen rate k).strat n).magnitude P :=
    fun n => Strategy.magnitude_nonneg _ P
  have hpartial : ∀ N,
      ∑ n ∈ Finset.range N,
        ((biasRunTrader h hWgen rate k).strat n).magnitude P ≤ 1 := by
    intro N
    cases N with
    | zero => simp
    | succ n =>
        rw [show ∑ i ∈ Finset.range (n + 1),
            ((biasRunTrader h hWgen rate k).strat i).magnitude P =
            prefixSum (fun i =>
              biasRunGamma As W rate P k i * (As i).magnitude P) n by
          apply Finset.sum_congr rfl
          intro i _
          exact biasRunTrader_dayMagnitude h hWgen hWdiv hmag rate
            hrate0 hrate1 k i]
        exact biasRun_magnitudePrefix_le_one hWdiv hmag rate hrate0 hrate1 k n
  have hsummable := summable_of_sum_range_le hterm0 hpartial
  refine ⟨hsummable, ?_⟩
  exact Real.tsum_le_of_sum_range_le hterm0 hpartial

theorem biasRunTrader_magnitude_eq_one_of_attemptedRisk
    {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1) (k : ℕ)
    (hrisk : Tendsto
      (prefixSum (fun i =>
        biasRunAttemptValue W rate P k i * (As i).magnitude P)) atTop atTop) :
    (biasRunTrader h hWgen rate k).magnitude P = 1 := by
  have hsummable :=
    (biasRunTrader_summable_and_magnitude_le_one h hWgen hWdiv hmag rate
      hrate0 hrate1 k).1
  have hpref := biasRun_magnitudePrefix_tendsto_one hWdiv hmag rate
    hrate0 hrate1 k hrisk
  have hprefTrader : Tendsto
      (prefixSum (fun n => ((biasRunTrader h hWgen rate k).strat n).magnitude P))
      atTop (𝓝 1) := by
    apply Tendsto.congr' _ hpref
    exact Eventually.of_forall (fun n => by
      apply Finset.sum_congr rfl
      intro i _
      exact (biasRunTrader_dayMagnitude h hWgen hWdiv hmag rate
        hrate0 hrate1 k i).symm)
  have htoMagnitude : Tendsto
      (prefixSum (fun n => ((biasRunTrader h hWgen rate k).strat n).magnitude P))
      atTop (𝓝 ((biasRunTrader h hWgen rate k).magnitude P)) := by
    have hraw := hsummable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    simpa [prefixSum, Trader.magnitude] using hraw
  exact tendsto_nhds_unique htoMagnitude hprefTrader

/-- A determined affine value differs from its diagonal market price by at most its share
magnitude.  The completed-theory world needed for this comparison is obtained by the
compactness theorem, not assumed separately for each member. -/
theorem DeterminedViaTheory.abs_truth_sub_price_le_magnitude
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    |truth n - (As n).price P n| ≤ (As n).magnitude P := by
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  rw [← hdet n v hv]
  exact (As n).abs_value_sub_price_le_magnitude P v.payout n
    (hpoly.terms_rank n) (fun φ => by
      by_cases hφ : v.Holds φ
      · exact Or.inr (by simp [PCWorld.payout, hφ])
      · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP n)

/-- A full-risk capped run with an Abel-prefix surplus has genuine ROI.  Compactness is
used only for the finitely many large early positions; the summable risk tail is controlled
uniformly by magnitude.  Thus no effective settlement oracle is hidden in this semantic
step. -/
theorem DeterminedViaTheory.biasRunTrader_hasROI_of_surplus
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1)
    (ρ δ : ℝ) (hρ0 : 0 ≤ ρ) (k : ℕ)
    (hsurplus : ∀ n,
      -δ ≤ prefixSum (fun i =>
        biasRunAttemptValue W rate P k i *
          ((truth i - (As i).price P i) - ρ * (As i).magnitude P)) n)
    (hrisk : Tendsto
      (prefixSum (fun i =>
        biasRunAttemptValue W rate P k i * (As i).magnitude P)) atTop atTop) :
    HasROI (biasRunTrader hpoly hWgen rate k) P DP (ρ - δ) := by
  let Tr := biasRunTrader hpoly hWgen rate k
  have hsummable :=
    (biasRunTrader_summable_and_magnitude_le_one hpoly hWgen hWdiv hmag rate
      hrate0 hrate1 k).1
  have hmagEq : Tr.magnitude P = 1 :=
    biasRunTrader_magnitude_eq_one_of_attemptedRisk hpoly hWgen hWdiv hmag
      rate hrate0 hrate1 k hrisk
  have hRiskT := biasRun_magnitudePrefix_tendsto_one hWdiv hmag rate
    hrate0 hrate1 k hrisk
  refine ⟨hsummable, fun η hη => ?_⟩
  let a : ℝ := η / (8 * (ρ + 1))
  have hρone : 0 < ρ + 1 := by linarith
  have ha : 0 < a := div_pos hη (mul_pos (by norm_num) hρone)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hRiskT a ha
  have hRiskM := hM M le_rfl
  rw [Real.dist_eq] at hRiskM
  have hRiskMlow : 1 - a < prefixSum (fun i =>
      biasRunGamma As W rate P k i * (As i).magnitude P) M := by
    rw [abs_lt] at hRiskM
    linarith
  let e : ℝ := η / (8 * (M + 1))
  have he : 0 < e := div_pos hη (by positivity)
  have hearly : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (M + 1),
      ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
        |(As i).value P v.payout - truth i| < e := by
    rw [Finset.eventually_all]
    intro i hi
    exact hdet.eventually_close i e he
  obtain ⟨Ne, hNe⟩ := eventually_atTop.1 hearly
  refine ⟨max M Ne, fun n hn v hv => ?_⟩
  have hnM : M ≤ n := (le_max_left M Ne).trans hn
  have hnNe : Ne ≤ n := (le_max_right M Ne).trans hn
  have hRiskN := hM n hnM
  rw [Real.dist_eq, abs_lt] at hRiskN
  have htruthLower := biasRun_truthProfitPrefix_lower_of_surplus hWdiv hmag
    rate hrate0 hrate1 truth ρ δ k hsurplus n
  have htruth : ρ - δ - η / 8 ≤ prefixSum (fun i =>
      biasRunGamma As W rate P k i *
        (truth i - (As i).price P i)) n := by
    have hrhoa : ρ * a ≤ η / 8 := by
      dsimp only [a]
      have hfrac : ρ / (ρ + 1) ≤ 1 := (div_le_one hρone).2 (by linarith)
      calc
        ρ * (η / (8 * (ρ + 1))) = (η / 8) * (ρ / (ρ + 1)) := by
          field_simp [ne_of_gt hρone]
        _ ≤ (η / 8) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = η / 8 := mul_one _
    have hriskMul := mul_le_mul_of_nonneg_left
      (show 1 - a ≤ prefixSum (fun i =>
        biasRunGamma As W rate P k i * (As i).magnitude P) n by linarith [hRiskN.1]) hρ0
    linarith
  have hgamma0 : ∀ i, 0 ≤ biasRunGamma As W rate P k i :=
    biasRunGamma_nonneg hWdiv hmag rate hrate0 hrate1 k
  have hgamma1 : ∀ i, biasRunGamma As W rate P k i ≤ 1 :=
    biasRunGamma_le_one hWdiv hmag rate hrate0 hrate1 k
  have hearlySum : -(η / 8) ≤
      ∑ i ∈ Finset.range (M + 1),
        biasRunGamma As W rate P k i *
          ((As i).value P v.payout - truth i) := by
    calc
      -(η / 8) = ∑ _i ∈ Finset.range (M + 1), -e := by
        simp [e]
        field_simp
      _ ≤ ∑ i ∈ Finset.range (M + 1),
          biasRunGamma As W rate P k i *
            ((As i).value P v.payout - truth i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hclose := hNe n hnNe i hi v hv
        rw [abs_lt] at hclose
        have hge := mul_nonneg (hgamma0 i)
          (show 0 ≤ ((As i).value P v.payout - truth i) + e by linarith)
        have hge' := mul_nonneg (show 0 ≤ 1 - biasRunGamma As W rate P k i by
            linarith [hgamma1 i]) (le_of_lt he)
        nlinarith
  have htailRisk :
      ∑ i ∈ Finset.Ico (M + 1) (n + 1),
        biasRunGamma As W rate P k i * (As i).magnitude P ≤ a := by
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun i => biasRunGamma As W rate P k i * (As i).magnitude P)
      (Nat.succ_le_succ hnM)
    have hcap := biasRun_magnitudePrefix_le_one hWdiv hmag rate
      hrate0 hrate1 k n
    change (∑ i ∈ Finset.range (M + 1),
      biasRunGamma As W rate P k i * (As i).magnitude P) +
        ∑ i ∈ Finset.Ico (M + 1) (n + 1),
          biasRunGamma As W rate P k i * (As i).magnitude P =
      ∑ i ∈ Finset.range (n + 1),
        biasRunGamma As W rate P k i * (As i).magnitude P at hsplit
    change ∑ i ∈ Finset.range (n + 1),
      biasRunGamma As W rate P k i * (As i).magnitude P ≤ 1 at hcap
    change 1 - a < ∑ i ∈ Finset.range (M + 1),
      biasRunGamma As W rate P k i * (As i).magnitude P at hRiskMlow
    linarith
  have htailSum : -(η / 4) ≤
      ∑ i ∈ Finset.Ico (M + 1) (n + 1),
        biasRunGamma As W rate P k i *
          ((As i).value P v.payout - truth i) := by
    have hpoint : ∀ i,
        -(2 * (biasRunGamma As W rate P k i * (As i).magnitude P)) ≤
          biasRunGamma As W rate P k i *
            ((As i).value P v.payout - truth i) := by
      intro i
      have hwprice := (As i).abs_value_sub_price_le_magnitude P v.payout i
        (hpoly.terms_rank i) (fun φ => by
          by_cases hφ : v.Holds φ
          · exact Or.inr (by simp [PCWorld.payout, hφ])
          · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP i)
      have htprice := hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP i
      have hdiff : -2 * (As i).magnitude P ≤
          (As i).value P v.payout - truth i := by
        rw [abs_le] at hwprice htprice
        linarith
      have hprod := mul_nonneg (hgamma0 i)
        (show 0 ≤ (As i).value P v.payout - truth i +
          2 * (As i).magnitude P by linarith)
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.Ico (M + 1) (n + 1)) => hpoint i)
    have haη : 2 * a ≤ η / 4 := by
      dsimp only [a]
      have hinv : 1 / (ρ + 1) ≤ 1 := (div_le_one hρone).2 (by linarith)
      have hale : η / (8 * (ρ + 1)) ≤ η / 8 := by
        calc
          η / (8 * (ρ + 1)) = (η / 8) * (1 / (ρ + 1)) := by
            field_simp [ne_of_gt hρone]
          _ ≤ (η / 8) * 1 :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = η / 8 := mul_one _
      nlinarith
    have hsumId :
        ∑ i ∈ Finset.Ico (M + 1) (n + 1),
            -(2 * (biasRunGamma As W rate P k i * (As i).magnitude P)) =
          -2 * ∑ i ∈ Finset.Ico (M + 1) (n + 1),
            biasRunGamma As W rate P k i * (As i).magnitude P := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsumId] at hsum
    nlinarith
  have herror : -(3 * η / 8) ≤ prefixSum (fun i =>
      biasRunGamma As W rate P k i *
        ((As i).value P v.payout - truth i)) n := by
    rw [prefixSum]
    rw [← Finset.sum_range_add_sum_Ico
      (fun i => biasRunGamma As W rate P k i *
        ((As i).value P v.payout - truth i)) (Nat.succ_le_succ hnM)]
    linarith
  rw [hmagEq, mul_one]
  rw [biasRunTrader_netWorth hpoly hWgen rate P v k n]
  have hdecomp : prefixSum (fun i =>
      biasRunGamma As W rate P k i *
        ((As i).value P v.payout - (As i).price P i)) n =
      prefixSum (fun i => biasRunGamma As W rate P k i *
        (truth i - (As i).price P i)) n +
      prefixSum (fun i => biasRunGamma As W rate P k i *
        ((As i).value P v.payout - truth i)) n := by
    simp only [prefixSum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdecomp]
  linarith

/-- A persistent negative affine bias forces divergent `W`-weighted share magnitude.
This is the exact specialization of the statistical forcing estimate to affine values
determined by the completed deductive theory. -/
theorem DeterminedViaTheory.weightedMagnitude_tendsto_atTop_of_negative_bias
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (hbias : ∀ᶠ n in atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε) :
    Tendsto
      (prefixSum (fun i => (W i).denote P * (As i).magnitude P))
      atTop atTop := by
  apply weightedExposure_tendsto_atTop_of_eventually_negative_bias
    (fun i => (W i).denote P) (fun i => (As i).price P i) truth
      (fun i => (As i).magnitude P) ε
  · exact fun n => (hWdiv.1 n).1
  · intro n
    exact (le_abs_self (truth n - (As n).price P n)).trans
      (hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP n)
  · exact hWdiv.2
  · exact hε
  · exact hbias

/-- Eventually, every sufficiently late launched run has a uniform Abel-prefix surplus
bound.  The only loss is its finite pre-launch prefix, at most `rateₖ · k`; the persistent
global bias pays for every later prefix. -/
theorem DeterminedViaTheory.biasRun_surplus_eventually
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (ε ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρε : ρ ≤ ε)
    (hbias : ∀ᶠ n in atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε) :
    ∃ N, ∀ k, N ≤ k → ∀ n,
      -(rate k : ℝ) * k ≤ prefixSum (fun i =>
        biasRunAttemptValue W rate P k i *
          ((truth i - (As i).price P i) - ρ * (As i).magnitude P)) n := by
  let w : ℕ → ℝ := fun i => (W i).denote P
  let x : ℕ → ℝ := fun i => truth i - (As i).price P i
  let m : ℕ → ℝ := fun i => (As i).magnitude P
  have hpos := hWdiv.eventually_prefixSum_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpos.and hbias)
  refine ⟨N, fun k hk n => ?_⟩
  have hgateEq :
      prefixSum (fun i =>
        biasRunAttemptValue W rate P k i * (x i - ρ * m i)) n =
      prefixSum (fun i => if k ≤ i then
        (rate k : ℝ) * (w i * (x i - ρ * m i)) else 0) n := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hki : k ≤ i
    · simp [biasRunAttemptValue, biasRunAttempt, hki, w, mul_assoc]
    · simp [biasRunAttemptValue, biasRunAttempt, hki]
  change -(rate k : ℝ) * k ≤
    prefixSum (fun i => biasRunAttemptValue W rate P k i * (x i - ρ * m i)) n
  rw [hgateEq]
  by_cases hkn : k ≤ n
  · rw [prefixSum_gate_mul_eq (fun i => w i * (x i - ρ * m i))
        (rate k : ℝ) k n hkn]
    have hnN : N ≤ n := hk.trans hkn
    have hn := hN n hnN
    have hbiasDiv :
        prefixSum (fun i => w i * ((As i).price P i - truth i)) n /
            prefixSum w n < -ε := by
      simpa [weightedBias, weightedAverage_eq_div (ne_of_gt hn.1), w] using hn.2
    have hpayoff : ε * prefixSum w n < prefixSum (fun i => w i * x i) n := by
      have hneg : prefixSum (fun i => w i * x i) n =
          -prefixSum (fun i => w i * ((As i).price P i - truth i)) n := by
        simp only [prefixSum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [x]
        ring
      rw [hneg]
      have := (div_lt_iff₀ hn.1).1 hbiasDiv
      nlinarith
    have hwm : prefixSum (fun i => w i * m i) n ≤ prefixSum w n := by
      apply Finset.sum_le_sum
      intro i _
      simpa using mul_le_of_le_one_right (hWdiv.1 i).1 (hmag i)
    have hprefix0 : 0 ≤ prefixSum (fun i => w i * (x i - ρ * m i)) n := by
      have hrewrite : prefixSum (fun i => w i * (x i - ρ * m i)) n =
          prefixSum (fun i => w i * x i) n -
            ρ * prefixSum (fun i => w i * m i) n := by
        simp only [prefixSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hrewrite]
      have hsum0 : 0 ≤ prefixSum w n := le_of_lt hn.1
      have hrhom := mul_le_mul_of_nonneg_left hwm hρ0
      have hrhoeps := mul_le_mul_of_nonneg_right hρε hsum0
      linarith
    have hinit :
        ∑ i ∈ Finset.range k, w i * (x i - ρ * m i) ≤ k := by
      calc
        ∑ i ∈ Finset.range k, w i * (x i - ρ * m i) ≤
            ∑ _i ∈ Finset.range k, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro i _
              have hxi : x i ≤ m i :=
                (le_abs_self (x i)).trans
                  (hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP i)
              have hexpr : x i - ρ * m i ≤ 1 := by
                have hm0 := (As i).magnitude_nonneg P
                have hrhom0 := mul_nonneg hρ0 hm0
                linarith [hmag i]
              calc
                w i * (x i - ρ * m i) ≤ w i * 1 :=
                  mul_le_mul_of_nonneg_left hexpr (hWdiv.1 i).1
                _ = w i := mul_one _
                _ ≤ 1 := (hWdiv.1 i).2
        _ = k := by simp
    have hc := hrate0 k
    nlinarith [mul_le_mul_of_nonneg_left hinit hc]
  · have hnlt : n < k := Nat.lt_of_not_ge hkn
    have hz : prefixSum (fun i => if k ≤ i then
        (rate k : ℝ) * (w i * (x i - ρ * m i)) else 0) n = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg]
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      omega
    rw [hz]
    have := mul_nonneg (hrate0 k) (Nat.cast_nonneg k)
    nlinarith

/-- End-to-end exposure consequence for one negative-bias run: under persistent negative
bias, every positive-rate launched component has total share magnitude exactly one.  This
is deliberately weaker than ROI—the latter additionally needs its plausible-world payoff
lower bound—but it closes all normalization, finite-prefix, and summability obligations. -/
theorem DeterminedViaTheory.biasRunTrader_magnitude_eq_one_of_negative_bias
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (hbias : ∀ᶠ n in atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε)
    (k : ℕ) (hratek : 0 < (rate k : ℝ)) :
    (biasRunTrader hpoly hWgen rate k).magnitude P = 1 := by
  have hweighted := hdet.weightedMagnitude_tendsto_atTop_of_negative_bias
    hpoly hWdiv hworld hP ε hε hbias
  have hrisk := biasRunAttemptedRisk_tendsto_atTop As rate P k hratek hweighted
  exact biasRunTrader_magnitude_eq_one_of_attemptedRisk hpoly hWgen hWdiv hmag
    rate hrate0 hrate1 k hrisk

/-- Persistent negative bias yields a uniformly positive-ROI tail of the canonical capped
run family.  The scale is chosen once from the alleged bias gap; every sufficiently late
member then has `ε/4` ROI and total magnitude one. -/
theorem DeterminedViaTheory.eventually_biasRunTrader_hasROI
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (hbias : ∀ᶠ n in atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε) :
    ∃ scale N, ∀ k, N ≤ k →
      HasROI (biasRunTrader hpoly hWgen (biasRunRate scale) k) P DP (ε / 4) := by
  obtain ⟨scale, hscaleNat⟩ := exists_nat_gt (4 / ε)
  have hscale : 1 / (scale + 1 : ℝ) ≤ ε / 4 := by
    have hspos : 0 < (scale : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hspos).2
    have hmul := (div_lt_iff₀ hε).1 hscaleNat
    nlinarith
  have hrate0 : ∀ k, 0 ≤ (biasRunRate scale k : ℝ) :=
    fun k => (biasRunRate_pos scale k).le
  have hrate1 : ∀ k, (biasRunRate scale k : ℝ) ≤ 1 :=
    biasRunRate_le_one scale
  obtain ⟨N, hN⟩ := hdet.biasRun_surplus_eventually hpoly hWdiv hmag
    hworld hP (biasRunRate scale) hrate0 ε (ε / 2) (by linarith)
      (by linarith) hbias
  refine ⟨scale, N, fun k hk => ?_⟩
  have hsurplusRaw := hN k hk
  have hcharge : (biasRunRate scale k : ℝ) * k ≤ ε / 4 :=
    (biasRunRate_mul_index_le scale k).trans hscale
  have hsurplus : ∀ n,
      -(ε / 4) ≤ prefixSum (fun i =>
        biasRunAttemptValue W (biasRunRate scale) P k i *
          ((truth i - (As i).price P i) -
            (ε / 2) * (As i).magnitude P)) n := by
    intro n
    linarith [hsurplusRaw n]
  have hweighted := hdet.weightedMagnitude_tendsto_atTop_of_negative_bias
    hpoly hWdiv hworld hP ε hε hbias
  have hrisk := biasRunAttemptedRisk_tendsto_atTop As (biasRunRate scale) P k
    (biasRunRate_pos scale k) hweighted
  convert hdet.biasRunTrader_hasROI_of_surplus hpoly hWgen hWdiv hmag
    hworld hP (biasRunRate scale) hrate0 hrate1 (ε / 2) (ε / 4)
      (by linarith) k hsurplus hrisk using 1 <;> ring

/-- Exact rational code for the canonical repeatable-ROI tolerance budget. -/
def roiToleranceRat (i : ℕ) : ℚ := ((1 : ℚ) / 2) ^ (i + 1)

/-- Canonical summable tolerance budget for the repeatable-ROI maturity verifier. -/
noncomputable def roiTolerance (i : ℕ) : ℝ := (roiToleranceRat i : ℝ)

theorem roiTolerance_eq (i : ℕ) :
    roiTolerance i = ((1 : ℝ) / 2) ^ (i + 1) := by
  simp [roiTolerance, roiToleranceRat]

theorem roiTolerance_nonneg (i : ℕ) : 0 ≤ roiTolerance i := by
  rw [roiTolerance_eq]
  positivity

theorem roiTolerance_summable : Summable roiTolerance := by
  apply (summable_geometric_two.mul_right ((1 : ℝ) / 2)).congr
  intro i
  rw [roiTolerance_eq, pow_succ]

/-! ## Finite exact maturity-certificate semantics -/

/-- The semantic core of a finite exact maturity checker for a unit-magnitude trader.
Every numeric inequality is rational, and the universal plausible-world payoff claim is
reduced to the finite type of assignments to the first `B` atoms.  The rational quote
function is fixed by the market's actual partial-recursive presentation, rather than being
supplied by this object.

This structure is deliberately named `SemanticCertificate`: its proposition-valued fields
are not claimed to be an encoded executable payload.  The next layer must define a Boolean
checker whose clocked market/process outputs entail these fields. -/
structure UnitMaturitySemanticCertificate (Tr : Trader) (P : History)
    (DP : DeductiveProcess) (market : MarketComputation P)
    (ε η : ℚ) (m : ℕ) where
  atomLimit : ℕ
  deduction_bounded : ∀ φ ∈ DP.D m, BoolPCWorld.atomBound φ ≤ atomLimit
  trades_bounded : ∀ d ≤ m, ∀ p ∈ (Tr.strat d).trades,
    BoolPCWorld.atomBound p.2 ≤ atomLimit
  risk : 1 - η ≤ Tr.partialMagnitudeRat
    (fun d φ => market.quote d (Encodable.encode φ)) m
  payoff : ∀ u : BoolPCWorld.FiniteWorld atomLimit,
    (∀ φ ∈ DP.D m, BoolPCWorld.eval u.toBoolPCWorld φ = true) →
      ε - η ≤ Tr.partialNetWorthRat
        (fun d φ => market.quote d (Encodable.encode φ)) u.payoutRat m

/-- A concrete support bound for every sentence inspected by maturity through day `m`.
Using sums rather than maxima keeps the membership proofs elementary; only finiteness and
the resulting upper bound matter to the exhaustive Boolean check. -/
def maturityAtomLimit (Tr : Trader) (DP : DeductiveProcess) (m : ℕ) : ℕ :=
  (DP.D m).sum BoolPCWorld.atomBound +
    ∑ d ∈ Finset.range (m + 1),
      ((Tr.strat d).trades.map (fun p => BoolPCWorld.atomBound p.2)).sum

/-- The same support bound computed from a decoded deductive stage. -/
def maturityAtomLimitFromStage (Tr : Trader) (stage : Finset Sentence) (m : ℕ) : ℕ :=
  stage.sum BoolPCWorld.atomBound +
    ∑ d ∈ Finset.range (m + 1),
      ((Tr.strat d).trades.map (fun p => BoolPCWorld.atomBound p.2)).sum

/-- The proposition checked for one finite Boolean world at one fuel bound. -/
def unitMaturityWorldProperty
    (Tr : Trader) (P : History) (market : MarketComputation P)
    (ε η : ℚ) (m fuel : ℕ) (stage : Finset Sentence)
    (u : BoolPCWorld.FiniteWorld (maturityAtomLimitFromStage Tr stage m)) : Prop :=
  (∀ φ : {φ // φ ∈ stage},
      BoolPCWorld.eval u.toBoolPCWorld φ.1 = true) →
    match Tr.partialNetWorthRatAtFuel market fuel u.payoutRat m with
    | none => False
    | some worth => ε - η ≤ worth

/-- An explicit executable decision procedure for the single-world maturity property.
The finite quantifier over the decoded deductive stage is handled by its `Fintype`
instance; the remaining branches are Boolean equality and rational comparison. -/
def unitMaturityWorldPropertyDecidable
    (Tr : Trader) (P : History) (market : MarketComputation P)
    (ε η : ℚ) (m fuel : ℕ) (stage : Finset Sentence)
    (u : BoolPCWorld.FiniteWorld (maturityAtomLimitFromStage Tr stage m)) :
    Decidable (unitMaturityWorldProperty Tr P market ε η m fuel stage u) := by
  unfold unitMaturityWorldProperty
  letI : Decidable (∀ φ : {φ // φ ∈ stage},
      BoolPCWorld.eval u.toBoolPCWorld φ.1 = true) :=
    Fintype.decidableForallFintype
  by_cases hstage : ∀ φ : {φ // φ ∈ stage},
      BoolPCWorld.eval u.toBoolPCWorld φ.1 = true
  · cases hworth : Tr.partialNetWorthRatAtFuel market fuel u.payoutRat m with
    | none =>
        exact isFalse (fun h => by
          have := h hstage
          simp at this)
    | some worth =>
        by_cases hle : ε - η ≤ worth
        · exact isTrue (fun _ => by simpa [hworth] using hle)
        · exact isFalse (fun h => hle (by simpa [hworth] using h hstage))
  · exact isTrue (fun h => (hstage h).elim)

/-- The executable bounded maturity check.  It accepts only after the certified process
program has produced stage `m`, all required market calls have terminated, the rational
risk inequality holds, and every finite Boolean world satisfying that stage passes the
rational payoff inequality. -/
def unitMaturityCheckAtFuel
    (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (ε η : ℚ) (m fuel : ℕ) : Bool :=
  match process.stageAtFuel fuel m with
  | none => false
  | some stage =>
      match Tr.partialMagnitudeRatAtFuel market fuel m with
      | none => false
      | some risk => by
          letI : DecidablePred (fun u : BoolPCWorld.FiniteWorld
              (maturityAtomLimitFromStage Tr stage m) =>
              unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
            unitMaturityWorldPropertyDecidable Tr P market ε η m fuel stage
          letI : Decidable (∀ u : BoolPCWorld.FiniteWorld
              (maturityAtomLimitFromStage Tr stage m),
              unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
            Fintype.decidableForallFintype
          exact decide
            (1 - η ≤ risk ∧
              ∀ u : BoolPCWorld.FiniteWorld
                  (maturityAtomLimitFromStage Tr stage m),
                unitMaturityWorldProperty Tr P market ε η m fuel stage u)

theorem maturityAtomLimit_deduction_bounded
    (Tr : Trader) (DP : DeductiveProcess) (m : ℕ) :
    ∀ φ ∈ DP.D m, BoolPCWorld.atomBound φ ≤ maturityAtomLimit Tr DP m := by
  intro φ hφ
  have hsingle : BoolPCWorld.atomBound φ ≤
      (DP.D m).sum BoolPCWorld.atomBound :=
    Finset.single_le_sum (fun ψ _ => Nat.zero_le (BoolPCWorld.atomBound ψ)) hφ
  unfold maturityAtomLimit
  omega

theorem maturityAtomLimit_trades_bounded
    (Tr : Trader) (DP : DeductiveProcess) (m : ℕ) :
    ∀ d ≤ m, ∀ p ∈ (Tr.strat d).trades,
      BoolPCWorld.atomBound p.2 ≤ maturityAtomLimit Tr DP m := by
  intro d hd p hp
  have hmem : BoolPCWorld.atomBound p.2 ∈
      ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)) :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  have hlocal : BoolPCWorld.atomBound p.2 ≤
      ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  have hday : d ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have houter :
      ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)).sum ≤
        ∑ j ∈ Finset.range (m + 1),
          ((Tr.strat j).trades.map
            (fun q => BoolPCWorld.atomBound q.2)).sum :=
    Finset.single_le_sum (fun j _ => Nat.zero_le
      ((Tr.strat j).trades.map
        (fun q => BoolPCWorld.atomBound q.2)).sum) hday
  unfold maturityAtomLimit
  omega

/-- A `true` bounded check produces the exact semantic certificate. -/
def unitMaturityCheckAtFuel_certificate
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {ε η : ℚ} {m fuel : ℕ}
    (hcheck : unitMaturityCheckAtFuel Tr P DP market process ε η m fuel = true) :
    UnitMaturitySemanticCertificate Tr P DP market ε η m := by
  unfold unitMaturityCheckAtFuel at hcheck
  split at hcheck
  · contradiction
  · rename_i stage hstage
    split at hcheck
    · contradiction
    · rename_i risk hrisk
      letI : DecidablePred (fun u : BoolPCWorld.FiniteWorld
          (maturityAtomLimitFromStage Tr stage m) =>
          unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
        unitMaturityWorldPropertyDecidable Tr P market ε η m fuel stage
      letI : Decidable (∀ u : BoolPCWorld.FiniteWorld
          (maturityAtomLimitFromStage Tr stage m),
          unitMaturityWorldProperty Tr P market ε η m fuel stage u) :=
        Fintype.decidableForallFintype
      have hfinite := of_decide_eq_true hcheck
      have hstageEq := process.stageAtFuel_sound hstage
      subst stage
      refine {
        atomLimit := maturityAtomLimit Tr DP m
        deduction_bounded := maturityAtomLimit_deduction_bounded Tr DP m
        trades_bounded := maturityAtomLimit_trades_bounded Tr DP m
        risk := ?_
        payoff := ?_
      }
      · have hriskEq := Tr.partialMagnitudeRatAtFuel_sound market fuel m hrisk
        simpa [hriskEq] using hfinite.1
      · intro u hu
        have hworld := hfinite.2 u (fun φ => hu φ.1 φ.2)
        cases hworth : Tr.partialNetWorthRatAtFuel market fuel u.payoutRat m with
        | none => simp [hworth] at hworld
        | some worth =>
            have hworthEq :=
              Tr.partialNetWorthRatAtFuel_sound market fuel u.payoutRat m hworth
            simpa [hworth, hworthEq] using hworld

/-- Soundness of the finite rational/Boolean maturity certificate.  This theorem closes
the semantic core of the checker: exhaustive finite assignments really imply the
universal real-valued plausible-world payoff condition in `Trader.Matured`. -/
theorem UnitMaturitySemanticCertificate.sound
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) {ε η : ℚ} {m : ℕ}
    (c : UnitMaturitySemanticCertificate Tr P DP market ε η m)
    (hmag : Tr.magnitude P = 1) :
    Tr.Matured P DP (ε : ℝ) (η : ℝ) m := by
  constructor
  · rw [hmag, mul_one, Tr.partialMagnitude_eq_ratCast P
      (fun d φ => market.quote d (Encodable.encode φ)) market.quote_exact]
    exact_mod_cast c.risk
  · intro v hv
    let u : BoolPCWorld.FiniteWorld c.atomLimit :=
      BoolPCWorld.FiniteWorld.restrict (BoolPCWorld.ofPCWorld v) c.atomLimit
    have hu : ∀ φ ∈ DP.D m,
        BoolPCWorld.eval u.toBoolPCWorld φ = true := by
      intro φ hφ
      dsimp only [u]
      rw [BoolPCWorld.eval_toBoolPCWorld_restrict _ _ _
        (c.deduction_bounded φ hφ)]
      apply (BoolPCWorld.eval_eq_true_iff_holds _ _).2
      simpa using hv φ hφ
    have hpay := c.payoff u hu
    have hworth :
        Tr.partialNetWorthRat
            (fun d φ => market.quote d (Encodable.encode φ)) u.payoutRat m =
          Tr.partialNetWorthRat
            (fun d φ => market.quote d (Encodable.encode φ)) v.payoutRat m := by
      apply Tr.partialNetWorthRat_congr
      intro d hd p hp
      exact BoolPCWorld.FiniteWorld.payoutRat_restrict_ofPCWorld
        v c.atomLimit p.2 (c.trades_bounded d hd p hp)
    rw [hworth] at hpay
    rw [hmag, mul_one,
      Tr.netWorth_eq_ratCast P
        (fun d φ => market.quote d (Encodable.encode φ)) market.quote_exact
        v v.payoutRat
        v.payout_eq_ratCast m]
    exact_mod_cast hpay

/-- A `true` bounded check is a genuine maturity witness for a unit-magnitude trader.
This is the central no-false-positive theorem for the executable checker. -/
theorem unitMaturityCheckAtFuel_sound
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {ε η : ℚ} {m fuel : ℕ}
    (hcheck : unitMaturityCheckAtFuel Tr P DP market process ε η m fuel = true)
    (hmag : Tr.magnitude P = 1) :
    Tr.Matured P DP (ε : ℝ) (η : ℝ) m :=
  (unitMaturityCheckAtFuel_certificate market process hcheck).sound market hmag

/-- Semantic completeness of the finite rational/Boolean reduction.  Every genuine
rational-parameter maturity witness for a unit-magnitude trader yields a finite support
bound and the exact rational inequalities consumed by the semantic certificate.  No
computability claim is made here; serialization and bounded checking are the next layer. -/
def UnitMaturitySemanticCertificate.ofMatured
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) {ε η : ℚ} {m : ℕ}
    (hmature : Tr.Matured P DP (ε : ℝ) (η : ℝ) m)
    (hmag : Tr.magnitude P = 1) :
    UnitMaturitySemanticCertificate Tr P DP market ε η m := by
  let Q : ℕ → Sentence → ℚ :=
    fun d φ => market.quote d (Encodable.encode φ)
  refine {
    atomLimit := maturityAtomLimit Tr DP m
    deduction_bounded := ?_
    trades_bounded := ?_
    risk := ?_
    payoff := ?_
  }
  · intro φ hφ
    have hsingle : BoolPCWorld.atomBound φ ≤
        (DP.D m).sum BoolPCWorld.atomBound :=
      Finset.single_le_sum (fun ψ _ => Nat.zero_le (BoolPCWorld.atomBound ψ)) hφ
    unfold maturityAtomLimit
    omega
  · intro d hd p hp
    have hmem : BoolPCWorld.atomBound p.2 ∈
        ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)) :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    have hlocal : BoolPCWorld.atomBound p.2 ≤
        ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
    have hday : d ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have houter :
        ((Tr.strat d).trades.map (fun q => BoolPCWorld.atomBound q.2)).sum ≤
          ∑ j ∈ Finset.range (m + 1),
            ((Tr.strat j).trades.map
              (fun q => BoolPCWorld.atomBound q.2)).sum :=
      Finset.single_le_sum (fun j _ => Nat.zero_le
        ((Tr.strat j).trades.map
          (fun q => BoolPCWorld.atomBound q.2)).sum) hday
    unfold maturityAtomLimit
    omega
  · have hrisk := hmature.1
    change 1 - η ≤ Tr.partialMagnitudeRat Q m
    rw [hmag, mul_one,
      Tr.partialMagnitude_eq_ratCast P Q market.quote_exact m] at hrisk
    exact_mod_cast hrisk
  · intro u hu
    let v : PCWorld := u.toBoolPCWorld.toPCWorld
    have hv : v.ConsistentWith (DP.D m) := by
      intro φ hφ
      exact (BoolPCWorld.eval_eq_true_iff_holds u.toBoolPCWorld φ).mp (hu φ hφ)
    have hpay := hmature.2 v hv
    have hpayout : ∀ φ, v.payout φ = (u.payoutRat φ : ℝ) := by
      intro φ
      rw [v.payout_eq_ratCast]
      congr 1
      exact (BoolPCWorld.FiniteWorld.payoutRat_eq_toPCWorld u φ).symm
    change ε - η ≤ Tr.partialNetWorthRat Q u.payoutRat m
    rw [hmag, mul_one,
      Tr.netWorth_eq_ratCast P Q market.quote_exact v u.payoutRat hpayout m] at hpay
    exact_mod_cast hpay

/-- Exact two-way semantic characterization of unit-trader maturity by the finite
rational/Boolean certificate core. -/
theorem UnitMaturitySemanticCertificate.nonempty_iff_matured
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) {ε η : ℚ} {m : ℕ}
    (hmag : Tr.magnitude P = 1) :
    Nonempty (UnitMaturitySemanticCertificate Tr P DP market ε η m) ↔
      Tr.Matured P DP (ε : ℝ) (η : ℝ) m := by
  constructor
  · rintro ⟨c⟩
    exact c.sound market hmag
  · intro hmature
    exact ⟨UnitMaturitySemanticCertificate.ofMatured market hmature hmag⟩

/-- No genuine unit-trader maturity witness is missed forever: one finite interpreter
clock simultaneously recovers the deductive stage and every exact rational market quote
needed by the trader prefix, after which the exhaustive Boolean checker accepts. -/
theorem unitMaturityCheckAtFuel_eventually_complete
    {Tr : Trader} {P : History} {DP : DeductiveProcess}
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    {ε η : ℚ} {m : ℕ}
    (hmature : Tr.Matured P DP (ε : ℝ) (η : ℝ) m)
    (hmag : Tr.magnitude P = 1) :
    ∃ fuel, unitMaturityCheckAtFuel Tr P DP market process ε η m fuel = true := by
  let c : UnitMaturitySemanticCertificate Tr P DP market ε η m :=
    UnitMaturitySemanticCertificate.ofMatured market hmature hmag
  obtain ⟨processFuel, hprocess⟩ := process.stageAtFuel_complete m
  obtain ⟨marketFuel, hmarket⟩ := market.exists_fuel_quoteAtFuel_list
    (Tr.partialMagnitudeRatQueries m ++ Tr.partialNetWorthRatQueries m)
  let fuel := max processFuel marketFuel
  have hstage : process.stageAtFuel fuel m = some (DP.D m) :=
    process.stageAtFuel_mono (le_max_left _ _) hprocess
  have hquotes : ∀ query ∈
      Tr.partialMagnitudeRatQueries m ++ Tr.partialNetWorthRatQueries m,
      market.quoteAtFuel fuel query.1 query.2 =
        some (market.quote query.1 (Encodable.encode query.2)) := by
    intro query hquery
    exact market.quoteAtFuel_mono (le_max_right _ _) (hmarket query hquery)
  have hmagnitude : Tr.partialMagnitudeRatAtFuel market fuel m = some
      (Tr.partialMagnitudeRat
        (fun d φ => market.quote d (Encodable.encode φ)) m) :=
    Tr.partialMagnitudeRatAtFuel_complete market fuel m (fun query hquery =>
      hquotes query (List.mem_append.mpr (Or.inl hquery)))
  have hnetWorth (u : BoolPCWorld.FiniteWorld (maturityAtomLimit Tr DP m)) :
      Tr.partialNetWorthRatAtFuel market fuel u.payoutRat m = some
        (Tr.partialNetWorthRat
          (fun d φ => market.quote d (Encodable.encode φ)) u.payoutRat m) :=
    Tr.partialNetWorthRatAtFuel_complete market fuel u.payoutRat m
      (fun query hquery =>
        hquotes query (List.mem_append.mpr (Or.inr hquery)))
  refine ⟨fuel, ?_⟩
  unfold unitMaturityCheckAtFuel
  rw [hstage, hmagnitude]
  letI : DecidablePred (fun u : BoolPCWorld.FiniteWorld
      (maturityAtomLimitFromStage Tr (DP.D m) m) =>
      unitMaturityWorldProperty Tr P market ε η m fuel (DP.D m) u) :=
    unitMaturityWorldPropertyDecidable Tr P market ε η m fuel (DP.D m)
  letI : Decidable (∀ u : BoolPCWorld.FiniteWorld
      (maturityAtomLimitFromStage Tr (DP.D m) m),
      unitMaturityWorldProperty Tr P market ε η m fuel (DP.D m) u) :=
    Fintype.decidableForallFintype
  apply decide_eq_true
  constructor
  · exact c.risk
  · intro u hu
    rw [hnetWorth u]
    exact c.payoff u (fun φ hφ => hu ⟨φ, hφ⟩)

/-- The exact remaining operational boundary in the affine recurring-unbiasedness proof:
for every alleged bias gap, a single polynomial Boolean table recognizes historical
maturity certificates for the canonical capped-run family.  Unlike a conclusion-bearing
oracle, the returned object exposes its checker, polynomial clock, soundness, and
eventual-completeness fields through `HistoricalVerifiedMaturitySchedule`.

The paper derives this interface by dovetailing the computable rational market and
deductive-process computations.  Constructing that dovetailer in the repository's
clocked token model is the remaining representation obligation. -/
def BiasRunHistoricallyVerifiable
    (As : ℕ → AffineCombination) (hpoly : PolySequence As)
    (W : ℕ → EF) (hWgen : PGenerableWeighting W)
    (P : History) (DP : DeductiveProcess) : Prop :=
  ∀ ε : ℚ, 0 < (ε : ℝ) → ∀ scale N,
    (∀ k, N ≤ k →
      HasROI (biasRunTrader hpoly hWgen (biasRunRate scale) k)
        P DP ((ε : ℝ) / 4)) →
    Nonempty (ROIBudget.HistoricalVerifiedMaturitySchedule
      (gateTraderFamily N
        (biasRunTrader hpoly hWgen (biasRunRate scale)))
      P DP ((ε : ℝ) / 4) roiTolerance)

/-- Operational consumer for the missing computability edge of affine recurring
unbiasedness.  A persistent negative bias produces a tail of unit-magnitude positive-ROI
run traders.  If finite historical maturity claims for that tail have the paper's bounded
verifier, `noRepeatableROI` forces the corresponding `0/1` magnitude progression to tend
to zero, contradicting its eventual value one.

This theorem intentionally exposes the historical verifier as a hypothesis and is not the
paper-facing capstone.  Its purpose is to isolate the remaining obligation precisely: the
next theorem must construct `hverify` from `IsLogicalInductor.marketComputable` and
`.processComputable`, rather than assuming a semantic closing day. -/
theorem DeterminedViaTheory.not_eventually_weightedBias_lt_of_historicalVerifier
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (ε : ℝ) (hε : 0 < ε)
    (η : ℕ → ℝ) (hη0 : ∀ i, 0 ≤ η i) (hηsum : Summable η)
    (hverify : ∀ scale N,
      (∀ k, N ≤ k →
        HasROI (biasRunTrader hpoly hWgen (biasRunRate scale) k)
          P DP (ε / 4)) →
      ROIBudget.HistoricalVerifiedMaturitySchedule
        (gateTraderFamily N
          (biasRunTrader hpoly hWgen (biasRunRate scale)))
        P DP (ε / 4) η) :
    ¬ ∀ᶠ n in atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε := by
  intro hbias
  obtain ⟨scale, N, hroiTail⟩ := hdet.eventually_biasRunTrader_hasROI
    hpoly hWgen hWdiv hmag hworld hP ε hε hbias
  let baseTs : ℕ → Trader :=
    biasRunTrader hpoly hWgen (biasRunRate scale)
  let Ts : ℕ → Trader := gateTraderFamily N baseTs
  let α : ℕ → EF := gateFeature N (fun _ => EF.const 1)
  have hroi : ∀ i, HasROI (Ts i) P DP (ε / 4) := by
    intro i
    by_cases hi : N ≤ i
    · simpa [Ts, baseTs, gateTraderFamily, hi] using hroiTail i hi
    · simpa [Ts, gateTraderFamily, hi] using
        (Trader.zero_hasROI P DP (ε / 4))
  have hbasePoly : PolyTradeEmulatable baseTs := by
    simpa [baseTs] using
      (biasRunTrader_polyTrade hpoly hWgen (biasRunRate scale)
        (biasRunRate_codes scale))
  have hTsPoly : PolyTradeEmulatable Ts := by
    simpa [Ts, baseTs] using hbasePoly.gateBefore N
  have hαrank : ∀ i, (α i).rank ≤ i := by
    intro i
    by_cases hi : N ≤ i <;> simp [α, gateFeature, hi, EF.rank]
  have hαseg : PolySegStream (fun i => (α i).serialize) := by
    apply PolySegStream.gateFeature
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)) N
  have hαclosed : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V := by
    intro i ρ V
    by_cases hi : N ≤ i <;>
      simp [α, gateFeature, hi, EF.denoteWith, EF.denote]
  have hαmag : ∀ i, (α i).denote P = (Ts i).magnitude P := by
    intro i
    by_cases hi : N ≤ i
    · simp only [α, gateFeature, hi, if_true, EF.denote_const, Ts,
        gateTraderFamily, baseTs]
      symm
      simpa using
        (hdet.biasRunTrader_magnitude_eq_one_of_negative_bias hpoly hWgen
          hWdiv hmag hworld hP (biasRunRate scale)
          (fun k => (biasRunRate_pos scale k).le)
          (biasRunRate_le_one scale) ε hε hbias i (biasRunRate_pos scale i))
    · simp [α, Ts, gateFeature, gateTraderFamily, hi, Trader.magnitude,
        Trader.zero, Strategy.magnitude]
  have hα0 : ∀ i, 0 ≤ (α i).denote P := by
    intro i
    by_cases hi : N ≤ i <;> simp [α, gateFeature, hi]
  have hα1 : ∀ i, (α i).denote P ≤ 1 := by
    intro i
    by_cases hi : N ≤ i <;> simp [α, gateFeature, hi]
  have hhist : ROIBudget.HistoricalVerifiedMaturitySchedule
      Ts P DP (ε / 4) η := by
    simpa [Ts, baseTs] using hverify scale N hroiTail
  let hver : ROIBudget.VerifiedMaturitySchedule Ts P DP (ε / 4) η :=
    hhist.toVerified hη0 hP hroi
  have hconv : ConvergesTo (fun i => (α i).denote P) 0 := by
    exact ROIBudget.noRepeatableROI_of_verifiedMaturity Ts P DP
      (ε / 4) (by linarith) η α hαrank hαseg hαclosed hαmag hα0 hα1
      hP hTsPoly hroi hη0 hηsum hver hworld
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hconv 1 (by norm_num)
  have hnear := hK (max N K) (le_max_right N K)
  have hlaunch : N ≤ max N K := le_max_left N K
  simp [α, gateFeature, hlaunch, Real.dist_eq] at hnear

/-- One-sided affine recurring unbiasedness from the isolated historical-verification
interface.  This is the exact `limsup ≥ 0` half of the paper proof. -/
theorem DeterminedViaTheory.not_eventually_weightedBias_lt
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hverify : BiasRunHistoricallyVerifiable As hpoly W hWgen P DP)
    (ε : ℝ) (hε : 0 < ε) :
    ¬ ∀ᶠ n in atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε := by
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, (0 : ℝ) < q ∧ (q : ℝ) < ε :=
    exists_rat_btwn hε
  have hnotq := hdet.not_eventually_weightedBias_lt_of_historicalVerifier
    hpoly hWgen hWdiv hmag hworld hP (q : ℝ) hq0 roiTolerance
      roiTolerance_nonneg roiTolerance_summable
      (fun scale N hroi => (hverify q hq0 scale N hroi).some)
  intro hbad
  apply hnotq
  filter_upwards [hbad] with n hn
  linarith

/-- Affine recurring unbiasedness, conditional only on the explicitly isolated
historical-verification representation boundary for the sequence and its negation.  The
analytic crossing, both economic contradictions, and negation transport are all proved
here; no limit-point or bias conclusion occurs in either verifier hypothesis. -/
theorem DeterminedViaTheory.recunbiasedaff_of_historicalVerifiers
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hverify : BiasRunHistoricallyVerifiable As hpoly W hWgen P DP)
    (hverifyNeg : BiasRunHistoricallyVerifiable (fun n => (As n).neg)
      hpoly.neg W hWgen P DP) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth) 0 := by
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).price P i
  let f : ℕ → ℝ := weightedBias w market truth
  have hstep : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0) := by
    apply weightedAverage_step_tendsto_zero w
      (fun i => market i - truth i) 1
    · exact fun n => (hWdiv.1 n).1
    · exact fun n => (hWdiv.1 n).2
    · intro n
      have hn := hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP n
      rw [abs_sub_comm] at hn
      exact hn.trans (hmag n)
    · exact hWdiv.2
  have hlower : ∀ ε > 0, ∃ᶠ n in atTop, -ε < f n := by
    intro ε hε
    have hnot := hdet.not_eventually_weightedBias_lt hpoly hWgen hWdiv
      hmag hworld hP hverify (ε / 2) (by linarith)
    rw [Filter.not_eventually] at hnot
    exact hnot.mono (fun n hn => by
      simp only [not_lt] at hn
      dsimp only [f, w, market]
      linarith)
  have hdetNeg := hdet.neg
  have hmagNeg : ∀ i, ((As i).neg).magnitude P ≤ 1 := by
    intro i
    rw [AffineCombination.neg_magnitude]
    exact hmag i
  have hupper : ∀ ε > 0, ∃ᶠ n in atTop, f n < ε := by
    intro ε hε
    have hnot := hdetNeg.not_eventually_weightedBias_lt hpoly.neg hWgen hWdiv
      hmagNeg hworld hP hverifyNeg (ε / 2) (by linarith)
    rw [Filter.not_eventually] at hnot
    exact hnot.mono (fun n hn => by
      simp only [not_lt] at hn
      rw [show (fun i => ((As i).neg).price P i) = fun i => -market i by
        funext i
        exact AffineCombination.neg_price (As i) P i,
        weightedBias_neg] at hn
      dsimp only [f]
      linarith)
  exact hasLimitPoint_zero_of_two_sided_recurring f hstep hlower hupper

/-- Paper-facing `thm:recunbiasedaff` for an arbitrary bounded-combination sequence.
The economic hub above is stated at unit magnitude; this wrapper performs one canonical
positive rational normalization, asks the operational verifier only for that concrete
normalized family, and cancels the scale from the exact zero-limit-point conclusion. -/
theorem BoundedCombinationSequence.recunbiasedaff
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hverify : BiasRunHistoricallyVerifiable
      (fun n => (As n).scale (.const h.unitNormalization.scale))
      (h.poly.scaleRat h.unitNormalization.scale) W hWgen P DP)
    (hverifyNeg : BiasRunHistoricallyVerifiable
      (fun n => ((As n).scale (.const h.unitNormalization.scale)).neg)
      (h.poly.scaleRat h.unitNormalization.scale).neg W hWgen P DP) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth) 0 := by
  let q : ℚ := h.unitNormalization.scale
  have hq : 0 < (q : ℝ) := h.unitNormalization.scale_pos
  have hdetScaled : DeterminedViaTheory
      (fun n => (As n).scale (.const q)) P DP
      (fun n => (q : ℝ) * truth n) := by
    intro n v hv
    rw [AffineCombination.scale_value, EF.denote_const, hdet n v hv]
  have hs := hdetScaled.recunbiasedaff_of_historicalVerifiers
    (h.poly.scaleRat q) hWgen hWdiv h.unitNormalization.magnitude_le_one
      hworld hP hverify hverifyNeg
  have hscaled : HasLimitPoint
      (fun n => (q : ℝ) * weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n) 0 := by
    have hs' : HasLimitPoint
        (weightedBias (fun i => (W i).denote P)
          (fun i => (q : ℝ) * (As i).price P i)
          (fun i => (q : ℝ) * truth i)) 0 := by
      simpa only [q, AffineCombination.scale_price, EF.denote_const] using hs
    have heq : weightedBias (fun i => (W i).denote P)
        (fun i => (q : ℝ) * (As i).price P i)
        (fun i => (q : ℝ) * truth i) =
        fun n => (q : ℝ) * weightedBias (fun i => (W i).denote P)
          (fun i => (As i).price P i) truth n := by
      funext n
      exact weightedBias_const_mul _ _ _ _ _
    rwa [heq] at hs'
  exact hasLimitPoint_zero_of_const_mul (ne_of_gt hq) hscaled

/-- A concrete truth stream for a sentence progression: every completed-theory world
assigns the same Boolean payout.  This is the propositional rendering of the paper's
efficient sequence of decidable sentences and `ThmInd(φₙ)`. -/
def TheoryTruth (φ : ℕ → Sentence) (DP : DeductiveProcess)
    (truth : ℕ → ℝ) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.payout (φ n) = truth n

theorem TheoryTruth.isBoolean {φ : ℕ → Sentence} {DP : DeductiveProcess}
    {truth : ℕ → ℝ} (h : TheoryTruth φ DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    truth n = 0 ∨ truth n = 1 := by
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  have hn := h n v hv
  by_cases hh : v.Holds (φ n)
  · right
    simpa [PCWorld.payout, hh] using hn.symm
  · left
    simpa [PCWorld.payout, hh] using hn.symm

/-- Ordinary recurring unbiasedness as the one-share specialization of affine recurring
unbiasedness, retaining the same explicit historical-verification boundary. -/
theorem recurringunbiasedness_of_historicalVerifiers
    (φ : ℕ → Sentence) (hpoly : PolySequence (sentenceAffine φ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} (htruth : TheoryTruth φ DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1)
    (hverify : BiasRunHistoricallyVerifiable (sentenceAffine φ)
      hpoly W hWgen P DP)
    (hverifyNeg : BiasRunHistoricallyVerifiable
      (fun n => (sentenceAffine φ n).neg) hpoly.neg W hWgen P DP) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => P i (φ i)) truth) 0 := by
  have hdet : DeterminedViaTheory (sentenceAffine φ) P DP truth := by
    intro n v hv
    simpa [sentenceAffine, AffineCombination.value] using htruth n v hv
  have hmag : ∀ i, (sentenceAffine φ i).magnitude P ≤ 1 := by
    intro i
    simp
  have h := hdet.recunbiasedaff_of_historicalVerifiers hpoly hWgen hWdiv
    hmag hworld hP hverify hverifyNeg
  simpa using h

/-- Recurring calibration from the ordinary recurring-unbiasedness specialization.  Both
the divergent-case limit point and convergent-case interval guarantee are the exact
paper conclusions; the only remaining representation premise is the named historical
verifier for the sentence family and its negation. -/
theorem simcal_of_historicalVerifiers
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (truth : ℕ → ℝ)
    (a b : ℚ) (δ : ℕ → ℚ)
    (hδ : PolyPositiveWidths δ)
    (hpoly : PolySequence (sentenceAffine φ))
    (htruth : TheoryTruth φ DP truth)
    (hWgen : PGenerableWeighting (calibrationIndicator φ a b δ))
    (hdiv : DivergentWeighting (calibrationIndicator φ a b δ) P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1)
    (hverify : BiasRunHistoricallyVerifiable (sentenceAffine φ) hpoly
      (calibrationIndicator φ a b δ) hWgen P DP)
    (hverifyNeg : BiasRunHistoricallyVerifiable
      (fun n => (sentenceAffine φ n).neg) hpoly.neg
      (calibrationIndicator φ a b δ) hWgen P DP) :
    HasLimitPointIn
        (weightedAverage
          (fun n => (calibrationIndicator φ a b δ n).denote P) truth)
        (Icc (a : ℝ) (b : ℝ)) ∧
      ∀ x, ConvergesTo
          (weightedAverage
            (fun n => (calibrationIndicator φ a b δ n).denote P) truth) x →
        x ∈ Icc (a : ℝ) (b : ℝ) := by
  have hbias := recurringunbiasedness_of_historicalVerifiers φ hpoly hWgen
    htruth hdiv hworld hP hverify hverifyNeg
  exact simcal_of_recurring_unbiasedness P φ truth a b δ hδ
    (fun n => htruth.isBoolean hworld n) hdiv hbias

end AffineCombination

#print axioms calibration_limitPoint_transfer
#print axioms calibration_convergent_limit_mem
#print axioms hasLimitPoint_zero_of_two_sided_recurring
#print axioms weightedAverage_step_tendsto_zero
#print axioms weightedBias_neg
#print axioms calibrationIndicator_pgenerable
#print axioms simcal_of_recurring_unbiasedness
#print axioms AffineCombination.DeterminedViaTheory.unique
#print axioms AffineCombination.DeterminedViaTheory.neg
#print axioms AffineCombination.DeterminedViaTheory.eventually_close
#print axioms AffineCombination.biasRunCoefficient_denote
#print axioms AffineCombination.biasRun_magnitudePrefix_le_one
#print axioms AffineCombination.biasRunTrader_summable_and_magnitude_le_one
#print axioms AffineCombination.biasRunTrader_magnitude_eq_one_of_attemptedRisk
#print axioms AffineCombination.DeterminedViaTheory.abs_truth_sub_price_le_magnitude
#print axioms weightedExposure_tendsto_atTop_of_eventually_negative_bias
#print axioms prefixSum_mul_lower_of_prefixSum_lower
#print axioms AffineCombination.fractionalFamilyFeatureWeight_polySeg
#print axioms AffineCombination.biasRunTrader_polyTrade
#print axioms AffineCombination.DeterminedViaTheory.biasRunTrader_hasROI_of_surplus
#print axioms AffineCombination.DeterminedViaTheory.eventually_biasRunTrader_hasROI
#print axioms MarketComputation.evaln_quote_eq
#print axioms MarketComputation.exists_evaln_quote
#print axioms MarketComputation.quoteAtFuel_sound
#print axioms MarketComputation.quoteAtFuel_complete
#print axioms MarketComputation.exists_fuel_quoteAtFuel_list
#print axioms DeductiveProcessComputation.evaln_eq_stage
#print axioms DeductiveProcessComputation.exists_evaln_stage
#print axioms DeductiveProcessComputation.stageAtFuel_sound
#print axioms DeductiveProcessComputation.stageAtFuel_complete
#print axioms AffineCombination.exists_valueSet
#print axioms AffineCombination.DeterminedViaTheory.exists_settled_stage
#print axioms AffineCombination.DeterminedViaTheory.settled_iff_agree
#print axioms AffineCombination.value_eq_ratCast
#print axioms AffineCombination.valueRat_congr
#print axioms AffineCombination.agree_of_finiteWorlds_agree
#print axioms EF.denoteRatWithAtFuel_sound
#print axioms EF.denoteRatWithAtFuel_complete
#print axioms EF.exists_fuel_denoteRatWithAtFuel
#print axioms AffineCombination.unitMaturityCheckAtFuel_certificate
#print axioms AffineCombination.unitMaturityCheckAtFuel_sound
#print axioms AffineCombination.unitMaturityCheckAtFuel_eventually_complete
#print axioms AffineCombination.UnitMaturitySemanticCertificate.sound
#print axioms AffineCombination.UnitMaturitySemanticCertificate.nonempty_iff_matured
#print axioms AffineCombination.DeterminedViaTheory.not_eventually_weightedBias_lt_of_historicalVerifier
#print axioms AffineCombination.DeterminedViaTheory.recunbiasedaff_of_historicalVerifiers
#print axioms AffineCombination.BoundedCombinationSequence.recunbiasedaff
#print axioms AffineCombination.recurringunbiasedness_of_historicalVerifiers
#print axioms AffineCombination.simcal_of_historicalVerifiers

end LogicalInduction
