/-
# `thm:ec` — Expectations Converge

Paper (`main.tex` 1688): the day-`n` expectation `𝔼ₙ(X)` of any `[0,1]`-LUV converges.

The paper derives `thm:ec` from the affine master theorems rather than from a bespoke
trader, and so do we.  `𝔼ₙ(X)` is *exactly* the market price of the precision-`n`
threshold bundle `X.expectAffine n` (`def:e`), an efficiently emitted affine progression.
Hence:

1. **Affine Coherence** (`thm:affcoh`) traps the diagonal price sequence between the
   liminf/limsup of the *limiting belief's* valuations of the same bundles.
2. **Limit Coherence** (`thm:lc`) presents the limiting belief as a countably additive
   probability measure concentrated on completed-theory worlds, so the limiting belief's
   precision-`n` valuation is the average of the worlds' precision-`n` valuations.
3. **`lem:conluvapprox`** bounds `|𝔼ⁿ_v(X) − 𝔼ᵐ_v(X)|` by `1/n + 1/m` in every world that
   values `X`, making that average Cauchy.

The world-value hypothesis is therefore consumed **per grid**: for each precision `k`,
*some* stage after which all stage-consistent worlds value `X` on grid `k`.  No rate ties
`k` to the stage — that is exactly what `Θ`-completeness delivers, and a completed-theory
world (being consistent with every stage) is constrained on every grid at once.

The feature-generic signal layer (`buyIndF`/`sellIndF`) that used to live here is shared
vocabulary and now sits in `Properties/Hysteresis.lean`, next to `thm:con`'s own signals.
-/
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.LimitCoherence
import LogicalInduction.Properties.ExpectationAffine
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace LogicalInduction

open Filter Topology MeasureTheory

/-! ### World-side inputs (`lem:conluvapprox`) -/

/-- `lem:conluvapprox`, difference form: two precisions of one world's approximate
expectation agree up to their two mesh errors. -/
lemma PCWorld.ApproxValuesUpTo.abs_expectApprox_sub_le {v : PCWorld} {X : LUV} {x : ℝ}
    {n m k : ℕ} (hx : v.ApproxValuesUpTo X x k) (hn : 0 < n) (hm : 0 < m)
    (hnk : n ≤ k) (hmk : m ≤ k) :
    |X.expectApprox v.payout n - X.expectApprox v.payout m| ≤ 1 / n + 1 / m := by
  have h1 := hx.2 n hn hnk
  have h2 := hx.2 m hm hmk
  calc |X.expectApprox v.payout n - X.expectApprox v.payout m|
      ≤ |X.expectApprox v.payout n - x| + |x - X.expectApprox v.payout m| :=
        abs_sub_le _ _ _
    _ ≤ 1 / n + 1 / m := by rw [abs_sub_comm x]; linarith

/-- A completed-theory world is consistent with *every* stage, so per-grid maturity —
which pins grid `k` only at some unspecified stage — still constrains it on every grid. -/
lemma PCWorld.approxValuesUpTo_of_consistentWithTheory {X : LUV} {DP : DeductiveProcess}
    (hval : ∀ k, ∀ᶠ n in atTop, ∀ (v : PCWorld),
      v.ConsistentWith (DP.D n) → ∃ x, v.ApproxValuesUpTo X x k)
    {v : PCWorld} (hv : v.ConsistentWithTheory DP) (k : ℕ) :
    ∃ x, v.ApproxValuesUpTo X x k := by
  obtain ⟨n, hn⟩ := (hval k).exists
  exact hn v (hv n)

/-! ### Averaging the limiting belief over completed-theory worlds (`thm:lc`) -/

/-- A `φ`-share's payout is the indicator of the event "`φ` holds". -/
lemma payout_eq_indicator (φ : Sentence) :
    (fun v : PCWorld => v.payout φ) = Set.indicator {v : PCWorld | v.Holds φ} 1 := by
  funext v
  by_cases h : v.Holds φ <;> simp [PCWorld.payout, h]

lemma measurable_payout (φ : Sentence) :
    Measurable (fun v : PCWorld => v.payout φ) := by
  rw [payout_eq_indicator]
  exact measurable_one.indicator (measurable_pcWorld_holds φ).setOf

lemma payout_mem_Icc (v : PCWorld) (φ : Sentence) : 0 ≤ v.payout φ ∧ v.payout φ ≤ 1 := by
  unfold PCWorld.payout
  split <;> norm_num

lemma integrable_payout {μ : Measure PCWorld} [IsFiniteMeasure μ] (φ : Sentence) :
    Integrable (fun v : PCWorld => v.payout φ) μ :=
  (integrable_const (1 : ℝ)).mono' (measurable_payout φ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (payout_mem_Icc v φ).1]
      exact (payout_mem_Icc v φ).2))

lemma measurable_expectApprox (X : LUV) (n : ℕ) :
    Measurable (fun v : PCWorld => X.expectApprox v.payout n) := by
  simp only [LUV.expectApprox]
  exact measurable_const.mul
    (Finset.measurable_sum _ (fun i _ => measurable_payout _))

lemma integrable_expectApprox {μ : Measure PCWorld} [IsFiniteMeasure μ] (X : LUV)
    (n : ℕ) : Integrable (fun v : PCWorld => X.expectApprox v.payout n) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_expectApprox X n).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun v => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg
    (X.expectApprox_nonneg v.payout n (fun s => (payout_mem_Icc v s).1))]
  exact X.expectApprox_le_one v.payout n (fun s => (payout_mem_Icc v s).2)

/-- Under a limit-coherent presentation (`thm:lc`), the limiting belief's approximate
expectation is the average of the worlds' approximate expectations. -/
lemma expectApprox_limitingBelief_eq_integral (P : History) {μ : Measure PCWorld}
    [IsFiniteMeasure μ] (X : LUV)
    (hmeasure : ∀ φ : Sentence,
      μ {v : PCWorld | v.Holds φ} = ENNReal.ofReal (limitingBelief P φ))
    (hL0 : ∀ φ, 0 ≤ limitingBelief P φ) (n : ℕ) :
    X.expectApprox (limitingBelief P) n = ∫ v, X.expectApprox v.payout n ∂μ := by
  have hpay : ∀ φ : Sentence, ∫ v, v.payout φ ∂μ = limitingBelief P φ := by
    intro φ
    rw [payout_eq_indicator,
      MeasureTheory.integral_indicator_one (measurable_pcWorld_holds φ).setOf,
      Measure.real, hmeasure φ, ENNReal.toReal_ofReal (hL0 φ)]
  have hsplit : ∫ v, X.expectApprox v.payout n ∂μ
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ v, v.payout (X.gt ((i : ℚ) / (n : ℚ))) ∂μ := by
    simp only [LUV.expectApprox]
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => integrable_payout _)]
  rw [hsplit, LUV.expectApprox]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (hpay _).symm)

/-- The limiting belief's approximate expectations converge: they are averages over
completed-theory worlds, each of which approximately values `X` on every grid, so the
precision sequence is Cauchy with modulus `1/n + 1/m`. -/
lemma LUV.expectApprox_limitingBelief_converges (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ k, ∀ᶠ n in atTop, ∀ (v : PCWorld),
      v.ConsistentWith (DP.D n) → ∃ x, v.ApproxValuesUpTo X x k) :
    ∃ L : ℝ, ConvergesTo (fun n => X.expectApprox (limitingBelief P) n) L := by
  obtain ⟨μ, hprob, hmeasure, hae⟩ := lic_limitCoherence P DP hcons
  haveI : IsProbabilityMeasure μ := hprob
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hL0 : ∀ φ, 0 ≤ limitingBelief P φ := fun φ =>
    ge_of_tendsto (lic_limitingBelief_tendsto P DP hcons φ)
      (Filter.Eventually.of_forall (fun n => (hP n φ).1))
  have hint := expectApprox_limitingBelief_eq_integral P X hmeasure hL0
  have hcauchy : ∀ n m : ℕ, 0 < n → 0 < m →
      |X.expectApprox (limitingBelief P) n - X.expectApprox (limitingBelief P) m|
        ≤ 1 / n + 1 / m := by
    intro n m hn hm
    rw [hint n, hint m, ← integral_sub (integrable_expectApprox X n)
      (integrable_expectApprox X m)]
    have hbound : ∀ᵐ v ∂μ, ‖X.expectApprox v.payout n - X.expectApprox v.payout m‖
        ≤ 1 / (n : ℝ) + 1 / (m : ℝ) := by
      filter_upwards [hae] with v hv
      obtain ⟨x, hx⟩ :=
        PCWorld.approxValuesUpTo_of_consistentWithTheory hval hv (max n m)
      simpa only [Real.norm_eq_abs] using
        hx.abs_expectApprox_sub_le hn hm (le_max_left n m) (le_max_right n m)
    have hnorm := norm_integral_le_of_norm_le
      (integrable_const ((1 : ℝ) / n + 1 / m)) hbound
    simpa only [Real.norm_eq_abs, integral_const, probReal_univ, smul_eq_mul,
      one_mul] using hnorm
  have hCauchy : CauchySeq (fun n => X.expectApprox (limitingBelief P) n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    have hkey : ∀ j : ℕ, N < j → 1 / (j : ℝ) < ε / 2 := by
      intro j hj
      have hjR : (2 / ε : ℝ) < (j : ℝ) := hN.trans (by exact_mod_cast hj)
      have hjpos : (0 : ℝ) < (j : ℝ) := lt_of_le_of_lt (by positivity) hjR
      rw [div_lt_div_iff₀ hjpos (by norm_num : (0:ℝ) < 2)]
      rw [div_lt_iff₀ hε] at hjR
      linarith
    refine ⟨N + 1, fun m hm n hn => ?_⟩
    have hm0 : 0 < m := by omega
    have hn0 : 0 < n := by omega
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hcauchy m n hm0 hn0) ?_
    have h1 := hkey m (by omega)
    have h2 := hkey n (by omega)
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCauchy
  exact ⟨L, hL⟩

/-! ### The endpoint -/

/-- **Expectations Converge** (`thm:ec`): under a logical inductor, the day-`n`
expectation of any `[0,1]`-LUV converges, provided plausible worlds keep existing
(`hcons`) and every finite threshold grid is eventually pinned in all plausible worlds
(`hval` — the `lem:conluvapprox` linkage, disclosed type-`(c)`: it imports "`Θ` represents
computations" as a hypothesis).  `hval` is **per grid**: for each precision `k` there is
some stage after which stage-consistent worlds value `X` on grid `k`, with *no rate* tying
`k` to the stage.

Proof kind `C` (composition): `thm:affcoh` traps the diagonal bundle price between the
limiting belief's liminf/limsup; `thm:lc` averages the limiting belief over
completed-theory worlds; `lem:conluvapprox` makes that average Cauchy.  The exploiting
traders are those of the affine master theorems, all constructed and e.c.-certified.
Provenance: `hcode` and `hcons` are the disclosed representation boundaries; `hval` is the
disclosed type-`(c)` linkage above; everything else is derived in-project.

The threshold-block hypothesis is the symbol-metered `def:ec` interface for the paper's
`Θ`-definable LUV syntax.
Paper node: `thm:ec` -/
theorem LUV.expect_converges (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (X : LUV)
    (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ k, ∀ᶠ n in atTop, ∀ (v : PCWorld),
      v.ConsistentWith (DP.D n) → ∃ x, v.ApproxValuesUpTo X x k) :
    ∃ L : ℝ, ConvergesTo (X.expectSeq P) L := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  obtain ⟨L, hL⟩ := X.expectApprox_limitingBelief_converges P DP hcons hval
  refine ⟨L, ?_⟩
  have hbdd : BoundedAffinePrices X.expectAffine P := by
    refine ⟨1, zero_le_one, fun n m => ?_⟩
    rw [AffineCombination.price, X.expectAffine_value P (P m) n, abs_of_nonneg
      (X.expectApprox_nonneg (P m) n (fun s => (hP m s).1))]
    exact X.expectApprox_le_one (P m) n (fun s => (hP m s).2)
  have hcoh := (X.expectAffine_polySequence hcode).affcoh P DP hbdd
    ⟨1, fun n => X.expectAffine_magnitude_le_one P n⟩ hcons
  have hvalEq : (fun n => (X.expectAffine n).value P (limitingBelief P))
      = fun n => X.expectApprox (limitingBelief P) n :=
    funext (fun n => X.expectAffine_value P (limitingBelief P) n)
  have hpriceEq : (fun n => (X.expectAffine n).price P n) = X.expectSeq P :=
    funext (fun n => X.expectAffine_price P n)
  rw [hvalEq, hpriceEq] at hcoh
  have hlimI : liminf (fun n => X.expectApprox (limitingBelief P) n) atTop = L :=
    hL.liminf_eq
  have hlimS : limsup (fun n => X.expectApprox (limitingBelief P) n) atTop = L :=
    hL.limsup_eq
  have hlo : IsBoundedUnder (· ≥ ·) atTop (X.expectSeq P) :=
    isBoundedUnder_of_eventually_ge (a := (0 : ℝ)) (Filter.Eventually.of_forall
      (fun n => (X.expect_mem_Icc P n (fun s => hP n s)).1))
  have hhi : IsBoundedUnder (· ≤ ·) atTop (X.expectSeq P) :=
    isBoundedUnder_of_eventually_le (a := (1 : ℝ)) (Filter.Eventually.of_forall
      (fun n => (X.expect_mem_Icc P n (fun s => hP n s)).2))
  have hle : liminf (X.expectSeq P) atTop ≤ limsup (X.expectSeq P) atTop :=
    liminf_le_limsup hhi hlo
  have hLlo : L ≤ liminf (X.expectSeq P) atTop := hlimI ▸ hcoh.1.2
  have hLhi : limsup (X.expectSeq P) atTop ≤ L := hlimS ▸ hcoh.2.1
  exact tendsto_of_liminf_eq_limsup (le_antisymm (hle.trans hLhi) hLlo)
    (le_antisymm hLhi (hLlo.trans hle)) hhi hlo

#print axioms LUV.expect_converges

/-- `𝔼_∞(X)` — the limiting expectation (`thm:ec`). -/
noncomputable def LUV.expectInf (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV)
    (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ k, ∀ᶠ n in atTop, ∀ (v : PCWorld),
      v.ConsistentWith (DP.D n) → ∃ x, v.ApproxValuesUpTo X x k) : ℝ :=
  (X.expect_converges P DP hcode hcons hval).choose

end LogicalInduction
