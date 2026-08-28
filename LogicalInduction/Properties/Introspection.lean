/-
# Introspection — §4.11: `thm:epr`, `thm:er`, `thm:ref`, `thm:lp`

Same-day introspective identities.  The propositional language here cannot construct the
paper's first-order quotations directly, so a quote is represented by a concrete polynomial
affine portfolio.  Unlike the deferred Self-Trust certificates, no cross-day coherence is
assumed: the portfolio has the quoted gap as its current price and is worth zero in every
world consistent with the completed theory.  Affine Provability Induction supplies the
learning step.
-/
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.WriteOut

namespace LogicalInduction

open Filter Topology

/-- A same-day affine quotation identity.  The inherited object exposes the exact
portfolio, uniform emitter, normalization, bounded prices, and bounded magnitude;
`theory_coherent` is the first-order quotation law translated to completed-theory worlds.
Paper node: `thm:er` -/
structure CompletedAffineQuoteEq (P : History) (DP : DeductiveProcess)
    (gap : ℕ → ℝ) extends AffineQuotePortfolio P gap where
  theory_coherent : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (family n).value P v.payout = 0

namespace CompletedAffineQuoteEq

/-- A completed-theory quotation identity is learned on the market diagonal. -/
lemma gap_asympEq_zero {P : History} {DP : DeductiveProcess} {gap : ℕ → ℝ}
    (q : CompletedAffineQuoteEq P DP gap) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    gap ≈ₙ fun _ => 0 := by
  have hprice := q.poly.affine_provind_theory_eq P DP q.bounded
    ⟨1, q.magnitude_le_one⟩ hworld 0 q.theory_coherent
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  have hs : (0 : ℝ) < q.scale := by exact_mod_cast q.scale_pos
  have hnear := asympEq_iff_eventuallyWithin.1 hprice
    ((q.scale : ℝ) * ε) (mul_pos hs hε)
  filter_upwards [hnear] with n hn
  rw [q.current_price, sub_zero, abs_mul, abs_of_pos hs] at hn
  simpa only [sub_zero] using (mul_le_mul_iff_of_pos_left hs).mp hn

end CompletedAffineQuoteEq

/-- A same-day quotation whose completed-theory value vanishes uniformly.  Numeric LUV
quotes naturally have this form: their finite threshold bundle differs from the represented
real by at most the mesh width, while Boolean quotation identities use the exact
`CompletedAffineQuoteEq` specialization above.
Paper node: `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` -/
structure CompletedAffineQuoteApprox (P : History) (DP : DeductiveProcess)
    (gap : ℕ → ℝ) extends AffineQuotePortfolio P gap where
  theory_coherent : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
    v.ConsistentWithTheory DP → |(family n).value P v.payout| ≤ ε

namespace CompletedAffineQuoteApprox

/-- A uniformly vanishing completed-theory quotation error is learned on the market
diagonal. -/
lemma gap_asympEq_zero {P : History} {DP : DeductiveProcess} {gap : ℕ → ℝ}
    (q : CompletedAffineQuoteApprox P DP gap) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    gap ≈ₙ fun _ => 0 := by
  have hprice := q.poly.affine_provind_theory_tendsto_zero P DP q.bounded
    ⟨1, q.magnitude_le_one⟩ hworld q.theory_coherent
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  have hs : (0 : ℝ) < q.scale := by exact_mod_cast q.scale_pos
  have hnear := asympEq_iff_eventuallyWithin.1 hprice
    ((q.scale : ℝ) * ε) (mul_pos hs hε)
  filter_upwards [hnear] with n hn
  rw [q.current_price, sub_zero, abs_mul, abs_of_pos hs] at hn
  simpa only [sub_zero] using (mul_le_mul_iff_of_pos_left hs).mp hn

end CompletedAffineQuoteApprox

/-- Operational quotation package for `thm:epr`. `Y n` is the LUV expressing the actual
day-`n` price of `φ n`. The `reflected` field records the intended first-order semantics;
the `affine` field is the concrete same-day portfolio consumed by the proof.
Paper node: `thm:epr` -/
structure CurrentPriceExpectationQuote (P : History) (DP : DeductiveProcess)
    (φ : ℕ → Sentence) (Y : ℕ → LUV) where
  sentence_codes : BigSentenceCodes φ
  quote_codes : LUV.RpnThresholdCodeSeq Y
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Y n) (P n (φ n))
  affine : CompletedAffineQuoteApprox P DP
    (fun n => P n (φ n) - (Y n).expect P n)

/-- Operational quotation package for `thm:er`. `Y n` expresses the actual day-`n`
expectation of `X n`.
Paper node: `thm:er` -/
structure CurrentExpectationQuote (P : History) (DP : DeductiveProcess)
    (X Y : ℕ → LUV) where
  source_codes : LUV.RpnThresholdCodeSeq X
  quote_codes : LUV.RpnThresholdCodeSeq Y
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    v.ValuesAt (Y n) ((X n).expect P n)
  affine : CompletedAffineQuoteApprox P DP
    (fun n => (X n).expect P n - (Y n).expect P n)

/-- **Expectations of Probabilities** (`thm:epr`): the price of `φ n` agrees
asymptotically with the expectation of its represented current-price LUV.
Paper node: `thm:epr` -/
theorem lic_expectations_of_probabilities
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (Y : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (q : CurrentPriceExpectationQuote P DP φ Y) :
    (fun n => P n (φ n)) ≈ₙ fun n => (Y n).expect P n := by
  simpa only [AsympEq, sub_zero] using q.affine.gap_asympEq_zero hworld

/-- **Iterated Expectations** (`thm:er`): the current expectation of `X n` agrees
asymptotically with the current expectation of the LUV representing that expectation.
Paper node: `thm:er` -/
theorem lic_iterated_expectations
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X Y : ℕ → LUV)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (q : CurrentExpectationQuote P DP X Y) :
    (fun n => (X n).expect P n) ≈ₙ fun n => (Y n).expect P n := by
  simpa only [AsympEq, sub_zero] using q.affine.gap_asympEq_zero hworld

/-! ## Interval introspection -/

/-- The continuous threshold gate always lies in `[0,1]` when its width is positive. -/
lemma ctsInd_mem_Icc (δ : ℚ) (x y : ℝ) :
    ctsInd δ x y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min zero_le_one (le_max_left _ _)
  · exact min_le_left _ _

/-- The continuous threshold gate is fully on once its first argument exceeds the second
by at least the positive rational width. -/
lemma ctsInd_eq_one_of_le_sub (δ : ℚ) (x y : ℝ) (hδ : 0 < δ)
    (hgap : (δ : ℝ) ≤ x - y) : ctsInd δ x y = 1 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hratio : 1 ≤ (x - y) / (δ : ℝ) := (le_div_iff₀ hδR).2 (by linarith)
  have hzero : 0 ≤ (x - y) / (δ : ℝ) := zero_le_one.trans hratio
  unfold ctsInd
  rw [max_eq_right hzero, min_eq_left hratio]

/-- Operational quotation package for `thm:ref`.  `quote n` is the represented sentence
saying that the actual day-`n` price of `φ n` lies strictly between `a n` and `b n`.
The two inherited affine objects are exactly the paper's inside and outside continuous
products.  They expose concrete polynomial portfolios and completed-world identities;
neither object assumes the error bounds proved below.
Paper node: `thm:ref` -/
structure IntrospectionIntervalQuote (P : History) (DP : DeductiveProcess)
    (φ : ℕ → Sentence) (a b δ : ℕ → ℚ) where
  source_codes : BigSentenceCodes φ
  lower_feature : ℕ → EF
  lower_generated : GeneratedRatFeature P a lower_feature
  upper_feature : ℕ → EF
  upper_generated : GeneratedRatFeature P b upper_feature
  inverse_width_codes : DigitRatCodes (fun n ↦ 1 / δ n)
  width_pos : ∀ n, 0 < δ n
  width_tendsto_zero : Tendsto (fun n ↦ (δ n : ℝ)) atTop (𝓝 0)
  probability_bounds : ∀ n,
    0 ≤ a n ∧ a n ≤ 1 ∧ 0 ≤ b n ∧ b n ≤ 1
  quote : ℕ → Sentence
  quote_codes : BigSentenceCodes quote
  reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (v.Holds (quote n) ↔ (a n : ℝ) < P n (φ n) ∧ P n (φ n) < (b n : ℝ))
  inside_affine : CompletedAffineQuoteEq P DP (fun n ↦
    (ctsInd (δ n) (P n (φ n)) (a n : ℝ) *
      ctsInd (δ n) (b n : ℝ) (P n (φ n))) *
      (1 - P n (quote n)))
  outside_affine : CompletedAffineQuoteEq P DP (fun n ↦
    (ctsInd (δ n) (a n : ℝ) (P n (φ n)) +
      ctsInd (δ n) (P n (φ n)) (b n : ℝ)) *
      P n (quote n))

lemma IntrospectionIntervalQuote.lower_pgenerable
    {P : History} {DP : DeductiveProcess} {φ : ℕ → Sentence}
    {a b δ : ℕ → ℚ} (q : IntrospectionIntervalQuote P DP φ a b δ) :
    PGenerableRat P a :=
  ⟨q.lower_feature, q.lower_generated⟩

lemma IntrospectionIntervalQuote.upper_pgenerable
    {P : History} {DP : DeductiveProcess} {φ : ℕ → Sentence}
    {a b δ : ℕ → ℚ} (q : IntrospectionIntervalQuote P DP φ a b δ) :
    PGenerableRat P b :=
  ⟨q.upper_feature, q.upper_generated⟩

/-- **Introspection** (`thm:ref`): there is a positive *rational* error sequence tending
to zero which controls both the shrunken-interval belief and expanded-interval disbelief
claims on every day.  The rational sequence is selected strictly between the maximum
absolute learned affine gap plus `1/(n+1)` and the same gap plus `2/(n+1)`; thus the
rational-valued conclusion is not hidden in the quotation package.
Paper node: `thm:ref` -/
theorem lic_introspection
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (a b δ : ℕ → ℚ)
    (q : IntrospectionIntervalQuote P DP φ a b δ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ ε : ℕ → ℚ,
      (∀ n, 0 < ε n) ∧
      Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) ∧
      ∀ n,
        (((a n : ℝ) + δ n < P n (φ n) ∧
            P n (φ n) < (b n : ℝ) - δ n) →
          1 - (ε n : ℝ) < P n (q.quote n)) ∧
        ((¬ ((a n : ℝ) - δ n < P n (φ n) ∧
              P n (φ n) < (b n : ℝ) + δ n)) →
          P n (q.quote n) < (ε n : ℝ)) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  let lowerGap : ℕ → ℝ := fun n ↦
    (ctsInd (δ n) (P n (φ n)) (a n : ℝ) *
      ctsInd (δ n) (b n : ℝ) (P n (φ n))) *
      (1 - P n (q.quote n))
  let upperGap : ℕ → ℝ := fun n ↦
    (ctsInd (δ n) (a n : ℝ) (P n (φ n)) +
      ctsInd (δ n) (P n (φ n)) (b n : ℝ)) *
      P n (q.quote n)
  let raw : ℕ → ℝ := fun n ↦ max |lowerGap n| |upperGap n|
  have hlower := q.inside_affine.gap_asympEq_zero hworld
  have hupper := q.outside_affine.gap_asympEq_zero hworld
  have hlower0 : Tendsto lowerGap atTop (𝓝 0) := by
    simpa [lowerGap, AsympEq] using hlower
  have hupper0 : Tendsto upperGap atTop (𝓝 0) := by
    simpa [upperGap, AsympEq] using hupper
  have hraw0 : Tendsto raw atTop (𝓝 0) := by
    simpa [raw] using hlower0.abs.max hupper0.abs
  have hsmall0 : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hexists : ∀ n, ∃ e : ℚ,
      raw n + (1 : ℝ) / (n + 1) < (e : ℝ) ∧
        (e : ℝ) < raw n + 2 * ((1 : ℝ) / (n + 1)) := by
    intro n
    apply exists_rat_btwn
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hs : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  let ε : ℕ → ℚ := fun n ↦ Classical.choose (hexists n)
  have hεbounds (n : ℕ) :
      raw n + (1 : ℝ) / (n + 1) < (ε n : ℝ) ∧
        (ε n : ℝ) < raw n + 2 * ((1 : ℝ) / (n + 1)) := by
    exact Classical.choose_spec (hexists n)
  have hraw_nonneg (n : ℕ) : 0 ≤ raw n := by
    exact le_max_of_le_left (abs_nonneg _)
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    exact_mod_cast (lt_trans (by positivity : (0 : ℝ) < raw n + 1 / (n + 1 : ℝ))
      (hεbounds n).1)
  have hupperBound0 : Tendsto
      (fun n ↦ raw n + 2 * ((1 : ℝ) / (n + 1))) atTop (𝓝 0) := by
    convert hraw0.add (hsmall0.const_mul 2) using 1 ; simp
  have hε0 : Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (le_of_lt (by exact_mod_cast hεpos n)))
      (fun n ↦ (hεbounds n).2.le) hupperBound0
  refine ⟨ε, hεpos, hε0, ?_⟩
  intro n
  have hlowRaw : |lowerGap n| ≤ raw n := le_max_left _ _
  have huppRaw : |upperGap n| ≤ raw n := le_max_right _ _
  have hrawε : raw n < (ε n : ℝ) := by
    have hs : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith [(hεbounds n).1]
  constructor
  · rintro ⟨ha, hb⟩
    have hgateA : ctsInd (δ n) (P n (φ n)) (a n : ℝ) = 1 :=
      ctsInd_eq_one_of_le_sub (δ n) _ _ (q.width_pos n) (by linarith)
    have hgateB : ctsInd (δ n) (b n : ℝ) (P n (φ n)) = 1 :=
      ctsInd_eq_one_of_le_sub (δ n) _ _ (q.width_pos n) (by linarith)
    have hgap : |1 - P n (q.quote n)| < (ε n : ℝ) := by
      rw [show lowerGap n = 1 - P n (q.quote n) by simp [lowerGap, hgateA, hgateB]] at hlowRaw
      exact hlowRaw.trans_lt hrawε
    linarith [(abs_lt.mp hgap).2]
  · intro houtside
    have hcases : P n (φ n) ≤ (a n : ℝ) - δ n ∨
        (b n : ℝ) + δ n ≤ P n (φ n) := by
      by_cases hleft : P n (φ n) ≤ (a n : ℝ) - δ n
      · exact Or.inl hleft
      · right
        have hinsideLeft : (a n : ℝ) - δ n < P n (φ n) := lt_of_not_ge hleft
        exact le_of_not_gt (fun hinsideRight ↦ houtside ⟨hinsideLeft, hinsideRight⟩)
    have hgate : 1 ≤
        ctsInd (δ n) (a n : ℝ) (P n (φ n)) +
          ctsInd (δ n) (P n (φ n)) (b n : ℝ) := by
      rcases hcases with hleft | hright
      · have hgateLeft : ctsInd (δ n) (a n : ℝ) (P n (φ n)) = 1 :=
          ctsInd_eq_one_of_le_sub (δ n) _ _ (q.width_pos n) (by linarith)
        rw [hgateLeft]
        linarith [(ctsInd_mem_Icc (δ n) (P n (φ n)) (b n : ℝ)).1]
      · have hgateRight : ctsInd (δ n) (P n (φ n)) (b n : ℝ) = 1 :=
          ctsInd_eq_one_of_le_sub (δ n) _ _ (q.width_pos n) (by linarith)
        rw [hgateRight]
        linarith [(ctsInd_mem_Icc (δ n) (a n : ℝ) (P n (φ n))).1]
    have hquote := (hP n (q.quote n)).1
    have hgap_nonneg : 0 ≤ upperGap n := by
      dsimp [upperGap]
      positivity
    have hquote_le_gap : P n (q.quote n) ≤ upperGap n := by
      dsimp [upperGap]
      nlinarith
    have hgap_lt : upperGap n < (ε n : ℝ) := by
      rw [abs_of_nonneg hgap_nonneg] at huppRaw
      exact huppRaw.trans_lt hrawε
    exact hquote_le_gap.trans_lt hgap_lt

/-! ## Paradox resistance -/

/-- Operational diagonal-quotation package for `thm:lp`. `sentence n` is the paradoxical
claim saying that its own day-`n` price is below `p`. The two affine certificates are the
paper's lower- and upper-side continuous products; their completed-world values are zero,
but no market convergence is included in the package.
Paper node: `thm:lp` -/
structure ParadoxResistanceQuote (P : History) (DP : DeductiveProcess)
    (p : ℚ) where
  sentence : ℕ → Sentence
  sentence_codes : BigSentenceCodes sentence
  width : ℕ → ℚ
  width_pos : ∀ n, 0 < width n
  width_tendsto_zero : Tendsto (fun n => (width n : ℝ)) atTop (𝓝 0)
  diagonal_reflected : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    (v.Holds (sentence n) ↔ P n (sentence n) < (p : ℝ))
  lower_affine : CompletedAffineQuoteEq P DP (fun n =>
    ctsInd (width n) (p : ℝ) (P n (sentence n)) * (1 - P n (sentence n)))
  upper_affine : CompletedAffineQuoteEq P DP (fun n =>
    ctsInd (width n) (P n (sentence n)) (p : ℝ) * P n (sentence n))

/-- **Paradox Resistance** (`thm:lp`): a diagonal sentence true exactly when its own
current price is below `p ∈ (0,1)` receives price asymptotic to `p`. The proof separately
rules out prices bounded below and above `p`; the vanishing continuous width absorbs the
boundary where the diagonal comparison is undecidable.
Paper node: `thm:lp` -/
theorem lic_paradox_resistance
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (q : ParadoxResistanceQuote P DP p)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (q.sentence n)) ≈ₙ fun _ => (p : ℝ) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  let μ : ℝ := min (p : ℝ) (1 - p)
  have hμ : 0 < μ := lt_min hp0R (sub_pos.mpr hp1R)
  have hlower := q.lower_affine.gap_asympEq_zero hworld
  have hupper := q.upper_affine.gap_asympEq_zero hworld
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  have hwidth : ∀ᶠ n in atTop, (q.width n : ℝ) < ε :=
    q.width_tendsto_zero (Iio_mem_nhds hε)
  have hlowerNear := asympEq_iff_eventuallyWithin.1 hlower (μ / 2) (by linarith)
  have hupperNear := asympEq_iff_eventuallyWithin.1 hupper (μ / 2) (by linarith)
  filter_upwards [hwidth, hlowerNear, hupperNear] with n hδ hnlow hnhigh
  simp only [sub_zero] at hnlow hnhigh
  rw [abs_le]
  constructor
  · by_contra hnot
    have hprice : P n (q.sentence n) < (p : ℝ) - ε := by linarith
    have hgate : ctsInd (q.width n) (p : ℝ) (P n (q.sentence n)) = 1 :=
      ctsInd_eq_one_of_le_sub (q.width n) (p : ℝ) (P n (q.sentence n))
        (q.width_pos n) (by linarith)
    rw [hgate, one_mul, abs_of_nonneg (by linarith [(hP n (q.sentence n)).2])] at hnlow
    have hμle : μ ≤ 1 - (p : ℝ) := min_le_right _ _
    linarith
  · by_contra hnot
    have hprice : (p : ℝ) + ε < P n (q.sentence n) := by linarith
    have hgate : ctsInd (q.width n) (P n (q.sentence n)) (p : ℝ) = 1 :=
      ctsInd_eq_one_of_le_sub (q.width n) (P n (q.sentence n)) (p : ℝ)
        (q.width_pos n) (by linarith)
    rw [hgate, one_mul, abs_of_nonneg (hP n (q.sentence n)).1] at hnhigh
    have hμle : μ ≤ (p : ℝ) := min_le_left _ _
    linarith

#print axioms CompletedAffineQuoteEq.gap_asympEq_zero
#print axioms CompletedAffineQuoteApprox.gap_asympEq_zero
#print axioms lic_expectations_of_probabilities
#print axioms lic_iterated_expectations
#print axioms lic_introspection
#print axioms lic_paradox_resistance

end LogicalInduction
