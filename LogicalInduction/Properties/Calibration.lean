import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.Support.WeightedAverages
import LogicalInduction.Properties.Support.SettlementDecision
import LogicalInduction.Framework.BooleanWorlds
import LogicalInduction.Framework.Emission.WriteOut
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact

/-!
# Calibration and unbiasedness

Renders §4.3 "Calibration and Unbiasedness" — the continuous threshold indicator
`def:ctsind` (tex:1174), divergent weightings `def:fuz` (tex:1212) and weightings generable
from the market `def:ece` (tex:1218) — together with the §4.5 affine generalization
`thm:recunbiasedaff` (tex:1469).  Appendix proofs: `app:simcal`,
`app:recurringunbiasedness`, `app:recunbiasedaff`.

## What this module builds

* **The two halves of "`P`-generable divergent weighting".** `PGenerableWeighting` carries
  `def:ece`'s emitted feature progression; `DivergentWeighting` carries `def:fuz`'s `[0,1]`
  bound together with the divergent prefix sum.  `pGenerableWeighting_iff` places the
  former against `GeneratedRatFeature`, which is the same data plus a denotation clause.
* **The calibration selector.** `calibrationLower`, `calibrationUpper` and
  `calibrationIndicator` render `def:ctsind` at the feature level, and
  `calibrationIndicator_pgenerable` proves the selector generable from the paper's own
  hypotheses on `⟨φ⟩` and `⟨δ⟩` rather than assuming it.  The real-valued rendering of the
  same definition is `ctsInd` in `Properties/SelfTrust.lean`.
* **Limit points.** `HasLimitPoint` and `HasLimitPointIn`, and the analytic calibration
  transfer built on them.
* **The capped bias-run trader family.** `biasRunRate`, `biasRunAttempt`,
  `biasRunCoefficient` and `biasRunTrader`, emitted by the single uniform polynomial
  emitter `biasRunTrader_polyTrade`; persistent negative bias forces every late member to
  unit share magnitude and positive ROI.

The averaging vocabulary this file is stated in and the settlement/maturity decision
procedures it runs are shared §4.3–4.4 technology and sit upstream, in
`Properties/Support/WeightedAverages.lean` and `Properties/Support/SettlementDecision.lean`;
those module headers inventory them.

## The conditional layer and where it is discharged

`BiasRunHistoricallyVerifiable` isolates the one remaining operational premise: a bounded
verifier for historical maturity claims about the capped-run family.  Every endpoint here
whose name ends `_of_historicalVerifiers` is stated against that premise —
`ApproxDeterminedViaTheory.recunbiasedaff_of_historicalVerifiers`, its exact-determination
specialization `DeterminedViaTheory.recunbiasedaff_of_historicalVerifiers`, the
bounded-sequence form
`BoundedCombinationSequence.recunbiasedaff_of_historicalVerifiers`, and the sentence-level
`recurringunbiasedness_of_historicalVerifiers` and `simcal_of_historicalVerifiers`.

The unconditional forms — `thm:recunbiasedaff` as
`AffineCombination.BoundedCombinationSequence.recunbiasedaff`,
`thm:recurringunbiasedness` as `AffineCombination.recurringunbiasedness` and `thm:simcal`
as `AffineCombination.simcal` — are proved in
`Construction/Statistics/HistoricalMaturity.lean`, which discharges the premise from the
constructed market and deductive-process computations.

Convention: `weightedAverage` is total, taking value zero when the denominator vanishes.
Every result that divides separately proves the denominator eventually positive from
divergence, so the paper's divergent-weighting hypothesis is never silently strengthened.
-/

namespace LogicalInduction

open Filter Topology Set
open scoped BigOperators

/-! ## Divergent weightings generable from the market -/

/-- A sequence of expressible features generated uniformly in polynomial time and legal
on its own day.  Its denotation may depend continuously on the market prefix, exactly as
in the paper's notion “generable from `P`”.
Paper node: `def:ece`, `def:fuz` -/
structure PGenerableWeighting (W : ℕ → EF) : Prop where
  polySeg : BigSpliceStream (fun n => (W n).serialize)
  rank_le : ∀ n, (W n).rank ≤ n
  closed : ∀ n ρ V, (W n).denoteWith ρ V = (W n).denote V

/-! ### The `def:ece` data with and without its denotation clause

`PGenerableWeighting` and `GeneratedRatFeature` are two renderings of the same paper
notion, `def:ece`: the `def:ece` progression data *without* and *with* its denotation
clause.  Both meter the feature serialization by `BigSpliceStream`, both cap the rank at
the day, both demand closure; they differ only in `GeneratedRatFeature`'s extra `denote`
clause tying the feature's value at the market to a rational sequence.  The lemmas below
make that relation a theorem rather than a remark, in both directions.

`def:fuz` has no emission content of its own — it is the `[0,1]` bound together with the
divergent prefix sum — and that content lives below in `DivergentWeighting`. -/

/-- The `def:ece` data forgets its denotation clause to `def:fuz` data. -/
lemma GeneratedRatFeature.toWeighting {P : History} {q : ℕ → ℚ} {feature : ℕ → EF}
    (h : GeneratedRatFeature P q feature) : PGenerableWeighting feature where
  polySeg := h.polyTok
  rank_le := h.rank_le
  closed := h.closed

/-- Conversely, `def:fuz` data plus a denotation is `def:ece` data. -/
lemma PGenerableWeighting.toGeneratedRatFeature {P : History} {q : ℕ → ℚ} {W : ℕ → EF}
    (h : PGenerableWeighting W) (hq : ∀ n, (W n).denote P = (q n : ℝ)) :
    GeneratedRatFeature P q W where
  rank_le := h.rank_le
  polyTok := h.polySeg
  closed := h.closed
  denote := hq

/-- **`def:fuz` is `def:ece` minus the denotation clause**, exactly.  The
`def:fuz` / `def:ece` annotations themselves sit on `PGenerableWeighting` and
`GeneratedRatFeature`; this is the bridge between them. -/
lemma pGenerableWeighting_iff {P : History} {q : ℕ → ℚ} {W : ℕ → EF} :
    GeneratedRatFeature P q W ↔
      PGenerableWeighting W ∧ ∀ n, (W n).denote P = (q n : ℝ) :=
  ⟨fun h => ⟨h.toWeighting, h.denote⟩, fun h => h.1.toGeneratedRatFeature h.2⟩

/-- Operational certificate for the paper's efficiently computable positive calibration
widths: exactly tex:1193-1195's "`⟨δ⟩` is an e.c. sequence of positive rationals", and
nothing more.  Efficient codeability of the reciprocal `1/δ` is *derived* from these two
(`PolyRatCodes.inv_of_pos`, `PolyPositiveWidths.inverse_codes`), never assumed. -/
structure PolyPositiveWidths (δ : ℕ → ℚ) : Prop where
  codes : DigitRatCodes δ
  positive : ∀ n, 0 < (δ n : ℝ)

/-- The reciprocal widths are efficiently codeable, *derived* from the paper's two
hypotheses rather than assumed alongside them. -/
lemma PolyPositiveWidths.inverse_codes {δ : ℕ → ℚ} (h : PolyPositiveWidths δ) :
    DigitRatCodes (fun n => 1 / δ n) :=
  h.codes.inv_of_pos (fun n => by exact_mod_cast h.positive n)

/-! ## The calibration selector -/

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

/-- The calibration indicator is a ℙ-generable weighting, from the paper's own data.

tex:1188 *asserts* that `ctsInd[δ](a < x < b)` is an expressible `[0,1]`-feature; this
proves it, from the `thm:simcal` hypotheses "`⟨φ⟩` is an e.c. sequence" and "`⟨δ⟩` is an
e.c. sequence of positive rationals".  It is the second discharge (with
`AffineCombination.sentenceAffine_polySequence`) that takes `AffineCombination.simcal`'s
argument list back to the paper's.
Paper node: `thm:simcal` -/
lemma calibrationIndicator_pgenerable
    (φ : ℕ → Sentence) (a b : ℚ) (δ : ℕ → ℚ)
    (hφ : BigSentenceCodes φ) (hδ : PolyPositiveWidths δ) :
    PGenerableWeighting (calibrationIndicator φ a b δ) := by
  have hprice := BigSpliceStream.serialize_price
    hφ PolyFueled.id PolyFueled.id
  have hinv : BigSpliceStream (fun n => (EF.const (1 / δ n)).serialize) :=
    BigSpliceStream.serialize_const_write hδ.inverse_codes.toBigDigits
  have hlowerRaw := BigSpliceStream.serialize_mul
    (BigSpliceStream.serialize_add hprice
      (BigSpliceStream.serialize_const (-a))) hinv
  have hupperRaw := BigSpliceStream.serialize_mul
    (BigSpliceStream.serialize_add
      (BigSpliceStream.serialize_const b)
      (BigSpliceStream.serialize_mul
        (BigSpliceStream.serialize_const (-1)) hprice)) hinv
  refine
    { polySeg := BigSpliceStream.serialize_efMin
        (BigSpliceStream.serialize_clip01 hlowerRaw)
        (BigSpliceStream.serialize_clip01 hupperRaw)
      rank_le := ?_
      closed := ?_ }
  · intro n
    simp [calibrationIndicator, calibrationLower, calibrationUpper, EF.rank]
  · intro n ρ V
    simp [calibrationIndicator, calibrationLower, calibrationUpper, clip01, efMin,
      EF.denoteWith, EF.denote]

/-- The calibration selector takes values in `[0,1]` at every market and on every day.
This is exactly the range half of the `DivergentWeighting (calibrationIndicator φ a b δ) P`
hypothesis that every calibration endpoint takes; the other half, divergence of the prefix
sums, is genuinely a hypothesis about the market. -/
lemma calibrationIndicator_mem (φ : ℕ → Sentence) (a b : ℚ)
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
lemma calibrationIndicator_pos_imp
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

/-! ## Limit points -/

/-- “`x` is a limit point of the sequence `f`”, in the standard subsequential sense.
This is Mathlib's map-cluster-point notion along `atTop`; first countability makes it
equivalent to the existence of a strictly increasing convergent subsequence. -/
abbrev HasLimitPoint (f : ℕ → ℝ) (x : ℝ) : Prop :=
  MapClusterPt x atTop f

/-- A nonzero fixed scale does not change whether zero is a subsequential limit. -/
lemma hasLimitPoint_zero_of_const_mul
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

lemma HasLimitPoint.exists_subseq {f : ℕ → ℝ} {x : ℝ}
    (h : HasLimitPoint f x) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (f ∘ ψ) atTop (𝓝 x) :=
  TopologicalSpace.FirstCountableTopology.tendsto_subseq h

lemma hasLimitPoint_of_convergesTo {f : ℕ → ℝ} {x : ℝ}
    (h : ConvergesTo f x) : HasLimitPoint f x :=
  h.mapClusterPt

lemma convergesTo_eq_of_hasLimitPoint {f : ℕ → ℝ} {x y : ℝ}
    (hy : ConvergesTo f y) (hx : HasLimitPoint f x) : x = y := by
  obtain ⟨ψ, hψ, hψx⟩ := hx.exists_subseq
  have hψy : Tendsto (f ∘ ψ) atTop (𝓝 y) :=
    hy.comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hψx hψy

/-- If a real sequence returns arbitrarily late to both sides of zero and its adjacent
jumps vanish, it has zero as a limit point.  This is the exact crossing argument used in
the paper after the two one-sided recurring-unbiasedness trader contradictions. -/
lemma hasLimitPoint_zero_of_two_sided_recurring (f : ℕ → ℝ)
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
lemma calibration_limitPoint_transfer
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
lemma calibration_convergent_limit_mem
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
    (hδpos : ∀ n, 0 < (δ n : ℝ))
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
    have hs := calibrationIndicator_pos_imp φ a b δ hδpos P i hi
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
lemma weightedExposure_tendsto_atTop_of_eventually_negative_bias
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

/-! ## Capped weighted affine runs -/

namespace AffineCombination

/-! ### The run rate and its emitters -/

/-- Canonical slowly varying run rate.  `scale` is chosen once from the alleged bias
gap; the `k+1` denominator makes the finite-prefix charge vanish uniformly in the family
index while remaining exactly rational and polynomially codeable. -/
def biasRunRate (scale k : ℕ) : ℚ :=
  1 / (((scale + 1) * (k + 1) : ℕ) : ℚ)

lemma biasRunRate_codes (scale : ℕ) : PolyRatCodes (biasRunRate scale) := by
  obtain ⟨cinv, hinv⟩ := encode_inv_nat_polyFueled
  obtain ⟨cmul, hmul⟩ := mulc_polyFueled (scale + 1)
  have harg := hmul.comp PolyFueled.id.succ_comp
  refine ⟨_, (hinv.comp harg).of_eq (fun n => ?_)⟩
  simp [biasRunRate, Nat.mul_comm]

lemma biasRunRate_pos (scale k : ℕ) : 0 < (biasRunRate scale k : ℝ) := by
  simp [biasRunRate]
  positivity

lemma biasRunRate_le_one (scale k : ℕ) : (biasRunRate scale k : ℝ) ≤ 1 := by
  simp only [biasRunRate, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  have hden : (1 : ℝ) ≤ (((scale + 1) * (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact (div_le_one (zero_lt_one.trans_le hden)).2 hden

lemma biasRunRate_mul_index_le (scale k : ℕ) :
    (biasRunRate scale k : ℝ) * k ≤ 1 / (scale + 1 : ℝ) := by
  simp only [biasRunRate, Rat.cast_div, Rat.cast_one,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hs : 0 < (scale : ℝ) + 1 := by positivity
  have hk : 0 < (k : ℝ) + 1 := by positivity
  push_cast
  field_simp [ne_of_gt hs, ne_of_gt hk]
  nlinarith

/-- Family-uniform token emitter for the fractional-weight recurrence: the family index is
carried through every recurrence body, so a single program covers all pairs `⟨k,n⟩` rather
than one program per fixed attempted-weight stream. -/
lemma fractionalFamilyFeatureWeight_polySeg
    (occupancy : ℕ → ℕ → EF) (α : ℕ → ℕ → EF)
    (hα : BigSpliceStream (fun z => (α z.unpair.1 z.unpair.2).serialize))
    (hocc : BigSpliceStream (fun z =>
      (occupancy z.unpair.2 z.unpair.1).serialize)) :
    BigSpliceStream (fun z =>
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
  have hvar : BigSpliceStream
      (fun z => (EF.var (day z - 1 - component z)).serialize) :=
    BigSpliceStream.serialize_var hidx
  have hαterm : BigSpliceStream
      (fun z => (α (family z) (component z)).serialize) :=
    BigSpliceStream.of_eq (hα.comp (hfamily.pair hcomponent)) (fun z => by
      simp [family, component])
  have hoccterm : BigSpliceStream
      (fun z => (occupancy (component z) (day z)).serialize) :=
    BigSpliceStream.of_eq (hocc.comp (hday.pair hcomponent)) (fun z => by
      simp [day, component])
  have hterm : BigSpliceStream (fun z => (term z).serialize) :=
    BigSpliceStream.serialize_mul (BigSpliceStream.serialize_mul hvar hαterm) hoccterm
  have hterms : BigSpliceStream (fun u =>
      (List.range u.unpair.2).flatMap
        (fun i => (term (Nat.pair u i)).serialize)) :=
    BigSpliceStream.concatVar hterm PolyFueled.right
  have hzero : BigSpliceStream (fun _ => (EF.const 0).serialize) :=
    BigSpliceStream.serialize_const 0
  have haddTags : BigSpliceStream (fun u => List.replicate u.unpair.2 2) :=
    BigSpliceStream.repeatTag 2 (by norm_num) PolyFueled.right
  have hsumRaw := (hterms.append hzero).append haddTags
  have hsum : BigSpliceStream (fun u =>
      (ROIBudget.sumFeatures (List.ofFn (fun i : Fin u.unpair.2 =>
        term (Nat.pair u i)))).serialize) := by
    refine BigSpliceStream.of_eq hsumRaw ?_
    intro u
    rw [ROIBudget.serialize_sumFeatures]
    simp only [List.length_ofFn]
    congr 2
    rw [← List.map_coe_finRange_eq_range]
    rw [List.flatMap_map]
    simp only [List.ofFn_eq_map, List.flatMap_map]
  have hone : BigSpliceStream (fun _ => (EF.const 1).serialize) :=
    BigSpliceStream.serialize_const 1
  have hnegone : BigSpliceStream (fun _ => (EF.const (-1)).serialize) :=
    BigSpliceStream.serialize_const (-1)
  have hbodyRaw := BigSpliceStream.serialize_add hone
    (BigSpliceStream.serialize_mul hnegone hsum)
  have hbody : BigSpliceStream (fun u =>
      (ROIBudget.fractionalWeightBody occupancy (α u.unpair.1) u.unpair.2).serialize) := by
    refine BigSpliceStream.of_eq hbodyRaw ?_
    intro u
    simp only [ROIBudget.fractionalWeightBody, term, family, day, component,
      Nat.unpair_pair]
  have hcanonical :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hbodies : BigSpliceStream (fun z =>
      (List.range (z.unpair.2 + 1)).flatMap (fun j =>
        (ROIBudget.fractionalWeightBody occupancy (α z.unpair.1) j).serialize)) := by
    refine BigSpliceStream.of_eq
      (BigSpliceStream.concatVar (hbody.comp hcanonical)
        PolyFueled.right.succ_comp) ?_
    intro z
    simp only [Nat.unpair_pair]
  have hvar0 : BigSpliceStream (fun _ => (EF.var 0).serialize) :=
    BigSpliceStream.serialize_var (PolyFueled.const 0)
  have htags : BigSpliceStream (fun z => List.replicate (z.unpair.2 + 1) 8) :=
    BigSpliceStream.repeatTag 8 (by norm_num) PolyFueled.right.succ_comp
  refine BigSpliceStream.of_eq ((hbodies.append hvar0).append htags) ?_
  intro z
  rw [ROIBudget.fractionalSharedFeatureWeight,
    ROIBudget.fractionalSharedWeights_serialize]
  rw [List.range_eq_range']

/-- The attempted purchase weight for family member `k` on day `n`: zero before launch,
then `rateₖ · Wₙ`. -/
def biasRunAttempt (W : ℕ → EF) (rate : ℕ → ℚ) (k n : ℕ) : EF :=
  if k ≤ n then EF.mul (EF.const (rate k)) (W n) else EF.const 0

lemma biasRunAttempt_family_polySeg {W : ℕ → EF}
    (hW : PGenerableWeighting W) (rate : ℕ → ℚ) (hrate : PolyRatCodes rate) :
    BigSpliceStream (fun z =>
      (biasRunAttempt W rate z.unpair.1 z.unpair.2).serialize) := by
  have hrateSeg : BigSpliceStream (fun z => (EF.const (rate z.unpair.1)).serialize) :=
    (BigSpliceStream.serialize_const_comp hrate).comp PolyFueled.left
  have hWSeg : BigSpliceStream (fun z => (W z.unpair.2).serialize) :=
    hW.polySeg.comp PolyFueled.right
  have hlive := BigSpliceStream.serialize_mul hrateSeg hWSeg
  have hzero : BigSpliceStream (fun _ => (EF.const 0).serialize) :=
    BigSpliceStream.serialize_const 0
  have htest := subc_polyFueled.comp
    (PolyFueled.right.succ_comp.pair PolyFueled.left)
  refine BigSpliceStream.of_eq (BigSpliceStream.ifZero hzero hlive htest) ?_
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

/-- The capped purchase coefficient.  `fractionalWeight` is the straight-line capital
recurrence; multiplying it by the attempted weight gives the actual number of copies
bought on day `n`. -/
def biasRunCoefficient (As : ℕ → AffineCombination) (W : ℕ → EF)
    (rate : ℕ → ℚ) (k n : ℕ) : EF :=
  EF.mul
    (ROIBudget.fractionalSharedFeatureWeight (biasRunOccupancy As)
      (biasRunAttempt W rate k) n)
    (biasRunAttempt W rate k n)

lemma biasRunCoefficient_family_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (hrate : PolyRatCodes rate) :
    BigSpliceStream (fun z =>
      (biasRunCoefficient As W rate z.unpair.1 z.unpair.2).serialize) := by
  have hattempt := biasRunAttempt_family_polySeg hW rate hrate
  have hocc : BigSpliceStream (fun z =>
      (biasRunOccupancy As z.unpair.2 z.unpair.1).serialize) := by
    simpa [biasRunOccupancy] using h.magnitudeFeature_polySeg.comp PolyFueled.right
  have hweight := fractionalFamilyFeatureWeight_polySeg
    (biasRunOccupancy As) (biasRunAttempt W rate) hattempt hocc
  exact BigSpliceStream.serialize_mul hweight hattempt

/-- Semantic form of the actual capped purchase coefficient. -/
noncomputable def biasRunGamma (As : ℕ → AffineCombination) (W : ℕ → EF)
    (rate : ℕ → ℚ) (P : History) (k n : ℕ) : ℝ :=
  ROIBudget.fractionalWeight
      (fun i _d => (As i).magnitude P)
      (biasRunAttemptValue W rate P k) n *
    biasRunAttemptValue W rate P k n

lemma biasRunAttempt_rank_le {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) :
    (biasRunAttempt W rate k n).rank ≤ n := by
  by_cases hkn : k ≤ n
  · simp [biasRunAttempt, hkn, EF.rank, hW.rank_le n]
  · simp [biasRunAttempt, hkn]

lemma biasRunAttempt_closed {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) (ρ : List ℝ) (P : History) :
    (biasRunAttempt W rate k n).denoteWith ρ P =
      (biasRunAttempt W rate k n).denote P := by
  by_cases hkn : k ≤ n
  · simp only [biasRunAttempt, hkn, if_true, EF.denoteWith, EF.denote_mul,
      EF.denote_const, Pi.mul_apply]
    rw [hW.closed n ρ P]
  · simp [biasRunAttempt, hkn, EF.denote]

lemma biasRunOccupancy_rank_le {As : ℕ → AffineCombination}
    (h : PolySequence As) (i n : ℕ) (hin : i ≤ n) :
    (biasRunOccupancy As i n).rank ≤ n := by
  exact ((As i).magnitudeFeature_rank_le (h.terms_rank i)).trans hin

lemma biasRunOccupancy_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (i n : ℕ) (ρ : List ℝ) (P : History) :
    (biasRunOccupancy As i n).denoteWith ρ P =
      (biasRunOccupancy As i n).denote P :=
  h.magnitudeFeature_closed i ρ P

lemma biasRunCoefficient_rank_le {As : ℕ → AffineCombination}
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

lemma biasRunCoefficient_denote {As : ℕ → AffineCombination}
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

lemma biasRunAttemptValue_nonneg
    {W : ℕ → EF} {P : History} (hW : DivergentWeighting W P)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ)) (k n : ℕ) :
    0 ≤ biasRunAttemptValue W rate P k n := by
  by_cases hkn : k ≤ n
  · simp [biasRunAttemptValue, biasRunAttempt, hkn, EF.denote_mul,
      mul_nonneg (hrate0 k) (hW.1 n).1]
  · simp [biasRunAttemptValue, biasRunAttempt, hkn, EF.denote]

lemma biasRunAttemptValue_le_one
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
lemma biasRunAttemptedRisk_tendsto_atTop
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
The bound comes from the fractional recurrence itself, not from a hypothesis. -/
lemma biasRun_magnitudePrefix_le_one
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

/-- A run launched on day `k` holds nothing before day `k`. -/
lemma biasRunGamma_eq_zero_of_lt
    {As : ℕ → AffineCombination} {W : ℕ → EF} {P : History}
    (rate : ℕ → ℚ) {k n : ℕ} (hnk : n < k) :
    biasRunGamma As W rate P k n = 0 := by
  simp [biasRunGamma, biasRunAttemptValue, biasRunAttempt, Nat.not_le.2 hnk]

lemma biasRunGamma_nonneg
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

lemma biasRunGamma_le_one
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

lemma biasRun_magnitudePrefix_eq_one_sub_weight
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

lemma biasRun_weight_succ
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
lemma biasRun_truthProfitPrefix_lower_of_surplus
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

/-- If the uncapped attempted risk has divergent total mass, the fractional cap uses its
entire unit budget: actual run magnitude tends to one.  The remaining budget is antitone;
if it stayed above `ε`, actual allocation would dominate `ε` times a divergent
attempted-risk sum, contradicting the unit cap. -/
lemma biasRun_magnitudePrefix_tendsto_one
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

/-! ### The capped-run trader -/

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

/-- The launch-gated per-day trade count of `biasRunTrader`, at the paired index
`z = ⟨k, n⟩`: family member `k` places one trade per term of `As n` on days `n ≥ k` and none
before.  This is the count component of `biasRunTrader_polyTrade`'s `PolyTradeEmulatable`
record. -/
def biasRunTradeCount {As : ℕ → AffineCombination}
    (h : PolySequence As) (z : ℕ) : ℕ :=
  if z.unpair.1 ≤ z.unpair.2 then h.termCount z.unpair.2 else 0

/-- The traded coefficient of `biasRunTrader` at the flattened index `z = ⟨⟨k, n⟩, j⟩`: the
run coefficient of member `k` on day `n` times the `j`-th term coefficient of `As n`.  This
is the coefficient component of `biasRunTrader_polyTrade`'s `PolyTradeEmulatable` record. -/
def biasRunTradeCoefficient {As : ℕ → AffineCombination}
    (h : PolySequence As) (W : ℕ → EF) (rate : ℕ → ℚ) (z : ℕ) : EF :=
  EF.mul
    (biasRunCoefficient As W rate z.unpair.1.unpair.1 z.unpair.1.unpair.2)
    (h.coefficient (Nat.pair z.unpair.1.unpair.2 z.unpair.2))

/-- The traded sentence of `biasRunTrader` at the flattened index `z = ⟨⟨k, n⟩, j⟩`: the
`j`-th sentence of `As n`, independent of the family member `k`.  This is the sentence
component of `biasRunTrader_polyTrade`'s `PolyTradeEmulatable` record. -/
def biasRunTradeSentence {As : ℕ → AffineCombination}
    (h : PolySequence As) (z : ℕ) : Sentence :=
  h.sentence (Nat.pair z.unpair.1.unpair.2 z.unpair.2)

lemma biasRunTradeCount_poly {As : ℕ → AffineCombination}
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

lemma biasRunTradeCoefficient_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (hrate : PolyRatCodes rate) :
    BigSpliceStream (fun z =>
      (biasRunTradeCoefficient h W rate z).serialize) := by
  have hk := PolyFueled.left.comp PolyFueled.left
  have hn := PolyFueled.right.comp PolyFueled.left
  have hj := PolyFueled.right
  have hrun : BigSpliceStream (fun z =>
      (biasRunCoefficient As W rate z.unpair.1.unpair.1
        z.unpair.1.unpair.2).serialize) := by
    simpa only [Nat.unpair_pair] using
      (biasRunCoefficient_family_polySeg h hW rate hrate).comp (hk.pair hn)
  have hbase : BigSpliceStream (fun z =>
      (h.coefficient (Nat.pair z.unpair.1.unpair.2 z.unpair.2)).serialize) := by
    simpa only [Nat.unpair_pair] using h.coefficient_poly.comp (hn.pair hj)
  simpa only [biasRunTradeCoefficient] using
    BigSpliceStream.serialize_mul hrun hbase

lemma biasRunTradeSentence_poly {As : ℕ → AffineCombination}
    (h : PolySequence As) :
    BigSentenceCodes (biasRunTradeSentence h) := by
  have hn := PolyFueled.right.comp PolyFueled.left
  have hj := PolyFueled.right
  exact (h.sentence_poly.comp (hn.pair hj)).of_eq (fun _ => rfl)

lemma biasRunTrader_trades_eq {As : ℕ → AffineCombination}
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
  have hcoeff := biasRunTradeCoefficient_polySeg h hW rate hrate
  have hzero : ∀ k n, n < k →
      (((biasRunTrader h hW rate) k).strat n).trades = [] := by
    intro k n hnk
    simp [biasRunTrader, Nat.not_le.mpr hnk]
  exact
    { launchGated := hzero
      tradeCount := biasRunTradeCount h
      coefficient := biasRunTradeCoefficient h W rate
      sentence := biasRunTradeSentence h
      tradeCount_poly := ⟨ccount, hcount⟩
      coefficient_poly := hcoeff
      sentence_poly := biasRunTradeSentence_poly h
      trades_eq := biasRunTrader_trades_eq h hW rate }

@[simp] lemma biasRunTrader_before {As : ℕ → AffineCombination}
    (h : PolySequence As) {W : ℕ → EF} (hW : PGenerableWeighting W)
    (rate : ℕ → ℚ) (k n : ℕ) (hnk : n < k) :
    ((biasRunTrader h hW rate k).strat n).trades = [] := by
  simp [biasRunTrader, Nat.not_le.mpr hnk]

lemma biasRunTrader_value {As : ℕ → AffineCombination}
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

lemma biasRunTrader_netWorth {As : ℕ → AffineCombination}
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

lemma biasRunTrader_dayMagnitude {As : ℕ → AffineCombination}
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
lemma biasRunTrader_summable_and_magnitude_le_one
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

lemma biasRunTrader_magnitude_eq_one_of_attemptedRisk
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
    exact hraw
  exact tendsto_nhds_unique htoMagnitude hprefTrader

/-! ### ROI accounting under persistent bias -/

/-- An approximately determined affine value differs from its diagonal market price by at
most its share magnitude plus the determination error.  The completed-theory world needed
for this comparison is obtained by the compactness theorem, not assumed separately for
each member. -/
lemma ApproxDeterminedViaTheory.abs_truth_sub_price_le_magnitude
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {P : History} {DP : DeductiveProcess} {truth e : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth e)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    |truth n - (As n).price P n| ≤ (As n).magnitude P + e n := by
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  have hval := (As n).abs_value_sub_price_le_magnitude P v.payout n
    (hpoly.terms_rank n) (fun φ => by
      by_cases hφ : v.Holds φ
      · exact Or.inr (by simp [PCWorld.payout, hφ])
      · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP n)
  have hnear := hdet n v hv
  rw [abs_le] at hval hnear ⊢
  constructor <;> linarith

lemma DeterminedViaTheory.abs_truth_sub_price_le_magnitude
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {P : History} {DP : DeductiveProcess} {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    |truth n - (As n).price P n| ≤ (As n).magnitude P := by
  simpa using hdet.approx.abs_truth_sub_price_le_magnitude hpoly hworld hP n

/-- A full-risk capped run with an Abel-prefix surplus has genuine ROI.  Compactness is
used only for the finitely many large early positions; the summable risk tail is controlled
uniformly by magnitude.  Thus no effective settlement oracle is hidden in this semantic
step.

Under approximate determination the run additionally forfeits the determination error it
has bought.  `hslack` says that error is at most a `c`-fraction of the share magnitude from
the run's launch day onwards, so the whole forfeit is at most `c`: the trader's total share
magnitude is one, and it holds no shares before day `k`. -/
lemma ApproxDeterminedViaTheory.biasRunTrader_hasROI_of_surplus
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herr0 : ∀ i, 0 ≤ err i)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (rate : ℕ → ℚ) (hrate0 : ∀ k, 0 ≤ (rate k : ℝ))
    (hrate1 : ∀ k, (rate k : ℝ) ≤ 1)
    (ρ δ c : ℝ) (hρ0 : 0 ≤ ρ) (hc0 : 0 ≤ c) (k : ℕ)
    (hslack : ∀ i, k ≤ i → err i ≤ c * (As i).magnitude P)
    (hsurplus : ∀ n,
      -δ ≤ prefixSum (fun i =>
        biasRunAttemptValue W rate P k i *
          ((truth i - (As i).price P i) - ρ * (As i).magnitude P)) n)
    (hrisk : Tendsto
      (prefixSum (fun i =>
        biasRunAttemptValue W rate P k i * (As i).magnitude P)) atTop atTop) :
    HasROI (biasRunTrader hpoly hWgen rate k) P DP (ρ - δ - c) := by
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
        |(As i).value P v.payout - truth i| < err i + e := by
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
  -- The determination error the run has bought, day by day.  It vanishes before launch
  -- and is at most `c` times that day's share magnitude afterwards, so the whole forfeit
  -- over the run's unit of magnitude is at most `c`.
  have hslack0 : ∀ i, 0 ≤ biasRunGamma As W rate P k i * err i :=
    fun i => mul_nonneg (hgamma0 i) (herr0 i)
  have hslackAll : ∑ i ∈ Finset.range (n + 1),
      biasRunGamma As W rate P k i * err i ≤ c := by
    have hterm : ∀ i ∈ Finset.range (n + 1),
        biasRunGamma As W rate P k i * err i ≤
          c * (biasRunGamma As W rate P k i * (As i).magnitude P) := by
      intro i _
      by_cases hik : k ≤ i
      · calc biasRunGamma As W rate P k i * err i
            ≤ biasRunGamma As W rate P k i * (c * (As i).magnitude P) :=
              mul_le_mul_of_nonneg_left (hslack i hik) (hgamma0 i)
          _ = c * (biasRunGamma As W rate P k i * (As i).magnitude P) := by ring
      · rw [biasRunGamma_eq_zero_of_lt rate (Nat.lt_of_not_le hik)]
        simp
    calc ∑ i ∈ Finset.range (n + 1), biasRunGamma As W rate P k i * err i
        ≤ ∑ i ∈ Finset.range (n + 1),
            c * (biasRunGamma As W rate P k i * (As i).magnitude P) :=
          Finset.sum_le_sum hterm
      _ = c * ∑ i ∈ Finset.range (n + 1),
            biasRunGamma As W rate P k i * (As i).magnitude P := by
          rw [Finset.mul_sum]
      _ ≤ c * 1 := by
          have hcap := biasRun_magnitudePrefix_le_one hWdiv hmag rate hrate0 hrate1 k n
          change ∑ i ∈ Finset.range (n + 1),
            biasRunGamma As W rate P k i * (As i).magnitude P ≤ 1 at hcap
          exact mul_le_mul_of_nonneg_left hcap hc0
      _ = c := mul_one _
  have hslackSplit :
      (∑ i ∈ Finset.range (M + 1), biasRunGamma As W rate P k i * err i) +
        ∑ i ∈ Finset.Ico (M + 1) (n + 1),
          biasRunGamma As W rate P k i * err i ≤ c := by
    rw [Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hnM)]
    exact hslackAll
  have hearlySum : -(η / 8) -
      (∑ i ∈ Finset.range (M + 1), biasRunGamma As W rate P k i * err i) ≤
      ∑ i ∈ Finset.range (M + 1),
        biasRunGamma As W rate P k i *
          ((As i).value P v.payout - truth i) := by
    have hpt : ∀ i ∈ Finset.range (M + 1),
        -e - biasRunGamma As W rate P k i * err i ≤
          biasRunGamma As W rate P k i *
            ((As i).value P v.payout - truth i) := by
      intro i hi
      have hclose := hNe n hnNe i hi v hv
      rw [abs_lt] at hclose
      have hge := mul_nonneg (hgamma0 i)
        (show 0 ≤ ((As i).value P v.payout - truth i) + (err i + e) by
          linarith [hclose.1])
      have hge' := mul_nonneg (show 0 ≤ 1 - biasRunGamma As W rate P k i by
          linarith [hgamma1 i]) (le_of_lt he)
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range] at hsum
    have hMe : (M + 1) • (-e) = -(η / 8) := by
      simp only [nsmul_eq_mul, e]
      push_cast
      field_simp
    rw [hMe] at hsum
    exact hsum
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
  have htailSum : -(η / 4) -
      (∑ i ∈ Finset.Ico (M + 1) (n + 1),
        biasRunGamma As W rate P k i * err i) ≤
      ∑ i ∈ Finset.Ico (M + 1) (n + 1),
        biasRunGamma As W rate P k i *
          ((As i).value P v.payout - truth i) := by
    have hpoint : ∀ i,
        -(2 * (biasRunGamma As W rate P k i * (As i).magnitude P)) -
            biasRunGamma As W rate P k i * err i ≤
          biasRunGamma As W rate P k i *
            ((As i).value P v.payout - truth i) := by
      intro i
      have hwprice := (As i).abs_value_sub_price_le_magnitude P v.payout i
        (hpoly.terms_rank i) (fun φ => by
          by_cases hφ : v.Holds φ
          · exact Or.inr (by simp [PCWorld.payout, hφ])
          · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP i)
      have htprice := hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP i
      have hdiff : -2 * (As i).magnitude P - err i ≤
          (As i).value P v.payout - truth i := by
        rw [abs_le] at hwprice htprice
        linarith
      have hprod := mul_nonneg (hgamma0 i)
        (show 0 ≤ (As i).value P v.payout - truth i +
          2 * (As i).magnitude P + err i by linarith)
      nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.Ico (M + 1) (n + 1)) => hpoint i)
    rw [Finset.sum_sub_distrib] at hsum
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
  have herror : -(3 * η / 8) - c ≤ prefixSum (fun i =>
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
This is the specialization of the statistical forcing estimate to affine values
approximately determined by the completed deductive theory.  `herrmag` — the determination
error never exceeds the day's share magnitude — is free for a threshold mesh, whose value
spread between any two worlds is bounded by its own coefficient sum. -/
lemma ApproxDeterminedViaTheory.weightedMagnitude_tendsto_atTop_of_negative_bias
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} {P : History} {DP : DeductiveProcess} {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herrmag : ∀ i, err i ≤ (As i).magnitude P)
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
  have hdouble : Tendsto
      (prefixSum (fun i => (W i).denote P * (2 * (As i).magnitude P)))
      atTop atTop := by
    apply weightedExposure_tendsto_atTop_of_eventually_negative_bias
      (fun i => (W i).denote P) (fun i => (As i).price P i) truth
        (fun i => 2 * (As i).magnitude P) ε
    · exact fun n => (hWdiv.1 n).1
    · intro n
      have := (le_abs_self (truth n - (As n).price P n)).trans
        (hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP n)
      linarith [herrmag n]
    · exact hWdiv.2
    · exact hε
    · exact hbias
  have hhalf : ∀ n, prefixSum (fun i => (W i).denote P * (2 * (As i).magnitude P)) n =
      2 * prefixSum (fun i => (W i).denote P * (As i).magnitude P) n := by
    intro n
    simp only [prefixSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hd2 := (hdouble.congr hhalf).const_mul_atTop (show (0:ℝ) < 1 / 2 by norm_num)
  refine hd2.congr fun n => ?_
  ring

lemma DeterminedViaTheory.weightedMagnitude_tendsto_atTop_of_negative_bias
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
      atTop atTop :=
  hdet.approx.weightedMagnitude_tendsto_atTop_of_negative_bias hpoly
    (fun i => (As i).magnitude_nonneg P) hWdiv hworld hP ε hε hbias

/-- Eventually, every sufficiently late launched run has a uniform Abel-prefix surplus
bound.  The only loss is its finite pre-launch prefix, at most `rateₖ · k`; the persistent
global bias pays for every later prefix. -/
lemma ApproxDeterminedViaTheory.biasRun_surplus_eventually
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} {P : History} {DP : DeductiveProcess} {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herrmag : ∀ i, err i ≤ (As i).magnitude P)
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
      -(rate k : ℝ) * (2 * k) ≤ prefixSum (fun i =>
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
  change -(rate k : ℝ) * (2 * k) ≤
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
        ∑ i ∈ Finset.range k, w i * (x i - ρ * m i) ≤ 2 * k := by
      calc
        ∑ i ∈ Finset.range k, w i * (x i - ρ * m i) ≤
            ∑ _i ∈ Finset.range k, (2 : ℝ) := by
              apply Finset.sum_le_sum
              intro i _
              have hxi : x i ≤ m i + err i :=
                (le_abs_self (x i)).trans
                  (hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP i)
              have hexpr : x i - ρ * m i ≤ 2 := by
                have hm0 := (As i).magnitude_nonneg P
                have hrhom0 := mul_nonneg hρ0 hm0
                linarith [hmag i, herrmag i]
              calc
                w i * (x i - ρ * m i) ≤ w i * 2 :=
                  mul_le_mul_of_nonneg_left hexpr (hWdiv.1 i).1
                _ ≤ 1 * 2 := by
                  have := (hWdiv.1 i).2
                  nlinarith
                _ = 2 := by ring
        _ = 2 * k := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
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

/-- Exposure consequence for one negative-bias run: under persistent negative bias, every
positive-rate launched component has total share magnitude exactly one.  This is weaker
than ROI — which additionally needs the plausible-world payoff lower bound — but it settles
the normalization, finite-prefix, and summability side conditions. -/
lemma ApproxDeterminedViaTheory.biasRunTrader_magnitude_eq_one_of_negative_bias
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herrmag : ∀ i, err i ≤ (As i).magnitude P)
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
    hpoly herrmag hWdiv hworld hP ε hε hbias
  have hrisk := biasRunAttemptedRisk_tendsto_atTop As rate P k hratek hweighted
  exact biasRunTrader_magnitude_eq_one_of_attemptedRisk hpoly hWgen hWdiv hmag
    rate hrate0 hrate1 k hrisk

/-- Persistent negative bias yields a uniformly positive-ROI tail of the canonical capped
run family.  The scale is chosen once from the alleged bias gap; every sufficiently late
member then has `ε/4` ROI and total magnitude one. -/
lemma ApproxDeterminedViaTheory.eventually_biasRunTrader_hasROI
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (hnegl : ErrorNegligible As P err)
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
  obtain ⟨herr0, herrmag, hfrac⟩ := hnegl
  obtain ⟨scale, hscaleNat⟩ := exists_nat_gt (16 / ε)
  have hscale : 1 / (scale + 1 : ℝ) ≤ ε / 16 := by
    have hspos : 0 < (scale : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hspos).2
    have hmul := (div_lt_iff₀ hε).1 hscaleNat
    nlinarith
  have hrate0 : ∀ k, 0 ≤ (biasRunRate scale k : ℝ) :=
    fun k => (biasRunRate_pos scale k).le
  have hrate1 : ∀ k, (biasRunRate scale k : ℝ) ≤ 1 :=
    biasRunRate_le_one scale
  obtain ⟨N, hN⟩ := hdet.biasRun_surplus_eventually hpoly herrmag hWdiv hmag
    hworld hP (biasRunRate scale) hrate0 ε (ε / 2) (by linarith)
      (by linarith) hbias
  obtain ⟨N₀, hN₀⟩ := hfrac (ε / 8) (by linarith)
  refine ⟨scale, max N N₀, fun k hk => ?_⟩
  have hsurplusRaw := hN k ((le_max_left N N₀).trans hk)
  have hcharge : (biasRunRate scale k : ℝ) * (2 * k) ≤ ε / 8 := by
    have := (biasRunRate_mul_index_le scale k).trans hscale
    nlinarith [hrate0 k, Nat.cast_nonneg (α := ℝ) k]
  have hsurplus : ∀ n,
      -(ε / 8) ≤ prefixSum (fun i =>
        biasRunAttemptValue W (biasRunRate scale) P k i *
          ((truth i - (As i).price P i) -
            (ε / 2) * (As i).magnitude P)) n := by
    intro n
    linarith [hsurplusRaw n]
  have hweighted := hdet.weightedMagnitude_tendsto_atTop_of_negative_bias
    hpoly herrmag hWdiv hworld hP ε hε hbias
  have hrisk := biasRunAttemptedRisk_tendsto_atTop As (biasRunRate scale) P k
    (biasRunRate_pos scale k) hweighted
  have hslack : ∀ i, k ≤ i → err i ≤ (ε / 8) * (As i).magnitude P :=
    fun i hi => hN₀ i (((le_max_right N N₀).trans hk).trans hi)
  convert hdet.biasRunTrader_hasROI_of_surplus hpoly hWgen herr0 hWdiv hmag
    hworld hP (biasRunRate scale) hrate0 hrate1 (ε / 2) (ε / 8) (ε / 8)
      (by linarith) (by linarith) k hslack hsurplus hrisk using 1 ; ring

/-! ### The repeatable-ROI tolerance budget -/

/-- Exact rational code for the canonical repeatable-ROI tolerance budget. -/
def roiToleranceRat (i : ℕ) : ℚ := ((1 : ℚ) / 2) ^ (i + 1)

/-- Canonical summable tolerance budget for the repeatable-ROI maturity verifier. -/
noncomputable def roiTolerance (i : ℕ) : ℝ := (roiToleranceRat i : ℝ)

lemma roiTolerance_eq (i : ℕ) :
    roiTolerance i = ((1 : ℝ) / 2) ^ (i + 1) := by
  simp [roiTolerance, roiToleranceRat]

lemma roiTolerance_nonneg (i : ℕ) : 0 ≤ roiTolerance i := by
  rw [roiTolerance_eq]
  positivity

lemma roiTolerance_summable : Summable roiTolerance := by
  apply (summable_geometric_two.mul_right ((1 : ℝ) / 2)).congr
  intro i
  rw [roiTolerance_eq, pow_succ]

/-! ## Recurring unbiasedness and calibration

Everything below is stated against `BiasRunHistoricallyVerifiable`, the one remaining
operational premise.  `Construction/Statistics/HistoricalMaturity.lean` discharges it from
the constructed market and deductive-process computations, and it is there that the
unconditional paper endpoints `AffineCombination.BoundedCombinationSequence.recunbiasedaff`
(`thm:recunbiasedaff`), `AffineCombination.recurringunbiasedness`
(`thm:recurringunbiasedness`) and `AffineCombination.simcal` (`thm:simcal`) stand. -/

/-- The exact remaining operational boundary in the affine recurring-unbiasedness proof:
for every alleged bias gap, a single polynomial Boolean table recognizes historical
maturity certificates for the canonical capped-run family.  Unlike a conclusion-bearing
oracle, the returned object exposes its checker, polynomial clock, soundness, and
eventual-completeness fields through `HistoricalVerifiedMaturitySchedule`.

The paper derives this interface by dovetailing the computable rational market and
deductive-process computations; `Construction.Statistics.HistoricalMaturity` implements
that dovetailer against this predicate. -/
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

/-- Operational consumer for the historical-maturity interface of affine recurring
unbiasedness.  A persistent negative bias produces a tail of unit-magnitude positive-ROI
run traders.  If finite historical maturity claims for that tail have the paper's bounded
verifier, `noRepeatableROI` forces the corresponding `0/1` magnitude progression to tend
to zero, contradicting its eventual value one.

The historical verifier is exposed as a hypothesis here; the construction layer discharges
it from `IsLogicalInductor.marketComputable` and `.processComputable`. -/
lemma ApproxDeterminedViaTheory.not_eventually_weightedBias_lt_of_historicalVerifier
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (hnegl : ErrorNegligible As P err)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
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
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  intro hbias
  obtain ⟨scale, N, hroiTail⟩ := hdet.eventually_biasRunTrader_hasROI
    hpoly hWgen hnegl hWdiv hmag hworld hP ε hε hbias
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
    by_cases hi : N ≤ i <;> simp [α, gateFeature, hi]
  have hαseg : BigSpliceStream (fun i => (α i).serialize) := by
    apply BigSpliceStream.gateFeature (BigSpliceStream.serialize_const 1) N
  have hαclosed : ∀ i ρ V, (α i).denoteWith ρ V = (α i).denote V := by
    intro i ρ V
    by_cases hi : N ≤ i <;>
      simp [α, gateFeature, hi, EF.denote]
  have hαmag : ∀ i, (α i).denote P = (Ts i).magnitude P := by
    intro i
    by_cases hi : N ≤ i
    · simp only [α, gateFeature, hi, if_true, EF.denote_const, Ts,
        gateTraderFamily, baseTs]
      symm
      simpa using
        (hdet.biasRunTrader_magnitude_eq_one_of_negative_bias hpoly hWgen
          hnegl.2.1 hWdiv hmag hworld hP (biasRunRate scale)
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
  simp [α, gateFeature, hlaunch] at hnear

/-- One-sided affine recurring unbiasedness from the isolated historical-verification
interface.  This is the exact `limsup ≥ 0` half of the paper proof. -/
lemma ApproxDeterminedViaTheory.not_eventually_weightedBias_lt
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (hnegl : ErrorNegligible As P err)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hverify : BiasRunHistoricallyVerifiable As hpoly W hWgen P DP)
    (ε : ℝ) (hε : 0 < ε) :
    ¬ ∀ᶠ n in atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε := by
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, (0 : ℝ) < q ∧ (q : ℝ) < ε :=
    exists_rat_btwn hε
  have hnotq := hdet.not_eventually_weightedBias_lt_of_historicalVerifier
    hpoly hWgen hnegl hWdiv hmag hworld (q : ℝ) hq0 roiTolerance
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
lemma ApproxDeterminedViaTheory.recunbiasedaff_of_historicalVerifiers
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth err : ℕ → ℝ}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (hnegl : ErrorNegligible As P err)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hverify : BiasRunHistoricallyVerifiable As hpoly W hWgen P DP)
    (hverifyNeg : BiasRunHistoricallyVerifiable (fun n => (As n).neg)
      hpoly.neg W hWgen P DP) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth) 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).price P i
  let f : ℕ → ℝ := weightedBias w market truth
  have hstep : Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0) := by
    apply weightedAverage_step_tendsto_zero w
      (fun i => market i - truth i) 2
    · exact fun n => (hWdiv.1 n).1
    · exact fun n => (hWdiv.1 n).2
    · intro n
      have hn := hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP n
      rw [abs_sub_comm] at hn
      exact hn.trans (by linarith [hmag n, hnegl.2.1 n])
    · exact hWdiv.2
  have hlower : ∀ ε > 0, ∃ᶠ n in atTop, -ε < f n := by
    intro ε hε
    have hnot := hdet.not_eventually_weightedBias_lt hpoly hWgen hnegl hWdiv
      hmag hworld hverify (ε / 2) (by linarith)
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
    have hnot := hdetNeg.not_eventually_weightedBias_lt hpoly.neg hWgen hnegl.neg hWdiv
      hmagNeg hworld hverifyNeg (ε / 2) (by linarith)
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

/-- Exact `thm:recunbiasedaff` hub: the `err = 0` specialization of the approximate one. -/
lemma DeterminedViaTheory.recunbiasedaff_of_historicalVerifiers
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hverify : BiasRunHistoricallyVerifiable As hpoly W hWgen P DP)
    (hverifyNeg : BiasRunHistoricallyVerifiable (fun n => (As n).neg)
      hpoly.neg W hWgen P DP) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth) 0 :=
  hdet.approx.recunbiasedaff_of_historicalVerifiers hpoly hWgen
    (AffineCombination.errorNegligible_zero As P) hWdiv hmag hworld hverify hverifyNeg

/-- The `thm:recunbiasedaff` shape for an arbitrary bounded-combination sequence, still
conditional on the historical-maturity verifier.  The economic hub above is stated at unit
magnitude; this wrapper performs one canonical positive rational normalization, asks the
operational verifier only for that concrete normalized family, and cancels the scale from the
exact zero-limit-point conclusion.

It carries no `Paper node` line by the file convention stated above: every
`_of_historicalVerifiers` form is conditional, and the node is carried by the unconditional
`AffineCombination.BoundedCombinationSequence.recunbiasedaff` in
`Construction/Statistics/HistoricalMaturity.lean`, which discharges the verifier. -/
theorem BoundedCombinationSequence.recunbiasedaff_of_historicalVerifiers
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
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
      hworld hverify hverifyNeg
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

lemma TheoryTruth.isBoolean {φ : ℕ → Sentence} {DP : DeductiveProcess}
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
unbiasedness, retaining the same explicit historical-verification boundary.  This is the
generic carrier a client with its own historical verifier applies; the unconditional
`thm:recurringunbiasedness` endpoint is `AffineCombination.recurringunbiasedness` in
`Construction/Statistics/HistoricalMaturity.lean`. -/
lemma recurringunbiasedness_of_historicalVerifiers
    (φ : ℕ → Sentence) (hpoly : PolySequence (sentenceAffine φ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} (htruth : TheoryTruth φ DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
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
    hmag hworld hverify hverifyNeg
  simpa using h

/-- Recurring calibration from the ordinary recurring-unbiasedness specialization.  Both
the divergent-case limit point and convergent-case interval guarantee are the exact
paper conclusions; the only remaining representation premise is the named historical
verifier for the sentence family and its negation.  This is the generic carrier a client
with its own verifier applies; the unconditional `thm:simcal` endpoint is
`AffineCombination.simcal` in `Construction/Statistics/HistoricalMaturity.lean`. -/
lemma simcal_of_historicalVerifiers
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (truth : ℕ → ℝ)
    (a b : ℚ) (δ : ℕ → ℚ)
    (hδpos : ∀ n, 0 < (δ n : ℝ))
    (hpoly : PolySequence (sentenceAffine φ))
    (htruth : TheoryTruth φ DP truth)
    (hWgen : PGenerableWeighting (calibrationIndicator φ a b δ))
    (hdiv : DivergentWeighting (calibrationIndicator φ a b δ) P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
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
    htruth hdiv hworld hverify hverifyNeg
  exact simcal_of_recurring_unbiasedness P φ truth a b δ hδpos
    (fun n => htruth.isBoolean hworld n) hdiv hbias

end AffineCombination

end LogicalInduction
