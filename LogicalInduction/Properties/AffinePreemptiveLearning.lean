/-
# `thm:affpolymax` — analytic preemptive-learning hub

This file isolates the order/limit half of Affine Preemptive Learning.  The economic half
constructs an efficiently emulatable family of affine round trips and proves the two
`NoPreemptive*` conditions below via repeatable ROI.  Once those conditions are available,
the paper's two liminf/limsup equalities are purely generic filter arguments.
-/
import LogicalInduction.Affine
import LogicalInduction.ROI
import LogicalInduction.Properties.ExpectationConvergence
import Mathlib.Topology.Order.LiminfLimsup

namespace LogicalInduction

open Filter

/-- Operational “no persistent underpricing” condition.  If the future benchmark is
eventually above `b`, the current value cannot be below the separated threshold `a < b`
infinitely often.  This is exactly the contradiction produced by the buy-low affine
round-trip family. -/
def NoPreemptiveUnderpricing (current future : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, a < b → (∀ᶠ n in atTop, b < future n) →
    ¬ ∃ᶠ n in atTop, current n < a

/-- Dual operational condition: an eventually low future benchmark rules out infinitely
many separated current overprices. -/
def NoPreemptiveOverpricing (current future : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, a < b → (∀ᶠ n in atTop, future n < a) →
    ¬ ∃ᶠ n in atTop, b < current n

/-- Generic liminf half of preemptive learning.  The first inequality is pointwise; the
reverse is precisely `NoPreemptiveUnderpricing`. -/
theorem liminf_eq_of_noPreemptiveUnderpricing
    (current future : ℕ → ℝ)
    (hcurrentBelow : IsBoundedUnder (· ≥ ·) atTop current)
    (hcurrentAbove : IsBoundedUnder (· ≤ ·) atTop current)
    (hfutureBelow : IsBoundedUnder (· ≥ ·) atTop future)
    (hfutureAbove : IsBoundedUnder (· ≤ ·) atTop future)
    (hle : ∀ n, current n ≤ future n)
    (hgap : NoPreemptiveUnderpricing current future) :
    liminf current atTop = liminf future atTop := by
  apply le_antisymm
  · exact liminf_le_liminf (Eventually.of_forall hle) hcurrentBelow
      hfutureAbove.isCobounded_flip
  · by_contra hnot
    have hlt : liminf current atTop < liminf future atTop := lt_of_not_ge hnot
    obtain ⟨a, hca, haf⟩ := exists_between hlt
    obtain ⟨b, hab, hbf⟩ := exists_between haf
    have hfuture : ∀ᶠ n in atTop, b < future n :=
      eventually_lt_of_lt_liminf hbf hfutureBelow
    have hcurrent : ∃ᶠ n in atTop, current n < a :=
      frequently_lt_of_liminf_lt hcurrentAbove.isCobounded_flip hca
    exact hgap a b hab hfuture hcurrent

/-- Generic limsup half, dual to `liminf_eq_of_noPreemptiveUnderpricing`. -/
theorem limsup_eq_of_noPreemptiveOverpricing
    (current future : ℕ → ℝ)
    (hcurrentBelow : IsBoundedUnder (· ≥ ·) atTop current)
    (hcurrentAbove : IsBoundedUnder (· ≤ ·) atTop current)
    (hfutureBelow : IsBoundedUnder (· ≥ ·) atTop future)
    (hfutureAbove : IsBoundedUnder (· ≤ ·) atTop future)
    (hle : ∀ n, future n ≤ current n)
    (hgap : NoPreemptiveOverpricing current future) :
    limsup current atTop = limsup future atTop := by
  apply le_antisymm
  · by_contra hnot
    have hlt : limsup future atTop < limsup current atTop := lt_of_not_ge hnot
    obtain ⟨a, hfa, hac⟩ := exists_between hlt
    obtain ⟨b, hab, hbc⟩ := exists_between hac
    have hfuture : ∀ᶠ n in atTop, future n < a :=
      eventually_lt_of_limsup_lt hfa hfutureAbove
    have hcurrent : ∃ᶠ n in atTop, b < current n :=
      frequently_lt_of_lt_limsup hcurrentBelow.isCobounded_flip hbc
    exact hgap a b hab hfuture hcurrent
  · exact limsup_le_limsup (Eventually.of_forall hle)
      hfutureBelow.isCobounded_flip hcurrentAbove

/-! ## Affine specialization -/

/-- `sup_{m ≥ n} P_m(A_n)`, indexed as `m = n + j`. -/
noncomputable def affineFutureHigh (As : ℕ → AffineCombination) (V : History) (n : ℕ) : ℝ :=
  sSup (Set.range (fun j => (As n).price V (n + j)))

/-- `inf_{m ≥ n} P_m(A_n)`. -/
noncomputable def affineFutureLow (As : ℕ → AffineCombination) (V : History) (n : ℕ) : ℝ :=
  sInf (Set.range (fun j => (As n).price V (n + j)))

/-- Uniform boundedness of all cross-time prices of the affine sequence.  A paper `BCS`
witness implies this from its coefficient `L¹` bound and market prices in `[0,1]`; the
analytic hub records only the consequence it consumes. -/
def BoundedAffinePrices (As : ℕ → AffineCombination) (V : History) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ n m, |(As n).price V m| ≤ B

theorem BoundedAffinePrices.diagonal_le_futureHigh
    {As : ℕ → AffineCombination} {V : History} (h : BoundedAffinePrices As V) (n : ℕ) :
    (As n).price V n ≤ affineFutureHigh As V n := by
  obtain ⟨B, _, hB⟩ := h
  apply le_csSup
  · refine ⟨B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans (hB n (n + j))
  · exact ⟨0, by simp⟩

theorem BoundedAffinePrices.futureLow_le_diagonal
    {As : ℕ → AffineCombination} {V : History} (h : BoundedAffinePrices As V) (n : ℕ) :
    affineFutureLow As V n ≤ (As n).price V n := by
  obtain ⟨B, _, hB⟩ := h
  apply csInf_le
  · refine ⟨-B, ?_⟩
    rintro x ⟨j, rfl⟩
    have := neg_abs_le ((As n).price V (n + j))
    linarith [hB n (n + j)]
  · exact ⟨0, by simp⟩

theorem BoundedAffinePrices.filterBounds
    {As : ℕ → AffineCombination} {V : History} (h : BoundedAffinePrices As V) :
    IsBoundedUnder (· ≥ ·) atTop (fun n => (As n).price V n) ∧
    IsBoundedUnder (· ≤ ·) atTop (fun n => (As n).price V n) ∧
    IsBoundedUnder (· ≥ ·) atTop (affineFutureHigh As V) ∧
    IsBoundedUnder (· ≤ ·) atTop (affineFutureHigh As V) ∧
    IsBoundedUnder (· ≥ ·) atTop (affineFutureLow As V) ∧
    IsBoundedUnder (· ≤ ·) atTop (affineFutureLow As V) := by
  obtain ⟨B, hB0, hB⟩ := h
  have hdiagLo : ∀ n, -B ≤ (As n).price V n := fun n => by
    linarith [neg_abs_le ((As n).price V n), hB n n]
  have hdiagHi : ∀ n, (As n).price V n ≤ B := fun n =>
    (le_abs_self _).trans (hB n n)
  have hhighLo : ∀ n, -B ≤ affineFutureHigh As V n := fun n =>
    (hdiagLo n).trans ((show BoundedAffinePrices As V from ⟨B, hB0, hB⟩).diagonal_le_futureHigh n)
  have hhighHi : ∀ n, affineFutureHigh As V n ≤ B := fun n => by
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro x ⟨j, rfl⟩
      exact (le_abs_self _).trans (hB n (n + j))
  have hlowLo : ∀ n, -B ≤ affineFutureLow As V n := fun n => by
    apply le_csInf
    · exact Set.range_nonempty _
    · rintro x ⟨j, rfl⟩
      linarith [neg_abs_le ((As n).price V (n + j)), hB n (n + j)]
  have hlowHi : ∀ n, affineFutureLow As V n ≤ B := fun n =>
    ((show BoundedAffinePrices As V from ⟨B, hB0, hB⟩).futureLow_le_diagonal n).trans
      (hdiagHi n)
  exact ⟨isBoundedUnder_of_eventually_ge (Eventually.of_forall hdiagLo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hdiagHi),
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hhighLo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hhighHi),
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hlowLo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hlowHi)⟩

/-- The two operational conditions supplied by the affine ROI construction. -/
structure AffineNoPreemptiveGaps (As : ℕ → AffineCombination) (V : History) : Prop where
  underpriced : NoPreemptiveUnderpricing
    (fun n => (As n).price V n) (affineFutureHigh As V)
  overpriced : NoPreemptiveOverpricing
    (fun n => (As n).price V n) (affineFutureLow As V)

/-- Analytic capstone for `thm:affpolymax`.  The remaining construction theorem must derive
`AffineNoPreemptiveGaps` from `[IsLogicalInductor V DP]` for bounded polynomially generated
affine sequences; no limit algebra is duplicated there. -/
theorem affpolymax_of_noPreemptiveGaps
    (As : ℕ → AffineCombination) (V : History)
    (hbounded : BoundedAffinePrices As V)
    (hgap : AffineNoPreemptiveGaps As V) :
    liminf (fun n => (As n).price V n) atTop =
        liminf (affineFutureHigh As V) atTop ∧
      limsup (fun n => (As n).price V n) atTop =
        limsup (affineFutureLow As V) atTop := by
  obtain ⟨hdlo, hdhi, hhlo, hhhi, hllo, hlhi⟩ := hbounded.filterBounds
  constructor
  · exact liminf_eq_of_noPreemptiveUnderpricing _ _ hdlo hdhi hhlo hhhi
      hbounded.diagonal_le_futureHigh hgap.underpriced
  · exact limsup_eq_of_noPreemptiveOverpricing _ _ hdlo hdhi hllo hlhi
      hbounded.futureLow_le_diagonal hgap.overpriced

/-! ## Continuous gradual-sale component

For a component opened on `buyDay`, offset `t` corresponds to market day
`buyDay + t + 1`.  `gradualRemaining t` is the unsold fraction immediately before that
day, and `gradualSellFraction t` is the fraction sold on it.  Each update mentions the
previous state once, so its feature syntax grows linearly rather than exponentially.
-/

namespace AffineCombination

def gradualRemaining (A : AffineCombination) (buyDay : ℕ) (high δ : ℚ) : ℕ → EF
  | 0 => .const 1
  | t + 1 => .mul (A.gradualRemaining buyDay high δ t)
      (oneMinus (sellIndF (A.priceFeature (buyDay + t + 1)) high δ))

def gradualSellFraction (A : AffineCombination) (buyDay : ℕ) (high δ : ℚ)
    (t : ℕ) : EF :=
  .mul (A.gradualRemaining buyDay high δ t)
    (sellIndF (A.priceFeature (buyDay + t + 1)) high δ)

@[simp] theorem gradualRemaining_zero (A : AffineCombination) (buyDay : ℕ)
    (high δ : ℚ) : A.gradualRemaining buyDay high δ 0 = .const 1 := rfl

@[simp] theorem gradualRemaining_succ (A : AffineCombination) (buyDay : ℕ)
    (high δ : ℚ) (t : ℕ) :
    A.gradualRemaining buyDay high δ (t + 1) =
      .mul (A.gradualRemaining buyDay high δ t)
        (oneMinus (sellIndF (A.priceFeature (buyDay + t + 1)) high δ)) := rfl

theorem gradualRemaining_denote_succ (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ) :
    (A.gradualRemaining buyDay high δ (t + 1)).denote V =
      (A.gradualRemaining buyDay high δ t).denote V *
        (1 - (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V) := by
  simp [gradualRemaining]

theorem gradualSellFraction_denote (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ) :
    (A.gradualSellFraction buyDay high δ t).denote V =
      (A.gradualRemaining buyDay high δ t).denote V *
        (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V := by
  simp [gradualSellFraction]

theorem gradualRemaining_mem (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) : ∀ t,
    0 ≤ (A.gradualRemaining buyDay high δ t).denote V ∧
      (A.gradualRemaining buyDay high δ t).denote V ≤ 1 := by
  intro t
  induction t with
  | zero => simp [gradualRemaining]
  | succ t ih =>
      rw [gradualRemaining_denote_succ]
      obtain ⟨hs0, hs1⟩ := sellIndF_mem
        (A.priceFeature (buyDay + t + 1)) high δ V
      constructor
      · exact mul_nonneg ih.1 (sub_nonneg.mpr hs1)
      · calc
          (A.gradualRemaining buyDay high δ t).denote V *
                (1 - (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V)
              ≤ 1 * (1 - (sellIndF
                  (A.priceFeature (buyDay + t + 1)) high δ).denote V) :=
            mul_le_mul_of_nonneg_right ih.2 (sub_nonneg.mpr hs1)
          _ ≤ 1 := by linarith

theorem gradualRemaining_denote_antitone (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ) :
    (A.gradualRemaining buyDay high δ (t + 1)).denote V ≤
      (A.gradualRemaining buyDay high δ t).denote V := by
  rw [gradualRemaining_denote_succ]
  obtain ⟨hrem0, _⟩ := A.gradualRemaining_mem V buyDay high δ t
  obtain ⟨hsell0, hsell1⟩ :=
    sellIndF_mem (A.priceFeature (buyDay + t + 1)) high δ V
  nlinarith

theorem gradualSellFraction_nonneg (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ) :
    0 ≤ (A.gradualSellFraction buyDay high δ t).denote V := by
  rw [gradualSellFraction_denote]
  exact mul_nonneg (A.gradualRemaining_mem V buyDay high δ t).1
    (sellIndF_mem (A.priceFeature (buyDay + t + 1)) high δ V).1

/-- One day's sold fraction is exactly the decrease in the remaining fraction. -/
theorem gradualRemaining_succ_eq_sub_sell (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ) :
    (A.gradualRemaining buyDay high δ (t + 1)).denote V =
      (A.gradualRemaining buyDay high δ t).denote V -
        (A.gradualSellFraction buyDay high δ t).denote V := by
  rw [gradualRemaining_denote_succ, gradualSellFraction_denote]
  ring

/-- Sale fractions telescope: total sold through the first `t` future days is
`1 - remaining t`. -/
theorem sum_gradualSellFraction (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ) :
    ∑ j ∈ Finset.range t, (A.gradualSellFraction buyDay high δ j).denote V =
      1 - (A.gradualRemaining buyDay high δ t).denote V := by
  induction t with
  | zero => simp [gradualRemaining]
  | succ t ih =>
      rw [Finset.sum_range_succ, ih, gradualRemaining_succ_eq_sub_sell]
      ring

/-- A full sell signal liquidates all remaining shares on that day. -/
theorem gradualRemaining_eq_zero_of_full_signal (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ)
    (hfull : (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V = 1) :
    (A.gradualRemaining buyDay high δ (t + 1)).denote V = 0 := by
  rw [gradualRemaining_denote_succ, hfull]
  ring

theorem gradualRemaining_rank_le (A : AffineCombination) (buyDay : ℕ)
    (high δ : ℚ) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) : ∀ t,
    (A.gradualRemaining buyDay high δ t).rank ≤ buyDay + t := by
  intro t
  induction t with
  | zero => simp [gradualRemaining, EF.rank]
  | succ t ih =>
      simp only [gradualRemaining, EF.rank, oneMinus_rank, sellIndF_rank]
      apply Nat.max_le.mpr
      constructor
      · exact ih.trans (by omega)
      · exact A.priceFeature_rank (by omega) hconst hterms

theorem gradualSellFraction_rank_le (A : AffineCombination) (buyDay : ℕ)
    (high δ : ℚ) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (t : ℕ) :
    (A.gradualSellFraction buyDay high δ t).rank ≤ buyDay + t + 1 := by
  simp only [gradualSellFraction, EF.rank, sellIndF_rank]
  exact Nat.max_le.mpr ⟨(A.gradualRemaining_rank_le buyDay high δ hconst hterms t).trans
    (by omega), A.priceFeature_rank (by omega) hconst hterms⟩

/-- The paper's component trader: buy the entry-weighted combination on `buyDay`, then
sell `entry · gradualSellFraction t` copies on each future day. -/
def gradualTrader (A : AffineCombination) (entry : EF) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) : Trader where
  strat n := by
    by_cases hb : n = buyDay
    · subst n
      exact (A.scale entry).buy buyDay
        (A.scale_terms_rank_le entry hentry hterms)
    · by_cases ha : buyDay < n
      · let t := n - buyDay - 1
        have hday : buyDay + t + 1 = n := by dsimp only [t]; omega
        let coeff := EF.mul (EF.const (-1))
          (EF.mul entry (A.gradualSellFraction buyDay high δ t))
        have hsell : (A.gradualSellFraction buyDay high δ t).rank ≤ n := by
          rw [← hday]
          exact A.gradualSellFraction_rank_le buyDay high δ hconst hterms t
        have hcoeff : coeff.rank ≤ n := by
          simp only [coeff, EF.rank]
          exact Nat.max_le.mpr ⟨by simp, Nat.max_le.mpr
            ⟨hentry.trans (Nat.le_of_lt ha), hsell⟩⟩
        exact (A.scale coeff).buy n (A.scale_terms_rank_le coeff hcoeff
          (fun p hp => (hterms p hp).trans (Nat.le_of_lt ha)))
      · exact emptyStrategy n

@[simp] theorem gradualTrader_strat_buyDay (A : AffineCombination) (entry : EF)
    (buyDay : ℕ) (high δ : ℚ) (hentry : entry.rank ≤ buyDay)
    (hconst : A.const.rank ≤ buyDay) (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    (A.gradualTrader entry buyDay high δ hentry hconst hterms).strat buyDay =
      (A.scale entry).buy buyDay (A.scale_terms_rank_le entry hentry hterms) := by
  simp [gradualTrader]

theorem gradualTrader_strat_before (A : AffineCombination) (entry : EF)
    (buyDay n : ℕ) (high δ : ℚ) (hentry : entry.rank ≤ buyDay)
    (hconst : A.const.rank ≤ buyDay) (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay)
    (hn : n < buyDay) :
    (A.gradualTrader entry buyDay high δ hentry hconst hterms).strat n =
      emptyStrategy n := by
  simp [gradualTrader, ne_of_lt hn, Nat.not_lt.mpr (Nat.le_of_lt hn)]

theorem gradualTrader_value_buyDay (A : AffineCombination) (entry : EF)
    (V : History) (w : Valuation) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    ((A.gradualTrader entry buyDay high δ hentry hconst hterms).strat buyDay).value V w =
      entry.denote V * (A.value V w - A.price V buyDay) := by
  rw [gradualTrader_strat_buyDay, AffineCombination.buy_value, scale_value, scale_price]
  ring

theorem gradualTrader_value_future (A : AffineCombination) (entry : EF)
    (V : History) (w : Valuation) (buyDay t : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    ((A.gradualTrader entry buyDay high δ hentry hconst hterms).strat
      (buyDay + t + 1)).value V w =
      -entry.denote V * (A.gradualSellFraction buyDay high δ t).denote V *
        (A.value V w - A.price V (buyDay + t + 1)) := by
  have hne : buyDay + t + 1 ≠ buyDay := by omega
  have hlt : buyDay < buyDay + t + 1 := by omega
  simp only [gradualTrader, hne, hlt, ↓reduceDIte]
  have ht : buyDay + t + 1 - buyDay - 1 = t := by omega
  simp only [ht]
  rw [AffineCombination.buy_value, scale_value, scale_price]
  simp only [EF.denote_mul, EF.denote_const, Pi.mul_apply]
  push_cast
  ring

theorem gradualTrader_netWorth_buyDay (A : AffineCombination) (entry : EF)
    (V : History) (v : PCWorld) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    (A.gradualTrader entry buyDay high δ hentry hconst hterms).netWorth V v buyDay =
      entry.denote V * (A.value V v.payout - A.price V buyDay) := by
  rw [Trader.netWorth]
  rw [Finset.sum_eq_single buyDay]
  · exact A.gradualTrader_value_buyDay entry V v.payout buyDay high δ hentry hconst hterms
  · intro i hi hne
    have hil : i < buyDay := by
      simp only [Finset.mem_range] at hi
      omega
    rw [A.gradualTrader_strat_before entry buyDay i high δ hentry hconst hterms hil]
    simp [emptyStrategy, Strategy.value]
  · intro hnot
    simp at hnot

/-- Cash received by the gradual sales through the first `t` future days. -/
noncomputable def gradualSaleProceeds (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range t, (A.gradualSellFraction buyDay high δ j).denote V *
    A.price V (buyDay + j + 1)

/-- Exact holdings/cash decomposition after `t` gradual-sale days. -/
theorem gradualTrader_netWorth (A : AffineCombination) (entry : EF)
    (V : History) (v : PCWorld) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) : ∀ t,
    (A.gradualTrader entry buyDay high δ hentry hconst hterms).netWorth V v (buyDay + t) =
      entry.denote V *
        ((A.gradualRemaining buyDay high δ t).denote V * A.value V v.payout -
          A.price V buyDay + A.gradualSaleProceeds V buyDay high δ t) := by
  intro t
  induction t with
  | zero =>
      simpa [gradualRemaining, gradualSaleProceeds] using
        A.gradualTrader_netWorth_buyDay entry V v buyDay high δ hentry hconst hterms
  | succ t ih =>
      rw [show buyDay + (t + 1) = (buyDay + t) + 1 by omega]
      rw [Trader.netWorth_succ, ih]
      rw [show (buyDay + t) + 1 = buyDay + t + 1 by omega]
      rw [A.gradualTrader_value_future entry V v.payout buyDay t high δ
        hentry hconst hterms]
      rw [gradualRemaining_succ_eq_sub_sell]
      simp only [gradualSaleProceeds, Finset.sum_range_succ]
      ring

theorem gradualSellFraction_pos_imp_price (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (hδ : 0 < (δ : ℝ)) (t : ℕ)
    (hpos : 0 < (A.gradualSellFraction buyDay high δ t).denote V) :
    (high : ℝ) - δ < A.price V (buyDay + t + 1) := by
  rw [gradualSellFraction_denote] at hpos
  have hrem := (A.gradualRemaining_mem V buyDay high δ t).1
  have hsig : 0 <
      (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V := by
    nlinarith
  have := sellIndF_pos_imp hδ hsig
  rwa [A.priceFeature_denote] at this

/-- Every partial sale is executed above the protected threshold `high - δ`. -/
theorem gradualSaleProceeds_lower (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (hδ : 0 < (δ : ℝ)) (t : ℕ) :
    ((high : ℝ) - δ) *
        (1 - (A.gradualRemaining buyDay high δ t).denote V) ≤
      A.gradualSaleProceeds V buyDay high δ t := by
  have hsum := A.sum_gradualSellFraction V buyDay high δ t
  calc
    ((high : ℝ) - δ) *
        (1 - (A.gradualRemaining buyDay high δ t).denote V) =
        ∑ j ∈ Finset.range t,
          ((high : ℝ) - δ) * (A.gradualSellFraction buyDay high δ j).denote V := by
            rw [← Finset.mul_sum, hsum]
    _ ≤ A.gradualSaleProceeds V buyDay high δ t := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hz : (A.gradualSellFraction buyDay high δ j).denote V = 0
      · simp [hz, gradualSaleProceeds]
      · have hf0 := A.gradualSellFraction_nonneg V buyDay high δ j
        have hfp : 0 < (A.gradualSellFraction buyDay high δ j).denote V :=
          lt_of_le_of_ne hf0 (Ne.symm hz)
        simpa [mul_comm] using mul_le_mul_of_nonneg_right
          (le_of_lt (A.gradualSellFraction_pos_imp_price V buyDay high δ hδ j hfp)) hf0

/-- If a full signal has occurred, all shares are sold at prices at least `high - δ`. -/
theorem gradualSaleProceeds_lower_of_full_signal (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) (hδ : 0 < (δ : ℝ)) (t : ℕ)
    (hfull : (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V = 1) :
    (high : ℝ) - δ ≤ A.gradualSaleProceeds V buyDay high δ (t + 1) := by
  have hzero := A.gradualRemaining_eq_zero_of_full_signal V buyDay high δ t hfull
  have h := A.gradualSaleProceeds_lower V buyDay high δ hδ (t + 1)
  rwa [hzero, sub_zero, mul_one] at h

/-- At every intermediate day, realized protected spread pays for the sold fraction; only
the remaining fraction can still carry affine world risk. This is the economic invariant
needed by an online, feature-driven capital budgeter. -/
theorem gradualTrader_netWorth_lower_partial (A : AffineCombination) (entry : EF)
    (V : History) (v : PCWorld) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay)
    (hentry0 : 0 ≤ entry.denote V) (hδ : 0 < (δ : ℝ))
    (hP : ∀ φ, 0 ≤ V buyDay φ ∧ V buyDay φ ≤ 1) (t : ℕ) :
    entry.denote V *
        ((1 - (A.gradualRemaining buyDay high δ t).denote V) *
            ((high : ℝ) - δ - A.price V buyDay) -
          (A.gradualRemaining buyDay high δ t).denote V * A.magnitude V) ≤
      (A.gradualTrader entry buyDay high δ hentry hconst hterms).netWorth V v
        (buyDay + t) := by
  classical
  rw [A.gradualTrader_netWorth entry V v buyDay high δ hentry hconst hterms t]
  let rem := (A.gradualRemaining buyDay high δ t).denote V
  have hrem0 : 0 ≤ rem := (A.gradualRemaining_mem V buyDay high δ t).1
  have hvalueAbs := A.abs_value_sub_price_le_magnitude V v.payout buyDay hterms
    (fun φ => by
      by_cases hφ : v.Holds φ
      · exact Or.inr (by simp [PCWorld.payout, hφ])
      · exact Or.inl (by simp [PCWorld.payout, hφ])) hP
  have hvalue : -A.magnitude V ≤ A.value V v.payout - A.price V buyDay :=
    neg_le_of_abs_le hvalueAbs
  have hvalueScaled := mul_le_mul_of_nonneg_left hvalue hrem0
  have hsales := A.gradualSaleProceeds_lower V buyDay high δ hδ t
  change entry.denote V *
      ((1 - rem) * ((high : ℝ) - δ - A.price V buyDay) -
        rem * A.magnitude V) ≤
    entry.denote V *
      (rem * A.value V v.payout - A.price V buyDay +
        A.gradualSaleProceeds V buyDay high δ t)
  apply mul_le_mul_of_nonneg_left _ hentry0
  nlinarith

/-- Once fully liquidated, the component's net worth is world-independent and bounded by
the entry weight times the guaranteed price spread. -/
theorem gradualTrader_netWorth_lower_of_full_signal (A : AffineCombination) (entry : EF)
    (V : History) (v : PCWorld) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay)
    (hentry0 : 0 ≤ entry.denote V) (hδ : 0 < (δ : ℝ)) (t : ℕ)
    (hfull : (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V = 1) :
    entry.denote V * ((high : ℝ) - δ - A.price V buyDay) ≤
      (A.gradualTrader entry buyDay high δ hentry hconst hterms).netWorth V v
        (buyDay + t + 1) := by
  rw [show buyDay + t + 1 = buyDay + (t + 1) by omega]
  rw [A.gradualTrader_netWorth entry V v buyDay high δ hentry hconst hterms (t + 1)]
  rw [A.gradualRemaining_eq_zero_of_full_signal V buyDay high δ t hfull]
  have hp := A.gradualSaleProceeds_lower_of_full_signal V buyDay high δ hδ t hfull
  nlinarith

theorem gradualRemaining_zero_mono (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) {t : ℕ}
    (hz : (A.gradualRemaining buyDay high δ t).denote V = 0) :
    ∀ s, t ≤ s → (A.gradualRemaining buyDay high δ s).denote V = 0 := by
  intro s hts
  induction s, hts using Nat.le_induction with
  | base => exact hz
  | succ s _ ih => rw [gradualRemaining_denote_succ, ih, zero_mul]

theorem gradualSellFraction_eq_zero_of_remaining_zero (A : AffineCombination) (V : History)
    (buyDay : ℕ) (high δ : ℚ) {t : ℕ}
    (hz : (A.gradualRemaining buyDay high δ t).denote V = 0) :
    (A.gradualSellFraction buyDay high δ t).denote V = 0 := by
  rw [gradualSellFraction_denote, hz, zero_mul]

theorem gradualTrader_magnitude_buyDay (A : AffineCombination) (entry : EF)
    (V : History) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (hentry0 : 0 ≤ entry.denote V) :
    ((A.gradualTrader entry buyDay high δ hentry hconst hterms).strat buyDay).magnitude V =
      entry.denote V * A.magnitude V := by
  rw [gradualTrader_strat_buyDay, AffineCombination.buy_magnitude, scale_magnitude,
    abs_of_nonneg hentry0]

theorem gradualTrader_magnitude_future (A : AffineCombination) (entry : EF)
    (V : History) (buyDay t : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (hentry0 : 0 ≤ entry.denote V) :
    ((A.gradualTrader entry buyDay high δ hentry hconst hterms).strat
      (buyDay + t + 1)).magnitude V =
      entry.denote V * (A.gradualSellFraction buyDay high δ t).denote V *
        A.magnitude V := by
  have hne : buyDay + t + 1 ≠ buyDay := by omega
  have hlt : buyDay < buyDay + t + 1 := by omega
  simp only [gradualTrader, hne, hlt, ↓reduceDIte]
  have ht : buyDay + t + 1 - buyDay - 1 = t := by omega
  simp only [ht]
  rw [AffineCombination.buy_magnitude, scale_magnitude]
  simp only [EF.denote_mul, EF.denote_const, Pi.mul_apply]
  push_cast
  have hf0 : 0 ≤ (A.gradualSellFraction buyDay high δ t).denote V :=
    A.gradualSellFraction_nonneg V buyDay high δ t
  rw [abs_of_nonpos]
  · ring
  · nlinarith [mul_nonneg hentry0 hf0]

theorem gradualTrader_partial_magnitude (A : AffineCombination) (entry : EF)
    (V : History) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (hentry0 : 0 ≤ entry.denote V) : ∀ t,
    ∑ i ∈ Finset.range (buyDay + t + 1),
        ((A.gradualTrader entry buyDay high δ hentry hconst hterms).strat i).magnitude V =
      entry.denote V * A.magnitude V *
        (1 + ∑ j ∈ Finset.range t,
          (A.gradualSellFraction buyDay high δ j).denote V) := by
  intro t
  induction t with
  | zero =>
      rw [add_zero]
      rw [Finset.sum_eq_single buyDay]
      · rw [A.gradualTrader_magnitude_buyDay entry V buyDay high δ hentry hconst hterms
          hentry0]
        simp
      · intro i hi hne
        have hil : i < buyDay := by
          simp only [Finset.mem_range] at hi
          omega
        rw [A.gradualTrader_strat_before entry buyDay i high δ hentry hconst hterms hil]
        simp [emptyStrategy, Strategy.magnitude]
      · intro hnot
        simp at hnot
  | succ t ih =>
      rw [show buyDay + (t + 1) + 1 = (buyDay + t + 1) + 1 by omega]
      rw [Finset.sum_range_succ, ih]
      rw [A.gradualTrader_magnitude_future entry V buyDay t high δ hentry hconst hterms
        hentry0]
      rw [Finset.sum_range_succ]
      ring

theorem gradualTrader_summable_of_full_signal (A : AffineCombination) (entry : EF)
    (V : History) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (hentry0 : 0 ≤ entry.denote V)
    (t : ℕ) (hfull :
      (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V = 1) :
    Summable (fun n =>
      ((A.gradualTrader entry buyDay high δ hentry hconst hterms).strat n).magnitude V) := by
  apply summable_of_finite_support
  refine (Set.finite_Iic (buyDay + t + 1)).subset ?_
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Set.mem_Iic]
  by_contra hnot
  have hnclose : buyDay + t + 1 < n := by omega
  let s := n - buyDay - 1
  have hday : n = buyDay + s + 1 := by dsimp only [s]; omega
  have hts : t + 1 ≤ s := by dsimp only [s]; omega
  have hzero := A.gradualRemaining_eq_zero_of_full_signal V buyDay high δ t hfull
  have hzero' := A.gradualRemaining_zero_mono V buyDay high δ hzero s hts
  have hfzero := A.gradualSellFraction_eq_zero_of_remaining_zero V buyDay high δ hzero'
  rw [hday, A.gradualTrader_magnitude_future entry V buyDay s high δ hentry hconst
    hterms hentry0, hfzero, mul_zero, zero_mul] at hn
  exact hn rfl

/-- A fully liquidated gradual component has the same exact `2 · entry · |A|` magnitude as
the finite round-trip kernel. -/
theorem gradualTrader_magnitude_of_full_signal (A : AffineCombination) (entry : EF)
    (V : History) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (hentry0 : 0 ≤ entry.denote V)
    (t : ℕ) (hfull :
      (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V = 1) :
    (A.gradualTrader entry buyDay high δ hentry hconst hterms).magnitude V =
      2 * entry.denote V * A.magnitude V := by
  rw [Trader.magnitude]
  rw [tsum_eq_sum (s := Finset.range (buyDay + t + 2))]
  · rw [show buyDay + t + 2 = buyDay + (t + 1) + 1 by omega]
    rw [A.gradualTrader_partial_magnitude entry V buyDay high δ hentry hconst hterms
      hentry0 (t + 1)]
    have hzero := A.gradualRemaining_eq_zero_of_full_signal V buyDay high δ t hfull
    have hsum := A.sum_gradualSellFraction V buyDay high δ (t + 1)
    rw [hzero, sub_zero] at hsum
    rw [hsum]
    ring
  · intro n hn
    rw [Finset.mem_range, not_lt] at hn
    let s := n - buyDay - 1
    have hday : n = buyDay + s + 1 := by dsimp only [s]; omega
    have hts : t + 1 ≤ s := by dsimp only [s]; omega
    have hzero := A.gradualRemaining_eq_zero_of_full_signal V buyDay high δ t hfull
    have hzero' := A.gradualRemaining_zero_mono V buyDay high δ hzero s hts
    have hfzero := A.gradualSellFraction_eq_zero_of_remaining_zero V buyDay high δ hzero'
    rw [hday, A.gradualTrader_magnitude_future entry V buyDay s high δ hentry hconst
      hterms hentry0, hfzero, mul_zero, zero_mul]

theorem gradualTrader_netWorth_stable_of_full_signal (A : AffineCombination) (entry : EF)
    (V : History) (v : PCWorld) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (t : ℕ)
    (hfull : (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V = 1) :
    ∀ n, buyDay + t + 1 ≤ n →
      (A.gradualTrader entry buyDay high δ hentry hconst hterms).netWorth V v n =
        (A.gradualTrader entry buyDay high δ hentry hconst hterms).netWorth V v
          (buyDay + t + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n _ ih =>
      rw [Trader.netWorth_succ, ih]
      let s := n - buyDay
      have hday : n + 1 = buyDay + s + 1 := by dsimp only [s]; omega
      have hts : t + 1 ≤ s := by dsimp only [s]; omega
      have hzero := A.gradualRemaining_eq_zero_of_full_signal V buyDay high δ t hfull
      have hzero' := A.gradualRemaining_zero_mono V buyDay high δ hzero s hts
      have hfzero := A.gradualSellFraction_eq_zero_of_remaining_zero V buyDay high δ hzero'
      rw [hday, A.gradualTrader_value_future entry V v.payout buyDay s high δ hentry
        hconst hterms, hfzero]
      ring

/-- Semantic ROI theorem for the continuous gradual-sale component. -/
theorem gradualTrader_hasROI_of_full_signal (A : AffineCombination) (entry : EF)
    (V : History) (DP : DeductiveProcess) (buyDay : ℕ) (high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (hentry0 : 0 ≤ entry.denote V)
    (hδ : 0 < (δ : ℝ)) (rate : ℝ) (t : ℕ)
    (hfull : (sellIndF (A.priceFeature (buyDay + t + 1)) high δ).denote V = 1)
    (hspread : rate * (2 * entry.denote V * A.magnitude V) ≤
      entry.denote V * ((high : ℝ) - δ - A.price V buyDay)) :
    HasROI (A.gradualTrader entry buyDay high δ hentry hconst hterms) V DP rate := by
  constructor
  · exact A.gradualTrader_summable_of_full_signal entry V buyDay high δ hentry hconst
      hterms hentry0 t hfull
  · intro η hη
    refine ⟨buyDay + t + 1, fun n hn v _ => ?_⟩
    rw [A.gradualTrader_magnitude_of_full_signal entry V buyDay high δ hentry hconst
      hterms hentry0 t hfull]
    rw [A.gradualTrader_netWorth_stable_of_full_signal entry V v buyDay high δ hentry
      hconst hterms t hfull n hn]
    have hnet := A.gradualTrader_netWorth_lower_of_full_signal entry V v buyDay high δ
      hentry hconst hterms hentry0 hδ t hfull
    have hmag := A.magnitude_nonneg V
    have htotal : 0 ≤ 2 * entry.denote V * A.magnitude V := by positivity
    calc
      (rate - η) * (2 * entry.denote V * A.magnitude V) ≤
          rate * (2 * entry.denote V * A.magnitude V) := by
        nlinarith [mul_nonneg (le_of_lt hη) htotal]
      _ ≤ entry.denote V * ((high : ℝ) - δ - A.price V buyDay) := hspread
      _ ≤ (A.gradualTrader entry buyDay high δ hentry hconst hterms).netWorth V v
          (buyDay + t + 1) := hnet

/-- A concrete low-to-high price gap gives positive ROI to the gradual affine component.
The entry feature is the continuous buy indicator at the opening price, while a later
price strictly above `high` supplies the full liquidation signal. -/
theorem gradualTrader_hasROI_of_price_gap (A : AffineCombination) (entry : EF)
    (V : History) (DP : DeductiveProcess) (buyDay : ℕ) (low high δ : ℚ)
    (hentry : entry.rank ≤ buyDay) (hconst : A.const.rank ≤ buyDay)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ buyDay)
    (hentrySignal : entry = buyIndF (A.priceFeature buyDay) low δ)
    (hmag : A.magnitude V ≤ 1) (hδ : 0 < (δ : ℝ))
    (hgap : 0 < (high : ℝ) - low - 2 * δ) (t : ℕ)
    (hfuture : (high : ℝ) < A.price V (buyDay + t + 1)) :
    HasROI (A.gradualTrader entry buyDay high δ hentry hconst hterms) V DP
      (((high : ℝ) - low - 2 * δ) / 2) := by
  subst entry
  have hentry0 : 0 ≤ (buyIndF (A.priceFeature buyDay) low δ).denote V :=
    (buyIndF_mem (A.priceFeature buyDay) low δ V).1
  apply A.gradualTrader_hasROI_of_full_signal
    (buyIndF (A.priceFeature buyDay) low δ) V DP buyDay high δ hentry hconst hterms
    hentry0 hδ (((high : ℝ) - low - 2 * δ) / 2) t
  · apply sellIndF_eq_one hδ
    rwa [A.priceFeature_denote]
  · by_cases hz : (buyIndF (A.priceFeature buyDay) low δ).denote V = 0
    · simp [hz]
    · have hentryPos : 0 < (buyIndF (A.priceFeature buyDay) low δ).denote V :=
        lt_of_le_of_ne hentry0 (Ne.symm hz)
      have hopen := buyIndF_pos_imp hδ hentryPos
      rw [A.priceFeature_denote] at hopen
      have hmag0 := A.magnitude_nonneg V
      have hscaled :
          ((high : ℝ) - low - 2 * δ) *
              (buyIndF (A.priceFeature buyDay) low δ).denote V * A.magnitude V ≤
            ((high : ℝ) - low - 2 * δ) *
              (buyIndF (A.priceFeature buyDay) low δ).denote V := by
        exact mul_le_of_le_one_right
          (mul_nonneg (le_of_lt hgap) (le_of_lt hentryPos)) hmag
      nlinarith

end AffineCombination

#print axioms liminf_eq_of_noPreemptiveUnderpricing
#print axioms limsup_eq_of_noPreemptiveOverpricing
#print axioms affpolymax_of_noPreemptiveGaps
#print axioms AffineCombination.sum_gradualSellFraction
#print axioms AffineCombination.gradualSellFraction_rank_le
#print axioms AffineCombination.gradualTrader_value_future
#print axioms AffineCombination.gradualTrader_netWorth
#print axioms AffineCombination.gradualTrader_netWorth_lower_partial
#print axioms AffineCombination.gradualTrader_netWorth_lower_of_full_signal
#print axioms AffineCombination.gradualTrader_magnitude_of_full_signal
#print axioms AffineCombination.gradualTrader_hasROI_of_full_signal
#print axioms AffineCombination.gradualTrader_hasROI_of_price_gap

end LogicalInduction
