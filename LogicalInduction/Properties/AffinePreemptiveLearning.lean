/-
# `thm:affpolymax` — analytic preemptive-learning hub

This file isolates the order/limit half of Affine Preemptive Learning.  The economic half
constructs an efficiently emulatable family of affine round trips and proves the two
`NoPreemptive*` conditions below via repeatable ROI.  Once those conditions are available,
the paper's two liminf/limsup equalities are purely generic filter arguments.
-/
import LogicalInduction.Affine
import LogicalInduction.ROI
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

#print axioms liminf_eq_of_noPreemptiveUnderpricing
#print axioms limsup_eq_of_noPreemptiveOverpricing
#print axioms affpolymax_of_noPreemptiveGaps

end LogicalInduction
