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

theorem oneMinus_closed {e : EF} {ρ : List ℝ} {V : History}
    (he : e.denoteWith ρ V = e.denote V) :
    (oneMinus e).denoteWith ρ V = (oneMinus e).denote V := by
  simp only [oneMinus, EF.denoteWith, EF.denote_add, EF.denote_mul, EF.denote_const,
    Pi.add_apply, Pi.mul_apply]
  rw [he]

theorem sellIndF_closed {e : EF} {ρ : List ℝ} {V : History} (high δ : ℚ)
    (he : e.denoteWith ρ V = e.denote V) :
    (sellIndF e high δ).denoteWith ρ V = (sellIndF e high δ).denote V := by
  simp only [sellIndF, clip01, efMin, EF.denoteWith, EF.denote_max, EF.denote_mul,
    EF.denote_add, EF.denote_const, Pi.mul_apply, Pi.add_apply]
  rw [he]

/-- Segment-level closure for the feature-generic sell ramp. -/
theorem PolySegStream.serialize_sellIndF {e : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize)) (high δ : ℚ) :
    PolySegStream (fun n => (sellIndF (e n) high δ).serialize) :=
  PolySegStream.serialize_clip01
    (PolySegStream.serialize_mul
      (PolySegStream.serialize_add he
        (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (δ - high))))
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (1 / δ))))

/-- Segment-level closure for the feature-generic buy ramp. -/
theorem PolySegStream.serialize_buyIndF {e : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize)) (low δ : ℚ) :
    PolySegStream (fun n => (buyIndF (e n) low δ).serialize) :=
  PolySegStream.serialize_clip01
    (PolySegStream.serialize_mul
      (PolySegStream.serialize_add
        (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (low + δ)))
        (PolySegStream.serialize_mul
          (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) he))
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (1 / δ))))

/-- Continuous entry signal for the diagonal affine price. -/
def gradualEntry (As : ℕ → AffineCombination) (low δ : ℚ) (n : ℕ) : EF :=
  buyIndF ((As n).priceFeature n) low δ

theorem PolySequence.gradualEntry_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) (low δ : ℚ) :
    PolySegStream (fun n => (gradualEntry As low δ n).serialize) := by
  have hdiag : PolySegStream (fun n => ((As n).priceFeature n).serialize) := by
    refine PolySegStream.of_eq (h.priceFeature_polySeg.comp (PolyFueled.id.pair PolyFueled.id)) ?_
    intro n
    simp only [Nat.unpair_pair]
  exact PolySegStream.serialize_buyIndF hdiag low δ

theorem PolySequence.gradualEntry_rank_le {As : ℕ → AffineCombination}
    (h : PolySequence As) (low δ : ℚ) (n : ℕ) :
    (gradualEntry As low δ n).rank ≤ n := by
  simp only [gradualEntry, buyIndF_rank]
  exact (As n).priceFeature_rank le_rfl (h.const_rank n) (h.terms_rank n)

theorem PolySequence.gradualEntry_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (low δ : ℚ) (n : ℕ) (ρ : List ℝ) (V : History) :
    (gradualEntry As low δ n).denoteWith ρ V =
      (gradualEntry As low δ n).denote V := by
  simp only [gradualEntry, buyIndF, clip01, efMin, EF.denoteWith, EF.denote_max,
    EF.denote_mul, EF.denote_add, EF.denote_const, Pi.mul_apply, Pi.add_apply]
  rw [h.priceFeature_closed n n ρ V]

def gradualRemaining (A : AffineCombination) (buyDay : ℕ) (high δ : ℚ) : ℕ → EF
  | 0 => .const 1
  | t + 1 => .mul (A.gradualRemaining buyDay high δ t)
      (oneMinus (sellIndF (A.priceFeature (buyDay + t + 1)) high δ))

def gradualSellFraction (A : AffineCombination) (buyDay : ℕ) (high δ : ℚ)
    (t : ℕ) : EF :=
  .mul (A.gradualRemaining buyDay high δ t)
    (sellIndF (A.priceFeature (buyDay + t + 1)) high δ)

/-- The recursive occupancy feature serializes as its initial `1` followed by one update
block for every elapsed day. -/
theorem gradualRemaining_serialize (A : AffineCombination) (buyDay : ℕ)
    (high δ : ℚ) (t : ℕ) :
    (A.gradualRemaining buyDay high δ t).serialize =
      (EF.const 1).serialize ++
        (List.range t).flatMap (fun j =>
          (oneMinus (sellIndF (A.priceFeature (buyDay + j + 1)) high δ)).serialize ++ [3]) := by
  induction t with
  | zero => simp [gradualRemaining]
  | succ t ih =>
      rw [gradualRemaining]
      simp only [EF.serialize, ih, List.range_succ, List.flatMap_append,
        List.flatMap_singleton]
      simp [List.append_assoc]

/-- Uniform emission of the two-index gradual occupancy family.  Input `z = ⟨i,t⟩`
denotes member `Aᵢ`, opened on day `i`, after `t` gradual-sale updates. -/
theorem PolySequence.gradualRemaining_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) (high δ : ℚ) :
    PolySegStream (fun z =>
      ((As z.unpair.1).gradualRemaining z.unpair.1 high δ z.unpair.2).serialize) := by
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  -- An update block is indexed by `q = ⟨⟨i,t⟩,j⟩`.
  have hmember := PolyFueled.left.comp PolyFueled.left
  have hstep := PolyFueled.right
  have hfuture := (hadd.comp (hmember.pair hstep)).succ_comp
  have hpriceIndex := hmember.pair hfuture
  have hprice : PolySegStream (fun q =>
      ((As q.unpair.1.unpair.1).priceFeature
        (q.unpair.1.unpair.1 + q.unpair.2 + 1)).serialize) := by
    refine PolySegStream.of_eq (h.priceFeature_polySeg.comp hpriceIndex) ?_
    intro q
    simp only [Nat.unpair_pair]
  have hsell := PolySegStream.serialize_sellIndF hprice high δ
  have hremain := PolySegStream.serialize_oneMinus hsell
  have hmul : PolySegStream (fun _ => [3]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 3)
  have hblock : PolySegStream (fun q =>
      (oneMinus (sellIndF
        ((As q.unpair.1.unpair.1).priceFeature
          (q.unpair.1.unpair.1 + q.unpair.2 + 1)) high δ)).serialize ++ [3]) := by
    exact hremain.append hmul
  have hblocks := PolySegStream.concatVar hblock PolyFueled.right
  have hone : PolySegStream (fun _ => (EF.const 1).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)
  refine PolySegStream.of_eq (hone.append hblocks) ?_
  intro z
  rw [gradualRemaining_serialize]
  simp only [Nat.unpair_pair]

theorem PolySequence.gradualSellFraction_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) (high δ : ℚ) :
    PolySegStream (fun z =>
      ((As z.unpair.1).gradualSellFraction z.unpair.1 high δ z.unpair.2).serialize) := by
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hmember := PolyFueled.left
  have hstep := PolyFueled.right
  have hfuture := (hadd.comp (hmember.pair hstep)).succ_comp
  have hprice : PolySegStream (fun z =>
      ((As z.unpair.1).priceFeature (z.unpair.1 + z.unpair.2 + 1)).serialize) := by
    refine PolySegStream.of_eq
      (h.priceFeature_polySeg.comp (hmember.pair hfuture)) ?_
    intro z
    simp only [Nat.unpair_pair]
  have hsell := PolySegStream.serialize_sellIndF hprice high δ
  refine PolySegStream.of_eq
    (PolySegStream.serialize_mul (h.gradualRemaining_polySeg high δ) hsell) ?_
  intro z
  rfl

/-- Day/member ordering used by `noFractionalRepeatableReturn`: on day `n`, member `i`
has elapsed occupancy `n-i` (truncated to zero before launch). -/
def gradualOccupancy (As : ℕ → AffineCombination) (high δ : ℚ)
    (i n : ℕ) : EF :=
  (As i).gradualRemaining i high δ (n - i)

def gradualRisk (As : ℕ → AffineCombination) (low δ : ℚ) (i : ℕ) : EF :=
  (As i).riskFeature (gradualEntry As low δ i)

def gateFeature (start : ℕ) (f : ℕ → EF) (i : ℕ) : EF :=
  if start ≤ i then f i else EF.const 0

def gateOccupancy (start : ℕ) (f : ℕ → ℕ → EF) (i n : ℕ) : EF :=
  if start ≤ i then f i n else EF.const 0

theorem PolySegStream.gateFeature {f : ℕ → EF}
    (hf : PolySegStream (fun i => (f i).serialize)) (start : ℕ) :
    PolySegStream (fun i => (gateFeature start f i).serialize) := by
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have htestRaw := subc_polyFueled.comp
    (PolyFueled.id.succ_comp.pair (PolyFueled.const start))
  have htest : PolyFueled
      (subc.comp ((Nat.Partrec.Code.succ.comp
        (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right)).pair
          (Nat.Partrec.Code.const start)))
      (fun i => i + 1 - start) := by
    apply PolyFueled.of_eq htestRaw
    intro i
    simp only [Nat.unpair_pair]
  refine PolySegStream.of_eq (PolySegStream.ifZero hzero hf htest) ?_
  intro i
  by_cases hs : start ≤ i
  · rw [if_neg (by omega), AffineCombination.gateFeature, if_pos hs]
  · rw [if_pos (by omega), AffineCombination.gateFeature, if_neg hs]

theorem PolySegStream.gateOccupancy {f : ℕ → ℕ → EF}
    (hf : PolySegStream (fun z => (f z.unpair.2 z.unpair.1).serialize)) (start : ℕ) :
    PolySegStream (fun z => (gateOccupancy start f z.unpair.2 z.unpair.1).serialize) := by
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have htestRaw := subc_polyFueled.comp
    (PolyFueled.right.succ_comp.pair (PolyFueled.const start))
  have htest : PolyFueled
      (subc.comp ((Nat.Partrec.Code.succ.comp Nat.Partrec.Code.right).pair
        (Nat.Partrec.Code.const start)))
      (fun z => z.unpair.2 + 1 - start) := by
    apply PolyFueled.of_eq htestRaw
    intro z
    simp only [Nat.unpair_pair]
  refine PolySegStream.of_eq (PolySegStream.ifZero hzero hf htest) ?_
  intro z
  by_cases hs : start ≤ z.unpair.2
  · rw [if_neg (by omega), AffineCombination.gateOccupancy, if_pos hs]
  · rw [if_pos (by omega), AffineCombination.gateOccupancy, if_neg hs]

theorem PolySequence.gradualRisk_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) (low δ : ℚ) :
    PolySegStream (fun i => (gradualRisk As low δ i).serialize) :=
  h.riskFeature_polySeg (h.gradualEntry_polySeg low δ)

theorem PolySequence.gradualRisk_rank_le {As : ℕ → AffineCombination}
    (h : PolySequence As) (low δ : ℚ) (i : ℕ) :
    (gradualRisk As low δ i).rank ≤ i :=
  (As i).riskFeature_rank_le (gradualEntry As low δ i)
    (h.gradualEntry_rank_le low δ i) (h.terms_rank i)

theorem PolySequence.gradualRisk_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (low δ : ℚ) (i : ℕ) (ρ : List ℝ) (V : History) :
    (gradualRisk As low δ i).denoteWith ρ V = (gradualRisk As low δ i).denote V :=
  h.riskFeature_closed (h.gradualEntry_closed low δ) i ρ V

def gradualTradeCount {As : ℕ → AffineCombination} (h : PolySequence As) (z : ℕ) : ℕ :=
  if z.unpair.1 ≤ z.unpair.2 then h.termCount z.unpair.1 else 0

def gradualCoefficient {As : ℕ → AffineCombination} (h : PolySequence As)
    (low high δ : ℚ) (z : ℕ) : EF :=
  let k := z.unpair.1.unpair.1
  let n := z.unpair.1.unpair.2
  let j := z.unpair.2
  let base := h.coefficient (Nat.pair k j)
  if n = k then EF.mul (gradualEntry As low δ k) base
  else
    EF.mul
      (EF.mul (EF.const (-1))
        (EF.mul (gradualEntry As low δ k)
          ((As k).gradualSellFraction k high δ (n - k - 1))))
      base

def gradualSentence {As : ℕ → AffineCombination} (h : PolySequence As) (z : ℕ) : Sentence :=
  h.sentence (Nat.pair z.unpair.1.unpair.1 z.unpair.2)

theorem PolySequence.gradualOccupancy_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) (high δ : ℚ) :
    PolySegStream (fun z =>
      (gradualOccupancy As high δ z.unpair.2 z.unpair.1).serialize) := by
  have helapsed := subc_polyFueled.comp (PolyFueled.left.pair PolyFueled.right)
  refine PolySegStream.of_eq
    ((h.gradualRemaining_polySeg high δ).comp (PolyFueled.right.pair helapsed)) ?_
  intro z
  simp only [Nat.unpair_pair, gradualOccupancy]

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

theorem PolySequence.gradualRemaining_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (i : ℕ) (high δ : ℚ) (ρ : List ℝ) (V : History) : ∀ t,
    ((As i).gradualRemaining i high δ t).denoteWith ρ V =
      ((As i).gradualRemaining i high δ t).denote V := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [gradualRemaining, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
      rw [ih]
      rw [oneMinus_closed (sellIndF_closed high δ
        (h.priceFeature_closed i (i + t + 1) ρ V))]

theorem PolySequence.gradualOccupancy_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (high δ : ℚ) (i n : ℕ) (ρ : List ℝ) (V : History) :
    (gradualOccupancy As high δ i n).denoteWith ρ V =
      (gradualOccupancy As high δ i n).denote V :=
  h.gradualRemaining_closed i high δ ρ V (n - i)

theorem PolySequence.gradualOccupancy_rank_le {As : ℕ → AffineCombination}
    (h : PolySequence As) (high δ : ℚ) (i n : ℕ) (hin : i ≤ n) :
    (gradualOccupancy As high δ i n).rank ≤ n := by
  rw [gradualOccupancy]
  have hr := (As i).gradualRemaining_rank_le i high δ (h.const_rank i)
    (h.terms_rank i) (n - i)
  exact hr.trans (by omega)

theorem gradualOccupancy_decreasing (As : ℕ → AffineCombination) (V : History)
    (high δ : ℚ) :
    ROIBudget.DecreasingOccupancy (fun i n => (gradualOccupancy As high δ i n).denote V) := by
  constructor
  · intro i n
    exact ((As i).gradualRemaining_mem V i high δ (n - i)).1
  · intro i n
    exact ((As i).gradualRemaining_mem V i high δ (n - i)).2
  · intro i n
    by_cases hin : i ≤ n
    · have hstep := (As i).gradualRemaining_denote_antitone V i high δ (n - i)
      have hn : n - i + 1 = n + 1 - i := by omega
      rwa [hn] at hstep
    · have hni : n + 1 ≤ i := by omega
      simp [gradualOccupancy, Nat.sub_eq_zero_of_le hni,
        Nat.sub_eq_zero_of_le (Nat.le_of_lt (by omega : n < i))]

theorem gradualOccupancy_eventually_zero (As : ℕ → AffineCombination) (V : History)
    (high δ : ℚ)
    (hfull : ∀ i, ∃ t,
      (sellIndF ((As i).priceFeature (i + t + 1)) high δ).denote V = 1) :
    ∀ i, ∃ N, ∀ n, N ≤ n → (gradualOccupancy As high δ i n).denote V = 0 := by
  intro i
  obtain ⟨t, ht⟩ := hfull i
  refine ⟨i + t + 1, fun n hn => ?_⟩
  have hz := (As i).gradualRemaining_eq_zero_of_full_signal V i high δ t ht
  have hmono : ∀ s, t + 1 ≤ s →
      ((As i).gradualRemaining i high δ s).denote V = 0 := by
    intro s hts
    induction s, hts using Nat.le_induction with
    | base => exact hz
    | succ s _ ih => rw [gradualRemaining_denote_succ, ih, zero_mul]
  exact hmono (n - i) (by omega)

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

/-- The uniformly generated gradual component family used by the affine ROI argument. -/
def gradualFamily (As : ℕ → AffineCombination) (low high δ : ℚ)
    (h : PolySequence As) : ℕ → Trader := fun i =>
  (As i).gradualTrader (gradualEntry As low δ i) i high δ
    (h.gradualEntry_rank_le low δ i) (h.const_rank i) (h.terms_rank i)

theorem PolySequence.gradualTradeCount_poly {As : ℕ → AffineCombination}
    (h : PolySequence As) : ∃ c, PolyFueled c (gradualTradeCount h) := by
  obtain ⟨ccount, hcount⟩ := h.termCount_poly
  have htest := subc_polyFueled.comp
    (PolyFueled.right.succ_comp.pair PolyFueled.left)
  have hraw := ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair (hcount.comp PolyFueled.left)).pair htest)
  refine ⟨_, PolyFueled.of_eq hraw ?_⟩
  intro z
  simp only [Function.comp_apply, Nat.unpair_pair, ifzSelFn, gradualTradeCount]
  by_cases hle : z.unpair.1 ≤ z.unpair.2
  · rw [if_pos hle, if_neg (by omega)]
  · rw [if_neg hle, if_pos (by omega)]

theorem PolySequence.gradualCoefficient_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) (low high δ : ℚ) :
    PolySegStream (fun z => (gradualCoefficient h low high δ z).serialize) := by
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hk := PolyFueled.left.comp PolyFueled.left
  have hn := PolyFueled.right.comp PolyFueled.left
  have hj := PolyFueled.right
  have hcanonical := hk.pair hj
  have hentry := (h.gradualEntry_polySeg low δ).comp hk
  have hbase := h.coefficient_poly.comp hcanonical
  have hbuy := PolySegStream.serialize_mul hentry hbase
  have helapsedRaw := predc_polyFueled.comp (subc_polyFueled.comp (hn.pair hk))
  have helapsed : PolyFueled
      (predc.comp (subc.comp
        ((Nat.Partrec.Code.right.comp Nat.Partrec.Code.left).pair
          (Nat.Partrec.Code.left.comp Nat.Partrec.Code.left)))) (fun z =>
      z.unpair.1.unpair.2 - z.unpair.1.unpair.1 - 1) := by
    apply PolyFueled.of_eq helapsedRaw
    intro z
    simp only [Function.comp_apply, Nat.unpair_pair, Nat.pred_eq_sub_one]
  have hsellFraction := (h.gradualSellFraction_polySeg high δ).comp (hk.pair helapsed)
  have hneg : PolySegStream (fun _ => (EF.const (-1)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
  have houter := PolySegStream.serialize_mul hneg
    (PolySegStream.serialize_mul hentry hsellFraction)
  have hsell := PolySegStream.serialize_mul houter hbase
  have hneq := subc_polyFueled.comp (hn.pair hk)
  have hken := subc_polyFueled.comp (hk.pair hn)
  have heqtestRaw := hadd.comp (hneq.pair hken)
  have heqtest : PolyFueled
      (cadd.comp
        ((subc.comp
          ((Nat.Partrec.Code.right.comp Nat.Partrec.Code.left).pair
            (Nat.Partrec.Code.left.comp Nat.Partrec.Code.left))).pair
          (subc.comp
            ((Nat.Partrec.Code.left.comp Nat.Partrec.Code.left).pair
              (Nat.Partrec.Code.right.comp Nat.Partrec.Code.left))))) (fun z =>
      (z.unpair.1.unpair.2 - z.unpair.1.unpair.1) +
        (z.unpair.1.unpair.1 - z.unpair.1.unpair.2)) := by
    apply PolyFueled.of_eq heqtestRaw
    intro z
    simp only [Function.comp_apply, Nat.unpair_pair]
  refine PolySegStream.of_eq (PolySegStream.ifZero hbuy hsell heqtest) ?_
  intro z
  simp only [gradualCoefficient, Function.comp_apply, Nat.unpair_pair, ifzSelFn]
  by_cases heq : z.unpair.1.unpair.2 = z.unpair.1.unpair.1
  · simp [heq]
  · have htest : z.unpair.1.unpair.2 - z.unpair.1.unpair.1 +
        (z.unpair.1.unpair.1 - z.unpair.1.unpair.2) ≠ 0 := by omega
    rw [if_neg htest, if_neg heq]

theorem PolySequence.gradualFamily_trades_eq {As : ℕ → AffineCombination}
    (h : PolySequence As) (low high δ : ℚ) (k n : ℕ) :
    (((gradualFamily As low high δ h) k).strat n).trades =
      (List.range (gradualTradeCount h (Nat.pair k n))).map (fun j =>
        let z := Nat.pair (Nat.pair k n) j
        (gradualCoefficient h low high δ z, gradualSentence h z)) := by
  by_cases hbefore : n < k
  · simp [gradualFamily, gradualTrader, ne_of_lt hbefore,
      Nat.not_lt.mpr (Nat.le_of_lt hbefore), emptyStrategy, gradualTradeCount, hbefore]
  · have hkn : k ≤ n := by omega
    by_cases heq : n = k
    · subst n
      simp only [gradualFamily, gradualTrader, ↓reduceDIte]
      rw [AffineCombination.buy_trades, AffineCombination.scale, h.terms_eq]
      simp [gradualTradeCount, gradualCoefficient, gradualSentence]
    · have hlt : k < n := lt_of_le_of_ne hkn (Ne.symm heq)
      simp only [gradualFamily, gradualTrader, heq, hlt, ↓reduceDIte]
      rw [AffineCombination.buy_trades, AffineCombination.scale, h.terms_eq]
      simp [gradualTradeCount, hkn, gradualCoefficient, gradualSentence, heq,
        List.map_map, Function.comp_apply]

/-- The gradual affine components form a structured efficiently emulatable family. -/
noncomputable def PolySequence.gradualFamilyPolyTrade {As : ℕ → AffineCombination}
    (h : PolySequence As) (low high δ : ℚ) :
    PolyTradeEmulatable (gradualFamily As low high δ h) := by
  let ccount := Classical.choose h.gradualTradeCount_poly
  have hcount := Classical.choose_spec h.gradualTradeCount_poly
  let csentence := Classical.choose h.sentence_poly
  have hsentence := Classical.choose_spec h.sentence_poly
  have hk := PolyFueled.left.comp PolyFueled.left
  have hj := PolyFueled.right
  have hcanonical := hk.pair hj
  have hcoeff := h.gradualCoefficient_polySeg low high δ
  have htag : PolySegStream (fun _ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  have hsentencePF : PolyFueled
      (csentence.comp
        ((Nat.Partrec.Code.left.comp Nat.Partrec.Code.left).pair Nat.Partrec.Code.right))
      (fun z => Encodable.encode (gradualSentence h z)) := by
    apply PolyFueled.of_eq (hsentence.comp hcanonical)
    intro z
    rfl
  have hsentenceSeg : PolySegStream (fun z => [Encodable.encode (gradualSentence h z)]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok hsentencePF)
  have hone : PolySegStream (fun z => serializeTrades
      [(gradualCoefficient h low high δ z, gradualSentence h z)]) := by
    refine PolySegStream.of_eq ((hcoeff.append htag).append hsentenceSeg) ?_
    intro z
    simp [serializeTrades, List.append_assoc]
  have hserialized : PolySegStream (fun z => serializeTrades
      (((gradualFamily As low high δ h) z.unpair.1).strat z.unpair.2).trades) := by
    refine PolySegStream.of_eq (PolySegStream.concatVar hone hcount) ?_
    intro z
    rw [h.gradualFamily_trades_eq]
    rw [serializeTrades_map_singleton]
    simp only [Nat.pair_unpair]
  have hzero : ∀ k n, n < k →
      (((gradualFamily As low high δ h) k).strat n).trades = [] := by
    intro k n hnk
    rw [h.gradualFamily_trades_eq]
    simp [gradualTradeCount, hnk]
  refine
    { emulatable := EfficientlyEmulatable.of_polySeg hzero hserialized
      tradeCount := gradualTradeCount h
      coefficient := gradualCoefficient h low high δ
      sentence := gradualSentence h
      tradeCount_poly := ⟨ccount, hcount⟩
      coefficient_poly := hcoeff
      sentence_poly := ⟨csentence.comp
        ((Nat.Partrec.Code.left.comp Nat.Partrec.Code.left).pair Nat.Partrec.Code.right),
          hsentencePF⟩
      trades_eq := h.gradualFamily_trades_eq low high δ }

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

/-- Continuous-budget capstone for the gradual affine family.  If every component
eventually receives a full high-price signal and the protected opening spread pays a fixed
rate on its affine share risk, logical induction forces the launch-risk sizes to vanish. -/
theorem PolySequence.gradualRisk_converges {As : ℕ → AffineCombination}
    (h : PolySequence As) (V : History) (DP : DeductiveProcess)
    [IsLogicalInductor V DP] (start : ℕ) (low high δ : ℚ) (ε : ℝ)
    (hε : 0 < ε) (hδ : 0 < (δ : ℝ))
    (hmag : ∀ i, (As i).magnitude V ≤ 1)
    (hspread : ∀ i,
      (gradualEntry As low δ i).denote V * (ε * (As i).magnitude V) ≤
        (gradualEntry As low δ i).denote V *
          ((high : ℝ) - δ - (As i).price V i))
    (hfuture : ∀ i, start ≤ i →
      0 < (gradualEntry As low δ i).denote V →
        ∃ t, (high : ℝ) < (As i).price V (i + t + 1))
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun i => (gradualRisk As low δ i).denote V) 0 := by
  let entry := gradualEntry As low δ
  let baseOccupancy := gradualOccupancy As high δ
  let occupancy := gateOccupancy start baseOccupancy
  let baseα := gradualRisk As low δ
  let α := gateFeature start baseα
  let baseTs := gradualFamily As low high δ h
  let Ts := gateTraderFamily start baseTs
  have hentry0 : ∀ i, 0 ≤ (entry i).denote V := fun i =>
    (buyIndF_mem ((As i).priceFeature i) low δ V).1
  have hentry1 : ∀ i, (entry i).denote V ≤ 1 := fun i =>
    (buyIndF_mem ((As i).priceFeature i) low δ V).2
  have hα0 : ∀ i, 0 ≤ (α i).denote V := fun i => by
    by_cases hs : start ≤ i
    · simp only [α, gateFeature, hs, if_true, baseα, gradualRisk, riskFeature_denote]
      exact mul_nonneg (hentry0 i) ((As i).magnitude_nonneg V)
    · simp [α, gateFeature, hs]
  have hα1 : ∀ i, (α i).denote V ≤ 1 := fun i => by
    by_cases hs : start ≤ i
    · simp only [α, gateFeature, hs, if_true, baseα, gradualRisk, riskFeature_denote]
      calc
        (entry i).denote V * (As i).magnitude V ≤ 1 * (As i).magnitude V :=
          mul_le_mul_of_nonneg_right (hentry1 i) ((As i).magnitude_nonneg V)
        _ ≤ 1 := by simpa using hmag i
    · simp [α, gateFeature, hs]
  have hzero : ∀ i, (α i).denote V = 0 ∨
      ∃ N, ∀ n, N ≤ n → (occupancy i n).denote V = 0 := by
    intro i
    by_cases hs : start ≤ i
    · by_cases he : (entry i).denote V = 0
      · left
        simp [α, gateFeature, hs, baseα, gradualRisk, riskFeature_denote, entry, he]
      right
      obtain ⟨t, ht⟩ := hfuture i hs
        (lt_of_le_of_ne (hentry0 i) (Ne.symm he))
      have hfull : (sellIndF ((As i).priceFeature (i + t + 1)) high δ).denote V = 1 := by
        apply sellIndF_eq_one hδ
        rwa [(As i).priceFeature_denote]
      have hz := (As i).gradualRemaining_eq_zero_of_full_signal V i high δ t hfull
      refine ⟨i + t + 1, fun n hn => ?_⟩
      have hmono : ∀ s, t + 1 ≤ s →
          ((As i).gradualRemaining i high δ s).denote V = 0 := by
        intro s hts
        induction s, hts using Nat.le_induction with
        | base => exact hz
        | succ s _ ih => rw [gradualRemaining_denote_succ, ih, zero_mul]
      simpa [occupancy, gateOccupancy, hs, baseOccupancy, gradualOccupancy] using
        hmono (n - i) (by omega)
    · left
      simp [α, gateFeature, hs]
  have hworth : ∀ i n, i ≤ n → ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      ε * (α i).denote V * (1 - (occupancy i n).denote V) -
          (α i).denote V * (occupancy i n).denote V ≤
        (Ts i).netWorth V v n := by
    intro i n hin v hv
    by_cases hs : start ≤ i
    swap
    · simp [α, occupancy, Ts, gateFeature, gateOccupancy, gateTraderFamily, hs,
        Trader.zero_netWorth]
    let t := n - i
    have hday : i + t = n := by dsimp only [t]; omega
    let rem := ((As i).gradualRemaining i high δ t).denote V
    let mag := (As i).magnitude V
    have hrem0 : 0 ≤ rem := ((As i).gradualRemaining_mem V i high δ t).1
    have hrem1 : rem ≤ 1 := ((As i).gradualRemaining_mem V i high δ t).2
    have hincome : (1 - rem) * ((entry i).denote V * (ε * mag)) ≤
        (1 - rem) * ((entry i).denote V *
          ((high : ℝ) - δ - (As i).price V i)) :=
      mul_le_mul_of_nonneg_left (hspread i) (sub_nonneg.mpr hrem1)
    have hpartial := (As i).gradualTrader_netWorth_lower_partial (entry i) V v i high δ
      (h.gradualEntry_rank_le low δ i) (h.const_rank i) (h.terms_rank i)
      (hentry0 i) hδ (hP i) t
    rw [hday] at hpartial
    calc
      ε * (α i).denote V * (1 - (occupancy i n).denote V) -
            (α i).denote V * (occupancy i n).denote V =
          (1 - rem) * ((entry i).denote V * (ε * mag)) -
            (entry i).denote V * rem * mag := by
            simp only [α, gradualRisk, riskFeature_denote, occupancy, gradualOccupancy,
              gateFeature, gateOccupancy, hs, if_true, baseα, baseOccupancy, rem, mag, t]
            ring
      _ ≤ (1 - rem) * ((entry i).denote V *
            ((high : ℝ) - δ - (As i).price V i)) -
          (entry i).denote V * rem * mag := sub_le_sub_right hincome _
      _ = (entry i).denote V *
          ((1 - rem) * ((high : ℝ) - δ - (As i).price V i) - rem * mag) := by ring
      _ ≤ (Ts i).netWorth V v n := by
        simpa [Ts, gateTraderFamily, hs, baseTs, gradualFamily, entry, rem, mag] using hpartial
  have hconv := ROIBudget.noFractionalRepeatableReturn Ts V DP ε hε occupancy α
    (fun i => by
      by_cases hs : start ≤ i
      · simpa [α, gateFeature, hs, baseα] using h.gradualRisk_rank_le low δ i
      · simp [α, gateFeature, hs, EF.rank])
    (fun i n hin => by
      by_cases hs : start ≤ i
      · simpa [occupancy, gateOccupancy, hs, baseOccupancy] using
          h.gradualOccupancy_rank_le high δ i n hin
      · simp [occupancy, gateOccupancy, hs, EF.rank])
    (PolySegStream.gateFeature (h.gradualRisk_polySeg low δ) start)
    (PolySegStream.gateOccupancy (h.gradualOccupancy_polySeg high δ) start)
    (fun i ρ W => by
      by_cases hs : start ≤ i
      · simpa [α, gateFeature, hs, baseα] using h.gradualRisk_closed low δ i ρ W
      · simp [α, gateFeature, hs, EF.denoteWith])
    (fun i n ρ W => by
      by_cases hs : start ≤ i
      · simpa [occupancy, gateOccupancy, hs, baseOccupancy] using
          h.gradualOccupancy_closed high δ i n ρ W
      · simp [occupancy, gateOccupancy, hs, EF.denoteWith])
    (by
      constructor
      · intro i n
        by_cases hs : start ≤ i
        · simpa [occupancy, gateOccupancy, hs, baseOccupancy] using
            (gradualOccupancy_decreasing As V high δ).nonneg i n
        · simp [occupancy, gateOccupancy, hs]
      · intro i n
        by_cases hs : start ≤ i
        · simpa [occupancy, gateOccupancy, hs, baseOccupancy] using
            (gradualOccupancy_decreasing As V high δ).le_one i n
        · simp [occupancy, gateOccupancy, hs]
      · intro i n
        by_cases hs : start ≤ i
        · simpa [occupancy, gateOccupancy, hs, baseOccupancy] using
            (gradualOccupancy_decreasing As V high δ).antitone i n
        · simp [occupancy, gateOccupancy, hs])
    hzero hα0 hα1
    ((h.gradualFamilyPolyTrade low high δ).gateBefore start) hworth hworld
  refine Filter.Tendsto.congr' ?_ hconv
  filter_upwards [Filter.eventually_atTop.mpr ⟨start, fun _ hi => hi⟩] with i hi
  simp [α, gateFeature, hi, baseα]

/-- A polynomial affine family cannot remain frequently underpriced relative to an
eventually separated future supremum.  Only components with a nonzero buy signal require
liquidation; for those components, the current low price ensures the supremum witness is
strictly in the future. -/
theorem PolySequence.noPreemptiveUnderpricing {As : ℕ → AffineCombination}
    (h : PolySequence As) (V : History) (DP : DeductiveProcess)
    [IsLogicalInductor V DP]
    (hmag : ∀ i, (As i).magnitude V ≤ 1)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    NoPreemptiveUnderpricing
      (fun n => (As n).price V n) (affineFutureHigh As V) := by
  intro a b hab hfuture hcurrent
  obtain ⟨low, halow, hlowb⟩ := exists_rat_btwn hab
  obtain ⟨high, hlowhigh, hhighb⟩ := exists_rat_btwn hlowb
  have hquarter : 0 < ((high : ℝ) - (low : ℝ)) / 4 := by linarith
  obtain ⟨δ, hδ0, hδsmall⟩ := exists_rat_btwn hquarter
  have hδ : 0 < (δ : ℝ) := hδ0
  let ε : ℝ := (high : ℝ) - low - 2 * δ
  have hε : 0 < ε := by dsimp only [ε]; linarith
  obtain ⟨start, hstart⟩ := Filter.eventually_atTop.mp hfuture
  have hspread : ∀ i,
      (gradualEntry As low δ i).denote V * (ε * (As i).magnitude V) ≤
        (gradualEntry As low δ i).denote V *
          ((high : ℝ) - δ - (As i).price V i) := by
    intro i
    have hentry0 := (buyIndF_mem ((As i).priceFeature i) low δ V).1
    by_cases hz : (gradualEntry As low δ i).denote V = 0
    · simp [hz]
    have hentryPos : 0 < (gradualEntry As low δ i).denote V :=
      lt_of_le_of_ne hentry0 (Ne.symm hz)
    have hopen := buyIndF_pos_imp hδ hentryPos
    rw [(As i).priceFeature_denote] at hopen
    have hscaled : ε * (As i).magnitude V ≤ ε :=
      mul_le_of_le_one_right (le_of_lt hε) (hmag i)
    apply mul_le_mul_of_nonneg_left _ hentry0
    exact hscaled.trans (by dsimp only [ε]; linarith)
  have hfutureActive : ∀ i, start ≤ i →
      0 < (gradualEntry As low δ i).denote V →
        ∃ t, (high : ℝ) < (As i).price V (i + t + 1) := by
    intro i hi hentry
    have hopen := buyIndF_pos_imp hδ hentry
    rw [(As i).priceFeature_denote] at hopen
    have hsup : (high : ℝ) < affineFutureHigh As V i :=
      hhighb.trans (hstart i hi)
    obtain ⟨x, ⟨j, rfl⟩, hj⟩ :=
      exists_lt_of_lt_csSup (Set.range_nonempty
        (fun j => (As i).price V (i + j))) hsup
    cases j with
    | zero => simp only [Nat.add_zero] at hj; linarith
    | succ t => exact ⟨t, by simpa [Nat.add_assoc] using hj⟩
  have hconv := h.gradualRisk_converges V DP start low high δ ε hε hδ
    hmag hspread hfutureActive hP hworld
  let r : ℝ := (high : ℝ) - low
  have hr : 0 < r := by dsimp only [r]; linarith
  have hrisk : ∃ᶠ i in Filter.atTop,
      r ≤ (gradualRisk As low δ i).denote V := by
    refine (hcurrent.and_eventually (Filter.eventually_ge_atTop start)).mono ?_
    intro i hi
    have hentryOne : (gradualEntry As low δ i).denote V = 1 := by
      apply buyIndF_eq_one hδ
      rw [(As i).priceFeature_denote]
      exact hi.1.trans halow
    obtain ⟨t, ht⟩ := hfutureActive i hi.2 (by rw [hentryOne]; norm_num)
    have hpriceBound := (As i).abs_price_sub_price_le_magnitude V i (i + t + 1)
      (hP i) (hP (i + t + 1))
    rw [abs_of_nonpos (by linarith [hi.1, halow, hlowhigh, ht])] at hpriceBound
    rw [gradualRisk, riskFeature_denote, hentryOne, one_mul]
    exact le_trans (le_of_lt (by dsimp only [r]; linarith [hi.1, ht])) hpriceBound
  have hevent : ∀ᶠ i in Filter.atTop,
      (gradualRisk As low δ i).denote V < r := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv r hr
    refine Filter.eventually_atTop.mpr ⟨N, fun i hi => ?_⟩
    have hnear := hN i hi
    have hrisk0 : 0 ≤ (gradualRisk As low δ i).denote V := by
      rw [gradualRisk, riskFeature_denote]
      exact mul_nonneg
        (buyIndF_mem ((As i).priceFeature i) low δ V).1
        ((As i).magnitude_nonneg V)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hrisk0] at hnear
    exact hnear
  obtain ⟨i, hirisk, hir⟩ := (hrisk.and_eventually hevent).exists
  exact (not_lt_of_ge hirisk) hir

theorem affineFutureHigh_neg (As : ℕ → AffineCombination) (V : History) (n : ℕ) :
    affineFutureHigh (fun i => (As i).neg) V n = -affineFutureLow As V n := by
  simp only [affineFutureHigh, affineFutureLow, neg_price]
  rw [show Set.range (fun j => -(As n).price V (n + j)) =
      -(Set.range (fun j => (As n).price V (n + j))) by
    ext x
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by linarith⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by linarith⟩]
  exact Real.sSup_neg _

/-- The overpricing half is the underpricing construction applied to the uniformly
emittable pointwise negation of the affine family. -/
theorem PolySequence.noPreemptiveOverpricing {As : ℕ → AffineCombination}
    (h : PolySequence As) (V : History) (DP : DeductiveProcess)
    [IsLogicalInductor V DP]
    (hmag : ∀ i, (As i).magnitude V ≤ 1)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    NoPreemptiveOverpricing
      (fun n => (As n).price V n) (affineFutureLow As V) := by
  intro a b hab hfuture hcurrent
  have hneg := h.neg.noPreemptiveUnderpricing V DP
    (fun i => by simpa only [neg_magnitude] using hmag i) hP hworld
  apply hneg (-b) (-a) (by linarith)
  · filter_upwards [hfuture] with n hn
    rw [affineFutureHigh_neg]
    linarith
  · exact hcurrent.mono (fun n hn => by
      change (As n).neg.price V n < -b
      rw [neg_price]
      linarith)

/-- Operational affine preemptive learning, obtained from the two gradual-return
constructions. -/
theorem PolySequence.noPreemptiveGaps {As : ℕ → AffineCombination}
    (h : PolySequence As) (V : History) (DP : DeductiveProcess)
    [IsLogicalInductor V DP]
    (hmag : ∀ i, (As i).magnitude V ≤ 1)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AffineNoPreemptiveGaps As V :=
  ⟨h.noPreemptiveUnderpricing V DP hmag hP hworld,
    h.noPreemptiveOverpricing V DP hmag hP hworld⟩

/-- Paper-facing affine preemptive-learning capstone for normalized polynomial affine
families with bounded cross-time prices. -/
theorem PolySequence.affpolymax {As : ℕ → AffineCombination}
    (h : PolySequence As) (V : History) (DP : DeductiveProcess)
    [IsLogicalInductor V DP]
    (hbounded : BoundedAffinePrices As V)
    (hmag : ∀ i, (As i).magnitude V ≤ 1)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => (As n).price V n) atTop =
        liminf (affineFutureHigh As V) atTop ∧
      limsup (fun n => (As n).price V n) atTop =
        limsup (affineFutureLow As V) atTop :=
  affpolymax_of_noPreemptiveGaps As V hbounded
    (h.noPreemptiveGaps V DP hmag hP hworld)

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
#print axioms AffineCombination.PolySequence.gradualRisk_converges
#print axioms AffineCombination.gradualTrader_netWorth_lower_of_full_signal
#print axioms AffineCombination.gradualTrader_magnitude_of_full_signal
#print axioms AffineCombination.gradualTrader_hasROI_of_full_signal
#print axioms AffineCombination.gradualTrader_hasROI_of_price_gap
#print axioms AffineCombination.PolySequence.noPreemptiveUnderpricing
#print axioms AffineCombination.PolySequence.noPreemptiveOverpricing
#print axioms AffineCombination.PolySequence.noPreemptiveGaps
#print axioms AffineCombination.PolySequence.affpolymax

end LogicalInduction
