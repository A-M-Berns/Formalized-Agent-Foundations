import LogicalInduction.Construction.M7Witnesses

/-!
# Concrete feedback-trader emission (`M7-FEEDBACK-EMIT`)

The feedback trader is indexed by a deferral function whose program runs in time
polynomial in its *output*, not necessarily in its input.  On day `n` we therefore run
that program only for the polynomial clock justified when its output is exactly `n`.
Successful runs are sound by partial-function uniqueness; unfinished runs emit no trade.

This file turns that bounded schedule into the literal coefficient/sentence streams of
`AffineCombination.feedbackTrader`.  It contains no market or convergence argument.
-/

namespace LogicalInduction
namespace FeedbackEmission

open AffineCombination PrefixPatchCompile

-- Deep products below use `Nat.unpair` through `Primcodable`; keep its square-root
-- implementation opaque during elaboration (the standard `dd:fuel` compiler gotcha).
attribute [local irreducible] Nat.sqrt

/-- Run the deferral program for component `k` with the day-`n` polynomial clock.
Input is `⟨n,k⟩`; output is normalized as `0` for unfinished and `f k + 1` for finished. -/
def scheduledRun (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  deadlineRun f (ecClock a degree z.unpair.1) z.unpair.2

/-- The bounded scheduled run is polynomial in the paired day/component input. -/
theorem scheduledRun_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledRun f a degree) := by
  obtain ⟨csim, hsim⟩ := codeEvalnNat_polyFueled f.code
  obtain ⟨cclock, hclock⟩ := ecClock_polyFueled a degree
  refine ⟨_, (hsim.comp ((hclock.comp PolyFueled.left).pair PolyFueled.right)).of_eq
    (fun z => ?_)⟩
  simp [scheduledRun, deadlineRun]

/-- `1` exactly when the day-bounded run has returned the current day `n`.
The natural-valued flag is the form consumed by the flat stream combinators. -/
def scheduledMatch (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  if scheduledRun f a degree z = z.unpair.1 + 1 then 1 else 0

/-- Equality of the scheduled output and the variable day is polynomially decidable. -/
theorem scheduledMatch_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledMatch f a degree) := by
  obtain ⟨crun, hrun⟩ := scheduledRun_polyFueled f a degree
  have hday : PolyFueled _ (fun z : ℕ => z.unpair.1 + 1) :=
    (PolyFueled.left.succ_comp)
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hleft : PolyFueled _ (fun z =>
      scheduledRun f a degree z - (z.unpair.1 + 1)) :=
    (subc_polyFueled.comp (hrun.pair hday)).of_eq (fun z => by simp)
  have hright : PolyFueled _ (fun z =>
      (z.unpair.1 + 1) - scheduledRun f a degree z) :=
    (subc_polyFueled.comp (hday.pair hrun)).of_eq (fun z => by simp)
  have hgap : PolyFueled _ (fun z =>
      (scheduledRun f a degree z - (z.unpair.1 + 1)) +
        ((z.unpair.1 + 1) - scheduledRun f a degree z)) :=
    (hadd.comp (hleft.pair hright)).of_eq (fun z => by simp)
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 1).pair (PolyFueled.const 0)).pair hgap)).of_eq
      (fun z => ?_)⟩
  simp only [ifzSelFn, Nat.unpair_pair, scheduledMatch]
  by_cases h : scheduledRun f a degree z = z.unpair.1 + 1
  · have hz : (scheduledRun f a degree z - (z.unpair.1 + 1)) +
        ((z.unpair.1 + 1) - scheduledRun f a degree z) = 0 := by omega
    rw [if_pos hz, if_pos h]
  · have hz : (scheduledRun f a degree z - (z.unpair.1 + 1)) +
        ((z.unpair.1 + 1) - scheduledRun f a degree z) ≠ 0 := by omega
    rw [if_neg hz, if_neg h]

/-- A successful match is sound even though the program was run only for the day clock. -/
theorem scheduledMatch_eq_one_iff
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (n k : ℕ) :
    scheduledMatch f a degree (Nat.pair n k) = 1 ↔ f k = n := by
  constructor
  · intro h
    have hrun : scheduledRun f a degree (Nat.pair n k) = n + 1 := by
      simpa [scheduledMatch] using h
    have hpos : 0 < scheduledRun f a degree (Nat.pair n k) := by omega
    have hsound := deadlineRun_eq f hpos
    simp only [scheduledRun, Nat.unpair_pair] at hsound hrun
    omega
  · intro h
    subst n
    simp [scheduledMatch, scheduledRun, deadlineRun, codeEvalnNat, hspec]

/-- The decoded value of the scheduled run, with the unfinished sentinel normalized to
zero.  Input is again `⟨day,component⟩`. -/
def scheduledValue (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  scheduledRun f a degree z - 1

/-- Decoding the bounded run preserves polynomial fuel. -/
theorem scheduledValue_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledValue f a degree) := by
  obtain ⟨crun, hrun⟩ := scheduledRun_polyFueled f a degree
  exact ⟨_, (predc_polyFueled.comp hrun).of_eq (fun z => by
    simp [scheduledValue, Nat.pred_eq_sub_one])⟩

/-- The standard evaluator clock is monotone in its day argument. -/
theorem ecClock_mono (a degree : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ecClock a degree m ≤ ecClock a degree n := by
  simp only [ecClock]
  gcongr

/-- Once the runtime day reaches `f k`, the scheduled value has converged to the true
deferral value.  This is the lookup fact used by every feedback feature emitted on that
day. -/
theorem scheduledValue_eq
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {n k : ℕ} (hkn : f k ≤ n) :
    scheduledValue f a degree (Nat.pair n k) = f k := by
  have hbase : deadlineRun f (ecClock a degree (f k)) k = f k + 1 := by
    simp [deadlineRun, codeEvalnNat, hspec]
  have hpos : 0 < deadlineRun f (ecClock a degree (f k)) k := by
    rw [hbase]
    omega
  have hrun := deadlineRun_mono f (ecClock_mono a degree hkn) hpos
  simp only [scheduledValue, scheduledRun, Nat.unpair_pair]
  rw [hrun, hbase]
  omega

/-- Day-indexed notation for the decoded bounded deferral lookup. -/
def scheduledDeferral (f : DeferralFunction) (a degree n k : ℕ) : ℕ :=
  scheduledValue f a degree (Nat.pair n k)

theorem scheduledDeferral_eq
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {n k : ℕ} (hkn : f k ≤ n) :
    scheduledDeferral f a degree n k = f k :=
  scheduledValue_eq f hspec hkn

/-- Bounded-schedule version of one feedback return feature. -/
def scheduledReturnFeature (As : ℕ → AffineCombination)
    (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : EF :=
  let n := z.unpair.1
  let k := z.unpair.2
  EF.add
    ((As (scheduledDeferral f a degree n k)).priceFeature
      (scheduledDeferral f a degree n (k + 1)))
    (EF.mul (EF.const (-1))
      ((As (scheduledDeferral f a degree n k)).priceFeature
        (scheduledDeferral f a degree n k)))

/-- Bounded-schedule version of one multiplicative Kelly factor. -/
def scheduledFactorFeature (As : ℕ → AffineCombination) (W : ℕ → EF)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (z : ℕ) : EF :=
  let n := z.unpair.1
  let k := z.unpair.2
  EF.add (EF.const 1)
    (EF.mul
      (EF.mul (EF.const δ) (W (scheduledDeferral f a degree n k)))
      (scheduledReturnFeature As f a degree z))

/-- Bounded-schedule wealth syntax before component `k` on runtime day `n`. -/
def scheduledWealthFeature (As : ℕ → AffineCombination) (W : ℕ → EF)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (z : ℕ) : EF :=
  ROIBudget.prodFeatures ((List.range z.unpair.2).map (fun j ↦
    scheduledFactorFeature As W f a degree δ (Nat.pair z.unpair.1 j)))

/-- Bounded-schedule shares for component `k` on runtime day `n`. -/
def scheduledBetaFeature (As : ℕ → AffineCombination) (W : ℕ → EF)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (z : ℕ) : EF :=
  EF.mul
    (EF.mul (EF.const δ) (scheduledWealthFeature As W f a degree δ z))
    (W (scheduledDeferral f a degree z.unpair.1 z.unpair.2))

theorem scheduledReturnFeature_eq
    (As : ℕ → AffineCombination) (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {n k : ℕ} (hcur : f k ≤ n) (hnext : f (k + 1) ≤ n) :
    scheduledReturnFeature As f a degree (Nat.pair n k) =
      feedbackReturnFeature As f k := by
  simp [scheduledReturnFeature, feedbackReturnFeature,
    scheduledDeferral_eq f hspec hcur, scheduledDeferral_eq f hspec hnext]

theorem scheduledFactorFeature_eq
    (As : ℕ → AffineCombination) (W : ℕ → EF)
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (δ : ℚ) {n k : ℕ} (hcur : f k ≤ n) (hnext : f (k + 1) ≤ n) :
    scheduledFactorFeature As W f a degree δ (Nat.pair n k) =
      feedbackFactorFeature As W f δ k := by
  simp [scheduledFactorFeature, feedbackFactorFeature,
    scheduledReturnFeature_eq As f hspec hcur hnext,
    scheduledDeferral_eq f hspec hcur]

theorem scheduledWealthFeature_eq
    {As : ℕ → AffineCombination} {W : ℕ → EF}
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (δ : ℚ) {n k : ℕ} (hk : f k ≤ n) :
    scheduledWealthFeature As W f a degree δ (Nat.pair n k) =
      feedbackWealthFeature As W f δ k := by
  simp only [scheduledWealthFeature, feedbackWealthFeature, Nat.unpair_pair]
  apply congrArg ROIBudget.prodFeatures
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  apply scheduledFactorFeature_eq As W f hspec δ
  · exact (hstrict.monotone (by omega)).trans hk
  · exact (hstrict.monotone (by omega)).trans hk

theorem scheduledBetaFeature_eq
    {As : ℕ → AffineCombination} {W : ℕ → EF}
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (δ : ℚ) {n k : ℕ} (hk : f k ≤ n) :
    scheduledBetaFeature As W f a degree δ (Nat.pair n k) =
      feedbackBetaFeature As W f δ k := by
  simp [scheduledBetaFeature, feedbackBetaFeature,
    scheduledWealthFeature_eq hstrict hspec δ hk,
    scheduledDeferral_eq f hspec hk]

/-! ### Polynomial syntax streams for the scheduled features -/

theorem scheduledDeferral_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (fun z ↦
      scheduledDeferral f a degree z.unpair.1 z.unpair.2) := by
  obtain ⟨c, h⟩ := scheduledValue_polyFueled f a degree
  exact ⟨c, h.of_eq (fun z => by simp [scheduledDeferral])⟩

theorem scheduledReturnFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    PolySegStream (fun z ↦ (scheduledReturnFeature As f a degree z).serialize) := by
  obtain ⟨cvalue, hvalue⟩ := scheduledValue_polyFueled f a degree
  have hcur : PolyFueled cvalue (fun z ↦
      scheduledDeferral f a degree z.unpair.1 z.unpair.2) :=
    hvalue.of_eq (fun z => by simp [scheduledDeferral])
  have hnextInput : PolyFueled _ (fun z : ℕ ↦
      Nat.pair z.unpair.1 (z.unpair.2 + 1)) :=
    PolyFueled.left.pair PolyFueled.right.succ_comp
  have hnext : PolyFueled _ (fun z ↦
      scheduledDeferral f a degree z.unpair.1 (z.unpair.2 + 1)) :=
    (hvalue.comp hnextInput).of_eq (fun z => by simp [scheduledDeferral])
  have hfuture := hpoly.priceFeature_polySeg.comp (hcur.pair hnext)
  have hpresent := hpoly.priceFeature_polySeg.comp (hcur.pair hcur)
  have hneg : PolySegStream (fun _ ↦ (EF.const (-1)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
  simpa [scheduledReturnFeature] using
    PolySegStream.serialize_add hfuture
      (PolySegStream.serialize_mul hneg hpresent)

theorem scheduledFactorFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    PolySegStream (fun z ↦ (scheduledFactorFeature As W f a degree δ z).serialize) := by
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  have hweight := hW.polySeg.comp hvalue
  have hone : PolySegStream (fun _ ↦ (EF.const 1).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)
  have hdelta : PolySegStream (fun _ ↦ (EF.const δ).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const δ)
  have hreturn := scheduledReturnFeature_polySeg hpoly f a degree
  simpa [scheduledFactorFeature] using PolySegStream.serialize_add hone
    (PolySegStream.serialize_mul
      (PolySegStream.serialize_mul hdelta hweight) hreturn)

theorem scheduledWealthFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    PolySegStream (fun z ↦ (scheduledWealthFeature As W f a degree δ z).serialize) := by
  have hfactor := scheduledFactorFeature_polySeg hpoly hW f a degree δ
  have hcanonical : PolyFueled _ (fun q : ℕ ↦
      Nat.pair q.unpair.1.unpair.1 q.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hblocks := PolySegStream.concatVar (hfactor.comp hcanonical) PolyFueled.right
  have hone : PolySegStream (fun _ ↦ (EF.const 1).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)
  have htags := PolySegStream.repeatTag 3 PolyFueled.right
  refine PolySegStream.of_eq ((hblocks.append hone).append htags) ?_
  intro z
  unfold scheduledWealthFeature
  rw [ROIBudget.serialize_prodFeatures]
  simp only [List.flatMap_map, List.length_map,
    List.length_range, Nat.unpair_pair, List.append_assoc]

theorem scheduledBetaFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    PolySegStream (fun z ↦ (scheduledBetaFeature As W f a degree δ z).serialize) := by
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  have hdelta : PolySegStream (fun _ ↦ (EF.const δ).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const δ)
  have hwealth := scheduledWealthFeature_polySeg hpoly hW f a degree δ
  have hweight := hW.polySeg.comp hvalue
  simpa [scheduledBetaFeature] using PolySegStream.serialize_mul
    (PolySegStream.serialize_mul hdelta hwealth) hweight

end FeedbackEmission
end LogicalInduction
