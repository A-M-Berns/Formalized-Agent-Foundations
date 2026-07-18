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

theorem scheduledMatch_zero_or_one (f : DeferralFunction) (a degree z : ℕ) :
    scheduledMatch f a degree z = 0 ∨ scheduledMatch f a degree z = 1 := by
  simp only [scheduledMatch]
  split <;> simp

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

/-! ### Conditional affine-term blocks and their flattened index -/

/-- Number of affine terms emitted by component `k` on day `n`.  An opening match takes
priority; strict increase later proves that the opening and closing cases cannot overlap. -/
def scheduledTermCount {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  let n := z.unpair.1
  let k := z.unpair.2
  let count := hpoly.termCount (scheduledDeferral f a degree n k)
  if scheduledMatch f a degree z = 1 then count
  else if scheduledMatch f a degree (Nat.pair n (k + 1)) = 1 then count
  else 0

theorem scheduledTermCount_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledTermCount hpoly f a degree) := by
  obtain ⟨cmatch, hmatch⟩ := scheduledMatch_polyFueled f a degree
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  obtain ⟨ccount, hcount⟩ := hpoly.termCount_poly
  have hbase := hcount.comp hvalue
  have hnextInput : PolyFueled _ (fun z : ℕ ↦
      Nat.pair z.unpair.1 (z.unpair.2 + 1)) :=
    PolyFueled.left.pair PolyFueled.right.succ_comp
  have hclose := hmatch.comp hnextInput
  have hcloseCount := ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair hbase).pair hclose)
  refine ⟨_, (ifzSel_polyFueled.comp
    ((hcloseCount.pair hbase).pair hmatch)).of_eq (fun z => ?_)⟩
  simp only [ifzSelFn]
  rcases scheduledMatch_zero_or_one f a degree z with hopen | hopen
  · rcases scheduledMatch_zero_or_one f a degree
        (Nat.pair z.unpair.1 (z.unpair.2 + 1)) with hclose | hclose
    · simp [scheduledTermCount, hopen, hclose]
    · simp [scheduledTermCount, hopen, hclose]
  · simp [scheduledTermCount, hopen]

/-- Coefficient at `q = ⟨⟨n,k⟩,j⟩` inside a nonempty scheduled component block.
The closing syntax deliberately retains the literal nested multiplication from
`AffineCombination.neg`. -/
def scheduledTermCoefficient
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (W : ℕ → EF) (f : DeferralFunction) (a degree : ℕ) (δ : ℚ)
    (q : ℕ) : EF :=
  let z := q.unpair.1
  let n := z.unpair.1
  let k := z.unpair.2
  let j := q.unpair.2
  let base := EF.mul (scheduledBetaFeature As W f a degree δ z)
    (hpoly.coefficient (Nat.pair (scheduledDeferral f a degree n k) j))
  if scheduledMatch f a degree z = 1 then base
  else EF.mul (EF.const (-1)) base

def scheduledTermSentence
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) (q : ℕ) : Sentence :=
  let z := q.unpair.1
  hpoly.sentence (Nat.pair
    (scheduledDeferral f a degree z.unpair.1 z.unpair.2) q.unpair.2)

theorem scheduledTermCoefficient_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    PolySegStream (fun q ↦
      (scheduledTermCoefficient hpoly W f a degree δ q).serialize) := by
  obtain ⟨cmatch, hmatch⟩ := scheduledMatch_polyFueled f a degree
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  have hblockValue := hvalue.comp PolyFueled.left
  have hcanonical := hblockValue.pair PolyFueled.right
  have hcoefficient := hpoly.coefficient_poly.comp hcanonical
  have hbeta := (scheduledBetaFeature_polySeg hpoly hW f a degree δ).comp PolyFueled.left
  have hbase := PolySegStream.serialize_mul hbeta hcoefficient
  have hneg : PolySegStream (fun _ ↦ (EF.const (-1)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
  have hclosing := PolySegStream.serialize_mul hneg hbase
  refine PolySegStream.of_eq
    (PolySegStream.ifZero hclosing hbase (hmatch.comp PolyFueled.left)) ?_
  intro q
  rcases scheduledMatch_zero_or_one f a degree q.unpair.1 with hopen | hopen
  · simp [scheduledTermCoefficient, hopen]
  · simp [scheduledTermCoefficient, hopen]

theorem scheduledTermSentence_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (fun q ↦
      Encodable.encode (scheduledTermSentence hpoly f a degree q)) := by
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  obtain ⟨csentence, hsentence⟩ := hpoly.sentence_poly
  have hcanonical := (hvalue.comp PolyFueled.left).pair PolyFueled.right
  exact ⟨_, (hsentence.comp hcanonical).of_eq (fun q => by
    simp [scheduledTermSentence])⟩

/-- Literal conditional trade block for component `k` on day `n`. -/
def scheduledTradeBlock
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (W : ℕ → EF) (f : DeferralFunction) (a degree : ℕ) (δ : ℚ)
    (z : ℕ) : List (EF × Sentence) :=
  (List.range (scheduledTermCount hpoly f a degree z)).map (fun j ↦
    (scheduledTermCoefficient hpoly W f a degree δ (Nat.pair z j),
      scheduledTermSentence hpoly f a degree (Nat.pair z j)))

@[simp] theorem scheduledTradeBlock_length
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (W : ℕ → EF) (f : DeferralFunction) (a degree : ℕ) (δ : ℚ)
    (z : ℕ) :
    (scheduledTradeBlock hpoly W f a degree δ z).length =
      scheduledTermCount hpoly f a degree z := by
  simp [scheduledTradeBlock]

/-- Total width of all component blocks potentially active on day `n`. -/
def scheduledTradeCount
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree n : ℕ) : ℕ :=
  segPrefix (scheduledTermCount hpoly f a degree) n (n + 1)

/-- Component block containing flattened day-term `j`. -/
def scheduledTradeMember
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree n j : ℕ) : ℕ :=
  segLocate (scheduledTermCount hpoly f a degree) n j (n + 1)

/-- Offset of flattened day-term `j` inside its component block. -/
def scheduledTradeOffset
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree n j : ℕ) : ℕ :=
  j - segPrefix (scheduledTermCount hpoly f a degree) n
    (scheduledTradeMember hpoly f a degree n j)

theorem scheduledTradeCount_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledTradeCount hpoly f a degree) := by
  obtain ⟨clen, hlen⟩ := scheduledTermCount_polyFueled hpoly f a degree
  obtain ⟨cprefix, hprefix⟩ := segPrefix_polyFueled hlen
  exact ⟨_, (hprefix.comp (PolyFueled.id.pair PolyFueled.id.succ_comp)).of_eq
    (fun n => by simp [scheduledTradeCount])⟩

theorem scheduledTradeMember_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (fun z ↦
      scheduledTradeMember hpoly f a degree z.unpair.1 z.unpair.2) := by
  obtain ⟨clen, hlen⟩ := scheduledTermCount_polyFueled hpoly f a degree
  obtain ⟨clocate, hlocate⟩ := segLocate_polyFueled hlen
  have hinput : PolyFueled _ (fun z : ℕ ↦ Nat.pair z (z.unpair.1 + 1)) :=
    PolyFueled.id.pair PolyFueled.left.succ_comp
  exact ⟨_, (hlocate.comp hinput).of_eq (fun z => by
    simp [scheduledTradeMember])⟩

theorem scheduledTradeOffset_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (fun z ↦
      scheduledTradeOffset hpoly f a degree z.unpair.1 z.unpair.2) := by
  obtain ⟨clen, hlen⟩ := scheduledTermCount_polyFueled hpoly f a degree
  obtain ⟨cprefix, hprefix⟩ := segPrefix_polyFueled hlen
  obtain ⟨cmember, hmember⟩ := scheduledTradeMember_polyFueled hpoly f a degree
  have hp := hprefix.comp (PolyFueled.left.pair hmember)
  exact ⟨_, (subc_polyFueled.comp (PolyFueled.right.pair hp)).of_eq (fun z => by
    simp [scheduledTradeOffset])⟩

def scheduledTradeCoefficient
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (W : ℕ → EF) (f : DeferralFunction) (a degree : ℕ) (δ : ℚ)
    (z : ℕ) : EF :=
  scheduledTermCoefficient hpoly W f a degree δ (Nat.pair
    (Nat.pair z.unpair.1
      (scheduledTradeMember hpoly f a degree z.unpair.1 z.unpair.2))
    (scheduledTradeOffset hpoly f a degree z.unpair.1 z.unpair.2))

def scheduledTradeSentence
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : Sentence :=
  scheduledTermSentence hpoly f a degree (Nat.pair
    (Nat.pair z.unpair.1
      (scheduledTradeMember hpoly f a degree z.unpair.1 z.unpair.2))
    (scheduledTradeOffset hpoly f a degree z.unpair.1 z.unpair.2))

theorem scheduledTradeCoefficient_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    PolySegStream (fun z ↦
      (scheduledTradeCoefficient hpoly W f a degree δ z).serialize) := by
  obtain ⟨cmember, hmember⟩ := scheduledTradeMember_polyFueled hpoly f a degree
  obtain ⟨coffset, hoffset⟩ := scheduledTradeOffset_polyFueled hpoly f a degree
  have hcanonical := (PolyFueled.left.pair hmember).pair hoffset
  simpa [scheduledTradeCoefficient] using
    (scheduledTermCoefficient_polySeg hpoly hW f a degree δ).comp hcanonical

theorem scheduledTradeSentence_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (fun z ↦
      Encodable.encode (scheduledTradeSentence hpoly f a degree z)) := by
  obtain ⟨cmember, hmember⟩ := scheduledTradeMember_polyFueled hpoly f a degree
  obtain ⟨coffset, hoffset⟩ := scheduledTradeOffset_polyFueled hpoly f a degree
  obtain ⟨cterm, hterm⟩ := scheduledTermSentence_polyFueled hpoly f a degree
  have hcanonical := (PolyFueled.left.pair hmember).pair hoffset
  exact ⟨_, (hterm.comp hcanonical).of_eq (fun z => by
    simp [scheduledTradeSentence])⟩

end FeedbackEmission
end LogicalInduction
