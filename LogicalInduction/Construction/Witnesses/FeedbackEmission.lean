import LogicalInduction.Construction.Witnesses.M7Witnesses

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
lemma scheduledRun_polyFueled (f : DeferralFunction) (a degree : ℕ) :
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
lemma scheduledMatch_polyFueled (f : DeferralFunction) (a degree : ℕ) :
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

lemma scheduledMatch_zero_or_one (f : DeferralFunction) (a degree z : ℕ) :
    scheduledMatch f a degree z = 0 ∨ scheduledMatch f a degree z = 1 := by
  simp only [scheduledMatch]
  split <;> simp

/-- A successful match is sound even though the program was run only for the day clock. -/
lemma scheduledMatch_eq_one_iff
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

lemma scheduledMatch_eq_zero_iff
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (n k : ℕ) :
    scheduledMatch f a degree (Nat.pair n k) = 0 ↔ f k ≠ n := by
  constructor
  · intro hzero heq
    have hone := (scheduledMatch_eq_one_iff f hspec n k).2 heq
    omega
  · intro hne
    rcases scheduledMatch_zero_or_one f a degree (Nat.pair n k) with hzero | hone
    · exact hzero
    · exact (hne ((scheduledMatch_eq_one_iff f hspec n k).1 hone)).elim

/-- The decoded value of the scheduled run, with the unfinished sentinel normalized to
zero.  Input is again `⟨day,component⟩`. -/
def scheduledValue (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  scheduledRun f a degree z - 1

/-- Decoding the bounded run preserves polynomial fuel. -/
lemma scheduledValue_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledValue f a degree) := by
  obtain ⟨crun, hrun⟩ := scheduledRun_polyFueled f a degree
  exact ⟨_, (predc_polyFueled.comp hrun).of_eq (fun z => by
    simp [scheduledValue, Nat.pred_eq_sub_one])⟩

/-- The standard evaluator clock is monotone in its day argument. -/
lemma ecClock_mono (a degree : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ecClock a degree m ≤ ecClock a degree n := by
  simp only [ecClock]
  gcongr

/-- Once the runtime day reaches `f k`, the scheduled value has converged to the true
deferral value.  This is the lookup fact used by every feedback feature emitted on that
day. -/
lemma scheduledValue_eq
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

lemma scheduledDeferral_eq
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

lemma scheduledReturnFeature_eq
    (As : ℕ → AffineCombination) (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {n k : ℕ} (hcur : f k ≤ n) (hnext : f (k + 1) ≤ n) :
    scheduledReturnFeature As f a degree (Nat.pair n k) =
      feedbackReturnFeature As f k := by
  simp [scheduledReturnFeature, feedbackReturnFeature,
    scheduledDeferral_eq f hspec hcur, scheduledDeferral_eq f hspec hnext]

lemma scheduledFactorFeature_eq
    (As : ℕ → AffineCombination) (W : ℕ → EF)
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (δ : ℚ) {n k : ℕ} (hcur : f k ≤ n) (hnext : f (k + 1) ≤ n) :
    scheduledFactorFeature As W f a degree δ (Nat.pair n k) =
      feedbackFactorFeature As W f δ k := by
  simp [scheduledFactorFeature, feedbackFactorFeature,
    scheduledReturnFeature_eq As f hspec hcur hnext,
    scheduledDeferral_eq f hspec hcur]

lemma scheduledWealthFeature_eq
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

lemma scheduledBetaFeature_eq
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

lemma scheduledDeferral_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (fun z ↦
      scheduledDeferral f a degree z.unpair.1 z.unpair.2) := by
  obtain ⟨c, h⟩ := scheduledValue_polyFueled f a degree
  exact ⟨c, h.of_eq (fun z => by simp [scheduledDeferral])⟩

lemma scheduledReturnFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    RpnSpliceStream (fun z ↦ (scheduledReturnFeature As f a degree z).serialize) := by
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
  have hneg : RpnSpliceStream (fun _ ↦ (EF.const (-1)).serialize) :=
    RpnSpliceStream.serialize_const (-1)
  simpa [scheduledReturnFeature] using
    RpnSpliceStream.serialize_add hfuture
      (RpnSpliceStream.serialize_mul hneg hpresent)

lemma scheduledFactorFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    RpnSpliceStream (fun z ↦ (scheduledFactorFeature As W f a degree δ z).serialize) := by
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  have hweight := hW.polySeg.comp hvalue
  have hone : RpnSpliceStream (fun _ ↦ (EF.const 1).serialize) :=
    RpnSpliceStream.serialize_const 1
  have hdelta : RpnSpliceStream (fun _ ↦ (EF.const δ).serialize) :=
    RpnSpliceStream.serialize_const δ
  have hreturn := scheduledReturnFeature_polySeg hpoly f a degree
  simpa [scheduledFactorFeature] using RpnSpliceStream.serialize_add hone
    (RpnSpliceStream.serialize_mul
      (RpnSpliceStream.serialize_mul hdelta hweight) hreturn)

lemma scheduledWealthFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    RpnSpliceStream (fun z ↦ (scheduledWealthFeature As W f a degree δ z).serialize) := by
  have hfactor := scheduledFactorFeature_polySeg hpoly hW f a degree δ
  have hcanonical : PolyFueled _ (fun q : ℕ ↦
      Nat.pair q.unpair.1.unpair.1 q.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hblocks := RpnSpliceStream.concatVar (hfactor.comp hcanonical) PolyFueled.right
  have hone : RpnSpliceStream (fun _ ↦ (EF.const 1).serialize) :=
    RpnSpliceStream.serialize_const 1
  have htags := RpnSpliceStream.repeatTag 3 (by norm_num) PolyFueled.right
  refine RpnSpliceStream.of_eq ((hblocks.append hone).append htags) ?_
  intro z
  unfold scheduledWealthFeature
  rw [ROIBudget.serialize_prodFeatures]
  simp only [List.flatMap_map, List.length_map,
    List.length_range, Nat.unpair_pair, List.append_assoc]

lemma scheduledBetaFeature_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    RpnSpliceStream (fun z ↦ (scheduledBetaFeature As W f a degree δ z).serialize) := by
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  have hdelta : RpnSpliceStream (fun _ ↦ (EF.const δ).serialize) :=
    RpnSpliceStream.serialize_const δ
  have hwealth := scheduledWealthFeature_polySeg hpoly hW f a degree δ
  have hweight := hW.polySeg.comp hvalue
  simpa [scheduledBetaFeature] using RpnSpliceStream.serialize_mul
    (RpnSpliceStream.serialize_mul hdelta hwealth) hweight

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

lemma scheduledTermCount_polyFueled
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

lemma scheduledTermCoefficient_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    RpnSpliceStream (fun q ↦
      (scheduledTermCoefficient hpoly W f a degree δ q).serialize) := by
  obtain ⟨cmatch, hmatch⟩ := scheduledMatch_polyFueled f a degree
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  have hblockValue := hvalue.comp PolyFueled.left
  have hcanonical := hblockValue.pair PolyFueled.right
  have hcoefficient := hpoly.coefficient_poly.comp hcanonical
  have hbeta := (scheduledBetaFeature_polySeg hpoly hW f a degree δ).comp PolyFueled.left
  have hbase := RpnSpliceStream.serialize_mul hbeta hcoefficient
  have hneg : RpnSpliceStream (fun _ ↦ (EF.const (-1)).serialize) :=
    RpnSpliceStream.serialize_const (-1)
  have hclosing := RpnSpliceStream.serialize_mul hneg hbase
  refine RpnSpliceStream.of_eq
    (RpnSpliceStream.ifZero hclosing hbase (hmatch.comp PolyFueled.left)) ?_
  intro q
  rcases scheduledMatch_zero_or_one f a degree q.unpair.1 with hopen | hopen
  · simp [scheduledTermCoefficient, hopen]
  · simp [scheduledTermCoefficient, hopen]

lemma scheduledTermSentence_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    RpnSentenceCodes (scheduledTermSentence hpoly f a degree) := by
  obtain ⟨cvalue, hvalue⟩ := scheduledDeferral_polyFueled f a degree
  have hcanonical := (hvalue.comp PolyFueled.left).pair PolyFueled.right
  exact (hpoly.sentence_poly.comp hcanonical).of_eq (fun q => by
    simp [scheduledTermSentence])

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

/-- A scheduled component block is literally the existing round-trip syntax on every
day, including the nested closing coefficient generated by `AffineCombination.neg`. -/
lemma scheduledTradeBlock_eq
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF}
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (δ : ℚ) (n k : ℕ) :
    scheduledTradeBlock hpoly W f a degree δ (Nat.pair n k) =
      feedbackRoundTripTrades As W f δ k n := by
  by_cases hopen : n = f k
  · subst n
    have hopenFlag : scheduledMatch f a degree (Nat.pair (f k) k) = 1 :=
      (scheduledMatch_eq_one_iff f hspec (f k) k).2 rfl
    have hk : f k ≤ f k := le_rfl
    simp [scheduledTradeBlock, scheduledTermCount, scheduledTermCoefficient,
      scheduledTermSentence, feedbackRoundTripTrades, feedbackPosition, AffineCombination.scale,
      hopenFlag, scheduledDeferral_eq f hspec hk,
      scheduledBetaFeature_eq hstrict hspec δ hk, hpoly.terms_eq,
      List.map_map, Function.comp_def]
  · by_cases hclose : n = f (k + 1)
    · subst n
      have hne : f (k + 1) ≠ f k := ne_of_gt (hstrict (Nat.lt_succ_self k))
      have hopenFlag : scheduledMatch f a degree (Nat.pair (f (k + 1)) k) = 0 :=
        (scheduledMatch_eq_zero_iff f hspec (f (k + 1)) k).2 hne.symm
      have hcloseFlag : scheduledMatch f a degree
          (Nat.pair (f (k + 1)) (k + 1)) = 1 :=
        (scheduledMatch_eq_one_iff f hspec (f (k + 1)) (k + 1)).2 rfl
      have hk : f k ≤ f (k + 1) := (hstrict (Nat.lt_succ_self k)).le
      simp [scheduledTradeBlock, scheduledTermCount, scheduledTermCoefficient,
        scheduledTermSentence, feedbackRoundTripTrades, feedbackPosition,
        AffineCombination.neg, AffineCombination.scale, hne, hopenFlag, hcloseFlag,
        scheduledDeferral_eq f hspec hk,
        scheduledBetaFeature_eq hstrict hspec δ hk, hpoly.terms_eq,
        List.map_map, Function.comp_def]
    · have hopenFlag : scheduledMatch f a degree (Nat.pair n k) = 0 :=
        (scheduledMatch_eq_zero_iff f hspec n k).2 (fun h => hopen h.symm)
      have hcloseFlag : scheduledMatch f a degree (Nat.pair n (k + 1)) = 0 :=
        (scheduledMatch_eq_zero_iff f hspec n (k + 1)).2 (fun h => hclose h.symm)
      simp [scheduledTradeBlock, scheduledTermCount, feedbackRoundTripTrades,
        hopen, hclose, hopenFlag, hcloseFlag]

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

lemma scheduledTradeMember_lt
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) {n j : ℕ}
    (hj : j < scheduledTradeCount hpoly f a degree n) :
    scheduledTradeMember hpoly f a degree n j < n + 1 := by
  let lenFn := scheduledTermCount hpoly f a degree
  let k := segLocate lenFn n j (n + 1)
  have hkle : k ≤ n + 1 := segLocate_le lenFn n j (n + 1)
  have hkstart : segPrefix lenFn n k ≤ j := (segLocate_spec lenFn n j (n + 1)).1
  have hj' : j < segPrefix lenFn n (n + 1) := by
    simpa [scheduledTradeCount, lenFn] using hj
  have hkne : k ≠ n + 1 := by
    intro heq
    rw [heq] at hkstart
    exact (not_le_of_gt hj') hkstart
  change k < n + 1
  omega

lemma scheduledTradeOffset_lt
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) {n j : ℕ}
    (hj : j < scheduledTradeCount hpoly f a degree n) :
    scheduledTradeOffset hpoly f a degree n j <
      scheduledTermCount hpoly f a degree
        (Nat.pair n (scheduledTradeMember hpoly f a degree n j)) := by
  let lenFn := scheduledTermCount hpoly f a degree
  let k := segLocate lenFn n j (n + 1)
  have hklt : k < n + 1 := by
    simpa [scheduledTradeMember, lenFn] using
      scheduledTradeMember_lt hpoly f a degree hj
  have hmax := (segLocate_spec lenFn n j (n + 1)).2
  have hstart : segPrefix lenFn n k ≤ j :=
    (segLocate_spec lenFn n j (n + 1)).1
  have hnext : j < segPrefix lenFn n (k + 1) := by
    by_contra hnot
    have hle : segPrefix lenFn n (k + 1) ≤ j := le_of_not_gt hnot
    have := hmax (k + 1) (by omega) hle
    omega
  rw [segPrefix_succ] at hnext
  have hoff : j - segPrefix lenFn n k < lenFn (Nat.pair n k) := by omega
  simpa [scheduledTradeOffset, scheduledTradeMember, lenFn, k] using hoff

lemma scheduledTradeCount_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledTradeCount hpoly f a degree) := by
  obtain ⟨clen, hlen⟩ := scheduledTermCount_polyFueled hpoly f a degree
  obtain ⟨cprefix, hprefix⟩ := segPrefix_polyFueled hlen
  exact ⟨_, (hprefix.comp (PolyFueled.id.pair PolyFueled.id.succ_comp)).of_eq
    (fun n => by simp [scheduledTradeCount])⟩

lemma scheduledTradeMember_polyFueled
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

lemma scheduledTradeOffset_polyFueled
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

lemma scheduledTradeCoefficient_polySeg
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) :
    RpnSpliceStream (fun z ↦
      (scheduledTradeCoefficient hpoly W f a degree δ z).serialize) := by
  obtain ⟨cmember, hmember⟩ := scheduledTradeMember_polyFueled hpoly f a degree
  obtain ⟨coffset, hoffset⟩ := scheduledTradeOffset_polyFueled hpoly f a degree
  have hcanonical := (PolyFueled.left.pair hmember).pair hoffset
  simpa [scheduledTradeCoefficient] using
    (scheduledTermCoefficient_polySeg hpoly hW f a degree δ).comp hcanonical

lemma scheduledTradeSentence_polyFueled
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (f : DeferralFunction) (a degree : ℕ) :
    RpnSentenceCodes (scheduledTradeSentence hpoly f a degree) := by
  obtain ⟨cmember, hmember⟩ := scheduledTradeMember_polyFueled hpoly f a degree
  obtain ⟨coffset, hoffset⟩ := scheduledTradeOffset_polyFueled hpoly f a degree
  have hcanonical := (PolyFueled.left.pair hmember).pair hoffset
  exact ((scheduledTermSentence_polyFueled hpoly f a degree).comp
    hcanonical).of_eq (fun z => by simp [scheduledTradeSentence])

/-- The prefix-scan fields reconstruct the variable-width component-block flattening. -/
lemma scheduledTradeFields_eq_blocks
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    (W : ℕ → EF) (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (n : ℕ) :
    (List.range (scheduledTradeCount hpoly f a degree n)).map (fun j ↦
      (scheduledTradeCoefficient hpoly W f a degree δ (Nat.pair n j),
        scheduledTradeSentence hpoly f a degree (Nat.pair n j))) =
      (List.range (n + 1)).flatMap (fun k ↦
        scheduledTradeBlock hpoly W f a degree δ (Nat.pair n k)) := by
  let lenFn := scheduledTermCount hpoly f a degree
  let seg : ℕ → List (EF × Sentence) :=
    scheduledTradeBlock hpoly W f a degree δ
  have hlen : ∀ k, (seg (Nat.pair n k)).length = lenFn (Nat.pair n k) := by
    intro k
    simp [seg, lenFn]
  have hlength :
      ((List.range (n + 1)).flatMap (fun k ↦ seg (Nat.pair n k))).length =
        scheduledTradeCount hpoly f a degree n := by
    simpa [scheduledTradeCount, lenFn] using
      AffineCombination.length_flatMap_eq_segPrefix_any seg lenFn n hlen (n + 1)
  apply List.ext_get
  · simpa only [List.length_map, List.length_range] using hlength.symm
  · intro j hjleft hjright
    have hj : j < scheduledTradeCount hpoly f a degree n := by simpa using hjleft
    let k := scheduledTradeMember hpoly f a degree n j
    let r := scheduledTradeOffset hpoly f a degree n j
    have hklt : k < n + 1 := by
      simpa [k] using scheduledTradeMember_lt hpoly f a degree hj
    have hrlt : r < lenFn (Nat.pair n k) := by
      simpa [r, k, lenFn] using scheduledTradeOffset_lt hpoly f a degree hj
    have hlo : segPrefix lenFn n k ≤ j := by
      simpa [k, scheduledTradeMember] using
        (segLocate_spec lenFn n j (n + 1)).1
    have hhi : j < segPrefix lenFn n (k + 1) := by
      by_contra hnot
      have hle := le_of_not_gt hnot
      have hmax := (segLocate_spec lenFn n j (n + 1)).2
      have hk := hmax (k + 1) (by omega) hle
      have hkid : k = segLocate lenFn n j (n + 1) := by
        simp [k, scheduledTradeMember, lenFn]
      omega
    let d : EF × Sentence := (EF.const 0, hpoly.sentence 0)
    have hget := AffineCombination.getD_flatMap_of_prefix_any
      seg lenFn d n (n + 1) j k hlen hklt hlo hhi
    have hright :
        ((List.range (n + 1)).flatMap (fun q ↦ seg (Nat.pair n q))).getD j d =
          (seg (Nat.pair n k)).getD r d := by
      simpa [r, scheduledTradeOffset, k, lenFn] using hget
    have hgetD := List.getD_eq_get
      (l := (List.range (n + 1)).flatMap (fun q ↦ seg (Nat.pair n q)))
      (d := d) ⟨j, hjright⟩
    rw [← hgetD, hright]
    rw [show (seg (Nat.pair n k)).getD r d =
        (scheduledTermCoefficient hpoly W f a degree δ (Nat.pair (Nat.pair n k) r),
          scheduledTermSentence hpoly f a degree (Nat.pair (Nat.pair n k) r)) by
      simp only [seg, scheduledTradeBlock]
      rw [List.getD_eq_getElem]
      · rw [List.getElem_map, List.getElem_range]
      · simpa [lenFn] using hrlt]
    rw [List.get_eq_getElem]
    rw [List.getElem_map, List.getElem_range]
    simp only [scheduledTradeCoefficient, scheduledTradeSentence, Nat.unpair_pair]
    rfl

lemma scheduledTradeFields_eq_trader
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (δ : ℚ) (n : ℕ) :
    ((feedbackTrader hpoly hW hstrict δ).strat n).trades =
      (List.range (scheduledTradeCount hpoly f a degree n)).map (fun j ↦
        (scheduledTradeCoefficient hpoly W f a degree δ (Nat.pair n j),
          scheduledTradeSentence hpoly f a degree (Nat.pair n j))) := by
  rw [feedbackTrader_trades hpoly hW hstrict δ n, feedbackTraderTrades,
    scheduledTradeFields_eq_blocks]
  apply List.flatMap_congr
  intro k hk
  exact (scheduledTradeBlock_eq hpoly hstrict hspec δ n k).symm

/-- Concrete bounded-dovetail inhabitant of the feedback trader's syntax boundary. -/
noncomputable def feedbackTraderEmission
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f) (δ : ℚ) :
    FeedbackTraderEmission hpoly hW hstrict δ := by
  let a := Classical.choose f.fueled
  let degree := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k,
      Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k) := by
    simpa [a, degree, ecClock] using
      Classical.choose_spec (Classical.choose_spec f.fueled)
  exact
    { tradeCount := scheduledTradeCount hpoly f a degree
      coefficient := scheduledTradeCoefficient hpoly W f a degree δ
      sentence := scheduledTradeSentence hpoly f a degree
      tradeCount_poly := scheduledTradeCount_polyFueled hpoly f a degree
      coefficient_poly := scheduledTradeCoefficient_polySeg hpoly hW f a degree δ
      sentence_poly := scheduledTradeSentence_polyFueled hpoly f a degree
      trades_eq := scheduledTradeFields_eq_trader hpoly hW hstrict hspec δ }

/-- One uniform construction supplies every rational Kelly fraction requested by the
feedback argument. -/
noncomputable def feedbackTraderEmissionFamily
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f) :
    FeedbackTraderEmissionFamily hpoly hW hstrict where
  emit δ _ _ := feedbackTraderEmission hpoly hW hstrict δ

/-- The construction is stable under the existing polynomial affine negation compiler,
so both sign orientations are concrete.
Paper node: `thm:wubaff` -/
noncomputable def feedbackTraderEmissionSigns
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f) :
    FeedbackTraderEmissionSigns hpoly hW hstrict where
  positive := feedbackTraderEmissionFamily hpoly hW hstrict
  negative := feedbackTraderEmissionFamily hpoly.neg hW hstrict

/-! ### Consumers with the emission boundary discharged -/

/-- Affine unbiasedness, with the feedback-emission boundary discharged by a concrete
feedback-truth sequence.
Paper node: `thm:wubaff` -/
theorem lic_wubaff_ofFeedbackTruth
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (bridge : FeedbackTruthSequence As truth P DP f)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).price P i) truth ≈ₙ (fun _ ↦ 0) :=
  AffineCombination.lic_wubaff hpoly hW hstrict hsupport
    (feedbackTraderEmissionSigns hpoly hW hstrict) bridge hWdiv hmag hworld

/--
Paper node: `thm:wubaff` -/
theorem boundedCombination_wubaff_ofFeedbackTruth
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (bridge : FeedbackTruthSequence
      (fun n ↦ (As n).scale (.const h.unitNormalization.scale))
      (fun n ↦ (h.unitNormalization.scale : ℝ) * truth n) P DP f)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).price P i) truth ≈ₙ (fun _ ↦ 0) :=
  h.wubaff hW hdet hstrict hsupport
    (feedbackTraderEmissionSigns
      (h.poly.scaleRat h.unitNormalization.scale) hW hstrict)
    bridge hWdiv hworld

/--
Paper node: `thm:wubexp` -/
theorem luv_wubexp_ofFeedbackTruth
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hvalued : LUVCombination.WorldValued As DP)
    {truth : ℕ → ℝ} (hdet : LUVCombination.DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (bridge : FeedbackTruthSequence
      (LUVCombination.normalizedMesh As b)
      (LUVCombination.normalizedMeshTruth As P DP hworld b) P DP f) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).expect P i) truth ≈ₙ (fun _ ↦ 0) :=
  h.wubexp hvalued hdet b hshare hW hWdiv hstrict hsupport hworld
    (feedbackTraderEmissionSigns (h.normalizedMesh_poly b) hW hstrict) bridge

#print axioms feedbackTraderEmissionSigns
#print axioms lic_wubaff_ofFeedbackTruth
#print axioms boundedCombination_wubaff_ofFeedbackTruth
#print axioms luv_wubexp_ofFeedbackTruth

end FeedbackEmission
end LogicalInduction
