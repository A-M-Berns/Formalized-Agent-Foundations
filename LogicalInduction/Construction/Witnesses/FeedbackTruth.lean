import LogicalInduction.Construction.Witnesses.QuotationAffine

/-!
# Concrete delayed feedback truth (`M7-FEEDBACK-TRUTH`)

The completed-theory value stream in `DeterminedViaTheory` is semantic data; it is not a
computable oracle.  This file therefore takes the paper's separate operational premise:
one program emits the rational value of `A_{f k}` by the next feedback deadline.  A bounded
simulation of that program is combined with the already-certified deferral schedule to
emit the literal sparse affine sequence

`A_{f k} - truth(f k)` on day `f(k+1)`, and `0` on every other day.

The operational certificate contains no price-accuracy, unbiasedness, convergence, or
logical-inductor conclusion.  Uniform normalization and market bounds remain separate
inputs to the public constructor.
-/

namespace LogicalInduction
namespace FeedbackTruth

open AffineCombination PrefixPatchCompile

attribute [local irreducible] Nat.sqrt

/-- The paper's delayed truth computation premise.  Input `k` names the value of
`A_{f k}`; the program must return its canonical rational code by day `f(k+1)`.
The equality with the semantic real stream is recorded only on those required indices.
Paper node: `thm:wubaff`, `thm:wubexp` -/
structure FeedbackTruthComputation (truth : ℕ → ℝ) (f : DeferralFunction) where
  value : ℕ → ℚ
  code : Nat.Partrec.Code
  a : ℕ
  degree : ℕ
  computes : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f (k + 1))) code k =
    some (Encodable.encode (value k))
  agrees : ∀ k, (value k : ℝ) = truth (f k)

/-! ## The shifted deferral schedule -/

/-- The source component on a delayed feedback day: the preimage of `m`, minus one. -/
def feedbackIndex (f : DeferralFunction) (a degree m : ℕ) : ℕ :=
  deferralPreimage f a degree m - 1

/-- A day is active exactly when it is `f(j)` for a positive index `j`.
Natural-valued Booleans keep the schedule inside the polynomial compiler. -/
def feedbackFlag (f : DeferralFunction) (a degree m : ℕ) : ℕ :=
  if deferralImageFlag f a degree m = 0 then 0
  else if deferralPreimage f a degree m = 0 then 0 else 1

lemma feedbackIndex_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (feedbackIndex f a degree) := by
  obtain ⟨cpre, hpre⟩ := deferralPreimage_polyFueled f a degree
  exact ⟨_, (predc_polyFueled.comp hpre).of_eq (fun m => by
    simp [feedbackIndex, Nat.pred_eq_sub_one])⟩

lemma feedbackFlag_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (feedbackFlag f a degree) := by
  obtain ⟨cflag, hflag⟩ := deferralImageFlag_polyFueled f a degree
  obtain ⟨cpre, hpre⟩ := deferralPreimage_polyFueled f a degree
  have hinner := ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair (PolyFueled.const 1)).pair hpre)
  exact ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair hinner).pair hflag)).of_eq (fun m => by
      simp only [ifzSelFn]
      simp [feedbackFlag])⟩

lemma feedbackFlag_zero_or_one (f : DeferralFunction) (a degree m : ℕ) :
    feedbackFlag f a degree m = 0 ∨ feedbackFlag f a degree m = 1 := by
  unfold feedbackFlag
  by_cases hi : deferralImageFlag f a degree m = 0
  · simp [hi]
  · by_cases hp : deferralPreimage f a degree m = 0
    · simp [hi, hp]
    · simp [hi, hp]

lemma feedbackFlag_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (k : ℕ) : feedbackFlag f a degree (f (k + 1)) = 1 := by
  rw [feedbackFlag,
    deferralImageFlag_at f hspec (k + 1),
    deferralPreimage_at f hstrict.injective hspec (k + 1)]
  simp

lemma feedbackIndex_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (k : ℕ) : feedbackIndex f a degree (f (k + 1)) = k := by
  rw [feedbackIndex, deferralPreimage_at f hstrict.injective hspec (k + 1)]
  omega

/-- On every active day, the shifted schedule really names a unique feedback component. -/
lemma feedbackFlag_spec
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {m : ℕ} (hm : feedbackFlag f a degree m = 1) :
    f (feedbackIndex f a degree m + 1) = m := by
  have himage : deferralImageFlag f a degree m = 1 := by
    unfold feedbackFlag at hm
    split at hm <;> rename_i hflag
    · omega
    · rcases deferralImageFlag_zero_or_one f a degree m with hz | ho
      · exact (hflag hz).elim
      · exact ho
  have hpre : deferralPreimage f a degree m ≠ 0 := by
    unfold feedbackFlag at hm
    rw [if_neg (by omega)] at hm
    split at hm <;> omega
  have hspec' := deferralPreimage_spec f hstrict.injective hspec himage
  rw [feedbackIndex]
  have hpos : 1 ≤ deferralPreimage f a degree m := Nat.one_le_iff_ne_zero.2 hpre
  rw [Nat.sub_add_cancel hpos]
  exact hspec'.2

/-- The source affine index is recovered by the same bounded deferral evaluator used by
the feedback-trader emitter; no unbounded inverse of `f` is evaluated. -/
def sourceIndex (f : DeferralFunction) (a degree m : ℕ) : ℕ :=
  FeedbackEmission.scheduledDeferral f a degree m (feedbackIndex f a degree m)

lemma sourceIndex_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (sourceIndex f a degree) := by
  obtain ⟨cvalue, hvalue⟩ := FeedbackEmission.scheduledValue_polyFueled f a degree
  obtain ⟨cindex, hindex⟩ := feedbackIndex_polyFueled f a degree
  have hquery : PolyFueled _ (fun m => Nat.pair m (feedbackIndex f a degree m)) :=
    PolyFueled.id.pair hindex
  exact ⟨_, (hvalue.comp hquery).of_eq (fun m => by
    simp [sourceIndex, FeedbackEmission.scheduledDeferral])⟩

lemma sourceIndex_at
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (k : ℕ) : sourceIndex f a degree (f (k + 1)) = f k := by
  rw [sourceIndex, feedbackIndex_at f hstrict hspec k]
  apply FeedbackEmission.scheduledDeferral_eq f hspec
  exact (hstrict (Nat.lt_succ_self k)).le

lemma sourceIndex_le_of_flag
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {m : ℕ} (hm : feedbackFlag f a degree m = 1) :
    sourceIndex f a degree m < m := by
  have hdeadline := feedbackFlag_spec f hstrict hspec hm
  have hkn : f (feedbackIndex f a degree m) ≤ m := by
    calc
      f (feedbackIndex f a degree m) ≤ f (feedbackIndex f a degree m + 1) :=
        (hstrict (Nat.lt_succ_self _)).le
      _ = m := hdeadline
  have hsource : sourceIndex f a degree m = f (feedbackIndex f a degree m) := by
    exact FeedbackEmission.scheduledDeferral_eq f hspec hkn
  calc
    sourceIndex f a degree m = f (feedbackIndex f a degree m) := hsource
    _ < f (feedbackIndex f a degree m + 1) := hstrict (Nat.lt_succ_self _)
    _ = m := hdeadline

lemma sourceIndex_eq_of_flag
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {m : ℕ} (hm : feedbackFlag f a degree m = 1) :
    sourceIndex f a degree m = f (feedbackIndex f a degree m) := by
  have hdeadline := feedbackFlag_spec f hstrict hspec hm
  apply FeedbackEmission.scheduledDeferral_eq f hspec
  calc
    f (feedbackIndex f a degree m) ≤ f (feedbackIndex f a degree m + 1) :=
      (hstrict (Nat.lt_succ_self _)).le
    _ = m := hdeadline

/-! ## Bounded truth-code simulation -/

/-- Raw canonical rational code returned by the bounded truth computation. -/
def truthCodeAt {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f) (fa fd m : ℕ) : ℕ :=
  codeEvalnNat C.code (Nat.pair (ecClock C.a C.degree m) (feedbackIndex f fa fd m)) - 1

lemma truthCodeAt_polyFueled {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f) (fa fd : ℕ) :
    ∃ c, PolyFueled c (truthCodeAt C fa fd) := by
  obtain ⟨csim, hsim⟩ := codeEvalnNat_polyFueled C.code
  obtain ⟨cclock, hclock⟩ := ecClock_polyFueled C.a C.degree
  obtain ⟨cindex, hindex⟩ := feedbackIndex_polyFueled f fa fd
  have hquery := (hclock.pair hindex)
  exact ⟨_, (predc_polyFueled.comp (hsim.comp hquery)).of_eq (fun m => by
    simp [truthCodeAt, Nat.pred_eq_sub_one])⟩

lemma truthCodeAt_eq_of_flag
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    {m : ℕ} (hm : feedbackFlag f fa fd m = 1) :
    truthCodeAt C fa fd m = Encodable.encode (C.value (feedbackIndex f fa fd m)) := by
  have hdeadline := feedbackFlag_spec f hstrict hspec hm
  have hrun := C.computes (feedbackIndex f fa fd m)
  rw [hdeadline] at hrun
  unfold truthCodeAt codeEvalnNat
  simp only [Nat.unpair_pair]
  rw [hrun]
  simp

/-! ## Literal sparse affine syntax -/

/-- The centered active member, or the literal zero affine combination off schedule. -/
def sequence {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (fa fd m : ℕ) : AffineCombination :=
  if feedbackFlag f fa fd m = 0 then
    ⟨EF.const 0, []⟩
  else
    ⟨EF.add (As (sourceIndex f fa fd m)).const
        (EF.mul (EF.const (-1)) (EF.const (C.value (feedbackIndex f fa fd m)))),
      (As (sourceIndex f fa fd m)).terms⟩

lemma sequence_eq_at
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    (k : ℕ) :
    sequence As C fa fd (f (k + 1)) =
      ⟨EF.add (As (f k)).const (EF.mul (EF.const (-1)) (EF.const (C.value k))),
        (As (f k)).terms⟩ := by
  rw [sequence, feedbackFlag_at f hstrict hspec k, if_neg one_ne_zero,
    sourceIndex_at f hstrict hspec k, feedbackIndex_at f hstrict hspec k]

@[simp] theorem sequence_price_at
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    (P : History) (k : ℕ) :
    (sequence As C fa fd (f (k + 1))).price P (f (k + 1)) =
      (As (f k)).price P (f (k + 1)) - (C.value k : ℝ) := by
  rw [sequence_eq_at As C hstrict hspec k]
  simp [AffineCombination.price, AffineCombination.value]
  ring

@[simp] theorem sequence_magnitude
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (As : ℕ → AffineCombination) (C : FeedbackTruthComputation truth f)
    (fa fd m : ℕ) (P : History) :
    (sequence As C fa fd m).magnitude P =
      if feedbackFlag f fa fd m = 0 then 0
      else (As (sourceIndex f fa fd m)).magnitude P := by
  unfold sequence AffineCombination.magnitude
  split <;> simp

/-! ### Polynomial affine-sequence certificate -/

/-- The sparse literal sequence has a uniform polynomial syntax emitter.  The rational
payload on an active branch is emitted directly from the bounded universal evaluator;
`truthCodeAt_eq_of_flag` proves that payload is the canonical code appearing in the syntax. -/
noncomputable def sequencePoly
    {As : ℕ → AffineCombination} (hA : PolySequence As)
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (fa fd : ℕ)
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k)) :
    PolySequence (sequence As C fa fd) := by
  let cflag := Classical.choose (feedbackFlag_polyFueled f fa fd)
  have hflag := Classical.choose_spec (feedbackFlag_polyFueled f fa fd)
  let csource := Classical.choose (sourceIndex_polyFueled f fa fd)
  have hsource := Classical.choose_spec (sourceIndex_polyFueled f fa fd)
  let ccount := Classical.choose hA.termCount_poly
  have hcount := Classical.choose_spec hA.termCount_poly
  let ctruth := Classical.choose (truthCodeAt_polyFueled C fa fd)
  have htruth := Classical.choose_spec (truthCodeAt_polyFueled C fa fd)
  let count : ℕ → ℕ := fun m =>
    if feedbackFlag f fa fd m = 0 then 0 else hA.termCount (sourceIndex f fa fd m)
  let coeff : ℕ → EF := fun z =>
    hA.coefficient (Nat.pair (sourceIndex f fa fd z.unpair.1) z.unpair.2)
  let sentence : ℕ → Sentence := fun z =>
    hA.sentence (Nat.pair (sourceIndex f fa fd z.unpair.1) z.unpair.2)
  have hcountSource := hcount.comp hsource
  have hcountPoly : ∃ c, PolyFueled c count := by
    exact ⟨_, (ifzSel_polyFueled.comp
      (((PolyFueled.const 0).pair hcountSource).pair hflag)).of_eq (fun m => by
        simp [count, ifzSelFn])⟩
  have hquery : PolyFueled _ (fun z : ℕ =>
      Nat.pair (sourceIndex f fa fd z.unpair.1) z.unpair.2) :=
    (hsource.comp PolyFueled.left).pair PolyFueled.right
  have hcoeffPoly : RpnSpliceStream (fun z => (coeff z).serialize) := by
    simpa only [coeff] using hA.coefficient_poly.comp hquery
  have hsentencePoly : RpnSentenceCodes sentence :=
    (hA.sentence_poly.comp hquery).of_eq (fun z => rfl)
  have hrawConst : RpnSpliceStream (fun m => [1, truthCodeAt C fa fd m]) :=
    RpnSpliceStream.payload 1 (Or.inl rfl) htruth
  have hminusRaw : RpnSpliceStream (fun m =>
      (EF.const (-1)).serialize ++ [1, truthCodeAt C fa fd m] ++ [3]) :=
    ((RpnSpliceStream.serialize_const (-1)).append hrawConst).append
      (RpnSpliceStream.tag 3 (by norm_num))
  have hactiveRaw : RpnSpliceStream (fun m =>
      (As (sourceIndex f fa fd m)).const.serialize ++
        ((EF.const (-1)).serialize ++ [1, truthCodeAt C fa fd m] ++ [3]) ++ [2]) :=
    ((hA.const_poly.comp hsource).append hminusRaw).append
      (RpnSpliceStream.tag 2 (by norm_num))
  have hconstIf := RpnSpliceStream.ifZero
    (RpnSpliceStream.serialize_const 0) hactiveRaw hflag
  exact {
    termCount := count
    coefficient := coeff
    sentence := sentence
    termCount_poly := hcountPoly
    const_poly := by
      refine RpnSpliceStream.of_eq hconstIf ?_
      intro m
      by_cases hm : feedbackFlag f fa fd m = 0
      · simp [sequence, hm]
      · have hm1 : feedbackFlag f fa fd m = 1 :=
          (feedbackFlag_zero_or_one f fa fd m).resolve_left hm
        rw [truthCodeAt_eq_of_flag C hstrict hspec hm1]
        simp [sequence, hm, EF.serialize, List.append_assoc]
    coefficient_poly := hcoeffPoly
    sentence_poly := hsentencePoly
    terms_eq := by
      intro m
      unfold sequence count coeff sentence
      by_cases hm : feedbackFlag f fa fd m = 0
      · simp [hm]
      · simp [hm, hA.terms_eq]
    const_rank := by
      intro m
      unfold sequence
      by_cases hm : feedbackFlag f fa fd m = 0
      · simp [hm]
      · rw [if_neg hm]
        simp only [EF.rank]
        have hone : feedbackFlag f fa fd m = 1 :=
          (feedbackFlag_zero_or_one f fa fd m).resolve_left hm
        have hsle := (sourceIndex_le_of_flag f hstrict hspec hone).le
        exact Nat.max_le.mpr ⟨hA.const_rank _ |>.trans hsle, by simp⟩
    coefficient_rank := by
      intro m j hj
      unfold count at hj
      have hm : feedbackFlag f fa fd m = 1 := by
        rcases feedbackFlag_zero_or_one f fa fd m with hz | ho
        · simp [hz] at hj
        · exact ho
      have hsle := (sourceIndex_le_of_flag f hstrict hspec hm).le
      unfold coeff
      simp only [Nat.unpair_pair]
      exact (hA.coefficient_rank _ j (by simpa [hm] using hj)).trans hsle
    const_closed := by
      intro m ρ V
      unfold sequence
      split
      · simp [EF.denoteWith]
      · simp only [EF.denoteWith, EF.denote_add, EF.denote_mul, EF.denote_const,
          Pi.add_apply, Pi.mul_apply]
        rw [hA.const_closed]
    coefficient_closed := by
      intro z ρ V
      exact hA.coefficient_closed _ ρ V
  }

/-! ## Semantic package -/

lemma sequence_value_zero
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hdet : DeterminedViaTheory As P DP truth)
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    (sequence As C fa fd m).value P v.payout = 0 := by
  unfold sequence
  by_cases hm : feedbackFlag f fa fd m = 0
  · simp [hm, AffineCombination.value]
  · have hm1 : feedbackFlag f fa fd m = 1 :=
      (feedbackFlag_zero_or_one f fa fd m).resolve_left hm
    rw [if_neg hm]
    have hsource := sourceIndex_eq_of_flag f hstrict hspec hm1
    have heq :
        (⟨EF.add (As (sourceIndex f fa fd m)).const
            (EF.mul (EF.const (-1)) (EF.const (C.value (feedbackIndex f fa fd m)))),
          (As (sourceIndex f fa fd m)).terms⟩ : AffineCombination).value P v.payout =
          (As (sourceIndex f fa fd m)).value P v.payout -
            (C.value (feedbackIndex f fa fd m) : ℝ) := by
      simp [AffineCombination.value]
      ring
    rw [heq, hsource, hdet _ v hv, C.agrees]
    ring

lemma sequence_bounded
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hpoly : PolySequence As)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hdet : DeterminedViaTheory As P DP truth)
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    BoundedAffinePrices (sequence As C fa fd) P := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  refine ⟨2 * B + 1, by positivity, ?_⟩
  intro m n
  unfold sequence
  by_cases hm : feedbackFlag f fa fd m = 0
  · simp [hm, AffineCombination.price, AffineCombination.value]
    linarith
  · have hm1 : feedbackFlag f fa fd m = 1 :=
      (feedbackFlag_zero_or_one f fa fd m).resolve_left hm
    rw [if_neg hm]
    have hsource := sourceIndex_eq_of_flag f hstrict hspec hm1
    have htruth : |(C.value (feedbackIndex f fa fd m) : ℝ)| ≤ B + 1 := by
      rw [C.agrees, ← hdet _ v hv, ← hsource]
      let i := sourceIndex f fa fd m
      have hdiff := (As i).abs_value_sub_price_le_magnitude P v.payout i
        (hpoly.terms_rank i) (by
          intro φ
          rw [PCWorld.payout]
          split <;> norm_num) (hP i)
      have hprice0 := hB i i
      have hmag0 := hmag i
      calc
        |(As i).value P v.payout| =
            |((As i).value P v.payout - (As i).price P i) + (As i).price P i| := by ring_nf
        _ ≤ |(As i).value P v.payout - (As i).price P i| +
              |(As i).price P i| := abs_add_le _ _
        _ ≤ B + 1 := by linarith
    have hprice := hB (sourceIndex f fa fd m) n
    have heq :
        (⟨EF.add (As (sourceIndex f fa fd m)).const
            (EF.mul (EF.const (-1)) (EF.const (C.value (feedbackIndex f fa fd m)))),
          (As (sourceIndex f fa fd m)).terms⟩ : AffineCombination).price P n =
          (As (sourceIndex f fa fd m)).price P n -
            (C.value (feedbackIndex f fa fd m) : ℝ) := by
      simp [AffineCombination.price, AffineCombination.value]
      ring
    rw [heq, abs_le]
    rw [abs_le] at hprice htruth
    constructor <;> linarith

/-- Public constructor for the formerly opaque `FeedbackTruthSequence` boundary.
Normalization is deliberately external: `hA`, `hP`, and `hworld` provide the ordinary
paper BCS/market premises, while `C` contains only the delayed computation.
Paper node: `thm:wubaff` -/
noncomputable def feedbackTruthSequence
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hpoly : PolySequence As)
    (hbounded : BoundedAffinePrices As P)
    (hdet : DeterminedViaTheory As P DP truth)
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    FeedbackTruthSequence As truth P DP f := by
  let fa := Classical.choose f.fueled
  let fd := Classical.choose (Classical.choose_spec f.fueled)
  have hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k) := by
    simpa [fa, fd, ecClock] using Classical.choose_spec (Classical.choose_spec f.fueled)
  exact {
    determined := hdet
    sequence := sequence As C fa fd
    poly := sequencePoly hpoly C hstrict fa fd hspec
    bounded := sequence_bounded hpoly hbounded hmag hdet C hstrict hspec hP hworld
    magnitude := by
      intro m
      rw [sequence_magnitude]
      split
      · simp
      · exact hmag _
    zero_value := sequence_value_zero hdet C hstrict hspec
    feedback_price := by
      intro k
      rw [sequence_price_at As C hstrict hspec P k, C.agrees]
  }

/-! ## Consumers with both feedback boundaries discharged -/

/-- Low-level `thm:wubaff` endpoint: the token emitter and delayed truth sequence are
both constructed, leaving only the paper's operational truth program and ordinary
normalization/market premises.
Paper node: `thm:wubaff` -/
theorem lic_wubaff_ofComputation
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hdet : DeterminedViaTheory As P DP truth)
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hWdiv : DivergentWeighting W P)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).price P i) truth ≈ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let bridge := feedbackTruthSequence hpoly hbounded hdet C hstrict hmag hP hworld
  exact AffineCombination.lic_wubaff hpoly hW hstrict hsupport
    (FeedbackEmission.feedbackTraderEmissionSigns hpoly hW hstrict)
    bridge hWdiv hmag hworld

/-- `thm:wub`, with both feedback boundaries discharged by the concrete trader emitter and
delayed-truth compiler.  This is the one-share specialization of
`lic_wubaff_ofComputation`; the caller supplies only the paper's sentence sequence,
completed-theory truth stream, weighting, schedule, and deadline-bounded truth program.
Paper node: `thm:wub` -/
theorem lic_wub_ofComputation
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (truth : ℕ → ℝ) (htruth : TheoryTruth φ DP truth)
    (W : ℕ → EF) (hW : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P) (fun i ↦ P i (φ i)) truth ≈ₙ
      (fun _ ↦ 0) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hdet : DeterminedViaTheory (sentenceAffine φ) P DP truth := by
    intro n v hv
    simpa [sentenceAffine, AffineCombination.value] using htruth n v hv
  have h := lic_wubaff_ofComputation (sentenceAffine_polySequence φ hφ) hW hdet C
    hstrict hsupport hWdiv (sentenceAffine_bounded φ P hP)
    (fun i => by simp) hworld
  simpa only [sentenceAffine_price] using h

/-- Paper-facing affine endpoint for an arbitrary BCS.  Its canonical normalization stays
outside `FeedbackTruthComputation`; the supplied program computes the normalized truth
stream that the actual unit-risk trader consumes.
Paper node: `thm:wubaff` -/
theorem boundedCombination_wubaff_ofComputation
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation
      (fun n ↦ (h.unitNormalization.scale : ℝ) * truth n) f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).price P i) truth ≈ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℚ := h.unitNormalization.scale
  have hdetScaled : DeterminedViaTheory
      (fun n ↦ (As n).scale (.const q)) P DP
      (fun n ↦ (q : ℝ) * truth n) := by
    intro n v hv
    rw [AffineCombination.scale_value, EF.denote_const, hdet n v hv]
  have hboundedScaled : BoundedAffinePrices
      (fun n ↦ (As n).scale (.const q)) P :=
    (h.boundedPrices hP).scaleRat q
  let bridge := feedbackTruthSequence (h.poly.scaleRat q) hboundedScaled
    hdetScaled C hstrict h.unitNormalization.magnitude_le_one hP hworld
  exact FeedbackEmission.boundedCombination_wubaff_ofFeedbackTruth h hW hdet hstrict
    hsupport bridge hWdiv hworld

/-- `thm:wubexp` with the normalized threshold mesh's delayed truth computation exposed
directly.  The threshold mesh, feedback traders, and sparse truth sequence are all concrete.
Paper node: `thm:wubexp` -/
theorem luv_wubexp_ofComputation
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hexact : LUVCombination.ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : LUVCombination.DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth As P DP hworld b) f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    :
    weightedBias (fun i ↦ (W i).denote P)
      (fun i ↦ (As i).expect P i) truth ≈ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let meshTruth := LUVCombination.normalizedMeshTruth As P DP hworld b
  have C' : FeedbackTruthComputation meshTruth f := by
    simpa only [meshTruth] using C
  have hmeshDet : AffineCombination.DeterminedViaTheory
      (LUVCombination.normalizedMesh As b) P DP meshTruth := by
    simpa only [meshTruth] using
      (hexact.normalizedMesh_determined (P := P) hworld b)
  let bridge := feedbackTruthSequence (h.normalizedMesh_poly b)
    (h.normalizedMesh_boundedPrices b hP) hmeshDet C' hstrict
    (LUVCombination.normalizedMesh_magnitude_le_one b hshare) hP hworld
  exact FeedbackEmission.luv_wubexp_ofFeedbackTruth h hexact hdet b hshare hW hWdiv
    hstrict hsupport hworld bridge

#print axioms feedbackTruthSequence
#print axioms lic_wubaff_ofComputation
#print axioms lic_wub_ofComputation
#print axioms boundedCombination_wubaff_ofComputation
#print axioms luv_wubexp_ofComputation

end FeedbackTruth
end LogicalInduction
