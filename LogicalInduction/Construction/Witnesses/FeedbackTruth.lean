import LogicalInduction.Construction.Witnesses.QuotationAffine
import LogicalInduction.Framework.WriteOut

/-!
# Concrete delayed feedback truth for `thm:wubaff` and `thm:wubexp`

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

open AffineCombination PrefixPatchCompile Filter Topology

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

/-! ## Non-vacuity witness -/

/-- **N+.** The delayed-truth premise is inhabited, for every deferral schedule `f`: the
constant program `Code.const ⌜1⌝` returns the code of `1` well inside the polynomial
feedback clock, because `f (k+1) > k` forces the clock above the `k + ⌜1⌝ + 1` fuel that
`fueled_const` needs.  Kind `N+`, provenance (a).

Disclosure: this witness is **degenerate in the value stream** — `value` and `truth` are
both constant.  A non-constant witness would have to fuel-certify a program emitting
`Encodable.encode (q k)` for a varying rational `q`, and the `Encodable ℚ` encoding is a
`Denumerable` bijection with no arithmetic normal form in the `PolyFueled` toolkit, so no
such certificate is available in-repo.  The witness therefore establishes satisfiability of
the premise, not the non-degeneracy of the values a real feedback stream would carry.
Paper node: `thm:wub`, `thm:wubaff`, `thm:wubexp` -/
def ordinaryFeedbackTruthComputation (f : DeferralFunction) :
    FeedbackTruthComputation (fun _ => (1 : ℝ)) f where
  value _ := 1
  code := Nat.Partrec.Code.const (Encodable.encode (1 : ℚ))
  a := Encodable.encode (1 : ℚ) + 1
  degree := 1
  computes k := by
    refine Nat.Partrec.Code.evaln_mono ?_ (fueled_const (Encodable.encode (1 : ℚ)) k)
    have hf : k + 1 < f (k + 1) := f.lt (k + 1)
    simp only [ecClock, pow_one]
    nlinarith [hf]
  agrees k := by norm_num

#print axioms ordinaryFeedbackTruthComputation

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

@[simp] lemma sequence_price_at
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

@[simp] lemma sequence_magnitude
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
  have hcoeffPoly : BigSpliceStream (fun z => (coeff z).serialize) := by
    simpa only [coeff] using hA.coefficient_poly.comp hquery
  have hsentencePoly : BigSentenceCodes sentence :=
    (hA.sentence_poly.comp hquery).of_eq (fun z => rfl)
  have hrawConst : BigSpliceStream (fun m => [1, truthCodeAt C fa fd m]) :=
    BigSpliceStream.payload 1 (Or.inl rfl) htruth
  have hminusRaw : BigSpliceStream (fun m =>
      (EF.const (-1)).serialize ++ [1, truthCodeAt C fa fd m] ++ [3]) :=
    ((BigSpliceStream.serialize_const (-1)).append hrawConst).append
      (BigSpliceStream.tag 3 (by norm_num))
  have hactiveRaw : BigSpliceStream (fun m =>
      (As (sourceIndex f fa fd m)).const.serialize ++
        ((EF.const (-1)).serialize ++ [1, truthCodeAt C fa fd m] ++ [3]) ++ [2]) :=
    ((hA.const_poly.comp hsource).append hminusRaw).append
      (BigSpliceStream.tag 2 (by norm_num))
  have hconstIf := BigSpliceStream.ifZero
    (BigSpliceStream.serialize_const 0) hactiveRaw hflag
  exact {
    termCount := count
    coefficient := coeff
    sentence := sentence
    termCount_poly := hcountPoly
    const_poly := by
      refine BigSpliceStream.of_eq hconstIf ?_
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

/-- The value the sparse sequence takes in a completed world, on either branch: `0` off
schedule, and the determination residual of `A_{f i}` on the active day `f (i+1)`. -/
lemma sequence_value_eq
    {As : ℕ → AffineCombination} {P : History}
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    {m : ℕ} (hm : feedbackFlag f fa fd m = 1) (v : PCWorld) :
    (sequence As C fa fd m).value P v.payout =
      (As (f (feedbackIndex f fa fd m))).value P v.payout -
        truth (f (feedbackIndex f fa fd m)) := by
  unfold sequence
  rw [if_neg (by omega)]
  have hsource := sourceIndex_eq_of_flag f hstrict hspec hm
  have heq :
      (⟨EF.add (As (sourceIndex f fa fd m)).const
          (EF.mul (EF.const (-1)) (EF.const (C.value (feedbackIndex f fa fd m)))),
        (As (sourceIndex f fa fd m)).terms⟩ : AffineCombination).value P v.payout =
        (As (sourceIndex f fa fd m)).value P v.payout -
          (C.value (feedbackIndex f fa fd m) : ℝ) := by
    simp [AffineCombination.value]
    ring
  rw [heq, hsource, C.agrees]

/-- On an active day the source index is at least the tolerance launch index: the deadline
identity `f (i + 1) = m` plus strict monotonicity reflects `m ≥ f (N + 1)` back to
`i ≥ N`, and `f i > i` then puts the *affine* index `f i` past `N` too. -/
lemma le_source_of_flag
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    {N m : ℕ} (hm : feedbackFlag f fa fd m = 1) (hmN : f (N + 1) ≤ m) :
    N ≤ f (feedbackIndex f fa fd m) := by
  have hdeadline := feedbackFlag_spec f hstrict hspec hm
  have hle : f (N + 1) ≤ f (feedbackIndex f fa fd m + 1) := by rw [hdeadline]; exact hmN
  have hN : N ≤ feedbackIndex f fa fd m := by
    have := hstrict.le_iff_le.1 hle
    omega
  exact hN.trans (f.lt (feedbackIndex f fa fd m)).le

/-- **The sparse feedback sequence's completed-world value vanishes uniformly.**

Only *approximate* determination of `As` is used, with a residual stream tending to zero.
On the active day `f (i+1)` the sequence is `A_{f i}` centred at the computed value of
`truth (f i)`, so a completed world values it at exactly the determination residual at
index `f i` — and `f i → ∞` along the schedule, so the residual is eventually below any
tolerance.  This is what lets the threshold mesh of a LUV combination, which
`def:affthmval` determines only up to its `O(1/n)` mesh error, still supply a feedback
bridge. -/
lemma sequence_value_vanishing
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth err : ℕ → ℝ} {f : DeferralFunction}
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herr : Tendsto err atTop (𝓝 0))
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k)) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      |(sequence As C fa fd m).value P v.payout| ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 herr ε hε
  rw [Filter.eventually_atTop]
  refine ⟨f (N + 1), fun m hm v hv => ?_⟩
  by_cases hflag : feedbackFlag f fa fd m = 0
  · have hzero : (sequence As C fa fd m).value P v.payout = 0 := by
      simp [sequence, hflag, AffineCombination.value]
    rw [hzero, abs_zero]
    exact hε.le
  · have hm1 : feedbackFlag f fa fd m = 1 :=
      (feedbackFlag_zero_or_one f fa fd m).resolve_left hflag
    rw [sequence_value_eq C hstrict hspec hm1 v]
    have hidx : N ≤ f (feedbackIndex f fa fd m) :=
      le_source_of_flag f hstrict hspec hm1 hm
    have hsmall := hN _ hidx
    rw [Real.dist_eq, sub_zero] at hsmall
    exact (hdet _ v hv).trans ((le_abs_self _).trans hsmall.le)

lemma sequence_bounded
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth err : ℕ → ℝ} {f : DeferralFunction}
    (hpoly : PolySequence As)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herr : Tendsto err atTop (𝓝 0))
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    {fa fd : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock fa fd (f k)) f.code k = some (f k))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    BoundedAffinePrices (sequence As C fa fd) P := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  obtain ⟨M0, hM0⟩ := herr.bddAbove_range
  set M : ℝ := max M0 0 with hMdef
  have hMerr : ∀ n, err n ≤ M := fun n => (hM0 ⟨n, rfl⟩).trans (le_max_left _ _)
  have hM0le : (0 : ℝ) ≤ M := le_max_right _ _
  refine ⟨2 * B + 1 + M, by positivity, ?_⟩
  intro m n
  unfold sequence
  by_cases hm : feedbackFlag f fa fd m = 0
  · simp [hm, AffineCombination.price, AffineCombination.value]
    linarith
  · have hm1 : feedbackFlag f fa fd m = 1 :=
      (feedbackFlag_zero_or_one f fa fd m).resolve_left hm
    rw [if_neg hm]
    have hsource := sourceIndex_eq_of_flag f hstrict hspec hm1
    have htruth : |(C.value (feedbackIndex f fa fd m) : ℝ)| ≤ B + 1 + M := by
      rw [C.agrees, ← hsource]
      set i := sourceIndex f fa fd m with hi
      have hres := hdet i v hv
      have hdiff := (As i).abs_value_sub_price_le_magnitude P v.payout i
        (hpoly.terms_rank i) (by
          intro φ
          rw [PCWorld.payout]
          split <;> norm_num) (hP i)
      have hprice0 := hB i i
      have hmag0 := hmag i
      have hMi := hMerr i
      have hval : |(As i).value P v.payout| ≤ B + 1 := by
        calc
          |(As i).value P v.payout| =
              |((As i).value P v.payout - (As i).price P i) + (As i).price P i| := by ring_nf
          _ ≤ |(As i).value P v.payout - (As i).price P i| +
                |(As i).price P i| := abs_add_le _ _
          _ ≤ B + 1 := by linarith
      rw [abs_le] at hval hres
      rw [abs_le]
      obtain ⟨hv1, hv2⟩ := hval
      obtain ⟨hr1, hr2⟩ := hres
      constructor <;> linarith
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

/-- **Public constructor for the `FeedbackTruthSequence` boundary.**
Normalization is deliberately external: `hpoly`, `hbounded`, `hmag`, `hP`, and `hworld`
provide the ordinary paper BCS/market premises, while `C` contains only the delayed
computation.

Determination enters only *approximately*: `hdet` bounds each completed world's
disagreement with the advertised `truth n` by `err n`, and `herr` sends that residual to
zero.  Exact determination is the `err = 0` instance (`feedbackTruthSequence_ofDetermined`).
The slack is what carries the LUV mesh, which `def:affthmval` determines only to within
its `O(1/n)` mesh error.
Paper node: `thm:wubaff` -/
noncomputable def feedbackTruthSequence
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    {truth err : ℕ → ℝ} {f : DeferralFunction}
    (hpoly : PolySequence As)
    (hbounded : BoundedAffinePrices As P)
    (hdet : ApproxDeterminedViaTheory As P DP truth err)
    (herr : Tendsto err atTop (𝓝 0))
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
    determined := ⟨err, herr, hdet⟩
    sequence := sequence As C fa fd
    poly := sequencePoly hpoly C hstrict fa fd hspec
    bounded := sequence_bounded hpoly hbounded hmag hdet herr C hstrict hspec hP hworld
    magnitude := by
      intro m
      rw [sequence_magnitude]
      split
      · simp
      · exact hmag _
    value_vanishing := sequence_value_vanishing hdet herr C hstrict hspec
    feedback_price := by
      intro k
      rw [sequence_price_at As C hstrict hspec P k, C.agrees]
  }

/-- The exactly-determined instance of `feedbackTruthSequence`, at zero residual.  This is
what the sentence-indicator and affine feedback endpoints use, where `Θ` really does pin
one value per member; only the LUV mesh needs the approximate form.
Paper node: `thm:wubaff` -/
noncomputable def feedbackTruthSequence_ofDetermined
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
    FeedbackTruthSequence As truth P DP f :=
  feedbackTruthSequence hpoly hbounded hdet.approx tendsto_const_nhds C hstrict hmag hP
    hworld

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
  let bridge := feedbackTruthSequence_ofDetermined hpoly hbounded hdet C hstrict hmag hP
    hworld
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
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
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
  let bridge := feedbackTruthSequence_ofDetermined (h.poly.scaleRat q) hboundedScaled
    hdetScaled C hstrict h.unitNormalization.magnitude_le_one hP hworld
  exact FeedbackEmission.boundedCombination_wubaff_ofFeedbackTruth h hW hdet hstrict
    hsupport bridge hWdiv hworld

/-- **`thm:wubexp` from the paper's own premises.**  The threshold mesh, its feedback
traders, and its sparse delayed-truth sequence are all constructed here; nothing about the
sequence is assumed beyond what tex:1822-1832 assumes.

The semantic premises are exactly the paper's: `hdet` is `def:affthmval` — every completed
world assigns the *combination* `Aₙ` the same value `truth n` — and `hvalued` is the
representation premise that each completed world values the component LUVs somehow
(`W(X)` being a supremum, paper worlds always do).  Neither pins a component LUV's value
across worlds, so `[(1, X), (-1, X)]` for a wholly undetermined `X` is covered.  `C` is
the paper's operational premise: one program emits `thmval` of the mesh by the next
deferral deadline.

*Why the mesh route survives combination-level determination.*  Meshing is nonlinear
(each LUV is replaced by a rounded threshold bundle), so the precision-`n` mesh of a
combination-determined sequence is **not** determined: two completed worlds may split the
determined total differently across components and mesh to different values.  What
`lem:conluvapprox` gives is quantitative — each world's mesh value is within
`shareNorm/n` of the determined value, hence any two agree to within twice that
(`WorldValued.normalizedMesh_approxDetermined`), a residual that vanishes
(`meshErrorBound_tendsto_zero`).  Affine provability induction needs no more than that:
`affine_provind_theory_tendsto_zero` learns the price of a sequence whose completed-world
values merely tend to zero uniformly.  So the feedback bridge is built at
`ApproxDeterminedViaTheory`, not `DeterminedViaTheory`.

No endpoint of this node uses `LUVCombination.ExactTheoryPresentation`, and none should:
that structure fixes a completed-theory value for *every component LUV*, which is strictly
stronger than `def:affthmval` and would be a premise the paper does not state.

Kind `C`; provenance: `hdet`, `hvalued`, `hshare`, `hW`, `hWdiv`, `hstrict`, `hsupport`
(a) — the paper's own hypotheses; `C` (a) — the paper's deadline-bounded truth program,
in the `dd:fuel` efficiency model; `hworld` (a) — finite-stage plausible worlds.
Paper node: `thm:wubexp` -/
theorem luv_wubexp_ofComputation
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : LUVCombination.BoundedSequence As P)
    (hvalued : LUVCombination.WorldValued As DP)
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
  have hmeshDet : AffineCombination.ApproxDeterminedViaTheory
      (LUVCombination.normalizedMesh As b) P DP
      (LUVCombination.normalizedMeshTruth As P DP hworld b)
      (LUVCombination.meshErrorBound As P b) :=
    hvalued.normalizedMesh_approxDetermined hdet hworld b
  have herr : Tendsto (LUVCombination.meshErrorBound As P b) atTop (𝓝 0) :=
    LUVCombination.meshErrorBound_tendsto_zero b hshare
  let bridge := feedbackTruthSequence (h.normalizedMesh_poly b)
    (h.normalizedMesh_boundedPrices b hP) hmeshDet herr C hstrict
    (LUVCombination.normalizedMesh_magnitude_le_one b hshare) hP hworld
  exact FeedbackEmission.luv_wubexp_ofFeedbackTruth h hvalued hdet b hshare
    hW hWdiv hstrict hsupport hworld bridge

#print axioms feedbackTruthSequence
#print axioms lic_wubaff_ofComputation
#print axioms lic_wub_ofComputation
#print axioms boundedCombination_wubaff_ofComputation
#print axioms luv_wubexp_ofComputation

end FeedbackTruth
end LogicalInduction
