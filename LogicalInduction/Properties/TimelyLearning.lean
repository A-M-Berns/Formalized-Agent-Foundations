import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Framework.Expectations
import LogicalInduction.Framework.WriteOut

/-!
# Timely Learning

Renders §4.2 *Timely Learning*: `thm:perkno` (Persistence of Knowledge, appendix
`app:perkno`) and `thm:tbo` (Preemptive Learning, appendix `app:tbo`). Both specialize the
affine results of `Properties/AffinePersistence.lean` to ordinary efficiently codeable
sentence sequences.

`AffineCombination.sentenceAffine φ n` is the one-share affine presentation of `φ n`, with
its price and magnitude simp lemmas and the exact `BCS` witness `sentenceAffine_bcs`. Its
emission certificate `sentenceAffine_polySequence` is the discharge that turns the paper's
"`⟨φ⟩` is an e.c. sequence" into the `PolySequence` argument `AffineCombination.simcal`
takes; it is consumed by `Properties/{AffineCoherence,Calibration,MetaLearning,
Pseudorandomness}.lean` and by the construction witnesses
`Construction/Witnesses/{FeedbackTruth,DeferralFibre,QuotationAffine}.lean`. The
presentation is kept explicit rather than inferred, so the paper's efficient-sequence
premise is not silently widened to an arbitrary Lean function.

`sentenceMinusProbability φ p n` is the centered family `φₙ − pₙ`, whose rational offset is
a closed feature. The centering is essential: applying persistence to `φₙ` alone would
compare only separate limsups and liminfs, and could not track a varying target.
`knowledgeFutureDeviation P φ p n` is the paper's `sup_{m ≥ n} |Pₘ(φₙ) − pₙ|`.

The main results are `lic_centered_persistence` (operational, both directions), the
one-sided clauses `lic_persistence_of_knowledge_upper` / `_lower`, the assembled
`lic_persistence_of_knowledge` (`thm:perkno`), and `lic_preemptive_learning` (`thm:tbo`).

Beyond the paper's hypotheses, plausible-world existence is an explicit `hworld` premise;
the price range is carried by `IsLogicalInductor`.
-/

namespace LogicalInduction

open Filter

namespace AffineCombination

/-! ## The one-share affine presentation -/

/-- The one-share affine combination representing `φ n`. -/
def sentenceAffine (φ : ℕ → Sentence) (n : ℕ) : AffineCombination where
  const := .const 0
  terms := [(.const 1, φ n)]

@[simp] lemma sentenceAffine_price (φ : ℕ → Sentence) (P : History) (n m : ℕ) :
    (sentenceAffine φ n).price P m = P m (φ n) := by
  simp [sentenceAffine, price, value]

@[simp] lemma sentenceAffine_magnitude (φ : ℕ → Sentence) (P : History) (n : ℕ) :
    (sentenceAffine φ n).magnitude P = 1 := by
  simp [sentenceAffine, magnitude]

/-- A polynomial sentence-code progression induces a legal one-share affine sequence.

This is one of the two discharges that make `thm:simcal`'s endpoint reach the paper's own
hypothesis set: `AffineCombination.simcal` takes `PolySequence (sentenceAffine φ)` as an
argument, and this constructs it from the paper's "`⟨φ⟩` is an e.c. sequence".
Paper node: `thm:simcal` -/
noncomputable def sentenceAffine_polySequence (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    PolySequence (sentenceAffine φ) :=
  {
    termCount := fun _ => 1
    coefficient := fun _ => .const 1
    sentence := fun z => φ z.unpair.1
    termCount_poly := ⟨Nat.Partrec.Code.const 1, PolyFueled.const 1⟩
    const_poly := BigSpliceStream.serialize_const 0
    coefficient_poly := BigSpliceStream.serialize_const 1
    sentence_poly := hφ.comp PolyFueled.left
    terms_eq := by intro n; simp [sentenceAffine]
    const_rank := by intro n; simp [sentenceAffine]
    coefficient_rank := by intro n j hj; simp [EF.rank]
    const_closed := by intro n ρ V; simp [sentenceAffine]
    coefficient_closed := by intro z ρ V; simp [EF.denoteWith]
  }

/-- The market's `[0,1]` price range makes the one-share family uniformly bounded across
days, which is the `BoundedAffinePrices` premise the persistence results take. -/
lemma sentenceAffine_bounded (φ : ℕ → Sentence) (P : History)
    (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1) :
    BoundedAffinePrices (sentenceAffine φ) P := by
  refine ⟨1, zero_le_one, fun n m => ?_⟩
  rw [sentenceAffine_price]
  rw [abs_le]
  constructor <;> linarith [(hP m (φ n)).1, (hP m (φ n)).2]

/-- The one-share sentence family as an exact paper `BCS` witness. -/
noncomputable def sentenceAffine_bcs (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (P : History) : BoundedCombinationSequence (sentenceAffine φ) P where
  poly := sentenceAffine_polySequence φ hφ
  bounded := ⟨1, fun n => by simp [l1Norm, sentenceAffine, magnitude]⟩

/-! ## The centered family `φₙ − pₙ` -/

/-- The affine combination `φ n - p n`.  The rational offset is represented by a
closed feature so that persistence can be applied to a moving comparison sequence. -/
def sentenceMinusProbability (φ : ℕ → Sentence) (p : ℕ → ℚ) (n : ℕ) :
    AffineCombination where
  const := .mul (.const (-1)) (.const (p n))
  terms := [(.const 1, φ n)]

@[simp] lemma sentenceMinusProbability_value (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (n : ℕ) (V : History) (w : Valuation) :
    (sentenceMinusProbability φ p n).value V w = w (φ n) - (p n : ℝ) := by
  simp [sentenceMinusProbability, value]
  ring

@[simp] lemma sentenceMinusProbability_price (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (P : History) (n m : ℕ) :
    (sentenceMinusProbability φ p n).price P m = P m (φ n) - (p n : ℝ) := by
  simp [price]

@[simp] lemma sentenceMinusProbability_magnitude (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (P : History) (n : ℕ) :
    (sentenceMinusProbability φ p n).magnitude P = 1 := by
  simp [sentenceMinusProbability, magnitude]

/-- Efficient sentence and rational codes emit the centered affine progression used in
the Appendix proof of `thm:perkno`. -/
noncomputable def sentenceMinusProbability_polySequence
    (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (hφ : BigSentenceCodes φ) (hp : DigitRatCodes p) :
    PolySequence (sentenceMinusProbability φ p) :=
  {
    termCount := fun _ => 1
    coefficient := fun _ => .const 1
    sentence := fun z => φ z.unpair.1
    termCount_poly := ⟨Nat.Partrec.Code.const 1, PolyFueled.const 1⟩
    const_poly := BigSpliceStream.serialize_mul
      (BigSpliceStream.serialize_const (-1))
      (BigSpliceStream.serialize_const_write hp.toBigDigits)
    coefficient_poly := BigSpliceStream.serialize_const 1
    sentence_poly := hφ.comp PolyFueled.left
    terms_eq := by intro n; simp [sentenceMinusProbability]
    const_rank := by intro n; simp [sentenceMinusProbability, EF.rank]
    coefficient_rank := by intro n j hj; simp [EF.rank]
    const_closed := by intro n ρ V; simp [sentenceMinusProbability, EF.denoteWith]
    coefficient_closed := by intro z ρ V; simp [EF.denoteWith]
  }

/-- The `[0,1]` price range together with `p n ∈ [0,1]` makes the centered family
uniformly bounded across days, which is the `BoundedAffinePrices` premise the persistence
results take. -/
lemma sentenceMinusProbability_bounded (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (P : History) (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1)
    (hp : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1) :
    BoundedAffinePrices (sentenceMinusProbability φ p) P := by
  refine ⟨1, zero_le_one, fun n m => ?_⟩
  rw [sentenceMinusProbability_price, abs_le]
  constructor <;> linarith [(hP m (φ n)).1, (hP m (φ n)).2, (hp n).1, (hp n).2]

@[simp] lemma sentenceAffine_futureHigh (φ : ℕ → Sentence) (P : History) (n : ℕ) :
    affineFutureHigh (sentenceAffine φ) P n =
      sSup (Set.range (fun j => P (n + j) (φ n))) := by
  simp [affineFutureHigh]

@[simp] lemma sentenceAffine_futureLow (φ : ℕ → Sentence) (P : History) (n : ℕ) :
    affineFutureLow (sentenceAffine φ) P n =
      sInf (Set.range (fun j => P (n + j) (φ n))) := by
  simp [affineFutureLow]

end AffineCombination

/-- The paper's `sup_{m ≥ n} |P_m(φ_n) - p_n|`, with `m = n + j`. -/
noncomputable def knowledgeFutureDeviation
    (P : History) (φ : ℕ → Sentence) (p : ℕ → ℚ) (n : ℕ) : ℝ :=
  sSup (Set.range (fun j => |P (n + j) (φ n) - (p n : ℝ)|))

/-! ## Operational persistence and its one-sided upgrades -/

/-- The operational overpricing condition upgrades an asymptotic upper bound on its
benchmark to the same upper bound on the guarded sequence. -/
lemma noPreemptiveOverpricing_asympLE_zero {current future : ℕ → ℝ}
    (hgap : NoPreemptiveOverpricing current future)
    (hfuture : future ≲ₙ fun _ => 0) :
    current ≲ₙ fun _ => 0 := by
  intro ε hε
  have hsmall := hfuture (ε / 4) (by linarith)
  have hfuture' : ∀ᶠ n in atTop, future n < ε / 2 := by
    filter_upwards [hsmall] with n hn
    linarith
  have hnot := hgap (ε / 2) ε (by linarith) hfuture'
  rw [Filter.not_frequently] at hnot
  filter_upwards [hnot] with n hn
  simpa only [Pi.zero_apply, zero_add] using (show current n ≤ ε by linarith)

/-- Dual upgrade for the operational underpricing condition. -/
lemma noPreemptiveUnderpricing_asympGE_zero {current future : ℕ → ℝ}
    (hgap : NoPreemptiveUnderpricing current future)
    (hfuture : (fun _ => 0) ≲ₙ future) :
    (fun _ => 0) ≲ₙ current := by
  intro ε hε
  have hlarge := hfuture (ε / 4) (by linarith)
  have hfuture' : ∀ᶠ n in atTop, -ε / 2 < future n := by
    filter_upwards [hlarge] with n hn
    linarith
  have hnot := hgap (-ε) (-ε / 2) (by linarith) hfuture'
  rw [Filter.not_frequently] at hnot
  filter_upwards [hnot] with n hn
  simpa only [Pi.zero_apply, zero_add] using (show 0 ≤ current n + ε by linarith)

/-- Centered operational form of Persistence of Knowledge. If the limiting centered
prices are asymptotically zero from one side, every future centered price is controlled
uniformly from that side.
Paper node: `thm:perkno` -/
theorem lic_centered_persistence (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (hφ : BigSentenceCodes φ) (hp : DigitRatCodes p)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (((fun n => limitingBelief P (φ n) - (p n : ℝ)) ≲ₙ
        (fun _ : ℕ => (0 : ℝ))) →
      affineFutureHigh (AffineCombination.sentenceMinusProbability φ p) P ≲ₙ
        (fun _ : ℕ => (0 : ℝ))) ∧
      (((fun _ : ℕ => (0 : ℝ)) ≲ₙ
          (fun n => limitingBelief P (φ n) - (p n : ℝ))) →
        (fun _ : ℕ => (0 : ℝ)) ≲ₙ
          affineFutureLow (AffineCombination.sentenceMinusProbability φ p) P) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  let As := AffineCombination.sentenceMinusProbability φ p
  have hpoly := AffineCombination.sentenceMinusProbability_polySequence φ p hφ hp
  have hbounded := AffineCombination.sentenceMinusProbability_bounded φ p P hP hpProb
  have hgap := hpoly.noPersistenceGaps P DP hbounded
    (fun n => by simp) hworld
  constructor
  · intro hlim
    apply noPreemptiveOverpricing_asympLE_zero hgap.overpriced
    simpa [As] using hlim
  · intro hlim
    apply noPreemptiveUnderpricing_asympGE_zero hgap.underpriced
    simpa [As] using hlim

/-- Upper one-sided clause of `thm:perkno`.
Paper node: `thm:perkno` -/
theorem lic_persistence_of_knowledge_upper (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (hφ : BigSentenceCodes φ) (hp : DigitRatCodes p)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hlim : (fun n => limitingBelief P (φ n)) ≲ₙ fun n => (p n : ℝ)) :
    (fun n => sSup (Set.range (fun j => P (n + j) (φ n)))) ≲ₙ
      fun n => (p n : ℝ) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hcenterLim : (fun n => limitingBelief P (φ n) - (p n : ℝ)) ≲ₙ
      fun _ => 0 := by
    intro ε hε
    filter_upwards [hlim ε hε] with n hn
    linarith
  have hcenter := (lic_centered_persistence P DP φ p hφ hp hpProb hworld).1
    hcenterLim
  intro ε hε
  have hnear := hcenter ε hε
  filter_upwards [hnear] with n hn
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro x ⟨j, rfl⟩
    have hprice := AffineCombination.BoundedAffinePrices.price_le_futureHigh
      (AffineCombination.sentenceMinusProbability_bounded φ p P hP hpProb)
      (show n ≤ n + j by omega)
    rw [AffineCombination.sentenceMinusProbability_price] at hprice
    linarith

/-- Lower one-sided clause of `thm:perkno`.
Paper node: `thm:perkno` -/
theorem lic_persistence_of_knowledge_lower (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (hφ : BigSentenceCodes φ) (hp : DigitRatCodes p)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hlim : (fun n => limitingBelief P (φ n)) ≳ₙ fun n => (p n : ℝ)) :
    (fun n => sInf (Set.range (fun j => P (n + j) (φ n)))) ≳ₙ
      fun n => (p n : ℝ) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hcenterLim : (fun _ => 0) ≲ₙ
      fun n => limitingBelief P (φ n) - (p n : ℝ) := by
    intro ε hε
    filter_upwards [hlim ε hε] with n hn
    linarith
  have hcenter := (lic_centered_persistence P DP φ p hφ hp hpProb hworld).2
    hcenterLim
  intro ε hε
  have hnear := hcenter ε hε
  filter_upwards [hnear] with n hn
  have hsinf : (p n : ℝ) - ε ≤ sInf (Set.range (fun j => P (n + j) (φ n))) := by
    apply le_csInf
    · exact Set.range_nonempty _
    · rintro x ⟨j, rfl⟩
      have hprice := AffineCombination.BoundedAffinePrices.futureLow_le_price
        (AffineCombination.sentenceMinusProbability_bounded φ p P hP hpProb)
        (show n ≤ n + j by omega)
      rw [AffineCombination.sentenceMinusProbability_price] at hprice
      linarith
  linarith

/-- Two one-sided uniform tail bounds force the future absolute deviation to vanish. -/
lemma knowledgeFutureDeviation_asympEq_zero (P : History)
    (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hupper : (fun n => sSup (Set.range (fun j => P (n + j) (φ n)))) ≲ₙ
      fun n => (p n : ℝ))
    (hlower : (fun n => sInf (Set.range (fun j => P (n + j) (φ n)))) ≳ₙ
      fun n => (p n : ℝ)) :
    knowledgeFutureDeviation P φ p ≈ₙ fun _ => 0 := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [hupper ε hε, hlower ε hε] with n hnupper hnlower
  have hbound : ∀ j, |P (n + j) (φ n) - (p n : ℝ)| ≤ ε := by
    intro j
    have hhigh := AffineCombination.BoundedAffinePrices.price_le_futureHigh
      (AffineCombination.sentenceAffine_bounded φ P hP) (show n ≤ n + j by omega)
    have hlow := AffineCombination.BoundedAffinePrices.futureLow_le_price
      (AffineCombination.sentenceAffine_bounded φ P hP) (show n ≤ n + j by omega)
    rw [AffineCombination.sentenceAffine_price,
      AffineCombination.sentenceAffine_futureHigh] at hhigh
    rw [AffineCombination.sentenceAffine_price,
      AffineCombination.sentenceAffine_futureLow] at hlow
    rw [abs_le]
    constructor <;> linarith
  have hdevUpper : knowledgeFutureDeviation P φ p n ≤ ε := by
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro x ⟨j, rfl⟩
      exact hbound j
  have hdevNonneg : 0 ≤ knowledgeFutureDeviation P φ p n := by
    have hbdd : BddAbove
        (Set.range (fun j => |P (n + j) (φ n) - (p n : ℝ)|)) := by
      refine ⟨1, ?_⟩
      rintro x ⟨j, rfl⟩
      rw [abs_le]
      constructor <;>
        linarith [(hP (n + j) (φ n)).1, (hP (n + j) (φ n)).2,
          (hpProb n).1, (hpProb n).2]
    have hmember : |P n (φ n) - (p n : ℝ)| ≤ knowledgeFutureDeviation P φ p n := by
      apply le_csSup hbdd
      exact ⟨0, by simp⟩
    exact (abs_nonneg _).trans hmember
  simpa only [Pi.zero_apply, sub_zero, abs_of_nonneg hdevNonneg] using hdevUpper

/-! ## Persistence of Knowledge (`thm:perkno`) -/

/-- **Persistence of Knowledge** (`thm:perkno`). For efficiently codeable sentences and
rational probabilities, agreement of the limiting beliefs with `p n` makes every later
price agree uniformly; either one-sided limiting comparison yields the corresponding
uniform future supremum/infimum comparison.

The centered affine family `φ n - p n` is essential here. Applying affine persistence to
`φ n` alone would compare only separate limsups/liminfs and would not control a varying
target sequence pointwise.
Paper node: `thm:perkno` -/
theorem lic_persistence_of_knowledge (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (p : ℕ → ℚ)
    (hφ : BigSentenceCodes φ) (hp : DigitRatCodes p)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (((fun n => limitingBelief P (φ n)) ≈ₙ fun n => (p n : ℝ)) →
        knowledgeFutureDeviation P φ p ≈ₙ fun _ => 0) ∧
      (((fun n => limitingBelief P (φ n)) ≲ₙ fun n => (p n : ℝ)) →
        (fun n => sSup (Set.range (fun j => P (n + j) (φ n)))) ≲ₙ
          fun n => (p n : ℝ)) ∧
      (((fun n => limitingBelief P (φ n)) ≳ₙ fun n => (p n : ℝ)) →
        (fun n => sInf (Set.range (fun j => P (n + j) (φ n)))) ≳ₙ
          fun n => (p n : ℝ)) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hupper := lic_persistence_of_knowledge_upper
    P DP φ p hφ hp hpProb hworld
  have hlower := lic_persistence_of_knowledge_lower
    P DP φ p hφ hp hpProb hworld
  refine ⟨?_, hupper, hlower⟩
  intro hlim
  exact knowledgeFutureDeviation_asympEq_zero P φ p hP hpProb
    (hupper hlim.asympLE) (hlower hlim.asympGE)

/-! ## Preemptive Learning (`thm:tbo`) -/

/-- **Preemptive Learning** (`thm:tbo`). For an efficiently codeable sequence of
sentences, the diagonal prices have exactly the same liminf as their future suprema and
the same limsup as their future infima.

The price range is carried by `IsLogicalInductor`; plausible-world existence remains an
explicit deductive-process hypothesis.
Paper node: `thm:tbo` -/
theorem lic_preemptive_learning (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => P n (φ n)) atTop =
        liminf (fun n => sSup (Set.range (fun j => P (n + j) (φ n)))) atTop ∧
      limsup (fun n => P n (φ n)) atTop =
        limsup (fun n => sInf (Set.range (fun j => P (n + j) (φ n)))) atTop := by
  have hbcs := AffineCombination.sentenceAffine_bcs φ hφ P
  have h := hbcs.affpolymax DP hworld
  have hhigh : affineFutureHigh (AffineCombination.sentenceAffine φ) P =
      fun n => sSup (Set.range (fun j => P (n + j) (φ n))) :=
    funext (AffineCombination.sentenceAffine_futureHigh φ P)
  have hlow : affineFutureLow (AffineCombination.sentenceAffine φ) P =
      fun n => sInf (Set.range (fun j => P (n + j) (φ n))) :=
    funext (AffineCombination.sentenceAffine_futureLow φ P)
  have hdiag : (fun n => (AffineCombination.sentenceAffine φ n).price P n) =
      fun n => P n (φ n) :=
    funext (fun n => AffineCombination.sentenceAffine_price φ P n n)
  rw [hdiag, hhigh, hlow] at h
  exact h

end LogicalInduction
