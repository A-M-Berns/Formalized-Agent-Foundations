import LogicalInduction.Construction.Witnesses.PaperTheoryDP
import LogicalInduction.Construction.Witnesses.FeedbackTruth
import LogicalInduction.Framework.WriteOut

/-!
# Feedback and LUV unbiasedness over the constructed `LIA`

The paper's unbiasedness-from-feedback theorems (`thm:wub`, `thm:wubaff`, `thm:wubexp`),
instantiated at the constructed provability process and its `LIA` inductor.  The
`_ofComputation` endpoints supply both operational witnesses of the argument — the feedback
traders and the delayed truth sequence — and the remaining market-side hypotheses are
discharged here over the same provability process the computational-knowledge and quotation
endpoints use:

* `paperDP_computable` constructs the deductive process and hence the `LIA` inductor;
* `liaHistory_range` supplies the ordinary probability bounds; and
* `paperDP_hworld` supplies a plausible world at every finite stage.

The caller still supplies the paper's substantive inputs: an affine/LUV sequence, its
completed-theory determination data, the deferral schedule, weighting, and the explicit
deadline-bounded program computing the delayed truth values.  No separate feedback deductive
process is needed: `FeedbackTruthComputation` is an operational value computation, not a
presentation whose literals must be enumerated by the process.
-/

namespace LogicalInduction
namespace FeedbackTruth

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open AffineCombination

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

private noncomputable abbrev feedbackLIA :
    IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
  LIA_is_logical_inductor (paperDP T) (paperDP_computable T)

/-- `thm:wub` over the constructed `LIA`: the market, deductive process, logical-inductor
instance, finite-stage plausible worlds, feedback traders, and sparse delayed truth sequence
are all constructed.  The caller supplies the paper's efficiently coded sentence sequence,
completed-theory truth stream, weighting, schedule, and deadline-bounded truth program.
Paper node: `thm:wub` -/
theorem lic_wub_ofComputation_unconditional
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (truth : ℕ → ℝ) (htruth : TheoryTruth φ (paperDP T) truth)
    (W : ℕ → EF) (hW : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W (liaHistory (paperDP T)))
    (f : DeferralFunction) (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation truth f)
    (hsupport : WeightingSupportedOnDeferralImage W (liaHistory (paperDP T)) f) :
    weightedBias (fun i ↦ (W i).denote (liaHistory (paperDP T)))
      (fun i ↦ liaHistory (paperDP T) i (φ i)) truth ≈ₙ (fun _ ↦ 0) := by
  haveI := feedbackLIA T
  exact lic_wub_ofComputation (liaHistory (paperDP T)) (paperDP T)
    φ hφ truth htruth W hW hWdiv f hstrict
    C hsupport
    (paperDP_hworld T)

/-- `thm:wubaff` over the constructed `LIA`.  Only the paper's affine data and the
operational delayed-truth program remain caller inputs.
Paper node: `thm:wubaff` -/
theorem lic_wubaff_ofComputation_unconditional
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {truth : ℕ → ℝ} {f : DeferralFunction}
    (hdet : DeterminedViaTheory As (liaHistory (paperDP T)) (paperDP T) truth)
    (C : FeedbackTruthComputation truth f)
    (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W (liaHistory (paperDP T)) f)
    (hWdiv : DivergentWeighting W (liaHistory (paperDP T)))
    (hbounded : BoundedAffinePrices As (liaHistory (paperDP T)))
    (hmag : ∀ i, (As i).magnitude (liaHistory (paperDP T)) ≤ 1) :
    weightedBias (fun i ↦ (W i).denote (liaHistory (paperDP T)))
      (fun i ↦ (As i).price (liaHistory (paperDP T)) i) truth ≈ₙ (fun _ ↦ 0) := by
  haveI := feedbackLIA T
  exact lic_wubaff_ofComputation hpoly hW hdet C hstrict hsupport hWdiv hbounded hmag
    (paperDP_hworld T)

/-- Paper-facing `thm:wubaff` over the constructed `LIA`, for an arbitrary bounded
affine-combination sequence.  The canonical unit-risk normalization and both feedback
operational witnesses are constructed by the lower-level endpoint.
Paper node: `thm:wubaff` -/
theorem boundedCombination_wubaff_ofComputation_unconditional
    {As : ℕ → AffineCombination}
    (h : BoundedCombinationSequence As (liaHistory (paperDP T)))
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As (liaHistory (paperDP T)) (paperDP T) truth)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation
      (fun n ↦ (h.unitNormalization.scale : ℝ) * truth n) f)
    (hsupport : WeightingSupportedOnDeferralImage W (liaHistory (paperDP T)) f)
    (hWdiv : DivergentWeighting W (liaHistory (paperDP T))) :
    weightedBias (fun i ↦ (W i).denote (liaHistory (paperDP T)))
      (fun i ↦ (As i).price (liaHistory (paperDP T)) i) truth ≈ₙ (fun _ ↦ 0) := by
  haveI := feedbackLIA T
  exact boundedCombination_wubaff_ofComputation h hW hdet hstrict C hsupport hWdiv
    (paperDP_hworld T)

/-- `thm:wubexp` over the constructed `LIA`: the concrete normalized threshold mesh, its
feedback traders, and its delayed truth sequence yield recurring unbiasedness for bounded LUV
combinations.  The deadline-bounded truth program `C` is the paper's explicit operational
input; `hdet` (`def:affthmval`) and `hvalued` (the representation premise) are its explicit
semantic ones.

The premises are exactly tex:1822-1832's.  In particular determination is at the
*combination* level only: `[(1, X), (-1, X)]` for a wholly undetermined `X` is covered,
which it would not be under `LUVCombination.ExactTheoryPresentation`.  The mesh feedback
bridge is built from approximate determination; see
`FeedbackTruth.luv_wubexp_ofComputation`.
Paper node: `thm:wubexp` -/
theorem luv_wubexp_ofComputation_unconditional
    {As : ℕ → LUVCombination}
    (h : LUVCombination.BoundedSequence As (liaHistory (paperDP T)))
    (hvalued : LUVCombination.WorldValued As (paperDP T))
    {truth : ℕ → ℝ}
    (hdet : LUVCombination.DeterminedViaTheory
      As (liaHistory (paperDP T)) (paperDP T) truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm (liaHistory (paperDP T)) ≤ (b : ℝ))
    {W : ℕ → EF} (hW : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W (liaHistory (paperDP T)))
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (C : FeedbackTruthComputation
      (LUVCombination.normalizedMeshTruth As (liaHistory (paperDP T))
        (paperDP T) (paperDP_hworld T) b) f)
    (hsupport : WeightingSupportedOnDeferralImage W (liaHistory (paperDP T)) f) :
    weightedBias (fun i ↦ (W i).denote (liaHistory (paperDP T)))
      (fun i ↦ (As i).expect (liaHistory (paperDP T)) i) truth ≈ₙ (fun _ ↦ 0) := by
  haveI := feedbackLIA T
  exact luv_wubexp_ofComputation h hvalued hdet b hshare hW hWdiv hstrict
    (paperDP_hworld T) C hsupport

#print axioms lic_wubaff_ofComputation_unconditional
#print axioms lic_wub_ofComputation_unconditional
#print axioms boundedCombination_wubaff_ofComputation_unconditional
#print axioms luv_wubexp_ofComputation_unconditional

end FeedbackTruth
end LogicalInduction
