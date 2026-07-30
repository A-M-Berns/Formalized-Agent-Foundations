import LogicalInduction.Construction.Witnesses.ComputationDP
import LogicalInduction.Construction.Witnesses.BitPrefixSyntax
import LogicalInduction.Construction.Witnesses.ConditioningCompiler
import LogicalInduction.Construction.Witnesses.RpnConditioning
import LogicalInduction.Construction.Witnesses.UniversalDovetailer

/-!
# Unconditional instantiations over the constructed `LIA` — semimeasure & conditioning

Companion to `ComputationDP.lean` (which instantiates the meta-learning and self-reference
endpoints over the provability process `theoremDP`).  Here two further property families are
made unconditional over a constructed `LIA` inductor:

* **Universal semimeasure** (`thm:dus`) over the constantly-empty deductive process, whose
  market non-vacuity `hworld` is trivial (no stage constrains any world).
* **Conditioning** (`thm:scon`), a *transformation* result: the constructed inductor,
  conditioned on a computable event, is again a logical inductor over the union process.

Where a from-below approximation of the semimeasure and its threshold-emission certificate
(`A`/`emit`) are still needed, they stay explicit caller inputs rather than being assumed.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology

/-! ## The empty deductive process is computable, with trivial non-vacuity -/

/-- The constantly-empty deductive process is computable: one fixed program emits the code
of `∅` on every input. -/
lemma emptyBitDeductiveProcess_computable :
    ComputableDeductiveProcess emptyBitDeductiveProcess :=
  ⟨Nat.Partrec.Code.const (Encodable.encode (∅ : Finset Sentence)), fun n => by
    simp [emptyBitDeductiveProcess, Nat.Partrec.Code.eval_const]⟩

/-- Every world is (vacuously) consistent with an empty stage. -/
lemma emptyBitDeductiveProcess_hworld (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith (emptyBitDeductiveProcess.D n) :=
  ⟨fun _ => False, by intro φ hφ; simp [emptyBitDeductiveProcess] at hφ⟩

/-! ## Universal semimeasure domination, unconditional over `LIA` -/

/-- `thm:dus`, unconditional over `LIA` except for the semimeasure's approximation data.
The market / inductor / non-vacuity side is fully discharged — the inductor is the
constructed `LIA` over the (computable) empty process and `hworld` is trivial — so only the
from-below approximation `A` and its threshold emission `emit` remain caller inputs.

**Vacuous:** the hypothesis `C` is uninhabited — `bitPrefixCodeComputation_isEmpty`
(`Construction/Witnesses/BitPrefixSyntax.lean`) proves that the whole-value code bound the
literal prefix conjunction is asked for cannot hold.  The statement is true but empty, and so
are the two `thm:dus` endpoints below, until that interface is repaired.
Paper node: `thm:dus` -/
theorem lic_domination_universalSemimeasure_unconditional
    (C : BitPrefixCodeComputation ordinaryIndependentBitAtoms)
    {M : LowerSemicomputableContinuousSemimeasure}
    (A : DUSApproximationPresentation M
      (bitPrefixSentencesOfIndependentAtoms ordinaryIndependentBitAtoms C))
    (emit : DUSThresholdEmission A) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * M.mass σ ≤ limitingBelief (liaHistory emptyBitDeductiveProcess)
        (bitPrefixSentence ordinaryIndependentBitAtoms.atom σ) :=
  haveI : IsLogicalInductor (liaHistory emptyBitDeductiveProcess) emptyBitDeductiveProcess :=
    LIA_is_logical_inductor emptyBitDeductiveProcess emptyBitDeductiveProcess_computable
  lic_domination_universalSemimeasure_ofIndependentAtoms ordinaryIndependentBitAtoms C A emit
    (liaHistory emptyBitDeductiveProcess)
    emptyBitDeductiveProcess_hworld

/-- **`thm:dus` over the constructed dovetail, with no semimeasure input.**  `M` is
`Construction/Witnesses/UniversalDovetailer.lean`'s explicit dovetail `M*`, and both the
from-below approximation and its threshold emission are discharged there by the
self-clamped stage table, so the only remaining caller input is the prefix-sentence code
emitter `C` — which is **uninhabited** (`bitPrefixCodeComputation_isEmpty`), leaving this
statement vacuous.
Paper node: `thm:dus` -/
theorem lic_domination_dovetailSemimeasure_unconditional
    (C : BitPrefixCodeComputation ordinaryIndependentBitAtoms) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * Dovetail.universalMass σ ≤ limitingBelief (liaHistory emptyBitDeductiveProcess)
        (bitPrefixSentence ordinaryIndependentBitAtoms.atom σ) :=
  lic_domination_universalSemimeasure_unconditional C
    (Dovetail.dusApproximationPresentation
      (bitPrefixSentencesOfIndependentAtoms ordinaryIndependentBitAtoms C) (fun _ ↦ rfl))
    (Dovetail.dusThresholdEmission _ _)

/-- **The paper's actual `thm:dus` conclusion, unconditional on the semimeasure side.**
Because the dovetail is *universal*, the constructed market's limiting beliefs dominate
**every** lower-semicomputable continuous semimeasure, with a constant assembled from the
dovetail weight of that semimeasure's own approximation program.

**Vacuous** for the same reason as the two statements above: `C` is uninhabited.
Paper node: `thm:dus` -/
theorem lic_domination_everyLowerSemicomputable_unconditional
    (C : BitPrefixCodeComputation ordinaryIndependentBitAtoms)
    (ν : LowerSemicomputableContinuousSemimeasure) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * ν.mass σ ≤ limitingBelief (liaHistory emptyBitDeductiveProcess)
        (bitPrefixSentence ordinaryIndependentBitAtoms.atom σ) := by
  obtain ⟨K, hK, hbelief⟩ := lic_domination_dovetailSemimeasure_unconditional C
  obtain ⟨c, hc, hdom⟩ := Dovetail.universalMass_dominates ν
  refine ⟨K * c, mul_pos hK hc, fun σ ↦ ?_⟩
  calc K * c * ν.mass σ = K * (c * ν.mass σ) := by ring
    _ ≤ K * Dovetail.universalMass σ := by
        exact mul_le_mul_of_nonneg_left (hdom σ) hK.le
    _ ≤ _ := hbelief σ

/-! ## Conditioning over the constructed `LIA` -/

/-- Compatibility wrapper for a caller-supplied conditioning compiler.  The paper-facing
fixed and growing forms below construct the repaired compiler internally.
Paper node: `thm:scon` -/
theorem lic_conditioned_ofCompiler_unconditional
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (extra : DeductiveProcess)
    (C : ConditioningPresentation (theoremDP T) extra)
    (compiler : ConditioningTraderCompiler (liaHistory (theoremDP T)) (theoremDP T) extra C) :
    IsLogicalInductor (conditionedHistory (liaHistory (theoremDP T)) C.condition)
      ((theoremDP T).union extra) :=
  haveI : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
    LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)
  lic_conditioned (liaHistory (theoremDP T)) (theoremDP T) extra C compiler

/-- Fixed-sentence `thm:scon` transfer over the constructed `LIA`, with **no** remaining
premise — the paper's statement exactly: conditioning the constructed inductor on any single
sentence `ψ` yields a logical inductor over `Θ ∪ {ψ}`, including the degenerate case where
`Θ ∪ {ψ}` is unsatisfiable at some stage (there the criterion holds vacuously; see
`isLogicalInductor_of_stage_unsatisfiable`).
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_unconditional
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (ψ : Sentence) :
    IsLogicalInductor
      (conditionedHistory (liaHistory (theoremDP T)) (fun _ => ψ))
      ((theoremDP T).adjoinSentence ψ) := by
  let base : DeductiveProcessComputation (theoremDP T) :=
    (theoremDP_computable T).nonemptyComputation.some
  haveI : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
    LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)
  exact ConditioningCompile.lic_conditioned_fixed_ofComputationAndMarket
    (liaHistory (theoremDP T)) (theoremDP T)
    base (theoremMarketComputation T) ψ

/-- Growing finite-prefix `thm:scon` transfer over the constructed `LIA`, with **no**
remaining premise — the paper's statement exactly.  The extra process supplies its compact
condition-code computation; the consistent case is carried by propositional compactness
(`DeductiveProcess.exists_consistentWithTheory`, which turns per-stage satisfiability of
`Θ ∪ {ψ₁…ψₙ}` into one world satisfying the whole growing theory, as the price-floor
argument needs) and the degenerate case by `isLogicalInductor_of_stage_unsatisfiable`.
Kind `C`; hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_unconditional
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (extra : DeductiveProcess)
    (more : CompactConditioningProcessComputation extra) :
    IsLogicalInductor
      (conditionedHistory (liaHistory (theoremDP T))
        (fun n => deductiveStageCondition (extra.D n)))
      ((theoremDP T).union extra) := by
  let base : DeductiveProcessComputation (theoremDP T) :=
    (theoremDP_computable T).nonemptyComputation.some
  haveI : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
    LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)
  exact ConditioningCompile.lic_conditioned_growing_ofComputationsAndMarket
    (liaHistory (theoremDP T)) (theoremDP T) extra
    base more (theoremMarketComputation T)

#print axioms lic_domination_universalSemimeasure_unconditional
#print axioms lic_domination_dovetailSemimeasure_unconditional
#print axioms lic_domination_everyLowerSemicomputable_unconditional
#print axioms lic_conditioned_ofCompiler_unconditional
#print axioms lic_conditioned_fixed_unconditional
#print axioms lic_conditioned_growing_unconditional

end LogicalInduction
