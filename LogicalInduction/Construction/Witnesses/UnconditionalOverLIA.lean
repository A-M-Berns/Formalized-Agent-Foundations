import LogicalInduction.Construction.Witnesses.ComputationDP
import LogicalInduction.Construction.Witnesses.BitPrefixSyntax
import LogicalInduction.Construction.Witnesses.ConditioningCompiler

/-!
# Unconditional instantiations over the constructed `LIA` — semimeasure & conditioning

Companion to `ComputationDP.lean` (which instantiates the meta-learning and self-reference
endpoints over the provability process `theoremDP`).  Here two further property families are
made unconditional over a constructed `LIA` inductor:

* **Universal semimeasure** (`thm:dus`) over the constantly-empty deductive process, whose
  market non-vacuity `hworld` is trivial (no stage constrains any world).
* **Conditioning** (`thm:scon`), a *transformation* result: the constructed inductor,
  conditioned on a computable event, is again a logical inductor over the union process.

The remaining disclosed boundary `M7-DUS-APPROX` (the from-below approximation `A`/`emit`)
stays an explicit caller input.
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

/-- `thm:dus`, unconditional over `LIA` modulo the disclosed `M7-DUS-APPROX` approximation.
The market / inductor / non-vacuity side is fully discharged — the inductor is the
constructed `LIA` over the (computable) empty process and `hworld` is trivial — so only the
from-below approximation `A` and its threshold emission `emit` remain caller inputs.
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

/-- Fixed-sentence `thm:scon` over the constructed `LIA`.  Only the paper's joint
consistency premise remains.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_unconditional
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (ψ : Sentence)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith ((theoremDP T).D n) ∧ v.Holds ψ) :
    IsLogicalInductor
      (conditionedHistory (liaHistory (theoremDP T)) (fun _ => ψ))
      ((theoremDP T).adjoinSentence ψ) := by
  let base : DeductiveProcessComputation (theoremDP T) :=
    (theoremDP_computable T).nonemptyComputation.some
  haveI : IsLogicalInductor (liaHistory (theoremDP T)) (theoremDP T) :=
    LIA_is_logical_inductor (theoremDP T) (theoremDP_computable T)
  exact ConditioningCompile.lic_conditioned_fixed_ofComputationAndMarket
    (liaHistory (theoremDP T)) (theoremDP T)
    base (theoremMarketComputation T) ψ hjoint

/-- Growing finite-prefix `thm:scon` over the constructed `LIA`.  The extra process supplies
its compact condition-code computation, and the remaining semantic premise is exactly joint
consistency of the base stages with the full growing condition theory.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_unconditional
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (extra : DeductiveProcess)
    (more : CompactConditioningProcessComputation extra)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith ((theoremDP T).D n) ∧
        ∀ i, v.ConsistentWith (extra.D i)) :
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
    base more (theoremMarketComputation T) hjoint

#print axioms lic_domination_universalSemimeasure_unconditional
#print axioms lic_conditioned_ofCompiler_unconditional
#print axioms lic_conditioned_fixed_unconditional
#print axioms lic_conditioned_growing_unconditional

end LogicalInduction
