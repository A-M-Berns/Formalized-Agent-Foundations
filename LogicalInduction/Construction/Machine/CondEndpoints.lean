/-
# `thm:scon` at the criterion level

`Construction/Witnesses/RpnConditioning.lean` certifies the conditioning translation in the
`dd:fuel` model; `Construction/Machine/CondStep.lean` certifies the same translation in the
machine model.  The criterion-level packaging — the operational witness constructors and the
paper-facing endpoints — belongs above *both*, which is why it lives here rather than inside
either realization.

The block below moved here unchanged from `RpnConditioning.lean`; every statement is
byte-identical to what it was there, and the `ConditioningCompile` namespace is preserved so
that the audit inventory's references still resolve.  What is new is the machine-class
material at the end: the machine field on the witness structures and the machine-class
endpoints.

**The eventual witness carries no machine field**, deliberately.  Its translation is
`eventualConditionedTranslation`, whose price rewrite is the zero-aware emitter
`rpnZeroAwareEmit` rather than the gated one, and that emitter has no machine realization
yet.  A field no constructor can discharge is a `sorry` one indirection away, so it is
absent rather than unfilled; `Properties/Conditioning.lean` records the same at the
structure.
-/
import LogicalInduction.Construction.Machine.CondStep

namespace LogicalInduction

namespace ConditioningCompile

open RpnConditioning

/-! ## `thm:scon` packaging: operational witnesses and the paper-facing endpoints

The two symbol-metered translation certificates discharge the operational witness
structures of `Properties/Conditioning.lean`, closing the criterion level: conditioning a
logical inductor on a computable presentation yields a logical inductor of the
conditioned market. -/

/-! ### Public operational witness constructors -/

/-- Construct the complete prefix-safe operational witness from an exact rational market
and a finite-zero floor certificate.
Paper node: `thm:scon` -/
noncomputable def eventualConditioningOperationalWitness
    {P : History} {DP extra : DeductiveProcess}
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (floor : EventualConditioningFloor P C.condition) :
    EventualConditioningOperationalWitness P DP extra C where
  floor := floor
  conditioned_computable :=
    (conditionedMarketComputation market C.condition C.condition_codes).toComputable
  translation_ec := fun T hT =>
    eventualConditionedTranslation_preserves_ecRpn floor
      C.condition_codes T hT

/-- Construct the complete gated-conditioning operational witness from a named rational
base-market computation and an actual positive denominator floor.
Paper node: `thm:scon` -/
noncomputable def gatedConditioningOperationalWitness
    {P : History} {DP extra : DeductiveProcess}
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    GatedConditioningOperationalWitness P DP extra C ε where
  epsilon_pos := hε
  denominator_floor := hfloor
  conditioned_computable :=
    (conditionedMarketComputation market C.condition C.condition_codes).toComputable
  translation_ec := fun T hT =>
    conditionedTranslation_preserves_ecRpn C.condition
      C.condition_codes ε T hT
  translation_machine := fun T hT =>
    CondStep.conditionedTranslation_preserves_machine C.condition
      C.condition_codes ε T hT

/-- The paper's finite-prefix denominator repair supplies the floor and the exact rational
market computation required by the operational witness.  Transporting logical induction
from `P` to the patched history is a separate step, behind the qualified
finite-perturbation theorem and its two `EfficientPrefixPatch` certificates.
Paper node: `thm:scon` -/
noncomputable def denominatorPatchedGatedConditioningOperationalWitness
    {P : History} {DP extra : DeductiveProcess}
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (cutoff : ℕ) (ε : ℚ) (hε : 0 < (ε : ℝ)) (hεone : (ε : ℝ) ≤ 1)
    (htail : ∀ day, cutoff ≤ day → (ε : ℝ) ≤ P day (C.condition day)) :
    GatedConditioningOperationalWitness
      (denominatorPatchedHistory P C.condition cutoff) DP extra C ε :=
  gatedConditioningOperationalWitness C
    (denominatorPatchedMarketComputation market C.condition C.condition_codes cutoff)
    ε hε (denominatorPatchedHistory_floor P C.condition cutoff hεone htail)

/-! ### The paper-facing `thm:scon` endpoints -/

/-- Closure under conditioning through the concrete gated translator.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_gated P DP extra C
    (gatedConditioningOperationalWitness C market ε hε hfloor)

/-- **The same at the paper's own quantifier**: from a rational market computation and a
positive denominator floor, conditioning a *machine* logical inductor yields a machine
logical inductor.  The fuel-class endpoint above is neither derivable from this nor it from
that; both stand.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_machine_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    IsMachineLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_gated_machine P DP extra C
    (gatedConditioningOperationalWitness C market ε hε hfloor)

/-- Closure under conditioning through the prefix-safe finite-zero compiler.  This does
not modify the base history and therefore does not depend on unrestricted
finite-perturbation closure.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventualOfFloor
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (floor : EventualConditioningFloor P C.condition) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_eventual P DP extra C
    (eventualConditioningOperationalWitness C market floor)

/-- Closure under conditioning from joint consistency of the base stages with the whole
condition sequence, plus concrete computability data.  The proof stays on the original
market: the finite exceptional prefix is handled by the zero-aware compiler.

`hjoint` is **repo-side**, not a premise of the paper's `thm:scon`; it is what the analytic
price-floor argument consumes, and it confines this constructor to the
consistent-conditioning case.  The degenerate case (some stage of the union process has no
propositionally consistent world) is handled separately by
`isLogicalInductor_of_stage_unsatisfiable`.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventual_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i)) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned_eventualOfFloor P DP extra C market
    (eventualConditioningFloorOfJointConsistency
      P DP market C.condition C.condition_codes hjoint)

/-- Fixed-sentence form of Closure Under Conditioning, with **no** consistency hypothesis —
the paper's `thm:scon` statement exactly.  The two branches are the paper's two cases: where
`Θ ∪ {ψ}` stays satisfiable at every stage the analytic price-floor argument runs, and where
some stage of `Θ ∪ {ψ}` is already unsatisfiable the criterion holds vacuously (no plausible
world remains to assess a trader's net worth, so nothing exploits — the paper's remark that
conditional prices go to `1` where the denominator vanishes).
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_ofComputationAndMarket
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP) (market : MarketComputation P)
    (ψ : Sentence) :
    IsLogicalInductor
      (conditionedHistory P (fun _ => ψ)) (DP.adjoinSentence ψ) := by
  let C := fixedConditioningPresentation base ψ
  by_cases hjoint : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds ψ
  · have hjointC : ∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
      intro n
      obtain ⟨v, hv, hψ⟩ := hjoint n
      exact ⟨v, hv, fun _ => hψ⟩
    have hresult :=
      lic_conditioned_eventual_ofMarketComputation
        P DP (fixedConditionProcess ψ) C market hjointC
    simpa [C, fixedConditioningPresentation,
      DeductiveProcess.adjoinSentence] using hresult
  · push_neg at hjoint
    obtain ⟨N, hN⟩ := hjoint
    refine isLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market (fun _ => ψ)
        (C.condition_codes)).toComputable)
      C.combined_computable (N := N) ?_
    intro v hv
    rw [DeductiveProcess.adjoinSentence,
      PCWorld.consistentWith_union_iff] at hv
    exact hN v hv.1 (hv.2 ψ (by simp [fixedConditionProcess]))

/-- Growing finite-prefix form of Closure Under Conditioning, with **no** consistency
hypothesis — the paper's `thm:scon` statement exactly.  As in the fixed-sentence form, the
two branches are the paper's two cases.  Where every finite stage of `Θ ∪ {ψ₁…ψₙ}` is
satisfiable, propositional compactness (`DeductiveProcess.exists_consistentWithTheory`)
produces a *single* world consistent with the whole growing theory, which is exactly what
the analytic price-floor argument consumes.  Where some stage is already unsatisfiable the
criterion holds vacuously.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_ofComputationsAndMarket
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra)
    (market : MarketComputation P) :
    IsLogicalInductor
      (conditionedHistory P
        (fun n => deductiveStageCondition (extra.D n)))
      (DP.union extra) := by
  let C := conditioningPresentationOfComputations base more
  by_cases hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union extra).D n)
  · obtain ⟨w, hw⟩ := (DP.union extra).exists_consistentWithTheory hsat
    have hjointC : ∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
      intro n
      refine ⟨w, ((PCWorld.consistentWith_union_iff w DP extra n).mp (hw n)).1, fun i => ?_⟩
      exact (C.holds_condition i w).2
        ((PCWorld.consistentWith_union_iff w DP extra i).mp (hw i)).2
    exact lic_conditioned_eventual_ofMarketComputation
      P DP extra C market hjointC
  · push_neg at hsat
    obtain ⟨N, hN⟩ := hsat
    exact isLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market C.condition
        C.condition_codes).toComputable)
      C.combined_computable (N := N) hN

/-- Paper-facing SCON constructor: the canonical finite-stage presentation and the complete
market/trader compiler are both assembled from their named computations.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_ofComputationsAndMarket
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (base : DeductiveProcessComputation DP)
    (more : CompactConditioningProcessComputation extra)
    (market : MarketComputation P) (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤
      P d (deductiveStageCondition (extra.D d))) :
    IsLogicalInductor
      (conditionedHistory P (fun n => deductiveStageCondition (extra.D n)))
      (DP.union extra) :=
  lic_conditioned_gated_ofMarketComputation P DP extra
    (conditioningPresentationOfComputations base more) market ε hε hfloor

#print axioms eventualConditioningOperationalWitness
#print axioms gatedConditioningOperationalWitness
#print axioms denominatorPatchedGatedConditioningOperationalWitness
#print axioms lic_conditioned_gated_ofMarketComputation
#print axioms lic_conditioned_gated_machine_ofMarketComputation
#print axioms lic_conditioned_eventualOfFloor
#print axioms lic_conditioned_eventual_ofMarketComputation
#print axioms lic_conditioned_fixed_ofComputationAndMarket
#print axioms lic_conditioned_growing_ofComputationsAndMarket
#print axioms lic_conditioned_gated_ofComputationsAndMarket

end ConditioningCompile

end LogicalInduction
