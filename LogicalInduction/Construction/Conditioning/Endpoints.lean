import LogicalInduction.Construction.Conditioning.TransductionFrame
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Conditioning.Compiler
import LogicalInduction.Construction.Conditioning.FramePass

/-! # `thm:scon` at the criterion level, and unconditionally over the constructed `LIA`

Closure Under Conditioning (tex:1613-1618, proved in app:scon) at the criterion level, in
both trader classes: conditioning a logical inductor on a fixed sentence `ψ`, and on the
growing prefix conjunctions `ψ₀ ⋏ ⋯ ⋏ ψₙ` of an efficiently computable sentence sequence,
again yields a logical inductor — of the conditioned market, over the extended process.

The packaging sits above both realizations of the conditioning translation because the
operational witness constructors must discharge both translation certificates at once: the
`dd:fuel` one from `Construction/Conditioning/FramePass.lean` and the machine one from
`Construction/Conditioning/TransductionFrame.lean`.  It can therefore live inside neither.

## What this module provides

* Three operational witness constructors — `eventualConditioningOperationalWitness`,
  `gatedConditioningOperationalWitness` and
  `denominatorPatchedGatedConditioningOperationalWitness` — filling the
  `conditioned_computable`, `translation_ec` and `translation_machine` fields of the witness
  structures of `Properties/Conditioning.lean`.
* The degenerate branch, `isMachineLogicalInductor_of_stage_unsatisfiable`: `def:lic` holds
  vacuously over a deductive process with an unsatisfiable stage.  It is the machine sibling
  of `isLogicalInductor_of_stage_unsatisfiable`.
* The machine-class endpoints at the paper's own quantifier, carrying no consistency
  hypothesis: `lic_conditioned_fixed_machine`,
  `lic_conditioned_growing_machine_ofProcessComputation`, and
  `lic_conditioned_growing_machine_ofSequence`, which takes an arbitrary
  `BigSentenceCodes ψ` and derives the prefix-conjunction certificate through
  `BigSentenceCodes.bigAnd` and `prefixConditioningPresentation`.
* The fuel-class siblings: `lic_conditioned_gated_ofMarketComputation`,
  `lic_conditioned_eventualOfFloor`, `lic_conditioned_eventual_ofMarketComputation`,
  `lic_conditioned_fixed_ofComputationAndMarket`,
  `lic_conditioned_growing_ofComputationsAndMarket` and
  `lic_conditioned_gated_ofComputationsAndMarket`.  Neither class's endpoints follow from
  the other's, so both stand.

## Unconditionally over the constructed `LIA`

The closing section makes `thm:scon` unconditional over a constructed `LIA`, in fixed and
growing forms and at both the fuel and machine quantifiers, with the degenerate
stage-unsatisfiable case carried by `isLogicalInductor_of_stage_unsatisfiable` and the
consistent case by propositional compactness.  `thm:scon` is a *transformation* result — the
constructed inductor, conditioned on a computable event, is again a logical inductor over the
union process — so `exists_growing_conditioned_machine_inductor` is its non-vacuity witness,
instantiated at `growingConditionProcess`, whose stages strictly grow, rather than at the
degenerate `extra.D n = ∅` inhabitant, which would make the conclusion a restatement of the
unconditioned theorem.  The semimeasure half of §4.6 — `thm:dus` and `thm:strict` over the
same inductor — is the lane `Construction/NonDogmatism.lean`.

## Repo-side hypotheses

`hjoint` — joint consistency of the base stages with the whole condition sequence — is not a
premise of `thm:scon`; it is what the analytic price-floor argument consumes.  The fixed and
growing forms discharge it themselves, by a case split on satisfiability and by
propositional compactness respectively, which is why they match the paper's statement with
no consistency hypothesis.

Non-vacuity of the arbitrary-e.c.-sequence quantifier is witnessed by `bigSentenceCodes_atom`
and the example beside it, at the injective atom family.  Every *public* declaration here is
inventoried in `AxiomAudit.lean` (the one `private` lemma, `bigSentenceCodes_atom`, cannot be
named from another file); the strength classification is the `thm:scon` row of
`scripts/coverage-classification.md`.
-/

namespace LogicalInduction

/-! ## The degenerate branch -/

/-- `def:lic` at the paper's own quantifier is satisfied vacuously over a deductive process
with an unsatisfiable stage: no trader of any class exploits such a process, so only
computability of the market and of the process remains to check.  This is the machine-class
sibling of `isLogicalInductor_of_stage_unsatisfiable`, and the degenerate branch of Closure
Under Conditioning — the case the paper's `thm:scon` covers implicitly when the extended
theory is inconsistent.  Kind `P`; hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem isMachineLogicalInductor_of_stage_unsatisfiable
    (V : History) (DP : DeductiveProcess)
    (hV : ComputableMarket V) (hDP : ComputableDeductiveProcess DP)
    {N : ℕ} (hN : ∀ v : PCWorld, ¬ v.ConsistentWith (DP.D N)) :
    IsMachineLogicalInductor V DP where
  marketComputable := hV
  processComputable := hDP
  noExploit Tr _ := Tr.not_exploits_of_stage_unsatisfiable V DP hV.1 hN

namespace ConditioningCompile

open RpnConditioning

/-! ## Operational witness constructors

The two token-metered translation certificates discharge the operational witness structures
of `Properties/Conditioning.lean`, closing the criterion level: conditioning a logical
inductor on a computable presentation yields a logical inductor of the conditioned market. -/

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
  translation_machine := fun T hT =>
    CondStep.eventualConditionedTranslation_preserves_machine floor
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

/-! ## The fuel-class `thm:scon` endpoints -/

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

/-! ## `thm:scon` at the paper's own quantifier -/

/-- `lic_conditioned_gated_ofMarketComputation` at the paper's own quantifier: from a
rational market computation and a positive denominator floor, conditioning a *machine*
logical inductor yields a machine logical inductor.  Neither class's endpoint is derivable
from the other's; both stand.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_machine_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    IsMachineLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_gated_machine P DP extra C
    (gatedConditioningOperationalWitness C market ε hε hfloor)

/-- `lic_conditioned_eventualOfFloor` at the paper's own quantifier: the prefix-safe
finite-zero compiler carries a *machine* logical inductor to a machine logical inductor of
the conditioned market.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventualOfFloor_machine
    (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (floor : EventualConditioningFloor P C.condition) :
    IsMachineLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_eventual_machine P DP extra C
    (eventualConditioningOperationalWitness C market floor)

/-- `lic_conditioned_eventual_ofMarketComputation` at the paper's own quantifier.  `hjoint`
is repo-side: it is not a premise of the paper's `thm:scon` but what the analytic
price-floor argument consumes.
Kind `C`; hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventual_machine_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i)) :
    IsMachineLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned_eventualOfFloor_machine P DP extra C market
    (eventualConditioningFloorOfJointConsistency
      P DP market C.condition C.condition_codes hjoint)

/-- **Fixed-sentence `thm:scon` at the paper's own quantifier**: conditioning a *machine*
logical inductor on a single sentence `ψ` yields a machine logical inductor over `Θ ∪ {ψ}`,
with **no** consistency hypothesis.  The two branches are the paper's own: where `Θ ∪ {ψ}`
stays satisfiable at every stage the analytic price-floor argument runs, and where some
stage is already unsatisfiable the criterion holds vacuously.  The stage program and the
rational market program the proof runs on are read off the inductor instance itself
(`processComputable`, `marketComputable`), so the statement carries no computability
premise beyond `IsMachineLogicalInductor`.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_machine
    (P : History) (DP : DeductiveProcess) [hLI : IsMachineLogicalInductor P DP]
    (ψ : Sentence) :
    IsMachineLogicalInductor
      (conditionedHistory P (fun _ => ψ)) (DP.adjoinSentence ψ) := by
  obtain ⟨base⟩ := hLI.processComputable.nonemptyComputation
  obtain ⟨market⟩ := hLI.marketComputable.nonemptyComputation
  let C := fixedConditioningPresentation base ψ
  by_cases hjoint : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds ψ
  · have hjointC : ∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
      intro n
      obtain ⟨v, hv, hψ⟩ := hjoint n
      exact ⟨v, hv, fun _ => hψ⟩
    have hresult :=
      lic_conditioned_eventual_machine_ofMarketComputation
        P DP (fixedConditionProcess ψ) C market hjointC
    simpa [C, fixedConditioningPresentation,
      DeductiveProcess.adjoinSentence] using hresult
  · push_neg at hjoint
    obtain ⟨N, hN⟩ := hjoint
    refine isMachineLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market (fun _ => ψ)
        (C.condition_codes)).toComputable)
      C.combined_computable (N := N) ?_
    intro v hv
    rw [DeductiveProcess.adjoinSentence,
      PCWorld.consistentWith_union_iff] at hv
    exact hN v hv.1 (hv.2 ψ (by simp [fixedConditionProcess]))

/-- **Growing finite-prefix `thm:scon`**, universally quantified over the adjoined
process `extra`, with **no** consistency hypothesis.  As in the fixed-sentence form the two
branches are the paper's own; where every finite stage of `Θ ∪ {ψ₁…ψₙ}` is satisfiable,
propositional compactness (`DeductiveProcess.exists_consistentWithTheory`) produces the
single world the price-floor argument consumes.  The base stage program and the rational
market program are read off the inductor instance itself.

**Scope** (this is the general *process*-quantified form; it takes a `def:ec` certificate as
data): the write-out efficiency of the cumulative conditions `n ↦ ⋀(extra.D n)` is supplied
by the `CompactConditioningProcessComputation` hypothesis, not derived here.  It proves
closure for every `extra` whose cumulative conditions are separately certified.  For the
paper's own quantifier — starting from an **arbitrary** efficiently computable
*individual-sentence* sequence `⟨ψ⟩` and conditioning on the prefix conjunctions
`ψ₀ ⋏ ⋯ ⋏ ψₙ` (tex:1613-1618, tex:6126), with the
`BigSentenceCodes ψ → BigSentenceCodes (n ↦ ⋀_{i≤n} ψ_i)` bridge *derived* by
`BigSentenceCodes.bigAnd` — use
`lic_conditioned_growing_machine_ofSequence` below.  For a non-degenerate `more` — nonempty,
strictly growing stages — see `growingCompactConditioningProcessComputation`.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_machine_ofProcessComputation
    (P : History) (DP extra : DeductiveProcess) [hLI : IsMachineLogicalInductor P DP]
    (more : CompactConditioningProcessComputation extra) :
    IsMachineLogicalInductor
      (conditionedHistory P
        (fun n => deductiveStageCondition (extra.D n)))
      (DP.union extra) := by
  obtain ⟨base⟩ := hLI.processComputable.nonemptyComputation
  obtain ⟨market⟩ := hLI.marketComputable.nonemptyComputation
  let C := conditioningPresentationOfComputations base more
  by_cases hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union extra).D n)
  · obtain ⟨w, hw⟩ := (DP.union extra).exists_consistentWithTheory hsat
    have hjointC : ∀ n, ∃ v : PCWorld,
        v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (C.condition i) := by
      intro n
      refine ⟨w, ((PCWorld.consistentWith_union_iff w DP extra n).mp (hw n)).1, fun i => ?_⟩
      exact (C.holds_condition i w).2
        ((PCWorld.consistentWith_union_iff w DP extra i).mp (hw i)).2
    exact lic_conditioned_eventual_machine_ofMarketComputation
      P DP extra C market hjointC
  · push_neg at hsat
    obtain ⟨N, hN⟩ := hsat
    exact isMachineLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market C.condition
        C.condition_codes).toComputable)
      C.combined_computable (N := N) hN

/-- **Growing `thm:scon` at the paper's own quantifier**: conditioning a *machine* logical
inductor on the prefix conjunctions `ψ₀ ⋏ ⋯ ⋏ ψₙ` of an **arbitrary** efficiently
computable sentence sequence `⟨ψ⟩` (`BigSentenceCodes ψ`) yields a machine logical inductor
over the growing process `Θ ∪ prefixProcess ψ` — whose stage `n` is `Θ.D n ∪ {ψ₀, …, ψₙ}`
and whose
union over all stages is `Θ ∪ {ψᵢ | i ∈ ℕ}` — with **no** consistency hypothesis.  This is
the endpoint the paper's growing clause (tex:1613-1618, appendix tex:6126) states: the
write-out efficiency of the growing conditions is *derived* from `BigSentenceCodes ψ` by
`BigSentenceCodes.bigAnd` (through `prefixConditioningPresentation`) rather than taken as
data, which is what `lic_conditioned_growing_machine_ofProcessComputation` asks for.  As in
that endpoint the
two branches are the paper's own: where every finite stage of `Θ ∪ {ψ₀…ψₙ}` is satisfiable,
propositional compactness produces the single world the price-floor argument consumes, and
where some stage is already unsatisfiable the criterion holds vacuously.  The base stage
program and the rational market program are read off the inductor instance itself.  The
condition carries a harmless `⊤` tail from `bigAnd`'s empty-fold terminator.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_machine_ofSequence
    (P : History) (DP : DeductiveProcess) [hLI : IsMachineLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) :
    IsMachineLogicalInductor
      (conditionedHistory P (fun n => sentenceConjunction ((List.range (n + 1)).map ψ)))
      (DP.union (prefixProcess ψ)) := by
  obtain ⟨base⟩ := hLI.processComputable.nonemptyComputation
  obtain ⟨market⟩ := hLI.marketComputable.nonemptyComputation
  let C := prefixConditioningPresentation base ψ hψ
  by_cases hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (prefixProcess ψ)).D n)
  · obtain ⟨w, hw⟩ := (DP.union (prefixProcess ψ)).exists_consistentWithTheory hsat
    exact lic_conditioned_eventual_machine_ofMarketComputation P DP (prefixProcess ψ) C market
      (fun n => ⟨w, ((PCWorld.consistentWith_union_iff w DP (prefixProcess ψ) n).mp (hw n)).1,
        fun i => (C.holds_condition i w).2
          ((PCWorld.consistentWith_union_iff w DP (prefixProcess ψ) i).mp (hw i)).2⟩)
  · push_neg at hsat
    obtain ⟨N, hN⟩ := hsat
    exact isMachineLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market C.condition C.condition_codes).toComputable)
      C.combined_computable (N := N) hN

/-! ## Non-vacuity of the e.c.-sequence quantifier -/

/-- The atom family `i ↦ atom i` is a written-out sentence sequence (`def:ec`): its
canonical Polish block is the single token `i + 5` (`rpn (atom i) = [i + 5]`), emitted by a
constant-shift poly-fueled program. -/
private lemma bigSentenceCodes_atom :
    BigSentenceCodes (fun i => (LO.Propositional.Formula.atom i : Sentence)) := by
  obtain ⟨c, hc⟩ := PolyFueled.id.addConst 5
  exact BigSentenceCodes.ofRpnSentenceCodes
    (RpnSentenceCodes.ofCanonical
      ((PolySegStream.ofTokenStream (PolyTokenStream.polyTok hc)).of_eq (fun i => rfl)))

/-- **Non-vacuity of the arbitrary-e.c.-sequence quantifier.**  A client instantiates
`lic_conditioned_growing_machine_ofSequence` at a genuinely growing sequence — the injective
atom family `i ↦ atom i`, whose prefix conjunctions strictly grow with `n` (they are not
eventually constant, unlike `growingConditionProcess`) — with the write-out certificate
discharged by `bigSentenceCodes_atom`.  This witnesses that the endpoint's hypothesis class
`BigSentenceCodes ψ` is inhabited by a non-degenerate `ψ`, so the paper's raw
e.c.-sequence quantifier is reached with content. -/
example (P : History) (DP : DeductiveProcess) [IsMachineLogicalInductor P DP] :
    IsMachineLogicalInductor
      (conditionedHistory P
        (fun n => sentenceConjunction
          ((List.range (n + 1)).map (fun i => (LO.Propositional.Formula.atom i : Sentence)))))
      (DP.union (prefixProcess (fun i => (LO.Propositional.Formula.atom i : Sentence)))) :=
  lic_conditioned_growing_machine_ofSequence P DP
    (fun i => (LO.Propositional.Formula.atom i : Sentence)) bigSentenceCodes_atom

end ConditioningCompile

end LogicalInduction

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open LO.Propositional
open Filter Topology

/-- `thm:scon` over the constructed `LIA` at a caller-supplied conditioning compiler: the
market and the inductor are discharged, the compiler is not.  The fixed and growing forms
below construct their compiler internally and are what a client should reach for.
Paper node: `thm:scon` -/
theorem lic_conditioned_ofCompiler_unconditional
    (T : ArithmeticTheory) [T.Δ₁]
    (extra : DeductiveProcess)
    (C : ConditioningPresentation (paperDP T) extra)
    (compiler : ConditioningTraderCompiler (liaHistory (paperDP T)) (paperDP T) extra C) :
    IsLogicalInductor (conditionedHistory (liaHistory (paperDP T)) C.condition)
      ((paperDP T).union extra) :=
  haveI : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_is_logical_inductor (paperDP T) (paperDP_computable T)
  lic_conditioned (liaHistory (paperDP T)) (paperDP T) extra C compiler

/-- Fixed-sentence `thm:scon` transfer over the constructed `LIA`, with **no** remaining
premise — the paper's statement exactly: conditioning the constructed inductor on any single
sentence `ψ` yields a logical inductor over `Θ ∪ {ψ}`, including the degenerate case where
`Θ ∪ {ψ}` is unsatisfiable at some stage (there the criterion holds vacuously; see
`isLogicalInductor_of_stage_unsatisfiable`).
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_unconditional
    (T : ArithmeticTheory) [T.Δ₁]
    (ψ : Sentence) :
    IsLogicalInductor
      (conditionedHistory (liaHistory (paperDP T)) (fun _ => ψ))
      ((paperDP T).adjoinSentence ψ) := by
  let base : DeductiveProcessComputation (paperDP T) :=
    (paperDP_computable T).nonemptyComputation.some
  haveI : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_is_logical_inductor (paperDP T) (paperDP_computable T)
  exact ConditioningCompile.lic_conditioned_fixed_ofComputationAndMarket
    (liaHistory (paperDP T)) (paperDP T)
    base (paperMarketComputation T) ψ

/-- Growing finite-prefix `thm:scon` transfer over the constructed `LIA`, with **no**
remaining premise — the paper's statement exactly.  The extra process supplies its compact
condition-code computation; the consistent case is carried by propositional compactness
(`DeductiveProcess.exists_consistentWithTheory`, which turns per-stage satisfiability of
`Θ ∪ {ψ₁…ψₙ}` into one world satisfying the whole growing theory, as the price-floor
argument needs) and the degenerate case by `isLogicalInductor_of_stage_unsatisfiable`.
Kind `C`; hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_unconditional
    (T : ArithmeticTheory) [T.Δ₁]
    (extra : DeductiveProcess)
    (more : CompactConditioningProcessComputation extra) :
    IsLogicalInductor
      (conditionedHistory (liaHistory (paperDP T))
        (fun n => deductiveStageCondition (extra.D n)))
      ((paperDP T).union extra) := by
  let base : DeductiveProcessComputation (paperDP T) :=
    (paperDP_computable T).nonemptyComputation.some
  haveI : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_is_logical_inductor (paperDP T) (paperDP_computable T)
  exact ConditioningCompile.lic_conditioned_growing_ofComputationsAndMarket
    (liaHistory (paperDP T)) (paperDP T) extra
    base more (paperMarketComputation T)

/-- **Fixed-sentence `thm:scon` over the constructed `LIA`, at the paper's own
quantifier**: conditioning on any single sentence `ψ` yields a market no trader in ordinary
machine polynomial time exploits, with no remaining premise.
Kind `C`; hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_machine_unconditional
    (T : ArithmeticTheory) [T.Δ₁]
    (ψ : Sentence) :
    IsMachineLogicalInductor
      (conditionedHistory (liaHistory (paperDP T)) (fun _ => ψ))
      ((paperDP T).adjoinSentence ψ) := by
  haveI : IsMachineLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_isMachineLogicalInductor (paperDP T) (paperDP_computable T)
  exact ConditioningCompile.lic_conditioned_fixed_machine
    (liaHistory (paperDP T)) (paperDP T) ψ

/-- **Growing finite-prefix `thm:scon` over the constructed `LIA`, at the paper's own
quantifier**, with no remaining premise.
Kind `C`; hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_machine_unconditional
    (T : ArithmeticTheory) [T.Δ₁]
    (extra : DeductiveProcess)
    (more : CompactConditioningProcessComputation extra) :
    IsMachineLogicalInductor
      (conditionedHistory (liaHistory (paperDP T))
        (fun n => deductiveStageCondition (extra.D n)))
      ((paperDP T).union extra) := by
  haveI : IsMachineLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_isMachineLogicalInductor (paperDP T) (paperDP_computable T)
  exact ConditioningCompile.lic_conditioned_growing_machine_ofProcessComputation
    (liaHistory (paperDP T)) (paperDP T) extra more

/-! ## The growing form, non-vacuously -/

/-- **The growing form of `thm:scon` doing visible work.**  Instantiated at
`growingConditionProcess`, whose stages are nonempty and *strictly grow*, so the adjoined
condition is a real sentence — never the empty conjunction `⊤` — and it changes as the
stages advance.  The degenerate inhabitant of the compact interface
(`compactConditioningProcessComputation_nonempty`, with `extra.D n = ∅`) is deliberately
**not** used here: it would make `DP.union extra = DP` and the conclusion a restatement of
the unconditioned theorem.

Kind `N+` non-vacuity witness.
Paper node: `thm:scon` -/
theorem exists_growing_conditioned_machine_inductor
    (T : ArithmeticTheory) [T.Δ₁] :
    ∃ extra : DeductiveProcess,
      extra.D 0 ⊂ extra.D 1 ∧
      (∀ n, deductiveStageCondition (extra.D n) ≠ ⊤) ∧
      deductiveStageCondition (extra.D 0) ≠ deductiveStageCondition (extra.D 1) ∧
      IsMachineLogicalInductor
        (conditionedHistory (liaHistory (paperDP T))
          (fun n => deductiveStageCondition (extra.D n)))
        ((paperDP T).union extra) :=
  ⟨growingConditionProcess, growingConditionProcess_ssubset,
    deductiveStageCondition_growing_ne_top, deductiveStageCondition_growing_ne,
    lic_conditioned_growing_machine_unconditional T growingConditionProcess
      growingCompactConditioningProcessComputation⟩

end LogicalInduction
