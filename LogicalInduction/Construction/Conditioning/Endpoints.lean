import LogicalInduction.Construction.Conditioning.TransductionFrame
import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Construction.Conditioning.Compiler
import LogicalInduction.Construction.Conditioning.FramePass

/-! # `thm:scon` at the criterion level, and unconditionally over the constructed `LIA`

Closure Under Conditioning (tex:1613-1618, proved in app:scon) at the criterion level, at
`def:ec`'s own trader class: conditioning a logical inductor on a fixed sentence `ψ`,
and on the growing prefix conjunctions `ψ₀ ⋏ ⋯ ⋏ ψₙ` of an efficiently computable sentence
sequence, again yields a logical inductor — of the conditioned market, over the
extended process.

The packaging sits above the market compiler and the transducer both — it needs
`conditionedMarketComputation` from `Construction/Conditioning/Compiler.lean` and
`CondStep.conditionedTranslation_preserves_ec` from
`Construction/Conditioning/TransductionFrame.lean` — so it can live inside neither.

## What this module provides

* Three operational witness constructors — `eventualConditioningOperationalWitness`,
  `gatedConditioningOperationalWitness` and
  `denominatorPatchedGatedConditioningOperationalWitness` — filling the
  `conditioned_computable` and `translation_ec` fields of the witness structures of
  `Properties/Conditioning.lean`.
* The degenerate branch is `isLogicalInductor_of_stage_unsatisfiable`
  (`Framework/Affine.lean`): `def:lic` holds vacuously over a deductive process with an
  unsatisfiable stage, since no trader of any class exploits one.
* The endpoints at the paper's own quantifier, carrying no consistency hypothesis:
  `lic_conditioned_fixed`, `lic_conditioned_growing_ofProcessComputation`, and
  `lic_conditioned_growing_ofSequence`, which takes an arbitrary `MachineSentenceCodes ψ`
  and derives the prefix-conjunction certificate through `MachineSentenceCodes.bigAnd` and
  `prefixConditioningPresentation`; and the parametric forms
  `lic_conditioned_gated_ofMarketComputation`, `lic_conditioned_eventualOfFloor` and
  `lic_conditioned_eventual_ofMarketComputation`.

**One layer.**  `def:ec` quantifies over ordinary machine polynomial time on both sides of
`thm:scon`, so these statements are the paper's, and there is no second layer stating the
same node over the certification engine's own class: closure of *that* class under the
conditioning translation is a fact about `dd:fuel` rather than a claim of the paper's.  The
fuel calculus still certifies traders — it is how the machine witnesses below get proved in
`Construction/Conditioning/FramePass.lean`'s sibling passes — it is simply not published as
a second conclusion.

## Unconditionally over the constructed `LIA`

The closing section makes `thm:scon` unconditional over a constructed `LIA`, in fixed and
growing forms at the paper's own quantifier, with the degenerate stage-unsatisfiable case
carried by `isLogicalInductor_of_stage_unsatisfiable` and the consistent case by
propositional compactness.  `thm:scon` is a *transformation* result — the
constructed inductor, conditioned on a computable event, is again a logical inductor over the
union process — so `exists_growing_conditioned_inductor` is its non-vacuity witness,
instantiated at the prefix process of the injective atom family, whose stages grow strictly
at *every* day, rather than at the degenerate `extra.D n = ∅` inhabitant, which would make
the conclusion a restatement of the unconditioned theorem.  The compact
`deductiveStageCondition` interface has its own non-degenerate inhabitant,
`growingConditionProcess`, whose condition is never `⊤` but changes exactly once (day `0`
adjoins `atom 0`, every later day `atom 0` and `atom 1`); it cannot grow at every day,
because a `Finset` stage erases the index order the condition emitter needs — see the
prefix-conjunction section of `Construction/Conditioning/Presentation.lean`.  The semimeasure half of §4.6 — `thm:dus` and `thm:strict` over the
same inductor — is the lane `Construction/NonDogmatism.lean`.

## Repo-side hypotheses

`hjoint` — joint consistency of the base stages with the whole condition sequence — is not a
premise of `thm:scon`; it is what the analytic price-floor argument consumes.  The fixed and
growing forms discharge it themselves, by a case split on satisfiability and by
propositional compactness respectively, which is why they match the paper's statement with
no consistency hypothesis.

Non-vacuity of the arbitrary-e.c.-sequence quantifier is witnessed by the example below, at
the injective atom family, whose write-out certificate is `machineSentenceCodes_atom`
(`Framework/Machine/Witnesses.lean`).  Every *public* declaration here is inventoried in
`AxiomAudit.lean`; the three `private` lemmas are that family's growth facts, which cannot
be named from another file.  The strength classification is the `thm:scon` row of
`scripts/coverage-classification.md`.
**The criterion binder below is `def:lic` at the paper's own quantifier throughout**, in and out: every endpoint
takes `[IsLogicalInductor P DP]` and concludes `IsLogicalInductor`, which is
`def:lic` at the paper's own quantifier over `EfficientlyComputable`.  The `_unconditional`
endpoints discharge it through `LIA_is_logical_inductor`.

-/

namespace LogicalInduction

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
    CondStep.eventualConditionedTranslation_preserves_ec floor
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
    CondStep.conditionedTranslation_preserves_ec C.condition
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

/-! ## `thm:scon` at the paper's own quantifier -/

/-- Closure under conditioning through the concrete gated translator: from a rational market
computation and a positive denominator floor, conditioning a *machine* logical inductor
yields a logical inductor.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_ofMarketComputation
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) (market : MarketComputation P)
    (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  LogicalInduction.lic_conditioned_gated P DP extra C
    (gatedConditioningOperationalWitness C market ε hε hfloor)

/-- Closure under conditioning through the prefix-safe finite-zero compiler, which carries
a *machine* logical inductor to a logical inductor of the conditioned market.  This
does not modify the base history and therefore does not depend on unrestricted
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
Kind `C`; hypotheses `(a)`.
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

/-- **Fixed-sentence `thm:scon` at the paper's own quantifier**: conditioning a *machine*
logical inductor on a single sentence `ψ` yields a logical inductor over `Θ ∪ {ψ}`,
with **no** consistency hypothesis.  The two branches are the paper's own: where `Θ ∪ {ψ}`
stays satisfiable at every stage the analytic price-floor argument runs, and where some
stage is already unsatisfiable the criterion holds vacuously.  The stage program and the
rational market program the proof runs on are read off the inductor instance itself
(`processComputable`, `marketComputable`), so the statement carries no computability
premise beyond `IsLogicalInductor`.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed
    (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (ψ : Sentence) :
    IsLogicalInductor
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
      lic_conditioned_eventual_ofMarketComputation
        P DP (fixedConditionProcess ψ) C market hjointC
    simpa [C, fixedConditioningPresentation,
      DeductiveProcess.adjoinSentence] using hresult
  · push Not at hjoint
    obtain ⟨N, hN⟩ := hjoint
    refine isLogicalInductor_of_stage_unsatisfiable _ _
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
`MachineSentenceCodes ψ → MachineSentenceCodes (n ↦ ⋀_{i≤n} ψ_i)` bridge *derived* by
`MachineSentenceCodes.bigAnd` — use
`lic_conditioned_growing_ofSequence` below.  For a non-degenerate `more` — nonempty stages
whose condition is never `⊤` and changes once — see
`growingCompactConditioningProcessComputation`.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_ofProcessComputation
    (P : History) (DP extra : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (more : CompactConditioningProcessComputation extra) :
    IsLogicalInductor
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
    exact lic_conditioned_eventual_ofMarketComputation
      P DP extra C market hjointC
  · push Not at hsat
    obtain ⟨N, hN⟩ := hsat
    exact isLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market C.condition
        C.condition_codes).toComputable)
      C.combined_computable (N := N) hN

/-- **Growing `thm:scon` at the paper's own quantifier**: conditioning a *machine* logical
inductor on the prefix conjunctions `ψ₀ ⋏ ⋯ ⋏ ψₙ` of an **arbitrary** efficiently
computable sentence sequence `⟨ψ⟩` (`MachineSentenceCodes ψ`) yields a logical inductor
over the growing process `Θ ∪ prefixProcess ψ` — whose stage `n` is `Θ.D n ∪ {ψ₀, …, ψₙ}`
and whose
union over all stages is `Θ ∪ {ψᵢ | i ∈ ℕ}` — with **no** consistency hypothesis.  This is
the endpoint the paper's growing clause (tex:1613-1618, appendix tex:6126) states: the
write-out efficiency of the growing conditions is *derived* from `MachineSentenceCodes ψ` by
`MachineSentenceCodes.bigAnd` (through `prefixConditioningPresentation`) rather than taken as
data, which is what `lic_conditioned_growing_ofProcessComputation` asks for.  As in
that endpoint the
two branches are the paper's own: where every finite stage of `Θ ∪ {ψ₀…ψₙ}` is satisfiable,
propositional compactness produces the single world the price-floor argument consumes, and
where some stage is already unsatisfiable the criterion holds vacuously.  The base stage
program and the rational market program are read off the inductor instance itself.  The
condition carries a harmless `⊤` tail from `bigAnd`'s empty-fold terminator.
Kind `C` (composition of the two branches); hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_growing_ofSequence
    (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    IsLogicalInductor
      (conditionedHistory P (fun n => sentenceConjunction ((List.range (n + 1)).map ψ)))
      (DP.union (prefixProcess ψ)) := by
  obtain ⟨base⟩ := hLI.processComputable.nonemptyComputation
  obtain ⟨market⟩ := hLI.marketComputable.nonemptyComputation
  let C := prefixConditioningPresentation base ψ hψ
  by_cases hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (prefixProcess ψ)).D n)
  · obtain ⟨w, hw⟩ := (DP.union (prefixProcess ψ)).exists_consistentWithTheory hsat
    exact lic_conditioned_eventual_ofMarketComputation P DP (prefixProcess ψ) C market
      (fun n => ⟨w, ((PCWorld.consistentWith_union_iff w DP (prefixProcess ψ) n).mp (hw n)).1,
        fun i => (C.holds_condition i w).2
          ((PCWorld.consistentWith_union_iff w DP (prefixProcess ψ) i).mp (hw i)).2⟩)
  · push Not at hsat
    obtain ⟨N, hN⟩ := hsat
    exact isLogicalInductor_of_stage_unsatisfiable _ _
      ((conditionedMarketComputation market C.condition C.condition_codes).toComputable)
      C.combined_computable (N := N) hN

/-! ## Non-vacuity of the e.c.-sequence quantifier -/

/-- **Non-vacuity of the arbitrary-e.c.-sequence quantifier.**  A client instantiates
`lic_conditioned_growing_ofSequence` at a genuinely growing sequence — the injective
atom family `i ↦ atom i`, whose prefix conjunctions strictly grow with `n` (they are not
eventually constant, unlike `growingConditionProcess`) — with the write-out certificate
discharged by `machineSentenceCodes_atom`.  This witnesses that the endpoint's hypothesis
class `MachineSentenceCodes ψ` is inhabited by a non-degenerate `ψ`, so the paper's raw
e.c.-sequence quantifier is reached with content. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP] :
    IsLogicalInductor
      (conditionedHistory P
        (fun n => sentenceConjunction
          ((List.range (n + 1)).map (fun i => (LO.Propositional.Formula.atom i : Sentence)))))
      (DP.union (prefixProcess (fun i => (LO.Propositional.Formula.atom i : Sentence)))) :=
  lic_conditioned_growing_ofSequence P DP
    (fun i => (LO.Propositional.Formula.atom i : Sentence)) machineSentenceCodes_atom

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
  haveI := paperLIA T
  lic_conditioned (liaHistory (paperDP T)) (paperDP T) extra C compiler

/-- **Fixed-sentence `thm:scon` transfer over the constructed `LIA`, at the paper's own
quantifier**, with **no** remaining premise — the paper's statement exactly: conditioning
the constructed inductor on any single sentence `ψ` yields a market no trader in ordinary
machine polynomial time exploits, over `Θ ∪ {ψ}`, including the degenerate case where
`Θ ∪ {ψ}` is unsatisfiable at some stage (there the criterion holds vacuously; see
`isLogicalInductor_of_stage_unsatisfiable`).
Kind `C`; hypotheses `(a)`.
Paper node: `thm:scon` -/
theorem lic_conditioned_fixed_unconditional
    (T : ArithmeticTheory) [T.Δ₁]
    (ψ : Sentence) :
    IsLogicalInductor
      (conditionedHistory (liaHistory (paperDP T)) (fun _ => ψ))
      ((paperDP T).adjoinSentence ψ) := by
  haveI : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_is_logical_inductor (paperDP T) (paperDP_computable T)
  exact ConditioningCompile.lic_conditioned_fixed
    (liaHistory (paperDP T)) (paperDP T) ψ

/-- **Growing finite-prefix `thm:scon` over the constructed `LIA`, at the paper's own
quantifier**, with **no** remaining premise.  The extra process supplies its compact
condition-code computation; the consistent case is carried by propositional compactness
(`DeductiveProcess.exists_consistentWithTheory`, which turns per-stage satisfiability of
`Θ ∪ {ψ₁…ψₙ}` into one world satisfying the whole growing theory, as the price-floor
argument needs) and the degenerate case by
`isLogicalInductor_of_stage_unsatisfiable`.
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
  haveI : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_is_logical_inductor (paperDP T) (paperDP_computable T)
  exact ConditioningCompile.lic_conditioned_growing_ofProcessComputation
    (liaHistory (paperDP T)) (paperDP T) extra more

/-! ## The growing form, non-vacuously -/

/-- The atom prefix stages grow strictly at every day: day `n + 1` adjoins `atom (n + 1)`,
which no earlier day names. -/
private lemma atomPrefixProcess_ssubset (n : ℕ) :
    (prefixProcess fun i => (Formula.atom i : Sentence)).D n ⊂
      (prefixProcess fun i => (Formula.atom i : Sentence)).D (n + 1) := by
  refine Finset.ssubset_iff_of_subset (Finset.le_iff_subset.mp ((prefixProcess _).mono n)) |>.mpr
    ⟨(Formula.atom (n + 1) : Sentence), ?_, ?_⟩
  · simp [prefixProcess]
  · simp [prefixProcess]

/-- No atom prefix condition is the empty conjunction: the all-false world falsifies
`atom 0`, which every prefix condition names. -/
private lemma atomPrefixCondition_ne_top (n : ℕ) :
    sentenceConjunction ((List.range (n + 1)).map fun i => (Formula.atom i : Sentence))
      ≠ ⊤ := by
  intro h
  have hv : PCWorld.Holds (fun _ => False)
      (sentenceConjunction ((List.range (n + 1)).map fun i => (Formula.atom i : Sentence))) := by
    rw [h]; exact PCWorld.holds_top _
  rw [holds_sentenceConjunction] at hv
  have h0 : PCWorld.Holds (fun _ => False) (Formula.atom 0 : Sentence) :=
    hv _ (List.mem_map_of_mem (List.mem_range.mpr (Nat.succ_pos n)))
  exact (PCWorld.holds_atom _ 0).mp h0

/-- The atom prefix condition changes at **every** day: the world holding exactly
`atom 0, …, atom n` satisfies day `n`'s condition and falsifies day `n + 1`'s. -/
private lemma atomPrefixCondition_ne_succ (n : ℕ) :
    sentenceConjunction ((List.range (n + 1)).map fun i => (Formula.atom i : Sentence)) ≠
      sentenceConjunction ((List.range (n + 2)).map fun i => (Formula.atom i : Sentence)) := by
  intro h
  have hle : PCWorld.Holds (fun i => i ≤ n)
      (sentenceConjunction ((List.range (n + 1)).map fun i => (Formula.atom i : Sentence))) := by
    rw [holds_sentenceConjunction]
    intro ψ hψ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hψ
    exact (PCWorld.holds_atom _ i).mpr (Nat.lt_succ_iff.mp (List.mem_range.mp hi))
  rw [h, holds_sentenceConjunction] at hle
  have hlast : PCWorld.Holds (fun i => i ≤ n) (Formula.atom (n + 1) : Sentence) :=
    hle _ (List.mem_map_of_mem (List.mem_range.mpr (by omega)))
  have hbad : n + 1 ≤ n := (PCWorld.holds_atom _ (n + 1)).mp hlast
  omega

/-- **The growing form of `thm:scon` doing visible work.**  Instantiated at the prefix
process of the injective atom family `i ↦ atom i`: the adjoined stages grow strictly at
*every* day, the day-`n` condition `atom 0 ⋏ ⋯ ⋏ atom n` is never the empty conjunction `⊤`,
and it differs from day `n + 1`'s at every `n`.  The degenerate inhabitant of the compact
interface — the constantly empty process — is deliberately **not** used here: it would make
`DP.union extra = DP` and the conclusion a restatement of the unconditioned theorem.

The condition is written in index order through `ConditioningPresentation.condition`, which
is what makes growth at every day poly-writable.  The compact
`deductiveStageCondition` route cannot reach it — a `Finset` stage erases the index order
its emitter needs — so that interface's own non-degenerate inhabitant,
`growingCompactConditioningProcessComputation`, changes exactly once; the `example` below
exercises it.

Kind `N+` non-vacuity witness.
Paper node: `thm:scon` -/
lemma exists_growing_conditioned_inductor
    (T : ArithmeticTheory) [T.Δ₁] :
    ∃ (ψ : ℕ → Sentence) (extra : DeductiveProcess),
      (∀ n, extra.D n ⊂ extra.D (n + 1)) ∧
      (∀ n, sentenceConjunction ((List.range (n + 1)).map ψ) ≠ ⊤) ∧
      (∀ n, sentenceConjunction ((List.range (n + 1)).map ψ) ≠
        sentenceConjunction ((List.range (n + 2)).map ψ)) ∧
      IsLogicalInductor
        (conditionedHistory (liaHistory (paperDP T))
          (fun n => sentenceConjunction ((List.range (n + 1)).map ψ)))
        ((paperDP T).union extra) := by
  haveI : IsLogicalInductor (liaHistory (paperDP T)) (paperDP T) :=
    LIA_is_logical_inductor (paperDP T) (paperDP_computable T)
  exact ⟨fun i => (Formula.atom i : Sentence), prefixProcess _,
    atomPrefixProcess_ssubset, atomPrefixCondition_ne_top, atomPrefixCondition_ne_succ,
    ConditioningCompile.lic_conditioned_growing_ofSequence _ (paperDP T) _
      machineSentenceCodes_atom⟩

/-- The compact `deductiveStageCondition` interface is inhabited non-degenerately too:
`growingConditionProcess`'s condition is never `⊤` and does change, once. -/
example (T : ArithmeticTheory) [T.Δ₁] :
    (∀ n, deductiveStageCondition (growingConditionProcess.D n) ≠ ⊤) ∧
      deductiveStageCondition (growingConditionProcess.D 0) ≠
        deductiveStageCondition (growingConditionProcess.D 1) ∧
      IsLogicalInductor
        (conditionedHistory (liaHistory (paperDP T))
          (fun n => deductiveStageCondition (growingConditionProcess.D n)))
        ((paperDP T).union growingConditionProcess) :=
  ⟨deductiveStageCondition_growing_ne_top, deductiveStageCondition_growing_ne,
    lic_conditioned_growing_unconditional T growingConditionProcess
      growingCompactConditioningProcessComputation⟩

end LogicalInduction
