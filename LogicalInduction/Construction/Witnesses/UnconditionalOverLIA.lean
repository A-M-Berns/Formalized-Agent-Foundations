import LogicalInduction.Construction.Witnesses.PaperTheoryDP
import LogicalInduction.Construction.Witnesses.BitPrefixSyntax
import LogicalInduction.Construction.Witnesses.ConditioningCompiler
import LogicalInduction.Construction.Witnesses.RpnConditioning
import LogicalInduction.Construction.Machine.CondEndpoints
import LogicalInduction.Construction.Witnesses.StrictSeparators
import LogicalInduction.Construction.Witnesses.UniversalDovetailer

/-!
# Unconditional instantiations over the constructed `LIA` — semimeasure & conditioning

Companion to `ComputationDP.lean` (which instantiates the meta-learning and self-reference
endpoints over the provability process `paperDP`).  Here two further property families are
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

The prefix-sentence presentation is the constructed `ordinaryBitPrefixSentences`, whose
token-metered naming certificate is discharged by `ordinaryBitPrefixCodes`.
Paper node: `thm:dus` -/
theorem lic_domination_universalSemimeasure_unconditional
    {M : LowerSemicomputableContinuousSemimeasure}
    (A : DUSApproximationPresentation M ordinaryBitPrefixSentences)
    (emit : DUSThresholdEmission A) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * M.mass σ ≤ limitingBelief (liaHistory emptyBitDeductiveProcess)
        (bitPrefixSentence ordinaryIndependentBitAtoms.atom σ) :=
  haveI : IsLogicalInductor (liaHistory emptyBitDeductiveProcess) emptyBitDeductiveProcess :=
    LIA_is_logical_inductor emptyBitDeductiveProcess emptyBitDeductiveProcess_computable
  lic_domination_universalSemimeasure_ofIndependentAtoms ordinaryIndependentBitAtoms
    ordinaryBitPrefixCodes A emit
    (liaHistory emptyBitDeductiveProcess)
    emptyBitDeductiveProcess_hworld

/-- **`thm:dus` over the constructed dovetail, with no semimeasure input.**  `M` is
`Construction/Witnesses/UniversalDovetailer.lean`'s explicit dovetail `M*`, and both the
from-below approximation and its threshold emission are discharged there by the
self-clamped stage table, and the prefix-sentence naming certificate is discharged by
`ordinaryBitPrefixCodes`, so **no caller input remains**.
Paper node: `thm:dus` -/
theorem lic_domination_dovetailSemimeasure_unconditional :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * Dovetail.universalMass σ ≤ limitingBelief (liaHistory emptyBitDeductiveProcess)
        (bitPrefixSentence ordinaryIndependentBitAtoms.atom σ) :=
  lic_domination_universalSemimeasure_unconditional
    (Dovetail.dusApproximationPresentation ordinaryBitPrefixSentences (fun _ ↦ rfl))
    (Dovetail.dusThresholdEmission _ _)

/-- **The paper's actual `thm:dus` conclusion, unconditional on the semimeasure side.**
Because the dovetail is *universal*, the constructed market's limiting beliefs dominate
**every** lower-semicomputable continuous semimeasure, with a constant assembled from the
dovetail weight of that semimeasure's own approximation program.

Paper node: `thm:dus` -/
theorem lic_domination_everyLowerSemicomputable_unconditional
    (ν : LowerSemicomputableContinuousSemimeasure) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * ν.mass σ ≤ limitingBelief (liaHistory emptyBitDeductiveProcess)
        (bitPrefixSentence ordinaryIndependentBitAtoms.atom σ) := by
  obtain ⟨K, hK, hbelief⟩ := lic_domination_dovetailSemimeasure_unconditional
  obtain ⟨c, hc, hdom⟩ := Dovetail.universalMass_dominates ν
  refine ⟨K * c, mul_pos hK hc, fun σ ↦ ?_⟩
  calc K * c * ν.mass σ = K * (c * ν.mass σ) := by ring
    _ ≤ K * Dovetail.universalMass σ := by
        exact mul_le_mul_of_nonneg_left (hdom σ) hK.le
    _ ≤ _ := hbelief σ

/-! ### The non-degenerate witness: bit atoms over the paper's own deductive process

`ordinaryIndependentBitAtoms` inhabits the premise, but over the constantly empty process,
so its `realizable` field is discharged vacuously.  This section supplies the substantive
witness: the same literal conjunctions, over an atom family realizable against every stage
of `paperDP T` — the process the construction actually runs on, whose stages carry the
established theorem stream *and* the universal theorem stream of `T`, and are therefore
saying something.

The only thing that has to be arranged is **freshness**.  `paperDP T` is
`(theoremDP T).union (paperTheoryDP T)`; its stage sentences are built from event atoms
(payload tags `0`–`2`) and paper-prime atoms (`paperPrimeTag = 5`).  Raw atom indices would
collide, so the bit atoms are tagged with a reserved tag, `bitAtomTag = 7` (tags `3`, `4`
and `6` are reserved elsewhere, by `productTag`, `semanticPrimeTag` and `oldLanguageTag`).
Disjointness then lets an arbitrary bit assignment be *grafted onto* any stage-consistent
world without disturbing its verdict on the stage.

Tagging costs nothing on the naming side: the write-out emitter above is stated for an
arbitrary `PolyFueled` name map, and `fun k ↦ Nat.pair bitAtomTag k` is one.
-/

section PaperBitAtoms

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable (T : ArithmeticTheory)

/-- The atom tag reserved for the `thm:dus` bit atoms, chosen fresh for `paperDP`. -/
def bitAtomTag : ℕ := 7

/-- The `thm:dus` bit atom family over the paper's process: ordinary propositional atoms,
carried at a reserved tag so they cannot collide with the process's own vocabulary. -/
def paperBitAtom (k : ℕ) : Sentence := Formula.atom (Nat.pair bitAtomTag k)

/-- The established event vocabulary does not use the reserved bit tag: every atom of an
`eventAtom` is a computation claim (payload tags `0`–`1`) or a quotation claim (tag `2`). -/
lemma eventAtom_atomCodes_ne_bitAtomTag (e : ℕ) :
    ∀ a ∈ sentenceAtomCodes (eventAtom e), a.unpair.1 ≠ bitAtomTag := by
  intro a ha
  rcases h : e.unpair.1 with _ | _ | _ | _ | _ | _ | m
  all_goals simp only [eventAtom, h, sentenceAtomCodes_neg] at ha
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, bitAtomTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, haltingClaim,
        ComputationClaimKind.godelCode, bitAtomTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, bitAtomTag] at hc
  · exact fun hc => by
      simp [sentenceAtomCodes_computationClaimSentence _ a ha, boundedHaltingClaim,
        ComputationClaimKind.godelCode, bitAtomTag] at hc
  · exact fun hc => by simp [sentenceAtomCodes_quoteAtom _ a ha, bitAtomTag] at hc
  · exact fun hc => by simp [sentenceAtomCodes_quoteAtom _ a ha, bitAtomTag] at hc
  · simp at ha

/-- **The paper's process never commits to a bit atom.**  Both halves of the union are
covered: the literal stream is an image of `eventAtom`, and every atom of the universal
theorem stream carries `paperPrimeTag`. -/
lemma paperDP_atomCodes_ne_bitAtomTag [T.Δ₁] {k : ℕ} {φ : Sentence}
    (hφ : φ ∈ (paperDP T).D k) :
    ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ bitAtomTag := by
  classical
  rw [paperDP, DeductiveProcess.union_stage, Finset.mem_union] at hφ
  rcases hφ with h | h
  · simp only [theoremDP, theoremStage, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at h
    obtain ⟨e, -, rfl⟩ := h
    exact eventAtom_atomCodes_ne_bitAtomTag e
  · intro a ha hc
    rw [paperTheoryDP_atom_tag T h ha] at hc
    simp [paperPrimeTag, bitAtomTag] at hc

/-- Graft a bit assignment onto a world at the reserved tag, leaving every other atom — in
particular every atom `paperDP` commits to — read exactly as before. -/
def bitExtensionWorld (v₀ : PCWorld) (f : ℕ → Bool) : PCWorld :=
  fun a ↦ if a.unpair.1 = bitAtomTag then f a.unpair.2 = true else v₀ a

lemma bitExtensionWorld_agree (v₀ : PCWorld) (f : ℕ → Bool) {a : ℕ}
    (ha : a.unpair.1 ≠ bitAtomTag) : bitExtensionWorld v₀ f a ↔ v₀ a := by
  simp only [bitExtensionWorld, if_neg ha]

/-- Sentences free of the reserved tag are read the same way by the extension. -/
lemma bitExtensionWorld_holds_iff (v₀ : PCWorld) (f : ℕ → Bool) {φ : Sentence}
    (hφ : ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ bitAtomTag) :
    (bitExtensionWorld v₀ f).Holds φ ↔ v₀.Holds φ :=
  PCWorld.holds_congr_atomCodes φ fun a ha ↦ bitExtensionWorld_agree v₀ f (hφ a ha)

lemma bitExtensionWorld_holds_paperBitAtom (v₀ : PCWorld) (f : ℕ → Bool) (k : ℕ) :
    (bitExtensionWorld v₀ f).Holds (paperBitAtom k) ↔ f k = true := by
  show (bitExtensionWorld v₀ f) (Nat.pair bitAtomTag k) ↔ _
  simp only [bitExtensionWorld, Nat.unpair_pair, if_pos]

/-- **The `thm:dus` independence premise, non-vacuously.**  Every bit assignment is
realizable against every stage of the paper's own deductive process: take any world
consistent with the stage (`paperDP_hworld`, from consistency of `T`) and overwrite it at
the reserved tag.  Unlike `ordinaryIndependentBitAtoms`, the stages here are genuinely
non-empty, so `realizable` is a substantive compatibility claim rather than a vacuous one.
Paper node: `thm:dus` -/
noncomputable def paperIndependentBitAtoms [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    IndependentBitAtoms (paperDP T) where
  atom := paperBitAtom
  realizable := by
    intro n f
    obtain ⟨v₀, hv₀⟩ := paperDP_hworld T n
    refine ⟨bitExtensionWorld v₀ f, fun φ hφ ↦ ?_, fun k ↦ ?_⟩
    · exact (bitExtensionWorld_holds_iff v₀ f
        (paperDP_atomCodes_ne_bitAtomTag T hφ)).mpr (hv₀ φ hφ)
    · exact bitExtensionWorld_holds_paperBitAtom v₀ f k

/-- **The tagged prefix conjunctions are efficiently nameable** (`dd:ec`, write-out
metered).  The reserved tag is applied by a `PolyFueled` name map, so the emitter is the
same one that serves the untagged family: one `Nat.pair` per token index.
Paper node: `thm:dus` -/
lemma paperBitPrefixCodes :
    BigSentenceCodes (fun i ↦ bitPrefixSentence paperBitAtom (bitStringEnumeration i)) :=
  BitChain.bigSentenceCodes_bitPrefixSentence
    ((PolyFueled.const bitAtomTag).pair PolyFueled.id)

/-- **The `thm:dus` / `thm:strict` presentation over the paper's own deductive process.**
Both halves are substantive here: `prefix_codes` is the write-out emitter, and
`realizable` is grafting onto a genuinely constrained stage rather than the vacuous
discharge of `ordinaryBitPrefixSentences`.
Paper node: `thm:dus` -/
noncomputable def paperBitPrefixSentences [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    BitPrefixSentences (paperDP T) :=
  bitPrefixSentencesOfIndependentAtoms (paperIndependentBitAtoms T) paperBitPrefixCodes

end PaperBitAtoms

section PaperDomination

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

variable (T : ArithmeticTheory)

/-- **Domination of the universal semimeasure at the paper's own market.**  The independence
premise and the naming certificate are both discharged concretely — over `paperDP T`, whose
stages are non-empty — so the only remaining inputs are the semimeasure's from-below
approximation and its threshold emission, exactly as in the abstract endpoint.
Paper node: `thm:dus` -/
theorem lic_domination_universalSemimeasure_paperDP
    [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]
    {M : LowerSemicomputableContinuousSemimeasure}
    (A : DUSApproximationPresentation M
      (bitPrefixSentencesOfIndependentAtoms (paperIndependentBitAtoms T) paperBitPrefixCodes))
    (emit : DUSThresholdEmission A) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * M.mass σ ≤ limitingBelief (liaHistory (paperDP T)) (bitPrefixSentence paperBitAtom σ) :=
  haveI := paperLIA T
  lic_domination_universalSemimeasure_ofIndependentAtoms
    (paperIndependentBitAtoms T) paperBitPrefixCodes A emit
    (liaHistory (paperDP T)) (paperDP_hworld T)

end PaperDomination

/-! ### The same, over the paper's own market

The endpoints above run over `emptyBitDeductiveProcess`, where the atoms' independence is
vacuous.  The following two repeat them over `paperDP T`, whose stages are non-empty, so the
independence premise is discharged substantively (`paperIndependentBitAtoms`). -/

section PaperDovetail

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **`thm:dus` over the constructed dovetail at the paper's market, with no caller input.**
The `paperDP` analogue of `lic_domination_dovetailSemimeasure_unconditional`: `M` is the
explicit dovetail `M*`, whose from-below approximation and threshold emission are discharged
in `Construction/Witnesses/UniversalDovetailer.lean`, and the independence and naming
premises are discharged by `paperIndependentBitAtoms` / `paperBitPrefixCodes` over a process
whose stages are non-empty.  **No caller input remains, and no premise is vacuous.**
Paper node: `thm:dus` -/
theorem lic_domination_dovetailSemimeasure_paperDP :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * Dovetail.universalMass σ ≤ limitingBelief (liaHistory (paperDP T))
        (bitPrefixSentence paperBitAtom σ) :=
  lic_domination_universalSemimeasure_paperDP T
    (Dovetail.dusApproximationPresentation _ (fun _ ↦ rfl))
    (Dovetail.dusThresholdEmission _ _)

/-- **The paper's actual `thm:dus` conclusion at the paper's own market.**  Universality of
the dovetail carries domination to *every* lower-semicomputable continuous semimeasure, over
a deductive process with non-empty stages.
Paper node: `thm:dus` -/
theorem lic_domination_everyLowerSemicomputable_paperDP
    (ν : LowerSemicomputableContinuousSemimeasure) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ,
      K * ν.mass σ ≤ limitingBelief (liaHistory (paperDP T))
        (bitPrefixSentence paperBitAtom σ) := by
  obtain ⟨K, hK, hbelief⟩ := lic_domination_dovetailSemimeasure_paperDP T
  obtain ⟨c, hc, hdom⟩ := Dovetail.universalMass_dominates ν
  refine ⟨K * c, mul_pos hK hc, fun σ ↦ ?_⟩
  calc K * c * ν.mass σ = K * (c * ν.mass σ) := by ring
    _ ≤ K * Dovetail.universalMass σ := by
        exact mul_le_mul_of_nonneg_left (hdom σ) hK.le
    _ ≤ _ := hbelief σ

end PaperDovetail

/-- **`thm:strict` over the constructed dovetail, with no caller input.**  The separator
argument is `strictSeparatorPresentationOfKleene`, its atom-code hypothesis is
`ordinaryAtom_code_computable`, and the prefix-sentence presentation is the constructed
`ordinaryBitPrefixSentences` — so the constructed market's limiting beliefs *strictly*
dominate the dovetail: no constant multiple of the universal mass bounds them.
Paper node: `thm:strict` -/
theorem lic_strict_domination_universalSemimeasure_unconditional :
    ∀ C : ℝ, 0 < C → ∃ σ : List Bool,
      limitingBelief (liaHistory emptyBitDeductiveProcess)
        (bitPrefixSentence ordinaryIndependentBitAtoms.atom σ) >
          C * Dovetail.universalSemimeasure.mass σ :=
  haveI : IsLogicalInductor (liaHistory emptyBitDeductiveProcess) emptyBitDeductiveProcess :=
    LIA_is_logical_inductor emptyBitDeductiveProcess emptyBitDeductiveProcess_computable
  lic_strict_domination_universalSemimeasure_ofAtomCodes
    (M := Dovetail.universalSemimeasure) (B := ordinaryBitPrefixSentences)
    ordinaryAtom_code_computable (liaHistory emptyBitDeductiveProcess)

/-! ## Conditioning over the constructed `LIA` -/

/-- Compatibility wrapper for a caller-supplied conditioning compiler.  The paper-facing
fixed and growing forms below construct the repaired compiler internally.
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

#print axioms lic_domination_universalSemimeasure_unconditional
#print axioms lic_domination_dovetailSemimeasure_unconditional
#print axioms lic_domination_everyLowerSemicomputable_unconditional
#print axioms lic_strict_domination_universalSemimeasure_unconditional
#print axioms lic_conditioned_ofCompiler_unconditional
#print axioms lic_conditioned_fixed_unconditional
#print axioms lic_conditioned_growing_unconditional
#print axioms lic_conditioned_fixed_machine_unconditional
#print axioms lic_conditioned_growing_machine_unconditional
#print axioms exists_growing_conditioned_machine_inductor

#print axioms eventAtom_atomCodes_ne_bitAtomTag
#print axioms paperDP_atomCodes_ne_bitAtomTag
#print axioms paperIndependentBitAtoms
#print axioms paperBitPrefixCodes
#print axioms paperBitPrefixSentences
#print axioms lic_domination_universalSemimeasure_paperDP
#print axioms lic_domination_dovetailSemimeasure_paperDP
#print axioms lic_domination_everyLowerSemicomputable_paperDP

end LogicalInduction
