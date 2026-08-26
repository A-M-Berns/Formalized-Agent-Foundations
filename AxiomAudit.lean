/-
# Axiom audit — the checked public-surface inventory

A standalone build target, deliberately outside the `LogicalInduction` library: the
library carries the mathematics, this target carries the check. This file is the endpoint
inventory: every declaration listed below is public trust surface — the table of contents
for the human statement read-through. Anything *not* listed here is internal and may be
renamed, moved, or inlined freely; changes to a listed statement are surface changes and
must be flagged.

The build fails if any listed endpoint acquires an axiom beyond `propext`,
`Classical.choice`, `Quot.sound` (in particular `sorryAx`), or ceases to exist.

Two independent claims, checked separately — do not conflate them:
  * **axiom cleanliness** (this build): every *listed* endpoint is `sorry`-free and uses no
    stray axioms. It says nothing about whether the list is complete.
  * **surface completeness** (`scripts/check_endpoint_coverage.py`): every paper `\label`
    cited in a `Paper node:` annotation has at least one endpoint *in this list*. It says
    nothing about axioms, nor about whether the listed endpoint is the strongest form of
    the theorem (that is the human statement read-through's job — see below).
Green here + green there = "the enumerated surface is clean and covers every annotated
paper node", not "the formalization is faithful". Faithfulness is the read-through.

Scope is the whole repository, and it is now **strictly clean throughout**: the former
sole intentional axiom `glFixedPoint_thm42` (GL fixed-point existence) has been discharged
by the `ProvabilityLogic/` development (a vendored subset of
FormalizedFormalLogic/ProvabilityLogic, pinned in `lakefile.lean`; see
`ModalAgents/FixedPoint.lean`),
so every ModalAgents endpoint — including the cooperation results that rest on the GL fixed
point — is asserted under `#assert_axioms_clean`. (`#assert_axioms_clean_except` is retained
as a reusable tool but is no longer needed.)

## Tier-2 membership, annotations, and regeneration

**Tier 2 (`#assert_fields`)** freezes boundary *structures*: a structure's fields are
the hypotheses its endpoints consume, so adding or removing one is premise smuggling.
Membership is mechanical, not taste: a structure is Tier 2 iff it appears in the type
of a Tier-1 endpoint, transitively through structure fields — computed by
`SurfaceProbe.lean`'s `#surface_types`. Transitive closure is the right depth because
reading an endpoint means understanding every structure its hypotheses mention.

**Annotation convention**: the last line of every inventory member's docstring is
`Paper node: ` followed by backticked labels taken verbatim from `\label{…}` in
`LogicalInduction/notes/1609.03543v5-main.tex`, comma-separated — no ranges, no glosses, so every label
is greppable. Members realizing the efficient-computability obligation without a node
of their own carry `def:ec`; graded-strength endpoints share their theorem's node.

**Regeneration** after a deliberate surface change: rerun `#surface_types` (seeded
with the current `#assert_axioms_clean` names) and `#dump_fields` in
`SurfaceProbe.lean`, update the `#assert_fields` block and affected `Paper node:`
fields here, then run `scripts/check-paper-nodes.sh`.
-/
import Lean.Util.CollectAxioms
import LogicalInduction.Properties
import LogicalInduction.Construction
import ModalAgents.Cooperation
import ModalAgents.Behavioral
import ModalAgents.FixedPoint
import ModalAgents.Arithmetic
import ModalAgents.ArithmeticAgent
import CartesianFrames.Examples
import CartesianFrames.Worlds
import CartesianFrames.Subagent
import CartesianFrames.AdditiveMultiplicative
import CartesianFrames.Operations
import CartesianFrames.Categorical
import FiniteFactoredSets
import Condensation
import FactoredSpaces

open Lean Elab Command in
/-- Fail elaboration unless every named declaration exists and depends on no axioms
beyond `propext`, `Classical.choice`, and `Quot.sound`. -/
elab "#assert_axioms_clean " ids:ident+ : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← Lean.collectAxioms name
    let bad := axioms.filter (! [``propext, ``Classical.choice, ``Quot.sound].contains ·)
    unless bad.isEmpty do
      throwErrorAt id "'{name}' depends on disallowed axioms: {bad.toList}"

open Lean Elab Command in
/-- Like `#assert_axioms_clean`, but additionally permits the one named axiom `extra`
(for the intentionally axiomatized `ModalAgents/` fixed-point fact). Still fails on `sorryAx`
or any other axiom. -/
elab "#assert_axioms_clean_except " extra:ident ids:ident+ : command => do
  let extraName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo extra
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← Lean.collectAxioms name
    let allowed := [``propext, ``Classical.choice, ``Quot.sound, extraName]
    let bad := axioms.filter (! allowed.contains ·)
    unless bad.isEmpty do
      throwErrorAt id "'{name}' depends on disallowed axioms: {bad.toList}"

open Lean Elab Command in
/-- Fail elaboration unless `struct` is a structure whose field-name set is exactly the
listed idents. Freezes the field *names* of a boundary structure — adding or removing a
field fails the build — but NOT their types: a field's type can change without failing
this check (it has, benignly: `mesh_poly`'s index moved during the precision reindex).
A type change on a frozen structure is still a surface change and must be flagged in a
comment here, as the `BitPrefixSentences.prefix_codes` note below does. Order-insensitive. -/
elab "#assert_fields " struct:ident fields:ident* : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo struct
  unless Lean.isStructure (← getEnv) name do
    throwErrorAt struct "'{name}' is not a structure"
  let actual := ((Lean.getStructureFields (← getEnv) name).map (·.toString)).qsort (· < ·)
  let expected := (fields.map (·.getId.toString)).qsort (· < ·)
  unless actual.toList == expected.toList do
    throwErrorAt struct
      "'{name}' fields changed.\n  expected: {expected.toList}\n  actual:   {actual.toList}"

namespace LogicalInduction

open ConditioningCompile FeedbackTruth FeedbackEmission PrefixPatchCompile

/-! ## Existence (`thm:li`) -/

#assert_axioms_clean exists_logical_inductor LIA_is_logical_inductor
  exists_computable_beliefSequence_logical_inductor
  exists_machine_logical_inductor LIA_isMachineLogicalInductor

-- The canonical trader universe is `MachineEfficientTrader` — ordinary machine
-- polynomial time, through `Complexity.FP`. The enumeration is sound and covers the whole
-- class, and the fuel calculus's certificates land inside it.
#assert_axioms_clean
  trading_firm_dominance exists_enumeratedTrader_eq enumeratedTrader_machineEfficient
  enumeratedOutput_mem_FP EfficientlyComputable.toMachine
  lia_no_machine_trader_exploits

/-! ## Property tail, conditional on `[IsLogicalInductor P DP]` -/

-- Properties/Coherence.lean
#assert_axioms_clean
  lic_disprovable_tendsto_zero lic_excl_gap_tendsto_zero lic_limit_additive
  lic_price_convergesTo

-- Properties/LimitCoherence.lean
#assert_axioms_clean lic_limitCoherence

-- Properties/ProvabilityInduction.lean, Properties/AffineCoherence.lean
-- Tier note: `lic_provind` / `lic_provind_true` / `lic_provind_false` are the
-- paper-facing `thm:provind` (theorems may appear arbitrarily late in the process).
-- `lic_deducible_*` and `lic_provind_seq` are retained FRAGMENTS whose membership
-- hypotheses (`φ ∈ D n` at every / its own index) are stronger than the paper's —
-- do not credit them as `thm:provind`.
#assert_axioms_clean
  lic_deducible_eventually_ge lic_deducible_price_near_one lic_deducible_tendsto_one
  lic_provind_seq lic_provind lic_provind_true lic_provind_false

-- Properties/TimelyLearning.lean, Properties/AffinePersistence.lean
#assert_axioms_clean
  lic_preemptive_learning lic_persistence_of_knowledge lic_persistence_of_knowledge_lower
  lic_persistence_of_knowledge_upper lic_centered_persistence lic_limitingBelief_tendsto

-- Properties/AffineCoherence.lean, AffinePreemptiveLearning.lean, AffinePersistence.lean:
-- the paper-facing analytic affine capstones (`thm:affcoh`, `thm:affpolymax`, `thm:peraffkno`)
-- and all three comparison forms of `thm:affprovind`.
-- Tier note: `thm:affprovind` is the affine statement — a bounded combination sequence and a
-- real bound `b`, in `≥`/`≤`/`=` forms.  It is these three, NOT `lic_provind_true`/`_false`,
-- which are the sentence-level halves of `thm:provind` (the `k=1`, `b ∈ {0,1}` special case).
#assert_axioms_clean
  AffineCombination.PolySequence.affcoh
  AffineCombination.BoundedCombinationSequence.affpolymax
  AffineCombination.PolySequence.peraffkno
  AffineCombination.PolySequence.affine_provind_theory_ge
  AffineCombination.PolySequence.affine_provind_theory_le
  AffineCombination.PolySequence.affine_provind_theory_eq

-- Properties/NonDogmatism.lean, Properties/UniformNonDogmatism.lean
-- Tier note: `lic_nonDogmatism` / `lic_nonDogmatism_dual` are the paper-facing `thm:nd`;
-- `lic_nonDogmatism_weak` is a retained FRAGMENT (its lower bound decays with `n`).
#assert_axioms_clean
  lic_nonDogmatism lic_nonDogmatism_dual lic_nonDogmatism_weak lic_limit_pos
  lic_limit_lt_one lic_uniform_nonDogmatism lic_uniform_nonDogmatism_repeating

-- Properties/OccamBounds.lean, Properties/UniversalSemimeasure.lean
#assert_axioms_clean
  lic_occamBounds lic_occam_lower lic_limitingBelief_add_neg
  lic_domination_universalSemimeasure lic_strict_domination_universalSemimeasure

-- Construction/Witnesses/KraftInequality.lean — the Kraft inequality underlying the
-- prefix-machine complexity bounds.  Proof body autoformalized by Aristotle and
-- kernel-revalidated in-repo; the statement is audited surface, the generated interior
-- has not had a line-by-line human read.
#assert_axioms_clean
  kraft_inequality

-- Construction/Witnesses/PrefixMachine.lean — the concrete self-delimiting sentence code,
-- with both fuel-model emission certificates constructed (no operational input remains).
#assert_axioms_clean
  prefixKraft prefixNegationCompiler
  invalidBit_polyFueled prefixSentenceEnum_polySentenceCodes prefixApprox_polyRatCodes
  lic_occam_lower_ofPrefixMachine lic_occamBounds_ofPrefixMachine

-- Construction/Witnesses/UniversalPrefix.lean (the self-delimiting UNIVERSAL prefix
-- machine).  `dom U` is prefix-free by construction, so the Kraft field
-- needs no hypothesis; `kappaU_le_of_prefixMachine` is the invariance theorem that earns
-- the word "universal"; `uSel_polyRatCodes` builds the polynomial clock (a self-clamped
-- `evaln` selection) on top of the exact stage table, whose own program
-- `uCode` is now CONSTRUCTED (`exists_uCode`, via the bounded search `uMinLen`), so the
-- two endpoints carry no operational input at all.
#assert_axioms_clean
  UPrefix.UHalt_prefixFree UPrefix.UHalt_functional UPrefix.acc_antichain
  UPrefix.kappaU_kraft UPrefix.kappaUNegationCompiler
  UPrefix.kappaU_le_of_prefixMachine UPrefix.kappaStage_eventually_eq
  UPrefix.uMinLen_eq UPrefix.uEmit_prim UPrefix.exists_uCode
  UPrefix.uSel_polyRatCodes UPrefix.universalPrefixPresentation
  UPrefix.universalPrefixThresholdEmission
  UPrefix.lic_occam_lower_ofUniversalPrefix UPrefix.lic_occamBounds_ofUniversalPrefix

-- Properties/Conditioning.lean, Properties/FinitePerturbations.lean
-- Tier note: `isLogicalInductor_of_stage_unsatisfiable` (Framework/Affine.lean) is the
-- degenerate half of `thm:scon` — the criterion over a deductive process one of whose
-- stages has no propositionally consistent world.  It is listed here because it is what
-- lets the `thm:scon` endpoints drop the repo-side joint-consistency hypothesis and match
-- the paper's premise-free statement.  For the growing form the other half of that split is
-- `DeductiveProcess.exists_consistentWithTheory` (Framework/Compactness.lean): propositional
-- compactness over Cantor space, which converts per-stage satisfiability of the union
-- process into the single world the price-floor argument consumes.  It is internal
-- infrastructure, not a paper node, so it is not itself an inventory member; its axiom
-- report is covered transitively by the `thm:scon` endpoints below.
#assert_axioms_clean
  lic_conditioned lic_conditioned_gated lic_conditioned_eventual
  isLogicalInductor_of_stage_unsatisfiable
  lic_iff_of_finitePerturbation
  lic_iff_of_finiteSupportPerturbation machine_lic_iff_of_finiteSupportPerturbation

-- Properties/Pseudorandomness.lean
#assert_axioms_clean
  lic_learning_pseudorandom_frequency lic_learning_pseudorandom_frequency_above
  lic_learning_pseudorandom_frequency_below lic_learning_varied_pseudorandom
  lic_learning_varied_pseudorandom_above lic_learning_varied_pseudorandom_below
  AffineCombination.BoundedCombinationSequence.recunbiasedaff
  AffineCombination.BoundedCombinationSequence.prandaff
  AffineCombination.BoundedCombinationSequence.prandaff_above
  AffineCombination.BoundedCombinationSequence.prandaff_below
  AffineCombination.recurringunbiasedness AffineCombination.simcal
  AffineCombination.lic_not_frequently_positive_feedback_return
  AffineCombination.lic_wub AffineCombination.lic_wubaff

-- Properties/Relationships.lean
#assert_axioms_clean
  lic_imp_eventually_le lic_lex_tendsto_zero lic_learning_exclusive_exhaustive

-- Properties/ExpectationAffine.lean, Properties/Introspection.lean,
-- Properties/SelfTrust.lean
#assert_axioms_clean
  lic_linearity_of_expectation lic_expectation_indicator lic_expectation_provind
  lic_linearity_of_expectation_ofValuesAt lic_expectation_provind_ofValuesAt
  lic_expectation_provind_le lic_expectation_provind_eq
  lic_expect_combination_provind_zero lic_expect_combination_provind_le_ofDetermined
  lic_expect_combination_provind_ge_ofDetermined lic_expect_combination_provind_eq_ofDetermined
  lic_expect_combination_provind_le
  lic_expect_combination_provind_ge
  lic_expect_combination_provind_eq
  lic_linearity_of_expectation_seq
  lic_introspection lic_paradox_resistance lic_expectations_of_probabilities
  lic_iterated_expectations lic_self_trust lic_expected_future_expectations

-- Properties/ExpectationConvergence.lean: Expectations Converge (`thm:ec`).
#assert_axioms_clean LUV.expect_converges

-- Properties/ExpectationProperties.lean: the paper-facing LUV-combination sequence
-- capstones (`thm:exppolymax`, `thm:expcoh`, `thm:perexpkno`, `thm:wubexp`).
#assert_axioms_clean
  LUVCombination.BoundedSequence.mesh_independence
  LUVCombination.BoundedSequence.exppolymax
  LUVCombination.BoundedSequence.expcoh
  LUVCombination.BoundedSequence.perexpkno
  LUVCombination.BoundedSequence.wubexp

-- Construction/Witnesses/LUVExpectationCertified.lean (`dd:luv-arith`): the
-- expectation endpoints whose world-value hypotheses are discharged from arithmetic
-- (`thm:loe`, `thm:expprovind`).  The certified LUV, its derived world-value
-- interfaces (`threshold_holds_iff`, `exactTheoryPresentation_ofArithmetic`), and the
-- process realizing them (`luvArithmeticPresentation`) are internal infrastructure.
#assert_axioms_clean
  ComputableLUV.lic_expectation_provind_arith
  ComputableLUV.lic_expectation_provind_le_arith
  ComputableLUV.lic_expectation_provind_eq_arith
  ComputableLUV.lic_linearity_of_expectation_arith
  ComputableLUV.exppolymax_arith ComputableLUV.wubexp_arith
  ComputableLUV.expcoh_arith ComputableLUV.perexpkno_arith

-- dd:fuel model card (`def:ec`): the fuel certificate's own trust facts — poly-fueled ⟹
-- primrec, the runtime-gcd inhabitation witness, the size-based separation (2^n is not
-- poly-fueled), and the two-sided EF.cost ↔ token-length seam.  The certificate's
-- relation to the paper's class is `EfficientlyComputable.toMachine`, audited above.
#assert_axioms_clean
  PolyFueled.primrec gcdc_polyFueled not_polyFueled_two_pow
  EF.cost_le_serialize_length EF.serialize_length_le_cost
  Strategy.serializeTrades_length_le_cost

-- dd:fuel digit layer (`def:ec`): the digit stream determines the token stream
-- (round-trip + injectivity), and every token-model certificate transfers into the
-- digit-metered class (the inclusion capstone).  The digit model is the
-- metering underneath the collapsed criterion class `EfficientlyComputable`.
#assert_axioms_clean
  undigitize_digitize digitize_injective
  PolySegStream.digitizeStream
  EfficientlyComputableTok.toDigit

-- dd:fuel discharged for dd:luv-arith: the threshold-code and process-computability
-- certificates are proved (gcdc_polyFueled/toLUV_polyThresholdCodes/gridDP_computable),
-- so these endpoints are FULLY unconditional over the constructed LIA — the sole
-- hypothesis is the rational bound/identity on the LUV values.
#assert_axioms_clean
  ComputableLUV.lic_expectation_provind_arith_unconditional
  ComputableLUV.lic_expectation_provind_le_arith_unconditional
  ComputableLUV.lic_expectation_provind_eq_arith_unconditional
  ComputableLUV.lic_linearity_of_expectation_arith_unconditional
  lic_no_expected_net_update lic_no_expected_net_update_conditional
  LUVCombination.BoundedSequence.recurringunbiasednessexp
  LUVCombination.BoundedSequence.prandexp
  LUVCombination.BoundedSequence.prandexp_below
  LUVCombination.BoundedSequence.prandexp_eq

-- Properties/MetaLearning.lean
#assert_axioms_clean
  lic_belief_finitistic_consistency lic_belief_stronger_theory_consistency
  lic_disbelief_inconsistent_theories lic_learns_halting_patterns
  lic_learns_provable_nonhalting_patterns lic_does_not_anticipate_halting

/-! ## Constructed boundary witnesses and their direct criterion consumers

Each block below names the file whose constructions *discharge* an interface the property
tail would otherwise assume, together with the criterion endpoints that consume them. -/

-- Construction/Witnesses/BoundedEvaluation.lean — the bounded-`evaln` compiler, repeated
-- enumeration of a c.e. set, settlement/patient clocks, and the prefix-freeze certificate.
#assert_axioms_clean
  codeEvalnNat_polyFueled
  EfficientRepeatedEnumeration.ofRpn EfficientRepeatedEnumeration.ofCE
  lic_uniform_nonDogmatism_ofCE
  SettlementChecker.ofComputations PatientSettlementClock.ofComputations
  liaFreezeBefore_preserves_ecTok

-- Construction/Witnesses/QuotationAffine.lean — the code-indexed quotation layer
-- (`dd:quote-code`) and the diagonal price fixed point it makes constructible.
#assert_axioms_clean
  diagonalPriceDecisionPart_partrec diagonalPriceDecisionCode_eval
  diagonalPriceQuotePos_iff diagonalPriceQuoteNeg_iff diagonalPriceFixedpoint_spec
  parameterizedDiagonalQuoteCodeOfMarket
  parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint
  lic_introspection_ofCode lic_paradox_resistance_ofDiagonal
  lic_expectations_of_probabilities_ofCode lic_iterated_expectations_ofCode
  lic_self_trust_ofRepresentation lic_expected_future_expectations_ofRepresentation
  lic_no_expected_net_update_ofRepresentation
  lic_no_expected_net_update_conditional_ofRepresentation
  theoremMarketComputation theoremDiagonalQuoteCode
  lic_paradox_resistance_ofDiagonal_unconditional

-- Construction/Witnesses/FeedbackEmission.lean — the emitter that turns a feedback
-- trader schedule into an `def:ec`-certified trade stream.
#assert_axioms_clean
  feedbackTraderEmissionSigns lic_wubaff_ofFeedbackTruth
  boundedCombination_wubaff_ofFeedbackTruth luv_wubexp_ofFeedbackTruth

-- Construction/Witnesses/FeedbackTruth.lean — the delayed-truth bridge: a computation of
-- the feedback value, clocked to the deferral day, feeding the unbiasedness endpoints.
-- `FeedbackTruth.ordinaryFeedbackTruthComputation` is the constructed non-vacuity
-- witness for the delayed-truth premise (constant value stream — see its docstring).
#assert_axioms_clean
  FeedbackTruth.ordinaryFeedbackTruthComputation
  feedbackTruthSequence feedbackTruthSequence_ofDetermined
  lic_wubaff_ofComputation lic_wub_ofComputation
  boundedCombination_wubaff_ofComputation luv_wubexp_ofComputation
  lic_wub_ofComputation_unconditional lic_wubaff_ofComputation_unconditional
  boundedCombination_wubaff_ofComputation_unconditional
  luv_wubexp_ofComputation_unconditional

-- Construction/Witnesses/BitPrefixSyntax.lean — the prefix-sentence family over
-- independent bit atoms, its symbol-metered naming emitter, and the semimeasure-domination
-- endpoint they feed.  `ordinaryBitPrefixSentences` is the **non-vacuity witness** for
-- `BitPrefixSentences`; `not_polySentenceCodes_bitPrefixSentence` records why that field must
-- be metered in symbols rather than in the pair-code value.
#assert_axioms_clean
  not_polySentenceCodes_bitPrefixSentence ordinaryBitPrefixCodes
  bitPrefixSentencesOfIndependentAtoms ordinaryBitPrefixSentences
  lic_domination_universalSemimeasure_ofIndependentAtoms

-- Construction/Witnesses/UniversalDovetailer.lean — the universal continuous semimeasure.
-- The universal continuous semimeasure is fully constructed: the semimeasure laws, the
-- monotone from-below stage table, the explicit domination constant, and the emission
-- program for the stage table (column tabulation).  The *polynomial* clock is now
-- discharged as well: the self-clamped stage table reads the fixed exact emitter under a
-- polynomial `evaln` clock, so both `DUSApproximationPresentation` and
-- `DUSThresholdEmission` are constructed objects.
#assert_axioms_clean
  Dovetail.continuousSemimeasure Dovetail.universalMass_dominates
  Dovetail.exists_universalApprox_code Dovetail.universalSemimeasure
  Dovetail.gridApprox_le_mass Dovetail.gridApprox_tendsto
  Dovetail.isPolyBounded_encode_gridApprox
  Dovetail.dusApprox_tendsto Dovetail.dusApprox_polyRatCodes
  Dovetail.dusApproximationPresentation Dovetail.dusThresholdEmission

-- Construction/Witnesses/StrictSeparators.lean — the recursively inseparable pair and the
-- null stage classes that make the strict-domination separator presentation constructible.
-- The separator presentation is fully constructed: Kleene's pair is recursively
-- inseparable, the constraint theory's enumerator is built from the atom codes, and the
-- stage classes are null (`separatorClass_mass_tendsto_zero`, the Kučera–Demuth argument)
-- rather than assumed.  `strictSeparatorPresentationOfKleene`'s only input is
-- computability of the atom Gödel codes, itself proved for the repo's atoms.
#assert_axioms_clean
  kleene_recursively_inseparable no_ce_null_prefix_family
  separatorClass_mass_tendsto_zero strictSeparatorPresentationOfKleene
  ordinaryAtom_code_computable

-- Construction/Witnesses/ConditioningPresentation.lean — the conditioning presentation
-- (condition sentences plus their codes) built from the process computations.
#assert_axioms_clean
  conditioningPresentationOfComputations fixedConditioningPresentation
  lic_conditioned_gated_ofComputations

-- Construction/Witnesses/ConditioningCompiler.lean — the eventual price floor the
-- conditioning translation needs.  (The `def:ec`-preserving translations themselves are
-- the `_ecRpn` endpoints below, at the criterion's own class.)
#assert_axioms_clean
  exists_eventual_condition_price_floor
  eventualConditioningFloorOfJointConsistency

-- Construction/Witnesses/DigitConditioning.lean — the conditioning translation in the
-- digit metering model: guarded compilers, guard honesty, and the digit-to-digit
-- preservation results.
#assert_axioms_clean
  ConditioningCompile.strategyOfTokens_trades_eq_nil_of_bigDay
  ConditioningCompile.guardedConditionRun_polySegStream
  ConditioningCompile.guardedZeroAwareConditionRun_polySegStream
  ConditioningCompile.safeSeparatedFrameDigitOutput_polySegStream
  ConditioningCompile.conditionedTranslation_preserves_ecDigit
  ConditioningCompile.eventualConditionedTranslation_preserves_ecDigit

-- Construction/Witnesses/RpnConditioning.lean — the conditioning translation in the RPN
-- symbol model: the run-aware price transducer and its master commutation, guard honesty,
-- the frame pass and its gated two-leg join, the two `def:ec → def:ec` translation
-- endpoints, and the `thm:scon` packaging (operational witnesses + criterion-level
-- closure of the conditioned market).
#assert_axioms_clean
  RpnConditioning.rpnGuardedConditionRun_polySegStream
  RpnConditioning.rpnGuardedZeroAwareConditionRun_polySegStream
  RpnConditioning.unRpn_rpnConditionRun
  RpnConditioning.unRpn_rpnZeroAwareConditionRun
  RpnConditioning.strategyOfTokens_rpnGuardedConditionTokens_trades
  RpnConditioning.strategyOfTokens_rpnGuardedZeroAwareConditionTokens_trades
  RpnConditioning.rpnTradeCountAt_eq_frameTradeCount
  RpnConditioning.rpnStructurallyAccepts_agree
  RpnConditioning.rpnSafeSeparatedFrameOutput_polySegStream
  RpnConditioning.strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades
  RpnConditioning.conditionedTranslation_preserves_ecRpn
  RpnConditioning.eventualConditionedTranslation_preserves_ecRpn
  ConditioningCompile.eventualConditioningOperationalWitness
  ConditioningCompile.gatedConditioningOperationalWitness
  ConditioningCompile.denominatorPatchedGatedConditioningOperationalWitness
  ConditioningCompile.lic_conditioned_gated_ofMarketComputation
  ConditioningCompile.lic_conditioned_eventualOfFloor
  ConditioningCompile.lic_conditioned_eventual_ofMarketComputation
  ConditioningCompile.lic_conditioned_fixed_ofComputationAndMarket
  ConditioningCompile.lic_conditioned_growing_ofComputationsAndMarket
  ConditioningCompile.lic_conditioned_gated_ofComputationsAndMarket

-- Construction/Witnesses/RpnFreeze.lean — the prefix-freeze transducer in the RPN symbol
-- model: the run-level quote lookup and the symbol-level freeze transducer, as the third
-- instance of the emitter-generic run rewriter.
-- PARTIAL, and the listed endpoints do NOT close the boundary:
-- `EfficientPrefixPatch.preserves_ec` still has no LIA inhabitant at the collapsed
-- class, because the emitted segment's fuel certificate needs a `BigDigits` decode
-- test on exponentially large escape codes (the inverse-operation ceiling of the digit
-- model).  `thm:ifp` is therefore covered only by `lic_iff_of_finitePerturbation` at the
-- efficiently-patchable restriction, never by an LIA-level discharge of the patch.
#assert_axioms_clean
  RpnFreeze.matchRun_iff
  RpnFreeze.runPrefixQuoteFromStates_exact
  RpnFreeze.unRpn_rpnFreezeRun

-- Construction/Witnesses/UnconditionalOverLIA.lean
#assert_axioms_clean
  lic_domination_universalSemimeasure_unconditional
  lic_domination_dovetailSemimeasure_unconditional
  lic_domination_everyLowerSemicomputable_unconditional
  lic_strict_domination_universalSemimeasure_unconditional
  lic_conditioned_ofCompiler_unconditional
  lic_conditioned_fixed_unconditional
  lic_conditioned_growing_unconditional

-- Construction/Witnesses/LUVSyntax.lean — LUV-combination syntax, the mesh-softmax
-- operational witness it constructs (`lem:mesh`), and the four expectation endpoints
-- that consume that witness with the operational hypothesis discharged
-- (`lem:mesh`, `thm:exppolymax`, `thm:expcoh`, `thm:perexpkno`).
-- `ordinaryLUVCombinationSyntax` (QuoteCodeOfMarket.lean) is the constructed
-- non-vacuity witness for the `_ofSyntax` endpoints' caller data, over a
-- non-degenerate index-varying sequence.
#assert_axioms_clean LUVCombinationSyntax.meshSoftmaxOperationalWitness
  ordinaryLUVCombinationSyntax
#assert_axioms_clean
  LUVCombination.BoundedSequence.mesh_independence_ofSyntax
  LUVCombination.BoundedSequence.exppolymax_ofSyntax
  LUVCombination.BoundedSequence.expcoh_ofSyntax
  LUVCombination.BoundedSequence.perexpkno_ofSyntax

-- Construction/Witnesses/ComputationSyntax.lean — represented semidecidable/decidable
-- claims built from a bounded computation, discharging the meta-learning interfaces.
-- `ordinarySemidecidableComputation` / `ordinaryBoundedComputation` are the constructed
-- non-vacuity witnesses for the two operational premises, over an index-varying truth
-- predicate.
#assert_axioms_clean
  ordinarySemidecidableComputation
  ordinaryBoundedComputation
  representedDecidableClaimsOfComputation
  inconsistentTheoryClaimsOfComputation
  lic_belief_finitistic_consistency_ofComputation
  lic_belief_stronger_theory_consistency_ofComputation
  lic_disbelief_inconsistent_theories_ofComputation
  lic_learns_halting_patterns_ofComputation
  lic_learns_provable_nonhalting_patterns_ofComputation
  lic_does_not_anticipate_halting_ofComputation

-- Construction/Witnesses/QuoteCodeOfMarket.lean — constructed rational quote codes:
-- the first *discharge* of the `RationalQuoteCode` reflection data.  `lic_expectations_of_probabilities_closed` is
-- `thm:epr` over the constructed LIA with no reflection hypotheses at all.
#assert_axioms_clean
  arithmeticThresholdLUV_polyThresholdCodeSeq
  RationalQuoteCode.ofComputable
  MarketComputation.expectQuote_computable
  theoremPriceQuoteCode theoremExpectationQuoteCode
  lic_expectations_of_probabilities_closed
  lic_iterated_expectations_closed

-- The deferred-day / self-trust reflection data constructed from the market
-- program.  `indicatorProductLUV_valuesAt` is the product law behind `thm:st`'s `A`.
-- `PGenerableRat.computable` is the certification that lets the closed quote codes emit a
-- threshold sentence about a *P-generable* (`def:ece`) threshold: parse the feature back
-- out of its emitted serialization, evaluate it against the certified market, minimize
-- over the interpreter clock.
#assert_axioms_clean
  theoremFutureQuoteCode theoremDeferredExpectationQuoteCode
  theoremConfidenceQuoteCode
  PGenerableRat.computable
  indicatorProductLUV_valuesAt indicatorProductLUV_rpnThresholdCodeSeq
  lic_no_expected_net_update_closed
  lic_expected_future_expectations_closed
  lic_self_trust_closed
  theoremIntervalQuoteCode lic_introspection_closed

-- Historical mesh `ccee`: the weighted conditional, **general-source** closed form. The deferred-weight
-- quote code names the `w ∘ f` program (deferral costs nothing at emission), and
-- `meshProductLUV` renders the product from that quote's own threshold atoms on a
-- width-`n+1` mesh, so no emitter ever needs the value `w (f n)` (which is neither
-- available — P-generable, and deferred — nor polynomially sized).  The price is that the
-- left product reflects only to within `1/(n+1)`: a **disclosed type-`(c)` substitution**
-- carried by `ConditionalExpectationQuote.slack`.  `indicatorProductLUV_exact_left_reflected`
-- is the non-vacuity witness at the exact (`slack = 0`) end.  See the Part F header and the
-- README's modeling-boundary history. The exact endpoint of record is audited next.
#assert_axioms_clean
  PCWorld.ValuesAt.eq
  theoremDeferredWeightQuoteCode
  theoremConditionalExpectationQuoteCode
  meshProductLUV_valuesAt
  meshProductLUV_rpnThresholdCodeSeq
  indicatorProductLUV_exact_left_reflected
  lic_no_expected_net_update_conditional_closed

-- Construction/Witnesses/SemanticLiftedCCEE.lean — endpoint of record for `thm:ccee`.
-- A fixed old-language copy prevents semantic self-reference; finite-stage entailment
-- admits every source satisfying the paper-facing `source_valued` premise. The one
-- canonical process is fixed from `T`, has an explicit completed world, and supports the
-- exact semantic product with zero slack.
#assert_axioms_clean
  liftedCCEEBaseDP_computable
  liftedCCEEBaseWorld_hworld
  canonicalCCEEDP_computable
  canonicalCCEEDP_hworld
  liftedRpnSemanticHandle_valuesAt
  liftedRpnSource_factor_eventually
  canonicalRationalQuote_factor_eventually
  lic_no_expected_net_update_conditional_closed_exact

-- Construction/Witnesses/ProductDefinition.lean — the exact-reflection route for the quoted
-- product.  Fresh product atoms are defined by the deductive process itself (a definitional
-- extension of the *process*, not of the theory), so a completed world values the product at
-- exactly `x · w` — `slack = 0`, no positivity hypothesis on the weight.
--
-- This historical diagnostic does **not** carry the `thm:ccee` row, and is inventoried so
-- its axiom cleanliness is gated. The endpoint of record is now the fixed-language
-- construction `lic_no_expected_net_update_conditional_closed_exact` above.
--
-- The route reaches a closed statement, `lic_no_expected_net_update_conditional_exact_closed`:
-- exact reflection over the constructed `LIA` on `theoremDP T ∪ productDefDP`, with `hworld`,
-- `source_valued`, `weight_valued` and `right_reflected` all discharged, and a jointly
-- satisfiable premise set exhibited by `..._nonvacuous`.  Its role is **diagnostic**, not
-- paper-facing: it shows the mesh endpoint's slack is an artifact of the propositional
-- substrate rather than of logical induction, because the same trader and criterion give an
-- exact conclusion once the product exists syntactically.
--
-- It establishes nothing about the base inductor's conditional expectations: `LIA` over the
-- extended process is a different inductor, and conservativity of completed-world truth does
-- not carry prices across.  This was adjudicated cross-family on 2026-08-11 (rejecting the
-- reading of it as `thm:ccee` at an instance; ranking mesh > this > weight-narrowing), and
-- the two costs it carries and the mesh endpoint does not — a genuine freshness restriction
-- on the source class, and `def:pgen` at the extended market — are stated at the theorem, in
-- `LogicalInduction/README.md` and in `scripts/coverage-classification.md`.  Full assessment
-- and the adjudication outcome in `LogicalInduction/notes/boundary-propositional-substrate.md`.
#assert_axioms_clean
  productDefDP_computable
  productDefDP_union_consistentWithTheory
  productLUV_valuesAt
  productLUV_valuesAt_union
  productLUV_rpnThresholdCodeSeq
  lic_no_expected_net_update_conditional_exact
  QuotationTheoryPresentation.mono
  exactProductDP_hworld
  lic_no_expected_net_update_conditional_exact_closed
  lic_no_expected_net_update_conditional_exact_closed_nonvacuous

-- Construction/Witnesses/ComputationDP.lean — unconditional-over-LIA capstones
-- (parity with the paradox-resistance and conditioning `_unconditional` endpoints above).
-- The quotation family below discharges market/inductor/presentation/hworld; the
-- reflection data (`RationalQuoteCode`, `*_reflected`) stays a caller hypothesis here,
-- discharged where needed by `RationalQuoteCode.ofComputable` (QuoteCodeOfMarket.lean).
#assert_axioms_clean
  lia_learns_halting_patterns_unconditional
  lic_expectations_of_probabilities_ofCode_unconditional
  lic_iterated_expectations_ofCode_unconditional
  lic_introspection_ofCode_unconditional
  lic_expected_future_expectations_ofRepresentation_unconditional
  lic_no_expected_net_update_ofRepresentation_unconditional
  lic_no_expected_net_update_conditional_ofRepresentation_unconditional
  lic_self_trust_ofRepresentation_unconditional
  lic_belief_finitistic_consistency_unconditional
  lic_belief_stronger_theory_consistency_unconditional
  lic_disbelief_inconsistent_theories_unconditional
  lic_learns_provable_nonhalting_patterns_unconditional
  lic_does_not_anticipate_halting_unconditional


open AffineCombination LUVCombination in
/-! ## Tier-2 boundary structures — field (hypothesis) surface

Each structure below appears in the *type* of a Tier-1 endpoint (directly, or
transitively through structure fields), so its fields are hypotheses the statement
read-through must audit. `#assert_fields` freezes that field-name set: adding or removing
a field — smuggling a premise in or out of a boundary — fails the build. It does not
freeze field *types* (see the macro's docstring); deliberate type changes are recorded in
comments beside the affected structure. The set is order-insensitive. Regenerate with
`SurfaceProbe`/`FieldProbe` if the surface changes deliberately. -/

#assert_fields AffineCombination
  const terms
#assert_fields AffineCombination.BoundedCombinationSequence
  poly bounded
#assert_fields AffineCombination.FeedbackTraderEmission
  tradeCount coefficient sentence tradeCount_poly coefficient_poly sentence_poly trades_eq
#assert_fields AffineCombination.FeedbackTraderEmissionFamily
  emit
#assert_fields AffineCombination.FeedbackTraderEmissionSigns
  positive negative
#assert_fields AffineCombination.FeedbackTruthSequence
  determined sequence poly bounded magnitude value_vanishing feedback_price
#assert_fields AffineCombination.PolySequence
  termCount coefficient sentence termCount_poly const_poly coefficient_poly sentence_poly terms_eq const_rank coefficient_rank const_closed coefficient_closed
#assert_fields AffineQuoteEq
  toAffineQuotePortfolio future_coherent
#assert_fields AffineQuoteGE
  toAffineQuotePortfolio future_coherent
#assert_fields AffineQuotePortfolio
  family poly scale scale_pos current_price bounded magnitude_le_one
-- Tier-2 field change (2026-07-30): `prefix_codes` moved from the whole-value
-- `PolySentenceCodes` to the symbol-metered `RpnSentenceCodes`.  `#assert_fields` freezes
-- field *names* only, so the type change is recorded here explicitly; it is what makes the
-- structure inhabitable (`ordinaryBitPrefixSentences`).
#assert_fields BitPrefixSentences
  atom prefixSentence enumeration enumeration_covers prefix_codes holds_prefix realizable
#assert_fields BooleanQuoteCode
  code pos_complete neg_complete
-- The step budget is now a `ComputableHorizon` (the paper's arbitrary computable `f`, named
-- by its program) in place of the former `steps_poly : PolyNatCodes steps`, which restricted
-- `f` to polynomial time.  `#assert_fields` freezes field *names* only, so the class change
-- is recorded here explicitly.
#assert_fields BoundedComputation
  machine input input_poly steps horizon truth_iff
#assert_fields CEEnumeration
  code halts outputs_sound
#assert_fields CompactConditioningProcessComputation
  toDeductiveProcessComputation condition_codes
#assert_fields CompletedAffineQuoteApprox
  toAffineQuotePortfolio theory_coherent
#assert_fields CompletedAffineQuoteEq
  toAffineQuotePortfolio theory_coherent
#assert_fields ComputableHorizon
  program program_spec
#assert_fields ComputationTheoryPresentation
  theory_deltaOne process halting_enters halting_refutes boundedHalting_enters boundedFailure_refutes inconsistency_enters inconsistency_refutesConsistency
#assert_fields ConditionalExpectationQuote
  weight_mem weight_generable source_codes left_codes right_codes slack slack_tendsto source_valued left_reflected right_reflected affine
#assert_fields ConditioningPresentation
  condition condition_codes holds_condition combined_computable
#assert_fields ConditioningTraderCompiler
  conditioned_computable translate translate_ec tracks_on_condition preserves_floor
#assert_fields ContinuousSemimeasure
  mass nonneg root_le_one children_le
#assert_fields CurrentExpectationQuote
  source_codes quote_codes reflected affine
#assert_fields CurrentPriceExpectationQuote
  sentence_codes quote_codes reflected affine
#assert_fields DUSApproximationPresentation
  approximation approximation_codes nonneg le_mass tendsto
#assert_fields DUSThresholdEmission
  threshold_sum_codes inverse_width_codes
#assert_fields DeductiveProcess
  D mono
#assert_fields DeductiveProcessComputation
  code code_spec
#assert_fields DeferralFunction
  f lt code fueled
#assert_fields EfficientPrefixPatch
  quote quote_exact preserves_ec
#assert_fields FiniteSupportPatch
  quote quote_exact preserves_ec
#assert_fields EfficientRepeatedEnumeration
  sequence sequence_poly repeats sound covers
#assert_fields EventualConditioningFloor
  cutoff zeroDays zeroDays_lt epsilon epsilon_pos zero_exact positive_floor
#assert_fields EventualConditioningOperationalWitness
  floor conditioned_computable translation_ec
#assert_fields ExpectedFutureExpectationQuote
  source_codes quote_codes reflected affine
#assert_fields FeedbackTruth.FeedbackTruthComputation
  value code a degree computes agrees
#assert_fields FuturePriceQuote
  sentence_codes quote_codes reflected affine
#assert_fields GatedConditioningOperationalWitness
  epsilon_pos denominator_floor conditioned_computable translation_ec
#assert_fields GeneratedRatFeature
  rank_le polyTok closed denote
#assert_fields InconsistentTheoryClaims
  inconsistencySentence consistencySentence inconsistency_poly consistency_poly inconsistency_provable consistency_disprovable
#assert_fields IndependentBitAtoms
  atom realizable
#assert_fields IntrospectionIntervalQuote
  source_codes lower_feature lower_generated upper_feature upper_generated width_codes inverse_width_codes width_pos width_tendsto_zero probability_bounds quote quote_codes reflected inside_affine outside_affine
#assert_fields IsLogicalInductor
  marketComputable processComputable noExploit
#assert_fields MachineFiniteSupportPatch
  quote quote_exact preserves_ec
#assert_fields LUV
  gt
#assert_fields LUVCombination
  const terms
#assert_fields LUVCombination.BoundedSequence
  poly bounded
#assert_fields LUVCombination.ExactTheoryPresentation
  value value_mem threshold_iff
#assert_fields LUVCombination.MeshSoftmaxOperationalWitness
  poly bounded magnitude lower_poly lower_bounded lower_magnitude
#assert_fields LUVCombination.PolySequence
  mesh_poly
#assert_fields LUVCombinationSyntax
  termCount coefficient luv termCount_poly const_poly coefficient_poly threshold_poly terms_eq const_rank coefficient_rank const_closed coefficient_closed
#assert_fields LowerSemicomputableContinuousSemimeasure
  toContinuousSemimeasure approximation approximation_code approximation_computes approximation_nonneg approximation_mono approximation_le approximation_tendsto
#assert_fields MarketComputation
  quote code quote_exact code_spec price_mem_Icc
#assert_fields OccamThresholdEmission
  threshold_sum_codes inverse_width_codes
#assert_fields PGenerableWeighting
  polySeg rank_le closed
#assert_fields PairedWeighting
  polySeg rank_le closed
#assert_fields ParadoxResistanceQuote
  sentence sentence_codes width width_codes width_pos width_tendsto_zero diagonal_reflected lower_affine upper_affine
#assert_fields ParameterizedDiagonalQuoteCode
  toBooleanQuoteCode body represents_fixedpoint
#assert_fields PatientSettlementClock
  active active_codes antitone active_through_envelope eventually_inactive settled_of_inactive
#assert_fields PolyMachineCodes
  code code_poly
#assert_fields PolyNatCodes
  code code_poly
#assert_fields PrefixMachinePresentation
  sentence sentence_codes approximation approximation_codes approximation_nonneg approximation_le approximation_tendsto kraft covers
#assert_fields PrefixNegationCompiler
  overhead complexity_neg_le
#assert_fields QuotationTheoryPresentation
  toComputationTheoryPresentation theory_sigmaOne quote_positive_enters quote_negative_refutes
#assert_fields RationalQuoteCode
  code value_mem pos_complete neg_complete threshold_poly
#assert_fields RepresentedDecidableClaims
  toRepresentedSemidecidableClaims disprovable_of_false
#assert_fields RepresentedSemidecidableClaims
  sentence sentence_poly provable_of_true
#assert_fields SelfTrustQuote
  delta_pos probability_mem sentence_codes delta_codes probability_generable product_codes confidence_codes confidence_reflected product_reflected affine
#assert_fields SemidecidableComputation
  machine input input_poly truth_iff
#assert_fields SettlementChecker
  code spec
#assert_fields Strategy
  trades rank_le
#assert_fields StrictSeparatorPresentation
  constraint repetition jointly_possible consistentAt class_covers mass_class_tendsto_zero
#assert_fields Trader
  strat
#assert_fields UniversalContinuousSemimeasure
  toLowerSemicomputableContinuousSemimeasure universal


end LogicalInduction

/-! ## ModalAgents — modal open-source game theory (Barász et al.)

Every ModalAgents endpoint is now strictly clean. The former sole intentional axiom
`glFixedPoint_thm42` (GL fixed-point existence) is discharged by the `ProvabilityLogic/`
development (vendored from FormalizedFormalLogic/ProvabilityLogic, pinned in
`lakefile.lean`; see `ModalAgents/FixedPoint.lean`); `glFixedPoint_thm42`
is a proved theorem, so the cooperation endpoints that rest on it are asserted strictly
clean below rather than via `#assert_axioms_clean_except`.

That paper numbers its nodes off a single section-scoped counter shared by
`theorem`/`lemma`/`proposition`/`corollary`/`condition`, and only 22 of them carry a
LaTeX `\label`, so — as for Cartesian Frames — the printed `Theorem 4.7` style number is
the provenance key rather than a label. `Paper node:` lines on the endpoints below cite
those numbers, and `scripts/check-modal-agents-nodes.py` validates them against the
committed TeX (`ModalAgents/notes/1401.5577-main.tex`) **and** checks that every
*declaration* annotated in `ModalAgents/` is itself listed between the MA-INVENTORY
markers below.

Several listed endpoints carry no annotation of their own, because they render no
numbered node of that paper. They are all `lemma`s or definitions, per the repo's keyword
rule, and they stay inventoried and axiom-checked regardless:

* `subst_congr` — a GL-level substitution congruence; the paper's Lemma 4.5 is the
  *arithmetic* statement, carried by `arithmetic_modal_substitution`.
* `glFixedPoint_uniqueness` — the *rule* form of Theorem 4.3, derived from the printed
  internal form `glFixedPoint_uniqueness_internal` (which carries the annotation) by
  necessitation; it is the form the modal-agent development consumes.
* `arithInterp` and `Realization.update` — the definitions the arithmetic statements are
  phrased in: `arithInterp f φ` is the paper's `φ(ψ₁,…,ψₙ)`, and `Realization.update`
  substitutes for the diagonal variable. Listed because they are statement surface.
* The §4 arithmetic-agent vocabulary — `Agent`, `Agent.app`, `opponentRealization`,
  `IsModalAgentOfRank`, `IsModalAgent`, `BehaviorallyEquivalent`, `IsBehavioral`,
  `cliqueBotSpec`, `cliqueBot`, `cliqueBotVariant`. These are the paper's §4 and §2
  definitions ("agent", "`[X(Y)]`", "modal agent of rank `k`", "behaviorally
  equivalent", "behavioral agent", CliqueBot). That paper's `definition` environment is
  an uncounted `trivlist`, so none of them *can* cite a node; they are listed because
  they are the statement surface of `modalAgent_isBehavioral` and
  `cliqueBot_not_modalAgent`, and reading either endpoint means reading them.
* `cooperateBot_isModalAgentOfRank_zero` — the non-vacuity witness for
  `IsModalAgentOfRank`: CooperateBot (action formula `⊤`) is a modal agent of rank 0, so
  Theorem 4.8 is not a statement about an empty class and Corollary 4.9 separates
  CliqueBot from a class that has members. The paper introduces CooperateBot in §2 and
  never numbers this.
* The Corollary 4.9 proof steps — `cliqueBot_app` (CliqueBot cooperates exactly with
  agents carrying its own code, the quining that makes it CliqueBot at all),
  `cliqueBotVariant_ne`, `cliqueBot_behaviorallyEquivalent_variant`,
  `cliqueBot_cooperates_self`, `cliqueBot_defects_variant` and
  `cliqueBot_not_isBehavioral`. These are the clauses of that corollary's one-sentence
  printed proof, not numbered nodes. They are listed rather than left internal because
  the corollary is a *negative* result: what makes it non-trivial is that `cliqueBot`
  really is CliqueBot and the variant really is behaviorally equivalent to it, and those
  are exactly the facts above.
* `defectBot_defects`, `defectBot_provably_defects` and `cooperateBot_cooperates` —
  the §2 remark that `PA ⊢ [CB(X)=C]` and `PA ⊢ [DB(X)=D]`, prose in an unnumbered
  `remark`.
* `fairBot_unexploitable`, `fairBot_vs_cooperateBot` and `fairBot_vs_defectBot` — §3
  prose on FairBot's unexploitability ("by inspection") and its waste against
  CooperateBot, again unnumbered.
* `prudentBot_vs_defectBot` — the "in particular, PA+1 ⊢ [PB(DB)=D]" step *inside* the
  proof of Theorem 3.2, not one of that theorem's four conjuncts.
* The defection-boundary block — `ProvablyDefects.defects`, the three outcome
  reductions `outcome_fairBot_defectBot`, `outcome_prudentBot_defectBot`,
  `outcome_prudentBot_cooperateBot`, and the three negative results
  `fairBot_not_provably_defects_defectBot`,
  `prudentBot_not_provably_defects_defectBot`,
  `prudentBot_not_provably_defects_cooperateBot`. These are *this development's* own
  accounting rather than paper nodes: they pin down exactly how far `Defects` (which
  is `GL ⊬ outcome`, weaker than the paper's provable defection) can be strengthened
  to `ProvablyDefects` (`GL ⊢ ∼outcome`, the paper's notion). The answer is: on
  DefectBot's side, all the way; on the other three endpoints, not at all, because
  their outcome formulas are GL-equivalent to `□⊥`, `□⊥` and `□□⊥`, so provable
  defection would require `GL` to prove `Con(PA)` or `Con(PA+1)`. That is exactly why
  the paper states those three in `PA+1`/`PA+2`. They are listed here so a regression
  in the obstruction argument fails the build alongside the endpoints it excuses. -/

-- MA-INVENTORY-BEGIN
#assert_axioms_clean
  subst_congr glFixedPoint_uniqueness glFixedPoint_uniqueness_internal glFixedPoint_thm42
  glFixedPoint_spec outcome_fixed_point
  lob_theorem arithInterp Realization.update
  arithmetic_modal_substitution arithmetic_fixedPoint_uniqueness
  Agent Agent.app opponentRealization IsModalAgentOfRank IsModalAgent
  cooperateBot_isModalAgentOfRank_zero
  BehaviorallyEquivalent IsBehavioral modalAgent_isBehavioral
  cliqueBotSpec cliqueBot cliqueBotVariant
  cliqueBot_app cliqueBotVariant_ne cliqueBot_behaviorallyEquivalent_variant
  cliqueBot_cooperates_self cliqueBot_defects_variant
  cliqueBot_not_isBehavioral cliqueBot_not_modalAgent
  defectBot_defects defectBot_provably_defects ProvablyDefects.defects
  cooperateBot_cooperates
  fairBot_vs_fairBot fairBot_unexploitable fairBot_vs_cooperateBot
  rank0_fairBot_implies_cooperateBot
  fairBot_vs_defectBot prudentBot_vs_fairBot prudentBot_vs_defectBot
  prudentBot_vs_cooperateBot prudentBot_vs_prudentBot prudentBot_unexploitable
  outcome_fairBot_defectBot outcome_prudentBot_defectBot
  outcome_prudentBot_cooperateBot
  fairBot_not_provably_defects_defectBot
  prudentBot_not_provably_defects_defectBot
  prudentBot_not_provably_defects_cooperateBot
  Cooperates.arithmeticLift ProvablyDefects.arithmeticLift modalAgent_behavioral
-- MA-INVENTORY-END

/-! ## Concrete arithmetic instantiation — the one upstream gap

Everything above is asserted of the endpoints **as stated**, and the arithmetic-quotation
family (`thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`, `thm:ref`, `thm:epr`, `thm:er`,
`thm:lp`, `thm:halts`, …) is stated parametrically over an arithmetic theory:
`(T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`. Those endpoints are
axiom-clean, but only because the theory data are *hypotheses*.

Instantiating them at a concrete theory is a different claim, and it currently costs one
upstream axiom: Foundation supplies `Δ₁`-definability of `𝗜𝚺₁` and `𝗣𝗔` only as
`axiom ISigma1_delta1Definable` / `axiom PA_delta1Definable`
(`Foundation/FirstOrder/Incompleteness/Examples.lean`, marked *TODO: Prove*). That is an
upstream gap, not a modeling choice of this development, and it is invisible to the
parametric assertions above — so it is pinned here instead, at a concrete instantiation,
where a regression would fail the build.

If Foundation later proves `𝗜𝚺₁.Δ₁`, this block starts failing (the `except` axiom
becomes unused) and should be promoted to `#assert_axioms_clean`. -/

open LO LO.FirstOrder LO.FirstOrder.Arithmetic in
/-- `thm:ceu` at the concrete theory `𝗜𝚺₁`. -/
noncomputable def concreteArithmeticInstantiation :=
  @LogicalInduction.lic_no_expected_net_update_closed 𝗜𝚺₁ inferInstance inferInstance
    inferInstance

open LO.FirstOrder.Arithmetic in
#assert_axioms_clean_except ISigma1_delta1Definable concreteArithmeticInstantiation

/-! ## Cartesian Frames — endpoint inventory

Same contract as the Logical Induction inventory above, for `CartesianFrames/`
(paper: arXiv:2109.10996). Most of that paper's nodes carry no LaTeX `\label`, so
`Paper node:` lines cite the printed `Definition n` / `Claim n` / `Theorem n`
numbers; `scripts/check-cartesian-frames-nodes.py` validates them against the
committed TeX **and** checks that every *declaration* annotated in the library is
itself listed between the CF-INVENTORY markers below — sharing a node with a listed
declaration is not enough. Five groups of listed names carry no annotation of their own:
the constructive carriers of Appendix B's Claims 46 and 48 (`Frame.dualEquivalence`,
`Frame.zeroIsInitial`, `Frame.topIsTerminal` — the `theorem`s state the paper's
propositional content, these are the data behind them); the four unnumbered facts the
paper uses silently (`Frame.Biextensional.nonempty_iso_collapse`, the step taken
whenever a biextensional frame is replaced by its collapse, together with the three
`≃ᵇ`-invariants `Frame.image_eq_of_biextEquiv`,
`Frame.exists_env_injective_of_biextEquiv` — the standard refuters for `◁ₓ` and `◁₊` —
and `Frame.BiextEquiv.dual`, which every dualized definition runs on); the
inhabitation of Definition 31's choice functions (`Frame.partitionSectionsOut` and the
`Nonempty` instance built from it, which the paper assumes without comment); the one
combined-iff convenience wrapper (`Frame.addSubagent_iff_addSubagentCategorical`,
whose two halves are the annotated Claims 55 and 56); and the last three blocks, the
non-vacuity, subagency, and operation/Appendix-B witnesses of
`CartesianFrames/Examples.lean`, listed here so that the separations they assert are
axiom-checked alongside the definitions they constrain. -/

open CartesianFrames in
-- CF-INVENTORY-BEGIN
#assert_axioms_clean
  Frame Frame.image Frame.Hom Frame.Hom.comp Frame.instChuCategory
  Frame.dual Frame.Hom.dual Frame.dualFunctor
  Frame.Hom.IsIsomorphism Frame.nonempty_iso_iff_exists_isIsomorphism
  Frame.Biextensional
  Frame.agentSetoid Frame.envSetoid Frame.collapse Frame.BiextEquiv
  Frame.Homotopic Frame.HomotopyEquiv
  Frame.Biextensional.nonempty_iso_collapse
  Frame.nonempty_iso_of_eq Frame.biextEquiv_of_nonempty_iso
  Frame.homotopyEquiv_iff_nonempty_iso_of_biextensional
  Frame.biextEquiv_iff_homotopyEquiv
  Frame.image_eq_of_biextEquiv Frame.exists_env_injective_of_biextEquiv
  Frame.BiextEquiv.dual
  Frame.mapWorlds Frame.BiextEquiv.mapWorlds Frame.curry
  Frame.botOf Frame.instBot Frame.botOfUnivIsoBot Frame.homBotEquiv
  Frame.Subagent Frame.SubagentCurry Frame.SubagentCovering
  Frame.subagent_iff_subagentCovering
  Frame.SubagentCovering.subagentCurry Frame.SubagentCurry.subagent
  Frame.subagent_iff_subagentCurry
  Frame.Subagent.trans Frame.Subagent.of_biextEquiv Frame.Subagent.refl
  Frame.AddSubagent Frame.MultSubagent
  Frame.AddSubagentCurry Frame.MultSubagentCurry
  Frame.AddSubagent.addSubagentCurry Frame.AddSubagentCurry.addSubagent
  Frame.MultSubagent.multSubagentCurry Frame.MultSubagentCurry.multSubagent
  Frame.addSubagent_iff_addSubagentCurry Frame.multSubagent_iff_multSubagentCurry
  Frame.AddSubagent.subagent Frame.MultSubagent.subagent
  Frame.AddSubagent.congr Frame.MultSubagent.congr
  Frame.AddSubagent.refl Frame.MultSubagent.refl
  Frame.AddSubagent.trans Frame.MultSubagent.trans
  Frame.subagent_iff_exists_multSubagent_addSubagent
  Frame.SubEnv Frame.AddSubEnv Frame.MultSubEnv
  Frame.multSubagent_iff_multSubEnv
  Frame.commit Frame.commitCompl Frame.assume Frame.assumeCompl
  Frame.commit_addSubagent Frame.commitCompl_addSubagent
  Frame.addSubEnv_assume Frame.addSubEnv_assumeCompl
  Frame.partitionSections
  Frame.partitionSectionsOut Frame.instNonemptyPartitionSections
  Frame.external Frame.externalQuot Frame.internal Frame.internalSect
  Frame.external_multSubagent Frame.externalQuot_multSubagent
  Frame.multSubagent_internal Frame.multSubagent_internalSect
  Frame.commit_commit_self Frame.commitCompl_commitCompl_self
  Frame.assume_assume_self Frame.assumeCompl_assumeCompl_self
  Frame.dualEquivalence Frame.dualFunctor_isEquivalence
  Frame.dualEquivalence_functor_comp_inverse Frame.dualEquivalence_inverse_comp_functor
  Frame.instZero Frame.instTop
  Frame.zeroIsInitial Frame.topIsTerminal
  Frame.nonempty_isInitial_zero Frame.nonempty_isTerminal_top
  Frame.oneOf Frame.instOne Frame.oneOfUnivIsoOne
  Frame.AddSubagentCategorical Frame.MultSubagentCategorical
  Frame.AddSubagentCategorical.addSubagent Frame.AddSubagent.addSubagentCategorical
  Frame.addSubagent_iff_addSubagentCategorical
  Frame.MultSubagentSubEnv
  Frame.multSubagentCategorical_iff_multSubagentSubEnv
  Frame.multSubagentSubEnv_iff_multSubagent
  -- Non-vacuity witnesses (CartesianFrames/Examples.lean).
  Examples.driver_biextensional
  Examples.seven_mem_driver_image Examples.two_not_mem_driver_image
  Examples.dedup_biextensional Examples.not_dup_biextensional
  Examples.homotopyEquiv_dedup_dup Examples.not_nonempty_iso_dedup_dup
  Examples.homotopyEquiv_strictly_weaker_than_iso
  Examples.biextEquiv_strictly_weaker_than_iso
  Examples.homotopic_ne_eq Examples.not_homotopic_of_row_col
  Examples.not_nonempty_hom_dedup_driver Examples.not_homotopyEquiv_dedup_driver
  Examples.not_biextEquiv_dedup_driver
  Examples.nonempty_iso_dup_collapse_dedup
  Examples.not_nonempty_iso_dup_collapse
  -- Subagency witnesses (CartesianFrames/Examples.lean).
  Examples.not_subagent_dedup_driver
  Examples.driver3_biextensional Examples.driver_addSubagent_driver3
  Examples.not_biextEquiv_driver_driver3
  Examples.teamZ_image_univ Examples.teamC_multSubagent_teamD
  Examples.teamC_biextensional Examples.teamD_biextensional
  Examples.not_biextEquiv_teamC_teamD
  Examples.not_subagent_driver3_driver Examples.not_subagent_teamD_teamC
  Examples.bigC_biextensional Examples.bigC_subagent_bigD
  Examples.not_bigC_multSubagent_bigD Examples.not_bigC_addSubagent_bigD
  Examples.every_witness_nontrivial Examples.bigC_decomposes
  -- Operation and Appendix-B witnesses (CartesianFrames/Examples.lean).
  Examples.externalBigD_multSubagent_bigD Examples.bigD_biextensional
  Examples.bigD_outcome_inj Examples.bigDCells_ne
  Examples.externalBigD_biextensional Examples.not_biextEquiv_externalBigD_bigD
  Examples.externalBigD_multSubagent_not_biextEquiv
  Examples.not_biextEquiv_driver3_driver3Assume
  Examples.colDupLoop_homotopy_factors Examples.colDup_addSubagentCategorical_self
  Examples.colDupLoop_no_exact_factorization Examples.colDup_two_distinct_endos
  Examples.colDup_addSubagentCategorical_oneCol
  Examples.not_exact_factorization_colDup_oneCol
-- CF-INVENTORY-END

/-! Tier-2 boundary structures for the Cartesian Frames surface (same contract as
the Logical Induction `#assert_fields` block). -/
#assert_fields CartesianFrames.Frame
  Agent Env outcome
#assert_fields CartesianFrames.Frame.Hom
  agent env adjoint
#assert_fields CartesianFrames.Frame.Biextensional
  agent_ext env_ext

/-! ## Finite Factored Sets — the checked endpoint inventory

Same contract as the CF-INVENTORY block above: every declaration carrying a
`Paper node:` annotation in `FiniteFactoredSets/` must itself be listed between the
FFS-INVENTORY markers below, and `scripts/check-finite-factored-sets-nodes.py` enforces
that direction, together with the validity of each cited node against the committed TeX and
the anchoring of each annotation to a named declaration.

Read that as the one direction it is.  The checker does **not** enforce the converse — that
every name listed below is a real, annotated declaration — and could not: this block also
carries the non-vacuity witnesses, so it holds several times as many entries as there are
annotations.  A line naming a declaration that does not exist passes the Python checker and
is caught only when this file is elaborated, by `#assert_axioms_clean` failing to resolve
the name.  `lake build AxiomAudit` is part of the contract, not an independent check of it.
Nor does anything mechanically check that the paper's in-scope nodes are all covered; that
accounting is prose in `FiniteFactoredSets/README.md`, to be re-derived by hand (compare
`grep -rho "Paper node: [A-Za-z]* [0-9]*" FiniteFactoredSets/*.lean | sort -u` against
`scripts/paper_nodes.py`'s `printed_independent_declarations`).

This formalization is **complete** for its ruled scope: the list below covers §2–§7 —
every in-scope node has a carrier or is Mathlib-rendered; Conjecture 1 (§7.2) is listed as
a stated `Prop` that nothing proves, and Examples 3–4 are out of scope by ruling.  Nine of
the paper's nodes have no Lean carrier at all because they are rendered by
Mathlib vocabulary under the `dd:` tags in `FiniteFactoredSets.lean`.  Six are in §2.1 —
Definition 1 (the disjoint union `⊔S`) is absorbed into `Setoid` and the dependent product,
Definition 2 (partition) is `Setoid`, Definition 5 (`∼_X`) is the setoid relation,
Definition 6 (finer) is `≤`, Definition 7 (`Dis_S`/`Ind_S`) is `⊥`/`⊤`, and Definition 9
(`∏(B)`) is the dependent product — and three are outside it: §5.1's Definitions 29
(evaluation) and 30 (support) and §6.1's Definition 39 (preimages).  Nine plus the 87
carried below is the 96 in-scope nodes.  Those nine are recorded in
`FiniteFactoredSets/README.md` rather than
inventoried here, because there is no declaration of this project's to axiom-check. -/

open FiniteFactoredSets in
-- FFS-INVENTORY-BEGIN
#assert_axioms_clean
  part equivalence_setoid IsTrivialPartition bot_le_and_le_top commonRefinement
  IsFactorization FactoredSet FactoredSet.eq_of_forall_rel
  isFactorization_iff_existsUnique FactoredSet.eq_of_part_eq
  FactoredSet.chimeraFun FactoredSet.chimera FactoredSet.chimeraImage
  FactoredSet.chimera_spec
  IsTrivialFactorization existsUnique_trivialFactorization
  FactoredSet.size FactoredSet.dim FactoredSet.finite_basis_of_finite
  FactoredSet.size_eq_prod isTrivialFactorization_of_isFactorization
  FactoredSet.dim_spec
  -- §3.1-§3.2: generation and history (FiniteFactoredSets/History.lean).  `history_isLeast`
  -- and `history_spec` are the endpoints that carry `[Finite F.B]` — finite *dimension*
  -- only, per `dd:finiteness-minimal`; nothing here assumes `S` finite.
  FactoredSet.Generates FactoredSet.generates_tfae FactoredSet.generates_spec
  FactoredSet.history FactoredSet.history_isLeast FactoredSet.history_spec
  -- §3.3-§3.4: orthogonality and time (FiniteFactoredSets/Orthogonality.lean).
  -- Definition 18 has two carriers, one per sentence: `Orthogonal` and `Entangled`.
  FactoredSet.Orthogonal FactoredSet.Entangled
  FactoredSet.orthogonal_iff_exists FactoredSet.orthogonal_spec
  FactoredSet.Before FactoredSet.StrictlyBefore
  FactoredSet.before_iff_forall_sInf FactoredSet.before_iff_forall_orthogonal
  FactoredSet.before_spec FactoredSet.history_eq_setOf_before
  -- §4.1: subpartitions and generating a subpartition
  -- (FiniteFactoredSets/Subpartition.lean).  Definition 20's `Subpartition` is a partial
  -- equivalence relation on `S` (`dd:subpartition`), Definition 21 is its `dom`, and
  -- Definition 22 is `restrict`; `GeneratesSub` is Definition 23.  As in §3.1, `C ⊆ B` is a
  -- hypothesis only where it is load-bearing — the `7 → 1` leg of Proposition 20.
  Subpartition Subpartition.dom Subpartition.restrict
  FactoredSet.GeneratesSub FactoredSet.generatesSub_tfae FactoredSet.generatesSub_spec
  -- §4.2: the history of a subpartition (FiniteFactoredSets/SubpartitionHistory.lean).
  -- `historySub` is Definition 24; Proposition 22 is the pair "least generating subset"
  -- plus "agrees with Definition 17 on partitions of `S`", so it is one endpoint with two
  -- conjuncts.  Lemmas 1 and 2 are the paper's two `lemma2`-numbered results.
  FactoredSet.historySub FactoredSet.historySub_isLeast_and_eq_history
  FactoredSet.historySub_spec FactoredSet.historySub_restrict_part_eq
  FactoredSet.historySub_inf_eq
  -- §4.3: conditional orthogonality (FiniteFactoredSets/ConditionalOrthogonality.lean).
  -- Definition 25 has three carriers, one per clause, as Definition 19 does.
  FactoredSet.OrthogonalSub FactoredSet.BeforeSub FactoredSet.StrictlyBeforeSub
  FactoredSet.OrthogonalGivenSet FactoredSet.OrthogonalGiven
  FactoredSet.orthogonal_iff_orthogonalGiven_top FactoredSet.orthogonalGiven_semigraphoid
  FactoredSet.orthogonalGiven_self_iff
  -- §5.1: characteristic polynomials (FiniteFactoredSets/Polynomial.lean).  `dd:poly` fixes
  -- the ring: `Poly^F` is `MvPolynomial (Set S) ℝ`, because under `dd:partition` a block
  -- `[s]_b` *is* the set `part b s` and so is a variable verbatim.  Definitions 29 and 30
  -- (evaluation `p(f)`, support `supp(p)`) have no declaration of ours — they are
  -- `MvPolynomial.eval` and `MvPolynomial.vars`, so they belong in the README's table of
  -- Mathlib-rendered nodes.  This is the first block that needs `[Finite S]` rather than
  -- `Finite F.B`: `Q^F_E` sums over `E ⊆ S`, so it is the intended polynomial only for
  -- finite `E`.  Not every statement here does, though — per `dd:finiteness-minimal` each
  -- carries what its own proof consumes, and Proposition 26 (`Q_eq_poly`) needs only
  -- `Finite F.B`, its content over an infinite `E` being the degenerate `0 = 0`.
  -- Propositions 27 and 28 are the two here that genuinely need `[Finite S]`, and 28
  -- (`factor2`) is the load-bearing result the rest of §5 routes through.
  Poly FactoredSet.Q mono monos poly
  FactoredSet.Q_eq_poly FactoredSet.poly_union_chimeraImage
  FactoredSet.eq_C_mul_poly_of_dvd_Q
  -- §5.3: characteristic polynomials and orthogonality
  -- (FiniteFactoredSets/CharacteristicOrthogonality.lean).  Lemma 3 (`CPO`) is a single
  -- three-clause `TFAE`, so it is one endpoint; the two isolated directions
  -- `Q_mul_Q_eq_of_orthogonalGiven` and `orthogonalGiven_of_Q_mul_Q_eq` are projections of
  -- it, on the consumer surface rather than the paper-node inventory.  The `2 → 1` leg is
  -- the one place §5 uses that `Poly^F` is a unique factorization monoid (Mathlib's
  -- `MvPolynomial.uniqueFactorizationMonoid`), which is what turns Proposition 31's
  -- irreducible factor into a prime.
  FactoredSet.orthogonalGiven_tfae
  -- Non-vacuity witnesses (FiniteFactoredSets/Examples.lean).  Every §2-§5.2 endpoint is
  -- stated over `FactoredSet`; these are what make those endpoints say something.
  -- `coordFS` is the load-bearing one: with a single factor every `C` behaves as `∅` or
  -- `B`, so Proposition 4 would be near-tautologous — and with a single factor there is no
  -- subset of `S` on which the §4 restrictions can pull apart or entangle two factors,
  -- which is what the §4 block at the end of this list needs, nor any nontrivial disjoint
  -- split of `B` for Proposition 27 or nontrivial `Irr^F(E)` for Propositions 29-31.
  Examples.bool_isFactorization Examples.boolFS
  Examples.coord_isFactorization Examples.coordFS
  Examples.not_subsingleton_coordFS_basis Examples.coordFS_chimera_corners
  Examples.empty_isFactorization Examples.emptyFS
  Examples.not_isFactorization_empty_basis
  Examples.unit_isFactorization Examples.unitFS Examples.unitFS_basis_unique
  -- Definition 10's two fields are independent: each of these exhibits one field holding
  -- while the other fails, so neither is decoration.
  Examples.not_isFactorization_singleton_fstFactor
  Examples.not_isFactorization_unit_singleton_top
  -- §2.5 on `coordFS` / `boolFS`: Propositions 7-9 applied to a concrete factored set.
  Examples.size_coordFS Examples.dim_coordFS
  Examples.size_eq_prod_coordFS Examples.dim_spec_coordFS Examples.boolFS_trivial
  -- §3 on `coordFS`: the three histories that pin the order down, then each §3 relation
  -- exhibited both holding and failing, so that none of `Generates`, `Orthogonal`,
  -- `Entangled`, `Before`, `StrictlyBefore` is silently empty or silently total.
  Examples.generates_singleton_fstFactor
  Examples.history_fstFactor Examples.history_sndFactor
  Examples.history_top Examples.history_bot Examples.history_eq_basis_of
  Examples.orthogonal_fstFactor_sndFactor Examples.not_orthogonal_fstFactor_self
  Examples.not_orthogonal_bot_fstFactor
  Examples.before_fstFactor_bot Examples.strictlyBefore_fstFactor_bot
  Examples.not_before_fstFactor_sndFactor Examples.history_eq_setOf_before_coordFS
  -- The XOR partition: `history` is not injective, so Proposition 18's `Before` is a
  -- preorder and *not* antisymmetric — which is why Proposition 18 claims no more.
  Examples.xorPart Examples.history_xorPart Examples.history_not_injective
  Examples.before_xorPart_bot_and_back Examples.entangled_xorPart_fstFactor
  -- `emptyFS`: the `Nonempty S` hypothesis on Proposition 13 clause 4 and Proposition 19
  -- is load-bearing — both conclusions fail outright over the empty set.
  Examples.emptyFS_history_bot Examples.emptyFS_history_ne_singleton
  Examples.emptyFS_history_ne_setOf_before
  -- §4 on `coordFS`: the two coordinate factors restricted to a block of `fstFactor`
  -- (`Efst`, where they stay independent) and to the diagonal (`Ediag`, a block of
  -- `xorPart`, where the first coordinate determines the second).  Domains, blocks,
  -- `GeneratesSub`, `historySub` and conditional orthogonality are computed over both.
  Examples.Efst Examples.Ediag Examples.sndOnEfst
  Examples.classes_sndOnEfst Examples.generatesSub_sndOnEfst
  Examples.not_generatesSub_fst_sndOnEfst Examples.historySub_sndOnEfst
  Examples.generatesSub_tfae_on_sndOnEfst Examples.generatesSub_iff_on_sndOnEfst
  -- Generation of a subpartition is not monotone in `C` (the paper's remark after
  -- Proposition 21), so Proposition 20 clause 7's second conjunct is load-bearing.
  Examples.indDiag Examples.historySub_indDiag Examples.generatesSub_empty_indDiag
  Examples.not_generatesSub_fst_indDiag Examples.generatesSub_not_superset_monotone
  Examples.clause7_second_conjunct_loadbearing
  -- `hE : X.dom = Y.dom` in Proposition 23 clause 2 is load-bearing, and the history it
  -- computes is the nondegenerate `{sndFactor}` rather than `∅`.
  Examples.Efalse Examples.botInfIndEfalse Examples.historySub_botInfIndEfalse
  Examples.historySub_spec_hE_loadbearing
  -- `Subset` (inclusion as sets of blocks) both ways, and `dd:subpartition`'s bijection
  -- with `Σ E, Setoid E` exhibited on a concrete `E`.
  Examples.subset_indDiag_xorPart Examples.not_subset_sndOnEfst_snd
  Examples.ofSetoidOn_bot_Efst Examples.roundtrip_sndOnEfst Examples.roundtrip_bot_Efst
  Examples.restrict_restrict_sndOnEfst
  -- Lemmas 1 and 2 instantiated: their hypothesis sets are satisfiable, and Lemma 2's two
  -- sides are each computed to `B` without invoking Lemma 2 (the left from Proposition 22,
  -- the right from Lemma 1), so the pair cross-checks Lemma 2 on the witness.
  Examples.historySub_ofSetoid_fstFactor Examples.historySub_ofSetoid_sndFactor
  Examples.historySub_disjoint_coord Examples.lemma1_coordFS Examples.lemma1_coordFS'
  Examples.lemma2_lhs_coordFS Examples.lemma2_rhs_coordFS
  -- §4.3: restriction can entangle, so `OrthogonalGiven` is neither empty nor total and is
  -- not implied by Definition 18; Proposition 25 exhibited on the witness, and Theorem 2
  -- partly so.  Read the Theorem 2 witnesses for exactly what they are: only decomposition
  -- and weak union have concrete instances, and `thm2_weakUnion_coordFS` takes `W = Y`, so
  -- contraction, composition and symmetry have no concrete instantiation here.  The
  -- endpoint `orthogonalGiven_semigraphoid` carries all five clauses; the witnesses meter
  -- two of them.
  Examples.fstOnEdiag Examples.sndOnEdiag
  Examples.historySub_fstOnEdiag Examples.historySub_sndOnEdiag
  Examples.not_orthogonalGivenSet_Ediag Examples.Ediag_mem_xorPart_classes
  Examples.not_orthogonalGiven_fst_snd_xorPart Examples.orthogonalGiven_fst_snd_top
  Examples.orthogonalGiven_nondegenerate Examples.not_orthogonalGiven_fst_fst_top
  Examples.orthogonalGiven_fst_fst_fst
  Examples.thm2_decomposition_coordFS Examples.thm2_weakUnion_coordFS
  -- Those two are instantiated at degenerate arguments (`W = ⊤`, resp. `W = Y`), so each
  -- of their conclusions is a fact §4.3 already has; their docstrings say so.  The
  -- non-degenerate instance conditions on `xorPart` and needs partitions of *mixed* type,
  -- because `fstFactor`, `sndFactor`, `xorPart`, `Dis_S` and `Ind_S` each restrict
  -- uniformly — all-discrete or all-indiscrete — to the two blocks of any 2+2 partition, so
  -- no two of them can trade roles across blocks.  `diagPart`, `orPart` and `andPart` do
  -- trade: `orthogonalGiven_diagPart_orAnd_xorPart` is `X ⊥^F (Y ∨_S W) | Z` with the left
  -- argument carrying the diagonal block and the right the antidiagonal one, certified
  -- two-sided by `orthogonalGiven_diagPart_orAnd_xorPart_two_sided` — neither restricted
  -- history is empty on both blocks — so Theorem 2's decomposition, contraction and
  -- composition clauses all do work on it.  Clauses 4 and 5 had no concrete instance
  -- before; their second input is the auxiliary `diagPart ⊥^F xorPart | Z`, so neither is
  -- the decomposition run backwards.
  Examples.diagPart Examples.orPart Examples.andPart
  Examples.orthogonalGiven_diagPart_orAnd_xorPart
  Examples.orthogonalGiven_diagPart_orAnd_xorPart_two_sided
  Examples.thm2_decomposition_coordFS_xorPart Examples.thm2_contraction_coordFS
  Examples.thm2_composition_coordFS
  -- The degenerate corners of Definitions 26-27, recorded so a client does not rediscover
  -- them: conditioning on `∅` or on `Dis_S` makes every pair orthogonal.
  Examples.orthogonalGivenSet_empty Examples.orthogonalGiven_bot
  -- §5.2: factoring the characteristic polynomial (FiniteFactoredSets/Factoring.lean).
  -- `irr` is Definition 35; Proposition 29 is the triple "members nonempty, pairwise
  -- disjoint, cover `B`", which under `dd:partition` is what "is a partition of the set
  -- `B`" means (`irr_isPartition` restates it as a `Subpartition`, and is machinery rather
  -- than a node).  Propositions 30 and 31 together are the factorization of `Q^F_E` into
  -- irreducibles.  Propositions 30 and 31 are where `[Finite S]` — finite *size*, not just
  -- finite dimension — is genuinely consumed, for the reason recorded under `dd:poly`.
  -- Proposition 29 is not: its proof is the minimal-element argument over subsets of `B`
  -- plus the `chimeraImage` closure lemmas, so it carries `Finite F.B` alone and holds
  -- over an infinite `S` — and, unlike the §5.1 relaxations, non-degenerately.
  FactoredSet.irr FactoredSet.irr_partition
  FactoredSet.Q_eq_finprod_poly_irr FactoredSet.irreducible_poly_of_mem_irr
  -- §5.4-§5.5: probability and the fundamental theorem
  -- (FiniteFactoredSets/Probability.lean).  Definition 36 is `ProbDist`, the paper's own
  -- elementary four-clause structure on `𝒫(S) → ℝ` (`dd:probability`; no measure theory
  -- stands in for it), and Definition 37 is the predicate `IsDistribution` on one.  Both
  -- §5.4-§5.5 theorems carry `[Finite S]`: Proposition 32 sums over `E ⊆ S`, and Theorem 3
  -- routes through Lemma 3, so this is the same `dd:poly` boundary as §5.1-§5.2 rather
  -- than a new hypothesis.  Theorem 3's converse is the only paper-node proof that
  -- *constructs* a distribution rather than quantifying over one — the paper's `P_f`, built
  -- from a strictly positive weight function — so the two directions have genuinely
  -- different content.  (The consumer surface also supplies `ProbDist.diracAt`, and
  -- `Examples` builds `uniform`, `biased`, `diagDist`, `unitDist` and `boolUniform`; none
  -- of those is a paper node.)
  ProbDist FactoredSet.IsDistribution
  FactoredSet.isDistribution_iff FactoredSet.orthogonalGiven_iff_forall_isDistribution
  -- §5.1-§5.2 on `coordFS`: the characteristic polynomial computed outright.  `vfst`/`vsnd`
  -- are the four variables of `Poly^{coordFS}` that ever occur — under `dd:partition` a
  -- block *is* a subset of `S`, hence a variable of the ring verbatim.  `Q_coordFS_univ_eq`
  -- expands Definition 31 to a four-term polynomial with no `finsum`/`finprod` left, and
  -- the two facts beside it rule out the degenerate readings: `Q^F_S` is not `0`, and no
  -- variable has degree above one in it (Corollary 1 at work).
  Examples.vfst Examples.vsnd
  Examples.Q_coordFS_univ_eq Examples.Q_coordFS_univ_ne_zero
  Examples.degreeOf_Q_coordFS_univ_le_one
  -- Definition 33 is an *image*, so coincident monomials collapse: `S` has four points and
  -- `poly^F_{fst}(S)` has two summands.  That collapse is the subtlety Proposition 26 has
  -- to rule out at `C = B`, and `mono_coordFS_basis_injective` is the ruling-out on the
  -- witness (proved by separating evaluation, not by citing Proposition 3).
  Examples.mono_singleton_fst_true_false
  Examples.poly_singleton_fst_univ Examples.poly_singleton_snd_univ
  Examples.mono_coordFS_basis_injective
  -- Proposition 26 on the witness, as a cross-check pair plus a separate application:
  -- `Q_coordFS_univ_eq` and `poly_coordFS_basis_univ_eq` each compute their own side to
  -- the same explicit polynomial and neither mentions `Q_eq_poly`, so
  -- `prop26_coordFS_crosscheck` re-derives the proposition rather than echoing it;
  -- `prop26_coordFS_applied` is the endpoint instantiated, which is a different claim.
  Examples.poly_coordFS_basis_univ_eq
  Examples.prop26_coordFS_crosscheck Examples.prop26_coordFS_applied
  -- Definition 35 computed at two subsets, with different answers.  At `E = S` the
  -- irreducible parts are the two singletons (the minimality clause is *vacuous* at a
  -- singleton — `∅` is the only strict subset and it is not nonempty — so what excludes
  -- `C = B` is that `{fstFactor}` already fixes `S`).  On the diagonal neither coordinate
  -- alone fixes `Ediag`, so the only irreducible part is the whole basis: the §5 shadow of
  -- the §4 fact that restriction entangles.
  Examples.mem_irr_singleton_fst_univ Examples.mem_irr_singleton_snd_univ
  Examples.irr_coordFS_univ
  Examples.chimeraImage_singleton_fst_Ediag_ne Examples.chimeraImage_singleton_snd_Ediag_ne
  Examples.irr_coordFS_Ediag
  -- Proposition 30 on the witness, the same cross-check shape: the factorization at `E = S`
  -- computed by expanding both sides (no mention of `Q_eq_finprod_poly_irr`), beside the
  -- endpoint applied at `S` and at `Ediag`, where the product degenerates to one factor and
  -- so agrees with Proposition 26 there.
  Examples.Q_coordFS_univ_eq_mul_poly
  Examples.prop30_coordFS_univ_applied Examples.prop30_coordFS_Ediag_applied
  -- §5 at `E = Efst`, a *third* subset, where Definitions 31 and 34 take values distinct
  -- from both earlier ones: `poly^F_{fst}(Efst)` collapses to one variable while
  -- `poly^F_{snd}(Efst)` keeps two, so Propositions 26 and 30 factor `Q^F_{Efst}` into two
  -- *different* polynomials (at `E = S` the two factors are symmetric; at `Ediag` there is
  -- one).  `Irr^F(Efst)` is the two singletons again — so `Irr^F` agreeing at two subsets
  -- does not mean the factorizations do.
  Examples.poly_singleton_fst_Efst Examples.poly_singleton_snd_Efst
  Examples.Q_coordFS_Efst_eq Examples.poly_coordFS_basis_Efst_eq
  Examples.prop26_coordFS_Efst_applied Examples.prop26_coordFS_Efst_crosscheck
  Examples.irr_coordFS_Efst
  Examples.prop30_coordFS_Efst_applied Examples.prop30_coordFS_Efst_crosscheck
  -- Proposition 27 at a nontrivial split — `C₀ = {fstFactor}`, `C₁ = {sndFactor}` disjoint
  -- and nonempty with `C₀ ∪ C₁ = B`, and `E₀ = Efst ≠ S = E₁` — applied, cross-checked by
  -- computation (no mention of `poly_union_chimeraImage`), and with the chimera's argument
  -- order pinned executably: the reversed reading `χ^F_{C₀}(E₁, E₀)` is *false* here.
  Examples.prop27_coordFS_applied Examples.prop27_coordFS_crosscheck
  Examples.prop27_reversed_false
  -- Proposition 28 is not vacuous on the witness, and its conclusion is doing work.
  -- `poly^F_{fst}(S)` really divides `Q^F_S` (computed, not via the endpoint).  The
  -- conclusion's `r · poly^F_C(E)` shape is *not* inventoried at that divisor, because
  -- asserting it at a `poly^F_C(E)` is a triviality — provable for every `C ⊆ B` and every
  -- `E` with none of the proposition's hypotheses (the `example` beside the divisor in
  -- Examples.lean is the probe).  The informative instances are the two below: at
  -- `2 · poly^F_{fst}(S)` the divisor is no `poly^F_C(S)` at all, so the real coefficient
  -- `r` cannot be dropped; and at a nonzero constant the returned `C` is forced to `∅`.
  Examples.poly_singleton_fst_dvd_Q_coordFS_univ
  Examples.prop28_coordFS_scaled_applied Examples.prop28_r_loadbearing
  Examples.prop28_coordFS_const_applied Examples.prop28_const_forces_empty
  -- Proposition 29 applied at both computed subsets, each cross-checked against the
  -- computed `Irr^F` without mentioning `irr_partition`; and its §4 restatement
  -- `irr_isPartition` instantiated, so the `Subpartition` it promises is constructed.
  -- The two cross-checks state the endpoint's own third conjunct, `⋃₀ Irr^F(E) = B`, and
  -- reach it by rewriting with the computed `Irr^F(E)`; they are not the generic set
  -- identities `⋃₀ {{fst}, {snd}} = B` / `⋃₀ {B} = B`, which mention no `Irr^F` and so
  -- would check nothing.
  Examples.prop29_coordFS_univ_applied Examples.sUnion_irr_coordFS_univ_crosscheck
  Examples.prop29_coordFS_Ediag_applied Examples.sUnion_irr_coordFS_Ediag_crosscheck
  Examples.irr_isPartition_coordFS_univ_applied
  -- Proposition 31 applied to both irreducible parts, with the two negatives that stop it
  -- being vacuous: neither factor is a unit, and `Irreducible` is not total on this ring —
  -- `Q^F_S` itself is reducible.
  Examples.prop31_coordFS_fst_applied Examples.prop31_coordFS_snd_applied
  Examples.not_isUnit_poly_singleton_fst_univ Examples.not_isUnit_poly_singleton_snd_univ
  Examples.not_irreducible_Q_coordFS_univ
  -- The three §5.1 endpoints the computed facts above shadow but never instantiate,
  -- applied on the witness.
  Examples.Q_ne_zero_coordFS_applied Examples.degreeOf_Q_le_coordFS_applied
  Examples.vars_disjoint_coordFS_applied
  -- The `E.Nonempty` hypotheses of §5 are load-bearing: at `E = ∅` both `Q^F_∅` and every
  -- `poly^F_C(∅)` are `0`, and Propositions 28, 30 and 31 each fail outright (30's on the
  -- zero-dimensional `unitFS`, where `Irr^F(∅) = ∅` makes the product `1`).  Proposition
  -- 29's `hE` is the exception, and `irr_partition_holds_at_empty` is the computation
  -- backing that disclosure rather than a load-bearing claim: it states all three of
  -- Proposition 29's conjuncts at `E = ∅`, computed from `irr_coordFS_empty`.
  Examples.poly_empty_eq_zero Examples.Q_coordFS_empty Examples.irr_coordFS_empty
  Examples.irr_partition_holds_at_empty
  Examples.prop28_hE_loadbearing Examples.prop30_hE_loadbearing
  Examples.prop31_hE_loadbearing
  -- `poly` is total in `C`, so it takes a junk value off the paper's `C ⊆ B`.  Recorded so
  -- that nobody reads a §5 statement as covering it: at `C = {Ind_S}` it is a single
  -- variable, and `Ind_S ∉ B`, so no §5.1-§5.2 hypothesis is satisfied by it.
  Examples.poly_top_univ_junk Examples.top_notMem_coordFS_basis
  -- §5.3-§5.5 on `coordFS`: Definition 31 at the remaining blocks Lemma 3 and Theorem
  -- 3 quantify over — the singleton `{s}`, every block of each coordinate factor (with the
  -- `sndFactor` block `[·]₂ = true` named separately, since the §5.3 witnesses run at it),
  -- and the diagonal `Ediag`, which is where both verdicts flip.
  Examples.Q_coordFS_singleton Examples.Q_coordFS_vfst Examples.Q_coordFS_vsnd
  Examples.Q_coordFS_vsnd_true Examples.Q_coordFS_Ediag
  -- Lemma 3's clause 3 on the witness, as a cross-check pair plus a separate application,
  -- and the negative that stops it being a triviality.  The cross-check expands both
  -- products from Definition 31 and mentions no divisibility endpoint; the application
  -- feeds the §4.3 fact `fstFactor ⊥^F sndFactor | Ind_S` to Lemma 3's 1 → 3 direction.
  -- At the `xorPart` block `Ediag` clause 3 *fails*, separated by one `coordSep`
  -- evaluation (310 against 100) — the polynomial shadow of §4.3's entanglement.
  Examples.lemma3_clause3_coordFS_top_crosscheck
  Examples.lemma3_clause3_coordFS_top_applied
  Examples.lemma3_clause3_coordFS_Ediag_fails
  -- Lemma 3's clause 2 — the divisibility, which is reachable only through the `TFAE` —
  -- at the same two conditionings.  The cross-check exhibits the cofactor `Q^F_{(t,t)}`
  -- computed from Definition 31 and states the same divisibility the application projects
  -- with `.out 0 1`; on the diagonal divisibility fails, refuted by a single *zero* of the
  -- divisor (`coordZero`) rather than by the separating value `coordSep` supplies for
  -- clause 3.
  Examples.lemma3_clause2_top_crosscheck Examples.lemma3_clause2_top_applied
  Examples.lemma3_clause2_Ediag_fails
  -- Lemma 3's `3 → 1` direction run FORWARD, with its hypothesis discharged by computing
  -- clause 3 at every pair of blocks rather than assumed or contraposed.  This is the
  -- direction §5.5 consumes, and `orthogonalGiven_from_clause3` reaches
  -- `fstFactor ⊥^F sndFactor | Ind_S` by a route independent of Proposition 24's.
  Examples.clause3_fst_snd_top Examples.orthogonalGiven_from_clause3
  -- Definitions 36 and 37 inhabited, kept apart, and kept from naming one distribution.
  -- `uniform` (`P E = |E| / 4`) and `biased` (a product of two `1/3`-biased coins) are two
  -- *different* distributions on the factored set; `diagDist` (`P E = |E ∩ Ediag| / 2`) is
  -- a `ProbDist` and is *not* one, since it makes the two coordinates perfectly correlated
  -- (`P {(t,t)} = 1/2` against `P([s]_fst) · P([s]_snd) = 1/4`).  Without `diagDist`,
  -- Definition 37's product condition would be indistinguishable from decoration; without
  -- `uniform` and `biased`, Proposition 32 and Theorem 3 would have no exhibited
  -- inhabitant to quantify over here.  (The family is not in fact empty for any nonempty
  -- `S`: the point mass is a distribution on every factored set of finite dimension,
  -- `FactoredSet.isDistribution_diracAt` in the conveniences block below.  What the
  -- witnesses supply is a *computed* inhabitant, and a second one that is not the first.)
  Examples.uniform Examples.uniform_isDistribution
  Examples.biased Examples.biased_isDistribution Examples.biased_ne_uniform
  Examples.diagDist Examples.not_isDistribution_diagDist
  -- Proposition 32 at two subsets and under two distributions.  At `E = Efst` the
  -- polynomial has two terms, so the evaluation is a genuine sum — equal summands under
  -- `uniform`, unequal ones under `biased`; at the three-element `E3` it has three terms
  -- taking two distinct values.  Each is cross-checked by computing both sides from
  -- Definitions 31 and 36, and separately applied.
  Examples.prop32_coordFS_Efst_crosscheck Examples.prop32_coordFS_Efst_applied
  Examples.prop32_biased_Efst_crosscheck Examples.prop32_biased_Efst_applied
  Examples.E3 Examples.Q_coordFS_E3
  Examples.prop32_biased_E3_crosscheck Examples.prop32_biased_E3_applied
  -- Theorem 3 in both directions on the pair §4.3 already separates.  Forward at
  -- `Z = Ind_S`: cross-checked (`1/2 · 1/2 = 1/4 · 1`, computed) and applied (from
  -- `orthogonalGiven_fst_snd_top`, with no computation).  Backward at `Z = xorPart`:
  -- `thm3_coordFS_Ediag_fails` computes the failure (`1/16` against `1/8`),
  -- `thm3_coordFS_xorPart_witness` names the distribution and blocks realizing the
  -- theorem's existential, and `thm3_coordFS_xorPart_applied` derives that same
  -- existential from `not_orthogonalGiven_fst_snd_xorPart` through the endpoint.
  Examples.thm3_coordFS_top_crosscheck Examples.thm3_coordFS_top_applied
  Examples.thm3_coordFS_Ediag_fails
  Examples.thm3_coordFS_xorPart_witness Examples.thm3_coordFS_xorPart_applied
  -- Theorem 3's converse run FORWARD as well: independence in every distribution on
  -- `coordFS`, obtained from `clause3_fst_snd_top` through Proposition 32 without invoking
  -- Lemma 3 or Theorem 3's forward direction, yields conditional orthogonality.  This is
  -- the third independent derivation of `fstFactor ⊥^F sndFactor | Ind_S` in the file.
  Examples.orthogonalGiven_from_independence
  -- The degenerate carriers of Definitions 36-37, which say where the quantifiers of
  -- Proposition 32 and Theorem 3 are and are not vacuous.  Over `Empty` there is no
  -- distribution at all, and both sides of Theorem 3 hold there (a partition of `∅` has no
  -- blocks) — so the theorem is consistent, not informative.  Over `Unit` there is exactly
  -- one distribution, and it *is* a distribution on the zero-dimensional `unitFS`, the
  -- empty product being `1`.
  Examples.isEmpty_probDist_empty Examples.orthogonalGiven_emptyFS
  Examples.unitDist Examples.subsingleton_probDist_unit Examples.unitDist_isDistribution
  -- …and Theorem 3's right-hand side is not universally true: one dimension suffices.  On
  -- `boolFS` every `ProbDist Bool` is a distribution on the factored set (`B = {Dis_S}`
  -- makes Definition 37 no constraint), and the uniform one refutes `Dis_S ⊥^F Dis_S |
  -- Ind_S` — `1/2 · 1/2` against `0 · 1`.
  Examples.boolUniform Examples.boolFS_isDistribution
  Examples.not_orthogonalGiven_bot_bot_top_boolFS
  -- §7.2: Conjecture 1 (FiniteFactoredSets/Conjecture.lean) and its finite-dimensional /
  -- infinite-dimensional witnesses (FiniteFactoredSets/InfiniteExamples.lean).
  -- `FundamentalTheoremFiniteDim` is a `def … : Prop` — Theorem 3 with `[Finite S]` weakened
  -- to `[Finite F.B]` — and is deliberately **not proved**: no declaration in the repo has
  -- that type.  It is used in exactly three places, each an `example` that takes it *as a
  -- hypothesis* and instantiates it at a witness: two in `InfiniteExamples` and one in
  -- `APITests/FiniteFactoredSets.lean`, the last being the client-side half.  So listing it here
  -- checks the statement's own axiom profile, exactly as the block already does for the
  -- other `def … : Prop`s above (`OrthDatabase.Consistent`, `FactoredSet.Generates`).  Its
  -- finite restriction needs no declaration of its own: it *is* Theorem 3
  -- (`FactoredSet.orthogonalGiven_iff_forall_isDistribution`, inventoried above).
  FundamentalTheoremFiniteDim
  -- The witnesses.  `natBoolFS` is dimension 2 over the *infinite* carrier `ℕ × Bool`, so
  -- `Finite natBoolFS.B` holds (by `Set.Finite.to_subtype`, not by Proposition 6, which
  -- runs the other way) while `¬ Finite (ℕ × Bool)`: it is inside Conjecture 1's scope and
  -- outside Theorem 3's, which is what stops the conjecture from being a restatement of
  -- the theorem.  §3-§4 is then run on it — Proposition 13 clause 4 for both factor
  -- histories, Definition 18 computed from those histories, Proposition 14 as an
  -- independent re-derivation, Proposition 15 clause 4 as the negative, Proposition 24 for
  -- Definition 27 at `Ind_S` — with `Finite B` alone and no `Finite S` anywhere, which is
  -- `dd:finiteness-minimal` discharged by construction rather than by inspection.
  -- `isDistribution_diracAt_natBoolFS` makes Definition 37 inhabited there, but
  -- inhabitation is not what makes the conjecture's right-hand side a constraint:
  -- `diracAt_rhs_trivial` shows a point mass satisfies Theorem 3's right-hand-side identity
  -- for *arbitrary* sets, so a dirac-only family would make that side constantly true and,
  -- against `not_orthogonal_natFactor_self`, would refute Conjecture 1 rather than exhibit
  -- it.  `rich` — uniform on the four points `{0,1} × Bool` — is the discriminating member:
  -- a Definition-37 distribution on `natBoolFS` (`rich_isDistribution`) that falsifies the
  -- right-hand-side clause in the shape the conjecture quantifies it
  -- (`rich_discriminates`), so `both_sides_fail_at_natFactor_self` computes both sides of
  -- the biconditional at one triple.  This is the infinite-carrier counterpart of
  -- `Examples.not_orthogonalGiven_bot_bot_top_boolFS`.
  InfiniteExamples.natFactor InfiniteExamples.boolFactor
  InfiniteExamples.natFactor_ne_boolFactor InfiniteExamples.natBoolBasis
  InfiniteExamples.natBoolBasis_nontrivial InfiniteExamples.natBoolBasis_existsUnique
  InfiniteExamples.natBool_isFactorization InfiniteExamples.natBoolFS
  InfiniteExamples.natBoolFS_B InfiniteExamples.natFactor_mem
  InfiniteExamples.boolFactor_mem InfiniteExamples.singleton_natFactor_subset
  InfiniteExamples.singleton_boolFactor_subset InfiniteExamples.natBoolFS_B_finite
  InfiniteExamples.not_finite_natBool
  InfiniteExamples.history_natFactor InfiniteExamples.history_boolFactor
  InfiniteExamples.orthogonal_natFactor_boolFactor
  InfiniteExamples.not_orthogonal_natFactor_self
  InfiniteExamples.orthogonalGiven_natFactor_boolFactor_top
  InfiniteExamples.isDistribution_diracAt_natBoolFS
  InfiniteExamples.diracAt_rhs_trivial InfiniteExamples.richSupport InfiniteExamples.rich
  InfiniteExamples.rich_apply InfiniteExamples.rich_isDistribution
  InfiniteExamples.rich_discriminates InfiniteExamples.both_sides_fail_at_natFactor_self
  -- `infFS` is the other side of the line: the coordinate factorization of `ℕ → Bool`,
  -- whose basis is infinite (`infFS_B_infinite`, `not_finite_B`).  Up to
  -- `𝒫(ℕ) ≃ (ℕ → Bool)` it is the factored set §7.2 uses to say it does *not* expect the
  -- fundamental theorem past finite dimension; the paper's §7.2 examples are out of scope
  -- by the ruling in `KNOWLEDGE.md`, so no node is claimed for it and it carries no
  -- annotation.  `not_isDistribution_diracAt_infFS` is what makes it earn its place: the
  -- `[Finite F.B]` on `FactoredSet.isDistribution_diracAt` is load-bearing, because with
  -- `B` infinite the family in Definition 37 has infinite multiplicative support and
  -- `finprod` returns `1` rather than the elementary product.  So past finite dimension
  -- Definition 37's product is not the product it is written as — the concrete reason the
  -- conjecture is stated at finite dimension and not beyond.  The second reason is
  -- `not_isLeast_history_evEq`: **Proposition 12's conclusion is false** on `infFS`.  For
  -- the eventually-equal partition `evEq`, dropping any single coordinate from `B` still
  -- generates it, so `h^F(evEq) = ∅` (`history_evEq`) while `∅` generates only `Ind_S` and
  -- `evEq ≠ Ind_S` (`evEq_ne_top`).  So `[Finite F.B]` on `FactoredSet.history_isLeast` is
  -- load-bearing, and past finite dimension `history` is defined but is no longer the
  -- object §3.2 onwards reasons about — the justification `History.lean`'s module doc gives
  -- for that binder is now compiled rather than asserted.
  InfiniteExamples.memFactor InfiniteExamples.infBasis
  InfiniteExamples.memFactor_injective InfiniteExamples.infBasis_nontrivial
  InfiniteExamples.infBasis_existsUnique InfiniteExamples.infFS
  InfiniteExamples.infFS_B InfiniteExamples.infFS_B_infinite
  InfiniteExamples.not_finite_B
  InfiniteExamples.not_isDistribution_diracAt_infFS
  InfiniteExamples.evEq InfiniteExamples.evEq_ne_top InfiniteExamples.history_evEq
  InfiniteExamples.not_generates_history_evEq InfiniteExamples.not_isLeast_history_evEq
  -- §6.1: factored set models and orthogonality databases
  -- (FiniteFactoredSets/Inference.lean).  Definition 38's `Model` bundles the carrier, its
  -- factored set, the map to `Ω`, and — because the paper says *finite* factored set — a
  -- `Finite` field, so Definition 45's quantifier over models is the paper's (`dd:model`).
  -- One precision: `Model : Type u → Type (u+1)` puts the carrier `S` in `Ω`'s own
  -- universe, so "every model" below means every model with a `Type u` carrier.  That is
  -- forced by Lean and mathematically empty — every carrier is finite, hence equivalent to
  -- one in `Type 0` — but the repo has no transport lemma along such an equivalence, so it
  -- is disclosed rather than discharged (`dd:model`).
  -- Definition 39's three preimages are Mathlib-rendered (README table); `Model.pullback`
  -- names the partition one and is a convenience, not a paper endpoint.  Definition 41 has
  -- two carriers, one per written form, as Definitions 18 and 19 do.  `Model` is spelled
  -- with its root prefix: `ProvabilityLogic/Kripke/Basic.lean` declares a root-namespace
  -- `Model`, so the bare name is ambiguous under this block's `open FiniteFactoredSets in`.
  FiniteFactoredSets.Model OrthDatabase OrthDatabase.Orth OrthDatabase.NotOrth
  OrthDatabase.Models OrthDatabase.Consistent OrthDatabase.Complete OrthDatabase.StrictlyBefore
  -- §6.2, Example 1 (FiniteFactoredSets/InferenceExamples.lean).  `Example1.D` is the
  -- database of the worked example; Propositions 33 and 34 are consistency (witnessed by
  -- the identity model on `(Ω, {X, V})`) and the inferred order `X <_D Y`, which quantifies
  -- over every model of `D` — in the §6.1 sense above, `Type u` carriers — and so is a
  -- universal claim, not an instantiated one.
  Example1.D Example1.D_consistent Example1.strictlyBefore_X_Y
  -- §6.2, Example 2 (FiniteFactoredSets/InferenceExamples.lean).  `Example2.D` is the
  -- database of the paper's second worked example; Propositions 35 and 36 are its
  -- consistency and the temporal order it forces.  Proposition 35 is discharged by the
  -- paper's own twelve-point model — `Example2.model`, on the carrier
  -- `Bool × Bool × Option Bool` whose `none` third coordinate is the paper's two-bit
  -- string — so the existential of Definition 43 is met by a construction, not a
  -- stand-in.  Proposition 36 quantifies over every model of `D` in that same sense, so it
  -- needs no witness of its own; what makes it non-vacuous is Proposition 35, which
  -- supplies one.
  Example2.D Example2.D_consistent Example2.strictlyBefore_X_Y_Z
  -- §6.1 on the witnesses (FiniteFactoredSets/Examples.lean).  Definitions 42-45 quantify
  -- over *models* of a sample space, not over factored sets, so none of the §2-§5 witnesses
  -- above touches them.  Definition 38 is inhabited four ways: the two identity models, the
  -- non-injective `fstModel` (`coordFS` observed through `Prod.fst`, where `S` has four
  -- points and `Ω` two — the latent structure Definition 38 exists to allow), and the
  -- one-point `pointModel`.  Definition 39 is computed on the two that are not the
  -- identity, and it moves in both directions: `f⁻¹(Dis_Ω)` can be a *factor* of `S`
  -- (`pullback_fstModel_bot`, whose §3 history is the singleton) and it can collapse every
  -- partition of `Ω` to `Ind_S` (`pullback_pointModel`).
  -- `voidModel` is the fifth and degenerate end of Definition 38: the empty carrier, legal
  -- because `Model`'s `Finite S` field is satisfied by `Empty`.  It is what makes
  -- `not_strictlyBefore_of_notOrth_empty` true — it models every database whose `N` is
  -- empty, and over it every history is `∅`, so Definition 45 infers nothing.  That is the
  -- exact dual of `totalDB_consistent`: `O` costs a database no consistency and buys it no
  -- inferences, `N` does both.
  Examples.coordModel Examples.boolModel Examples.fstModel Examples.pointModel
  Examples.voidModel
  Examples.pullback_fstModel_bot Examples.history_pullback_fstModel_bot
  Examples.pullback_pointModel
  -- Definitions 40-44 on six databases.  Two natural misreadings are ruled out here.
  -- First, `Consistent` is cheap on `O` alone: `totalDB` asserts *every* triple orthogonal
  -- and is still consistent, because the one-point model satisfies all of `O` at once
  -- (`unitFS` has no factors) — so it is `N` that constrains, and
  -- `nonconstDB_forces_nonconstant` is the mechanism in its simplest form, a single
  -- `N`-entry forcing every model's map to be non-constant through Proposition 25.
  -- Second, `Consistent` and `Complete` are independent **in both directions**, and each
  -- direction is now inhabited: `emptyDB` is consistent and not complete,
  -- `completeInconsistentDB` — asserting every triple both ways — is complete and not
  -- consistent, and `totalDB` is both.  `coordDB` repeats the consistent-and-not-complete
  -- corner with both of its clauses non-empty, and `contradictoryDB` — asserting one triple
  -- both ways — has no model at all, which is what makes Definition 43's existential a real
  -- condition.
  -- `models_coordDB` is the Definition 42 computation proper, discharging both clauses on
  -- the identity model of `coordFS` from §4.3's own computations on that witness.
  Examples.emptyDB Examples.models_emptyDB Examples.emptyDB_consistent
  Examples.not_emptyDB_complete
  Examples.not_strictlyBefore_of_notOrth_empty Examples.not_emptyDB_strictlyBefore
  Examples.contradictoryDB Examples.not_contradictoryDB_consistent
  Examples.totalDB Examples.totalDB_complete Examples.totalDB_consistent
  Examples.completeInconsistentDB Examples.completeInconsistentDB_complete
  Examples.not_completeInconsistentDB_consistent
  Examples.nonconstDB Examples.nonconstDB_consistent
  Examples.nonconstDB_forces_nonconstant
  Examples.coordDB Examples.models_coordDB Examples.coordDB_consistent
  Examples.not_coordDB_complete
  -- Definition 45 from both sides.  On a *consistent* database it is irreflexive, since
  -- `<^F` is a strict inclusion of histories; on an *inconsistent* one it is vacuously
  -- total, quantifying over models that do not exist.  That second fact is the trap the
  -- paper's own ordering guards against — Propositions 33 and 35 (consistency) come before
  -- Propositions 34 and 36 (the inference).  The informative positive instances of
  -- Definition 45 are those two propositions in `InferenceExamples.lean`; nothing here
  -- stands in for them, and `Examples.lean` does not import that file.  The two generic
  -- statements these instantiate are `OrthDatabase.not_strictlyBefore_self_of_consistent` and
  -- `OrthDatabase.strictlyBefore_of_not_consistent`, on the consumer surface below.
  Examples.not_nonconstDB_strictlyBefore_self Examples.contradictoryDB_strictlyBefore_all
  -- §7.3: embedded observations, counterfactability, conditional time
  -- (FiniteFactoredSets/EmbeddedAgency.lean).  Five definitions and no theorem: §7 states
  -- nothing about them, so the whole non-vacuity burden falls on the witnesses below.
  -- Definition 46's auxiliary `X_E` is `FactoredSet.eventPartition`, which carries no node
  -- annotation and is therefore not listed here — the paper introduces it inside the
  -- statement of Definition 46 rather than as a numbered node, and it is an auxiliary in the
  -- same sense `Model.pullback` is.  Two renderings to record.  First, `eventPartition E` is
  -- `Setoid.comap (· ∈ E) ⊥` — agreement on membership in `E` — so the paper's case split
  -- (`{S}` when `E` is `∅` or `S`, `{E, S \ E}` otherwise) is absorbed into one formula and
  -- recovered by computation on the witnesses.  Second, Definition 47's family `A_i` is
  -- indexed by the *blocks* of `X` rather than by a numbering `{x_0, …, x_{n-1}}` of them,
  -- and the paper's `⋁_S({A_i})` is `sInf (Set.range ·)` (`dd:order-flip`); indexing by
  -- blocks changes nothing and needs no finiteness.  Per `dd:finiteness-minimal` none of the
  -- five carries a finiteness hypothesis — each is a formula in
  -- `history`/`historySub`/`Orthogonal`/`OrthogonalGiven`, all defined for every factored
  -- set — and Definition 50's `h^F(X | E)` is `historySub ((ofSetoid X).restrict E)`, the
  -- Definition 26 rendering reused.
  FactoredSet.Observes FactoredSet.ObservesPartition FactoredSet.Counterfactable
  FactoredSet.CounterfactableRel FactoredSet.BeforeGivenSet
  -- §7.3 on the witnesses (FiniteFactoredSets/Examples.lean).  The paper's case split for
  -- `X_E` is recovered in three pieces: `Ind_S` at both degenerate ends, and at a proper
  -- nonempty `E` the blocks are exactly `E` and `S \ E`.  `eventPartition_compl` records
  -- that `X_E` cannot tell `E` from its complement, which is why Definition 46's two clauses
  -- do not repeat each other; on `coordFS`, `X_E` at a block of a coordinate factor is that
  -- factor, which is what makes the Definition 46 instances computable from §3.3 and §4.3
  -- material already on the witness.
  Examples.eventPartition_empty Examples.eventPartition_univ
  Examples.eventPartition_classes Examples.eventPartition_compl
  Examples.eventPartition_vsnd Examples.eventPartition_vfst
  -- Definition 46 inhabited, and **both** clauses shown load-bearing at the two failure
  -- shapes the paper itself names.  The positive instance reads the first coordinate as the
  -- agent's action, "the second coordinate is `true`" as the event, and the second
  -- coordinate as the world model.  `not_observes_snd_vsnd_true` is the transparent-Newcomb
  -- shape (Drescher): the action *is* the event, so clause 1 fails for every world model.
  -- `not_observes_snd_snd_Efalse` is the counterfactual-mugging shape (Nesov): clause 1
  -- holds and clause 2 fails, because on the branch where the event fails the action still
  -- determines the whole world model.  Neither clause therefore implies the other.
  Examples.observes_fst_snd_vsnd_true Examples.not_observes_snd_vsnd_true
  Examples.not_observes_snd_snd_Efalse
  -- What `observes_fst_snd_vsnd_true` does *not* pin: at that `(W, E)` the complement is a
  -- block of `W`, so `W|Eᶜ` is indiscrete and clause 2 holds of **every** agent —
  -- `observes_snd_vsnd_true_iff` proves the collapse to clause 1 outright.  The witness
  -- with a substantive clause 2 is `observes_fst_snd_empty`: at `E = ∅` the complement is
  -- all of `S`, so clause 2 is the unconditional `fstFactor ⊥^F sndFactor` against a
  -- nonempty restricted history, and `not_observes_snd_snd_empty` is the matching failure.
  Examples.observes_snd_vsnd_true_iff Examples.observes_fst_snd_empty
  Examples.not_observes_snd_snd_empty
  -- Definition 47 inhabited at a two-block partition, with the constant family
  -- `A_x = fstFactor`, and tied to Definition 46 on an instance —
  -- `observes_and_observesPartition_vsnd_true` exhibits the same agent and world model
  -- observing the event `E` and the partition `X_E` — rather than by a general lemma, which
  -- the paper does not state either.  `observesPartition_top` is the corner that keeps the
  -- positive instance honest: `Ind_S` observes every partition with respect to every world
  -- model, so a Definition 47 witness says something only once its agent is nontrivial.
  -- A second honesty corner, disclosed rather than discharged by the two positive instances
  -- above: in both `observes_fst_snd_vsnd_true` and `observesPartition_fst_snd` the set the
  -- second clause conditions on is a *block* of the world model `W`, so `W|Eᶜ` is
  -- indiscrete, its history is empty, and clause 2 holds for **every** agent and every
  -- sub-agent family.  Those two therefore meter clause 1 and the inhabitation of
  -- Definition 47's `∃ As`, not the sub-agent decomposition.  A witness that meters clause 2
  -- needs `h^F(W|Eᶜ) ≠ ∅`, and a witness that meters the decomposition needs a
  -- *non-constant* family — at a constant family `sInf (Set.range As) = A` by
  -- `sInf_singleton`, so the `∃ As` does no work.
  Examples.classes_sndFactor Examples.observesPartition_fst_snd
  Examples.observes_and_observesPartition_vsnd_true Examples.not_observesPartition_snd
  Examples.observesPartition_top
  -- Both of those use a *constant* sub-agent family, where `⋁_S {Aᵢ} = A` is
  -- `sInf_singleton` and the decomposition does nothing; and at `W = X = sndFactor` clause
  -- 2 again collapses to clause 1 for every agent (`observesPartition_snd_snd_iff`).
  -- `observesPartition_fst_snd_nonconstant` is the instance where the family genuinely
  -- varies, with the non-constancy in the statement.  Its two values are comparable, and
  -- that is forced rather than lazy: clause 1 admits only `fstFactor` and `Ind_S` as agents
  -- for a two-block `X` on this carrier, and `Ind_S` is the only partition strictly coarser
  -- than a factor there — an incomparable family needs more than two factors.
  Examples.observesPartition_snd_snd_iff Examples.observesPartition_fst_snd_nonconstant
  -- Definitions 48-49 separated by the agreement partition ("do the two coordinates
  -- match?").  Definition 48 holds at a factor, at `Ind_S` and at `Dis_S`, and fails at the
  -- agreement partition for the paper's own reason: it is too coarse to specify the
  -- counterfactual, its history being the whole basis, so `⋁_S(h^F(X)) = Dis_S ≠ X`.
  -- Definition 49 is then implied by Definition 48 for every `W`
  -- (`FactoredSet.counterfactableRel_of_counterfactable`, general, in `EmbeddedAgency.lean`
  -- with the other §7.3 reductions), holds of the agreement partition relative to `Ind_S` —
  -- where `FactoredSet.counterfactableRel_top` shows the corner is general, so that instance
  -- alone would certify nothing — and *fails* of it relative to `fstFactor`, which is what
  -- makes Definition 49 neither empty nor total.
  Examples.counterfactable_fstFactor Examples.counterfactable_top
  Examples.counterfactable_bot Examples.not_counterfactable_xorPart
  Examples.counterfactableRel_fstFactor
  Examples.not_counterfactable_but_counterfactableRel_xorPart
  Examples.not_counterfactableRel_xorPart_fstFactor
  -- Definition 50 against Definition 19.  At `E = S` the two agree
  -- (`FactoredSet.beforeGivenSet_univ_iff`, general, in `EmbeddedAgency.lean`), and away
  -- from it they genuinely differ — the coordinate factors are incomparable in `≤^F`, yet on
  -- the diagonal each is before the other, which is the §7.3 shadow of §4.3's "restriction
  -- can entangle".  The negative and the two degenerate corners keep it from being read as
  -- total: given `∅` every pair is ordered, and `Ind_S` is before everything given anything.
  Examples.beforeGivenSet_fst_bot_univ
  Examples.beforeGivenSet_fst_snd_Ediag Examples.not_beforeGivenSet_fst_top_Ediag
  Examples.beforeGivenSet_corners
-- FFS-INVENTORY-END

/-! Tier-2 boundary structures for the Finite Factored Sets surface. -/
#assert_fields FiniteFactoredSets.IsFactorization
  nontrivial bijective
#assert_fields FiniteFactoredSets.FactoredSet
  B isFactorization
#assert_fields FiniteFactoredSets.Subpartition
  r symm' trans'
#assert_fields FiniteFactoredSets.ProbDist
  P nonneg empty univ additive
#assert_fields FiniteFactoredSets.Model
  S F f finite
#assert_fields FiniteFactoredSets.OrthDatabase
  O N

/-! ## Condensation (Eisenstat 2025) — endpoint inventory

Nodes are cited by printed number (`Paper node: \`Definition 3.1\``) read off the committed
text extraction `Condensation/notes/condensation-25-07.txt`; `scripts/check-condensation-nodes.py`
enforces validity, anchoring, and that every annotated declaration appears in one of the
two blocks below.  Status: **statements and proofs complete** as of M2 (landed
2026-08-18).  Every in-scope node of §2, §3, §3.1, §4 and §5 has a carrier, every carrier
is proved, and there is **no `sorry` anywhere in `Condensation/`**:
`scripts/check_sorry_ledger.py` enumerates every `sorryAx`-dependent declaration of the
library from the compiled environment and reports zero for this paper.  Consequently the
`CONDENSATION-PENDING` block below is **empty**, and the whole annotated surface is in the
`#assert_axioms_clean` block.  (Examples 5.1-5.3 carry no declaration; they are
illustrations rather than claims, and the coverage ruling that excludes them is on the
record as *proposed*, not settled — `scripts/check-condensation-nodes.py` therefore reports
39/42 rather than 42/42.)

This is **not** the same as the paper being `completed` in `scripts/papers.py`: that status
additionally requires a curated `Condensation/API.lean` boundary, client tests in
`APITests/`, a human read-through and a final fresh-context audit, none of which has
happened.  The roadmap is `Condensation/notes/roadmap.md`.  There are **no** residual
modeling substitutions: the
`dd:finite-range` narrowing was retired on 2026-08-17, and `Condensation.RVModel` is now
Definition 3.1 verbatim — a countable discrete probability space *with finite entropy*
(`ShannonInformation.FiniteEntropyMeasure`) carrying countable-discrete-range variables of
finite entropy.  See `Condensation/README.md`.

**Why there are two blocks: the staged inventory.**  This formalization reached the
paper's endpoints statement-first, and the second block is the mechanism that made that
honest.  A declaration may carry a `Paper node:` annotation because its *statement* is
final and is the paper's real endpoint, while its proof is still `sorry`.  Such a
declaration cannot be listed in `#assert_axioms_clean`: that command exists to catch
exactly a `sorryAx` dependency, and listing it would either fail the build or tempt someone
to weaken the check.  Dropping the `Paper node:` annotation instead would be a lie about
the statement's provenance, and the node checker would then also stop guarding the
statement.

**The pending block is empty by construction, and is retained deliberately.**  M2
discharged the last staged endpoint, so nothing is named there today.  It is kept, rather
than deleted, because it is a live gate in both directions: `check_sorry_ledger.py` fails
on a `sorryAx`-dependent declaration that is named in neither section *and* on a ledger
entry that no longer depends on `sorryAx`, so an empty block is an assertion that there is
nothing to stage, re-checked on every run.  Deleting it would remove the assertion, not
record it.  A future statement-first endpoint is staged by adding a line back.

So the annotated surface is split.  The `CONDENSATION-INVENTORY` block below is the
ordinary axiom gate.  The `CONDENSATION-PENDING` block that follows it is **pure Lean
comment** — it compiles to nothing and asserts nothing — and names, one per line with a
reason, every annotated endpoint that is not yet axiom-clean.  It is a declaration of
intent, not a discharge.

The pending block has **two sections**, separated by a `-- SECTION: …` marker line.  The
first names annotated endpoints.  The second, `consumers (un-annotated)`, names
declarations that depend on `sorryAx` but carry no `Paper node:` line at all — small
consequences of a staged theorem, which are not claims about the paper and so cannot be
annotated, but which a reader must still not mistake for proved.  Round 2 found three of
them living outside both blocks (R2-F22), which is precisely the drift the ledger exists to
prevent; `scripts/check_sorry_ledger.py` now enumerates every `sorryAx`-dependent
declaration of the library from the compiled environment and fails on any that is named in
neither section, so the two sections together are mechanically complete rather than
maintained by hand.

`scripts/check-condensation-nodes.py` (via the generic `pending_block` support in
`scripts/paper_nodes.py`, available to any paper) accepts an annotated declaration listed
in *either* block, and fences the staging with four hard failures: a name in both blocks,
a pending entry naming no annotated declaration (a stale entry outliving its endpoint), a
malformed pending line, and a non-empty pending block once `scripts/papers.py` registers
the paper `completed`.  A surviving non-empty block prints as a note carrying the count,
which is the number to watch shrink; it prints no such note now.  **Moving a name from the
pending block to the inventory block is what "M2 proved this endpoint" means**; the two
edits belong in the same commit as the proof, and M2 made the last of them. -/

-- CONDENSATION-INVENTORY-BEGIN
#assert_axioms_clean
  -- §2 conventions (Condensation/Probability.lean).  Definition 2.1 has three carriers:
  -- the Mathlib rendering `IsRandomVariable` and the "function of" conventions.
  Condensation.IsRandomVariable Condensation.FunctionOf Condensation.AEFunctionOf
  Condensation.AEFunctionOf.of_functionOf Condensation.AEFunctionOf.comp Condensation.AEFunctionOf.trans Condensation.AEFunctionOf.prodMk
  Condensation.AEFunctionOf.comp_measurePreserving Condensation.aeFunctionOf_self
  -- eq. (2.2): pullback invariance along probability-preserving maps.
  Condensation.identDistrib_comp_measurePreserving Condensation.entropy_comp_measurePreserving
  Condensation.mutualInfo_comp_measurePreserving Condensation.condEntropy_comp_measurePreserving
  Condensation.PPlus Condensation.PPlus.toFinset Condensation.PPlus.single Condensation.PPlus.le_iff Condensation.PPlus.lt_iff
  Condensation.interactionInfo Condensation.interactionInfo_comm Condensation.interactionInfo_swap Condensation.condInteractionInfo
  Condensation.GiryMeasurableSpace
  -- Proposition 2.5 (the determinism bridge), its converse and the iff, and the two
  -- entropy consequences §4 uses.
  Condensation.aeFunctionOf_of_condEntropy_eq_zero Condensation.condEntropy_eq_zero_of_aeFunctionOf
  Condensation.aeFunctionOf_iff_condEntropy_eq_zero Condensation.entropy_le_of_aeFunctionOf Condensation.entropy_pair_of_aeFunctionOf
  -- Definitions 3.1–3.4 (Condensation/Model.lean).
  Condensation.RVModel Condensation.RVModel.joint Condensation.RVModel.jointOn Condensation.RVModel.measurable_joint Condensation.RVModel.measurable_jointOn
  Condensation.contrib Condensation.above Condensation.strictAbove Condensation.contribIdx Condensation.mem_contrib_iff
  Condensation.contribIdx_eq_contrib_singleton Condensation.contribIdx_eq_above_singleton Condensation.strictAbove_subset_above
  Condensation.LatentModel Condensation.LatentModel.jointOn Condensation.LatentModel.jointContrib Condensation.LatentModel.jointAbove
  Condensation.LatentModel.jointStrictAbove Condensation.LatentModel.jointContribIdx Condensation.LatentModel.pullbackJoint
  Condensation.LatentModel.measurable_pullbackJoint
  Condensation.LatentModel.simpleScore Condensation.LatentModel.condScore Condensation.LatentModel.reconScore
  -- Non-vacuity witnesses (Condensation/Examples.lean): a constructed model and latent model.
  Condensation.coinModel Condensation.coinLatent Condensation.coinModel_entropy_pos Condensation.coinLatent_nonempty
  -- §3.1 (Condensation/Morphism.lean).  All ten endpoints of the section are proved:
  -- Definitions 3.5, 3.6, 3.9, 3.10 and Propositions 3.7, 3.8, 3.11, 3.12.  `RVModel.Hom`
  -- carries no measurability field for `f` -- Definition 3.5's own remark is that it is
  -- automatic on countable discrete ranges -- and the category laws (3.17)-(3.20) hold by
  -- `rfl`.  Definition 3.10 has two carriers, the pair predicate and the existential.
  Condensation.RVModel.Hom Condensation.RVModel.Hom.comp
  Condensation.RVModelObj.instCategory Condensation.RVModel.Hom.isIso_iff
  Condensation.RVModel.Hom.AEEq
  Condensation.RVModel.IsEquivalence Condensation.RVModel.Equivalent
  Condensation.RVModel.Hom.aeEq_equivalence Condensation.RVModel.Hom.comp_aeEq_congr
  Condensation.RVModelObj.equivalent_equivalence
  -- §4 (Condensation/Perfect.lean, Amalgamation.lean, Comparison.lean, Examples.lean).
  -- All three of Proposition 4.2's inequalities are here as of M2, including the middle
  -- one, (4.7)-(4.9), which used to be staged; Corollary 4.6, whose proof consumes it,
  -- came with it.  Definitions 4.11 and 4.12 are structures and are clean as such.
  --
  -- **Lemma 4.13 is complete as of 2026-08-17.**  Its three supporting measure lemmas --
  -- (4.55)-(4.56) total mass and both halves of (4.57) -- were the library's last
  -- un-annotated `sorry`s, and were discharged against Mathlib's
  -- `Measure.sum_smul_dirac_singleton` / `Measure.sum_smul_dirac` and the (4.53) weight
  -- rewritten as an indicator on `Λ₁ × Λ₂`.  All four of its carriers -- the two `canonical`
  -- constructions and the two existence statements -- are therefore inventoried here
  -- rather than staged, and every remaining `sorry` in the library now sits inside a
  -- declaration that carries a paper-node annotation.
  Condensation.LatentModel.simpleScore_ge_condScore
  Condensation.LatentModel.condScore_ge_entropy_jointContrib
  Condensation.LatentModel.entropy_jointContrib_ge_entropy_joint
  Condensation.LatentModel.PerfectlyCondenses Condensation.LatentModel.SimplyPerfectlyCondenses
  Condensation.LatentModel.perfect_entropy_iff_aeFunctionOf
  Condensation.LatentModel.aeFunctionOf_of_perfectlyCondenses
  Condensation.LatentModel.perfect_tfae_A Condensation.LatentModel.perfect_tfae_B
  Condensation.LatentModel.aeFunctionOf_iff_isEquivalence_contribModel
  Condensation.RVModel.OrderedMarkov Condensation.RVModel.orderedMarkov_iff
  Condensation.Amalgamation Condensation.LatentAmalgamation
  Condensation.Amalgamation.canonical Condensation.nonempty_amalgamation
  Condensation.LatentAmalgamation.canonical Condensation.nonempty_latentAmalgamation
  Condensation.Example41.L₁ Condensation.Example41.L₂
  Condensation.Example44.M44 Condensation.Example44.L44
  -- Example 4.1's (4.2)-(4.5) and Example 4.4's (4.11) and conclusion: proved at M2.
  Condensation.Example41.L₁_simpleScore Condensation.Example41.L₁_condScore
  Condensation.Example41.L₂_simpleScore Condensation.Example41.L₂_condScore
  Condensation.Example44.entropy_joint_eq Condensation.Example44.simplyPerfectlyCondenses
  -- §5 (Condensation/Quantitative.lean): Lemma 5.4 in both printed forms, Definition 5.5's
  -- polar, Definition 5.6's intersection tree with its computed labels and its family of
  -- intersections (5.11), Proposition 5.7 in full (existence and uniqueness of the
  -- extension of a leaf labelling), and Corollary 5.10's (5.24).  Theorem 5.8, Corollary
  -- 5.9 and Corollary 5.10's (5.25) were staged when this comment was first written; all
  -- three were **proved at M2** and are inventoried at the foot of this block, so the
  -- staged half of the §5 surface is now empty.
  --
  -- Proposition 5.7 is the **`M`-version** since 2026-08-17 (R2-F08/F11): the paper's `ℓ̃`
  -- maps the leaves *into an intersection-closed collection `M`* and the unique extension
  -- is a function `ℓ : V → M`, so `existsUnique_intersectionTree` now takes `M`, its
  -- closure under `⊓`, and `t.LabelsIn M`, and concludes with `d.LabelsIn M` as a third
  -- conjunct.  The earlier ambient-lattice statement is kept, un-annotated, as
  -- `existsUnique_intersectionTree_ambient` in the machinery block below; it is not
  -- Proposition 5.7.
  Condensation.condEntropy_eq_of_pair Condensation.condEntropy_le_of_pair
  Condensation.polar
  Condensation.ITree Condensation.ITree.label Condensation.ITree.intersections
  Condensation.ITree.LabelsIn
  Condensation.ITree.label_eq_leaves_foldr
  Condensation.eq_decorate_of_isIntersectionTree Condensation.existsUnique_intersectionTree
  Condensation.polar_kSubsets
  -- Lemma 4.14 (Comparison.lean), proved at M2 with the [MeasurableSingletonClass S] binder ruling.
  Condensation.aeFunctionOf_of_condIndepFun
  -- Theorem 4.15 (Comparison.lean), proved at M2 (the induction the paper omits — erratum 5 — is `aeFunctionOf_jointAbove_aux`).
  Condensation.aeFunctionOf_jointAbove_of_perfectlyCondenses
  -- M2: Theorem 5.8 in both printed forms, Corollary 5.9 (both forms) and Corollary 5.10's (5.25).
  Condensation.condEntropy_jointAbove_eq Condensation.condEntropy_jointAbove_le
  Condensation.condEntropy_jointAbove_le_reconScore
  Condensation.condEntropy_jointAbove_le_reconScore_of_orderedMarkov
  Condensation.condEntropy_jointAbove_le_choose
-- CONDENSATION-INVENTORY-END

-- The staged half of the Condensation annotated surface: endpoints whose *statements* are
-- final and carry a `Paper node:` line, but which are not yet axiom-clean -- either their
-- own proof is `sorry` or they consume one.  This block is pure comment; it compiles to
-- nothing and asserts nothing.  See the preamble above for the four failure modes
-- `scripts/check-condensation-nodes.py` fences it with.  Moving a name from here into the
-- `#assert_axioms_clean` block above is what "M2 proved this endpoint" means, and the two
-- edits belong in the same commit as the proof.
--
-- **Both sections are empty as of M2 (2026-08-18), and that is the point.**  There is no
-- `sorry` left in `Condensation/`, so there is nothing to stage.  Do not delete the block:
-- `scripts/check_sorry_ledger.py` cross-checks it against the compiled environment in both
-- directions on every run, so "empty" is a re-verified assertion rather than an absence.
-- The `-- SECTION:` marker line must stay for the same reason -- the second section is
-- where an un-annotated consumer of a staged theorem would be named (R2-F22).
--
-- CONDENSATION-PENDING-BEGIN
-- SECTION: consumers (un-annotated)
-- CONDENSATION-PENDING-END

/-! Tier-2 boundary structures for the Condensation surface.

Two things a reader should not mistake for omissions.  `RVModel`'s index type carries
`[Finite I]` — Definition 3.1's *finite* family — as a **class parameter of the structure**,
not as a field, so it is correctly absent from the freeze below; it has to be a parameter,
because `Finite I` does not mention the model and instance search would never find it as a
field (the concrete symptom was `reconScore` elaborating at `I = ℕ` with every sum silently
empty).  And `LatentModel`'s universes are independent of its model's — the full parameter
list is `LatentModel.{u, v, w, u', v'}` — which likewise changes no field. -/
#assert_fields Condensation.RVModel
  Ω mΩ countΩ singΩ P probP finiteEntropy_Ω R mR countR singR X measurable_X finiteEntropy_X
#assert_fields Condensation.LatentModel
  L π π_pres contributes

/-! The §3.1 and §4 boundary structures.

`RVModel.Hom` has **no measurability field for `f`**, and that absence is load-bearing
rather than an omission: Definition 3.5's own remark is that `f_j` is automatically
measurable because the ranges are countable and discrete, so a field would be a
strengthening of the paper's data.  `RVModel.Hom.measurable_f` supplies it as a lemma.
`RVModelObj` carries the index type `I` as a **field**, with `Finite I` as an instance
field beside it, because Definition 3.5 lets a morphism change the index set and a
`Category` instance needs a single object type — the opposite of `RVModel`, where the same
`Finite I` must be a *parameter*.  `IsEquivalence` is a `Prop`-valued structure, so
freezing its two fields freezes the two clauses of Definition 3.10.

`LatentAmalgamation`'s field list is long because Definition 4.12's "two latent variable
models with underlying probability space `Λ₀`" is rendered with `Λ₀` primary and the two
models *derived* (`lat₁`, `lat₂`), which is what makes their carrier `Λ₀` definitionally
rather than by a transported type equality.  Its last field, `comm`, is the **only** one
not read off Definition 4.12: nothing in the printed clause ties `π̃₁` to `π̃₂`, and Theorem
4.15 needs them to agree almost everywhere (`Condensation/notes/paper-errata.md` entry 10).

What the list no longer contains is the point of the 2026-08-17 freeze (R2-F12/F20).  Two
fields `ρ₁_π`/`ρ₂_π`, saying `Lₖ.π ∘ ρₖ = π̃ₖ` almost everywhere, were deleted: Definition
4.12(3)'s `ρₖ` are morphisms in the sense of **Definition 3.5**, i.e. of the underlying
*random variable* models, whose only conditions are "probability preserving" and
`fⱼ(X_{ι(j)}) = ρₖ^* Yⱼ` a.e.  The paper defines no morphism of *latent* variable models
and asks for no compatibility with the maps to `Ω`, so those fields were a strengthening of
the printed data.  What survives of clause (3) is exactly `ρₖ_pres` and `ρₖ_Y`.  A future
change that reintroduces either field is a faithfulness regression, and this freeze is what
catches it. -/
#assert_fields Condensation.RVModel.Hom
  π π_pres ι f eq_ae
#assert_fields Condensation.RVModelObj
  I finI M
#assert_fields Condensation.RVModel.IsEquivalence
  comp_left comp_right
#assert_fields Condensation.Amalgamation
  π₁_pres π₂_pres Λ₀ mΛ₀ countΛ₀ singΛ₀ P₀ probP₀ «ρ₁» «ρ₂» ρ₁_pres ρ₂_pres comm
#assert_fields Condensation.LatentAmalgamation
  Λ₀ mΛ₀ countΛ₀ singΛ₀ P₀ probP₀ finiteEntropy_Λ₀
  Y₁ measurable_Y₁ finiteEntropy_Y₁ «π₁» π₁_pres contributes₁
  Y₂ measurable_Y₂ finiteEntropy_Y₂ «π₂» π₂_pres contributes₂
  «ρ₁» ρ₁_pres ρ₁_Y «ρ₂» ρ₂_pres ρ₂_Y comm

/-! ## Factored Space Models — the checked endpoint inventory

Same contract as the FFS-INVENTORY block above: every declaration carrying a
`Paper node:` annotation in `FactoredSpaces/` must itself be listed between the
FS-INVENTORY markers below, and `scripts/check-factored-spaces-nodes.py` enforces that
direction, together with the validity of each cited node against the committed TeX
(`printed-counter-appendix` scheme: section-scoped shared counter, lettered appendix,
`restatable` wrappers) and the anchoring of each annotation to a named declaration.  The
converse (every listed name is a real declaration) is caught only when this file is
elaborated.

This formalization is **complete** (`scripts/papers.py`: `completed`): all 50 numbered
nodes of the paper are annotated and inventoried, and `notes/scope-manifest.json` records
that nothing was ruled out of scope.  Besides the numbered nodes the block carries three
kinds of unannotated entries, all deliberate: the non-vacuity witnesses of
`FactoredSpaces/Examples.lean`; the working form `disintegrates_iff_splice` of Definition
4.5 (the equivalence every history proof goes through, audited beside its definition); and
the claims the paper makes without a number —
`not_isGraphoid_structIndepRel` (Table 1, row "Intersection": structural independence
is *not* a graphoid; §5.1 calls this an important property) and
`isSemigraphoid_condIndepRel` (the Pearl 1988 fact cited in the proof of Proposition
5.2, proved here so that no citation boundary remains).  Neither can carry a
`Paper node:` line, since the checker admits only numbered nodes.
A third unnumbered entry joins them: `not_intersection_structIndepRel`, the same Table 1
"Intersection" claim with the failing axiom written out, so that reading the negative
claim needs no Proposition 5.2 alongside it. -/

open FactoredSpaces in
-- FS-INVENTORY-BEGIN
#assert_axioms_clean
  -- §4.1: Definitions 4.1, 4.2 and Lemma C.3
  Pt bg DerivedOn derivedOn_iff
  -- §4.2 / Appendix A: Definitions 4.5, 4.6; Lemmas 4.7, 4.8, 4.9, A.1, A.2, C.4
  Disintegrates disintegrates_iff_splice Disintegrates.union Disintegrates.inter
  Generates history generates_history history_subset_of_generates history_unique_minimal
  Generates.inter history_pair history_eq_iUnion_fibers history_eq_biUnion_fibers
  generates_indic_iff_agree generates_indic_iff_splice eventHistory_minimal_splice
  -- §4.3–4.4 / Appendix B: Definitions 4.10, 4.11; Lemmas 4.12, B.1
  StructIndep StructIndepGiven Before StrictlyBefore
  structIndep_of_before before_of_forall_bg before_iff_forall_structIndep
  structIndepGiven_pair
  -- Probability substrate: Definitions 4.3, 4.4, 6.1, C.1, C.2; Lemmas C.11, C.13, C.14,
  -- C.15, C.16, C.17
  Factorizes IsFactoredSpaceModel Distr.marg Distr.outer
  Distr.prob_pos_of_support_subset Distr.support_outerCompl Distr.prob_pos_of_marg_support_subset
  CondIndep CondIndepVar CondIndepEventVar.of_pair CondIndepEventVar.of_proj_subset
  Distr.prob_cyl_inter_cyl Factorizes.prob_sliceAt Distr.prob_outerCompl_delta
  condIndepVarEvent_proj_history
  -- §6 / Appendix C.2–C.3: Lemmas 6.3, 6.4, 6.5, C.5, C.7, C.8, C.9, C.10, C.12, C.18,
  -- C.19, C.20; Definition C.6; Theorem 6.2; Proposition 6.6
  condIndep_of_disjoint_eventHistory
  exists_polynomial_interp_prob interp_prob_pos condIndepVar_of_local
  interp_mem_factorizingPos
  PQIrrelevant Irrelevant cohistory pqIrrelevant_or_of_condIndepAll
  cohistory_union_eq_univ_of_condIndepAll condProb_eq_of_agree_on_relevant
  condIndepEventVar_proj_cohistory condIndepVarEvent_proj_cohistory disintegrates_cohistory
  cohistory_eq_compl_eventHistory disjoint_eventHistory_of_condIndepAll
  structIndepGiven_iff_forall_condIndepVar structIndepGiven_of_open
  -- §5.1: Definition 5.1, Proposition 5.2; plus the two unnumbered claims named in the
  -- preamble (Table 1 "Intersection" row; the Pearl semigraphoid fact behind Prop 5.2)
  IsSemigraphoid IsGraphoid IsCompositionalSemigraphoid
  isCompositionalSemigraphoid_structIndepRel not_isGraphoid_structIndepRel
  not_intersection_structIndepRel
  isSemigraphoid_condIndepRel
  -- §5.2 / Appendix B: Lemma 5.3, B.2; Propositions 5.4, 5.5, 5.6, 5.8; Definition 5.7
  prob_jointVar_fiber factorizesOverDAG_tau factorizes_tauInv tau_tauInv tauPos_bijective
  tauInv_condCPD_tau
  factorizesOverDAG_iff_isFactoredSpaceModel isAncestor_iff_strictlyBefore
  dSeparated_iff_structIndepGiven
  IsPerfectMapDAG IsPerfectMapFSM isPerfectMapFSM_nodeVar_of_isPerfectMapDAG
  exists_isPerfectMapFSM_of_exists_isPerfectMapDAG exists_isPerfectMapFSM_not_exists_isPerfectMapDAG
  -- Non-vacuity witnesses and convention pins (`FactoredSpaces/Examples.lean`): the paper's
  -- two-coin example, the trivial one-factor model of every distribution (remark after
  -- Definition 4.4), the collider DAG pinning the `dd:dsep` conventions from both sides
  -- (`not_dSeparated_self_zero` and `dSeparated_given_endpoint` are the two discriminating
  -- endpoint pins), Props 5.5/5.6 with content — `StructIndepGiven` positively inhabited
  -- (`structIndepGiven_collider`) as well as refuted — and the first inhabitant of
  -- `IsPerfectMapDAG` (Prop 5.8(1) is not vacuous).
  Examples.disintegrates_univ_diag Examples.not_disintegrates_singleton_diag
  Examples.history_bg_zero Examples.structIndep_bg_zero_one Examples.not_structIndep_bg_self
  Examples.isFactoredSpaceModel_single
  Examples.collider_isAcyclic Examples.not_dSeparated_given_collider
  Examples.not_colliderTrail_active_empty Examples.dSeparated_parents_of_collider
  Examples.nil_active_zero Examples.not_nil_active_zero Examples.not_dSeparated_self_zero
  Examples.not_dSeparated_adj Examples.dSeparated_given_endpoint
  Examples.structIndepGiven_collider Examples.not_structIndepGiven_nodesVar
  Examples.strictlyBefore_nodeVar Examples.G₁_acyclic Examples.isPerfectMapDAG_G₁_Q
  -- Negative instances of the paper's three *factorizes* predicates, so that none of them
  -- is trivially true: a constant observation variable is not a factored space model of a
  -- non-degenerate law (Definition 4.4), and the perfectly-correlated two-coin law `Pdiag`
  -- factorizes neither over `Ω` (Definition 4.3) nor over the edgeless two-node DAG `G₀`
  -- (§5.2, eq. (2)).
  Examples.not_isFactoredSpaceModel_const
  Examples.not_factorizes_diag
  Examples.G₀_acyclic
  Examples.not_factorizesOverDAG_diag
  -- Definition 5.7(1) inhabited by a DAG that actually has an edge, so that neither side
  -- of its equivalence is idle: `G₂ = (0 -> 1)` is a perfect map of the law `Pedge` whose
  -- two coordinates are dependent.  `not_dSeparated_G₂` / `dSeparated_G₂_given_endpoint`
  -- pin the graph side and `not_condIndepVar_Pedge` the probability side.
  Examples.G₂_acyclic
  Examples.G₂_adj_zero_one
  Examples.not_dSeparated_G₂
  Examples.dSeparated_G₂_given_endpoint
  Examples.not_condIndepVar_Pedge
  Examples.isPerfectMapDAG_G₂_Pedge
  -- The empty-value-space errata (E12, E16), kernel-checked rather than asserted in prose
  Examples.generates_not_inter_closed_twoEmpty Examples.history_ne_iUnion_fibers_oneEmpty
  Examples.history_bg_eq_empty_twoUnit
-- FS-INVENTORY-END

/-! Tier-2 boundary structures for the Factored Space Models surface. -/
#assert_fields FactoredSpaces.Distr
  mass nonneg sum_eq_one
-- `#assert_fields` freezes field *names* only.  The content of these three structures is
-- carried by the field *types*: `IsGraphoid.intersection` carries the cross-typed side
-- condition `β = γ → ¬ HEq Y Z` (the paper's `Y ≠ Z`), and the `[Nonempty _]` binders on
-- the axiom fields are the minimal ones Theorem 6.2 needs — weakening either would pass
-- this freeze silently, so any such change must be reviewed against
-- `FactoredSpaces/KNOWLEDGE.md` (round-1 record) rather than trusted to the audit.
#assert_fields FactoredSpaces.IsSemigraphoid
  symm decomposition weakUnion contraction
#assert_fields FactoredSpaces.IsGraphoid
  toIsSemigraphoid intersection
#assert_fields FactoredSpaces.IsCompositionalSemigraphoid
  toIsSemigraphoid composition
#assert_fields Digraph.Trail
  verts chain head last nodup
#assert_fields Digraph.Walk
  verts chain head last

/-! ## Consumer API conveniences (not paper endpoint inventories)

The trust-surface inventories above remain the paper-facing accounting.  These
declarations instead belong to the supported consumer surface: they are small
extensionality, simplification, certification, and transport tools advertised in each
paper's consumer API module, a subset of which is exercised by `APITests`.
Axiom-checking them here does not designate them as paper claims or add them to any
`*-INVENTORY` block. -/

open LogicalInduction in
#assert_axioms_clean
  DeductiveProcess.ext Strategy.ext Trader.ext AffineCombination.ext LUV.ext
  RpnSentenceCodes.const

#assert_axioms_clean
  ModalAgent.formula_mkRank0 ModalAgent.arity_mkRank0 ModalAgent.rank_mkRank0
  BehavEquiv.outcome_congr BehavEquiv.cooperates_iff BehavEquiv.defects_iff
  BehavEquiv.provablyDefects_iff

open CartesianFrames in
#assert_axioms_clean
  Frame.Subagent.congr Frame.multSubagent_iff_multSubagentCategorical
  Frame.commit_outcome Frame.assume_outcome Frame.external_outcome
  Frame.externalQuot_outcome Frame.internal_outcome Frame.internalSect_outcome

-- Finite Factored Sets: the consumer-surface conveniences advertised in
-- `FiniteFactoredSets/API.lean`; a subset of them is exercised by `APITests`.
open FiniteFactoredSets in
#assert_axioms_clean
  FactoredSet.StrictlyBefore.before FactoredSet.strictlyBefore_def FactoredSet.before_def
  FactoredSet.orthogonal_def FactoredSet.orthogonal_iff_forall_notMem
  FactoredSet.entangled_iff FactoredSet.size_eq_mk FactoredSet.dim_eq_mk
  FactoredSet.dim_eq_zero_iff FactoredSet.generates_iff_rel
  FactoredSet.generates_iff_sInf_le FactoredSet.generates_iff_history_subset
  FactoredSet.le_iff_history_subset
  FactoredSet.chimera_self FactoredSet.chimera_sdiff FactoredSet.chimera_union
  FactoredSet.chimera_inter FactoredSet.chimera_left_idem FactoredSet.chimera_right_idem
  FactoredSet.chimera_left_comm FactoredSet.chimera_basis FactoredSet.chimera_empty
  -- The setwise companions of those projections, which §3-§5 quantify over:
  -- `mem_chimeraImage_self` is clause 3 read setwise, `chimeraImage_univ_univ` its
  -- specialization at `T = R = S`, and `chimeraImage_sdiff` is clause 4 read setwise.
  FactoredSet.mem_chimeraImage_self FactoredSet.chimeraImage_univ_univ
  FactoredSet.chimeraImage_sdiff
  Subpartition.ofSetoidOn Subpartition.dom_ofSetoidOn Subpartition.toSetoid_ofSetoidOn
  Subpartition.restrict_univ Subpartition.restrict_restrict_of_subset
  Subpartition.dom_restrict_ofSetoid Subpartition.part_restrict_ofSetoid
  Subpartition.restrict_ofSetoid_inf
  Subpartition.restrict_inter_subset_restrict_inf classes_top
  FactoredSet.generatesSub_iff_historySub_subset
  FactoredSet.orthogonalSub_def FactoredSet.beforeSub_def
  FactoredSet.strictlyBeforeSub_def FactoredSet.StrictlyBeforeSub.beforeSub
  FactoredSet.orthogonalSub_iff_forall_notMem FactoredSet.orthogonalSub_ofSetoid
  FactoredSet.beforeSub_ofSetoid FactoredSet.orthogonalGivenSet_def
  FactoredSet.orthogonalGiven_def FactoredSet.historySub_restrict_inf
  -- Definition 24 agrees with Definition 17 on a partition of `S` with no finiteness at
  -- all (`historySub_ofSetoid`: two `⋂₀`s over the same family), which is what lets
  -- Proposition 24, the two `*_ofSetoid` identifications above and
  -- `beforeGivenSet_univ_iff` below drop `[Finite F.B]`; Proposition 22's *least*-element
  -- sentence still needs it.  The two empty-history
  -- computations and the Definition 26 corners are the §4.3/§7.3 facts every consumer
  -- needs and no paper node states — `orthogonalGiven_given_self` in particular is NOT
  -- Proposition 25 (which covers only `W = X`) and is the mechanism behind Definition 48
  -- implying Definition 49.
  FactoredSet.historySub_ofSetoid
  FactoredSet.historySub_top_restrict FactoredSet.historySub_restrict_empty
  FactoredSet.historySub_restrict_eq_empty_iff
  FactoredSet.orthogonalGivenSet_comm FactoredSet.orthogonalGivenSet_top_left
  FactoredSet.orthogonalGivenSet_top_right FactoredSet.orthogonalGiven_given_self
  -- §2.1: Definition 8's second sentence, the binary common refinement.  The set form
  -- `commonRefinement` is the node; `commonRefinement_pair` is the bridge saying that the
  -- `⊓` in which Propositions 11, 13, 15 and 18 are stated *is* the paper's `X ∨_S Y`.
  commonRefinement_pair
  -- §7.3: the four reductions a client applies before reading a Definition 48-50 fact as
  -- §7 content rather than §3/§4 content.  `beforeGivenSet_univ_iff` is Definition 50 at
  -- `E = S` being Definition 19; the two `*_top`/`_empty` corners are vacuously total and
  -- are listed so a positive witness at them is not mistaken for content.  No paper node:
  -- §7 states no theorem about Definitions 46-50.
  FactoredSet.counterfactableRel_of_counterfactable FactoredSet.counterfactableRel_top
  FactoredSet.beforeGivenSet_univ_iff FactoredSet.beforeGivenSet_empty
  -- §5.1-§5.2: the polynomial surface.  `Q_eq_finsum_mono`, `Q_eq_sum`,
  -- `poly_eq_sum_image`, `mono_eq_prod`, `mono_congr`, `mono_union` and `poly_empty` are
  -- the unfoldings of Definitions 31-34; `coeff_poly`, `mem_support_poly`, `poly_ne_zero`
  -- and `monos_eq_of_support_eq` describe `poly^F_C(E)` monomial by monomial; and
  -- `mono_eq_iff`, `degreeOf_poly_le`, `mem_vars_poly`, `degreeOf_Q_le`, `Q_ne_zero`,
  -- `vars_disjoint_of_mul_eq_Q` are the squarefreeness facts Corollary 1 buys, with
  -- `mono_basis_injective` the separation of distinct elements underneath Proposition 26
  -- and `coeff_add_mul_of_split` the generic, upstreamable one.  `mem_irr` and
  -- `poly_dvd_Q` are §5.2's unfolding and divisibility corollary; `irr_isPartition`
  -- restates Proposition 29 in §4's vocabulary; `subset_chimeraImage_self` and
  -- `mem_iff_part_mem_vars` are the two §5.2 helpers §5.3 also runs on.  None of these is
  -- a paper node.
  FactoredSet.Q_eq_finsum_mono FactoredSet.Q_eq_sum poly_eq_sum_image
  mono_eq_prod mono_congr mono_union poly_empty
  coeff_poly mem_support_poly poly_ne_zero monos_eq_of_support_eq
  FactoredSet.mono_eq_iff FactoredSet.degreeOf_poly_le FactoredSet.mem_vars_poly
  FactoredSet.degreeOf_Q_le FactoredSet.Q_ne_zero FactoredSet.vars_disjoint_of_mul_eq_Q
  FactoredSet.mono_basis_injective coeff_add_mul_of_split
  FactoredSet.mem_irr FactoredSet.poly_dvd_Q FactoredSet.irr_isPartition
  FactoredSet.subset_chimeraImage_self FactoredSet.mem_iff_part_mem_vars
  -- §5.3: the two directions of Lemma 3 isolated from its `TFAE`, which is how §5.5 and a
  -- downstream client consume it.  Neither is a paper node of its own — the node is
  -- `orthogonalGiven_tfae`, inventoried above, and each of these is one of its projections.
  -- `eq_of_Q_eq` is the injectivity of `E ↦ Q^F_E` the `2 → 1` direction runs on.
  FactoredSet.Q_mul_Q_eq_of_orthogonalGiven FactoredSet.orthogonalGiven_of_Q_mul_Q_eq
  FactoredSet.eq_of_Q_eq
  -- §5.4: `ProbDist` is finitely additive, so a distribution is determined by its
  -- singletons on any finite set; these are the two forms of that, and they carry no
  -- finiteness of their own.  `diracAt` is the point mass, and `isDistribution_diracAt`
  -- is the general non-vacuity fact behind §5.4-§5.5: it is a distribution on *every*
  -- factored set of finite dimension, so the family Proposition 32 and Theorem 3 quantify
  -- over is empty only over an empty `S` — where Theorem 3's other side holds too.
  -- None of these is a paper node.
  ProbDist.eq_sum_singleton ProbDist.eq_sum_singleton_of_finite
  ProbDist.diracAt ProbDist.diracAt_apply FactoredSet.isDistribution_diracAt
  -- §6.1: Definition 39's third clause named for legibility.  The node itself is rendered
  -- by Mathlib — `f⁻¹(ω)` and `f⁻¹(E)` are `Set.preimage` and `f⁻¹(X)` is `Setoid.comap` —
  -- so `Model.pullback` carries no paper-node annotation and belongs here rather than in
  -- the inventory above; `pullback_apply` is its unfolding, which is how a client reads a
  -- Definition 42 or 45 statement pointwise.  `not_strictlyBefore_self_of_consistent` and
  -- `strictlyBefore_of_not_consistent` are the two ways a client reads Definition 45 before
  -- trusting it: irreflexive wherever `D` has a model, vacuously total where it has none.
  -- Neither is a paper node; the paper's positive instances are Propositions 34 and 36.
  Model.pullback Model.pullback_apply
  OrthDatabase.not_strictlyBefore_self_of_consistent OrthDatabase.strictlyBefore_of_not_consistent

-- Condensation: the consumer-surface conveniences of the M0 layer, and the constructed
-- non-vacuity witnesses added in the round-1 fix wave.  None of these carries a
-- `Paper node:` annotation and none belongs in the CONDENSATION-INVENTORY block above:
-- the instances and `famFinset`/`AEFunctionOf.pi`/`condEntropy_eq_entropy_of_subsingleton`
-- are plumbing a client needs but the paper never states, and the witnesses are what makes
-- Definitions 3.1-3.3 non-vacuous rather than statements *of* the paper.  (The two earlier
-- witnesses `coinModel`/`coinLatent` remain in the inventory block above, where they were
-- first listed.)  Two of the witness facts exist to correct a specific over-claim:
-- `coinLatent_reconScore` and `twoCoinLatent_reconScore` prove the reconstruction score is
-- *zero* on the easy witnesses -- perfect reconstruction is exactly what a vanishing
-- `ϱ_L` means -- and `noisyLatent_reconScore_pos` is the witness that it is not identically
-- zero.
open Condensation in
#assert_axioms_clean
  Condensation.instFiniteFinset Condensation.PPlus.instFinite
  Condensation.AEFunctionOf.pi Condensation.condEntropy_eq_entropy_of_subsingleton
  Condensation.RVModel.finiteEntropyOf
  Condensation.RVModel.finiteEntropy_joint Condensation.RVModel.finiteEntropy_jointOn
  Condensation.LatentModel.finiteEntropy_pullbackJoint
  Condensation.famFinset Condensation.mem_famFinset
  Condensation.RVModel.jointFamily Condensation.LatentModel.ofJoint
  Condensation.LatentModel.nonempty
  Condensation.coinLatent_reconScore
  Condensation.twoCoinModel Condensation.twoCoinLatent Condensation.twoCoin_famFinset_contrib
  Condensation.twoCoinLatent_simpleScore Condensation.twoCoinLatent_condScore
  Condensation.twoCoinLatent_condScore_lt_simpleScore Condensation.twoCoinLatent_reconScore
  Condensation.noisyModel Condensation.noisyLatent Condensation.noisyLatent_reconScore
  Condensation.noisyLatent_reconScore_pos Condensation.noisyLatent_simpleScore
  Condensation.noisyLatent_condScore
  -- Round 3 (2026-08-18): witnesses for the *conditions* of §4 rather than its structures
  -- (R3-F08).  Definitions 4.3 and 4.8 had no constructed inhabitant before this, so
  -- Theorem 4.9, Proposition 4.10 and Theorem 4.15 were non-vacuous only in the sense that
  -- their statements elaborate.  `coinLatent_perfectlyCondenses` is Definition 4.3's
  -- conditioned clause on the fair coin; `coinLatent_orderedMarkov` is Definition 4.8, got
  -- from it by Theorem 4.9's (B1 => B2) rather than proved by hand;
  -- `Example44.L44_coin_simplyPerfectlyCondenses` is the simple clause, and is also what
  -- discharges `Example44.simplyPerfectlyCondenses`'s joint-independence hypothesis on a
  -- constructed family (Mathlib's `ProbabilityTheory.iIndepFun.of_subsingleton` over the
  -- one-element `P⁺Unit`).
  -- `noisyLatent_not_perfectlyCondenses` is the NEGATIVE witness: perfect condensation is a
  -- real restriction, not a property every latent variable model has.  None of these is a
  -- paper statement -- the paper asserts no instance of Definition 4.3 beyond Example 4.4,
  -- which is `Example44.simplyPerfectlyCondenses` in the inventory block above -- so they
  -- belong here.
  --
  -- **The `coinLatent_*` witnesses above are DEGENERATE, and round 4 (R4-F23) corrected the
  -- over-claim this comment used to make.**  At `I = Unit` the ordered Markov condition
  -- holds for *every* `RVModel (PPlus Unit)` and `condScore = simpleScore` for *every*
  -- latent over an `RVModel Unit`, so `coinLatent_orderedMarkov` witnesses satisfiability
  -- and nothing about the content of Definition 4.8.  The witnesses that carry content are
  -- the `twoCoinLatent_*` ones at `I = Bool` listed further down, where `P⁺Bool` has three
  -- elements and `incomparable twoCoinT` is nonempty.
  Condensation.coinLatent_entropy Condensation.coinLatent_condScore
  Condensation.coinLatent_perfectlyCondenses Condensation.coinLatent_orderedMarkov
  Condensation.coinLatentRV_iIndepFun
  Condensation.Example44.L44_coin_simplyPerfectlyCondenses
  Condensation.Example44.L44_coin_perfectlyCondenses
  Condensation.noisyModel_entropy_joint Condensation.noisyLatent_not_perfectlyCondenses
  -- Round 4 (2026-08-18, R4-F23): the witnesses that carry CONTENT, at `I = Bool`, plus the
  -- two lemmas that prove the `Unit`-indexed ones above do not.
  --
  -- The degeneracy, proved rather than asserted: over a subsingleton `P⁺I`,
  -- `condScore_eq_simpleScore_of_subsingleton_index` says `χ_L = σ_L` for **every** latent
  -- variable model, and `incomparable_eq_empty_of_subsingleton_index` says Definition 4.8's
  -- family of incomparable indices is empty.  So at `I = Unit` neither Definition 4.3's
  -- distinction nor Definition 4.8's conditional independence has any content, and the
  -- `coinLatent_*` witnesses establish satisfiability only.
  --
  -- At `I = Bool` with all three latents equal to one fair coin: `χ_L = log 2` at each of
  -- the three nonempty `A` while `σ_L({true}) = 2 log 2`, so
  -- `twoCoinLatent_perfectlyCondenses` and `twoCoinLatent_not_simplyPerfectlyCondenses`
  -- **separate Definition 4.3's two clauses on a single witness** —
  -- `LatentModel.PerfectlyCondenses.of_simply` has no converse, and that is not observable
  -- at `I = Unit`.  `twoCoinLatent_orderedMarkov` inhabits Definition 4.8 where the
  -- condition is not vacuous: `twoCoin_incomparable_T` computes
  -- `incomparable twoCoinT = {twoCoinF}`, which is nonempty.
  Condensation.twoCoinF Condensation.twoCoinF_ne_twoCoinTF
  Condensation.condScore_eq_simpleScore_of_subsingleton_index
  Condensation.incomparable_eq_empty_of_subsingleton_index
  Condensation.twoCoin_famFinset_contrib_F Condensation.twoCoin_famFinset_contrib_TF
  Condensation.twoCoinLatent_condEntropy_F
  Condensation.twoCoinLatent_condScore_F Condensation.twoCoinLatent_condScore_TF
  Condensation.twoCoinLatent_perfectlyCondenses
  Condensation.twoCoinLatent_not_simplyPerfectlyCondenses
  Condensation.twoCoin_incomparable_T Condensation.twoCoinLatent_orderedMarkov
  -- Phase 4b (2026-08-17): the witness with an **infinite-range** variable, which the
  -- retired `dd:finite-range` narrowing excluded and Definition 3.1 admits.  `Ω = ℕ` under
  -- the geometric law of `ShannonInformation/FiniteEntropy/Examples.lean`, `X () = id`.
  -- `geomModel_not_finiteRange` is what makes the retirement demonstrably more than a
  -- re-spelling; `geomModel_entropy` rules out the degenerate reading in which the class
  -- grew only by variables of zero entropy.
  Condensation.Example.geomModel Condensation.Example.geomModel_X
  Condensation.Example.geomModel_P Condensation.Example.geomModel_not_finiteRange
  Condensation.Example.geomModel_entropy Condensation.Example.geomModel_entropy_pos
  Condensation.Example.geomLatent Condensation.Example.geomLatent_reconScore
  -- M1 additions, none of which carries a `Paper node:` annotation.
  --
  -- `Model.lean`: the generic joint-variable and index-family companions of
  -- `measurable_joint(On)` / `finiteEntropy_joint(On)` that §4 and §5 run on.  `jointAll` is
  -- `X_A` at `A = I` spelled as the dependent product over `I` itself, so that naming
  -- `X_I` in a statement needs only `[Finite I]` and not a `Fintype` datum to write
  -- `Finset.univ`; equations (4.4)-(4.5) of Example 4.1 use it for exactly that.
  -- `incomparable` is the auxiliary index family of Definition 4.8, beside
  -- `contrib`/`above`/`strictAbove`/`contribIdx` and carrying no node for the same reason.
  -- `isUpperSet_contrib`/`isUpperSet_above` are stated with Mathlib's `IsUpperSet` -- the
  -- library defines no synonym for "upward closed" -- and `contrib_injective` is what makes
  -- Theorem 5.8's leaf-bijection hypothesis equivalent to the multiset equation it is
  -- stated as.
  Condensation.RVModel.jointAll Condensation.RVModel.measurable_jointAll
  Condensation.RVModel.finiteEntropy_jointAll
  Condensation.RVModel.functionOf_jointOn_mono Condensation.RVModel.aeFunctionOf_jointOn_mono
  Condensation.RVModel.functionOf_joint Condensation.RVModel.entropy_joint_singleton
  Condensation.LatentModel.entropy_pullbackJoint
  Condensation.contribIdx_subset_contrib Condensation.incomparable
  Condensation.isUpperSet_contrib Condensation.isUpperSet_above Condensation.contrib_injective
  -- The five membership `Iff`s of the Definition 3.4 auxiliaries and of `incomparable`.
  -- They are `@[simp]` and mostly `Iff.rfl`, which is exactly why they were missed until
  -- R4-F27: a client rewrites with them constantly, so they are part of the supported
  -- boundary even though nothing here has to be *proved*.
  Condensation.mem_contrib Condensation.mem_above Condensation.mem_strictAbove
  Condensation.mem_contribIdx Condensation.mem_incomparable
  -- M2 additions.  `ChainRule.lean`: the chain rule for a *finite family* of joint
  -- variables along a strict linear order, which PFR does not have (it stops at the two-
  -- and three-variable forms) and which all four remaining §4 endpoints run on.  None of
  -- it is a numbered node: `entropy_jointOn_eq_sum` is the shape of (4.9)/(4.29)/(4.34),
  -- `condEntropy_jointOn_eq_sum` the shape of (4.38), `condEntropy_jointOn_mono` is (4.8),
  -- and the two `condIndepFun` bridges are the termwise equalities (4.30)/(4.35)/(4.40).
  -- The two order constructions are the paper's own linear extensions -- of reverse
  -- inclusion (4.7), and of the partial order `⪯ₚ` of the paragraph before (4.29).
  Condensation.exists_strictTotalOrder_ext
  Condensation.exists_revIncl_strictTotalOrder
  Condensation.exists_revIncl_strictTotalOrder_incomparable_first
  Condensation.pred_subset_incomparable_union_strictAbove
  Condensation.RVModel.condEntropy_pair_jointOn Condensation.RVModel.condEntropy_jointOn_mono
  Condensation.RVModel.condEntropy_jointOn_sdiff Condensation.RVModel.condEntropy_jointOn_above
  Condensation.RVModel.condEntropy_jointOn_eq_sum Condensation.RVModel.entropy_jointOn_eq_sum
  Condensation.RVModel.condEntropy_jointOn_eq_of_condIndepFun
  Condensation.RVModel.condIndepFun_of_condEntropy_jointOn_eq
  -- and the two directions of "joint independence of a finite family ⟺ additivity of
  -- entropy", which Theorem 4.9's (A1) ⟺ (A3) needs both of.  PFR's
  -- `iIndepFun.entropy_eq_add` is the forward direction only, and only at `Fin m`.
  Condensation.RVModel.entropy_jointOn_le_sum
  Condensation.RVModel.entropy_jointOn_eq_sum_of_iIndepFun
  Condensation.RVModel.entropy_jointOn_eq_sum_of_subset
  Condensation.RVModel.indepFun_X_jointOn_of_entropy_eq
  Condensation.RVModel.iIndepFun_of_entropy_jointOn_eq_sum
  -- The three consequences of Proposition 4.2's chain that used to sit in the pending
  -- block's `consumers` section: with (4.7)-(4.9) proved they are axiom-clean, and they
  -- are consequences of the chain rather than nodes of the paper, so they belong here.
  Condensation.LatentModel.entropy_joint_le_condScore
  Condensation.LatentModel.entropy_joint_le_simpleScore
  Condensation.LatentModel.PerfectlyCondenses.of_simply
  -- `Morphism.lean`: the §3.1 machinery around the endpoints.  `Hom.ofSameIndex` and
  -- `isEquivalence_ofSameIndex_iff` are the "laid out" characterization the paragraph after
  -- Definition 3.10 gives, which is the shape Proposition 4.7 consumes; `Hom.ext` needs
  -- `HEq` on the `f` component because `f`'s type mentions `ι`.
  Condensation.RVModelObj Condensation.RVModel.Hom.id
  Condensation.RVModel.Hom.measurable_f Condensation.RVModel.Hom.pullback_eq
  Condensation.RVModel.Hom.aeFunctionOf Condensation.RVModel.Hom.eq_ae_all
  Condensation.RVModel.Hom.ext
  Condensation.RVModel.Hom.IsMeasurableIso Condensation.RVModel.Hom.isMeasurableIso_of_bijective
  Condensation.RVModel.Hom.ofSameIndex Condensation.RVModel.isEquivalence_ofSameIndex_iff
  -- Definition 3.9 packaged as a `Setoid` on each hom-type (`dd:category`); the `≈`
  -- notation a client uses for a.e. equality of morphisms resolves through it (R4-F27).
  Condensation.RVModel.Hom.instSetoid
  Condensation.RVModel.Equivalent.refl Condensation.RVModel.Equivalent.symm
  Condensation.RVModel.Equivalent.trans
  Condensation.RVModelObj.Equivalent Condensation.RVModelObj.id_eq Condensation.RVModelObj.comp_eq
  -- `Perfect.lean`: the two random variable models Proposition 4.7 compares.  They are the
  -- objects the `↔` is *about*, and the `↔` is the node, so they carry no annotation of
  -- their own.
  Condensation.LatentModel.pullbackModel Condensation.LatentModel.contribModel
  Condensation.LatentModel.aeFunctionOf_jointContrib_pullbackJoint
  -- `Amalgamation.lean`: the derived halves of Definition 4.12, and the constructed
  -- non-vacuity witness.  `lat₁`/`lat₂` are the two latent variable models the definition
  -- names; their underlying space is `Λ₀` definitionally, which is what Theorem 4.15 needs.
  -- `diagonal` amalgamates a latent variable model with itself along the identity: it is
  -- the *axiom-clean* inhabitant of `LatentAmalgamation`, and therefore what makes Theorem
  -- 4.15 and every §5 statement non-vacuous today.  Lemma 4.13's `canonical` /
  -- `nonempty_latentAmalgamation` are the paper's own, stronger, existence claim; they were
  -- staged when this comment was written and were **proved on 2026-08-17**, so they now sit
  -- in the CONDENSATION-INVENTORY block above and are axiom-clean like everything else
  -- there.  The reason `diagonal` is still named as *the* non-vacuity witness is not that
  -- the others are unproved but that it is the one an existence-free argument may cite:
  -- a non-vacuity claim about Definition 4.12 must not be routed through Lemma 4.13's
  -- existence theorem (R2-F19).
  -- (The lemma `comm_ρ` stood here until 2026-08-17.  It said the square (4.43) commutes
  -- a.e. inside Definition 4.12, and was provable only from the fields `ρ₁_π`/`ρ₂_π`, which
  -- are not in Definition 4.12 and were deleted with it -- R2-F12/F20.)
  Condensation.LatentAmalgamation.rv₁ Condensation.LatentAmalgamation.rv₂
  Condensation.LatentAmalgamation.lat₁ Condensation.LatentAmalgamation.lat₂
  Condensation.LatentAmalgamation.diagonal
  -- `Comparison.lean`: the set identity (4.62) that Theorem 4.15's missing induction runs
  -- on.  The paper writes `F_i` for `contribIdx i` and never defines it (errata entry 5).
  Condensation.iInter_contribIdx_eq_above
  -- `Quantitative.lean`: the conditional interaction-information symmetries Lemma 5.4 is
  -- proved through, the polar's lattice facts, and the `ITree`/`LTree` machinery behind
  -- Definition 5.6 and Proposition 5.7.  `kSubsets` is Corollary 5.10's family `F`; the
  -- node is `polar_kSubsets`, inventoried above.
  Condensation.condEntropy_pair_rotate Condensation.condInteractionInfo_comm
  Condensation.condInteractionInfo_swap Condensation.condInteractionInfo_rotate
  Condensation.mem_polar Condensation.mem_polar_iff Condensation.isUpperSet_polar
  Condensation.polar_antitone Condensation.polar_singleton Condensation.polar_eq_iInter
  Condensation.polar_empty
  Condensation.isUpperSet_inf_closed
  Condensation.ITree.leaves Condensation.ITree.subtrees
  Condensation.ITree.label_mem_of_labelsIn Condensation.ITree.label_eq_polar
  Condensation.ITree.decorate
  Condensation.LTree Condensation.LTree.rootLabel Condensation.LTree.erase
  Condensation.LTree.IsIntersectionTree Condensation.LTree.LabelsIn
  Condensation.ITree.labelsIn_decorate Condensation.existsUnique_intersectionTree_ambient
  Condensation.kSubsets
  -- `Examples.lean`, §3.1 witnesses.  `coinCollapse` is a morphism that genuinely changes
  -- the index set; `pairCoinHom₁`/`pairCoinHom₂` are Definition 3.9's remark made concrete
  -- -- a.e.-equal morphisms whose `f` components differ, which is possible because `X` need
  -- not be surjective onto its range type.
  Condensation.coinCollapse Condensation.coinObj Condensation.twoCoinObj
  Condensation.coinCollapseArrow
  Condensation.pairCoinModel Condensation.pairCoinHom₁ Condensation.pairCoinHom₂
  -- M2 close-out (2026-08-18): the generic machinery the four M2 proof shards needed.
  -- Each shard owned a single file, so these landed in "TO BE MOVED" sections of
  -- `Comparison.lean` / `Quantitative.lean` / `Examples.lean` and were relocated to their
  -- proper homes in this pass; they are listed here, not in the inventory above, because
  -- none of them is a numbered node.
  --
  -- `Probability.lean`, beside the rest of the `AEFunctionOf` API and the §2 entropy
  -- substrate.  `congr_left`/`congr_right` transport a dependence across an a.e. equality
  -- of the independent/dependent variable respectively -- `congr_right` is what consumes
  -- `LatentAmalgamation.comm`, reconciling Definition 4.12's `π̃₂` with Theorem 5.8's `π̃₁`.
  -- The three `condEntropy_*_of_aeFunctionOf` lemmas are the conditional analogues of
  -- `entropy_le_of_aeFunctionOf`; the two `_of_subsingleton` lemmas are the companions of
  -- `condEntropy_eq_entropy_of_subsingleton` above, for a *conditioned* variable of
  -- subsingleton range (Example 4.1's guarded-subtype encoding of "let `Y_A` be constant").
  Condensation.AEFunctionOf.congr_left Condensation.AEFunctionOf.congr_right
  Condensation.AEFunctionOf.prodMk_left
  Condensation.condEntropy_congr_of_aeFunctionOf
  Condensation.condEntropy_le_condEntropy_of_aeFunctionOf
  Condensation.condEntropy_le_of_aeFunctionOf
  Condensation.entropy_eq_zero_of_subsingleton Condensation.condEntropy_eq_zero_of_subsingleton
  -- `Model.lean`, beside the Definition 3.4 auxiliaries and the other index-family facts.
  -- `functionOf_jointOn_union` is the union companion of `functionOf_jointOn_mono` above;
  -- `above_mono` is antitonicity of the upward cones; `isUpperSet_iInter_contribIdx` is the
  -- invariant Theorem 4.15's induction carries, so that Proposition 4.10 applies at each
  -- step.
  Condensation.RVModel.functionOf_jointOn_union
  Condensation.above_mono Condensation.isUpperSet_iInter_contribIdx
  -- `ChainRule.lean`: the `famFinset` restatement of `entropy_jointOn_eq_sum_of_iIndepFun`
  -- above, which is the form §4's clients rewrite with.  It replaces three `private`
  -- lemmas that had been re-proved independently in `Examples.lean`.
  Condensation.RVModel.entropy_jointOn_eq_sum_famFinset
  -- `Amalgamation.lean`: `symm` reads an amalgamation of `L₁` with `L₂` backwards, which is
  -- the paper's "using the symmetry of the situation to interchange `Y` and `Z`".  The two
  -- `condScore_lat` lemmas transfer Definition 3.3's `χ` along `ρₖ`; they are what let
  -- Corollary 4.6 and Theorem 4.9 be applied to `L̃ₖ` rather than to `Lₖ`, which is
  -- necessary because R2-F12/F20 deleted the `ρₖ_π` fields and left no relation between
  -- `Lₖ.π ∘ ρₖ` and `π̃ₖ`.  `finiteEntropyOf'` is the same instance as
  -- `RVModel.finiteEntropyOf` with the sample space spelled `Λ₀`; the spelling is
  -- load-bearing, since `lat₁`/`rv₁` are plain `def`s that instance search will not unfold.
  Condensation.LatentAmalgamation.symm
  Condensation.LatentAmalgamation.condScore_lat₁ Condensation.LatentAmalgamation.condScore_lat₂
  Condensation.LatentAmalgamation.finiteEntropyOf'
  -- `Comparison.lean`: the `PerfectlyCondenses` companions of the two `condScore_lat`
  -- lemmas.  They stay here rather than moving to `Amalgamation.lean` with the rest,
  -- because Definition 4.3 lives in `Perfect.lean`, which `Amalgamation.lean` does not
  -- import.
  Condensation.LatentAmalgamation.perfectlyCondenses_lat₁
  Condensation.LatentAmalgamation.perfectlyCondenses_lat₂

-- Factored Space Models: the consumer-surface conveniences advertised in
-- `FactoredSpaces/API.lean` that are not paper endpoints; a subset of them is exercised by
-- `APITests`.  Auto-generated field projections (`Distr.mass`, `.nonneg`, `.sum_eq_one`)
-- are not listed, matching the Finite Factored Sets register above; `Distr` and the two
-- trail structures are, because the boundary advertises the types themselves and their
-- fields are frozen separately by `#assert_fields`.
open FactoredSpaces in
#assert_axioms_clean
  -- §4.1: the ambient factored space and the splice calculus (`dd:pi-space`, `dd:splice`).
  -- `Pt`, `bg`, `DerivedOn` and `derivedOn_iff` are paper nodes and stay in the inventory
  -- above; these are the surrounding vocabulary a client actually writes with.
  PtOn proj projSet proj_eq_restrict splice prodSplit mem_splice_iff splice_eq_cyl_inter
  splice_compl fiber pair indic
  DerivedOn.trans DerivedOn.mono DerivedOn.pair DerivedOn.comp_left
  -- §4.2: the corners and working forms of Definitions 4.5/4.6 and the membership
  -- criteria for `history` that every §5 proof and every client runs on.
  Disintegrates.compl disintegrates_univ disintegrates_empty disintegrates_univ_set
  generates_iff generates_univ generates_iff_history_subset
  history_mono_of_derived history_bg_subset mem_history_bg_of_mem_history
  mem_history_of_sep mem_history_iff_exists_ne exists_ne_of_mem_history
  eventHistory inter_eq_splice
  -- §4.3: the symmetry a client needs before Definition 4.10 is usable.
  StructIndepGiven.symm
  -- Probability substrate (`dd:dist`).  `Distr` itself, its `@[ext]` lemma, the whole
  -- `prob` calculus, and the constructions (`map`, `delta`, `uniform`, `mix`, `prod`,
  -- `margAt`, `outerCompl`, `condDist`, `cyl`, `sliceAt`) with the transport equivalences
  -- `splitEquiv`/`unionEquiv`/`unionComplEquiv`.  None of these is a paper node; the nodes
  -- they support (Definitions 4.3, 4.4, C.1, C.2) are inventoried above.
  Distr Distr.ext Distr.prob Distr.prob_nonneg Distr.prob_univ Distr.prob_empty
  Distr.prob_mono Distr.prob_le_one Distr.prob_union_of_disjoint Distr.prob_singleton
  Distr.prob_eq_sum_filter Distr.prob_eq_sum_fiber Distr.prob_pos_iff
  Distr.prob_eq_zero_iff Distr.prob_eq_zero_of_subset
  Distr.support Distr.condProb Distr.StrictlyPositive
  Distr.map Distr.map_mass Distr.map_prob Distr.map_map
  Distr.delta Distr.delta_mass Distr.delta_prob Distr.support_delta Distr.delta_eq_prod
  Distr.uniform Distr.uniform_strictlyPositive Distr.mix Distr.euclDist
  Distr.euclDist_self Distr.euclDist_comm Distr.euclDist_nonneg Distr.abs_sub_le_euclDist
  Distr.nonempty_carrier condDist condDist_mass condDist_prob
  Distr.prod Distr.prod_mass Distr.prod_mass_pos_iff Distr.prob_prod_agree_on
  Distr.prob_prod_inter_bg Distr.margAt Distr.margAt_prod
  factorizing factorizingPos factorizes_iff_exists_prod factorizes_prod
  Factorizes.eq_prod_margAt factorizes_delta
  Distr.outerCompl Distr.outerCompl_mass Factorizes.eq_outerCompl Factorizes.marg_mass
  outerCompl_delta_eq_prod cyl sliceAt splitEquiv unionEquiv unionComplEquiv
  -- §6.1 and Appendix C: the mixed conditional-independence forms, the two directions of
  -- Theorem 6.2 isolated from the iff (which is how a client consumes it), the
  -- interpolation, and the general form of Lemma C.17.
  CondIndepEventVar CondIndepVarEvent CondIndepAll CondIndep.symm CondIndep.of_prob_eq_zero
  fiber_pair condIndepVar_of_structIndepGiven structIndepGiven_of_forall_condIndepVar
  condIndepVarEvent_proj_of_disintegrates
  interp interp_zero interp_one factorizes_interp pairsDifferingAt mem_cohistory_iff
  -- §5.1: the carrier of Definition 5.1's axioms and the two relations Proposition 5.2
  -- and Theorem 6.2 instantiate it at.
  IndepRel structIndepRel condIndepRel
  -- §5.2, graph side (root `Digraph` namespace): acyclicity and its one-line consequences,
  -- ancestry, parents, and the depth/ancestral-closure order the chain rule of
  -- `factorizesOverDAG_of_isIMapDAG` runs on.
  Digraph.IsAcyclic Digraph.IsAcyclic.wf Digraph.IsAcyclic.ne_of_adj
  Digraph.IsAcyclic.not_adj_symm Digraph.IsAcyclic.not_ancestor_of_adj
  Digraph.IsAncestor Digraph.parents Digraph.mem_parents Digraph.notMem_parents_self
  Digraph.depth Digraph.depth_lt Digraph.depth_lt_of_isAncestor Digraph.AncClosed
  -- §5.2, construction side: `Ω^G` and the node variables, with the reading-off API, plus
  -- the CPD vocabulary and the components of `τ`.  The Lemma 5.3 / Propositions 5.4, 5.6
  -- statements themselves are inventoried above.  `mem_history_nodeVar_iff` is the closed
  -- form of `H(X_v)` that Proposition 5.6 is read off from (`FactoredSpaces/Separation.lean`).
  ParentVals parentConfig bnIndex bnFactor nodeVar nodeVar_apply nodeVar_eq_of_diag
  jointVar_eq_iff constTable jointVar_constTable jointVar nodesVar famVar famJoint
  CPD FactorizesOverDAG dagFactorizing condCPD tau tauInv tauPos mem_history_nodeVar_iff
  -- d-separation (`dd:dsep`): the definition itself is not a paper node (the paper does not
  -- define it, errata E8), so all of it lives here — trails, collider status, activity, the
  -- `Z`-closure criterion, and the local Markov property.
  Digraph.Trail Digraph.Walk Digraph.Walk.IsColliderAt Digraph.Walk.Active
  Digraph.Trail.Active Digraph.ColliderOK Digraph.DSeparated Digraph.Trail.nil
  Digraph.Trail.nil_active_iff Digraph.not_dSeparated_self
  Digraph.dSeparated_iff_forall_singleton Digraph.dSeparated_singleton_parents
  Digraph.dSeparated_iff_disjoint_zClosureSet
  -- §5.2.3: the I-map weakening of Definition 5.7(1) and the theorem the paper's proof of
  -- Proposition 5.8(1) omits (errata E7).
  IsIMapDAG factorizesOverDAG_of_isIMapDAG
  -- The witness objects of `FactoredSpaces/Examples.lean` the API advertises by name; the
  -- facts proved about them are inventoried above.
  Examples.Coins Examples.diag Examples.G₁ Examples.Q
  Examples.Pdiag Examples.G₀
  -- The `Z`-closure vocabulary of `ConditionalHistory.lean` (root `Digraph` namespace).
  -- `dSeparated_iff_disjoint_zClosureSet` above is *stated* in it, so a client cannot use
  -- that criterion without these names; `Skel` and `Trail.toWalk` are what writing a
  -- concrete trail down and reading its collider status take; and
  -- `exists_active_trail_of_active_walk` is the walk-to-trail bridge the `dd:owalk`
  -- glossary cites, which lets a client define d-separation through walks instead.
  Digraph.unblockedAnc
  Digraph.IsZClosed
  Digraph.zClosure
  Digraph.zClosureSet
  Digraph.zClosure_subset
  Digraph.mem_zClosureSet_self
  Digraph.mem_zClosureSet_of_mem_unblockedAnc
  Digraph.exists_of_mem_zClosureSet
  Digraph.Skel
  Digraph.Trail.toWalk
  Digraph.exists_active_trail_of_active_walk
  -- Small tools `APITests` uses that the bullets above did not name: the `Ω^G` index at a
  -- joint value and the transport that keeps its dependent argument out of a rewrite, the
  -- mass of the Lemma 5.3 pushforward, and the support-membership criterion.
  idxAt
  table_congr
  tau_mass
  Distr.mem_support_iff
  -- The two general d-separation discharge routes and the one-edge trail they are checked
  -- against (`FactoredSpaces/DSeparation.lean`), plus the §6.1 conditional-independence
  -- tools a client needs to verify Definition 5.7 by hand over arbitrary, possibly
  -- overlapping triples, and the transport of a conditional independence along a
  -- pushforward (`FactoredSpaces/Probability.lean`).
  Digraph.dSeparated_of_subset_left
  Digraph.dSeparated_of_subset_right
  Digraph.Trail.pair
  Digraph.Trail.pair_active
  Digraph.not_dSeparated_of_skel
  CondIndep.of_subset_left
  CondIndep.of_disjoint_left
  CondIndepVar.symm
  fiber_proj_subset_or_disjoint
  condIndepVar_proj_of_subset_left
  condIndepVar_proj_of_subset_right
  CondIndepVar.of_proj_subset
  not_condIndepVar_proj_self
  condIndepVar_map
  -- The new witness objects `FactoredSpaces/API.lean` advertises by name.
  Examples.G₂
  Examples.Pedge
