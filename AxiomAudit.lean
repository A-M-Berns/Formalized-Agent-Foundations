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

-- Single-class collapse: `EfficientlyComputable` is the symbol-metered `def:ec`;
-- the enumeration's single RPN decode covers the whole class.
#assert_axioms_clean
  trading_firm_dominance exists_enumeratedTrader_eq enumeratedTrader_ec

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

-- dd:fuel model card (`def:ec`): the fuel model's own trust facts — upper calibration
-- (poly-fueled ⟹ primrec), the runtime-gcd inhabitation witness, the size-based
-- separation (2^n is not poly-fueled), and the two-sided EF.cost ↔ token-length seam.
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

-- `ccee`: the weighted conditional, **general-source** closed form.  The deferred-weight
-- quote code names the `w ∘ f` program (deferral costs nothing at emission), and
-- `meshProductLUV` renders the product from that quote's own threshold atoms on a
-- width-`n+1` mesh, so no emitter ever needs the value `w (f n)` (which is neither
-- available — P-generable, and deferred — nor polynomially sized).  The price is that the
-- left product reflects only to within `1/(n+1)`: a **disclosed type-`(c)` substitution**
-- carried by `ConditionalExpectationQuote.slack`.  `indicatorProductLUV_exact_left_reflected`
-- is the non-vacuity witness at the exact (`slack = 0`) end.  See the Part F header and the
-- README's modeling-boundary list; the exact route stays in future work.
#assert_axioms_clean
  PCWorld.ValuesAt.eq
  theoremDeferredWeightQuoteCode
  theoremConditionalExpectationQuoteCode
  meshProductLUV_valuesAt
  meshProductLUV_rpnThresholdCodeSeq
  indicatorProductLUV_exact_left_reflected
  lic_no_expected_net_update_conditional_closed

-- Construction/Witnesses/ProductDefinition.lean — the exact-reflection route for the quoted
-- product.  Fresh product atoms are defined by the deductive process itself (a definitional
-- extension of the *process*, not of the theory), so a completed world values the product at
-- exactly `x · w` — `slack = 0`, no positivity hypothesis on the weight.
--
-- This does **not** carry the `thm:ccee` row, and is inventoried so that its axiom
-- cleanliness is gated rather than left to the file's own `#print axioms`.
-- `lic_no_expected_net_update_conditional_closed` above remains the `thm:ccee` endpoint of
-- record, at the disclosed `1/(n+1)` slack over the base `LIA`.
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
that in both directions.

This formalization is **in progress**: the list below covers §2, §3 and §4.  Several
of the paper's §2.1 nodes have no Lean carrier at all because they are rendered by
Mathlib vocabulary under the `dd:` tags in `FiniteFactoredSets.lean` — Definition 2
(partition) is `Setoid`, Definition 5 (`∼_X`) is the setoid relation, Definition 6
(finer) is `≤`, Definition 7 (`Dis_S`/`Ind_S`) is `⊥`/`⊤`, and Definition 9 (`∏(B)`) is
the dependent product.  Those are recorded in `FiniteFactoredSets/README.md` rather than
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
  -- Non-vacuity witnesses (FiniteFactoredSets/Examples.lean).  Every §2-§4 endpoint is
  -- stated over `FactoredSet`; these are what make those endpoints say something.
  -- `coordFS` is the load-bearing one: with a single factor every `C` behaves as `∅` or
  -- `B`, so Proposition 4 would be near-tautologous — and with a single factor there is no
  -- subset of `S` on which the §4 restrictions can pull apart or entangle two factors,
  -- which is what the §4 block at the end of this list needs.
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
  -- not implied by Definition 18; Proposition 25 and Theorem 2 exhibited on the witness.
  Examples.fstOnEdiag Examples.sndOnEdiag
  Examples.historySub_fstOnEdiag Examples.historySub_sndOnEdiag
  Examples.not_orthogonalGivenSet_Ediag Examples.Ediag_mem_xorPart_classes
  Examples.not_orthogonalGiven_fst_snd_xorPart Examples.orthogonalGiven_fst_snd_top
  Examples.orthogonalGiven_nondegenerate Examples.not_orthogonalGiven_fst_fst_top
  Examples.orthogonalGiven_fst_fst_fst
  Examples.thm2_decomposition_coordFS Examples.thm2_weakUnion_coordFS
  -- The degenerate corners of Definitions 26-27, recorded so a client does not rediscover
  -- them: conditioning on `∅` or on `Dis_S` makes every pair orthogonal.
  Examples.orthogonalGivenSet_empty Examples.orthogonalGiven_bot
-- FFS-INVENTORY-END

/-! Tier-2 boundary structures for the Finite Factored Sets surface. -/
#assert_fields FiniteFactoredSets.IsFactorization
  nontrivial bijective
#assert_fields FiniteFactoredSets.FactoredSet
  B isFactorization
#assert_fields FiniteFactoredSets.Subpartition
  r symm' trans'

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
