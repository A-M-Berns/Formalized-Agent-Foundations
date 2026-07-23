/-
# Axiom audit — the checked public-surface inventory

Mechanical guard 1 of the consolidation phase (`notes/consolidation.md`). A standalone
build target, deliberately outside the `LogicalInduction` library: the library carries
the mathematics, this target carries the check. This file is the endpoint inventory: every declaration listed below is public trust surface — the
table of contents for the deferred human read-through. Anything *not* listed here is
internal and may be renamed, moved, or inlined freely; changes to a listed statement are
surface changes and must be flagged.

The build fails if any listed endpoint acquires an axiom beyond `propext`,
`Classical.choice`, `Quot.sound` (in particular `sorryAx`), or ceases to exist.

Two independent claims, checked separately — do not conflate them:
  * **axiom cleanliness** (this build): every *listed* endpoint is `sorry`-free and uses no
    stray axioms. It says nothing about whether the list is complete.
  * **surface completeness** (`scripts/check_endpoint_coverage.py`): every paper `\label`
    cited in a `Paper node:` annotation has at least one endpoint *in this list*. It says
    nothing about axioms, nor about whether the listed endpoint is the strongest form of
    the theorem (that is the deferred human read-through's job — see below).
Green here + green there = "the enumerated surface is clean and covers every annotated
paper node", not "the formalization is faithful". Faithfulness is the read-through.

Scope is the whole repository, and it is now **strictly clean throughout**: the former
sole intentional axiom `glFixedPoint_thm42` (GL fixed-point existence) has been discharged
by the autoformalized `ProvabilityLogic/` sequent calculus (see `ModalAgents/FixedPoint.lean`),
so every ModalAgents endpoint — including the cooperation results that rest on the GL fixed
point — is asserted under `#assert_axioms_clean`. (`#assert_axioms_clean_except` is retained
as a reusable tool but is no longer needed.)
-/
import Lean.Util.CollectAxioms
import LogicalInduction.Properties
import LogicalInduction.Construction
import ModalAgents.Cooperation
import ModalAgents.Behavioral
import ModalAgents.FixedPoint

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
listed idents. Freezes the hypothesis surface of a boundary structure: adding or removing
a field fails the build. Order-insensitive. -/
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

/-! ## Property tail, conditional on `[IsLogicalInductor P DP]` (M3–M5) -/

-- Properties/Coherence.lean
#assert_axioms_clean
  lic_disprovable_tendsto_zero lic_excl_gap_tendsto_zero lic_limit_additive
  lic_price_convergesTo

-- Properties/LimitCoherence.lean
#assert_axioms_clean lic_limitCoherence

-- Properties/ProvabilityInduction.lean, Properties/AffineCoherence.lean
#assert_axioms_clean
  lic_deducible_eventually_ge lic_deducible_price_near_one lic_deducible_tendsto_one
  lic_provind_seq lic_provind lic_provind_true lic_provind_false

-- Properties/TimelyLearning.lean, Properties/AffinePersistence.lean
#assert_axioms_clean
  lic_preemptive_learning lic_persistence_of_knowledge lic_persistence_of_knowledge_lower
  lic_persistence_of_knowledge_upper lic_centered_persistence lic_limitingBelief_tendsto

-- Properties/NonDogmatism.lean, Properties/UniformNonDogmatism.lean
#assert_axioms_clean
  lic_nonDogmatism lic_nonDogmatism_dual lic_nonDogmatism_weak lic_limit_pos
  lic_limit_lt_one lic_uniform_nonDogmatism lic_uniform_nonDogmatism_repeating

-- Properties/OccamBounds.lean, Properties/UniversalSemimeasure.lean
#assert_axioms_clean
  lic_occamBounds lic_occam_lower lic_limitingBelief_add_neg
  lic_domination_universalSemimeasure lic_strict_domination_universalSemimeasure

-- Properties/Conditioning.lean, Properties/FinitePerturbations.lean
#assert_axioms_clean
  lic_conditioned lic_conditioned_gated lic_conditioned_eventual
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
  lic_expect_combination_provind_zero lic_expect_combination_provind_le
  lic_expect_combination_provind_ge lic_expect_combination_provind_eq
  lic_linearity_of_expectation_seq
  lic_introspection lic_paradox_resistance lic_expectations_of_probabilities
  lic_iterated_expectations lic_self_trust lic_expected_future_expectations

-- Construction/Witnesses/LUVExpectationCertified.lean (F7 `dd:luv-arith`): the
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

/-! ## Constructed M7 witnesses and their direct criterion consumers -/

-- Construction/Witnesses/M7Witnesses.lean (`M7-HIST-EVALN`, `M7-CE-REPETITION`,
-- `M7-PATIENT-CLOCK`, `M7-PREFIX-PATCH`)
#assert_axioms_clean
  codeEvalnNat_polyFueled boundedEvalnCompiler EfficientRepeatedEnumeration.ofCE
  SettlementChecker.ofComputations PatientSettlementClock.ofComputations
  liaEfficientPrefixPatch

-- Construction/Witnesses/QuotationAffine.lean (`M7-QUOTE-AFFINE`)
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

-- Construction/Witnesses/FeedbackEmission.lean (`M7-FEEDBACK-EMIT`)
#assert_axioms_clean
  feedbackTraderEmissionSigns lic_wubaff_ofFeedbackTruth
  boundedCombination_wubaff_ofFeedbackTruth luv_wubexp_ofFeedbackTruth

-- Construction/Witnesses/FeedbackTruth.lean (`M7-FEEDBACK-TRUTH`)
#assert_axioms_clean
  feedbackTruthSequence lic_wubaff_ofComputation lic_wub_ofComputation
  boundedCombination_wubaff_ofComputation luv_wubexp_ofComputation
  lic_wub_ofComputation_unconditional lic_wubaff_ofComputation_unconditional
  boundedCombination_wubaff_ofComputation_unconditional
  luv_wubexp_ofComputation_unconditional

-- Construction/Witnesses/BitPrefixSyntax.lean (`M7-DUS-PREFIX-SYNTAX`)
#assert_axioms_clean
  bitPrefixSentencesOfIndependentAtoms lic_domination_universalSemimeasure_ofIndependentAtoms

-- Construction/Witnesses/ConditioningPresentation.lean (`M7-SCON-PRESENTATION`)
#assert_axioms_clean
  conditioningPresentationOfComputations fixedConditioningPresentation
  lic_conditioned_gated_ofComputations

-- Construction/Witnesses/ConditioningCompiler.lean (`M7-SCON-COMPILER`)
#assert_axioms_clean
  conditionedTranslation_preserves_ec eventualConditionedTranslation_preserves_ec
  exists_eventual_condition_price_floor
  eventualConditioningOperationalWitness
  lic_conditioned_eventual_ofMarketComputation
  lic_conditioned_fixed_ofComputationAndMarket
  lic_conditioned_growing_ofComputationsAndMarket
  gatedConditioningOperationalWitness
  denominatorPatchedGatedConditioningOperationalWitness
  lic_conditioned_gated_ofMarketComputation lic_conditioned_gated_ofComputationsAndMarket

-- Construction/Witnesses/UnconditionalOverLIA.lean
#assert_axioms_clean
  lic_domination_universalSemimeasure_unconditional
  lic_conditioned_ofCompiler_unconditional
  lic_conditioned_fixed_unconditional
  lic_conditioned_growing_unconditional

-- Construction/Witnesses/LUVSyntax.lean (`M7-LUV-SYNTAX`)
#assert_axioms_clean LUVCombinationSyntax.meshSoftmaxOperationalWitness

-- Construction/Witnesses/ComputationSyntax.lean (`M7-COMP-SYNTAX`)
#assert_axioms_clean
  representedSemidecidableClaimsOfComputation representedDecidableClaimsOfComputation
  inconsistentTheoryClaimsOfComputation
  lic_belief_finitistic_consistency_ofComputation
  lic_belief_stronger_theory_consistency_ofComputation
  lic_disbelief_inconsistent_theories_ofComputation
  lic_learns_halting_patterns_ofComputation
  lic_learns_provable_nonhalting_patterns_ofComputation
  lic_does_not_anticipate_halting_ofComputation

-- Construction/Witnesses/ComputationDP.lean — unconditional-over-LIA capstones
-- (parity with the paradox-resistance and conditioning `_unconditional` endpoints above)
#assert_axioms_clean
  lia_learns_halting_patterns_unconditional
  lic_expectations_of_probabilities_ofCode_unconditional


open AffineCombination LUVCombination in
/-! ## Tier-2 boundary structures — field (hypothesis) surface

Each structure below appears in the *type* of a Tier-1 endpoint (directly, or
transitively through structure fields), so its fields are hypotheses the deferred
read-through must audit. `#assert_fields` freezes that field set: adding or removing
a field — smuggling a premise in or out of a boundary — fails the build. The set is
order-insensitive. Regenerate with `SurfaceProbe`/`FieldProbe` if the surface changes
deliberately. -/

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
  determined sequence poly bounded magnitude zero_value feedback_price
#assert_fields AffineCombination.PolySequence
  termCount coefficient sentence termCount_poly const_poly coefficient_poly sentence_poly terms_eq const_rank coefficient_rank const_closed coefficient_closed
#assert_fields AffineQuoteEq
  toAffineQuotePortfolio future_coherent
#assert_fields AffineQuoteGE
  toAffineQuotePortfolio future_coherent
#assert_fields AffineQuotePortfolio
  family poly scale scale_pos current_price bounded magnitude_le_one
#assert_fields BitPrefixCodeComputation
  code code_poly
#assert_fields BitPrefixSentences
  atom prefixSentence enumeration enumeration_covers prefix_codes holds_prefix finite_realizable
#assert_fields BooleanQuoteCode
  code pos_complete neg_complete
#assert_fields BoundedComputation
  machine input steps input_poly steps_poly truth_iff
#assert_fields BoundedEvalnCompiler
  code poly
#assert_fields CEEnumeration
  code halts outputs_sound
#assert_fields CompactConditioningProcessComputation
  toDeductiveProcessComputation condition_code condition_code_poly
#assert_fields CompletedAffineQuoteApprox
  toAffineQuotePortfolio theory_coherent
#assert_fields CompletedAffineQuoteEq
  toAffineQuotePortfolio theory_coherent
#assert_fields ComputationTheoryPresentation
  theory_deltaOne process halting_enters halting_refutes boundedHalting_enters boundedFailure_refutes inconsistency_enters inconsistency_refutesConsistency
#assert_fields ConditionalExpectationQuote
  weight_mem weight_generable source_codes left_codes right_codes source_valued left_reflected right_reflected affine
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
  atom finite_realizable
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
#assert_fields PseudorandomFrequencyInfrastructure
  clock
#assert_fields QuotationTheoryPresentation
  toComputationTheoryPresentation theory_sigmaOne quote_positive_enters quote_negative_refutes
#assert_fields RationalQuoteCode
  code value_mem pos_complete neg_complete threshold_poly
#assert_fields RepresentedDecidableClaims
  toRepresentedSemidecidableClaims disprovable_of_false
#assert_fields RepresentedSemidecidableClaims
  sentence sentence_poly provable_of_true
#assert_fields SelfTrustQuote
  delta_pos probability_mem sentence_codes delta_codes probability_codes product_codes confidence_codes confidence_reflected product_reflected affine
#assert_fields SemidecidableComputation
  machine input input_poly truth_iff
#assert_fields SettlementChecker
  code spec
#assert_fields Strategy
  trades rank_le
#assert_fields StrictSeparatorPresentation
  prefixes nested length_tendsto_atTop repetition jointly_possible mass_tendsto_zero
#assert_fields Trader
  strat
#assert_fields UniversalContinuousSemimeasure
  toLowerSemicomputableContinuousSemimeasure universal


end LogicalInduction

/-! ## ModalAgents — modal open-source game theory (Barász et al.)

Every ModalAgents endpoint is now strictly clean. The former sole intentional axiom
`glFixedPoint_thm42` (GL fixed-point existence) is discharged by the autoformalized
`ProvabilityLogic/` sequent calculus (see `ModalAgents/FixedPoint.lean`); `glFixedPoint_thm42`
is a proved theorem, so the cooperation endpoints that rest on it are asserted strictly
clean below rather than via `#assert_axioms_clean_except`. -/

#assert_axioms_clean
  subst_congr glFixedPoint_uniqueness glFixedPoint_thm42
  glFixedPoint_spec outcome_fixed_point
  defectBot_defects cooperateBot_cooperates
  fairBot_vs_fairBot fairBot_vs_cooperateBot rank0_fairBot_implies_cooperateBot
  fairBot_vs_defectBot prudentBot_vs_fairBot prudentBot_vs_defectBot
  prudentBot_vs_cooperateBot prudentBot_vs_prudentBot
  Cooperates.arithmeticLift modalAgent_behavioral
