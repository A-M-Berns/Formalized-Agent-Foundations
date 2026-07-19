/-
# Axiom audit — the checked public-surface inventory

Mechanical guard 1 of the consolidation phase (`notes/consolidation.md`). This file is
the endpoint inventory: every declaration listed below is public trust surface — the
table of contents for the deferred human read-through. Anything *not* listed here is
internal and may be renamed, moved, or inlined freely; changes to a listed statement are
surface changes and must be flagged.

The build fails if any listed endpoint acquires an axiom beyond `propext`,
`Classical.choice`, `Quot.sound` (in particular `sorryAx`), or ceases to exist.
-/
import Lean.Util.CollectAxioms
import LogicalInduction.Properties
import LogicalInduction.Construction

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

namespace LogicalInduction

open ConditioningCompile FeedbackTruth FeedbackEmission PrefixPatchCompile

/-! ## Existence (`thm:li`) -/

#assert_axioms_clean exists_logical_inductor LIA_is_logical_inductor

/-! ## Property tail, conditional on `[IsLogicalInductor P DP]` (M3–M5) -/

-- Properties/Coherence.lean, Properties/Convergence.lean
#assert_axioms_clean
  lic_disprovable_tendsto_zero lic_excl_gap_tendsto_zero lic_limit_additive
  lic_price_convergesTo

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

-- Properties/OccamBounds.lean, Properties/UniversalSemimeasure.lean,
-- Properties/StrictSemimeasure.lean
#assert_axioms_clean
  lic_occamBounds lic_occam_lower lic_limitingBelief_add_neg
  lic_domination_universalSemimeasure lic_strict_domination_universalSemimeasure

-- Properties/Conditioning.lean, Properties/FinitePerturbations.lean
#assert_axioms_clean
  lic_conditioned lic_conditioned_gated lic_iff_of_finitePerturbation

-- Properties/Pseudorandomness.lean
#assert_axioms_clean
  lic_learning_pseudorandom_frequency lic_learning_pseudorandom_frequency_above
  lic_learning_pseudorandom_frequency_below lic_learning_varied_pseudorandom
  lic_learning_varied_pseudorandom_above lic_learning_varied_pseudorandom_below
  AffineCombination.lic_not_frequently_positive_feedback_return
  AffineCombination.lic_wub AffineCombination.lic_wubaff

-- Properties/Relationships.lean
#assert_axioms_clean
  lic_imp_eventually_le lic_lex_tendsto_zero lic_learning_exclusive_exhaustive

-- Properties/ExpectationAffine.lean, Properties/Introspection.lean,
-- Properties/SelfTrust.lean
#assert_axioms_clean
  lic_linearity_of_expectation lic_expectation_indicator lic_expectation_provind
  lic_introspection lic_paradox_resistance lic_expectations_of_probabilities
  lic_iterated_expectations lic_self_trust lic_expected_future_expectations
  lic_no_expected_net_update lic_no_expected_net_update_conditional

-- Properties/MetaLearning.lean
#assert_axioms_clean
  lic_belief_finitistic_consistency lic_belief_stronger_theory_consistency
  lic_disbelief_inconsistent_theories lic_learns_halting_patterns
  lic_learns_provable_nonhalting_patterns lic_does_not_anticipate_halting

/-! ## Constructed M7 witnesses and their direct criterion consumers -/

-- Construction/M7Witnesses.lean (`M7-HIST-EVALN`, `M7-CE-REPETITION`,
-- `M7-PATIENT-CLOCK`, `M7-PREFIX-PATCH`)
#assert_axioms_clean
  codeEvalnNat_polyFueled boundedEvalnCompiler EfficientRepeatedEnumeration.ofCE
  SettlementChecker.ofComputations PatientSettlementClock.ofComputations
  liaEfficientPrefixPatch

-- Construction/QuotationAffine.lean (`M7-QUOTE-AFFINE`)
#assert_axioms_clean
  lic_introspection_ofCode lic_paradox_resistance_ofDiagonal
  lic_expectations_of_probabilities_ofCode lic_iterated_expectations_ofCode
  lic_self_trust_ofRepresentation lic_expected_future_expectations_ofRepresentation
  lic_no_expected_net_update_ofRepresentation
  lic_no_expected_net_update_conditional_ofRepresentation

-- Construction/FeedbackEmission.lean (`M7-FEEDBACK-EMIT`)
#assert_axioms_clean
  feedbackTraderEmissionSigns lic_wubaff_ofFeedbackTruth
  boundedCombination_wubaff_ofFeedbackTruth luv_wubexp_ofFeedbackTruth

-- Construction/FeedbackTruth.lean (`M7-FEEDBACK-TRUTH`)
#assert_axioms_clean
  feedbackTruthSequence lic_wubaff_ofComputation boundedCombination_wubaff_ofComputation
  luv_wubexp_ofComputation

-- Construction/BitPrefixSyntax.lean (`M7-DUS-PREFIX-SYNTAX`)
#assert_axioms_clean
  bitPrefixSentencesOfIndependentAtoms lic_domination_universalSemimeasure_ofIndependentAtoms

-- Construction/ConditioningPresentation.lean (`M7-SCON-PRESENTATION`)
#assert_axioms_clean
  conditioningPresentationOfComputations lic_conditioned_gated_ofComputations

-- Construction/ConditioningCompiler.lean (`M7-SCON-COMPILER`)
#assert_axioms_clean
  conditionedTranslation_preserves_ec gatedConditioningOperationalWitness
  denominatorPatchedGatedConditioningOperationalWitness
  lic_conditioned_gated_ofMarketComputation lic_conditioned_gated_ofComputationsAndMarket

-- Construction/LUVSyntax.lean (`M7-LUV-SYNTAX`)
#assert_axioms_clean LUVCombinationSyntax.meshSoftmaxOperationalWitness

-- Construction/ComputationSyntax.lean (`M7-COMP-SYNTAX`)
#assert_axioms_clean
  representedSemidecidableClaimsOfComputation representedDecidableClaimsOfComputation
  inconsistentTheoryClaimsOfComputation
  lic_belief_finitistic_consistency_ofComputation
  lic_belief_stronger_theory_consistency_ofComputation
  lic_disbelief_inconsistent_theories_ofComputation
  lic_learns_halting_patterns_ofComputation
  lic_learns_provable_nonhalting_patterns_ofComputation
  lic_does_not_anticipate_halting_ofComputation

end LogicalInduction
