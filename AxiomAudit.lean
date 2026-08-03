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
by the autoformalized `ProvabilityLogic/` sequent calculus (see `ModalAgents/FixedPoint.lean`),
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
`notes/1609.03543v5-main.tex`, comma-separated — no ranges, no glosses, so every label
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
#assert_axioms_clean
  feedbackTruthSequence lic_wubaff_ofComputation lic_wub_ofComputation
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
#assert_axioms_clean
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
  determined sequence poly bounded magnitude zero_value feedback_price
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
#assert_fields BoundedComputation
  machine input steps input_poly steps_poly truth_iff
#assert_fields CEEnumeration
  code halts outputs_sound
#assert_fields CompactConditioningProcessComputation
  toDeductiveProcessComputation condition_codes
#assert_fields CompletedAffineQuoteApprox
  toAffineQuotePortfolio theory_coherent
#assert_fields CompletedAffineQuoteEq
  toAffineQuotePortfolio theory_coherent
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
