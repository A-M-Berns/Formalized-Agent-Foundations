# Formalized Agent Foundations

This repo contains Lean 4 formalizations of important papers in the fields of agent foundations and open-source game
theory, built on the
[Foundation](https://github.com/FormalizedFormalLogic/Foundation) library of the Formalized Formal Logic project.

## Garrabrant et al. (2016) *Logical Induction* — in progress

`LogicalInduction/` formalizes [arXiv:1609.03543v5](https://arxiv.org/abs/1609.03543).
The spec is `notes/logical-induction-roadmap.md`; the active construction scope and handoff
are in `notes/next-session.md`. Defects found in the source paper, as distinct from
repository-faithfulness findings, are tracked in
[`notes/logical-induction-paper-errata.md`](notes/logical-induction-paper-errata.md).

The central construction is complete. For every computable deductive process,
`LogicalInduction.exists_logical_inductor` constructs a logical inductor, and
`LogicalInduction.LIA_is_logical_inductor` proves that the repository's concrete recursive
rational `LIA` satisfies the criterion. These theorems are unconditional and use none of
the M7 representation boundaries listed below. Their only reported axioms are Lean and
Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.

The M3–M5 property theorems are genuine but conditional: their paper-facing declarations
are named `lic_<node>` after the paper node they mirror (`lic_provind` ↔ `thm:provind`)
and take `[IsLogicalInductor P DP]`. Some additionally take an explicitly disclosed
representation or compiler interface. Fourteen of the fifteen M7 witness boundaries have been
constructed in Lean. Thus the public endpoint is **unconditional existence plus a
conditional, disclosed property tail**, not a claim that all of the paper's first-order
syntax and classical computability theory have been reconstructed in this propositional
development.

One modeling substitution is repository-wide rather than local to a boundary: efficient
computability (`EfficientlyComputable`, `PolyFueled`, and every "polynomial" certificate)
is defined relative to a fuel-clocked interpreter over `Nat.Partrec.Code`, not an abstract
complexity class (`dd:fuel` in the roadmap). Every efficiency claim below is correct
relative to that model. The model's cost anchor is Mathlib's standard clocked interpreter
`Nat.Partrec.Code.evaln`, and its trust facts are proved and audited as a model card
(`Framework/Computable.lean`, "`dd:fuel` model card"): every poly-fueled function is
primitive recursive (`PolyFueled.primrec`); the class is closed under composition, pairing,
and bounded primitive recursion and contains runtime multiplication, division, and gcd
(`gcdc_polyFueled`); it provably excludes exponential-output functions
(`not_polyFueled_two_pow`) — a size-based separation only, since time-based lower bounds
and any equivalence with machine-model polynomial time remain unproved; and the syntactic
`EF.cost` measure agrees two-sidedly with serialized token length up to a factor of 3
(`serialize_length_le_cost` / `cost_le_serialize_length`). One interpreter subtlety is
load-bearing: `evaln` outputs can genuinely exceed the fuel
(`evaln_output_can_exceed_fuel`), which is why `PolyFueled` carries a polynomial bound on
output size separately from the fuel bound.

`LogicalInduction.brouwer_fixed_point`, used by the construction, was proved from scratch
via Sperner's lemma because Mathlib has no suitable Brouwer theorem. Its proof body was
autoformalized by Harmonic's Aristotle and revalidated in this repository; its statement
and axiom report are part of the audited surface, while its roughly 1,300-line generated
interior has not received a human line-by-line read-through.

### Axioms and disclosed M7 boundaries

There are no `axiom` declarations or executable `sorry`s in `LogicalInduction/`. The
three names in the capstone axiom reports (`propext`, `Classical.choice`, `Quot.sound`) are
standard dependencies, not project-specific postulates. The remaining assumptions are
ordinary hypotheses on the conditional property theorems. They are isolated below rather
than being confused with the unconditional existence result.

These cleanliness claims are checked by the build: `AxiomAudit.lean` (a standalone build target)
enumerates every public endpoint and fails compilation if any of them acquires an axiom
beyond the three named above or ceases to exist.

The primary paper citation in the table is Garrabrant et al., especially its named theorem
and Appendix sections. Older primary sources cover facts imported at the boundary: Gödel's
arithmetization and diagonal construction
([1931](https://doi.org/10.1007/BF01700692)), Kleene's general-recursive and arithmetical-
predicate machinery ([1936](https://doi.org/10.1007/BF01565439),
[1943](https://doi.org/10.1090/S0002-9947-1943-0007371-8)), Solomonoff's universal
inductive probability ([1964, Part I](https://doi.org/10.1016/S0019-9958(64)90223-2)),
Chaitin's self-delimiting program-size complexity
([1975](https://doi.org/10.1145/321892.321894)), and Zvonkin and Levin's algorithmic
probability/universal semimeasure treatment
([1970](https://doi.org/10.1070/RM1970v025n06ABEH001269)).

Paths abbreviated as `Properties/...` or `Framework/Expectations.lean` in the table are relative to
`LogicalInduction/`.

| Boundary | Exact Lean interface and source | Paper node and concrete realizer / primary citation | Conditional consumers | What is assumed, and what is not |
|---|---|---|---|---|
| `M7-COMP-SYNTAX` | Boundary interfaces in `Properties/MetaLearning.lean`; `ComputationClaim`, `ComputationTheoryPresentation`, the three boundary constructors, and six direct consumers in `Construction/Witnesses/ComputationSyntax.lean` | The paper's “represents computations” convention (§2.1) and `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` (Apps. `pac`–`dontwait`). The construction uses FFL's quoted arithmetic `codeOfREPred` schemas and `re_complete`, an injective compact Gödel naming layer, and repository `Nat.Partrec.Code` semantics; see [Kleene 1936](https://doi.org/10.1007/BF01565439), [Kleene 1943](https://doi.org/10.1090/S0002-9947-1943-0007371-8), and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | The six `..._ofComputation` entry points for finitistic/stronger consistency, inconsistent theories, halting, provable nonhalting, and non-anticipation | Constructed from polynomial machine/input codes plus a `ComputationTheoryPresentation`: a `Δ₁` arithmetic theory, a computable `DP`, and pointwise translation of proofs of the fixed universal schemas into `DP`. FFL supplies weak positive r.e. representation, so bounded false claims use a separate complementary r.e. failure schema whose proof translates to the negated market literal. No price, convergence, exploitation, or logical-inductor conclusion is assumed. |
| `M7-QUOTE-AFFINE` | Boundary interfaces in `Properties/Introspection.lean` and `Properties/SelfTrust.lean`; arithmetic quotation codes, FFL diagonalization, concrete same-day/deferred affine constructors, and direct consumers in `Construction/Witnesses/QuotationAffine.lean` | First-order quotation and diagonalization for `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` (Apps. `ref`–`st`). Boolean and rational threshold claims use dual FFL arithmetic representations. For `thm:lp`, Kleene's second recursion theorem constructs a selector that prices its own public atom, while FFL's genuine `parameterizedFixedpoint` represents that same predicate and is proved equivalent to the same-day price comparison. Explicit affine meshes and image-gated cross-precision corrections realize the market packages. See [Gödel 1931](https://doi.org/10.1007/BF01700692), [Garrabrant et al.](https://arxiv.org/abs/1609.03543), and the Kleene sources above. | The eight direct `..._ofCode`, `..._ofDiagonal`, and `..._ofRepresentation` entry points for `ref` through `st` | Constructed from a `QuotationTheoryPresentation`, polynomial sentence/rational/LUV codes, and explicit completed-theory `ValuesAt` representation facts. Paradox resistance derives its public diagonal from a named `MarketComputation` and accepts no semantic self-reference premise. The four deferred constructors additionally require a strictly increasing deferral, because the paper's image-reindexing argument is ambiguous for noninjective deferrals; the abstract `AffineQuoteEq/GE` consumers remain general. No price convergence, introspection, paradox-resistance, expectation, or self-trust conclusion is assumed. |
| `M7-PREFIX-MACHINE` | `PrefixMachinePresentation`, `OccamThresholdEmission`, `PrefixNegationCompiler` in `Properties/OccamBounds.lean` | `thm:ob` / App. `ob`. A prefix machine supplies sentence coverage, from-below `2^{-κ}` approximations, Kraft's finite inequality, gate-token arithmetic, and fixed-overhead negation; see [Chaitin 1975](https://doi.org/10.1145/321892.321894) and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_occam_lower`, `lic_occamBounds` | **Both instances constructed.** Fixed self-delimiting code (`Construction/Witnesses/PrefixMachine.lean`): unconditional. Self-delimiting **universal** machine (`Construction/Witnesses/UniversalPrefix.lean`, `UPrefix.kappaU`, invariance theorem `UPrefix.kappaU_le_of_prefixMachine`): every mathematical field proved — `dom U` is prefix-free by construction, so Kraft is not assumed — with one conclusion-free operational input, `UPrefix.UniversalPrefixComputation` (a `Nat.Partrec.Code` for the *exact* from-below stage table; the polynomial clock is constructed on top of it, not assumed). |
| `M7-FEEDBACK-EMIT` | Interfaces `FeedbackTraderEmission`, `.Family`, `.Signs` in `Properties/Pseudorandomness.lean`; concrete constructor `FeedbackEmission.feedbackTraderEmissionSigns` in `Construction/Witnesses/FeedbackEmission.lean` | `thm:wubaff` / App. `wubaff`, reused by `thm:wubexp` / App. `wubexp`. The constructed bounded dovetail runs the deferral code at a day-polynomial clock, emits the literal open/close trade list for every rational Kelly fraction and both signs, and proves exact list equality; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_wubaff`, `LUVCombination.BoundedSequence.wubexp` | Constructed from `DeferralFunction.fueled`, `PolySequence`, and `PGenerableWeighting`; it assumes no market values, wealth bound, bias, exploitation, convergence, or LI conclusion. |
| `M7-FEEDBACK-TRUTH` | Boundary `FeedbackTruthSequence` in `Properties/Pseudorandomness.lean`; operational `FeedbackTruthComputation`, literal sparse compiler, `FeedbackTruth.feedbackTruthSequence`, direct computation-backed consumers in `Construction/Witnesses/FeedbackTruth.lean`, and constructed-LIA corollaries in `FeedbackUnconditional.lean` | `thm:wub`, `thm:wubaff` / App. `wubaff`, and `thm:wubexp`. A bounded simulation of the paper's `poly(f(k+1))` completed-theory-value program emits `A_{f k} - truth(f k)` exactly on day `f(k+1)` and literal zero elsewhere; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `FeedbackTruth.lic_wub_ofComputation`, `.lic_wubaff_ofComputation`, `.boundedCombination_wubaff_ofComputation`, `.luv_wubexp_ofComputation`, and their four `_unconditional` variants | Constructed from completed-theory determination, an explicit rational program/deadline law, and the ordinary affine syntax/bounds. The `_unconditional` variants instantiate the concrete `LIA` over `theoremDP`, whose computability and finite-stage plausible worlds are proved in-repo. The computation certificate assumes no prices, delayed accuracy, bias, convergence, or LI conclusion; `FeedbackTruthSequence.accurate` still derives accuracy using affine provability induction. |
| `M7-DUS-APPROX` | **Constructed** — `DUSApproximationPresentation`, `DUSThresholdEmission` in `Properties/UniversalSemimeasure.lean`, inhabited by `Dovetail.dusApproximationPresentation` / `Dovetail.dusThresholdEmission` in `Construction/Witnesses/UniversalDovetailer.lean` | `thm:dus` / App. `dus`. The paper's bounded-simulation slowdown turns a lower semicomputable universal semimeasure into a polynomially emitted rational approximation; see [Solomonoff 1964](https://doi.org/10.1016/S0019-9958(64)90223-2), [Zvonkin–Levin 1970](https://doi.org/10.1070/RM1970v025n06ABEH001269), and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_domination_universalSemimeasure` | Every field is now built, not assumed: the explicit universal dovetailer `M*` (universality proved, `universalMass_dominates`), with the polynomially clocked stage emitter `dusApprox_polyRatCodes` (the `evaln` self-clamp makes the emitter *select* exact stage values under a polynomial clock) and the derived threshold streams.  Unconditional endpoints: `lic_domination_dovetailSemimeasure_unconditional`, `lic_domination_everyLowerSemicomputable_unconditional`. |
| `M7-DUS-PREFIX-SYNTAX` | Interfaces `IndependentBitAtoms` / `BitPrefixSentences` in `Properties/UniversalSemimeasure.lean`; operational `BitPrefixCodeComputation`, concrete `bitPrefixSentence`, `bitPrefixSentencesOfIndependentAtoms`, and `lic_domination_universalSemimeasure_ofIndependentAtoms` in `Construction/Witnesses/BitPrefixSyntax.lean` | `thm:dus` / App. `dus`; also supplies the prefix language used by `thm:strict`. The constructed stock decode-with-empty enumeration and literal conjunctions realize exact bit-prefix semantics, including the empty prefix, and reduce stagewise realizability to finite independence; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_domination_universalSemimeasure_ofIndependentAtoms`; indirectly `lic_strict_domination_universalSemimeasure` through `StrictSeparatorPresentation` | Constructed from total (infinite-assignment) compatibility of an atom sequence and one compact program emitting the actual conjunction code with polynomial fuel. It assumes no prefix semantics, price, payoff, semimeasure domination, or asymptotic market conclusion. |
| `M7-STRICT-SEPARATORS` | **Constructed** — `StrictSeparatorPresentation` in `Properties/UniversalSemimeasure.lean`, inhabited by `strictSeparatorPresentationOfKleene` in `Construction/Witnesses/StrictSeparators.lean` | `thm:strict` / App. `strict`. Disjoint recursively inseparable c.e. sets yield a c.e. theory of single-bit constraints; the appendix's computability argument shows every universal continuous semimeasure gives the stagewise class of consistent strings vanishing total mass; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `strict_domination_of_null_separator_class`, `lic_strict_domination_universalSemimeasure`, `lic_strict_domination_universalSemimeasure_ofAtomCodes` | Every field of the interface is now built, not assumed: Kleene's pair is recursively inseparable (`kleene_recursively_inseparable`), the constraint theory's enumerator is built from the atom codes (`separatorConstraintCE`), and the stage classes are null by the Kučera–Demuth argument (`separatorClass_mass_tendsto_zero`: the class masses are antitone, and a positive floor would let the semimeasure's own bounded-fuel approximants compute a separator by majority vote). The single remaining input of `strictSeparatorPresentationOfKleene` is computability of the atom family's Gödel codes, proved for the repo's concrete atoms (`ordinaryAtom_code_computable`). The earlier *nested prefix family* shape of this interface is provably uninhabitable — see `no_ce_null_prefix_family`. |
| `M7-SCON-COMPILER` | Interfaces `EventualConditioningFloor` and `EventualConditioningOperationalWitness` in `Properties/Conditioning.lean`; exact rational conditional-market programs, finite-zero price-leaf rewriting, arbitrary-stream price/frame transducers, and direct consumers in `Construction/Witnesses/ConditioningCompiler.lean` | `thm:scon` / App. `scon`. Uniform Non-Dogmatism plus Preemptive Learning produce an eventual floor; exact rational prefix prices reduce the exceptions to the zero-denominator days, where the capped quote is the constant `1`. The parser-transparent compiler rewrites those leaves, counts trades, emits both locally gated legs, and starts after the finite cutoff; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_conditioned_eventual_ofMarketComputation`, `lic_conditioned_fixed_ofComputationAndMarket`, `lic_conditioned_growing_ofComputationsAndMarket`, and the two paper-facing constructed-LIA corollaries | Constructed from a named rational base-market computation, polynomial condition codes, and joint consistency. Economic loss, failed-condition behavior, finite-prefix exploit preservation, wealth floors, exploit transport, and LI closure are proved outside the operational certificate. The repaired path stays on the original market and does not invoke unrestricted finite-perturbation closure. |
| `M7-SCON-PRESENTATION` | Interface `ConditioningPresentation` in `Properties/Conditioning.lean`; concrete `deductiveStageCondition`, fixed-sentence and growing-stage presentations, `DeductiveProcessComputation.union`, and their computation constructors in `Construction/Witnesses/ConditioningPresentation.lean` | `thm:scon` / App. `scon`. The growing condition is the canonical finite conjunction of the extra stage, with exact Boolean semantics including the empty stage; the fixed form uses the constant one-sentence process. A primitive-recursive code-sorted union normalizer composes stage programs; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | The fixed and growing `M7-SCON-COMPILER` endpoints | Constructed from an ordinary base-process computation and, for the growing form, one compact operational program emitting the actual extra-stage conjunction code with polynomial fuel. It assumes no condition semantics, combined-process computation, conditional prices, trader, wealth, exploitation, or LI conclusion. |
| `M7-LUV-SYNTAX` | Boundary interfaces `LUV.PolyThresholdCodes`/`PolyThresholdCodeSeq` in `Framework/Expectations.lean` and `LUVCombination.PolySequence`, `WorldValued`, `ConvergencePresentation`, `ExactTheoryPresentation`, `MeshSoftmaxOperationalWitness` in `Properties/ExpectationProperties.lean`; concrete compact thresholds, semantic presentations, cross-precision meshes, and `LUVCombinationSyntax.meshSoftmaxOperationalWitness` in `Construction/Witnesses/LUVSyntax.lean` | `def:luv`, `thm:expprovind`, `thm:expcoh`, `thm:perexpkno`, `thm:exppolymax`, `thm:recurringunbiasednessexp`, `thm:wubexp`, `thm:prandexp` and their appendices. First-order threshold formulas plus the paper's finite soft-max mesh realize the packages; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | The expectation-property tail, especially `BoundedSequence.exppolymax`, `.perexpkno`, `.expcoh`, `.recurringunbiasednessexp`, `.wubexp`, and `.prandexp` | Constructed from `LUVCombinationSyntax` plus its conclusion-free stage/completed-theory representation laws: compact threshold codes, exact semantic presentations, and polynomial/bounded/magnitude certificates for the concrete soft-max meshes. It assumes no expectation limit, persistence, unbiasedness, pseudorandom-learning, or preemptive-learning conclusion. |

### M7 witness inventory

| # | Boundary | Endpoint status | Evidence / disclosure |
|---:|---|---|---|
| 1 | `M7-HIST-EVALN` | **constructed** | `codeEvalnNat_polyFueled`, `boundedEvalnCompiler` (`Construction/Witnesses/M7Witnesses.lean`) |
| 2 | `M7-CE-REPETITION` | **constructed** | `EfficientRepeatedEnumeration.ofCE` (`Construction/Witnesses/M7Witnesses.lean`) |
| 3 | `M7-PATIENT-CLOCK` | **constructed** | `SettlementChecker.ofComputations`, `PatientSettlementClock.ofComputations` (`Construction/Witnesses/M7Witnesses.lean`) |
| 4 | `M7-PREFIX-PATCH` | **constructed** | `liaEfficientPrefixPatch` (`Construction/Witnesses/M7Witnesses.lean`) |
| 5 | `M7-QUOTE-AFFINE` | **constructed** | Arithmetic quotation/diagonal codes, a market-derived public fixed point for paradox resistance, concrete same-day/deferred packages, and eight direct consumers (`Construction/Witnesses/QuotationAffine.lean`) |
| 6 | `M7-PREFIX-MACHINE` | **constructed** (fixed code) / **constructed modulo one computability input** (universal machine) | `prefixMachinePresentation`, `lic_occam_lower_ofPrefixMachine`, `lic_occamBounds_ofPrefixMachine` (`Construction/Witnesses/PrefixMachine.lean`); `UPrefix.universalPrefixPresentation`, `UPrefix.lic_occam_lower_ofUniversalPrefix`, `UPrefix.lic_occamBounds_ofUniversalPrefix` (`Construction/Witnesses/UniversalPrefix.lean`), the latter conditional on `UPrefix.UniversalPrefixComputation` |
| 7 | `M7-FEEDBACK-EMIT` | **constructed** | `FeedbackEmission.feedbackTraderEmissionSigns` (`Construction/Witnesses/FeedbackEmission.lean`) |
| 8 | `M7-FEEDBACK-TRUTH` | **constructed** | `FeedbackTruth.feedbackTruthSequence`, the four `..._ofComputation` consumers, and their `_unconditional` corollaries over `theoremDP`/`LIA` (`Construction/Witnesses/FeedbackTruth.lean`, `FeedbackUnconditional.lean`) |
| 9 | `M7-DUS-PREFIX-SYNTAX` | **constructed** | `bitPrefixSentencesOfIndependentAtoms`, `lic_domination_universalSemimeasure_ofIndependentAtoms` (`Construction/Witnesses/BitPrefixSyntax.lean`) |
| 10 | `M7-SCON-COMPILER` | **constructed** | `eventualConditioningOperationalWitness`, `lic_conditioned_fixed_ofComputationAndMarket`, `lic_conditioned_growing_ofComputationsAndMarket`, and their constructed-LIA corollaries (`Construction/Witnesses/ConditioningCompiler.lean`, `UnconditionalOverLIA.lean`) |
| 11 | `M7-SCON-PRESENTATION` | **constructed** | `conditioningPresentationOfComputations`, `fixedConditioningPresentation`, `lic_conditioned_gated_ofComputations` (`Construction/Witnesses/ConditioningPresentation.lean`) |
| 12 | `M7-LUV-SYNTAX` | **constructed** | Compact thresholds, semantic presentations, cross-precision meshes, and `LUVCombinationSyntax.meshSoftmaxOperationalWitness` (`Construction/Witnesses/LUVSyntax.lean`) |
| 13 | `M7-DUS-APPROX` | **constructed** | `Dovetail.dusApproximationPresentation`, `dusApprox_polyRatCodes`, `lic_domination_everyLowerSemicomputable_unconditional` (`Construction/Witnesses/UniversalDovetailer.lean`) |
| 14 | `M7-STRICT-SEPARATORS` | **constructed** | `kleene_recursively_inseparable`, `separatorClass_mass_tendsto_zero`, `strictSeparatorPresentationOfKleene`, `lic_strict_domination_universalSemimeasure_ofAtomCodes` (`Construction/Witnesses/StrictSeparators.lean`) |
| 15 | `M7-COMP-SYNTAX` | **constructed** | `representedSemidecidableClaimsOfComputation`, `representedDecidableClaimsOfComputation`, `inconsistentTheoryClaimsOfComputation`, and the six `..._ofComputation` consumers (`Construction/Witnesses/ComputationSyntax.lean`) |

The active construction target is recorded in `notes/next-session.md`; this inventory reports
what is concrete today. Constructing all fifteen would additionally require,
among other things, the remaining operational inputs recorded per boundary above (today:
the universal prefix machine's exact stage-table code, `UniversalPrefixComputation` — a
bounded-search `Primrec` obligation with no complexity content).  The universal prefix
machine with its Kraft proof, the universal lower semicomputable continuous semimeasure,
and the recursively-inseparable-set mass theorem are all now constructed
(`Construction/Witnesses/UniversalPrefix.lean`, `UniversalDovetailer.lean`,
`StrictSeparators.lean`, `KraftInequality.lean`). The present endpoint does
not claim that stronger scope.

## Barasz et al. (2014) *Robust Cooperation in the Prisoner's Dilemma via Provability Logic*.

The ModalAgents folder contains a formalization of this paper at the level of Gödel-Löb provability logic. It covers:

* the modal agent definition from §4;
* CooperateBot, DefectBot, FairBot, and PrudentBot;
* the GL fixed-point construction used to define interaction outcomes;
* the cooperation results for FairBot and PrudentBot from §§2-3;
* the modal agent fixed-point equation (§4, Thm 4.7);
* the modal agent behavioral result (§4, Thm 4.8, GL-level form);
* the rank-0 FairBot-to-CooperateBot result (§4, Thm 4.10);
* the generic lift from GL-provability to arithmetical realizations (§4, Thm 4.1).

### Axioms

**None.** Every ModalAgents endpoint reports only `propext`, `Classical.choice`, and
`Quot.sound` (checked by `AxiomAudit.lean`).

The one standard GL fact previously axiomatized — `glFixedPoint_thm42`, the de
Jongh–Sambin–Bernardi modal fixed-point existence theorem (single-variable form; Barasz
§4, Thm 4.2, which they state without proof, citing Lindström (1996) Thm 11) — is now
**proved**. It is discharged through `ProvabilityLogic/`, an autoformalized (Harmonic
Aristotle) sequent-calculus development: a de Jongh–Sambin construction via Maehara
interpolation and Löb's rule, transported to Foundation's `Modal.GL` through finite Kripke
completeness, with the `GlFixedPointBridge` translation in `FixedPoint.lean`. Like the
Brouwer construction, it is **kernel-gated**: its statement and axiom report are audited,
but its roughly 9,500-line generated `ProvabilityLogic/` interior has not received a human
line-by-line read-through. `ProvabilityLogic`'s `Formula`-level notations are `scoped` so
they do not collide with Foundation's modal notation.

Fixed-point *uniqueness* (Barasz §4, Thm 4.3; Lindström Thm 12) is proved in
`FixedPoint.lean` as `glFixedPoint_uniqueness`, via a boxed-equivalence substitution lemma
and Löb's rule.

### Files

* `ModalAgents/GL.lean` — GL lemmas used by the agent proofs.
* `ModalAgents/ModalAgent.lean` — modal agents and the four concrete agents.
* `ModalAgents/FixedPoint.lean` — GL fixed-point existence/uniqueness theorems, the `ProvabilityLogic/` bridge, and substitution congruence.
* `ProvabilityLogic/` — autoformalized sequent-calculus development discharging GL fixed-point existence (kernel-gated).
* `ModalAgents/Cooperation.lean` — outcomes, cooperation/defection, and the main cooperation theorems.
* `ModalAgents/Behavioral.lean` — behavioral equivalence for modal agents.

### Scope

This formalization deals only with modal agents, rather than arbitrary
arithmetic agents. Therefore, Corrollary 4.9 about `CliqueBot` (an algorithm 
that only cooperates with syntactic copies of itself) is outside the scope.
Game-theoretic program equilibrium framing is also left for a future paper.
