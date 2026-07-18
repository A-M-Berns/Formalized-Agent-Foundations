# Formalized Agent Foundations

This repo contains Lean 4 formalizations of important papers in the fields of agent foundations and open-source game
theory, built on the
[Foundation](https://github.com/FormalizedFormalLogic/Foundation) library of the Formalized Formal Logic project.

## Garrabrant et al. (2016) *Logical Induction* — in progress

`LogicalInduction/` formalizes [arXiv:1609.03543v5](https://arxiv.org/abs/1609.03543).
The spec is `notes/logical-induction-roadmap.md`; the active construction scope and handoff
are in `notes/next-session.md`.

The central construction is complete. For every computable deductive process,
`LogicalInduction.exists_logical_inductor` constructs a logical inductor, and
`LogicalInduction.LIA_is_logical_inductor` proves that the repository's concrete recursive
rational `LIA` satisfies the criterion. These theorems are unconditional and use none of
the M7 representation boundaries listed below. Their only reported axioms are Lean and
Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.

The M3–M5 property theorems are genuine but conditional: their paper-facing declarations
take `[IsLogicalInductor P DP]`. Some additionally take one of nine explicitly disclosed
representation or compiler interfaces. Six other M7 witnesses have been constructed in
Lean. Thus the public endpoint is **unconditional existence plus a conditional, disclosed
property tail**, not a claim that all of the paper's first-order syntax and classical
computability theory have been reconstructed in this propositional development.

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

Paths abbreviated as `Properties/...` or `Expectations.lean` in the table are relative to
`LogicalInduction/`.

| Boundary | Exact Lean interface and source | Paper node and concrete realizer / primary citation | Conditional consumers | What is assumed, and what is not |
|---|---|---|---|---|
| `M7-COMP-SYNTAX` | `RepresentedSemidecidableClaims`, `RepresentedDecidableClaims`, and `InconsistentTheoryClaims` in `LogicalInduction/Properties/MetaLearning.lean` | The paper's “represents computations” convention (§2.1) and `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`, `thm:dontwait` (Apps. `pac`–`dontwait`). A realizer is a first-order Gödel coding with the representability theorem for recursive predicates; see [Kleene 1936](https://doi.org/10.1007/BF01565439), [Kleene 1943](https://doi.org/10.1090/S0002-9947-1943-0007371-8), and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_belief_finitistic_consistency`, `lic_belief_stronger_theory_consistency`, `lic_disbelief_inconsistent_theories`, `lic_learns_halting_patterns`, `lic_learns_provable_nonhalting_patterns`, `lic_does_not_anticipate_halting` | Assumes polynomial sentence emission and eventual proof/refutation when the represented computation has the stated truth value. It assumes no price, convergence, exploitation, or logical-inductor conclusion. |
| `M7-QUOTE-AFFINE` | Same-day interfaces `CompletedAffineQuoteEq`, `CurrentPriceExpectationQuote`, `CurrentExpectationQuote`, `IntrospectionIntervalQuote`, `ParadoxResistanceQuote` in `Properties/Introspection.lean`; deferred interfaces `AffineQuotePortfolio`, `AffineQuoteEq`, `AffineQuoteGE`, `ExpectedFutureExpectationQuote`, `FuturePriceQuote`, `ConditionalExpectationQuote`, `SelfTrustQuote` in `Properties/SelfTrust.lean` | First-order quotation and diagonalization for `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` (Apps. `ref`–`st`). A realizer quotes the concrete LIA computation using Gödel coding, representability, and fixed-point/diagonal syntax; see [Gödel 1931](https://doi.org/10.1007/BF01700692), [Garrabrant et al.](https://arxiv.org/abs/1609.03543), and the Kleene sources above. | `lic_introspection`, `lic_paradox_resistance`, `lic_expectations_of_probabilities`, `lic_iterated_expectations`, `lic_expected_future_expectations`, `lic_no_expected_net_update`, `lic_no_expected_net_update_conditional`, `lic_self_trust` | This is not syntax alone. It assumes exact current-price portfolio identities and completed-world or delayed revelation semantics; `AffineQuoteEq/GE` also assume deferred-price coherence at `f n`. It does **not** assume the consumers' resulting diagonal introspection, expectation, paradox-resistance, or self-trust conclusions. |
| `M7-PREFIX-MACHINE` | `PrefixMachinePresentation`, `OccamThresholdEmission`, `PrefixNegationCompiler` in `Properties/OccamBounds.lean` | `thm:ob` / App. `ob`. A concrete universal self-delimiting machine supplies sentence coverage, from-below `2^{-κ}` approximations, Kraft's finite inequality, gate-token arithmetic, and fixed-overhead negation; see [Chaitin 1975](https://doi.org/10.1145/321892.321894) and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_occam_lower`, `lic_occamBounds` | Assumes the prefix-complexity presentation, convergence/Kraft facts, and negation overhead. It contains no market price, possible-world, trader wealth, exploitation, or Occam-bound conclusion. |
| `M7-FEEDBACK-EMIT` | Interfaces `FeedbackTraderEmission`, `.Family`, `.Signs` in `Properties/Pseudorandomness.lean`; concrete constructor `FeedbackEmission.feedbackTraderEmissionSigns` in `Construction/FeedbackEmission.lean` | `thm:wubaff` / App. `wubaff`, reused by `thm:wubexp` / App. `wubexp`. The constructed bounded dovetail runs the deferral code at a day-polynomial clock, emits the literal open/close trade list for every rational Kelly fraction and both signs, and proves exact list equality; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_wubaff`, `LUVCombination.BoundedSequence.wubexp` | Constructed from `DeferralFunction.fueled`, `PolySequence`, and `PGenerableWeighting`; it assumes no market values, wealth bound, bias, exploitation, convergence, or LI conclusion. |
| `M7-FEEDBACK-TRUTH` | `FeedbackTruthSequence` in `Properties/Pseudorandomness.lean` | `thm:wubaff` / App. `wubaff`, reused by `thm:wubexp`. The paper's `poly(f(k+1))` completed-theory-value computation yields the sparse centered affine sequence; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_wubaff`, `LUVCombination.BoundedSequence.wubexp` | Assumes completed-theory determination, polynomial/bounded sparse syntax, zero completed-world value, and the exact delayed price identity. It does not assume delayed-price accuracy, weighted unbiasedness, or convergence; `FeedbackTruthSequence.accurate` derives accuracy using affine provability induction. |
| `M7-DUS-APPROX` | `DUSApproximationPresentation`, `DUSThresholdEmission` in `Properties/UniversalSemimeasure.lean` | `thm:dus` / App. `dus`. The paper's bounded-simulation slowdown turns a lower semicomputable universal semimeasure into a polynomially emitted rational approximation; see [Solomonoff 1964](https://doi.org/10.1016/S0019-9958(64)90223-2), [Zvonkin–Levin 1970](https://doi.org/10.1070/RM1970v025n06ABEH001269), and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_domination_universalSemimeasure` | Assumes a nonnegative from-below rational table converging to prefix mass and polynomial emission of it and the derived gate tokens. It contains no market price, purchase, possible-world, exploitation, or domination conclusion. |
| `M7-DUS-PREFIX-SYNTAX` | Interfaces `IndependentBitAtoms` / `BitPrefixSentences` in `Properties/UniversalSemimeasure.lean`; operational `BitPrefixCodeComputation`, concrete `bitPrefixSentence`, `bitPrefixSentencesOfIndependentAtoms`, and `lic_domination_universalSemimeasure_ofIndependentAtoms` in `Construction/BitPrefixSyntax.lean` | `thm:dus` / App. `dus`; also supplies the prefix language used by `thm:strict`. The constructed stock decode-with-empty enumeration and literal conjunctions realize exact bit-prefix semantics, including the empty prefix, and reduce stagewise realizability to finite independence; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_domination_universalSemimeasure_ofIndependentAtoms`; indirectly `lic_strict_domination_universalSemimeasure` through `StrictSeparatorPresentation` | Constructed from finite compatibility of an atom sequence and one compact program emitting the actual conjunction code with polynomial fuel. It assumes no prefix semantics, price, payoff, semimeasure domination, or asymptotic market conclusion. |
| `M7-STRICT-SEPARATORS` | `StrictSeparatorPresentation` in `Properties/StrictSemimeasure.lean` | `thm:strict` / App. `strict`. Disjoint recursively inseparable c.e. sets yield nested finite separator constraints; the appendix's computability argument shows every universal continuous semimeasure gives their separator class vanishing mass; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `strict_domination_of_null_prefix_theory`, `lic_strict_domination_universalSemimeasure` | Assumes nested unbounded prefixes, efficient repetition, joint stagewise realizability, and the substantive `mass_tendsto_zero` theorem. It contains no market prices and assumes no strict-domination conclusion. |
| `M7-SCON-COMPILER` | `GatedConditioningOperationalWitness` in `Properties/Conditioning.lean` | `thm:scon` / App. `scon`. The paper's finite-prefix denominator patch supplies a positive floor, a computable rational conditional market, and a polynomial transducer for the concrete gated trader translation; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_conditioned_gated` | Assumes the market-dependent denominator floor, conditional-market computability, and token-level translation efficiency. The loss bound, failed-condition behavior, wealth floor, exploit transport, and LI closure are proved outside the interface. |
| `M7-SCON-PRESENTATION` | Interface `ConditioningPresentation` in `Properties/Conditioning.lean`; concrete `deductiveStageCondition`, `DeductiveProcessComputation.union`, `conditioningPresentationOfComputations`, and `lic_conditioned_gated_ofComputations` in `Construction/ConditioningPresentation.lean` | `thm:scon` / App. `scon`. The constructed condition is the canonical finite conjunction of the extra stage, with exact Boolean semantics including the empty stage. A primitive-recursive code-sorted union normalizer composes the two stage programs; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_conditioned_gated_ofComputations` and the construction of `M7-SCON-COMPILER` | Constructed from ordinary computations for the two processes and one compact operational program that emits the actual extra-stage conjunction code with polynomial fuel. It assumes no condition semantics, combined-process computation, conditional prices, trader, wealth, exploitation, or LI conclusion. |
| `M7-LUV-SYNTAX` | `LUV.PolyThresholdCodes`/`PolyThresholdCodeSeq` in `Expectations.lean`; `LUVCombination.PolySequence`, `WorldValued`, `ConvergencePresentation`, `ExactTheoryPresentation`, `MeshSoftmaxOperationalWitness` in `Properties/ExpectationProperties.lean` | `def:luv`, `thm:expprovind`, `thm:expcoh`, `thm:perexpkno`, `thm:exppolymax`, `thm:recurringunbiasednessexp`, `thm:wubexp`, `thm:prandexp` and their appendices. First-order threshold formulas plus the paper's finite soft-max mesh realize the packages; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | The expectation-property tail, especially `BoundedSequence.exppolymax`, `.perexpkno`, `.expcoh`, `.recurringunbiasednessexp`, `.wubexp`, and `.prandexp` | Assumes compact threshold syntax, daily/completed-world LUV semantics, exact theory values where needed, and polynomial/bounded/magnitude certificates for the concrete soft-max meshes. It assumes no expectation limit, persistence, unbiasedness, pseudorandom-learning, or preemptive-learning conclusion. |

### M7 witness inventory

| # | Boundary | Endpoint status | Evidence / disclosure |
|---:|---|---|---|
| 1 | `M7-HIST-EVALN` | **constructed** | `codeEvalnNat_polyFueled`, `boundedEvalnCompiler` (`Construction/M7Witnesses.lean`) |
| 2 | `M7-CE-REPETITION` | **constructed** | `EfficientRepeatedEnumeration.ofCE` (`Construction/M7Witnesses.lean`) |
| 3 | `M7-PATIENT-CLOCK` | **constructed** | `SettlementChecker.ofComputations`, `PatientSettlementClock.ofComputations` (`Construction/M7Witnesses.lean`) |
| 4 | `M7-PREFIX-PATCH` | **constructed** | `liaEfficientPrefixPatch` (`Construction/M7Witnesses.lean`) |
| 5 | `M7-QUOTE-AFFINE` | **disclosed** | Exact interfaces and assumptions in the table above |
| 6 | `M7-PREFIX-MACHINE` | **disclosed** | Exact interfaces and assumptions in the table above |
| 7 | `M7-FEEDBACK-EMIT` | **constructed** | `FeedbackEmission.feedbackTraderEmissionSigns` (`Construction/FeedbackEmission.lean`) |
| 8 | `M7-FEEDBACK-TRUTH` | **disclosed** | Exact interfaces and assumptions in the table above |
| 9 | `M7-DUS-PREFIX-SYNTAX` | **constructed** | `bitPrefixSentencesOfIndependentAtoms`, `lic_domination_universalSemimeasure_ofIndependentAtoms` (`Construction/BitPrefixSyntax.lean`) |
| 10 | `M7-SCON-COMPILER` | **disclosed** | Exact interfaces and assumptions in the table above |
| 11 | `M7-SCON-PRESENTATION` | **constructed** | `conditioningPresentationOfComputations`, `lic_conditioned_gated_ofComputations` (`Construction/ConditioningPresentation.lean`) |
| 12 | `M7-LUV-SYNTAX` | **disclosed** | Exact interfaces and assumptions in the table above |
| 13 | `M7-DUS-APPROX` | **disclosed** | Exact interfaces and assumptions in the table above |
| 14 | `M7-STRICT-SEPARATORS` | **disclosed** | Exact interfaces and assumptions in the table above |
| 15 | `M7-COMP-SYNTAX` | **disclosed** | Exact interfaces and assumptions in the table above |

The active construction target is recorded in `notes/next-session.md`; this inventory reports
what is concrete today. Constructing all fifteen would additionally require,
among other things, a first-order Gödel syntax and representability development, a concrete
universal prefix machine and Kraft proof, a universal lower semicomputable continuous
semimeasure, and the recursively-inseparable-set mass theorem. The present endpoint does
not claim that stronger scope.

## Barasz et al. (2014) *Robust Cooperation in the Prisoner's Dilemma via Provability Logic*.

The Barasz folder contains a formalization of this paper at the level of Gödel-Löb provability logic. It covers:

* the modal agent definition from §4;
* CooperateBot, DefectBot, FairBot, and PrudentBot;
* the GL fixed-point construction used to define interaction outcomes;
* the cooperation results for FairBot and PrudentBot from §§2-3;
* the modal agent fixed-point equation (§4, Thm 4.7);
* the modal agent behavioral result (§4, Thm 4.8, GL-level form);
* the rank-0 FairBot-to-CooperateBot result (§4, Thm 4.10);
* the generic lift from GL-provability to arithmetical realizations (§4, Thm 4.1).

### Axioms

Two standard GL fixed-point facts are currently axiomatized because they are not yet available in Foundation:

* `glFixedPoint_thm42`: fixed-point existence, in the single-variable form used by Barasz §4, Thm 4.2;
* `glFixedPoint_uniqueness`: fixed-point uniqueness, corresponding to Barasz §4, Thm 4.3.

These are the de Jongh-Sambin-Bernardi modal fixed-point theorem and its uniqueness theorem. 
These theorems are prior to the modal agent framework, and Barasz et al do not provide proofs of either.
Instead, they cite Lindström (1996) Thms 11 and 12 as a reference (full citation in `FixedPoint.lean`.)

### Files

* `Barasz/GL.lean` — GL lemmas used by the agent proofs.
* `Barasz/ModalAgent.lean` — modal agents and the four concrete agents.
* `Barasz/FixedPoint.lean` — fixed-point assumptions and substitution congruence.
* `Barasz/Cooperation.lean` — outcomes, cooperation/defection, and the main cooperation theorems.
* `Barasz/Behavioral.lean` — behavioral equivalence for modal agents.

### Scope

This formalization deals only with modal agents, rather than arbitrary
arithmetic agents. Therefore, Corrollary 4.9 about `CliqueBot` (an algorithm 
that only cooperates with syntactic copies of itself) is outside the scope.
Game-theoretic program equilibrium framing is also left for a future paper.
