# Logical Induction, formalized

A Lean 4 formalization of Garrabrant, Benson-Tilsen, Critch, Soares, Taylor,
[*Logical Induction*](https://arxiv.org/abs/1609.03543) (arXiv:1609.03543v5).

**Zero `sorry`, zero `axiom` declarations.** Every public endpoint reports only Lean's
standard `propext`, `Classical.choice`, `Quot.sound`, checked by the build
(`AxiomAudit.lean` at the repo root enumerates the full public surface and fails
compilation on any regression). Every paper label cited below is verified two-way by
script: every cited label exists in the paper source, and every annotated label has an
endpoint.

## The main theorem

For every computable deductive process, a logical inductor exists — in the paper's full
sense:

* `exists_computable_beliefSequence_logical_inductor` — there is a computable sequence
  of explicit finite-support rational belief states (one program emits the day-`n`
  association list) whose induced pricing satisfies the logical induction criterion.
* `LIA_is_logical_inductor` — the concrete recursively-constructed rational market
  built here (the paper's §5 algorithm: market maker via a from-scratch Sperner/Brouwer
  fixed point, budgeter, trading firm over a universal trader enumeration) satisfies
  the criterion.

These are unconditional. The property tail (§4 of the paper: convergence, coherence,
provability induction, calibration, unbiasedness, pseudorandomness, non-dogmatism,
Occam bounds, universal-semimeasure domination, conditioning, expectations,
introspection, paradox resistance, self-trust) is proved conditional on
`[IsLogicalInductor P DP]` — i.e. for *every* logical inductor, as in the paper — with
paper-facing names `lic_<node>` mirroring the paper's labels (`lic_provind` ↔
`thm:provind`). Where the paper's theorems need representation machinery (quotation,
arithmetic, computation-representing theories), that machinery is *constructed* over the
concrete inductor, yielding `_unconditional` endpoints with no hypotheses beyond the
statement's own data.

## The two disclosed modeling substitutions

Everything below is faithful to the paper except two declared substitutions. They are
the honest summary of this development's trust boundary:

1. **Efficient computability is a fuel-clocked interpreter model, not a machine
   complexity class.** Traders, markets, and every "polynomial" certificate are metered
   by Mathlib's clocked interpreter `Nat.Partrec.Code.evaln` under a polynomial fuel
   bound, emitting strategies as symbol/digit streams. The model card
   (`Framework/Computable.lean`) proves its calibration facts — poly-fueled ⟹ primitive
   recursive, closure under composition/pairing/bounded recursion/runtime division and
   gcd, a genuine separation (`2^n` is not poly-fueled) — and states the open question
   plainly: **there is no theorem that every polynomial-time trader in the paper's sense
   lands in this class.** Consequence, stated precisely: the property tail is unaffected
   (each exploiting trader is certified inside the class), but the existence theorem
   defeats this class rather than the paper's, and is weaker than the paper's `thm:li`
   if the inclusion fails.
2. **The logical substrate is propositional.** Sentences are Foundation's propositional
   formulas; the paper's first-order theory Θ appears through explicit interfaces
   (arithmetic theories instantiate them for the unconditional endpoints). In
   particular a logically uncertain variable is presented by its family of threshold
   sentences, with its world-value semantics carried as explicit, build-frozen
   certificate structures rather than derived from first-order syntax.

Two smaller residuals are disclosed at their endpoints: the growing-conjunction form of
closure-under-conditioning assumes joint consistency (the bridge to the paper's
unrestricted form is propositional compactness, which Foundation lacks; the
fixed-sentence form is hypothesis-free, exactly the paper's statement), and the
construction-backed self-trust chain assumes the deferral function is injective (the
paper asks only `f(n) > n`).

## Faithfulness process

The statement surface was hardened by fresh-context adversarial audit (independent
auditors plus a cross-family model check), followed by a fix wave in which each finding
was either repaired at the statement level or pinned to a verified obstruction — see
[`notes/faithfulness-audit-2026-07-28.md`](../notes/faithfulness-audit-2026-07-28.md)
for the complete finding-by-finding ledger, including its own corrected misjudgments.
The audit process also surfaced four errata in the paper itself (an invalid proof of
finite-perturbation closure, a swapped hypothesis pair, a decidability claim that
mentions a non-computable value, and a patience argument that implicitly assumes
monotone deferral), recorded with repairs in
[`notes/logical-induction-paper-errata.md`](../notes/logical-induction-paper-errata.md).

`brouwer_fixed_point`, used by the market maker, was proved from scratch via Sperner's
lemma (Mathlib has no Brouwer theorem). Its proof body was autoformalized by Harmonic's
Aristotle and kernel-revalidated here; its statement and axiom report are audited
surface, while the generated proof interior has not had a human line-by-line read.

## Layout

* `Framework/` — the paper's §2–3: sentences, markets, features, traders, exploitation,
  the criterion, efficient computability, expectations, and the shared asymptotic
  vocabulary.
* `Properties/` — the §4 property tail, one file per theorem family.
* `Construction/` — the §5 existence proof (market maker, budgeter, trading firm,
  trader enumeration, the inductor itself) and `Construction/Witnesses/` — the
  constructed representation machinery that discharges the property tail's interfaces
  over the concrete inductor.

## Representation boundaries — detailed accounting

The tables below record, for each representation interface the property tail consumes:
the exact Lean interface, the paper node it realizes, its consumers, and — the column
that matters — *what is assumed and what is not*. All fifteen are constructed; one
(`M7-PREFIX-PATCH`, feeding finite-perturbation closure) is constructed at the token
metering only, with the symbol-level residual disclosed in the table. (The `M7-` tags
are internal work-package names retained here as stable keys into the development
notes.)

### Axioms

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
| `M7-PREFIX-MACHINE` | `PrefixMachinePresentation`, `OccamThresholdEmission`, `PrefixNegationCompiler` in `Properties/OccamBounds.lean` | `thm:ob` / App. `ob`. A prefix machine supplies sentence coverage, from-below `2^{-κ}` approximations, Kraft's finite inequality, gate-token arithmetic, and fixed-overhead negation; see [Chaitin 1975](https://doi.org/10.1145/321892.321894) and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_occam_lower`, `lic_occamBounds` | **Both instances constructed, unconditionally.** Fixed self-delimiting code (`Construction/Witnesses/PrefixMachine.lean`). Self-delimiting **universal** machine (`Construction/Witnesses/UniversalPrefix.lean`, `UPrefix.kappaU`, invariance theorem `UPrefix.kappaU_le_of_prefixMachine`): every field proved — `dom U` is prefix-free by construction, so Kraft is not assumed; the *exact* from-below stage table is a bounded search and its `Nat.Partrec.Code` is constructed (`UPrefix.exists_uCode`), with the polynomial clock built on top of it. |
| `M7-FEEDBACK-EMIT` | Interfaces `FeedbackTraderEmission`, `.Family`, `.Signs` in `Properties/Pseudorandomness.lean`; concrete constructor `FeedbackEmission.feedbackTraderEmissionSigns` in `Construction/Witnesses/FeedbackEmission.lean` | `thm:wubaff` / App. `wubaff`, reused by `thm:wubexp` / App. `wubexp`. The constructed bounded dovetail runs the deferral code at a day-polynomial clock, emits the literal open/close trade list for every rational Kelly fraction and both signs, and proves exact list equality; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_wubaff`, `LUVCombination.BoundedSequence.wubexp` | Constructed from `DeferralFunction.fueled`, `PolySequence`, and `PGenerableWeighting`; it assumes no market values, wealth bound, bias, exploitation, convergence, or LI conclusion. |
| `M7-FEEDBACK-TRUTH` | Boundary `FeedbackTruthSequence` in `Properties/Pseudorandomness.lean`; operational `FeedbackTruthComputation`, literal sparse compiler, `FeedbackTruth.feedbackTruthSequence`, direct computation-backed consumers in `Construction/Witnesses/FeedbackTruth.lean`, and constructed-LIA corollaries in `FeedbackUnconditional.lean` | `thm:wub`, `thm:wubaff` / App. `wubaff`, and `thm:wubexp`. A bounded simulation of the paper's `poly(f(k+1))` completed-theory-value program emits `A_{f k} - truth(f k)` exactly on day `f(k+1)` and literal zero elsewhere; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `FeedbackTruth.lic_wub_ofComputation`, `.lic_wubaff_ofComputation`, `.boundedCombination_wubaff_ofComputation`, `.luv_wubexp_ofComputation`, and their four `_unconditional` variants | Constructed from completed-theory determination, an explicit rational program/deadline law, and the ordinary affine syntax/bounds. The `_unconditional` variants instantiate the concrete `LIA` over `theoremDP`, whose computability and finite-stage plausible worlds are proved in-repo. The computation certificate assumes no prices, delayed accuracy, bias, convergence, or LI conclusion; `FeedbackTruthSequence.accurate` still derives accuracy using affine provability induction. |
| `M7-DUS-APPROX` | **Constructed** — `DUSApproximationPresentation`, `DUSThresholdEmission` in `Properties/UniversalSemimeasure.lean`, inhabited by `Dovetail.dusApproximationPresentation` / `Dovetail.dusThresholdEmission` in `Construction/Witnesses/UniversalDovetailer.lean` | `thm:dus` / App. `dus`. The paper's bounded-simulation slowdown turns a lower semicomputable universal semimeasure into a polynomially emitted rational approximation; see [Solomonoff 1964](https://doi.org/10.1016/S0019-9958(64)90223-2), [Zvonkin–Levin 1970](https://doi.org/10.1070/RM1970v025n06ABEH001269), and [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_domination_universalSemimeasure` | Every field is now built, not assumed: the explicit universal dovetailer `M*` (universality proved, `universalMass_dominates`), with the polynomially clocked stage emitter `dusApprox_polyRatCodes` (the `evaln` self-clamp makes the emitter *select* exact stage values under a polynomial clock) and the derived threshold streams.  Unconditional endpoints: `lic_domination_dovetailSemimeasure_unconditional`, `lic_domination_everyLowerSemicomputable_unconditional`. |
| `M7-DUS-PREFIX-SYNTAX` | Interfaces `IndependentBitAtoms` / `BitPrefixSentences` in `Properties/UniversalSemimeasure.lean`; operational `BitPrefixCodeComputation`, concrete `bitPrefixSentence`, `bitPrefixSentencesOfIndependentAtoms`, and `lic_domination_universalSemimeasure_ofIndependentAtoms` in `Construction/Witnesses/BitPrefixSyntax.lean` | `thm:dus` / App. `dus`; also supplies the prefix language used by `thm:strict`. The constructed stock decode-with-empty enumeration and literal conjunctions realize exact bit-prefix semantics, including the empty prefix, and reduce stagewise realizability to finite independence; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_domination_universalSemimeasure_ofIndependentAtoms`; indirectly `lic_strict_domination_universalSemimeasure` through `StrictSeparatorPresentation` | Constructed from total (infinite-assignment) compatibility of an atom sequence and one compact program emitting the actual conjunction code with polynomial fuel. It assumes no prefix semantics, price, payoff, semimeasure domination, or asymptotic market conclusion. |
| `M7-STRICT-SEPARATORS` | **Constructed** — `StrictSeparatorPresentation` in `Properties/UniversalSemimeasure.lean`, inhabited by `strictSeparatorPresentationOfKleene` in `Construction/Witnesses/StrictSeparators.lean` | `thm:strict` / App. `strict`. Disjoint recursively inseparable c.e. sets yield a c.e. theory of single-bit constraints; the appendix's computability argument shows every universal continuous semimeasure gives the stagewise class of consistent strings vanishing total mass; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `strict_domination_of_null_separator_class`, `lic_strict_domination_universalSemimeasure`, `lic_strict_domination_universalSemimeasure_ofAtomCodes` | Every field of the interface is now built, not assumed: Kleene's pair is recursively inseparable (`kleene_recursively_inseparable`), the constraint theory's enumerator is built from the atom codes (`separatorConstraintCE`), and the stage classes are null by the Kučera–Demuth argument (`separatorClass_mass_tendsto_zero`: the class masses are antitone, and a positive floor would let the semimeasure's own bounded-fuel approximants compute a separator by majority vote). The single remaining input of `strictSeparatorPresentationOfKleene` is computability of the atom family's Gödel codes, proved for the repo's concrete atoms (`ordinaryAtom_code_computable`). The earlier *nested prefix family* shape of this interface is provably uninhabitable — see `no_ce_null_prefix_family`. |
| `M7-SCON-COMPILER` | Interfaces `EventualConditioningFloor` and `EventualConditioningOperationalWitness` in `Properties/Conditioning.lean`; exact rational conditional-market programs, finite-zero price-leaf rewriting, arbitrary-stream price/frame transducers, and direct consumers in `Construction/Witnesses/ConditioningCompiler.lean` | `thm:scon` / App. `scon`. Uniform Non-Dogmatism plus Preemptive Learning produce an eventual floor; exact rational prefix prices reduce the exceptions to the zero-denominator days, where the capped quote is the constant `1`. The parser-transparent compiler rewrites those leaves, counts trades, emits both locally gated legs, and starts after the finite cutoff; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | `lic_conditioned_eventual_ofMarketComputation`, `lic_conditioned_fixed_ofComputationAndMarket`, `lic_conditioned_growing_ofComputationsAndMarket`, and the two paper-facing constructed-LIA corollaries | Constructed from a named rational base-market computation, polynomial condition codes, and joint consistency. Economic loss, failed-condition behavior, finite-prefix exploit preservation, wealth floors, exploit transport, and LI closure are proved outside the operational certificate. The repaired path stays on the original market and does not invoke unrestricted finite-perturbation closure. |
| `M7-SCON-PRESENTATION` | Interface `ConditioningPresentation` in `Properties/Conditioning.lean`; concrete `deductiveStageCondition`, fixed-sentence and growing-stage presentations, `DeductiveProcessComputation.union`, and their computation constructors in `Construction/Witnesses/ConditioningPresentation.lean` | `thm:scon` / App. `scon`. The growing condition is the canonical finite conjunction of the extra stage, with exact Boolean semantics including the empty stage; the fixed form uses the constant one-sentence process. A primitive-recursive code-sorted union normalizer composes stage programs; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | The fixed and growing `M7-SCON-COMPILER` endpoints | Constructed from an ordinary base-process computation and, for the growing form, one compact operational program emitting the actual extra-stage conjunction code with polynomial fuel. It assumes no condition semantics, combined-process computation, conditional prices, trader, wealth, exploitation, or LI conclusion. |
| `M7-LUV-SYNTAX` | Boundary interfaces `LUV.PolyThresholdCodes`/`PolyThresholdCodeSeq` in `Framework/Expectations.lean` and `LUVCombination.PolySequence`, `WorldValued`, `ConvergencePresentation`, `ExactTheoryPresentation`, `MeshSoftmaxOperationalWitness` in `Properties/ExpectationProperties.lean`; concrete compact thresholds, semantic presentations, cross-precision meshes, and `LUVCombinationSyntax.meshSoftmaxOperationalWitness` in `Construction/Witnesses/LUVSyntax.lean` | `def:luv`, `thm:expprovind`, `thm:expcoh`, `thm:perexpkno`, `thm:exppolymax`, `thm:recurringunbiasednessexp`, `thm:wubexp`, `thm:prandexp` and their appendices. First-order threshold formulas plus the paper's finite soft-max mesh realize the packages; see [Garrabrant et al.](https://arxiv.org/abs/1609.03543). | The expectation-property tail, especially `BoundedSequence.exppolymax`, `.perexpkno`, `.expcoh`, `.recurringunbiasednessexp`, `.wubexp`, and `.prandexp` | Constructed from `LUVCombinationSyntax` plus its conclusion-free stage/completed-theory representation laws: compact threshold codes, exact semantic presentations, and polynomial/bounded/magnitude certificates for the concrete soft-max meshes. It assumes no expectation limit, persistence, unbiasedness, pseudorandom-learning, or preemptive-learning conclusion. |

### Boundary inventory

| # | Boundary | Endpoint status | Evidence / disclosure |
|---:|---|---|---|
| 1 | `M7-HIST-EVALN` | **constructed** | `codeEvalnNat_polyFueled`, `boundedEvalnCompiler` (`Construction/Witnesses/M7Witnesses.lean`) |
| 2 | `M7-CE-REPETITION` | **constructed** | `EfficientRepeatedEnumeration.ofCE` (`Construction/Witnesses/M7Witnesses.lean`) |
| 3 | `M7-PATIENT-CLOCK` | **constructed** | `SettlementChecker.ofComputations`, `PatientSettlementClock.ofComputations` (`Construction/Witnesses/M7Witnesses.lean`) |
| 4 | `M7-PREFIX-PATCH` | **partial — token model only** | `liaFreezeBefore_preserves_ecTok` (`Construction/Witnesses/M7Witnesses.lean`) compiles the LIA's finite prefix quote table into a token-metered freeze. The symbol-metered `EfficientPrefixPatch.preserves_ec` has **no LIA inhabitant**: the run-level transducer and quote lookup are constructed (`Construction/Witnesses/RpnFreeze.lean`), but its fuel certificate needs a `BigDigits` decode test on exponentially large escape codes, which the `dd:fuel` digit model cannot express. The obstruction is structural, not effort: `BigDigits` is closed under an operation exactly when its base-4 digit recurrence has a poly-bounded carry, and `evaln`'s fuel guard forbids big intermediates outright — so the forward operations (`add`, `mul`, `natPair`, `ltNat`) close and their inverses (`sqrt`, `unpair`) do not. Disclosed in `notes/next-session.md` (INTERIM SEAMS item 2, "Route (A) — ATTEMPTED"); `thm:ifp` remains conditional on the patch structure. |
| 5 | `M7-QUOTE-AFFINE` | **constructed** | Arithmetic quotation/diagonal codes, a market-derived public fixed point for paradox resistance, concrete same-day/deferred packages, and eight direct consumers (`Construction/Witnesses/QuotationAffine.lean`) |
| 6 | `M7-PREFIX-MACHINE` | **constructed** (fixed code and universal machine) | `prefixMachinePresentation`, `lic_occam_lower_ofPrefixMachine`, `lic_occamBounds_ofPrefixMachine` (`Construction/Witnesses/PrefixMachine.lean`); `UPrefix.universalPrefixPresentation`, `UPrefix.lic_occam_lower_ofUniversalPrefix`, `UPrefix.lic_occamBounds_ofUniversalPrefix` (`Construction/Witnesses/UniversalPrefix.lean`) |
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
what is concrete today. All fifteen boundaries are constructed (the one partial row,
`M7-PREFIX-PATCH`, is constructed at the token model with the symbol-level residual
disclosed above; the universal prefix machine's exact stage-table code is
constructed as `UPrefix.uCode` / `exists_uCode`).  The universal prefix
machine with its Kraft proof, the universal lower semicomputable continuous semimeasure,
and the recursively-inseparable-set mass theorem are all now constructed
(`Construction/Witnesses/UniversalPrefix.lean`, `UniversalDovetailer.lean`,
`StrictSeparators.lean`, `KraftInequality.lean`). The present endpoint does
not claim that stronger scope.
