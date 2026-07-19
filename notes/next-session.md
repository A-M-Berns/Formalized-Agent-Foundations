# Logical Induction — current construction handoff

_Last updated: 2026-07-18. Branch: `logical-induction`._

This is the authoritative execution handoff. The M7 table in `README.md` is the public
inventory of what is concrete today; this file records the stronger active construction
target and what to build next. Historical plans remain available in Git history. There is
intentionally no `PROGRESS.md`.

## Active target

Construct twelve of the fifteen M7 witness boundaries. The earlier
“four constructed, eleven disclosed” endpoint was achieved, but it is a baseline rather
than a stop instruction.

| # | Boundary | Current state | Active disposition / evidence |
|---:|---|---|---|
| 1 | `M7-HIST-EVALN` | **constructed** | Keep; `codeEvalnNat_polyFueled`, `boundedEvalnCompiler` |
| 2 | `M7-CE-REPETITION` | **constructed** | Keep; `EfficientRepeatedEnumeration.ofCE` |
| 3 | `M7-PATIENT-CLOCK` | **constructed** | Keep; `SettlementChecker.ofComputations`, `PatientSettlementClock.ofComputations` |
| 4 | `M7-PREFIX-PATCH` | **constructed** | Keep; `liaEfficientPrefixPatch` |
| 5 | `M7-QUOTE-AFFINE` | **constructed** | Keep; `QuotationAffine.lean` arithmetic codes, affine constructors, and eight direct consumers |
| 6 | `M7-PREFIX-MACHINE` | disclosed | **keep disclosed**; optional post-target Kraft/prefix-machine stretch |
| 7 | `M7-FEEDBACK-EMIT` | **constructed** | Keep; `FeedbackEmission.feedbackTraderEmissionSigns` |
| 8 | `M7-FEEDBACK-TRUTH` | **constructed** | Keep; `FeedbackTruth.feedbackTruthSequence` and three computation-based consumers |
| 9 | `M7-DUS-PREFIX-SYNTAX` | **constructed** | Keep; `bitPrefixSentencesOfIndependentAtoms`, `lic_domination_universalSemimeasure_ofIndependentAtoms` |
| 10 | `M7-SCON-COMPILER` | disclosed | **construct**, attempt 6 |
| 11 | `M7-SCON-PRESENTATION` | **constructed** | Keep; `conditioningPresentationOfComputations`, `lic_conditioned_gated_ofComputations` |
| 12 | `M7-LUV-SYNTAX` | disclosed | **construct**, attempt 7 |
| 13 | `M7-DUS-APPROX` | disclosed | Leave disclosed unless Anson reopens it |
| 14 | `M7-STRICT-SEPARATORS` | disclosed | Leave disclosed unless Anson reopens it |
| 15 | `M7-COMP-SYNTAX` | **constructed** | Keep; `ComputationClaim`, three boundary constructors, and six direct consumers in `Construction/ComputationSyntax.lean` |

Current count: **10/15 constructed**. Target count: **12/15 constructed**. The two remaining
constructions are `M7-SCON-COMPILER` and `M7-LUV-SYNTAX`.
`M7-PREFIX-MACHINE`, `M7-DUS-APPROX`, and `M7-STRICT-SEPARATORS` are the three intentional
disclosures at the target.

Do not revive instructions to stop after feedback emission, treat all former Tier 2
witnesses as permanently disclosed, or begin final closeout/audit work before this active
construction slate is complete.

## Verified state at this handoff

- The main existence result remains unconditional and axiom-clean.
- The M3–M5 property tail remains green under `[IsLogicalInductor P DP]`.
- `M7-FEEDBACK-EMIT` is complete in
  `LogicalInduction/Construction/FeedbackEmission.lean` and imported from
  `LogicalInduction/Construction.lean`.
- `M7-SCON-PRESENTATION` is complete in
  `LogicalInduction/Construction/ConditioningPresentation.lean` and imported from
  `LogicalInduction/Construction.lean`.
- Its public constructor is `conditioningPresentationOfComputations`; the useful closure
  entry point with the presentation discharged is `lic_conditioned_gated_ofComputations`.
- `M7-DUS-PREFIX-SYNTAX` is complete in
  `LogicalInduction/Construction/BitPrefixSyntax.lean` and imported from
  `LogicalInduction/Construction.lean`.
- Its public constructor is `bitPrefixSentencesOfIndependentAtoms`; the direct DUS entry
  point with `BitPrefixSentences` discharged is
  `lic_domination_universalSemimeasure_ofIndependentAtoms`.
- `IndependentBitAtoms` is the genuine semantic premise: an atom sequence and finite
  stagewise compatibility only. `bitPrefixSentence` is the literal `List.conj`, including
  the empty `⊤` prefix, and `bitStringEnumeration` is stock `List Bool` decode-with-empty.
  `BitPrefixCodeComputation` isolates one honest polynomial program for the actual
  conjunction code; no primitive-recursive-to-polynomial shortcut was introduced.
- `ordinaryIndependentBitAtoms` and `independentBitAtoms_nonempty` witness the semantic
  premise over the constantly empty deductive process with ordinary propositional atoms.
- `M7-COMP-SYNTAX` is complete in
  `LogicalInduction/Construction/ComputationSyntax.lean` and imported from
  `LogicalInduction/Construction.lean`.
- FFL supplies the actual quoted arithmetic schemas: `UniversalCodeHalts` is r.e.,
  `UniversalCodeHaltsWithin` is computable, and `codeOfREPred_spec`/`re_complete` prove the
  standard-model and theory representation laws. `ComputationClaim.godelCode` injectively
  names a role, an FFL arithmetic schema, and a compact input inside a propositional atom.
- `ComputationTheoryPresentation` is the exact residual seam: a `Δ₁` arithmetic theory, a
  computable deductive process, and pointwise translation of proofs of the fixed schemas into
  positive or negative market literals. FFL only supplies weak positive r.e. representation;
  bounded false claims therefore use a separate complementary r.e. failure schema rather than
  pretending the original r.e. formula is strongly refutable.
- `representedSemidecidableClaimsOfComputation`,
  `representedDecidableClaimsOfComputation`, and
  `inconsistentTheoryClaimsOfComputation` discharge all three old boundaries. The six
  `..._ofComputation` consumers discharge them at `pac`, `pazfc`, `incons`, `halts`, `loops`,
  and `dontwait`; `loops` now takes an arithmetic proof of the negated halting instance, not a
  preassembled eventual-membership family.
- `M7-QUOTE-AFFINE` is complete in
  `LogicalInduction/Construction/QuotationAffine.lean` and imported from
  `LogicalInduction/Construction.lean`.
- It supplies dual FFL Boolean/rational quotation codes, compact injective public names,
  genuine FFL `parameterizedFixedpoint` diagonalization, exact same-day Boolean/numeric
  affine meshes, completed-theory coherence, and all four concrete deferred packages.
- The direct endpoints are `lic_introspection_ofCode`,
  `lic_paradox_resistance_ofDiagonal`, `lic_expectations_of_probabilities_ofCode`,
  `lic_iterated_expectations_ofCode`, and the four deferred `..._ofRepresentation`
  consumers for `cee`, `ceu`, `ccee`, and `st`.
- `M7-FEEDBACK-TRUTH` is complete in
  `LogicalInduction/Construction/FeedbackTruth.lean` and imported from
  `LogicalInduction/Construction.lean`.
- `FeedbackTruthComputation` is the paper-faithful residual input: one rational value
  program on feedback index `k`, a canonical-code result by the explicit
  `ecClock a degree (f (k+1))` deadline, and equality with the semantic truth stream at
  `f k`. It contains no market prices, delayed accuracy, bias, convergence, or LI result.
- The compiler recognizes only positive deferral-image indices, recovers `f k` through the
  bounded scheduled evaluator, and emits the literal centered affine member on day
  `f(k+1)` and literal zero elsewhere. `feedbackTruthSequence` proves polynomial syntax,
  uniform bounded prices, unit magnitude, completed-world value zero, and the exact delayed
  price identity from separate ordinary normalization/market inputs.
- The public endpoints `lic_wubaff_ofComputation`,
  `boundedCombination_wubaff_ofComputation`, and `luv_wubexp_ofComputation` discharge both
  feedback boundaries. They take the explicit truth computation rather than an opaque
  preassembled `FeedbackTruthSequence`; delayed accuracy remains derived by affine
  provability induction.
- The Foundation audit found the required fixed-point theorem in
  `Foundation/FirstOrder/Bootstrapping/FixedPoint.lean`; no public propositional adapter
  existed, so `QuotationTheoryPresentation` remains the explicit proof-to-market seam.
- A paper-level ambiguity was repaired locally: image reindexing is not well-defined for an
  arbitrary noninjective deferral. Only the four concrete deferred constructors require
  `StrictlyIncreasingDeferral`; the abstract quote structures and consumers still accept
  every `DeferralFunction`. Cross-mesh comparison also requires explicit completed-world
  `ValuesAt` premises rather than pretending compact syntax determines semantics.
- `deductiveStageCondition` is the actual `Finset.conj`; Foundation Boolean semantics prove
  the exact stage equivalence, including the empty conjunction. `DeductiveProcessComputation.union`
  pairs the two stage programs and applies a primitive-recursive code-sorted union normalizer.
- Polynomial naming is honestly isolated in `CompactConditioningProcessComputation`: one
  program must emit the actual extra-stage conjunction code with `PolyFueled`. Ordinary
  `ComputableDeductiveProcess` was not silently upgraded to a polynomial oracle. The
  interface has an `N+` inhabitance witness using the constantly empty process.
- The feedback-emission public constructor is
  `LogicalInduction.FeedbackEmission.feedbackTraderEmissionSigns`.
- Derived consumers with the emission boundary discharged are
  `lic_wubaff_ofFeedbackTruth`, `boundedCombination_wubaff_ofFeedbackTruth`, and
  `luv_wubexp_ofFeedbackTruth`.
- The focused construction/property/integration roll-up built **2,573 jobs**; the full
  project built **2,686 jobs**.
- The quotation reports, computation-syntax reports, six public prefix-syntax axiom reports,
  five public conditioning-presentation reports, four public feedback-emission reports, and
  four public feedback-truth reports
  contain only `propext`, `Classical.choice`, and `Quot.sound` (some prefix reports need a
  strict subset).
- The last verified tree was green and contained no executable proof holes.

Relevant commits, newest first:

- `261bdf7` — construct the bounded delayed feedback truth compiler and direct consumers
- `f1c1355` — construct FFL-backed computation syntax and all six direct MetaLearning consumers
- `4546178` — construct independent Boolean-prefix syntax and the direct DUS entry point
- `0d6ae13` — construct the conditioning presentation witness
- `d51d456` — rewrite this file as the authoritative current handoff
- `3eb3d93` — scope the delayed feedback truth compiler
- `caf5562` — construct feedback trader emission
- `2cb2a03` — flatten scheduled feedback trades
- `d95db6a` — emit scheduled feedback features
- `e069871` — decode scheduled feedback values
- `e3cb97f` — compile the bounded feedback schedule
- `5b1de90` — expose feedback trader syntax
- `d780996` — redirect active progress references to this handoff
- `78f0860` — remove the stale progress ledger
- `4fb0939` — restore the expanded witness construction scope

## Attempt order for the remaining constructions

This order is deliberate: take the two narrowest old Tier 2 presentations first, then build
the faithfulness-critical first-order representation and quotation spine, then return to the
three broader operational compilers.

| Attempt | Boundary | Why here |
|---:|---|---|
| 1 | `M7-SCON-PRESENTATION` | **Complete**; finite conjunction, exact semantics, and union computation landed |
| 2 | `M7-DUS-PREFIX-SYNTAX` | **Complete**; Boolean-prefix syntax, enumeration, semantics, and finite realizability landed |
| 3 | `M7-COMP-SYNTAX` | **Complete**; FFL arithmetic schemas, compact Gödel names, representation constructors, and direct consumers landed |
| 4 | `M7-QUOTE-AFFINE` | **Complete**; FFL quotation/diagonalization and concrete same-day/deferred affine packages landed |
| 5 | `M7-FEEDBACK-TRUTH` | **Complete**; bounded delayed truth compiler and direct consumers landed |
| 6 | `M7-SCON-COMPILER` | **Next**; market-dependent denominator patch plus arbitrary token-stream translation |
| 7 | `M7-LUV-SYNTAX` | Broadest Tier 2 package: thresholds, exact-theory semantics, meshes, and softmax emission |

“Attempt” is intentional. Before implementing each witness, audit whether its current
interface can be inhabited at the stated generality. If it needs a paper-faithful
computability, language, or independence premise, repair the interface and record the
dependency; do not manufacture a circular or oracle-like constructor merely to preserve the
order. A minimal LUV threshold-code sublayer needed by quotation may be pulled into attempts
3–4, while the full `M7-LUV-SYNTAX` package remains attempt 7.

## Completed attempt 1 — `M7-SCON-PRESENTATION`

`LogicalInduction/Construction/ConditioningPresentation.lean` closes the former
`ConditioningPresentation` boundary:

- `deductiveStageCondition` is the canonical `Finset.conj`; the theorem
  `PCWorld.holds_deductiveStageCondition` proves exact finite-stage semantics and covers the
  empty-stage `⊤` case.
- `sentenceFinsetUnionNorm` reuses the LIA compiler's canonical sentence sorting and duplicate
  removal. `DeductiveProcessComputation.union` explicitly composes that normalizer with the
  two certified stage programs.
- `CompactConditioningProcessComputation` is the strengthened operational input forced by the
  audit: it retains an ordinary stage computation and requires one `PolyFueled` program for
  the code of the actual stage conjunction. This is provenance `(a)` for the semantic and
  union fields and an explicit operational premise for polynomial naming, not a semantic or
  market conclusion. `compactConditioningProcessComputation_nonempty` proves the interface is
  inhabited.
- `conditioningPresentationOfComputations` constructs the boundary object, and
  `lic_conditioned_gated_ofComputations` removes the presentation argument from the useful
  gated closure entry point. Neither constructor assumes prices, trades, wealth, exploitation,
  or a logical-inductor conclusion.

## Completed attempt 2 — `M7-DUS-PREFIX-SYNTAX`

`LogicalInduction/Construction/BitPrefixSyntax.lean` closes the former
`BitPrefixSentences` boundary:

- `IndependentBitAtoms` contains only an atom sequence and finite compatibility with every
  deductive stage. It has no preassembled prefix syntax or semantic law.
- `bitPrefixSentence` is the finite `List.conj` of the selected positive/negative literals.
  `PCWorld.holds_bitPrefixSentence` proves the exact bit semantics, including `[] ↦ ⊤`.
- `bitStringEnumeration` is the total stock `List Bool` decode-with-empty enumeration;
  `bitStringEnumeration_covers` proves literal coverage with `Encodable.encodek`.
- `BitPrefixCodeComputation` is the only operational premise and names the actual conjunction
  code with `PolyFueled`. `bitPrefixSentencesOfIndependentAtoms` builds the old boundary, and
  `lic_domination_universalSemimeasure_ofIndependentAtoms` removes it from the paper-facing
  theorem while leaving `M7-DUS-APPROX` untouched.
- The semantic premise is inhabited by the constantly empty process and ordinary atoms.
  None of the new inputs assumes prices, trader payoff, domination, or an asymptotic market
  conclusion.

## Completed attempt 3 — `M7-COMP-SYNTAX`

`LogicalInduction/Construction/ComputationSyntax.lean` closes all three representation
boundaries in `Properties/MetaLearning.lean`:

- `UniversalCodeHalts` and `UniversalCodeHaltsWithin` are tied directly to
  `Nat.Partrec.Code.eval`/`evaln`; the former is proved r.e. and the latter computable.
- FFL's `codeOfREPred` supplies real arithmetic schemas, with explicit standard-model
  specifications. The bounded-failure schema is proved complementary to bounded halting.
- `ComputationClaim` stores its role, arithmetic schema, and compact input. Its nested-pair
  Gödel code and the resulting propositional atom are injective.
- `PolyMachineCodes`, `PolyNatCodes`, and the `PolyFueled` pair/atom compiler prove whole
  `PolySentenceCodes` for every emitted family without running the named machine.
- `ComputationTheoryPresentation` records a `Δ₁` theory, a concrete `DP` computation, and
  only pointwise proof translations for the fixed schemas. It assumes no sentence family,
  market datum, or consumer conclusion.
- The three boundary constructors and two sequence-specialized constructors feed six direct
  MetaLearning consumers. Concrete Code.zero/zero-fuel theorems exercise the positive and
  complementary negative paths.

## Completed attempt 4 — `M7-QUOTE-AFFINE`

`LogicalInduction/Construction/QuotationAffine.lean` closes both the same-day and deferred
quotation boundaries:

- `ArithmeticDecision`, `BooleanQuoteCode`, and `RationalQuoteCode` use FFL weak
  representation for a predicate and its complement, with one injective polynomial public
  name. `QuotationTheoryPresentation` is the honest residual bridge from arithmetic proofs
  to membership of the corresponding positive or negated market literal.
- `ParameterizedDiagonalQuoteCode` uses FFL's actual `parameterizedFixedpoint` theorem.
  `introspectionIntervalQuoteOfCode` and `paradoxResistanceQuoteOfDiagonal` build literal
  gate portfolios, while the two numeric constructors build the current-price/current-
  expectation mesh portfolios.
- `CompletedAffineQuoteApprox`, image flags, bounded preimages, and cross-precision meshes
  discharge completed-theory and deferred repricing obligations. The `cee`, `ceu`, `ccee`,
  and `st` constructors are concrete fixed affine portfolios; self-trust proves the required
  one-sided correction rather than smuggling in its conclusion.
- The paper's informal image assignment is ambiguous for noninjective deferrals. The repair
  is deliberately local: only the four concrete deferred constructors take
  `StrictlyIncreasingDeferral`; `AffineQuoteEq`, `AffineQuoteGE`, and all consumer theorems
  retain their original arbitrary-`DeferralFunction` interfaces.
- Compact LUV syntax does not determine completed-world values. Cross-precision constructors
  therefore expose the necessary `ValuesAt` facts explicitly. This is a representation
  premise, not a price or convergence premise.
- Eight direct paper-facing consumers discharge the constructed packages. Their axiom
  reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Completed attempt 5 — `M7-FEEDBACK-TRUTH`

`LogicalInduction/Construction/FeedbackTruth.lean` closes the former
`FeedbackTruthSequence` boundary:

- `DeterminedViaTheory As P DP truth` remains semantic and is never used as a computation
  oracle. `FeedbackTruthComputation` supplies rational values at the required `f k` indices,
  their semantic equality, one uniform program, and halting within
  `ecClock a degree (f (k + 1))`.
- The compiler reuses `codeEvalnNat_polyFueled`, `scheduledMatch`, and `scheduledDeferral`
  to recognize the unique scheduled `k` without computing an unbounded inverse of `f`.
- It emits literal centered syntax `A (f k) - truthRat (f k)`, else zero, with polynomial
  term, coefficient, sentence, and constant serialization.
- It proves `PolySequence`, bounded prices, magnitude, completed-world value zero, and the
  exact delayed `feedback_price` identity. Normalization data stays outside the computation
  certificate.
- The three public `..._ofComputation` entry points take the computation premise instead of
  an opaque preassembled `FeedbackTruthSequence`. Accuracy remains derived, never assumed.

Provenance: `FeedbackTruthComputation.value/code/computes/agrees` are the explicit paper
operational premise, not a derived market conclusion. The deferral schedule, raw
rational-code emission, affine syntax, semantic zero-value law, bounds, and consumers are
proved composition (`C`) from those inputs and existing project compilers. The only type-(c)
modeling substitution remains the repository-wide disclosed `dd:fuel` clock model.

## START HERE — attempt 6, `M7-SCON-COMPILER`

Construct `GatedConditioningOperationalWitness` in
`LogicalInduction/Properties/Conditioning.lean`. Keep the boundary split already enforced by
the property file: `ConditioningPresentation` supplies the real stage conjunction and union
process, while the new operational constructor must supply only a positive rational
denominator floor, computation of the actual conditional market, and token-level efficient
translation of every `EfficientlyComputableTok` trader through
`Trader.conditionedTranslation`.

Audit the interface at the intended generality before coding. The denominator patch is
market-dependent, so expose whatever concrete base-market computation and finite-prefix
minimum program are genuinely required; do not infer computability from the semantic
`History`. The translated trader has an arbitrary polynomial-length token stream, so compile
the literal gated conditional contract stream rather than assuming a fixed extensional
length. Economic tracking, first-failure downside control, exploitation transport, and the
LI conclusion are already proved in `Conditioning.lean` and must not enter the operational
certificate.

## Deliberately disclosed boundaries

- `M7-PREFIX-MACHINE` stays disclosed because it mainly supplies standard universal
  self-delimiting-machine, from-below weight, finite Kraft, and fixed negation-overhead facts
  for Occam Bounds. The paper-specific market proof is already formalized. Keep it as an
  optional post-target showcase; if reopened, the finite Kraft core is a good Aristotle job.
- `M7-DUS-APPROX` and `M7-STRICT-SEPARATORS` remain disclosed unless Anson separately reopens
  them.

Only after the **12/15** construction target is green should the work move to surface freeze,
human statement read-through, consolidation/API/style work, paper comparison, and the
fresh-context errata audit.

## Verification and commit discipline

Commit coherent green layers as construction proceeds. Before each commit, use the smallest
relevant build; before closing a witness, run at least:

```sh
lake build LogicalInduction.Construction LogicalInduction.Properties LogicalInduction.IntegrationTest
lake build
rg -n '(^|[[:space:]])(sorry|admit)([[:space:]]|$)' LogicalInduction --glob '*.lean'
git diff --check
git status --short
```

Also print the axioms of every new public constructor and consumer. Expected reports contain
only `propext`, `Classical.choice`, and `Quot.sound`; investigate any additional axiom.

Record a short durable update in this file whenever a completed tranche changes the count,
the exact next goal, its boundary design, or its verification state. Keep historical detail
in Git rather than appending superseded plans below the active handoff.

## Aristotle

Aristotle is available through `scripts/aristotle-prove.sh`. Use it only after a proof goal is
fully stated and self-contained; it is not a substitute for construction or interface
design. A likely high-value use is the long Mathlib-only finite Kraft inequality core after
the prefix-machine definitions are fixed.

Requirements and trust rule:

- `ARISTOTLE_API_KEY` must be available to the process.
- Prefer small extracted Mathlib-only projects, not the entire repository.
- Toolchain versions may differ.
- A returned proof is trusted only after it compiles in this repository.

## Reusable construction notes

- Search before proving. Useful existing anchors include `codeEvalnNat_polyFueled`,
  `deadlineRun`, `scheduledMatch`, `segPrefix_polyFueled`, `segLocate_polyFueled`,
  `PolySegStream.concatVar`, `PolySequence.priceFeature_polySeg`, and
  `PGenerableWeighting.polySeg`.
- Deep `PolyFueled` proofs involving nested `Nat.unpair` may trigger `Nat.sqrt` weak-head
  normalization blowups. Prefer a narrow local `attribute [irreducible] Nat.sqrt` over
  raising heartbeat limits.
- Preserve literal token/list equalities at representation boundaries. Semantic equality
  alone is not enough for the witness constructors.
- Keep computation certificates conclusion-free. Economic and asymptotic conclusions
  belong in the already-proved consumer layer.
