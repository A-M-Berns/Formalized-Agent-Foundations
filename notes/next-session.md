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
| 5 | `M7-QUOTE-AFFINE` | disclosed | **construct**, attempt 4 after `M7-COMP-SYNTAX` |
| 6 | `M7-PREFIX-MACHINE` | disclosed | **keep disclosed**; optional post-target Kraft/prefix-machine stretch |
| 7 | `M7-FEEDBACK-EMIT` | **constructed** | Keep; `FeedbackEmission.feedbackTraderEmissionSigns` |
| 8 | `M7-FEEDBACK-TRUTH` | disclosed | **construct**, attempt 5 |
| 9 | `M7-DUS-PREFIX-SYNTAX` | **constructed** | Keep; `bitPrefixSentencesOfIndependentAtoms`, `lic_domination_universalSemimeasure_ofIndependentAtoms` |
| 10 | `M7-SCON-COMPILER` | disclosed | **construct**, attempt 6 |
| 11 | `M7-SCON-PRESENTATION` | **constructed** | Keep; `conditioningPresentationOfComputations`, `lic_conditioned_gated_ofComputations` |
| 12 | `M7-LUV-SYNTAX` | disclosed | **construct**, attempt 7 |
| 13 | `M7-DUS-APPROX` | disclosed | Leave disclosed unless Anson reopens it |
| 14 | `M7-STRICT-SEPARATORS` | disclosed | Leave disclosed unless Anson reopens it |
| 15 | `M7-COMP-SYNTAX` | disclosed | **construct next**, attempt 3 and prerequisite of `M7-QUOTE-AFFINE` |

Current count: **7/15 constructed**. Target count: **12/15 constructed**. The five remaining
constructions are `M7-COMP-SYNTAX`, `M7-QUOTE-AFFINE`, `M7-FEEDBACK-TRUTH`,
`M7-SCON-COMPILER`, and `M7-LUV-SYNTAX`.
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
- The focused construction/property/integration roll-up built **2,472 jobs**; the full
  project built **2,683 jobs**.
- The six public prefix-syntax axiom reports, five public conditioning-presentation
  reports, and four public feedback-emission reports contain only `propext`,
  `Classical.choice`, and `Quot.sound` (some prefix reports need a strict subset).
- The last verified tree was green and contained no executable proof holes.

Relevant commits, newest first:

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

## Attempt order for the five remaining constructions

This order is deliberate: take the two narrowest old Tier 2 presentations first, then build
the faithfulness-critical first-order representation and quotation spine, then return to the
three broader operational compilers.

| Attempt | Boundary | Why here |
|---:|---|---|
| 1 | `M7-SCON-PRESENTATION` | **Complete**; finite conjunction, exact semantics, and union computation landed |
| 2 | `M7-DUS-PREFIX-SYNTAX` | **Complete**; Boolean-prefix syntax, enumeration, semantics, and finite realizability landed |
| 3 | `M7-COMP-SYNTAX` | **Next**; faithfulness root: concrete representation of computations and Gödel syntax |
| 4 | `M7-QUOTE-AFFINE` | Directly consumes attempt 3; closes introspection/self-trust quotation |
| 5 | `M7-FEEDBACK-TRUTH` | Bounded delayed truth compiler; already scoped but has a real boundary correction |
| 6 | `M7-SCON-COMPILER` | Market-dependent denominator patch plus arbitrary token-stream translation |
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

## START HERE — attempt 3, `M7-COMP-SYNTAX`

Construct the computation-representation root currently exposed by
`RepresentedSemidecidableClaims`, `RepresentedDecidableClaims`, and
`InconsistentTheoryClaims` in `Properties/MetaLearning.lean`. Audit generality before
writing a constructor:

1. An arbitrary `DeductiveProcess` does not prove true machine claims. Isolate the actual
   paper premise tying `DP` to a recursively axiomatized background theory that represents
   the repository's `Nat.Partrec.Code` computations. Do not assume the three completed
   representation structures or any market conclusion wholesale.
2. Decide the language integration explicitly. The current public `Sentence` is
   `LO.Propositional.Formula ℕ`; atom labels may carry Gödel codes, but Boolean semantics alone
   cannot prove representability. A faithful constructor therefore needs concrete quoted
   first-order syntax plus a translation/naming layer into `Sentence`, or a narrow certified
   theory-enumeration premise whose fields are strictly below the existing consumer boundaries.
   Record any required repair rather than treating an atom label as a representability theorem.
3. Build uniform sentence constructors for unbounded halting/semidecidable claims, bounded
   `CodeHaltsWithin` claims and their negations, and the paired consistency/inconsistency
   claims. Prove the exact positive and negative eventual-membership laws from the background
   representation certificate.
4. Supply `PolySentenceCodes` honestly for every family. Compact syntax may name a fixed
   machine/horizon program without executing it, but the whole sentence-code program and its
   polynomial fuel/output bound must be explicit.
5. Expose public constructors discharging all three MetaLearning interfaces and direct entry
   points for the six consumers (`pac`, `pazfc`, `incons`, `halts`, `loops`, `dontwait`). Add
   non-vacuity witnesses that exercise both positive and negative representation paths; print
   axioms for every new public constructor/consumer.
6. Keep attempt 3 scoped to computation/Gödel representation. A minimal threshold-code layer
   may be factored now if quotation genuinely needs it, but do not begin the market-dependent
   `CompletedAffineQuoteEq` / `AffineQuoteEq` / `AffineQuoteGE` construction until this root is
   green.

Definition of done: computation claims and their Gödel names are concrete, polynomially named,
and enter/refute in `DP` for the right computational reasons. The residual premise describes a
background theory and its representation theorem, not preassembled claim families, market
prices, convergence, exploitation, or a logical-inductor conclusion.

## Attempt 4 — quotation and affine portfolios

`M7-COMP-SYNTAX` must precede `M7-QUOTE-AFFINE`. The current `Sentence` is propositional, so
this is a real integration campaign rather than a wrapper around the existing boundary
structures.

- `M7-COMP-SYNTAX` must supply the first-order representability/Gödel machinery behind
  `RepresentedSemidecidableClaims`, `RepresentedDecidableClaims`, and
  `InconsistentTheoryClaims`, with polynomial sentence naming and eventual proof/refutation
  laws for the represented computations.
- `M7-QUOTE-AFFINE` must construct both the same-day completed-theory quotation packages and
  the deferred fixed-portfolio `AffineQuoteEq`/`AffineQuoteGE` packages. It must cover the
  quotation, diagonal/fixed-point, exact current-price, completed-world, and deferred
  coherence obligations used by introspection and self-trust.
- Do not describe quotation as mere wiring, silently leave its computation-representation
  root disclosed, or assume the consumer conclusions in the quotation certificate.

These two witnesses take priority over the later operational compilers because they test the
largest remaining paper-faithfulness claim.

## Attempt 5 brief — `M7-FEEDBACK-TRUTH`

Preserve this scoped design when the ordered campaign reaches it:

- `DeterminedViaTheory As P DP truth` is semantic and cannot make `truth : ℕ → ℝ`
  computable. Introduce a conclusion-free operational certificate (working name
  `FeedbackTruthComputation`) supplying rational values at the required `f k` indices, their
  semantic equality, one uniform program, and halting within
  `ecClock a degree (f (k + 1))`.
- Reuse `codeEvalnNat_polyFueled`, `scheduledMatch`, and `scheduledDeferral` to recognize the
  unique scheduled `k` without computing an unbounded inverse of `f`.
- Emit literal centered syntax `A (f k) - truthRat (f k)`, else zero, with polynomial term,
  coefficient, sentence, and constant serialization.
- Prove `PolySequence`, bounded prices, magnitude, completed-world value zero, and the exact
  delayed `feedback_price` identity. Keep normalization data outside the computation
  certificate.
- Add public `wubaff`/`wubexp` entry points taking the computation premise instead of an
  opaque preassembled `FeedbackTruthSequence`. Accuracy remains derived, never assumed.

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
