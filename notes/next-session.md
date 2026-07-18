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
| 9 | `M7-DUS-PREFIX-SYNTAX` | disclosed | **construct**, attempt 2 |
| 10 | `M7-SCON-COMPILER` | disclosed | **construct**, attempt 6 |
| 11 | `M7-SCON-PRESENTATION` | disclosed | **construct next**, attempt 1 |
| 12 | `M7-LUV-SYNTAX` | disclosed | **construct**, attempt 7 |
| 13 | `M7-DUS-APPROX` | disclosed | Leave disclosed unless Anson reopens it |
| 14 | `M7-STRICT-SEPARATORS` | disclosed | Leave disclosed unless Anson reopens it |
| 15 | `M7-COMP-SYNTAX` | disclosed | **construct**, attempt 3 and prerequisite of `M7-QUOTE-AFFINE` |

Current count: **5/15 constructed**. Target count: **12/15 constructed**. The seven remaining
constructions are `M7-SCON-PRESENTATION`, `M7-DUS-PREFIX-SYNTAX`, `M7-COMP-SYNTAX`,
`M7-QUOTE-AFFINE`, `M7-FEEDBACK-TRUTH`, `M7-SCON-COMPILER`, and `M7-LUV-SYNTAX`.
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
- Its public constructor is
  `LogicalInduction.FeedbackEmission.feedbackTraderEmissionSigns`.
- Derived consumers with the emission boundary discharged are
  `lic_wubaff_ofFeedbackTruth`, `boundedCombination_wubaff_ofFeedbackTruth`, and
  `luv_wubexp_ofFeedbackTruth`.
- The focused construction/property/integration roll-up built **2,470 jobs**; the full
  project built **2,681 jobs**.
- The four public feedback-emission axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The last verified tree was green and contained no executable proof holes.

Relevant commits, newest first:

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

## Attempt order for the seven remaining constructions

This order is deliberate: take the two narrowest old Tier 2 presentations first, then build
the faithfulness-critical first-order representation and quotation spine, then return to the
three broader operational compilers.

| Attempt | Boundary | Why here |
|---:|---|---|
| 1 | `M7-SCON-PRESENTATION` | Smallest finite-conjunction/union presentation; also prepares `M7-SCON-COMPILER` |
| 2 | `M7-DUS-PREFIX-SYNTAX` | Self-contained Boolean-prefix syntax and finite realizability |
| 3 | `M7-COMP-SYNTAX` | Faithfulness root: concrete representation of computations and Gödel syntax |
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

## START HERE — attempt 1, `M7-SCON-PRESENTATION`

Construct the `ConditioningPresentation DP extra` used by `thm:scon`:

1. Define the finite conjunction sentence for `extra.D n`, using a canonical ordering and
   existing propositional conjunction semantics.
2. Prove `v.Holds (condition n) ↔ v.ConsistentWith (extra.D n)`, including the empty-stage
   case.
3. Supply `PolySentenceCodes condition` from an honest compact compiler. Audit this before
   coding: bare `ComputableDeductiveProcess extra` has no polynomial runtime or output-size
   promise, so a direct enumeration of `extra.D n` may be too weak for the current field.
   Strengthen the operational input or route through compact represented computation if that
   is what the paper requires; do not treat `extra.D` as a polynomial oracle.
4. Construct `ComputableDeductiveProcess (DP.union extra)` from explicit computations for
   the two inputs, reusing the existing finite-stage encoding machinery.
5. Expose a public constructor with no conditional price, trader, wealth, exploitation, or
   logical-inductor conclusion, then discharge the presentation argument in the most useful
   `lic_conditioned_gated` entry point.
6. Run focused/full builds, hole and diff checks, public axiom reports, and commit coherent
   green layers.

Definition of done: callers provide only the operational process data genuinely required by
the paper; the conjunction syntax, exact stage semantics, and union computation are concrete.
If compact polynomial conjunction naming genuinely depends on `M7-COMP-SYNTAX`, land every
independent green layer, record that dependency, and resume the remainder in attempt 3.

## Attempts 3–4 — the faithfulness-critical campaign

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
