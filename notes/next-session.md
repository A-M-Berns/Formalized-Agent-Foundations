# Logical Induction — current construction handoff

_Last updated: 2026-07-18. Branch: `logical-induction`._

This is the authoritative execution handoff. The M7 table in `README.md` is the public
inventory of what is concrete today; this file records the stronger active construction
target and what to build next. Historical plans remain available in Git history. There is
intentionally no `PROGRESS.md`.

## Active target

Construct thirteen of the fifteen M7 witness boundaries. The earlier
“four constructed, eleven disclosed” endpoint was achieved, but it is a baseline rather
than a stop instruction.

| # | Boundary | Current state | Active disposition / evidence |
|---:|---|---|---|
| 1 | `M7-HIST-EVALN` | **constructed** | Keep; `codeEvalnNat_polyFueled`, `boundedEvalnCompiler` |
| 2 | `M7-CE-REPETITION` | **constructed** | Keep; `EfficientRepeatedEnumeration.ofCE` |
| 3 | `M7-PATIENT-CLOCK` | **constructed** | Keep; `SettlementChecker.ofComputations`, `PatientSettlementClock.ofComputations` |
| 4 | `M7-PREFIX-PATCH` | **constructed** | Keep; `liaEfficientPrefixPatch` |
| 5 | `M7-QUOTE-AFFINE` | disclosed | **construct**, after `M7-COMP-SYNTAX` |
| 6 | `M7-PREFIX-MACHINE` | disclosed | **construct**, including the finite Kraft proof and fixed-overhead negation compiler |
| 7 | `M7-FEEDBACK-EMIT` | **constructed** | Keep; `FeedbackEmission.feedbackTraderEmissionSigns` |
| 8 | `M7-FEEDBACK-TRUTH` | disclosed | **construct next** |
| 9 | `M7-DUS-PREFIX-SYNTAX` | disclosed | **construct** (old Tier 2) |
| 10 | `M7-SCON-COMPILER` | disclosed | **construct** (old Tier 2) |
| 11 | `M7-SCON-PRESENTATION` | disclosed | **construct** (old Tier 2) |
| 12 | `M7-LUV-SYNTAX` | disclosed | **construct** (old Tier 2) |
| 13 | `M7-DUS-APPROX` | disclosed | Leave disclosed unless Anson reopens it |
| 14 | `M7-STRICT-SEPARATORS` | disclosed | Leave disclosed unless Anson reopens it |
| 15 | `M7-COMP-SYNTAX` | disclosed | **construct**, prerequisite of `M7-QUOTE-AFFINE` |

Current count: **5/15 constructed**. Target count: **13/15 constructed**. The eight remaining
constructions are `M7-FEEDBACK-TRUTH`, `M7-DUS-PREFIX-SYNTAX`, `M7-SCON-COMPILER`,
`M7-SCON-PRESENTATION`, `M7-LUV-SYNTAX`, `M7-PREFIX-MACHINE`, `M7-COMP-SYNTAX`, and
`M7-QUOTE-AFFINE`.

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

## START HERE — construct `M7-FEEDBACK-TRUTH`

This is the next sizeable goal. It completes the other half of the delayed-feedback
representation used by `thm:wubaff` and reused by `thm:wubexp`.

### Boundary correction that must happen first

`DeterminedViaTheory As P DP truth` is semantic. It does not make the real-valued function
`truth : ℕ → ℝ` computable, so there cannot be a uniform `FeedbackTruthSequence` constructor
from determination alone.

The paper additionally assumes that the completed-theory value of the relevant affine
combination is computable before the next deferral deadline. Represent that premise
explicitly with a conclusion-free operational certificate (working name
`FeedbackTruthComputation`). It should provide:

- rational truth values, or rational codes for them, at the required `f k` indices;
- equality of those rationals with the semantic completed-theory values;
- one code/program that produces the rational result from `k` (or an equivalent uniform
  input convention); and
- a halting specification within `ecClock a degree (f (k + 1))`.

The computation certificate must not contain prices, delayed-price accuracy, bias,
convergence, exploitation, or weighted-unbiasedness conclusions. Do not use the semantic
real-valued `truth` function as an efficient oracle.

### Construction tranche

1. **Fix the interface.** State the minimal operational computation certificate near
   `FeedbackTruthSequence`, document its correspondence with the premise of `thm:wubaff`,
   and keep normalization/magnitude data separate from the computation claim.

2. **Compile the sparse schedule.** Reuse `codeEvalnNat_polyFueled`, `scheduledMatch`, and
   `scheduledDeferral`. On day `n`, boundedly recognize the unique `k` satisfying
   `f (k + 1) = n`; emit zero when no bounded run establishes a scheduled match. Strict
   increase supplies uniqueness. Do not compute an unbounded inverse of `f`.

3. **Emit literal centered affine syntax.** At a scheduled day emit
   `A (f k) - truthRat (f k)`, including polynomial term count, coefficient serialization,
   sentence codes, and constant serialization. Prefer the existing variable-width
   conditional blocks and prefix scanner.

4. **Prove the `FeedbackTruthSequence` fields.** Establish `PolySequence`, bounded prices,
   magnitude at most one, completed-world value zero, and the exact identity

   ```text
   sequence (f (k + 1)) priced on day f (k + 1)
     = price of A (f k) on day f (k + 1) - truth (f k).
   ```

   Obtain normalization and magnitude bounds from the normalized
   `BoundedCombinationSequence` data used by `wubaff`, rather than putting an artificial
   bound inside the truth-computation certificate.

5. **Discharge public consumers.** Add a public constructor from the computation
   certificate and derived `wubaff`/`wubexp` entry points that accept the paper-faithful
   computation premise instead of an opaque preassembled `FeedbackTruthSequence`.

6. **Close the tranche.** Build the focused roll-up and the whole project, scan for holes,
   inspect the diff, print public axioms, and commit each coherent green layer.

Definition of done: the derived public feedback theorems no longer require callers to
manufacture `FeedbackTruthSequence`. Their remaining extra input is an explicit uniform
program-and-deadline law matching the paper. The constructed sequence is literal syntax,
and its accuracy is still derived by `FeedbackTruthSequence.accurate` rather than assumed.

Likely commit layers:

1. expose the operational truth-computation certificate;
2. compile/decode the bounded sparse schedule;
3. emit the centered affine fields;
4. assemble `FeedbackTruthSequence` and prove semantics;
5. discharge consumers and run the full verification gate.

## What follows `M7-FEEDBACK-TRUTH`

The next session should reassess ordering after the truth compiler lands, but it must retain
all eight active constructions above. The dependency shape is:

- The remaining old Tier 2 operational witnesses are `M7-DUS-PREFIX-SYNTAX`,
  `M7-SCON-PRESENTATION`, `M7-SCON-COMPILER`, and `M7-LUV-SYNTAX`.
  `M7-SCON-PRESENTATION` should precede the parts of `M7-SCON-COMPILER` that consume it.
- `M7-PREFIX-MACHINE` is an independent, sizeable tranche. It includes a concrete universal
  self-delimiting machine/presentation, efficient sentence coverage, from-below weight
  emission, the finite Kraft inequality, derived threshold-token arithmetic, and the
  fixed-overhead syntactic-negation compiler. It may be moved earlier when a self-contained
  Kraft tranche is desirable.
- `M7-COMP-SYNTAX` must precede `M7-QUOTE-AFFINE`. It supplies the first-order
  representability, Gödel coding, and diagonal/fixed-point machinery needed to make affine
  quotation concrete.
- `M7-QUOTE-AFFINE` must cover both the same-day completed-theory quotation packages and the
  deferred fixed-portfolio `AffineQuoteEq`/`AffineQuoteGE` packages. Do not describe it as a
  mere wiring theorem or silently leave its `M7-COMP-SYNTAX` root disclosed.
- `M7-DUS-APPROX` and `M7-STRICT-SEPARATORS` remain the only two disclosed boundaries at the
  13/15 target.

Only after the 13/15 construction target is green should the work move to surface freeze,
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
