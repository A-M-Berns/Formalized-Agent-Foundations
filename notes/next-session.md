# Logical Induction — handoff

_Last updated: 2026-07-21. Branch: `logical-induction`._

The active next task is the **fresh-context M7-ERRATA-AUDIT** (below). If you are a fresh
context reading this: that is the whole point — you are the independent auditor. This
handoff was written by an involved party; treat its framing and every docstring/provenance
claim as *to be verified*, not trusted.

## Where things stand (end of consolidation)

The **12/15 conditional+disclosed green endpoint is complete** and the consolidation phase
(step 2 of the sequencing override in `CLAUDE.md`) is essentially done. This session landed,
on top of the construction handoff (now in git history):

- **Paper-node inventory, two tiers, build-enforced.** `AxiomAudit.lean` (a
  `@[default_target]`, so `lake build`/CI runs it) is the endpoint inventory: Tier 1 = 103
  proof endpoints under `#assert_axioms_clean`; Tier 2 = boundary structures under a new
  `#assert_fields` (freezes each structure's hypothesis fields — adding/removing a field
  fails the build). Membership is mechanical: a structure is Tier 2 iff it appears in a
  Tier-1 endpoint's type, transitively through fields (`SurfaceProbe.lean`). Rationale and
  judgment calls: `notes/endpoint-inventory.md`.
- **`Paper node:` annotations** on every inventory member's docstring, labels verbatim from
  `notes/1609.03543v5-main.tex`. Enforced by `scripts/check-paper-nodes.sh` (every cited
  label exists; every member carries one). `scripts/lint_paper_labels.py` is now blocking
  (every `theorem` ⇔ a paper node; no `private theorem`).
- **Whole-repo axiom audit.** `AxiomAudit.lean` now also covers `Barasz/`, with the one
  intentional axiom `glFixedPoint_thm42` scoped precisely to the endpoints that use it via
  `#assert_axioms_clean_except`. Barász endpoints that don't need it are asserted strictly
  clean.
- **Duplication sweep.** Removed two genuine duplicate helper lemmas (`max_sub_max_neg`,
  `oneMinus_denote`). Construction/ has no duplicate *facts* — its parallel shapes
  (`*FromStages`/`*FromStageLists`, triangular/gap/frame families) are by-design over
  distinct types.
- **Stale-reference repair.** Fixed a merged-away README path (`StrictSemimeasure.lean` →
  `UniversalSemimeasure.lean`) and three dead `PROGRESS.md` pointers (that ledger was
  deleted; the comments are now self-contained). Includes a live `thm:ifp` paper-erratum
  note in `FinitePerturbations.lean` — see the errata-audit brief.

**State:** working tree clean; full `lake build` green (2689 jobs); AxiomAudit clean.
**8 commits on `logical-induction` are unpushed** (top is `bdb9e28`). Nothing pushed this
session, per Anson's workflow.

## What remains after this (not just documentation)

Per the roadmap endpoint list: surface freeze ✓, consolidation/API/style ✓ (this session).
Still open, in order:

1. **This task — fresh-context M7-ERRATA-AUDIT** (below).
2. **Human statement read-through** — Anson reads every top-level statement + definition
   over the frozen surface. A verification gate, only Anson. Not started.
3. **Paper comparison** — fidelity of each statement to Garrabrant et al. The paper-node
   annotations are its scaffolding. Not started.
4. **Optional construction** — the two Aristotle experiments in flight (below), and behind
   Kraft the rest of `M7-PREFIX-MACHINE` for a 13/15 stretch (`notes/m7-prefix-machine-scope.md`).

---

# THE NEXT TASK — M7-ERRATA-AUDIT (fresh-context adversarial audit)

Mandated by `CLAUDE.md` ("Scheduled adversarial audit") as a **separate, fresh-context**
statement-level pass, run **last** in the sequencing override. Clearing context and running
it here satisfies the fresh-context requirement.

## Mandate

A kernel-clean build certifies each *body* matches its *statement*. It says nothing about
whether the statement is the one we meant. Audit the **trust surface** — the top-level
statements, their hypotheses, their conclusions, and the definitions they rest on — for the
ways a statement can be green yet hollow. **Do not trust docstrings, provenance labels
(`Def`/`P`/`C`/`S`/`T`/`N±`, `(a)`/`(b)`/`(c)`), or this handoff; verify against the Lean
source and the paper.**

## Scope (precisely defined — use it)

The audit target is the audited inventory, already enumerated for you:

- **`AxiomAudit.lean`** — Tier 1 (103 `#assert_axioms_clean` endpoints, incl. `Barasz`) and
  Tier 2 (the `#assert_fields` boundary structures). This *is* the list of top-level
  theorems + the hypothesis-bearing structures.
- **`notes/endpoint-inventory.md`** — the tiers' rationale and the judgment calls made
  building them (those calls are themselves fair game).
- Paper source for fidelity: `notes/1609.03543v5-main.tex` (labels resolve via
  `\label{...}`), PDF alongside.

## The six failure modes to hunt (from CLAUDE.md)

1. **Vacuous theorems** — hypotheses unsatisfiable or unrealizable, so the theorem is
   about nothing. Especially: boundary structures whose field set (frozen in
   `#assert_fields`) is not inhabitable for the intended objects.
2. **Conclusion-in-hypothesis squeezes** — the conclusion is ≡ a hypothesis, or a
   hypothesis does the work the proof should. (Docstrings self-flag these as kind `S`;
   confirm each is honest, and find the unflagged ones.)
3. **Oversold stubs** — a `T`/trivial or arithmetic proof standing in for real content;
   most dangerous where an *exploiting trader* or an *e.c. certificate* should be the work
   (`CLAUDE.md` load-bearing rule 1).
4. **Type-`(c)` substitutions** — a weaker/different object stands in for the intended one.
   `dd:fuel` (efficiency = fuel-clocked interpreter, not a complexity class) is the
   repo-wide one and is disclosed; hunt for *undisclosed* local ones.
5. **Degenerate non-vacuity** — a "non-empty"/existence witness that is a constant sequence
   or otherwise trivial, so it proves inhabitation without proving anything real. Where
   possible the non-vacuity guard should be discharged **by the M7 construction**, not a
   stand-in witness — check that the constructors actually inhabit the boundaries their
   consumers assume.
6. **Off-loaded steps** — a hand-computation where a Mathlib/Foundation lemma should carry
   it (a correctness-and-legibility smell, not necessarily a soundness bug).

## Method

- Start from the paper. For each Tier-1 endpoint, read its statement against its
  `Paper node:` label in `main.tex`: does the Lean statement say what the paper's node
  claims, with the same strength, or has a hypothesis been added / a conclusion weakened?
- For each `_ofComputation` / `_ofRepresentation` / `_ofFeedbackTruth` construction-
  discharged endpoint, verify the constructor genuinely inhabits the boundary (mode 5) and
  that the discharged version is not weaker than the abstract one it replaces.
- Cross-check the disclosed boundaries (below) are *only* the three intended, and that no
  additional boundary is silently assumed inside a "constructed" witness.
- The `thm:ifp` **paper erratum** in `Properties/FinitePerturbations.lean` (the appendix
  proof's efficiency claim is false — finitely many *days* but unboundedly many sentences)
  is a known live disclosure. Confirm the Lean statement handles it honestly (the
  perturbation structure is *not* inhabited for every `ComputableMarket`) and is not sold
  as more than it is. This item likely belongs in the README's disclosures too — flag if so.

## Deliverable

Write `notes/m7-errata-audit.md`: findings ranked most-severe first, each with the failure
mode, the exact endpoint/file:line, the evidence, and a proposed disposition. An empty or
near-empty report is a legitimate and good outcome — but only if genuinely verified, stated
as such, with the method shown. **Fix nothing during the audit**; report, then let Anson
triage. Green the build is not the goal here; honest findings are.

---

## Aristotle experiments in flight (external state — survives context, IDs do not)

Two jobs testing whether Aristotle can discharge remaining hard pieces. **Job IDs live only
here now — a fresh context needs them to poll.** Trust rule: a returned proof is trusted
only after it compiles in *this* repo; the kernel is the gate, never Aristotle's word.

- **GL fixed-point axiom** (`glFixedPoint_thm42`, the one intentional Barász axiom).
  Project id **`9226321a-32f8-414b-9d30-6ef06093b7f0`** (name `gl-fixedpoint`), submitted
  2026-07-20, `RUNNING` at last check (~50 min). Poll: `aristotle list` /
  `aristotle show 9226321a-32f8-414b-9d30-6ef06093b7f0`. Odds low (Foundation-dependent;
  toolchain one patch off; hard modal metatheorem). If it returns a proof, drop it into
  `Barasz/FixedPoint.lean` replacing the `axiom`, rebuild, and re-run AxiomAudit — the
  `#assert_axioms_clean_except glFixedPoint_thm42` block should then move to strict
  `#assert_axioms_clean`.
- **Kraft inequality** (`kraft_inequality`, the Mathlib-only core of `M7-PREFIX-MACHINE`).
  **Prepared, not submitted** (awaiting Anson's go). Statement in
  `notes/m7-prefix-machine-scope.md`; Mathlib-only, validated to elaborate in-repo.

**Scratchpad projects may be ephemeral** (session-specific dir):
`…/scratchpad/gl-fixedpoint/` and `…/scratchpad/kraft/`. Both are tiny and reconstructible —
the Kraft statement is in the scope note; the GL project is `require Foundation @ aada66ef…`
+ the `Modalized`/`diag` defs + the axiom-as-`sorry` (see `Barasz/FixedPoint.lean:45`). If
resubmitting, use `scripts/aristotle-prove.sh <project-dir> "<prompt>"`.

## Deliberately disclosed boundaries

- `M7-PREFIX-MACHINE` — supplies standard universal self-delimiting-machine, from-below
  weight, finite Kraft, and fixed negation-overhead facts for Occam Bounds; the paper-
  specific market proof is already formalized. Optional post-target showcase; the finite
  Kraft core is the Aristotle-able piece (`notes/m7-prefix-machine-scope.md`).
- `M7-DUS-APPROX` and `M7-STRICT-SEPARATORS` — remain disclosed unless Anson reopens them.

These three are the only intentional disclosures at the 12/15 target. The audit should
confirm no fourth boundary is assumed anywhere it isn't named.

## Verification and commit discipline

Before any commit, smallest relevant build first, then:

```sh
lake build
rg -n '(^|[[:space:]])(sorry|admit)([[:space:]]|$)' LogicalInduction Barasz --glob '*.lean'
./scripts/check-paper-nodes.sh
python3 scripts/lint_paper_labels.py
git diff --check && git status --short
```

Axiom reports of any new public endpoint must contain only `propext`, `Classical.choice`,
`Quot.sound` (plus `glFixedPoint_thm42` for the Barász cooperation endpoints). Keep
historical detail in git rather than appending superseded plans below the active handoff.

## Aristotle usage

Via `scripts/aristotle-prove.sh`; only after a goal is fully stated and self-contained.
Prefer small extracted Mathlib-only projects, not the whole repo. `ARISTOTLE_API_KEY` must
be in the environment. Toolchain versions may differ; a returned proof is trusted only after
it compiles here.

## Reusable construction notes

- Search before proving. Anchors: `codeEvalnNat_polyFueled`, `deadlineRun`,
  `scheduledMatch`, `segPrefix_polyFueled`, `segLocate_polyFueled`,
  `PolySegStream.concatVar`, `PolySequence.priceFeature_polySeg`, `PGenerableWeighting.polySeg`.
- Deep `PolyFueled` proofs with nested `Nat.unpair` can trigger `Nat.sqrt` whnf blowups;
  prefer a narrow local `attribute [irreducible] Nat.sqrt` over raising heartbeats.
- Preserve literal token/list equalities at representation boundaries; semantic equality
  alone is not enough for the witness constructors.
- Keep computation certificates conclusion-free; economic/asymptotic conclusions belong in
  the already-proved consumer layer.
