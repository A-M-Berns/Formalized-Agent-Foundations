# PROGRESS — Logical Induction formalization

The ledger. Maps `blueprint label → Lean decl → status → kind → provenance`. Status:
`stmt` (statement only) · `sorry` (stated, proof deferred) · `done`. **Kind:** `Def` ·
`P` proved · `C` composition · `S` squeeze-over-named (flag + justify) · `T` trivial stub
· `N±` non-vacuity witness. **Provenance** (per hypothesis): `(a)` derived in-project ·
`(b)` Foundation/Mathlib citation · `(c)` modeling substitution (disclose or eliminate).

Rule: a new theorem is not committed without its ledger row, in the same commit. Fill
kind/provenance honestly as you go — they are the anti-self-deception mechanism, not
post-hoc bookkeeping.

## Pinned versions

| Component | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.28.0-rc1` |
| Foundation | **fork** `A-M-Berns/Foundation@0939b51` (= upstream `83d98a36` + `Matrix.map`→`Matrix.vecMap` rename; see OPEN RISK 1) |
| Mathlib | as resolved transitively by Foundation (see `lake-manifest.json`) |

Both Mathlib and Foundation are precompiled and build under this toolchain (Foundation
already `require`s mathlib). With the Foundation fork (OPEN RISK 1, resolved) they now
co-build across the full stack, including Bochner integration and matrix-heavy analysis.

Environment note: a stale ProofWidgets JS trace blocked all Mathlib builds with
"ProofWidgets failed to reuse pre-built JS code". Fixed by building ProofWidgets' JS
locally from its own package (`cd .lake/packages/proofwidgets && lake build`; npm is
available), which sidesteps Mathlib's `errorOnBuild` guard. Re-run if it recurs.

## Milestone status

| M | Scope | Status |
|---|---|---|
| M0 | Project stands up; namespace/file scaffold; substrate verified | **in progress** — scaffold + `Scratchpad` done; `Asymptotics` content pending |
| M1 | `def:tf` keystone + `def:lang` + criterion defs | not started |
| M2 | Engine + one e.c.-certified exploiting trader, end-to-end | not started |
| M3–M7 | see roadmap | not started |

## Node ledger

| Label | Lean decl | Status | Kind | Provenance / notes |
|---|---|---|---|---|
| (scaffold) | `LogicalInduction.*` module skeleton | stmt | — | Parts I–IV + Asymptotics; all elaborate, no decls yet |
| `def:lang` | `Sentence` (planned) | — | Def | will wrap `LO.Propositional.Formula ℕ` `(b)` |
| `dd:fuel` | `EfficientlyComputable` (planned) | — | Def | fuel-clocked interpreter; **disclosed type-`(c)`** modeling of poly-time |
| `def:tf` | `EF` / `denote` / `cost` / `CommRing EF_n` (planned) | — | Def | keystone; M1 target |
| `lem:fpl` (dep) | `brouwer_fixed_point` | sorry | N/A | **project axiom** — Mathlib lacks Brouwer (OPEN RISK 2); stated over `EuclideanSpace ℝ (Fin d)`, proof deferred to upstream contribution |

## Substrate findings (from `Scratchpad.lean`, M0)

- **`def:lang` is well-served by Foundation.** `LO.Propositional.Formula ℕ` carries
  `DecidableEq` and — the gating fact for `def:ec` — `Encodable (Formula α)`, a concrete
  `toNat` coding. So sentences have **computable codes off `ℕ` for free**; we do not need
  to build a Gödel numbering. Derivability/consistency come from `LO.Entailment`
  (`⊢` / `⊬` / `Consistent`), classical logic from `LO.Propositional.Hilbert.Cl`. Plan:
  wrap these behind a thin `LogicalInduction.Sentence` interface. Provenance `(b)`.
- **Mathlib substrate present:** `Filter.Tendsto` / `atTop` / `nhds` / `Filter.Eventually`
  (asymptotics), `IsCompact` / `Convex` / `ContinuousMap` (price space), and
  `MeasureTheory.integral` (Bochner, for the LUV bridge — present but see clash below).
- **✅ OPEN RISK 1 — scoped Foundation/Mathlib co-import clash — RESOLVED via fork.**
  `Foundation.Vorspiel.Matrix` (in Foundation's prelude, so *all* Foundation modules)
  defined its own `Matrix.map : (Fin k → α) → (Fin k → β)`, shadowing Mathlib's
  `Matrix.map`; both generate `Matrix.map.eq_1`, so Foundation could not be imported
  alongside any Mathlib module that materialized it (Bochner integration, matrix-heavy
  analysis) — which would have blocked the **LUV expectation bridge (M3)** and the
  **finite-dim analysis under Brouwer (M6)**. Fixed by forking Foundation and renaming
  the def to `Matrix.vecMap` (`A-M-Berns/Foundation@0939b51`, one-file change; notation
  `⨟` and lemmas unchanged). *Discipline note kept:* still never `import Mathlib`
  (umbrella) alongside Foundation — use targeted imports.
- **⚠ OPEN RISK 2 — no Brouwer.** Installed Mathlib has **no Brouwer (or Schauder/Kakutani)
  fixed-point theorem** — only Brouwerian/Heyting *algebras* and Riesz–Markov–Kakutani (a
  measure theorem). The roadmap's "use Mathlib's Brouwer" (`lem:fpl`) is false as written.
  M6 is gated on contributing the theorem upstream or finding an alternate route. This is
  the single biggest schedule risk found at M0, and it lands squarely on the construction
  (the Part the deference corpus dodged), exactly where the genuine difficulty was always
  expected to be.

## Decisions log

- **Library layout flattened.** One file per Part (`LogicalInduction/<Part>.lean`) rather
  than the Mathlib `<Part>.lean` + `<Part>/` roll-up idiom, since each Part currently has
  a single file. Promote a Part to the directory idiom when it grows multiple files
  (`Properties` will be first).
