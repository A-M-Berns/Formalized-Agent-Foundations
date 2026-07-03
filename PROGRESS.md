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
| M0 | Project stands up; namespace/file scaffold; substrate verified | **done** (pending Anson's statement read-through) — scaffold, `Scratchpad`, `Asymptotics` content all green |
| M1 | `def:tf` keystone + `def:lang` + criterion defs | not started |
| M2 | Engine + one e.c.-certified exploiting trader, end-to-end | not started |
| M3–M7 | see roadmap | not started |

Out-of-sequence bonus: `brouwer_fixed_point` (the M6 gate) is already **proved**, not
axiomatized — see the ledger row and OPEN RISK 2 below.

## Node ledger

| Label | Lean decl | Status | Kind | Provenance / notes |
|---|---|---|---|---|
| (scaffold) | `LogicalInduction.*` module skeleton | stmt | — | Parts I–IV + Asymptotics; all elaborate |
| `dd:asymp` | `AsympEq`/`AsympLE`/`AsympGE` (`≈ₙ`/`≲ₙ`/`≳ₙ`), `EventuallyWithin`, `ConvergesTo` | done | Def | thin defs over `Tendsto (·−·) atTop (𝓝 0)` / `∀ᶠ n in atTop` `(b)` |
| `dd:asymp` API | `asympEq_iff_eventuallyWithin`, `AsympEq.refl/symm/trans`, `AsympEq.asympLE/asympGE`, `asympEq_iff_asympLE_asympGE`, `convergesTo_iff_asympEq_const` | done | P | all hypotheses `(b)` (Mathlib: `Metric.tendsto_atTop`, `tendsto_sub_nhds_zero_iff`, …); no sorries |
| `def:lang` | `Sentence` (planned) | — | Def | will wrap `LO.Propositional.Formula ℕ` `(b)` |
| `dd:fuel` | `EfficientlyComputable` (planned) | — | Def | fuel-clocked interpreter; **disclosed type-`(c)`** modeling of poly-time |
| `def:tf` | `EF` / `denote` / `cost` / `CommRing EF_n` (planned) | — | Def | keystone; M1 target |
| `lem:fpl` (dep) | `brouwer_fixed_point` | **done** | P | **proved from scratch** (Sperner/Kuhn over the Freudenthal triangulation → fixed point on compact convex `K ⊆ EuclideanSpace ℝ (Fin d)`). Provenance: **autoformalized by Harmonic's Aristotle** (runs `1d7dc5e0`/`c712e6d9`, built there on Lean/Mathlib v4.28.0), dropped in verbatim modulo namespace + header, **revalidated on this project's toolchain** (v4.28.0-rc1, Mathlib master@58d8468): builds green, `#print axioms` = `propext, Classical.choice, Quot.sound` (checked in-file). Trust surface = the final statement only (unchanged from the M0 `sorry` version); the ~1300-line `BrouwerProof.*` interior is machine-generated proof plumbing nobody has read — the kernel has checked it, a human has not, which is exactly the division of labor the standard permits. Imports trimmed from the Aristotle original's `import Mathlib` umbrella to the 7-module minimal set found by `linter.minImports`. |

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
- **✅ OPEN RISK 2 — no Brouwer in Mathlib — RESOLVED in-project.** Installed Mathlib has
  **no Brouwer (or Schauder/Kakutani) fixed-point theorem** — only Brouwerian/Heyting
  *algebras* and Riesz–Markov–Kakutani (a measure theorem); the roadmap's "use Mathlib's
  Brouwer" (`lem:fpl`) remains false as written. Resolved instead by a from-scratch proof
  (Sperner's lemma route) in `LogicalInduction/Construction/Brouwer.lean`, autoformalized
  by Harmonic's Aristotle and revalidated on this toolchain — see the ledger row for the
  full provenance and trust-surface accounting. M6 is no longer gated. Upstreaming the
  proof to Mathlib is still desirable (and would let us delete the 1300-line vendored
  proof) but is now optional, not blocking.

## Decisions log

- **Paper vendored into `notes/`** (M0 close-out): `1609.03543v5.pdf` and its LaTeX
  source `1609.03543v5-main.tex` (the file the roadmap's `\label`s were verified
  against), so label questions are answerable in-repo. First use: the roadmap's §7
  kickoff prompt said `def:ef` where the paper's real label is `def:tf`
  (`main.tex:786`); fixed.
- **Aristotle output accepted for `lem:fpl`'s Brouwer dependency** (M0 close-out): see
  ledger row. Statement unchanged from the hand-written `sorry` version, so the trust
  surface didn't move; only the proof body (kernel-checked, human-unread) changed status.
- **Library layout flattened.** One file per Part (`LogicalInduction/<Part>.lean`) rather
  than the Mathlib `<Part>.lean` + `<Part>/` roll-up idiom, since each Part currently has
  a single file. Promote a Part to the directory idiom when it grows multiple files
  (`Properties` will be first).
