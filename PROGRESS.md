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
| Foundation | **fork** `A-M-Berns/Foundation@aada66e` (= upstream `83d98a36` + three `Matrix.*`→`vec*` renames: `map`, `forall_iff`, `exists_iff`; see OPEN RISK 1; upstreamed as PR #835) |
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
| M1 | `def:tf` keystone + `def:lang` + criterion defs | **in progress** — `def:tf` keystone + `def:lang` substrate done (below); `World`/`Trader`/`Exploits`/`IsLogicalInductor` still TODO |
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
| `def:lang` | `Sentence` (`Foundations.lean`) | done | Def | reducible `abbrev` over `LO.Propositional.Formula ℕ` `(b)`; `DecidableEq`+`Encodable` transfer for free (`example` witnesses in-file) |
| `def:market` (substrate) | `Valuation`, `History` (`Foundations.lean`) | done | Def | `Valuation := Sentence → ℝ`, `History := ℕ → Valuation`. Type-`(c)` disclosures: codomain `ℝ` not `[0,1]` (constraint imposed downstream); days indexed from `0` not `ℕ⁺` (uniform convention). Full `def:market`/`def:world`/`def:pricing` structures still TODO |
| `dd:fuel` | `EfficientlyComputable` (planned) | — | Def | fuel-clocked interpreter; **disclosed type-`(c)`** modeling of poly-time |
| **`def:tf`** | `EF` (inductive), `EF.denote`, `EF.cost`, `EF.rank` (`Criterion.lean`) | done | Def | keystone DSL: price/const/add/mul/max/safeRecip. `denote` noncomputable (ℝ inv); `cost` = structural node count — **disclosed `dd:fuel` deferral:** precise unary day/code charging tying `cost` to poly-runtime is M2, when the trader e.c. cert first consumes it |
| `def:tf` (continuity) | `EF.continuous_denote` | done | **P** | continuity **proved** for the whole DSL (not left as a stated constraint), by induction; safeRecip via `max 1 · ≥ 1 > 0`. Hyps `(b)` (Mathlib `continuous_apply`/`Continuous.{add,mul,max,inv₀}`). This is what breaks the price/trade circularity for Brouwer |
| `def:tf` (ring) | `EF.ExpressibleRankLE`/`EFn`, `CommRing (EFn n)` | done | **P** | `𝔼_n` realized as a **`Subring` of `History → ℝ`** (features are functions): carrier `{denote e \| rank e ≤ n}`, closure under `+,×,neg` proved; `CommRing` inherited. Faithful to the paper's "𝔼_n is a commutative ring" `(b)` |
| `def:tf` (non-vacuity) | `EF.exMaxDiff` + 2 `example`s | done | **N+** | the paper's `max(0, φ*6−ψ*7)`: rank `= 7` and value `= 0.3` at the paper's inputs; plus safeRecip lands in `(0,1]` for all args. Genuine (non-constant) witnesses |
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
- **✅ OPEN RISK 1 — Foundation/Mathlib `Matrix`-namespace clash — RESOLVED via fork (now
  the complete set).** `Foundation.Vorspiel.Matrix` (in Foundation's prelude, so *all*
  Foundation modules) extends the `Matrix` namespace with its own `Fin k → α` helpers,
  three of which shadow distinct Mathlib `Matrix.*` names, making Foundation unimportable
  alongside the corresponding Mathlib module:
    - `Matrix.map` ↔ Mathlib `Matrix.map` (via `Matrix.map.eq_1`; Bochner, matrix analysis) — found M0;
    - `Matrix.forall_iff`, `Matrix.exists_iff` ↔ `Mathlib.Data.Matrix.Reflection` — found **M1**, when
      `Foundations`/`Criterion` (which import Foundation) first shared the roll-up's import graph with
      `Construction/Brouwer` (which pulls `Matrix.Reflection` transitively via `EuclideanSpace`).
  Fixed by renaming all three to `vecMap` / `vecForall_iff` / `vecExists_iff`
  (`A-M-Berns/Foundation@aada66e`; notation `⨟` and lemma bodies unchanged, 12 call sites
  updated). Verified **complete**: intersected every `Matrix.*` decl in `Vorspiel/Matrix.lean`
  against Mathlib — no other collisions. Full roll-up (Foundation + Bochner + Brouwer) now
  builds green. Upstreamed as **PR #835**. *Discipline note kept:* still prefer targeted
  Mathlib imports over the `import Mathlib` umbrella alongside Foundation.
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
- **`def:tf` keystone modeling choices** (M1): (1) `EF` is *syntax*; the CommRing "`𝔼_n`"
  lives on the *semantic* side as a `Subring` of `History → ℝ` (features are functions),
  avoiding a syntax quotient — the syntax stays the object that carries `cost`. (2)
  `denote`'s domain `History := ℕ → Sentence → ℝ` uses codomain `ℝ` (not `[0,1]`) and
  0-indexed days (not `ℕ⁺`) — both disclosed type-`(c)` conveniences, ledgered. (3)
  Continuity is *proved*, not just stated (the roadmap allowed `sorry`); it was cheap and
  it strengthens the Brouwer hand-off. (4) `cost` = structural node count for now; the
  precise `dd:fuel` unary charging is deferred to M2 where the e.c. cert first needs it.
- **Extended the Foundation fork to the full clash set** (M1): the `Matrix.map` rename
  (M0) was one of three colliders; `forall_iff`/`exists_iff` surfaced when the roll-up
  first co-imported Foundation with the Brouwer file. Chose to fix the root cause now
  (rename all three, bump pin to `aada66e`, broaden PR #835) rather than decouple the
  roll-up — per Anson's call — since the construction (M6) will need Foundation+Brouwer
  together regardless.
- **Library layout flattened.** One file per Part (`LogicalInduction/<Part>.lean`) rather
  than the Mathlib `<Part>.lean` + `<Part>/` roll-up idiom, since each Part currently has
  a single file. Promote a Part to the directory idiom when it grows multiple files
  (`Properties` will be first).
