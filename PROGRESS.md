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
| M1 | `def:tf` keystone + `def:lang` + criterion defs | **done** (pending Anson's statement read-through) — keystone + all Part-I criterion defs stated & green; one **provisional type-`(c)`** in `EfficientlyComputable` |
| M2 | Engine + one e.c.-certified exploiting trader, end-to-end | **done** (pending read-through) — the loop is wired **completely and with no `sorry`**: real trader, e.c. discharged via the faithful clocked-interpreter model, exploitation proved, criterion invoked. Engine `def:tradermag`/`def:roi` defined. **`EfficientlyComputable` reconciled to the paper's poly-time `def:ec`** (OPEN RISK 3 resolved) |
| M3–M7 | see roadmap | not started |

Out-of-sequence bonus: `brouwer_fixed_point` (the M6 gate) is already **proved**, not
axiomatized — see the ledger row and OPEN RISK 2 below.

## Node ledger

| Label | Lean decl | Status | Kind | Provenance / notes |
|---|---|---|---|---|
| (scaffold) | `LogicalInduction.*` module skeleton | stmt | — | Parts I–IV + Asymptotics; all elaborate |
| `dd:asymp` | `AsympEq`/`AsympLE`/`AsympGE` (`≈ₙ`/`≲ₙ`/`≳ₙ`), `EventuallyWithin`, `ConvergesTo` | done | Def | thin defs over `Tendsto (·−·) atTop (𝓝 0)` / `∀ᶠ n in atTop` `(b)` |
| `dd:asymp` API | `asympEq_iff_eventuallyWithin`, `AsympEq.refl/symm/trans`, `AsympEq.asympLE/asympGE`, `AsympLE.trans`, `AsympLE.trans_asympEq`, `AsympEq.finsetSum`, `asympEq_iff_asympLE_asympGE`, `convergesTo_iff_asympEq_const` | done | P | all hypotheses `(b)`; no sorries. `AsympLE.trans`/`trans_asympEq`/`finsetSum` added to match the deference corpus's `DeferenceAsymp` combinators (integration test) |
| `def:lang` | `Sentence` (`Foundations.lean`) | done | Def | reducible `abbrev` over `LO.Propositional.Formula ℕ` `(b)`; `DecidableEq`+`Encodable` transfer for free (`example` witnesses in-file) |
| `def:market` (substrate) | `Valuation`, `History` (`Foundations.lean`) | done | Def | `Valuation := Sentence → ℝ`, `History := ℕ → Valuation`. Type-`(c)` disclosures: codomain `ℝ` not `[0,1]` (constraint imposed downstream); days indexed from `0` not `ℕ⁺` (uniform convention). Full `def:market`/`def:world`/`def:pricing` structures still TODO |
| `def:world`+p.c. | `PCWorld`, `.Holds`, `.payout`, `.ConsistentWith` | done | Def | p.c. world = Foundation Boolean model (`Formula.Boolean.val` over `ℕ → Prop`) `(b)`; `payout` the `{0,1}` share value (classical `if`) |
| `def:dedproc` | `DeductiveProcess` (`D : ℕ → Finset Sentence`, `mono`) | done | Def | type-`(c)`: computability of `D` not carried in the type (re-enters in Part IV); disclosed |
| `def:tradestrat` | `Strategy n` (`trades`, `rank_le`), `.value`, `.cost` | done | Def | paper's canonical `(eᵢ,φᵢ)` encoding; `value = Σ eᵢ(𝓥)·(w φᵢ − 𝓥ₙ φᵢ)` |
| `def:trader` | `Trader` (`strat`), `.netWorth`, `.plausibleAssessments` | done | Def | sequence of `n`-strategies; net worth `∑_{i≤n}` day-`i` values |
| `def:exploitation` | `Trader.Exploits` | done | Def | `BddBelow ∧ ¬BddAbove` of plausible assessments — quantifiers per paper `(b)` |
| `def:exploitation` (non-vac) | `Trader.zero_not_exploits` | done | **N+** | do-nothing trader (netWorth ≡ 0) does not exploit → `Exploits` is refutable, criterion non-vacuous |
| `def:lang` (codes) | `EF.toNat`/`ofNatAux`/`ofNat`, `Encodable EF` | done | **P** | hand-built **computable** encoding (no `deriving`), **`Nat.pair`-tagged (no multiplication)** so the strategy-encoding function is `Nat.Partrec.Code`-primitive-friendly (`pair`/`comp`/`const`, no `prec`) — the key to provable responsive-trader e.c. (design (B), full faithfulness preserved). Round-trip axiom-clean |
| `dd:fuel` (infra) | `Fueled` + `fueled_const/left/right/succ/pair/comp/id` (`Computable.lean`) | done | **P** | prec-free fuel combinators: `Code.pair`/`comp` don't decrement `evaln`, so a `Nat.pair`-tree code's budget composes. The hard, novel part — fuel accounting through the clocked interpreter. Axiom-clean |
| `dd:fuel` (bridge) | `IsPolyBounded` (+`of_le`/`linear`/`max`/`add_one`/`pair`), `pair_lt_sq`, `of_fueled` | done | **P** | poly-bound closure incl. `Nat.pair` (degree doubles); turns a poly-bounded `Fueled` fact into `def:ec` |
| `dd:fuel` (capstone) | `PolyFueled` (+`const`/`id`/`pair`/`succ_comp`), `priceTrader`, **`priceTrader_ec`** | done | **P** | **first responsive trader certified e.c. under the faithful `def:ec`** — `priceTrader φ` plays `[(φ*ⁿ,φ)]` (coefficient varies with `n`); code assembled from `PolyFueled` primitives, poly bound automatic. Axiom-clean. Validates the whole e.c. pipeline; the property-tail responsive traders now follow this pattern |
| `def:ec` (tool) | `evaln_const_self` | done | **P** | `K ∈ evaln (n+K+1) (Code.const K) n` — fuel bound for constant-strategy traders |
| `def:ec` | `EfficientlyComputable` | done | **Def, faithful** | ✅ **reconciled (was type-`(c)`):** `∃ code, poly, ∀n, evaln (poly n) code n = some (encode strat)` — the paper's poly-*runtime* `def:ec` via `Nat.Partrec.Code` + `evaln` (`dd:fuel`). No longer broader than paper; `IsLogicalInductor` now matches. See OPEN RISK 3 (resolved) |
| **`def:lic`** | `IsLogicalInductor` (class over `P`, `DP`) | done | Def | "no e.c. trader exploits `P`". The property-tail hypothesis. Meaningfulness rests on the provisional `EfficientlyComputable` above |
| `def:trader` (M2) | `buyDaily` (buys 1 share of `φ`/day) | done | **C** | the **constructed** exploiting trader for the base case of `thm:provind`. Real EF (`[(const 1, φ)]`), not a stub |
| `def:ec` (M2 cert) | `buyDaily_ec` via `buyDaily_cost` | done | **P** | e.c. **discharged through `EF.cost`**: strategy cost `= 3` ∀n ⇒ poly. The load-bearing M2 step, done for real |
| `def:exploitation` (M2) | `buyDaily_exploits` | done | **P** | full proof: BddBelow (net worth ≥ 0 in every plausible world) ∧ ¬BddAbove (≥ (m+1)ε → ∞). No `sorry`; `#print axioms` = the 3 standard only |
| `def:luv` | `LUV` (threshold sentences `gt : ℚ → Sentence`) | done | Def | **disclosed type-`(c)`:** LUVs are first-order (formula free in one var over Θ-rep-computations); we model the `[0,1]`-LUV by its market-observable content = its threshold-sentence family `⌜X>r⌝`. No first-order syntax reconstructed |
| `def:e` | `LUV.expectApprox`, `.expect`, `.expectSeq`, `.expectInf`; `expect_mem_Icc` | done | Def+P | `𝔼ₙ(X)=(1/n)∑_{i<n}Pₙ(⌜X>i/n⌝)` — the **concrete `ℕ→ℝ` expectation** the deference corpus abstracts as `E^H_n(X)`. Bounds `∈[0,1]` proved. **This is the LUV-bridge object that closes the price→expectation level gap** |
| `thm:ec` | `LUV.expect_converges` | **sorry** | C | expectations converge; stated conditionally on `[IsLogicalInductor]`. **Deferred `sorry`** — genuine property-tail theorem (`app:ec`): needs per-threshold `thm:con` + moving-precision control (moving-threshold trader infra). Honestly ledgered |
| **integration** (expectation) | `IntegrationTest` Part C | done | **C** | closes the interface level gap: `value_argmax_asymptotic` instantiated with concrete `X.expectSeq P` for all `E_now(·)` slots — the corpus's expectation sequences **are** our objects, no adapter. LI hypotheses still assumed (= `thm:cee/expprovind`, the property-tail work `Expectations` states) |
| **integration** | `IntegrationTest.value_argmax_asymptotic`, `provind_hypothesis_discharged` | done | **C** | roadmap M3 integration test. Reproduces the deference corpus's `value_argmax_asymptotic` in our vocabulary (drop-in ✓ — `DeferenceAsymp.Approx/AsympLE` are *defeq* our `AsympEq/AsympLE`) and discharges a provind-shaped hypothesis `Approx (P·φ) 1` from `lic_deducible_tendsto_one` with no adapter. Axioms clean. **Finding:** interface matches at the *price/asymptotic* level; expectation-level hypotheses (`E^H_n`) still need the LUV bridge (M3/M4) |
| `thm:lc` bullet 2 (disprovable→0) | `lic_disprovable_tendsto_zero`, `sellDaily`, `sellDaily_exploits_freq`, `PCWorld.payout_of_disprovable` | done | **C** | Limit-Coherence dual: `∼φ` always-deducible ⇒ `Pₙ(φ)→0` under a logical inductor. Mirror **sell** trader (`[(const -1,φ)]`), constant hence e.c.-certified like `buyDaily`; frequently-overpriced accumulation. Foundation Boolean semantics gives `payout φ = 0` in `∼φ`-worlds. Axioms clean. (Bullet 1 = `lic_deducible_tendsto_one`; bullet 3, finite additivity, needs a non-constant/ROI trader — bounded-below fails for a naive constant portfolio — deferred) |
| `thm:provind` (limit, fixed φ) | `lic_deducible_tendsto_one`, `lic_deducible_eventually_ge`, `buyDaily_exploits_freq` | done | **C** | the genuine `≈ₙ 1` limiting form for a *fixed* always-deducible `φ`: **reuses the M2 e.c.-certified `buyDaily`** (no new trader/e.c.) via a frequently-underpricing accumulation argument (`extraction_of_frequently_atTop` + subset-sum). Axioms clean. Sequence form (`𝓔𝓒`-sequence `φₙ`, responsive trader) deferred — needs the e.c. Code-combinator infra |
| `thm:provind` (base case) | `lic_deducible_price_near_one` | done | **C** | the loop closed against `def:lic`: under `[IsLogicalInductor]`, an always-deducible `φ` has `1−ε < Pₙφ` for some n, ∀ε>0. **Special case** (always-deducible, uniformly underpriced); general `thm:provind` is M3 |
| `def:tradermag` | `Strategy.magnitude`, `Trader.magnitude`, `abs_value_le_magnitude` | done | Def+P | magnitude + the `\|value\| ≤ magnitude` bound proved (needs `[0,1]` prices + `{0,1}` world) |
| `def:roi` | `HasROI` | done | Def | ε-ROI predicate over `ConvergesTo` (`dd:asymp`). The ROI⇒exploitation **lemma** is M4 |
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

- **✅ OPEN RISK 3 — `EfficientlyComputable` fidelity — RESOLVED.** The provisional
  poly-*size* stand-in has been replaced by the faithful `dd:fuel` model: a trader is e.c.
  iff a single `Nat.Partrec.Code` program, run under the clocked interpreter `evaln` for a
  *polynomial* fuel budget `a·(n+1)ᵏ+a`, outputs the encoded day-`n` strategy. This is the
  paper's poly-time (unary) `def:ec` on the nose, and the e.c. class is computably
  enumerable (over `(code, a, k)` triples) as the construction will need. It no longer
  admits uncomputable strategy sequences, so `IsLogicalInductor` now *matches* the paper
  rather than being strictly stronger — the M7 soundness risk is gone. Two pieces of new
  infrastructure made this possible: a hand-built **computable** `Encodable EF` (there is no
  `deriving Encodable`; structural `toNat` + fuel-clocked structural `ofNat` + round-trip,
  `#print axioms` clean), and `evaln_const_self` (a `Code.const` fuel bound). M2's
  `buyDaily_ec` was re-proved against the new definition with no `sorry` and a clean axiom
  footprint.

- **Faithful `def:ec` via `Nat.Partrec.Code.evaln`** (post-M2): chose to model efficient
  computability directly on `dd:fuel` — Mathlib's clocked interpreter `evaln` with a
  polynomial fuel budget — rather than keep the poly-size proxy. Required hand-building a
  **computable** `Encodable EF` (no `deriving Encodable` exists; a classical `Countable`
  one would give a non-computable decoder, which would not let a machine recover the
  strategy — so it had to be genuinely computable). Used a fuel-clocked *structural*
  decoder (`ofNatAux`) to sidestep well-founded-recursion pain (`decreasing_by` would not
  expose the match's `m % 6 = k` condition to `omega`). This closes the one genuine
  soundness gap in the stack.
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
- **`def:lic` criterion definitions** (M1): worlds modeled as Foundation Boolean models
  (`PCWorld := ℕ → Prop` read through `Formula.Boolean.val`), so propositional consistency
  is free and faithful rather than hand-rolled over Foundation's connectives. Strategies use
  the paper's canonical `(eᵢ,φᵢ)`-list encoding. **The one load-bearing debt is
  `EfficientlyComputable`** — a provisional poly-*size* bound standing in for the paper's
  poly-*runtime* `def:ec`; it is *broader* than the paper's notion (so `IsLogicalInductor`
  is *stronger*), which is the single most important thing to get right in M2 before any
  property proof leans on it. Flagged loudly in the def's docstring and the ledger. This is
  a **surfaced friction**, not a silent shortcut: M2 exists precisely to wire `EF.cost`
  through a genuine efficiency notion end-to-end.
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
