# Condensation — knowledge base

Institutional memory for this formalization: settled design decisions, the
correspondence table, intentional deviations, paper errata, and pitfalls. Committed on
purpose — a future session (or auditor) reads this before touching the library. See
`README.md` for the trust surface, `notes/roadmap.md` for the plan and the `dd:` glossary
in full, and `Condensation.lean` for the glossary as shipped.

## Correspondence table

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| Def 2.1 random variable `X : Ω → R` | Mathlib `Measurable` | rendered, not redefined |
| Def 2.1 pullback `π^* X` | `X ∘ π` | `dd:pullback` |
| Def 2.1 "`Y` is a function of `X` (a.e.)" | `Condensation.FunctionOf` / `Condensation.AEFunctionOf` | `dd:ae-function` |
| Def 2.2 `P⁺ S` | `Condensation.PPlus` | `dd:pplus` |
| Def 2.3 `H(X)`, `H(X\|Y)`, `I(X;Y\|Z)` | `H[X ; μ]`, `H[X \| Y ; μ]`, `I[X : Y \| Z ; μ]` (`ShannonInformation.API`) | vendored PFR |
| Def 2.3 `I(X;Y;Z)` | `Condensation.interactionInfo` | `dd:interaction` |
| Def 2.4 `G(Ω)` | Mathlib `MeasureTheory.Measure.instMeasurableSpace` | rendered |
| Def 3.1 random variable model | `Condensation.RVModel` | `dd:bundled-model`, `dd:finite-range` |
| Def 3.2 latent variable model | `Condensation.LatentModel` | |
| Def 3.3 σ_L, χ_L, ϱ_L | `LatentModel.simpleScore`, `.condScore`, `.reconScore` | |
| Def 3.4 `X_A`, `Y_F`, `Y_∩A`, `Y_⊇A`, `Y_⊋A`, `Y_∋i` | `RVModel.joint`, `LatentModel.jointOn`, `.contrib`, `.above`, `.strictAbove`, `.contribIdx` | names provisional until M0 lands |

(Extend as declarations land. Every formalized node gets a row.)

## Design decisions

See the `dd:` table in `notes/roadmap.md` — `dd:finite-range`, `dd:pplus`,
`dd:bundled-model`, `dd:ae-function`, `dd:pullback`, `dd:interaction`, `dd:tree`,
`dd:category`, `dd:amalgamation`. Rationale lives there; this file records *changes* to
them and the finding IDs that forced any.

- **`dd:finite-range` generalization: costed and deferred (2026-08-17).** Generalizing the
  substrate to countable range + finite entropy is ~1,450–2,400 lines / 3–4.5 focused
  weeks in four phases; the abstract core (grouping bound, local chain rule, countable
  Gibbs) was proved in ~90 lines against the pinned Mathlib as calibration; nothing in the
  paper is false or different under finite range, only the model class shrinks; no upstream
  help exists (PFR master's entropy files are byte-identical to the pin, Mathlib has no
  Shannon entropy). Full plan with acceptance criteria: `notes/finite-range-generalization-plan.md`.
  Consequence for the code: the finiteness condition lives in **exactly one field of
  `RVModel`** (role-named, documented as the stand-in for Def 3.1's "finite entropy") and is
  never taken as a separate theorem hypothesis, so a later swap to a `FiniteEntropy` class
  is a one-field edit plus substrate re-proof. Auditors: do not re-litigate the deferral;
  do flag any statement that reintroduces `FiniteRange` outside that field.
- Registry: `scripts/papers.py` uses two axes for this paper — `scheme: printed-counter`
  (how the paper numbers) and `source_format: text-extraction` (what the committed source
  is). Resolve parsers via `paper_nodes.scheme_of(paper)`, never `SCHEMES[scheme]` (the TeX
  parser returns an *empty* node set on a `.txt`, silently disarming the gate).
- Wiring-gate order for this library: `lean_lib Condensation` → Lean under `Condensation/` →
  `import Condensation` in `AxiomAudit.lean` → `-- CONDENSATION-INVENTORY-BEGIN/END` block
  wrapping `#assert_axioms_clean` (mandatory from the first annotated declaration; fully
  qualified names) → `python3 scripts/gen-trust-surface.py` after **any** change to a
  Condensation Lean file, README, KNOWLEDGE, errata, extraction, `papers.py`,
  `paper_nodes.py`, generator or template (the freshness hash covers all of them; CI blocks).
- Scope completeness is not yet machine-checked: `check-condensation-nodes.py` checks cited
  nodes are real, not that every in-scope node is cited. Once the Examples 5.1–5.3 ruling
  lands, pass a `scope_manifest` (`out_of_scope`, `mathlib_rendered` = Def 2.1, Def 2.4) to
  `paper_nodes.run_node_check` as the FFS checker does.
- Substrate: `ShannonInformation.API` only. Never name `PFR.*`; never `import Mathlib`
  wholesale in a Condensation file (clashes with the vendored shims — see
  `ShannonInformation/README.md`).

## Intentional deviations from the paper

- **`dd:finite-range`** (standing, type-(c) narrowing, disclosed): variables have finite
  range, not merely countable range with finite entropy; the sample space carries no
  finite-entropy hypothesis of its own. Reason: the vendored theorems are proved only in
  the finite-range fragment. Auditors: not a finding unless a *statement* is narrower than
  this decision requires.
- Examples 5.1–5.3 carry no declarations (proposed ruling; see roadmap).

## Disclosures (residual modeling substitutions)

None yet.

## Paper errata

- Thm 5.8 proof: "Equation (5.14) follows by a term-by-term comparison" — should be (5.13).
- Thm 4.15 proof: `F_i` is used but never defined (evidently `F_i = {B : i ∈ B}`); the
  induction over `⋂_{i∈A} F_i` is asserted, not set up.
- Cor 5.10 (5.24): "all but `n − 1` elements" — the parameter is `k`.
- Thm 4.9 (B2): "is a function of `X_i`" drops the "almost everywhere" of (A2).
- Lemma 4.5 proof cites "Corollary 2.5" — 2.5 is a Proposition.
- Cor 4.6 proof cites only Prop 4.2; the argument needs Lemma 4.5.
- `P I` written for `P⁺ I` in Lemma 4.5(2) and Cor 4.6 (the paper's omission, not the
  extractor's — the extractor renders this paper's superscript `+` on its own line elsewhere).
- Cor 5.10 uses `k` in its hypothesis one sentence before binding it; the degenerate
  `k = 0` (`F = {∅}`) and `k > |A|` (`F = ∅`, `G = P⁺I`) cases are unaddressed — must be
  resolved to state it in Lean.
- The intersection tree's label function is `ℓ` in Def 5.6/Prop 5.7 but `I` in Thm 5.8 and
  Cors 5.9–5.10, colliding with the index set and (inside (5.13)) with the mutual-information
  operator. Part of why `dd:tree` computes labels from tree structure.

Full list with line numbers: `notes/paper-errata.md`.

## Pitfalls

- `pdftotext` emits the font's f-ligature slots as C0 bytes (`\x1c`=fi, `\x1b`=ff,
  `\x1d`=fl, `\x1e`=ffi), so `Definition` is stored as `De\x1cnition` (prints `Denition`).
  **Python's `str.splitlines()` splits on `\x1c`/`\x1d`/`\x1e`** and silently deletes all
  18 Definition headers — always `text.split("\n")` on this file (`paper_nodes.extraction_lines()`).
  Ligature-tolerant regex is `De(?:fi)?.?nition` (`De.?nition` fails on the plain spelling).
  Node headers are distinguished from line-initial cross-references only by the trailing
  period after the number/title parenthetical.
- Two `∑'`-style traps in the substrate: `H[X]` is `0` for a non-summable entropy series, and
  `condEntropy` is a Bochner integral, silently `0` when non-integrable. Under
  `dd:finite-range` neither can bite, but any generalization must carry both as proved
  consequences of its finiteness class.
- `SCOPE.md` §6 says `klDiv` is `EReal`-valued; at this pin it is `ℝ≥0∞`
  (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`). Corrected on this branch;
  the entropy-infrastructure owner should carry the same fix.
- The paper's `π` in a latent variable model goes `Λ → Ω` (latent space onto the base),
  while §3.1's morphisms go source → target with `π : Ω → Λ`. Do not conflate the two
  directions when reading Def 4.12 (morphisms `ρ_k : L̃_k → L_k`).
