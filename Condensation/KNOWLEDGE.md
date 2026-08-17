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
- `P I` written for `P⁺ I` in Lemma 4.5(2) and Cor 4.6.

## Pitfalls

- `pdftotext` drops `fi`/`ff` ligatures: the committed extraction reads `Denition`,
  `nite`, `dierent`. The node checker's regex allows `De.?nition`.
- The paper's `π` in a latent variable model goes `Λ → Ω` (latent space onto the base),
  while §3.1's morphisms go source → target with `π : Ω → Λ`. Do not conflate the two
  directions when reading Def 4.12 (morphisms `ρ_k : L̃_k → L_k`).
