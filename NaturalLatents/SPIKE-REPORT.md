# Spike: how hard is *Natural Latents* (Wentworth & Lorell, 2025)?

**Paper.** John Wentworth and David Lorell, *Natural Latents: Latent Variables Stable
Across Ontologies*, arXiv:2509.03780v1, 4 Sep 2025, math.PR, 15 pp. Two Bayesian agents
agree on a predictive distribution over observables but use different latents; under what
conditions is one agent's latent guaranteed to be a function of the other's? Answer: the
*natural latent* conditions — mediation plus redundancy — and these are shown to be both
sufficient and (absent further constraints) necessary, robustly to approximation.

**Verdict.** By far the smallest of the papers spiked here — **4 numbered nodes** — and
the mathematics is genuinely short. It is also the one where the *statements themselves*
are the problem.

> **Seven of the paper's roughly twelve mathematical items — including the statement of
> both theorems, both corollaries, and the entire proof of Theorem 1 — exist only as
> raster images.** Not TikZ. PNGs.

This is not an aesthetic complaint. It relocates the formalization's trust surface: a
reader cannot check a Lean statement against a printed formula, because there is no
printed formula. Transcription becomes the load-bearing step, and it is unreviewable by
the usual means.

---

## 1. The diagram problem, established as fact

The arXiv source (`natlats.tex`, 538 lines) was downloaded and inspected. Every
`\includegraphics` is a `.png`:

| paper item | how it is stated | file |
| --- | --- | --- |
| Mediation (definition) | figure only | `mediation.png` |
| Mediation with `ε` | figure only | `mediation_dkl.png` |
| Redundancy (definition) | figure only | `redund_basic.png` |
| **Theorem 1** (Mediator Determines Redund) | English gloss + figure | `fndmtl_statement.png` |
| **Corollary 1.1** (Naturality ⟹ Minimality) | *"Corollary is stated graphically"* + figure | `fndmtl_minimal_big.png` |
| **Corollary 1.2** (Naturality ⟹ Maximality) | *"Corollary is stated graphically"* + figure | `fndmtl_maximal_big.png` |
| **Theorem 2** (Guaranteed Translatability) | *"The theorem is stated graphically"* + figure | `theorem_2_2_var.png` |
| D.B. Lemma (statement) | figure only | `dangly.png` |
| **Proof of Theorem 1** | figure only (rotated 90°) | `better_fndmtl_thm.png` |

What *is* in text: the definition of "satisfies a diagram to within `ε`"
(`ε ≥ D_KL(P ‖ ∏ⱼ P[Yⱼ|Y_pa(j)])`), the derivation that `Y ← X → Y` reduces to
`ε ≥ H(Y|X)`, and the proofs of the Frankenstein rule, Factorization Transfer, the
Bookkeeping rule and the D.B. Lemma. So the *machinery* is textual; the *results* are
pictures.

Having read the figures, the content is legible and the proof is real — Figure 9 is a
five-step diagram rewrite (Marginalize → D.B. Lemma → D.B. Lemma → Marginalize) with
honest `ε` bookkeeping `ε_med → ε_med + ε_red → ε_med + 2ε_red`. This is not hand-waving.
But a formalization must *first* commit to a textual rendering of each diagram, and that
rendering is exactly what no reviewer can check against the paper.

**Recommendation if this is pursued:** produce a transcription document — every figure
redrawn as an explicit inequality over KL divergences — and get it confirmed by the
authors *before* writing Lean. That is cheap, it is the actual risk, and it is the sort of
thing authors are usually glad to check.

## 2. Two gaps found by reading

- **The proof of Theorem 1 uses a rule the paper never states.** Figure 9 invokes
  "Marginalize" twice. The paper's stated rules are the Frankenstein rule, Factorization
  Transfer, the Bookkeeping rule (Appendix A) and the D.B. Lemma (Appendix B).
  *Marginalize is not among them and is nowhere proved.* It is presumably "if `P[X,Y]`
  satisfies `G` to within `ε` then the marginal satisfies the marginalized graph to within
  `ε`", which should follow from the KL chain rule — but a formalization has to supply it,
  and it is load-bearing in the only proof the paper gives.

  Symmetrically, **Frankenstein and Bookkeeping are proved but never used** in any proof
  in the paper.

- **Theorem 2's approximate converse has no written `ε` accounting.** Theorem 2 is an
  `⟺` carrying `(ε_med' + 2ε_red')` on one side. The "only if" direction is argued in one
  sentence — *"follows trivially from considering either `Λ^B = X₁` or `Λ^B = X₂`"* — which
  is exact-case reasoning. In the approximate case the implied bookkeeping (what `ε` you
  recover for redundancy, given a determination bound) is not written down anywhere, in
  text or figure. This is where I would expect a formalization to find real work, or a
  defect.

## 3. Substrate fit — and a direct answer to an open question in the entropy PR

`ShannonInformation/SCOPE.md` (PR #1) had "Natural Latents: not assessed" as an
outstanding item. This spike closes it, and the answer is **no, not as written**:

- Theorems 1 and 2 are stated for generic `Λ`, `Λ'` with **no finiteness hypothesis**.
- The paper's own worked quantitative example (§IV B) assumes **a uniform prior on `Λ` over
  the interval `[0,1]`** — a continuous latent. That is outside not merely `FiniteRange`
  but discreteness altogether.

Two mitigations, both real:

- the quantities the example actually *computes* are finite-range — `N₁, N₂ ∈ {0,…,1000}`
  and `Λ' ∈ {0,1}`, and the reported `H = 0.058` bits is a finite sum — so a finite-range
  formalization would cover the theorems **as applied**, while excluding the
  continuous-latent modelling built around them;
- the paper's primitive is **KL divergence, not entropy**, and Mathlib's
  `InformationTheory.klDiv` is defined in full generality. Only the bridge
  `Y ← X → Y ⟺ ε ≥ H(Y|X)` lands in the entropy layer.

**Probed, not assumed:** `ShannonInformation.API` and
`Mathlib.InformationTheory.KullbackLeibler.Basic` co-import cleanly, and both NL
primitives are expressible side by side. One impedance mismatch to plan for: `klDiv` is
`EReal`-valued while PFR's entropy is `ℝ`-valued, so the bridge lemma will carry
finiteness side conditions.

`SCOPE.md` on the `entropy-infrastructure` branch has been updated with this finding.

## 4. What formalizing would actually require

| piece | status | estimate |
| --- | --- | --- |
| "satisfies a Bayes net to within `ε`" over KL | **new** — neither Mathlib nor PFR has it | 400–700 lines |
| Marginalize rule | **new, and missing from the paper** | 150–300 |
| Frankenstein, Factorization Transfer, Bookkeeping | textual proofs, chain-rule manipulation | 400–600 |
| D.B. Lemma | textual proof, four lines | 100–200 |
| KL ↔ entropy bridge (`ε ≥ H(Y\|X)`) | new; `EReal`/`ℝ` friction | 150–250 |
| Theorem 1 + Corollaries 1.1, 1.2 | five diagram rewrites once the calculus exists | 200–400 |
| Theorem 2 | + the unwritten converse bookkeeping | 200–400 |
| **Total** | | **1,600–2,850 lines** |

Smaller than Condensation, and much smaller than Finite Factored Sets. **The cost is
dominated by building the approximate-Bayes-net calculus, not by the theorems** — which
is a good sign, because that calculus is reusable and is arguably the paper's real
contribution.

Note what is *not* on this list: a d-separation library. NL never needs one — its
diagrams are used to assert factorizations, not to derive independences.

## 5. Recommendation

Worth doing, and cheap by this repository's standards, **but sequence it carefully**:

1. **Transcribe the nine figures into explicit inequalities and get the authors to confirm
   the transcription.** This is the whole risk. Everything downstream is ordinary work.
2. Ask about the two gaps in §2 at the same time — the missing Marginalize rule and the
   approximate converse's `ε` accounting. Both are the kind of thing that is a five-minute
   answer for an author and a week of guessing otherwise.
3. Build the approximate-Bayes-net calculus over Mathlib's `klDiv` as its own module —
   plausibly a second piece of shared infrastructure alongside `ShannonInformation`, since
   Condensation's §5 error terms want much the same vocabulary.
4. Only then state Theorems 1 and 2.

Provenance is the best of the three spiked papers: real arXiv ID, LaTeX source available,
`\newtheorem{theorem}{Theorem}` with `\newtheorem{corollary}{Corollary}[theorem]`, so
printed numbers are derivable — the `printed-counter` scheme already supported by
`scripts/papers.py`. The catch is that a node checker can verify *that* Theorem 1 is cited;
it cannot verify that the Lean statement matches a PNG.

---

*This is a feasibility spike, not a formalization. No Lean was committed on this branch:
the only probe run — that the entropy layer and Mathlib's KL divergence co-import — is
recorded in §3 and reproduced in the scope note of PR #1.*
