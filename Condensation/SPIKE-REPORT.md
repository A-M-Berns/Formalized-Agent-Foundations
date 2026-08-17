# Spike: how hard is *Condensation: A Theory of Concepts* (Eisenstat, 2025)?

**Paper.** Sam Eisenstat, *Condensation: A Theory of Concepts*, July 2025, 27 pp.
Latent-variable models indexed by the nonempty power set of an index set, scored by
entropy; the main results (Theorem 4.15, Theorem 5.8) say that two good "condensations"
of the same data put their latent variables into correspondence — an intersubjectivity
theorem. Cites Factored Space Models (arXiv:2412.02579) as a neighbouring framework and
is adjacent to Wentworth–Lorell natural latents.

**Verdict.** This is the hardest of the three papers spiked so far, and the difficulty is
almost entirely *substrate*, not theorems. 42 numbered nodes, of which the mathematical
content is a dozen entropy inequalities plus a category-theoretic §3 and one
measure-construction lemma. **The blocker is that the entire paper is written in a
vocabulary Mathlib does not have.**

Artifacts:

- `Condensation/Spike.lean` — 255 lines, **compiles, zero `sorry`**, axioms clean. Builds
  a finite entropy layer from scratch and proves the paper's Proposition 2.5 (the
  determinism bridge), plus §5's polar combinatorics.
- `Condensation/spike-build.sh` — compiles against the parent checkout's oleans.

---

## 1. The blocker: Mathlib has no Shannon entropy

Checked exhaustively against the pinned Mathlib (`fabf563a`, toolchain v4.31.0):

- `Mathlib/InformationTheory/` contains exactly **`Coding/`, `Hamming.lean`,
  `KullbackLeibler/`**.
- No `H[X]`, no `condEntropy`, no `mutualInfo`, no `condMutualInfo`. Grepping for the
  `H[·]` notation and for any `def *entropy*` returns only **topological** entropy in
  `Mathlib/Dynamics/TopologicalEntropy/`, which is unrelated.

The paper needs, on essentially every page: `H(X)`, `H(X | Y)`, `I(X; Y)`, `I(X; Y | Z)`,
the three-way interaction information `I(X; Y; Z) = I(X;Y) − I(X;Y|Z)` (Definition 2.3),
the chain rule over an arbitrary linear extension of a partial order, subadditivity,
monotonicity, nonnegativity of conditional mutual information, the equivalence
"conditional independence ⟺ `I(·;·|·) = 0`", and invariance of all of it under pullback
along measure-preserving maps (equation 2.2).

None of that exists. It has to come from somewhere.

## 2. Where it exists: PFR — and what vendoring would cost

It *is* Lean-ed elsewhere. The [PFR project](https://github.com/teorth/pfr) (Tao et al.,
polynomial Freiman–Ruzsa) built the Shannon entropy library precisely because Mathlib
lacked it. Hard numbers, fetched from `master`:

| PFR file | lines | needed for Condensation? |
|---|---|---|
| `PFR/ForMathlib/Entropy/Measure.lean` | 816 | yes — measure entropy `Hm[μ]` |
| `PFR/ForMathlib/Entropy/Basic.lean` | 1199 | **yes** — `H[X]`, `H[X\|Y]`, `I[X:Y]`, `I[X:Y\|Z]`, chain rules |
| `PFR/ForMathlib/Entropy/Kernel/Basic.lean` | 431 | yes — `Basic.lean` is built on it |
| `PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean` | 408 | yes |
| `PFR/ForMathlib/Entropy/Group.lean` | 274 | no — additive-group specific |
| `PFR/ForMathlib/Entropy/{Kernel/,}RuzsaDist*.lean` | 393 + … | no — Ruzsa distance is PFR-specific |
| `PFR/Mathlib/Probability/IdentDistrib.lean` | 377 | shim |
| `PFR/Mathlib/Probability/ConditionalProbability.lean` | 30 | shim |

So the **relevant vendorable core is roughly 2,850–3,300 lines**, plus shims, minus the
additive-combinatorics tail. The `ForMathlib/` naming is a genuine advantage: those files
were written to be extracted and upstreamed, so they are not entangled with PFR's main
argument.

**Three things to know before counting on this.**

1. **Toolchain gap.** PFR is on `leanprover/lean4:v4.34.0-rc1`; this repo is pinned at
   **v4.31.0** by Foundation, and `lakefile.lean` documents why that pin is load-bearing
   (it is the last upstream commit that still contains `Foundation.Modal`, which
   `ModalAgents` is stated over). So vendoring PFR entropy means either back-porting
   across three toolchain versions, or moving the Foundation pin — which the lakefile
   already flags as "a scoped follow-up, not part of routine bumping". **This is the first
   thing to test, and it is a real risk, not a formality.**
2. **It is not upstream yet and may not be soon.** As of the October 2025 Mathlib
   probability survey, only the *definition* of KL divergence had been ported; entropy
   "and other divergences have not yet been the object of pull requests". So there is no
   near-term "just wait for Mathlib" option.
3. **PFR's entropy is measure-theoretic**, over `Measure Ω` with kernels and
   `FiniteRange` side conditions. Condensation only ever needs the countable-discrete
   finite-entropy case. Vendoring buys correctness and completeness at the cost of
   carrying measure-theoretic hypotheses through every statement in a paper that never
   needs them.

**The paper itself is not formalized anywhere** — searched; nothing exists.

## 3. What the spike established

`Condensation/Spike.lean` builds a finite discrete entropy layer from nothing and proves
**Proposition 2.5**, the bridge

> `H(X | Y) = 0` ⟺ `X` is almost everywhere a function of `Y`

which is what converts every entropy inequality in §4 into the paper's "is a function of"
conclusions (Lemma 4.5, Corollary 4.6, Theorem 4.9, Theorem 4.15). If that bridge were
expensive, the paper would be.

It is not. The whole thing reduces to one elementary lemma Mathlib lacks —

> `negMulLog (∑ tᵢ) ≤ ∑ negMulLog tᵢ` for nonnegative `t`, with equality iff at most one
> summand is nonzero

— proved in ~15 lines from `t i ≤ ∑ t j ⟹ log (t i) ≤ log (∑ t j)`. **No concavity, no
Jensen, no Gibbs.** Everything else (`H_pair_ge`, `H_pair_eq_iff`) follows by summing it
over the fibres of `Y`.

**Honest caveat, and it matters:** I deliberately probed the piece that needs no convexity.
**Subadditivity** — `H(X,Y) ≤ H(X) + H(Y)`, which Theorem 4.9's proof (equation 4.25) leans
on directly — does need Gibbs / the log-sum inequality, and I did **not** probe it. Mathlib
has `Real.negMulLog` with concavity and has Gibbs' inequality for KL divergence, so the
ingredients are there, but the cost is unmeasured. Do not read the cheapness of §3 as a
claim about the whole library.

§5's combinatorial layer *is* free: Definition 5.5's polar, its upward-closedness (which
is what Theorem 5.8's intersection tree ranges over), and its antitonicity are pure
`Set` manipulation, a few lines each.

## 4. Difficulty by section

**§2 (5 nodes) — background.** Definitions 2.1–2.4 are conventions; Definition 2.4 (the
Giry-style σ-algebra on `G(Ω)`) is used only in Lemma 4.13. Proposition 2.5 is done.
Low.

**§3 (12 nodes) — the category.** Morphisms of random variable models (3.5), composition
(3.6), category (3.7), isomorphism characterization (3.8), a.e.-equality (3.9),
equivalence (3.10), congruence (3.11), equivalence-is-an-equivalence (3.12). Mathlib's
`CategoryTheory` can host this, but "morphisms up to almost-everywhere equality" means
the hom-sets carry a `Setoid` — the paper says it is a strict 2-category and then
declines to use 2-categorical language. **Recommend following the paper: build the
category, prove 3.11 as a plain congruence lemma, and do not import `Bicategory`.**
Medium-low, ~700–1000 lines, mostly bookkeeping.

**§4 (15 nodes) — perfect condensation.** The mathematical heart. Once entropy exists,
Propositions 4.2, 4.7, 4.10, Lemma 4.5, Corollary 4.6, and Theorem 4.9 are chain-rule
manipulations over linear extensions of the inclusion order on `P⁺I` — routine given the
substrate, voluminous in Lean because every `Y_F` is a joint variable over a *subfamily*
and the index-set algebra (`F ∩ G`, `F ∪ G`, upward-closed, `Y_⊇A`, `Y_⊋A`, `Y_∩A`) is
constant. **This is the same dependent-family friction as the Factored Space Models
paper, and the `Finset.piecewise` trick from that spike does not transfer** — there the
subsets indexed sample-space factors; here they index random variables, so `Y_F` is
genuinely a dependent product over a subtype.

Two harder items:
- **Lemma 4.13 (amalgamation)** constructs a measure on the fibre product by integrating
  a product of conditional distributions, with Tonelli. In the countable discrete setting
  this is a sum rather than an integral, which helps a great deal, but conditional
  distributions, the fibre product, and measure-preservation of both projections are all
  real work. ~300–500 lines.
- **Theorem 4.15's proof is genuinely compressed.** It says "we will apply Lemma 4.14
  repeatedly, using induction" and then asserts `⋂_{i∈A} F_i = {B : B ⊇ A}` — but **`F_i`
  is never defined** anywhere in the paper. It evidently means `F_i = {B : i ∈ B}`. The
  induction is not set up; formalizing has to supply it (intersect the `|A|` upward-closed
  sets pairwise, invoking Proposition 4.10 for the conditional-independence side condition
  at each step). Expect this one node to cost more than its half-page suggests.

**§5 (10 nodes) — quantitative comparison.** Lemma 5.4 is an information-diagram identity
plus two nonnegativity steps — easy given the substrate. Definitions 5.5/5.6 and
Proposition 5.7 (intersection trees) are combinatorics; the binary-tree induction is
`Tree`-shaped and Mathlib-friendly. **Theorem 5.8** is the same induction as 4.15 but
carrying error terms, and Corollaries 5.9/5.10 are specializations. Medium.

## 5. Errata found while reading

- **Theorem 5.8's proof, after establishing (5.14):** "Equation (5.14) follows by a
  term-by-term comparison." Should be **(5.13)** — (5.14) was just proved on the previous
  line.
- **Theorem 4.15's proof** uses `F_i` without defining it (see above). Substantive, not
  cosmetic: it is the only place the induction is specified.
- **Corollary 5.10** states `G = {C ⊆ I : C contains at least all but n − 1 elements of
  A}`, but the corollary's parameter is `k`, not `n`; `n` is left over from the §5.2 prose.
- **Theorem 4.9 (B2)** says "the latent variable `Y_A` is a function of `X_i`", dropping
  the "almost everywhere" that the parallel clause (A2) carries. In an a.e. framework that
  is a slip, and a formalization must pick one.
- **Lemma 4.5's proof** cites "Corollary 2.5"; 2.5 is a Proposition.
- **Corollary 4.6's proof** cites only Proposition 4.2, but the argument also needs
  Lemma 4.5 (4.2 gives `H(Y_∩A) = H(X_A)`; 4.5 turns that into the function conclusion).
- `P I` is written for `P⁺ I` in Lemma 4.5(2) and Corollary 4.6.

None of these threaten the results; all of them are things a formalization would have to
resolve, and they are worth sending to the author.

## 6. Provenance — better than the Demski paper

The paper is hosted at `sameisenstat.net/doc/condensation-25-07.pdf` and has an
**OpenReview record** (`openreview.net/forum?id=HwKFJ3odui`), so it is citable and
locatable. Still no arXiv ID and no LaTeX source in hand; this repo's node checkers
recompute printed numbers from a committed `.tex`, so the source is still an ask —
but OpenReview submissions often include it, which is worth checking before emailing.

Numbering scheme: a **single shared section-scoped counter** (`Definition 2.1`,
`Proposition 2.5`, `Definition 3.1`, … `Corollary 5.10`), same family as ModalAgents.
42 numbered nodes: 18 definitions, 12 propositions, 4 lemmas, 2 theorems, 1 corollary… by
kind: Definitions 18, Propositions 8, Lemmas 4, Theorems 2, Corollaries 3, Examples 5,
plus §2's four conventions. Every node is numbered, which is better than Cartesian Frames
or Finite Factored Sets.

## 7. Estimate

| Tranche | Lines | Risk |
|---|---|---|
| Entropy substrate — **vendor PFR** | ~3,000 vendored + integration | **high** (toolchain) |
| Entropy substrate — **build bespoke discrete** | 1,200–2,000 | medium (subadditivity unprobed) |
| §2 conventions + Prop 2.5 | 300 | low — done |
| §3 category | 700–1,000 | medium-low |
| §4 perfect condensation | 1,500–2,200 | medium (4.13, 4.15) |
| §5 quantitative comparison | 800–1,200 | medium |
| **Total (excl. substrate)** | **3,300–4,700** | |

With the substrate, this is comfortably the **largest of the three papers spiked** —
plausibly comparable to FiniteFactoredSets in total effort, and with a genuine external
dependency that the other two do not have.

## 8. Recommendation

**Do the substrate decision first, and do it as a one-day experiment, before anything
else.** Specifically: try to build PFR's `ForMathlib/Entropy/{Measure,Basic}.lean` and
`Kernel/{Basic,MutualInfo}.lean` against this repo's pinned toolchain. That single
experiment determines the shape of the whole project:

- **If it ports cleanly** (or the Foundation pin can move without disturbing
  `ModalAgents`), vendor it. Rule 2b in `CLAUDE.md` — *search before you prove* — points
  hard this way, and re-deriving submodularity and the chain rules by hand to save a
  dependency would be exactly the duplicated-work failure that rule exists to prevent.
- **If it does not port**, build the bespoke finite-discrete layer. My probe is evidence
  that the discrete case is much cheaper than PFR's generality — the determinism bridge
  came out of one elementary lemma — but measure the subadditivity/Gibbs step before
  committing to a number, since I did not.

Either way, vendored entropy would be a **shared asset**, not Condensation-specific: it is
the same substrate any future information-theoretic agent-foundations paper needs, natural
latents included. That materially changes the cost/benefit — it is the first spike here
where the substrate is worth building even if the paper is deferred.

Send the §5 errata to Eisenstat, and ask for the LaTeX source at the same time.

---

Sources consulted for the vendoring question:
[teorth/pfr](https://github.com/teorth/pfr) ·
[PFR blueprint, Shannon entropy inequalities](https://teorth.github.io/pfr/blueprint/sect0002.html) ·
[Tao, "Formalizing the proof of PFR in Lean4 using Blueprint"](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/) ·
[Degenne, "Markov kernels in Mathlib's probability library"](https://arxiv.org/html/2510.04070v1) ·
[Condensation on OpenReview](https://openreview.net/forum?id=HwKFJ3odui) ·
[Condensation (author's copy)](https://www.sameisenstat.net/doc/condensation-25-07.pdf)
