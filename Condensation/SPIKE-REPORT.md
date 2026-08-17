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

**The paper itself is not formalized anywhere** — searched; nothing exists.

## 2a. The vendoring experiment — RUN, and it works

The first version of this report flagged the toolchain gap (PFR on `v4.34.0-rc1`, this
repo pinned at **v4.31.0** by Foundation) as the top risk and said to test it before
anything else. **That experiment has now been run, and the risk evaporated.**

**Key move: don't port from PFR `master`.** PFR was itself on `v4.31.0` — this repo's exact
toolchain — from `38e9417` (2026-06-16) to `b56e834^` (2026-07-03). Vendor from the last
such commit, **`01c9b666945eaf73b3f7d8b20ffe003f8640e630`** (2026-06-27), and the
three-toolchain-version gap does not exist at all. That revision pins Mathlib `e1d1de3b`
against our `fabf563a` (the v4.31.0 release tag) — same toolchain, weeks of drift.

### Result

| measure | value |
|---|---|
| PFR-internal modules in the entropy import closure | **25** |
| lines vendored | **6,074** |
| modules compiling against *this repo's* Mathlib | **25 / 25** |
| genuine porting edits required | **2** |
| `sorry` in the vendored closure | **0** |
| full closure build time | **~41 s** |

The two edits, in full:

1. **`ForMathlib/Entropy/Measure.lean`** — a `positivity` tactic extension for
   `measureMutualInfo` fails to elaborate: `PositivityExt.eval`'s `pα?` argument changed
   from `Option _` to `Q(PartialOrder $α)`. **Deleted** (~20 lines). Pure tactic plumbing;
   `measureMutualInfo_nonneg` itself is untouched and nothing downstream needs `positivity`
   to know about `Im[μ]`.
2. **`ForMathlib/Entropy/Kernel/Basic.lean:211`**, in `entropy_prodMkLeft_unit` —
   `rw [← MeasurableEquiv.map_symm]` does not fire because in our Mathlib that lemma is
   stated *applied to a measure* (`μ.map ⇑e.symm = μ.comap ⇑e`) while the goal is an
   equality of the *functions* `Measure.map` / `Measure.comap`. **Fixed by inserting
   `funext ν`** — three lines.

That is the entire cost. Everything else — the 948-line kernel disintegration shim, the
independence and `IdentDistrib` shims, `Uniform`, `ConditionalIndependence`,
`FiniteRange` — compiled untouched on the first attempt.

**Correction to the earlier estimate in this report:** I had put the vendorable core at
~2,850 lines by counting only the four entropy files. The true import closure is
**6,074 lines across 25 modules** — the `PFR/Mathlib/` shim layer is bigger than the
entropy library itself. The good news is that none of it needed work.

### And it is usable, not merely compilable

Compiling is necessary but not sufficient. `Condensation/VendorSmokeTest.lean` proves
**Lemma 5.4 of *Condensation*** — the quantitative core of its §5 — directly against the
vendored library, in both the exact form (5.6) and the inequality form (5.5):

```
H(X | C) = H(X | Y₁,C) + H(X | Y₂,C) − H(X | Y₁,Y₂,C) + I(Y₁; Y₂; X | C)
H(X | C) ≤ H(X | Y₁,C) + H(X | Y₂,C) + I(Y₁; Y₂; X | C)
```

The paper calls its own proof of (5.6) "a straightforward if unenlightening calculation".
Against the vendored substrate it is `rw [condMutualInfo_eq', condMutualInfo_eq']; ring`.
Both are axiom-clean (`propext, Classical.choice, Quot.sound`). Definition 2.3's
interaction information is a one-line `def` over PFR's `condMutualInfo`.

That is a paper result, not a restatement of a PFR lemma, and it is the strongest evidence
available that the API fits this paper.

### Reproducing

```
Condensation/vendor-pfr.sh                                        # 25/25, ~40 s
Condensation/vendor-build.sh Condensation/VendorSmokeTest.lean    # Lemma 5.4
```

`vendor-pfr.sh` clones PFR, checks out `01c9b66`, computes the import closure
(`vendor-closure.py`), applies both patches, and compiles the closure against the parent
checkout's oleans. **The vendored source is deliberately not committed** — it is
third-party (Apache-2.0) and the script regenerates it exactly.

### What is still true, and what changed

- Still true: entropy is **not upstream in Mathlib** and had no open PRs as of the
  October 2025 probability survey, so there is no near-term "wait for Mathlib" option.
- Still true: **PFR's entropy is measure-theoretic**, over `Measure Ω` with kernels and
  `FiniteRange`/`MeasurableSingletonClass` side conditions. Condensation only needs the
  countable-discrete case, so every statement will carry hypotheses the paper never
  mentions. The smoke test shows this is livable — four typeclass blocks in the `variable`
  line — but it is a real, permanent ergonomic tax, and it should be disclosed as a
  modeling decision rather than discovered later.
- **Changed:** the Foundation pin does not have to move. That was the thing that made this
  look expensive, and it is simply not a problem if you vendor from the v4.31.0 window
  rather than from `master`.
- **New risk, small:** vendoring from a June 2026 PFR commit means the vendored copy is
  frozen at that revision. Any future toolchain bump of this repo re-opens the port —
  though the evidence here (two edits across three toolchain versions' worth of drift,
  both mechanical) suggests that cost is low and roughly linear.

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
| Entropy substrate — **vendor PFR @ `01c9b66`** | 6,074 vendored, **2 edits** | **low — measured** |
| §2 conventions + Prop 2.5 | 300 | low — done |
| §3 category | 700–1,000 | medium-low |
| §4 perfect condensation | 1,500–2,200 | medium (4.13, 4.15) |
| §5 quantitative comparison | 800–1,200 | medium — Lemma 5.4 already proved |
| **Total new Lean to write** | **3,300–4,700** | |

The substrate line was the whole risk, and the experiment retired it. What remains is
**3,300–4,700 lines of ordinary work** on a vendored foundation that builds in 40 seconds
and has no `sorry` in it.

## 8. Recommendation

**Vendor PFR's entropy closure from commit `01c9b66`.** This is no longer a judgement
call — it was tested. 25/25 modules compile against this repo's pinned Mathlib after two
mechanical edits, neither of which touches mathematics, and the resulting API proves a real
Condensation lemma in three tactics. Rule 2b in `CLAUDE.md` — *search before you prove* —
points the same way: re-deriving submodularity, the chain rules, and kernel disintegration
by hand to avoid a dependency would be exactly the duplicated-work failure that rule exists
to prevent.

Concretely, for whoever picks this up:

1. Add the vendored closure as a `lean_lib` with its own directory and a README recording
   the upstream commit, the Apache-2.0 licence, and the two patches — the same treatment
   `lakefile.lean` already gives the vendored `ProvabilityLogic` subset, which is the
   established precedent in this repo for exactly this situation.
2. Register the patches as a diff against `01c9b66` so they can be audited and re-applied
   on any future bump.
3. Disclose the measure-theoretic setting as a modeling decision (`dd:measure-entropy`):
   the paper says "countable discrete with finite entropy", the substrate says
   `Measure Ω` + `MeasurableSingletonClass` + `FiniteRange`. These agree, but the Lean
   statements will carry hypotheses the paper does not write, and a reader must be told
   that up front rather than inferring it from a `variable` block.

And note the strategic point, now backed by a working build: vendored entropy is a
**shared asset**, not Condensation-specific. It is the substrate any future
information-theoretic agent-foundations paper needs — natural latents included. It is
worth landing even if Condensation itself is deferred.

Send the §5 errata to Eisenstat, and ask for the LaTeX source at the same time.

---

Sources consulted for the vendoring question:
[teorth/pfr](https://github.com/teorth/pfr) ·
[PFR blueprint, Shannon entropy inequalities](https://teorth.github.io/pfr/blueprint/sect0002.html) ·
[Tao, "Formalizing the proof of PFR in Lean4 using Blueprint"](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/) ·
[Degenne, "Markov kernels in Mathlib's probability library"](https://arxiv.org/html/2510.04070v1) ·
[Condensation on OpenReview](https://openreview.net/forum?id=HwKFJ3odui) ·
[Condensation (author's copy)](https://www.sameisenstat.net/doc/condensation-25-07.pdf)
