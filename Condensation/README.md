# Condensation — trust surface

Formalization of Sam Eisenstat, *Condensation: A Theory of Concepts* (July 2025, 27 pp.).

There is **no arXiv ID**. The paper's public record is OpenReview `HwKFJ3odui`, with an
author copy at `https://sameisenstat.net/doc/condensation-25-07.pdf`. Both the PDF and a
`pdftotext -layout` extraction of it are committed here, as
[`notes/condensation-25-07.pdf`](notes/condensation-25-07.pdf) and
[`notes/condensation-25-07.txt`](notes/condensation-25-07.txt), so the specification
travels with the formalization. **The paper is the spec.** Unlike every other paper in
this repo, we do **not** have its TeX source; *Numbering and provenance* below says what
that costs and how the node checker is built around the gap.

Read this file for what is and is not claimed, [`KNOWLEDGE.md`](KNOWLEDGE.md) for the
correspondence table and the pitfalls log, and [`notes/roadmap.md`](notes/roadmap.md) for
the plan, the milestones, and the `dd:` glossary in full.

## What the paper is

A *random variable model* (Def 3.1) is a countable discrete probability space `Ω` of
finite entropy together with a finite family of random variables `X_i : Ω → R_i`, each of
countable discrete range. A *latent variable model* for it (Def 3.2) is a second random
variable model `(Λ, (Y_A)_{A ∈ P⁺I})` — its variables indexed by the **nonempty** subsets
of the index set `I` (Def 2.2) — together with a probability-preserving `π : Λ → Ω` such
that each pulled-back `π^* X_i` is almost everywhere a function of the latents that
*contribute* to `i`, that is of `Y_∋i = (Y_A : i ∈ A)`. The reading the paper is after:
`Y_A` is the part of a body of meaning that the observables indexed by `A` share, so a
latent variable model is a system of concepts rather than a single postulated parameter.
Def 3.3 grades such systems by three *scores* — simple `σ_L`, conditioned `χ_L`, and
reconstruction `ϱ_L` — all built from entropies of the latents; lower is better. §3.1 makes
random variable models into a category (Prop 3.7) whose morphisms refine both the
probability space and the ranges, characterizes its isomorphisms (Prop 3.8), and passes to
equality of morphisms almost everywhere and the induced notion of *equivalence*
(Def 3.9–3.10, Props 3.11–3.12).

§4 works in the exact case. Prop 4.2 gives the chain of lower bounds
`σ_L(A) ≥ χ_L(A) ≥ H(Y_∩A) ≥ H(X_A)`, and Def 4.3 calls `L` a *perfect condensation* of `M`
when `χ_L(A) = H(X_A)` for every `A ⊆ I` (and *simply-perfect* when `σ_L(A) = H(X_A)`) —
that is, when the bound is tight. Theorem 4.9 characterizes both: simple-perfection is
equivalent to each `Y_A` being a.e. a function of `X_i` for every `i ∈ A` together with
joint independence of the latents, and perfection is equivalent to the same functional
condition together with the *ordered Markov condition* of Def 4.8. Theorem 4.15, the
comparison theorem of §4, is the paper's first main result: if `L₁` and `L₂` both perfectly
condense the same `M`, then after amalgamating them over a common probability space `Λ₀`
(Defs 4.11–4.12, Lemma 4.13) each `Y_A` is almost everywhere a function of `Z_{⊇A}`, and
reciprocally each `Z_A` of `Y_{⊇A}` — two different systems of concepts for the same world
stand in a correspondence, each side's concepts recoverable from the other side's coarser
ones. §5 replaces the exact hypotheses with quantitative ones. Theorem 5.8 bounds
`H(Y_{⊇A} | Z_G)`, where `G = F°` is the *polar* (Def 5.5) of a family `F ⊆ P⁺I`, by a sum
of reconstruction-type terms `Σ_{B ∈ F} H(Y_{⊇A} | X_B)` plus conditional mutual
informations read off an *intersection tree* (Def 5.6, Prop 5.7) — each term depending on
only one of the two latent systems — with an accompanying exact identity, and Corollaries
5.9 and 5.10 specialize it. The upshot is that the §4 correspondence degrades gracefully:
approximate hypotheses buy an approximate correspondence rather than none.

## Status

**In progress — milestone M1. Statements for every in-scope node have landed; twenty
proofs are still `sorry`.**

This is not a completed formalization and must not be read as one. What that means
precisely, as of this commit:

* **Every in-scope node has a carrier.** 39 of the paper's 42 numbered nodes are cited by
  at least one annotated declaration. The three that are not are Examples 5.1–5.3, out of
  scope by the proposed ruling in *Open rulings* below. `scripts/check-condensation-nodes.py`
  reports the coverage per section.
* **Twenty proofs are `sorry`**, listed exhaustively below. **Sixteen annotated endpoints
  are not axiom-clean** — thirteen because their own proof is `sorry`, three because they
  consume one (Corollary 4.6 is fully proved but runs through Proposition 4.2's staged
  inequality; Lemma 4.13's two `canonical` constructions and their two existence statements
  run through three staged measure lemmas). Those sixteen are staged in `AxiomAudit.lean`'s
  `CONDENSATION-PENDING` block, which is pure comment and asserts nothing. Nothing outside
  that set depends on a `sorry`.
* **Everything not in that list is proved and axiom-checked.** `AxiomAudit.lean`'s
  `CONDENSATION-INVENTORY` block asserts that each listed endpoint uses no axiom beyond
  `propext`, `Classical.choice`, `Quot.sound`. That includes all of §2 (Proposition 2.5 and
  its converse, the equation-(2.2) pullback identities, the two symmetries of interaction
  information), all of Definitions 3.1–3.4, **all ten §3.1 endpoints** (Definitions 3.5,
  3.6, 3.9, 3.10 and Propositions 3.7, 3.8, 3.11, 3.12), and in §4/§5: Proposition 4.2's
  first and third inequalities, Definition 4.3, Lemma 4.5, Proposition 4.7, Definition 4.8,
  Definitions 4.11 and 4.12 as structures, Examples 4.1 and 4.4 as constructed models, and
  in §5 Lemma 5.4 in both forms, Definition 5.5's polar with its lattice facts, Definition
  5.6 and Proposition 5.7 in full, and Corollary 5.10's (5.24).
* **No `axiom` declarations are introduced at any milestone**, and none is.
* **No modeling substitutions.** As of 2026-08-17 the model class is Definition 3.1
  verbatim — including the "with finite entropy" clause on `Ω`, which this library did not
  carry at all before that date — and the disclosures list in
  [`KNOWLEDGE.md`](KNOWLEDGE.md) is empty. The one standing narrowing, `dd:finite-range`,
  is retired; *Modeling boundary* below says what it was and what replaced it. The two
  restrictions that remain are universe stratification (presentational, open ruling 3) and
  the Examples 5.1–5.3 scope ruling. What is *not* claimed is anything about the twenty
  `sorry`s: this section, not the modeling boundary, is where the incompleteness lives.

### The twenty `sorry`s, by file

`sorry` remains allowed and expected mid-flight under the repo standard (`../CLAUDE.md`,
load-bearing rule 3 — `sorry` is honest, an arithmetic stub standing in for content is
not). A ✱ marks a declaration that carries a `Paper node:` annotation, i.e. a claimed
endpoint of the paper rather than a supporting lemma.

Note that the table below lists `sorry` *sites*, while the `CONDENSATION-PENDING` block
lists *endpoints that are not axiom-clean* — a longer list, because an endpoint whose own
proof is complete still fails the axiom check if it consumes a staged one. The three that
differ are `LatentModel.aeFunctionOf_of_perfectlyCondenses` (Corollary 4.6, proved but
running through Proposition 4.2's staged inequality) and, in `Amalgamation.lean`,
`Amalgamation.canonical` / `nonempty_amalgamation` / `LatentAmalgamation.canonical` /
`nonempty_latentAmalgamation` (Lemma 4.13, whose three `sorry`s sit in supporting measure
lemmas rather than in the annotated declarations themselves).

| file | declaration | what is unproved |
|---|---|---|
| `Perfect.lean` | ✱ `LatentModel.condScore_ge_entropy_jointContrib` | **Proposition 4.2**, second inequality (4.7)–(4.9): `H(Y_∩A) ≤ χ_L(A)`. Needs a chain rule for a finite family along a linear extension of the inclusion order. |
| `Perfect.lean` | ✱ `RVModel.orderedMarkov_iff` | **Proposition 4.10** (4.38): the ordered Markov condition is equivalent to conditional independence of `Y_F`, `Y_G` given `Y_{F∩G}` for upward-closed `F`, `G`. Same linear-extension machinery. |
| `Perfect.lean` | ✱ `LatentModel.perfect_tfae_A` | **Theorem 4.9**, the (A1)–(A3) `TFAE`. |
| `Perfect.lean` | ✱ `LatentModel.perfect_tfae_B` | **Theorem 4.9**, the (B1) ⟺ (B2) equivalence. |
| `Amalgamation.lean` | `isProbabilityMeasure_canonicalMeasure` | the measure of (4.53) is a probability measure |
| `Amalgamation.lean` | `measurePreserving_fst` | `ρ₁` is probability preserving |
| `Amalgamation.lean` | `measurePreserving_snd` | `ρ₂` is probability preserving |
| `Comparison.lean` | ✱ `aeFunctionOf_of_condIndepFun` | **Lemma 4.14** |
| `Comparison.lean` | ✱ `aeFunctionOf_jointAbove_of_perfectlyCondenses` | **Theorem 4.15** — the induction the printed proof only gestures at (errata entry 5) |
| `Examples.lean` | `Example41.L₁_simpleScore` | equation (4.2) |
| `Examples.lean` | `Example41.L₁_condScore` | equation (4.3) |
| `Examples.lean` | `Example41.L₂_simpleScore` | equation (4.4) |
| `Examples.lean` | `Example41.L₂_condScore` | equation (4.5) |
| `Examples.lean` | `Example44.entropy_joint_eq` | equation (4.11) |
| `Examples.lean` | `Example44.simplyPerfectlyCondenses` | Example 4.4's conclusion |
| `Quantitative.lean` | ✱ `condEntropy_jointAbove_le` | **Theorem 5.8** (5.13), the inequality |
| `Quantitative.lean` | ✱ `condEntropy_jointAbove_eq` | **Theorem 5.8** (5.14), the exact identity |
| `Quantitative.lean` | ✱ `condEntropy_jointAbove_le_reconScore` | **Corollary 5.9** (5.21) |
| `Quantitative.lean` | ✱ `condEntropy_jointAbove_le_reconScore_of_orderedMarkov` | **Corollary 5.9** (5.22) |
| `Quantitative.lean` | ✱ `condEntropy_jointAbove_le_choose` | **Corollary 5.10** (5.25) |

Note the shared blocker: the §4 tranche (Proposition 4.2's second inequality, Proposition
4.10, both halves of Theorem 4.9) all run on the same missing piece of infrastructure — a
chain rule for a *finite family* of variables along a linear order. The vendored library
has only the two- and three-variable forms (`chain_rule`, `chain_rule'`, `chain_rule''`,
`cond_chain_rule`, `cond_chain_rule'`), and the linear order comes from
`Mathlib.Order.Extension.Linear` (`LinearExtension`, `toLinearExtension`), which is not in
the substrate's import closure and is imported explicitly by `Model.lean` for that reason.
Build that one chain rule and four of the ten claimed endpoints unblock together.

### Milestones

What each milestone gates, from [`notes/roadmap.md`](notes/roadmap.md):

| milestone | what it delivers | what it gates |
|---|---|---|
| **M0** (harness round 1) | `Probability.lean` (§2) and `Model.lean` (Defs 3.1–3.4) complete *statements*, definitions total, theorem bodies may be `sorry`; `Examples.lean` inhabitants for `RVModel` and `LatentModel`; wiring — `lean_lib Condensation`, a `scripts/papers.py` entry marked `in-progress`, `scripts/check-condensation-nodes.py`, the CI branch, the `CONDENSATION-INVENTORY` block in `AxiomAudit.lean`, this README, `KNOWLEDGE.md` | audit round 1 attacks **the core definitions only**. A wrong `RVModel` or `LatentModel` invalidates everything built on it, so it is audited before anything is built on it. **Landed**, with no `sorry` at all. |
| **M1** (round 2) | statements for §3.1, §4 and §5 in full (proofs may still be `sorry`); Examples 4.1 and 4.4 constructed | audit round 2 attacks **the theorem statements**. **Landed** — the twenty `sorry`s above are what "proofs may still be `sorry`" bought. |
| **M2+** | proofs: Props 4.2, 4.10, Thm 4.9 (the chain-rule tranche); Lemma 4.13 (the measure construction); Lemma 4.14 and Thm 4.15; Thm 5.8, Cors 5.9–5.10; equations (4.2)–(4.5) and (4.11) of the examples — then hardening rounds, with Aristotle offload for stalled goals | the point at which the paper's §4 and §5 theorems are claimed *proved*. |

Two corrections to that table as it stood when it was written. Proposition 2.5 was
scheduled for M2 and is in fact **proved at M0** — the determinism bridge turned out to be
the natural place to start, since §4 consumes it in both directions. And Propositions 4.5
and 4.7 were listed as M2 work; Lemma 4.5 and Proposition 4.7 are both **proved at M1**,
as are Proposition 4.2's first and third inequalities, Lemma 5.4, Proposition 5.7 and
Corollary 5.10's (5.24).

## Modeling boundary

### `dd:finite-range` — retired 2026-08-17

**Definition 3.1 is now carried verbatim, and there is no modeling substitution left in
this library.** A random variable model is a countable discrete probability space *with
finite entropy* (`[Countable Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure P]`
plus the field `finiteEntropy_Ω : ShannonInformation.FiniteEntropyMeasure P`) together
with a finite family of variables of countable discrete range and finite entropy
(`finiteEntropy_X : ∀ i, ShannonInformation.FiniteEntropyOf (X i) P`).

**What the state was, and when it changed.** Until 2026-08-17 every variable of a model
carried `FiniteRange` (finitely many *attained* values) and `Ω` carried no entropy
hypothesis at all. That was a genuine type-(c) narrowing — a geometric variable on `ℕ` is
countable-discrete with finite entropy and was excluded — and it was forced, because the
vendored PFR theorems are proved only in the finite-range fragment. It was disclosed here,
in `KNOWLEDGE.md`, in the roadmap, and at every model structure. It was costed on
2026-08-17 (`notes/finite-range-generalization-plan.md`: ~1,450–2,400 lines, 3–4.5 focused
weeks in four phases), ruled a desired endpoint by Anson the same day rather than deferred,
and retired the same day.

**What replaced it.** A FAF-authored finite-entropy layer, `ShannonInformation/FiniteEntropy/`,
proving the §2–§5 corpus this paper consumes — the chain rules, subadditivity, mutual- and
conditional-mutual-information nonnegativity, the independence characterizations, data
processing — at `ShannonInformation.FiniteEntropyOf` rather than `FiniteRange`. The consumer
migration then swapped `RVModel`'s finiteness field, added Definition 3.1's `Ω` clause, and
rebound the §2 substrate lemmas and the bare-variable lemmas of §5's Lemma 5.4 and §4's
Lemma 4.14. **No statement of any §3–§5 theorem changed, and the `sorry` count is unchanged
at twenty.** The one node whose *shape* changed is Proposition 2.5, which gained `Countable
R_Y` at the same time it lost `FiniteRange` (its `omit [Countable T] in` is gone, forced by
the `tsum` form of conditional entropy). Before, it was stronger than printed in one respect
and weaker in another, so it was not comparable as printed; now it is the printed statement.
The [`KNOWLEDGE.md`](KNOWLEDGE.md) correspondence table records this per declaration.

**The class genuinely grew, and there is a witness for it.** `Condensation.Example.geomModel`
is an `RVModel Unit` on `Ω = ℕ` with the `Geometric(1/2)` law and `X_() = id`, with
`geomModel_entropy : H(X_()) = 2 log 2` and `geomModel_not_finiteRange : ¬ FiniteRange
(geomModel.X ())`. It is a random variable model of this library today and was not
expressible before the swap; every other witness in `Examples.lean` lives on a finite sample
space and so cannot distinguish Definition 3.1's reading from the narrowed one. Per the
repo's non-vacuity discipline it is constructed, not asserted.

### The `dd:` design decisions

Mirrors the table in [`notes/roadmap.md`](notes/roadmap.md); the same glossary ships in
`Condensation.lean`, and each decision is tagged at its site.

| Tag | Decision | Why |
|---|---|---|
| `dd:finite-range` | **Retired 2026-08-17.** It read: every random variable of a model carries `FiniteRange`, and `Ω` carries no entropy hypothesis. It now reads: `finiteEntropy_Ω : ShannonInformation.FiniteEntropyMeasure P` and `finiteEntropy_X : ∀ i, ShannonInformation.FiniteEntropyOf (X i) P` — Definition 3.1 verbatim. The tag is kept in the glossary, marked retired, because older commits, the audit ledger and `notes/finite-range-generalization-plan.md` refer to it by name. | **See the callout above** for what the state was, what replaced it, and the witness (`Example.geomModel`) that shows the model class genuinely grew. No longer a narrowing, and no longer an open ruling. |
| `dd:pplus` | `P⁺I` is the subtype `PPlus I := {A : Finset I // A.Nonempty}`. Finiteness of the index type is carried by the model — `RVModel` takes `[Finite I]` as a class parameter (Def 3.1: *finite* family) — so no `Fintype`/`DecidableEq` data appears anywhere and `PPlus I` is exactly the paper's `P⁺I`. Subfamilies `F ⊆ P⁺I` are `Set (PPlus I)` (finite automatically), and the joint variable `Y_F` is `fun ω (B : F) => Y B ω`, a dependent product over the subtype `↥F` with `MeasurableSpace.pi`. | Faithful to Def 2.2 (nonempty subsets only, no phantom `Y_∅`); `Set` keeps upward-closure/polar/intersection algebra (§4.10, §5) as plain set algebra; finiteness of `↥F` is by instance. |
| `dd:bundled-model` | `RVModel (I : Type w) [Finite I]` bundles the sample space `Ω : Type u`, its σ-algebra/countability/singleton-class instances, the probability measure, the range family `R : I → Type v` with their instances, the variables `X i : Ω → R i`, their measurability and their finite entropy, plus Def 3.1's finite entropy of `Ω` itself; Def 3.1's *finite* family is the class parameter `[Finite I]`, not a field, so instance search finds it. `LatentModel M` bundles a `RVModel.{u', v', w} (PPlus I)` plus `π : Λ → Ω` (`MeasurePreserving`) plus the a.e.-function condition of Def 3.2, with the latent universes `u'`/`v'` **independent** of `M`'s. | Def 3.5–3.12 need models as objects of a category, and 3.2/4.12 need "two latent models with the same underlying space" — bundling with explicit `Ω`/`R` fields is what makes those statable. **`RVModel`'s `Type u`/`Type v` stratification is a disclosed narrowing** — see below. |
| `dd:ae-function` | "`Y` is a function of `X` almost everywhere" is `AEFunctionOf X Y P := ∃ f, Measurable f ∧ ∀ᵐ ω ∂P, Y ω = f (X ω)`; the everywhere version `FunctionOf` likewise without `∀ᵐ`. Measurability of `f` is kept in the definition (paper: "measurable function") and discharged by `measurable_of_countable` on countable discrete ranges. | Verbatim Def 2.1's fifth convention; the measurability conjunct is free in our setting but keeping it stops the definition drifting from the paper. |
| `dd:pullback` | Pullback `π^* X` is plain composition `X ∘ π`; probability-preserving = Mathlib `MeasureTheory.MeasurePreserving π P_Λ P_Ω`. Equation (2.2) invariance is `IdentDistrib`-based (`MeasurePreserving` gives `IdentDistrib (X ∘ π) X`). | Repo rule: never redefine what Mathlib has. |
| `dd:interaction` | Def 2.3's `I(X;Y;Z) := I[X : Y] − I[X : Y \| Z]` and its conditional form `I(X;Y;Z \| C) := I[X : Y \| C] − I[X : Y \| ⟨Z, C⟩]` (needed by Lemma 5.4 / Thm 5.8) are FAF-authored `def`s over the vendored `mutualInfo`/`condMutualInfo`; symmetry is a lemma. | The API deliberately adds no definitions; interaction information is paper-specific until a second client needs it. |
| `dd:tree` | Def 5.6's intersection tree is an inductive binary tree `ITree (M) := leaf (a : M) \| node (l r : ITree M)` with the label of a node *computed* as the meet of its children's labels; Prop 5.7 is stated as: any labeling of the tree's positions that agrees on leaves and satisfies (5.10) at every internal position equals the computed labeling. Leaves/internal vertices are lists of positions; Thm 5.8's "bijection between leaves and `{C : B∩C≠∅}_{B∈F}`" is `List.Nodup` + `toFinset = image`. | A directed rooted binary tree with unique paths to the root *is* an inductive binary tree; the (V,E,ℓ) presentation would import graph theory for no content. Recorded as a rendering, not a substitution; auditors should attack it if any §5 statement loses generality. |
| `dd:category` | Prop 3.7 is a `CategoryTheory.Category` instance on the bundled type of random variable models (objects `Σ I, RVModel I` at fixed universes); Prop 3.8 uses `CategoryTheory.IsIso`; Def 3.9's a.e.-equality is a relation on hom-types (a `Setoid`), 3.10–3.12 are stated over it. No `Bicategory`. | Follows the paper, which names the 2-category and declines to use it. |
| `dd:amalgamation` | Def 4.11's Λ₀ is the subtype `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with the discrete σ-algebra and the measure `∑' p, w p • dirac p`, `w (λ₁,λ₂) = P₁{λ₁} P₂{λ₂} / P_Ω{π₁ λ₁}` (0 when the denominator is 0) — the paper's (4.53) integral evaluated on a countable discrete space. | Same object; the sum form is what a countable-discrete Λ₀ means. |

### Universe stratification (`dd:bundled-model`), a second disclosed narrowing

`RVModel` fixes its sample space in `Type u` and its range family in `Type v`, and the
category instance of `dd:category` is taken at fixed universes. The paper quantifies over
probability spaces with no such stratification. Universe *lifting* can represent larger
presentations, so this is presentational rather than a cardinality bound — but it is a
restriction, it is the price of bundling models into objects of a category, and it is
recorded here and in [`KNOWLEDGE.md`](KNOWLEDGE.md) rather than left to be discovered in a
signature. It is likewise an **open ruling** (below).

**A latent model's universes are not pinned to its model's.** An earlier draft of
`LatentModel` required `Λ : Type u` and the latent ranges in `Type v` — the same universes
as `M` — and described that as a documented narrowing. It has been removed: the full
parameter list is `LatentModel.{u, v, w, u', v'}`, with `Λ : Type u'` and the latent ranges
in `Type v'`, unrelated to `M`'s. Nothing in the paper ties them, and the pin cost real
generality: Example 4.4 builds `M` out of `L` by setting `X_i := Y_∋i`, which puts the
*given* ranges in `Type (max v' w)` while the latents stay in `Type v'`, so under the pin
that example was statable only for pre-inflated latent universes. Unpinning costs an
explicit universe list at *existence* statements (`Nonempty (LatentModel.{u,v,w,u,v} M)`)
and nothing at all at the statement shape every §4/§5 theorem uses
(`{I} [Finite I] {M : RVModel I} (L : LatentModel M) …`); `Nonempty (RVModel.{u,v,w} I)`
already needed the same annotation, so this is not a new kind of friction.

## Scope

The paper numbers **42 nodes** on a single section-scoped counter shared across kinds,
running `Definition 2.1` … `Corollary 5.10`. By kind:

| kind | count | which |
|---|---|---|
| Definitions | 18 | 2.1, 2.2, 2.3, 2.4; 3.1–3.6, 3.9, 3.10; 4.3, 4.8, 4.11, 4.12; 5.5, 5.6 |
| Propositions | 9 | 2.5, 3.7, 3.8, 3.11, 3.12, 4.2, 4.7, 4.10, 5.7 |
| Lemmas | 4 | 4.5, 4.13, 4.14, 5.4 |
| Theorems | 3 | 4.9, 4.15, 5.8 |
| Corollaries | 3 | 4.6, 5.9, 5.10 |
| Examples | 5 | 4.1, 4.4, 5.1, 5.2, 5.3 |

18 + 9 + 4 + 3 + 3 + 5 = 42. This breakdown is not stated in the paper's own prose; it was
derived from the committed extraction. `scripts/check-condensation-nodes.py` hard-asserts
both the total of 42 **and each of the six per-kind counts** in that table, so a drift in
the extraction is a CI failure rather than a silent narrowing of the node set.

Per section, with the in-scope ruling — reproduced from
[`notes/roadmap.md`](notes/roadmap.md):

| § | Nodes | In scope? |
|---|---|---|
| 2 | Def 2.1 (random variable), 2.2 (`P⁺S`), 2.3 (`H`, `I`, interaction information), 2.4 (`G(Ω)`), Prop 2.5 (determinism bridge) | yes; 2.1 and 2.4 Mathlib-rendered (`Measurable`, `Measure.instMeasurableSpace`) with `Paper node:` on the alias/`abbrev` that names them |
| 3 | Def 3.1 (random variable model), 3.2 (latent variable model), 3.3 (scores σ, χ, ϱ), 3.4 (joint variables `X_A`, `Y_F`, `Y_∩A`, `Y_⊇A`, `Y_⊋A`, `Y_∋i`), 3.5 (morphism), 3.6 (composite), Prop 3.7 (category), 3.8 (iso characterization), Def 3.9 (a.e.-equal morphisms), 3.10 (equivalence), Prop 3.11 (congruence), 3.12 (equivalence is an equivalence relation) | yes, all |
| 4 | Ex 4.1, Prop 4.2, Def 4.3, Ex 4.4, Lemma 4.5, Cor 4.6, Prop 4.7, Def 4.8, Thm 4.9, Prop 4.10, Def 4.11, 4.12, Lemma 4.13, 4.14, Thm 4.15 | yes, all (examples 4.1/4.4 are constructive and double as non-vacuity witnesses) |
| 5 | Ex 5.1, 5.2, 5.3, Lemma 5.4, Def 5.5 (polar), 5.6 (intersection tree), Prop 5.7, Thm 5.8, Cor 5.9, 5.10 | 5.4–5.10 yes. **Ex 5.1–5.3 proposed OUT** (pending Anson's ruling): 5.1/5.2 posit `[0,1]`-valued latents `L`, outside the paper's own countable-discrete framework and only bucketed into it informally; 5.3 is a prose translation of structural causal models with no claim. Nothing downstream cites them. |

Everything else in the paper — equation (3.4)'s score aggregation, the 2-category remark
after Def 3.10, the (4.41) discussion — is unnumbered prose and gets no carrier.

### Open rulings

Two questions are open for Anson, and one is closed. Work proceeds under the stated
assumption in each open case; **neither of those is a settled ruling, and this file does
not present either as one.** If a ruling comes back the other way, the affected work is
redone.

1. ~~**`dd:finite-range`** as the standing type-(c) narrowing~~ — **CLOSED, 2026-08-17.**
   It was assumed yes; Anson ruled the other way, that the generalization was a desired
   endpoint to be pursued in parallel with the paper rather than deferred, and it landed
   the same day. `Condensation/` now carries Definition 3.1 verbatim. See the callout
   under *Modeling boundary*. Nothing here is waiting on this question.
2. **Examples 5.1–5.3 out of scope** — *assumed yes*, for the reason in the §5 row above:
   5.1 and 5.2 posit `[0,1]`-valued latents, outside the paper's own countable-discrete
   framework and only bucketed into it informally, and 5.3 is a prose translation of
   structural causal models with no claim. They are the only nodes proposed for exclusion,
   and nothing downstream cites them.
3. **Universe stratification** of `RVModel` (`Ω : Type u`, `R : I → Type v`) — *assumed
   acceptable* as a documented narrowing. The distinct question of whether a latent model
   must live in its model's universes is **not** open: it does not, as of the round-1 fix
   wave (see the callout above).

## File layout

Reproduced from [`notes/roadmap.md`](notes/roadmap.md). All of these files exist as of M1.
The import order is also the dependency order; two edges are worth naming because they were
settled by construction rather than by plan. `Perfect.lean` imports `Morphism.lean`, because
Proposition 4.7's clause (2) *is* Definition 3.10 — so §3.1 sits upstream of §4, not beside
it. And `Examples.lean` imports `Perfect.lean`, so the §3.1 witnesses (the concrete
morphisms, the category objects, the a.e.-equal-but-different-`f` pair) live at the end of
`Examples.lean`; putting them in `Morphism.lean` would close the cycle
`Morphism → Examples → Perfect → Morphism`.

| file | content | at M1 |
|---|---|---|
| `Probability.lean` | §2: `AEFunctionOf`/`FunctionOf`, pullback lemmas (2.2), `PPlus`, interaction information, Def 2.4 alias, **Prop 2.5** (`H[Y \| X] = 0 → AEFunctionOf X Y`) — proved over the vendored entropy, not the spike's | complete, no `sorry` |
| `Model.lean` | Def 3.1–3.4: `RVModel`, `LatentModel`, joint variables, the four `Y_∩A`/`Y_⊇A`/`Y_⊋A`/`Y_∋i` families plus `incomparable`, (3.9), scores σ/χ/ϱ, and the generic joint-variable / upward-closure lemmas §4 and §5 run on | complete, no `sorry` |
| `Morphism.lean` | §3.1: Def 3.5, 3.6, Prop 3.7, 3.8, Def 3.9, 3.10, Prop 3.11, 3.12 | complete, no `sorry` — all ten endpoints axiom-clean |
| `Perfect.lean` | §4: Prop 4.2, Def 4.3, Lemma 4.5, Cor 4.6, Prop 4.7, Def 4.8, **Thm 4.9**, Prop 4.10 | statements complete; 4 `sorry` |
| `Amalgamation.lean` | Def 4.11, 4.12, **Lemma 4.13** (the measure construction) | statements complete; 3 `sorry` |
| `Comparison.lean` | Lemma 4.14, **Thm 4.15** | statements complete; 2 `sorry` |
| `Quantitative.lean` | Lemma 5.4, Def 5.5, 5.6, Prop 5.7, **Thm 5.8**, Cor 5.9, 5.10 | statements complete; 5 `sorry` |
| `Examples.lean` | Ex 4.1, 4.4, inhabitants of every boundary structure, `LatentModel.nonempty`, and the §3.1 witnesses | constructions complete; 6 `sorry` (the score equations (4.2)–(4.5), (4.11) and Ex 4.4's conclusion) |
| `Condensation.lean` | aggregator + `dd:` glossary | imports all eight |
| `README.md`, `KNOWLEDGE.md`, `notes/paper-errata.md` | trust surface, institutional memory, errata | all three exist |

## Substrate: `ShannonInformation.API`

This library's entropy, conditional entropy, mutual information and conditional mutual
information all come from **one import**, `ShannonInformation.API` — FAF's shared,
paper-neutral Shannon layer, which is a vendored snapshot of the
[PFR project](https://github.com/teorth/pfr)'s information theory. Read
[`../ShannonInformation/README.md`](../ShannonInformation/README.md) and, before relying
on any entropy statement, [`../ShannonInformation/SCOPE.md`](../ShannonInformation/SCOPE.md).

Two standing rules, both inherited from that layer:

1. **Never name a `PFR.*` module from a Condensation file.** The vendor/consumer split
   exists so that re-pinning the vendored tree — a routine maintenance event — does not
   ripple into paper libraries. Go through `ShannonInformation.API`.
2. **Never `import Mathlib` wholesale in a Condensation file.** PFR's `Mathlib/` shim
   modules re-declare lemmas that FAF's newer Mathlib pin has since acquired upstream, and
   a file that imports all of Mathlib alongside this layer fails to elaborate
   (`import PFR.Mathlib.Probability.IdentDistrib failed, environment already contains
   'ProbabilityTheory.IdentDistrib.prodMk'`). Import the specific `Mathlib.*` modules you
   need.

And a third rule, new since 2026-08-17 and the one most likely to bite: **cite
`ShannonInformation.foo` by its full name, never bare.** The *vendored* theorems still hold
only in the finite-range fragment — the chain rules, `mutualInfo_nonneg`, the independence
characterizations, submodularity, data processing all carry a `FiniteRange` hypothesis that
is load-bearing in PFR's proof, not a typeclass artefact, and `SCOPE.md` §2 still records
that this is strictly narrower than countable-discrete-with-finite-entropy. What changed is
that this library no longer cites them for anything load-bearing. It cites the FAF-authored
`ShannonInformation.*` corpus in `ShannonInformation/FiniteEntropy/`, which proves the same
facts at `ShannonInformation.FiniteEntropyOf`. Both versions are reachable through the one
import, and with `ProbabilityTheory` open a bare lemma name resolves by elaboration success
rather than by namespace — so a bare citation can silently pick the narrow one and fail
several lines later with a missing `FiniteRange` instance. `ShannonInformation/API.lean`'s
module docstring carries the "which version to cite" table. Dot notation is the sharp case,
because opening a namespace cannot fix it: `h.condEntropy_eq_entropy` and
`hid.condEntropy_eq` resolve in the head symbol's namespace (`ProbabilityTheory.IndepFun`,
`ProbabilityTheory.IdentDistrib`) and so always find the vendored original. Write those two
out in full.

**No `FiniteRange` citation remains anywhere in `Condensation/`,** including the concrete
witnesses. The reason is worth knowing, because the obvious guess is wrong: one might expect
a witness built on `Bool × Bool` to keep citing the vendored lemmas, the range being finite.
It cannot. With `RVModel`'s finiteness field now `FiniteEntropyOf` there is no structure
instance for `FiniteRange (M.X i)`, and instance search will not unfold a concrete model to
rediscover that its range type happens to be a `Fintype`. `FiniteRange` survives in
`Condensation/` in exactly one statement, `Example.geomModel_not_finiteRange`, where it is
negated. A citation anywhere else is a finding.

`SCOPE.md` also flags a trap worth carrying while reading any statement here, and it is now
live rather than hypothetical: Lean's `∑'` is `0` on a non-summable family, so `H[X]` for an
infinite-entropy variable is silently `0` rather than `∞`, and `condEntropy` is a Bochner
integral, silently `0` when non-integrable. Under the old narrowing neither could bite. What
keeps them from biting now is that the finiteness class carries both as *proved consequences*
(`ShannonInformation.FiniteEntropyOf.summable`, `ShannonInformation.integrable_entropy_cond`)
rather than as side hypotheses on statements.

## Numbering and provenance

The paper numbers through a **single section-scoped LaTeX theorem counter shared by
`Definition`, `Proposition`, `Lemma`, `Theorem`, `Corollary` and `Example`**, so a node id
reads `<section>.<n>` — `Definition 3.4`, `Lemma 4.13`, `Theorem 5.8` — and the kinds
interleave in one sequence. No LaTeX labels are available to us, so the **printed number is
the provenance key**, as in `CartesianFrames/`, `ModalAgents/` and `FiniteFactoredSets/`.

**We have no TeX source.** That is the difference from every other paper here, and it
changes the shape of the checker. `scripts/check-modal-agents-nodes.py` and
`scripts/check-finite-factored-sets-nodes.py` *recompute* their papers' printed numbers by
emulating the LaTeX counters, so the node set is derived rather than transcribed. We cannot
do that. The committed *source* our checker reads is
[`notes/condensation-25-07.txt`](notes/condensation-25-07.txt), the `pdftotext -layout`
extraction of the committed PDF, and `scripts/check-condensation-nodes.py` reads the
**printed numbers directly off that extraction's header lines**. Because an extraction can
drift — a re-run under a different `poppler`, a reflowed header, a lost line break — the
checker **hard-asserts that exactly 42 nodes are found, with the per-kind counts of the
table above**. A drift that silently dropped a node would otherwise narrow the node set
without failing anything; instead it fails CI.

One quirk of the extraction to know before reading it or the checker: **`pdftotext` drops
the `fi` and `ff` ligatures**, so the committed text reads `Denition`, `nite`, `dierent`,
`sucient`. The header regex (in `scripts/paper_nodes.py`) therefore reads
`De(?:fi)?.?nition`, accepting the extraction's spelling and the plain one alike, rather
than `Definition`. This is a *tool* artifact and never a defect of the paper — do
not log one as an erratum. It has a sharp consequence for anyone writing code against the
extraction: what the extractor actually emits in place of a dropped ligature is the font's
own slot byte, `\x1c` for `fi`, and Python's `str.splitlines()` splits on `\x1c`/`\x1d`/`\x1e`
— so `splitlines()` over this file makes every `Definition` header disappear. Split on
`\n`.

The annotation contract is the repo's standard one, enforced fail-closed:

* every paper-facing `theorem` carries a final `Paper node:` docstring line naming the
  printed node;
* validity is checked **including the kind** — citing `Theorem 2.5` where the paper prints
  `Proposition 2.5` is a failure, and a line that parses to *no* node is itself a
  violation, so a typo cannot silently disable the check;
* the annotation must be the last line of a `/-- … -/` docstring on a **named**
  declaration (anonymous instances therefore cannot carry one; internal lemmas cite the
  paper in prose instead);
* **coverage, per declaration**: every annotated declaration is itself listed in
  `AxiomAudit.lean`'s `CONDENSATION-INVENTORY` block, matched on fully qualified names.
  Sharing a node with some other listed declaration is not enough — the annotation claims
  the node for *that* statement, so *that* statement is what gets axiom-checked. One
  in-progress concession, and it expires on its own: while *nothing* is annotated yet, an
  absent `CONDENSATION-INVENTORY` block is reported as a note rather than a failure, since
  there is no endpoint for it to protect. The block becomes mandatory with the first
  annotated declaration.

### The staged inventory (`CONDENSATION-PENDING`)

The coverage rule above collides with reaching the paper statement-first. At M1 sixteen
declarations carry a `Paper node:` annotation — their *statements* are final and are the
paper's real endpoints — while their proofs are not yet axiom-clean. Such a declaration
cannot be listed in `#assert_axioms_clean`: that command exists to catch exactly a
`sorryAx` dependency, so listing it would either fail the build or invite someone to weaken
the check. Dropping the annotation instead would be a lie about the statement's provenance,
and would also stop the node checker from guarding the statement.

So the annotated surface is split across two blocks in `AxiomAudit.lean`. The
`CONDENSATION-INVENTORY` block is the ordinary axiom gate. The `CONDENSATION-PENDING`
block that follows it is **pure Lean comment** — it compiles to nothing and asserts nothing
— and names, one per line with a reason, every annotated endpoint that is not yet
axiom-clean:

```
-- CONDENSATION-PENDING-BEGIN
-- Condensation.LatentModel.perfect_tfae_A   -- M2: Theorem 4.9 (A1)-(A3); same chain rule
-- CONDENSATION-PENDING-END
```

It is a declaration of intent, not a discharge, and the checker fences it so it buys
nothing else. `scripts/check-condensation-nodes.py` accepts an annotated declaration listed
in *either* block, and **fails** if:

* a name appears in **both** blocks — an endpoint is axiom-checked or proof-pending, never
  both, which is what stops one being quietly "proved" in one place while still excused in
  the other;
* a pending entry names **no annotated declaration** — a stale entry left behind when an
  endpoint is renamed or retired would otherwise sit there excusing nothing;
* a pending line is **malformed** — not a `--` comment, no declaration name, no reason, or
  a duplicate — so the block cannot degrade into a place to hide things;
* the block is **non-empty while `scripts/papers.py` registers the paper `completed`** —
  staging is a mid-flight device, and the gate arms itself the moment the registry says the
  paper is done.

A surviving non-empty block prints as a note (`note: 16 endpoints pending (sorry) — not
axiom-checked`), never as a violation. **Moving a name from the pending block into the
inventory block is what "M2 proved this endpoint" means**, and the two edits belong in the
same commit as the proof. The mechanism lives in `scripts/paper_nodes.py` as a generic
`pending_block` keyword argument, so any paper in this repo can opt into it; Condensation
is currently the only one that does.

Per the repo's surface-hygiene rule, `theorem` is reserved for paper-facing statements;
supporting results are `lemma` (or `private lemma`), and data-valued carriers are `def`s.

## Errata

Defects found in the printed paper while formalizing are recorded in
[`notes/paper-errata.md`](notes/paper-errata.md) — thirteen entries as of M1: a wrong
equation reference in Theorem 5.8's proof, an undefined symbol in Theorem 4.15's proof, a
leftover parameter name in Corollary 5.10, a dropped "almost everywhere" in Theorem 4.9,
and several citation and notation slips.

Four of the thirteen bite hard enough to change a Lean statement, and all four were found
by trying to write the statement down:

* **entry 10 — Definition 4.12 does not tie `π̃₁` to `π̃₂`.** Each `L̃ₖ` carries its own map
  to `Ω`, and the commuting square (4.43) that would relate them belongs to Definition
  4.11, which Definition 4.12 does not restate. Theorem 4.15's proof needs them to agree
  almost everywhere. Carried as the explicit field `LatentAmalgamation.comm`.
* **entry 11 — Example 4.1's (4.4) and (4.5) are false at `A = ∅`.** Both scores are then
  the empty sum `0` while the right-hand side is `H(X_I)`. The Lean statements take
  `A.Nonempty`.
* **entry 12 — Theorem 5.8 uses the `Z`-side contribution condition at (5.18) without
  listing it as a hypothesis.** Legitimate, because Definition 4.12 supplies it; the Lean
  statement quantifies over `LatentAmalgamation`, whose field `contributes₂` is where the
  licence actually lives.
* **entry 13 — Definition 5.6's "parents" are children under the usual convention.** Not an
  error, but it inverts the reading a formalizer brings to it, and it cost one wrong first
  draft here.

**Consult that file before concluding that a Lean statement or proof diverges from the
printed one**, because in several places the printed text is the thing that is wrong. This
is the same discipline as `CartesianFrames/notes/paper-errata.md`, and it exists because a
formalizer's first instinct on a mismatch is to assume the Lean is wrong.

## Non-vacuity discipline

Repo standard, and it applies here from M0 onward: **every boundary structure gets a
constructed inhabitant in `Examples.lean`, never a stand-in.** A hypothesis nobody has
exhibited a witness for is not a formalization, and a theorem whose antecedents are
unrealizable proves nothing.

What is actually constructed and proved at M0, so that no reader has to take the word
"witness" on trust:

| witness | what it is | what is *proved* about it |
|---|---|---|
| `coinModel` | `Ω = Bool` uniform, `I = Unit`, `X_() = id` | `coinModel_entropy : H(X_()) = log 2` and `coinModel_entropy_pos : 0 < H(X_())` — not the degenerate zero-entropy model |
| `coinLatent` | Example 4.1's `L₁` recipe over it: `Λ = Ω`, `π = id`, `Y_{()} = X_()` | `coinLatent_nonempty`; `coinLatent_reconScore : ϱ_L({()}) = 0` |
| `twoCoinLatent` | two indices (`I = Bool`), `P⁺I` of size 3, all latents equal to one fair coin | `σ_L({true}) = 2 log 2`, `χ_L({true}) = log 2`, hence `0 < χ_L < σ_L`; and `ϱ_L({true}) = 0` |
| `noisyLatent` | `I = Unit`, `Λ = Bool × Bool`, `π = fst`, `Y_{()} = id` — the latent keeps a bit that `π` throws away | `ϱ_L({()}) = log 2`, hence `0 < ϱ_L({()})`: the reconstruction score is **not** identically zero. Also `σ_L({()}) = χ_L({()}) = 2 log 2` |
| `LatentModel.ofJoint` / `.nonempty` | the tautological latent model `Y_A = X_A` of an arbitrary `M` | `Nonempty (LatentModel M)` for **every** random variable model `M` |
| `Example.geomModel` / `.geomLatent` (added 2026-08-17) | `I = Unit`, `Ω = ℕ` with the `Geometric(1/2)` law, `X_() = id : ℕ → ℕ`; `geomLatent` is `LatentModel.ofJoint geomModel` | `geomModel_entropy : H(X_()) = 2 log 2` (the textbook two bits) and `geomModel_not_finiteRange : ¬ FiniteRange (geomModel.X ())`. This is the witness that retiring `dd:finite-range` has content rather than being a re-spelling: every other witness here lives on a finite sample space and so cannot tell Definition 3.1's reading from the narrowed one. `geomLatent_reconScore = 0` for the same reason `coinLatent`'s does |

Two of those exist to correct a specific over-claim. An earlier draft of `Examples.lean`
asserted that *every* score is positive on the coin witness; that is false —
`coinLatent.reconScore {()} = 0`, and `ϱ_L(A) = H(Y_⊇A | X_A)` vanishes for any latent
system that the observables determine, which is precisely what a *perfect* reconstruction
is. `twoCoinLatent` is what shows `χ_L`'s conditioning doing work (the `Unit`-indexed
witness has nothing strictly above anything), and `noisyLatent` is what shows `ϱ_L` is not
identically zero.

The paper's own worked examples supply the rest at M1 — Example 4.1's two deliberately-bad
latent systems `L₁` (with `Y_{i} = X_i` and the other latents constant) and `L₂` (with
`Z_I = X_I` and the other latents constant), and Example 4.4's independent-latents model,
which *simply-perfectly* condenses the model built from it and so keeps Definition 4.3 and
Theorem 4.9 from being about an empty class. `coinLatent` follows `L₁`'s recipe but is not
yet annotated as Example 4.1: that annotation waits for the general statement, since with
`I = Unit` the `L₁` and `L₂` recipes coincide and prove nothing about the distinction the
example is making.
