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

**In progress — milestone M0. Nothing is claimed proved.**

This is not a completed formalization and must not be read as one. At M0 the library
carries *statements*: definitions are total, but theorem bodies may be `sorry`, which is
allowed and expected mid-flight under the repo standard (`../CLAUDE.md`, load-bearing rule
3 — `sorry` is honest, an arithmetic stub standing in for content is not). No `axiom`
declarations are introduced at any milestone. When a milestone lands, this section is what
says so; until then, a statement's presence in this library is a claim about the
*statement*, not about a proof.

What each milestone gates, from [`notes/roadmap.md`](notes/roadmap.md):

| milestone | what it delivers | what it gates |
|---|---|---|
| **M0** (harness round 1) | `Probability.lean` (§2) and `Model.lean` (Defs 3.1–3.4) complete *statements*, definitions total, theorem bodies may be `sorry`; `Examples.lean` inhabitants for `RVModel` and `LatentModel`; wiring — `lean_lib Condensation`, a `scripts/papers.py` entry marked `in-progress`, `scripts/check-condensation-nodes.py`, the CI branch, the `CONDENSATION-INVENTORY` block in `AxiomAudit.lean`, this README, `KNOWLEDGE.md` | audit round 1 attacks **the core definitions only**. A wrong `RVModel` or `LatentModel` invalidates everything built on it, so it is audited before anything is built on it. |
| **M1** (round 2) | statements for §3.1, §4 and §5 in full (proofs may still be `sorry`); Examples 4.1 and 4.4 constructed | audit round 2 attacks **the theorem statements**. |
| **M2+** | proofs: Prop 2.5, 4.2, 4.5–4.7, 4.9, 4.10 (the chain-rule tranche); Lemma 4.13 (the measure construction); 4.14 and 4.15; Lemma 5.4, Prop 5.7, Thm 5.8, Cors 5.9–5.10 — then hardening rounds, with Aristotle offload for stalled goals | the first point at which any theorem of this paper is claimed *proved*. |

At the time of writing, M0 is being assembled and not every artifact in its row is in
place yet; the file layout table below marks what exists.

## Modeling boundary

### `dd:finite-range` — the standing type-(c) narrowing

**Learn this here rather than from a `variable` block.** The decision, in the roadmap's
words:

> Every random variable of a model carries `FiniteRange` (finitely many attained values),
> on a countable discrete sample space (`Countable Ω`, `MeasurableSingletonClass Ω`,
> `IsProbabilityMeasure P`). The paper's "countable discrete range with finite entropy"
> and "probability space with finite entropy" become: countable-discrete range types
> (`Countable`, `MeasurableSingletonClass`), finite range per variable, and **no**
> hypothesis on the entropy of `Ω` itself.

and the reason, likewise verbatim:

> The vendored entropy library proves its theorems only in the finite-range fragment
> (`ShannonInformation/SCOPE.md`); generalizing it is new mathematics (summability
> arguments), out of this paper's scope. Finite range implies finite entropy, so every
> quantity in the paper is finite as required. This is a genuine (c)-type narrowing — a
> geometric variable on `ℕ` is countable-discrete with finite entropy and is excluded —
> and is disclosed at the statement level (every model structure), in `README.md`, and
> here. Ω's own finite entropy is used by the paper only to make the variables' entropies
> finite, which finite range already does.

Two consequences to state flatly, because they are what a reader is owed:

* **What is excluded.** A random variable with countably infinite attained range and finite
  entropy — the standard example is a geometric variable on `ℕ` — satisfies the paper's
  hypotheses and does **not** satisfy ours. Every §4 and §5 statement in this library is
  therefore narrower than printed. The restriction is on the *variables*, not on the value
  types: `X : Ω → ℕ` attaining finitely many values is fine.
* **What Ω carries.** The paper assumes the probability space itself has finite entropy;
  we assume `Countable Ω`, `MeasurableSingletonClass Ω`, `IsProbabilityMeasure P` and
  **nothing about the entropy of `Ω`**. That is a *dropped* hypothesis rather than a
  narrowing, and it is sound only because the paper uses `Ω`'s finite entropy solely to
  make the variables' entropies finite, which per-variable finite range already delivers.
  If some argument turns out to need finite `H(Ω)` for its own sake, that is a finding,
  not a detail.

This decision is an **open ruling** (see *Open rulings* below): work proceeds under the
assumption that Anson accepts it, because the alternative is generalizing the vendored
entropy library — months of work outside this paper.

### The `dd:` design decisions

Mirrors the table in [`notes/roadmap.md`](notes/roadmap.md); the same glossary ships in
`Condensation.lean`, and each decision is tagged at its site.

| Tag | Decision | Why |
|---|---|---|
| `dd:finite-range` | Every random variable of a model carries `FiniteRange` (finitely many attained values), on a countable discrete sample space (`Countable Ω`, `MeasurableSingletonClass Ω`, `IsProbabilityMeasure P`). The paper's "countable discrete range with finite entropy" and "probability space with finite entropy" become: countable-discrete range types (`Countable`, `MeasurableSingletonClass`), finite range per variable, and **no** hypothesis on the entropy of `Ω` itself. | **See the callout above** — this is the standing type-(c) narrowing, disclosed there in full, with the roadmap's reason quoted verbatim. |
| `dd:pplus` | `P⁺I` is the subtype `PPlus I := {A : Finset I // A.Nonempty}`; `I` carries `[Fintype I] [DecidableEq I]` (Def 3.1: *finite* family). Subfamilies `F ⊆ P⁺I` are `Set (PPlus I)` (finite automatically), and the joint variable `Y_F` is `fun ω (B : F) => Y B ω`, a dependent product over the subtype `↥F` with `MeasurableSpace.pi`. | Faithful to Def 2.2 (nonempty subsets only, no phantom `Y_∅`); `Set` keeps upward-closure/polar/intersection algebra (§4.10, §5) as plain set algebra; finiteness of `↥F` is by instance. |
| `dd:bundled-model` | `RVModel I` bundles the sample space `Ω : Type u`, its σ-algebra/countability/singleton-class instances, the probability measure, the range family `R : I → Type v` with their instances, the variables `X i : Ω → R i`, their measurability and finite range. `LatentModel M` bundles a `RVModel (PPlus I)` plus `π : Λ → Ω` (`MeasurePreserving`) plus the a.e.-function condition of Def 3.2. | Def 3.5–3.12 need models as objects of a category, and 3.2/4.12 need "two latent models with the same underlying space" — bundling with explicit `Ω`/`R` fields is what makes those statable. **Universe pins (`Type u`, `Type v`) are a disclosed narrowing** — see below. |
| `dd:ae-function` | "`Y` is a function of `X` almost everywhere" is `AEFunctionOf X Y P := ∃ f, Measurable f ∧ ∀ᵐ ω ∂P, Y ω = f (X ω)`; the everywhere version `FunctionOf` likewise without `∀ᵐ`. Measurability of `f` is kept in the definition (paper: "measurable function") and discharged by `measurable_of_countable` on countable discrete ranges. | Verbatim Def 2.1's fifth convention; the measurability conjunct is free in our setting but keeping it stops the definition drifting from the paper. |
| `dd:pullback` | Pullback `π^* X` is plain composition `X ∘ π`; probability-preserving = Mathlib `MeasureTheory.MeasurePreserving π P_Λ P_Ω`. Equation (2.2) invariance is `IdentDistrib`-based (`MeasurePreserving` gives `IdentDistrib (X ∘ π) X`). | Repo rule: never redefine what Mathlib has. |
| `dd:interaction` | Def 2.3's `I(X;Y;Z) := I[X : Y] − I[X : Y \| Z]` and its conditional form `I(X;Y;Z \| C) := I[X : Y \| C] − I[X : Y \| ⟨Z, C⟩]` (needed by Lemma 5.4 / Thm 5.8) are FAF-authored `def`s over the vendored `mutualInfo`/`condMutualInfo`; symmetry is a lemma. | The API deliberately adds no definitions; interaction information is paper-specific until a second client needs it. |
| `dd:tree` | Def 5.6's intersection tree is an inductive binary tree `ITree (M) := leaf (a : M) \| node (l r : ITree M)` with the label of a node *computed* as the meet of its children's labels; Prop 5.7 is stated as: any labeling of the tree's positions that agrees on leaves and satisfies (5.10) at every internal position equals the computed labeling. Leaves/internal vertices are lists of positions; Thm 5.8's "bijection between leaves and `{C : B∩C≠∅}_{B∈F}`" is `List.Nodup` + `toFinset = image`. | A directed rooted binary tree with unique paths to the root *is* an inductive binary tree; the (V,E,ℓ) presentation would import graph theory for no content. Recorded as a rendering, not a substitution; auditors should attack it if any §5 statement loses generality. |
| `dd:category` | Prop 3.7 is a `CategoryTheory.Category` instance on the bundled type of random variable models (objects `Σ I, RVModel I` at fixed universes); Prop 3.8 uses `CategoryTheory.IsIso`; Def 3.9's a.e.-equality is a relation on hom-types (a `Setoid`), 3.10–3.12 are stated over it. No `Bicategory`. | Follows the paper, which names the 2-category and declines to use it. |
| `dd:amalgamation` | Def 4.11's Λ₀ is the subtype `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with the discrete σ-algebra and the measure `∑' p, w p • dirac p`, `w (λ₁,λ₂) = P₁{λ₁} P₂{λ₂} / P_Ω{π₁ λ₁}` (0 when the denominator is 0) — the paper's (4.53) integral evaluated on a countable discrete space. | Same object; the sum form is what a countable-discrete Λ₀ means. |

### Universe pinning (`dd:bundled-model`), a second disclosed narrowing

`RVModel` fixes its sample space in `Type u` and its range family in `Type v`, and the
category instance of `dd:category` is taken at fixed universes. The paper quantifies over
probability spaces with no such stratification. Universe *lifting* can represent larger
presentations, so this is presentational rather than a cardinality bound — but it is a
restriction, it is the price of bundling models into objects of a category, and it is
recorded here and in [`KNOWLEDGE.md`](KNOWLEDGE.md) rather than left to be discovered in a
signature. It is likewise an **open ruling** (below).

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

Three questions are open for Anson. Work proceeds under the stated assumption in each
case; **none of these is a settled ruling, and this file does not present any of them as
one.** If a ruling comes back the other way, the affected work is redone.

1. **`dd:finite-range`** as the standing type-(c) narrowing — *assumed yes*. The
   alternative is generalizing the vendored entropy library, months of work outside this
   paper.
2. **Examples 5.1–5.3 out of scope** — *assumed yes*, for the reason in the §5 row above:
   5.1 and 5.2 posit `[0,1]`-valued latents, outside the paper's own countable-discrete
   framework and only bucketed into it informally, and 5.3 is a prose translation of
   structural causal models with no claim. They are the only nodes proposed for exclusion,
   and nothing downstream cites them.
3. **Universe pinning** of `RVModel` (`Ω : Type u`, `R : I → Type v`) — *assumed
   acceptable* as a documented narrowing.

## File layout

Reproduced from [`notes/roadmap.md`](notes/roadmap.md). **Most of these files do not exist
yet at M0** — the last column says which are landing now and which are M1/M2 work. That is
also why the file names below are not links.

| file | content | at M0 |
|---|---|---|
| `Probability.lean` | §2: `AEFunctionOf`/`FunctionOf`, pullback lemmas (2.2), `PPlus`, interaction information, Def 2.4 alias, **Prop 2.5** (`H[Y \| X] = 0 → AEFunctionOf X Y`) — proved over the vendored entropy, not the spike's | statements land |
| `Model.lean` | Def 3.1–3.4: `RVModel`, `LatentModel`, joint variables, the four `Y_∩A`/`Y_⊇A`/`Y_⊋A`/`Y_∋i` families, (3.9), scores σ/χ/ϱ | statements land |
| `Morphism.lean` | §3.1: Def 3.5, 3.6, Prop 3.7, 3.8, Def 3.9, 3.10, Prop 3.11, 3.12 | not yet — M1 |
| `Perfect.lean` | §4: Prop 4.2, Def 4.3, Lemma 4.5, Cor 4.6, Prop 4.7, Def 4.8, **Thm 4.9**, Prop 4.10 | not yet — M1 |
| `Amalgamation.lean` | Def 4.11, 4.12, **Lemma 4.13** (the measure construction) | not yet — M1 |
| `Comparison.lean` | Lemma 4.14, **Thm 4.15** | not yet — M1 |
| `Quantitative.lean` | Lemma 5.4, Def 5.5, 5.6, Prop 5.7, **Thm 5.8**, Cor 5.9, 5.10 | not yet — M1 |
| `Examples.lean` | Ex 4.1, 4.4 + inhabitants of every boundary structure | `RVModel`/`LatentModel` inhabitants land; Ex 4.1/4.4 at M1 |
| `Condensation.lean` | aggregator + `dd:` glossary | lands |
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

And the fact that makes `dd:finite-range` necessary rather than convenient: **the vendored
theorems hold only in the finite-range fragment.** The *definitions* there are correct for
any countable-discrete variable, but every statement with content — the chain rules,
`mutualInfo_nonneg`, the independence characterizations, submodularity, data processing —
carries a `FiniteRange` hypothesis that is load-bearing *in the proof*, not a typeclass
artefact. `SCOPE.md` §2 records that this is strictly narrower than
countable-discrete-with-finite-entropy, and its §6 assesses this very paper: the generality
it states is not covered, its substance is. That is exactly what `dd:finite-range`
discloses. `SCOPE.md` also flags one sharp trap worth carrying while reading any statement
here: Lean's `∑'` is `0` on a non-summable family, so `H[X]` for an infinite-entropy
variable is silently `0` rather than `∞`.

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

Per the repo's surface-hygiene rule, `theorem` is reserved for paper-facing statements;
supporting results are `lemma` (or `private lemma`), and data-valued carriers are `def`s.

## Errata

Defects found in the printed paper while formalizing are recorded in
[`notes/paper-errata.md`](notes/paper-errata.md): a wrong equation reference in Theorem
5.8's proof, an undefined symbol in Theorem 4.15's proof, a leftover parameter name in
Corollary 5.10, a dropped "almost everywhere" in Theorem 4.9, and several citation and
notation slips.

**Consult that file before concluding that a Lean statement or proof diverges from the
printed one**, because in several places the printed text is the thing that is wrong. This
is the same discipline as `CartesianFrames/notes/paper-errata.md`, and it exists because a
formalizer's first instinct on a mismatch is to assume the Lean is wrong.

## Non-vacuity discipline

Repo standard, and it applies here from M0 onward: **every boundary structure gets a
constructed inhabitant in `Examples.lean`, never a stand-in.** `RVModel` and `LatentModel`
get theirs at M0; the paper's own worked examples supply the rest — Example 4.1's two
deliberately-bad latent systems `L₁` (with `Y_{i} = X_i` and the other latents constant)
and `L₂` (with `Z_I = X_I` and the other latents constant), and Example 4.4's
independent-latents model, which *simply-perfectly* condenses the model built from it and
so keeps Definition 4.3 and Theorem 4.9 from being about an empty class. A hypothesis
nobody has exhibited a witness for is not a formalization, and a theorem whose antecedents
are unrealizable proves nothing.
