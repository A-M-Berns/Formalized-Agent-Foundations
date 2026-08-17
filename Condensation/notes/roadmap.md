# Condensation — formalization roadmap

**Paper.** Sam Eisenstat, *Condensation: A Theory of Concepts*, July 2025 (27 pp.,
`notes/condensation-25-07.pdf`; OpenReview `HwKFJ3odui`; no arXiv ID, no TeX source in
hand — `notes/condensation-25-07.txt` is the `pdftotext -layout` extraction and is the
committed *source* the node checker reads; ligatures `fi`/`ff` are dropped by the
extractor, so `Definition` reads `Denition` there).

**Substrate.** `ShannonInformation.API` (vendored PFR entropy, branch
`entropy-infrastructure`, onto which this branch is rebased). This paper never names a
`PFR.*` module and never `import Mathlib` wholesale (see `ShannonInformation/README.md`).
The feasibility spike (`SPIKE-REPORT.md`) is retained as history; `Spike.lean`,
`VendorSmokeTest.lean` and the `vendor-*.sh` scripts are superseded by the shared layer
and are removed in the M0 commit.

## Scope — 42 numbered nodes

Single section-scoped counter shared across kinds (`Definition 2.1 … Corollary 5.10`).

| § | Nodes | In scope? |
|---|---|---|
| 2 | Def 2.1 (random variable), 2.2 (`P⁺S`), 2.3 (`H`, `I`, interaction information), 2.4 (`G(Ω)`), Prop 2.5 (determinism bridge) | yes; 2.1 and 2.4 Mathlib-rendered (`Measurable`, `Measure.instMeasurableSpace`) with `Paper node:` on the alias/`abbrev` that names them |
| 3 | Def 3.1 (random variable model), 3.2 (latent variable model), 3.3 (scores σ, χ, ϱ), 3.4 (joint variables `X_A`, `Y_F`, `Y_∩A`, `Y_⊇A`, `Y_⊋A`, `Y_∋i`), 3.5 (morphism), 3.6 (composite), Prop 3.7 (category), 3.8 (iso characterization), Def 3.9 (a.e.-equal morphisms), 3.10 (equivalence), Prop 3.11 (congruence), 3.12 (equivalence is an equivalence relation) | yes, all |
| 4 | Ex 4.1, Prop 4.2, Def 4.3, Ex 4.4, Lemma 4.5, Cor 4.6, Prop 4.7, Def 4.8, Thm 4.9, Prop 4.10, Def 4.11, 4.12, Lemma 4.13, 4.14, Thm 4.15 | yes, all (examples 4.1/4.4 are constructive and double as non-vacuity witnesses) |
| 5 | Ex 5.1, 5.2, 5.3, Lemma 5.4, Def 5.5 (polar), 5.6 (intersection tree), Prop 5.7, Thm 5.8, Cor 5.9, 5.10 | 5.4–5.10 yes. **Ex 5.1–5.3 proposed OUT** (pending Anson's ruling): 5.1/5.2 posit `[0,1]`-valued latents `L`, outside the paper's own countable-discrete framework and only bucketed into it informally; 5.3 is a prose translation of structural causal models with no claim. Nothing downstream cites them. |

Everything else in the paper (eq. 3.4 aggregation, the 2-category remark after 3.10,
the (4.41) discussion) is unnumbered prose and gets no carrier.

## Standing design decisions (`dd:` glossary — mirrored in `Condensation.lean`)

| Tag | Decision | Why |
|---|---|---|
| `dd:finite-range` | Every random variable of a model carries `FiniteRange` (finitely many attained values), on a countable discrete sample space (`Countable Ω`, `MeasurableSingletonClass Ω`, `IsProbabilityMeasure P`). The paper's "countable discrete range with finite entropy" and "probability space with finite entropy" become: countable-discrete range types (`Countable`, `MeasurableSingletonClass`), finite range per variable, and **no** hypothesis on the entropy of `Ω` itself. | The vendored entropy library proves its theorems only in the finite-range fragment (`ShannonInformation/SCOPE.md`); generalizing it is new mathematics (summability arguments), out of this paper's scope. Finite range implies finite entropy, so every quantity in the paper is finite as required. This is a genuine (c)-type narrowing — a geometric variable on `ℕ` is countable-discrete with finite entropy and is excluded — and is disclosed at the statement level (every model structure), in `README.md`, and here. Ω's own finite entropy is used by the paper only to make the variables' entropies finite, which finite range already does. |
| `dd:pplus` | `P⁺I` is the subtype `PPlus I := {A : Finset I // A.Nonempty}`. The index type's finiteness is carried by the *model* — `RVModel` takes `[Finite I]` as a class parameter (Def 3.1: *finite* family) — so `PPlus I` is the paper's `P⁺I` (every subset of a finite set is finite) and no `Fintype`/`DecidableEq` data appears anywhere. Subfamilies `F ⊆ P⁺I` are `Set (PPlus I)` (finite automatically, from `instFiniteFinset` → `PPlus.instFinite` → `Subtype.finite`), and the joint variable `Y_F` is `fun ω (B : F) => Y B ω`, a dependent product over the subtype `↥F` with `MeasurableSpace.pi`. | Faithful to Def 2.2 (nonempty subsets only, no phantom `Y_∅`); `Set` keeps upward-closure/polar/intersection algebra (§4.10, §5) as plain set algebra; finiteness of `↥F` is by instance. Mathlib has `Finset.fintype` for `[Fintype α]` but no `Finite (Finset α)` at this pin, so `Condensation.instFiniteFinset` supplies it. |
| `dd:bundled-model` | `RVModel (I : Type w) [Finite I]` bundles the sample space `Ω : Type u`, its σ-algebra/countability/singleton-class instances, the probability measure, the range family `R : I → Type v` with their instances, the variables `X i : Ω → R i`, their measurability and finite range; Def 3.1's *finite* family is the class parameter `[Finite I]`, not a field. `LatentModel M` bundles a `RVModel.{u', v', w} (PPlus I)` plus `π : Λ → Ω` (`MeasurePreserving`) plus the a.e.-function condition of Def 3.2, with the latent universes `u' v'` **independent** of `M`'s. | Def 3.5–3.12 need models as objects of a category, and 3.2/4.12 need "two latent models with the same underlying space" — bundling with explicit `Ω`/`R` fields is what makes those statable. `[Finite I]` must be a parameter, not a field: `Finite I` does not mention the model, so a field would never be found by instance search and a score over `I = ℕ` would elaborate with every sum silently empty. Independent latent universes are what makes Ex 4.4 (`X_i := Y_∋i`, given ranges in `Type (max v' w)`) statable in its printed generality; the cost is that existence statements name universes explicitly (`Nonempty (LatentModel.{u,v,w,u,v} M)`), exactly as `Nonempty (RVModel.{u,v,w} I)` already must. `RVModel`'s own `Type u`/`Type v` stratification is recorded as a disclosed narrowing in KNOWLEDGE. |
| `dd:ae-function` | "`Y` is a function of `X` almost everywhere" is `AEFunctionOf X Y P := ∃ f, Measurable f ∧ ∀ᵐ ω ∂P, Y ω = f (X ω)`; the everywhere version `FunctionOf` likewise without `∀ᵐ`. Measurability of `f` is kept in the definition (paper: "measurable function") and discharged by `measurable_of_countable` on countable discrete ranges. | Verbatim Def 2.1's fifth convention; the measurability conjunct is free in our setting but keeping it stops the definition drifting from the paper. |
| `dd:pullback` | Pullback `π^* X` is plain composition `X ∘ π`; probability-preserving = Mathlib `MeasureTheory.MeasurePreserving π P_Λ P_Ω`. Equation (2.2) invariance is `IdentDistrib`-based (`MeasurePreserving` gives `IdentDistrib (X ∘ π) X`). | Repo rule: never redefine what Mathlib has. |
| `dd:interaction` | Def 2.3's `I(X;Y;Z) := I[X : Y] − I[X : Y | Z]` and its conditional form `I(X;Y;Z | C) := I[X : Y | C] − I[X : Y | ⟨Z, C⟩]` (needed by Lemma 5.4 / Thm 5.8) are FAF-authored `def`s over the vendored `mutualInfo`/`condMutualInfo`; symmetry is a lemma. | The API deliberately adds no definitions; interaction information is paper-specific until a second client needs it. |
| `dd:tree` | Def 5.6's intersection tree is an inductive binary tree `ITree (M) := leaf (a : M) \| node (l r : ITree M)` with the label of a node *computed* as the meet of its children's labels; Prop 5.7 is stated as: any labeling of the tree's positions that agrees on leaves and satisfies (5.10) at every internal position equals the computed labeling. Leaves/internal vertices are lists of positions; Thm 5.8's "bijection between leaves and `{C : B∩C≠∅}_{B∈F}`" is `List.Nodup` + `toFinset = image`. | A directed rooted binary tree with unique paths to the root *is* an inductive binary tree; the (V,E,ℓ) presentation would import graph theory for no content. Recorded as a rendering, not a substitution; auditors should attack it if any §5 statement loses generality. |
| `dd:category` | Prop 3.7 is a `CategoryTheory.Category` instance on the bundled type of random variable models (objects `Σ I, RVModel I` at fixed universes); Prop 3.8 uses `CategoryTheory.IsIso`; Def 3.9's a.e.-equality is a relation on hom-types (a `Setoid`), 3.10–3.12 are stated over it. No `Bicategory`. | Follows the paper, which names the 2-category and declines to use it. |
| `dd:amalgamation` | Def 4.11's Λ₀ is the subtype `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with the discrete σ-algebra and the measure `∑' p, w p • dirac p`, `w (λ₁,λ₂) = P₁{λ₁} P₂{λ₂} / P_Ω{π₁ λ₁}` (0 when the denominator is 0) — the paper's (4.53) integral evaluated on a countable discrete space. | Same object; the sum form is what a countable-discrete Λ₀ means. |

Non-vacuity discipline (repo standard): every boundary structure gets a constructed
inhabitant in `Examples.lean` (Ex 4.1's `L₁`, `L₂`; Ex 4.4's independent-latents model),
never a stand-in.

## File layout (`Condensation/`)

| file | content |
|---|---|
| `Probability.lean` | §2: `AEFunctionOf`/`FunctionOf`, pullback lemmas (2.2), `PPlus`, interaction information, Def 2.4 alias, **Prop 2.5** (`H[Y \| X] = 0 → AEFunctionOf X Y`) — proved over the vendored entropy, not the spike's |
| `Model.lean` | Def 3.1–3.4: `RVModel`, `LatentModel`, joint variables, the four `Y_∩A`/`Y_⊇A`/`Y_⊋A`/`Y_∋i` families plus `incomparable`, (3.9), scores σ/χ/ϱ, and the generic joint-variable / upward-closure lemmas §4 and §5 run on |
| `Morphism.lean` | §3.1: Def 3.5, 3.6, Prop 3.7, 3.8, Def 3.9, 3.10, Prop 3.11, 3.12 |
| `Perfect.lean` | §4: Prop 4.2, Def 4.3, Lemma 4.5, Cor 4.6, Prop 4.7, Def 4.8, **Thm 4.9**, Prop 4.10 |
| `Amalgamation.lean` | Def 4.11, 4.12, **Lemma 4.13** (the measure construction) |
| `Comparison.lean` | Lemma 4.14, **Thm 4.15** |
| `Quantitative.lean` | Lemma 5.4, Def 5.5, 5.6, Prop 5.7, **Thm 5.8**, Cor 5.9, 5.10 |
| `Examples.lean` | Ex 4.1, 4.4 + inhabitants of every boundary structure, including the §3.1 witnesses (which cannot live in `Morphism.lean`: `Perfect.lean` imports it, so a witness there would close a cycle) |
| `Condensation.lean` | aggregator + `dd:` glossary |
| `README.md`, `KNOWLEDGE.md`, `notes/paper-errata.md` | trust surface, institutional memory, errata |

## Milestones (harness rounds)

- **M0 (round 1 target)** — `Probability.lean` + `Model.lean` complete *statements* (defs
  total; theorem bodies may be `sorry`), Examples inhabitants for `RVModel`/`LatentModel`,
  wiring: `lean_lib Condensation`, `scripts/papers.py` entry (`in-progress`), node checker
  `scripts/check-condensation-nodes.py` (printed numbers read from the committed
  extraction), CI branch, `AxiomAudit.lean` CONDENSATION-INVENTORY block, README,
  KNOWLEDGE. **Audit round 1 attacks the core definitions only** — a wrong `RVModel` or
  `LatentModel` invalidates everything after it, so it is audited before anything is
  built on it.
- **M1 (round 2)** — statements for §3.1, §4, §5 in full (proofs may be `sorry`), Ex
  4.1/4.4 constructed. Audit round 2 attacks the theorem statements. **Landed**: all 39
  in-scope nodes have carriers, twenty proofs are `sorry`, and sixteen annotated endpoints
  are staged in `AxiomAudit.lean`'s `CONDENSATION-PENDING` block. §3.1 came out complete —
  all ten endpoints are proved and axiom-clean — as did Lemma 4.5, Prop 4.7, Lemma 5.4,
  Prop 5.7 and Cor 5.10's (5.24).
- **M2+** — proofs: Prop 4.2's second inequality, Prop 4.10 and both halves of Thm 4.9
  (one tranche: they share a single missing piece of infrastructure, a chain rule for a
  *finite family* along a linear extension of the inclusion order — build it once and four
  endpoints unblock together); Lemma 4.13
  (measure construction); 4.14, 4.15; Lemma 5.4, 5.7, 5.8–5.10; then hardening rounds.
  Aristotle offload for stalled goals.

## Open rulings for Anson (work proceeds under the stated assumption)

1. `dd:finite-range` as the standing type-(c) narrowing (assumed yes — the alternative is
   generalizing the vendored entropy library, months of work outside this paper).
2. Examples 5.1–5.3 out of scope (assumed yes).
3. Universe *stratification* of `RVModel` (`Ω : Type u`, `R : I → Type v`) — assumed
   acceptable as a documented narrowing. (The separate question of *pinning* `LatentModel`
   to `M`'s universes was settled in round 1: it is not pinned. See KNOWLEDGE
   design-decisions.)

## Paper errata (running list; see `notes/paper-errata.md` once created)

Carried over from the spike: Thm 5.8 proof "(5.14) follows by term-by-term comparison"
should read (5.13); Thm 4.15's proof uses undefined `F_i` (evidently `{B : i ∈ B}`) and
leaves the induction unspecified; Cor 5.10 says `n − 1` for `k − 1`; Thm 4.9 (B2) drops
"almost everywhere" that (A2) carries; Lemma 4.5's proof cites "Corollary 2.5" (a
Proposition); Cor 4.6's proof cites only Prop 4.2 but needs Lemma 4.5; `P I` written for
`P⁺I` in Lemma 4.5(2) and Cor 4.6.
