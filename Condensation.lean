/-
# Condensation (Eisenstat, 2025)

This is the root import for the formalization of Sam Eisenstat, *Condensation: A Theory of
Concepts* (July 2025, 27 pp.; OpenReview `HwKFJ3odui`).  The paper is the specification:
`Condensation/notes/condensation-25-07.pdf` is the PDF and
`Condensation/notes/condensation-25-07.txt` is the committed `pdftotext -layout`
extraction that the node checker reads.  No TeX source exists in hand, so the printed
node numbers — a single section-scoped counter shared across kinds, `Definition 2.1` …
`Corollary 5.10` — are the provenance keys.  (The extractor drops `fi`/`ff` ligatures, so
the committed text reads `Denition`, `nite`, `dierent`; the checker's regex allows this.)

Paper-facing declarations follow the repository's labeling convention: the docstring ends
in a paper-node line naming the printed node (kind and number, backticked).  That
annotation is reserved for the audited surface; internal lemmas cite the paper in prose
instead.  `theorem` is reserved for the paper's numbered results and paper-facing `def`s
and `structure`s carry the annotation too; supporting mathematics is stated as `lemma`.

**Substrate.**  Entropy, conditional entropy, mutual information and conditional mutual
information are *not* formalized here.  They come from `ShannonInformation.API`, FAF's
shared consumer surface over a pinned vendoring of the PFR project's Shannon-information
library.  A Condensation file imports `ShannonInformation.API` and targeted `Mathlib.*`
modules only: it must never name a `PFR.*` module, and must never `import Mathlib`
wholesale, which fails to elaborate against the vendored shims (see
`ShannonInformation/README.md`).

**Scope boundary, read this first.**  `ShannonInformation/SCOPE.md` is required reading.
The *vendored* theorems are proved only for **finite-range** variables, which is narrower
than the paper's standing assumption of countable discrete ranges with finite entropy.
This library no longer cites them for anything load-bearing: it cites the FAF-authored
corpus in `ShannonInformation/FiniteEntropy/`, which proves the same facts at
`ShannonInformation.FiniteEntropyOf` — countable discrete range with finite entropy, the
paper's own hypothesis.  The narrowing `dd:finite-range` was retired on 2026-08-17 and
there is no modeling substitution left here (`Condensation/README.md`, *Modeling
boundary*).

Where the finiteness now sits: **fields of `RVModel`** — `finiteEntropy_Ω`, which is
Definition 3.1's own "with finite entropy" clause on the sample space, and
`finiteEntropy_X` for the variables — so every statement quantifying over a model or a
latent model gets it from the structure and never as a separate hypothesis.  Any
measurable variable derived from a model's sample space gets it in one step from
`RVModel.finiteEntropyOf`.  The §2 substrate lemmas of `Condensation/Probability.lean` are
stated over bare variables rather than models, and those carry the hypothesis explicitly —
seven of them do (`condEntropy_comp_measurePreserving`, `interactionInfo_swap`,
`condEntropy_eq_entropy_of_subsingleton`, `entropy_le_of_aeFunctionOf`,
`condEntropy_eq_zero_of_aeFunctionOf`, `aeFunctionOf_of_condEntropy_eq_zero`,
`aeFunctionOf_iff_condEntropy_eq_zero`), while the `IdentDistrib`-based pullback
identities, `interactionInfo_comm` and `entropy_pair_of_aeFunctionOf` need no finiteness at
all.  It is *not* the case that every statement with entropy content carries it.

**Namespace hazard, and it is the one most likely to cost you an hour.**  Both versions of
several entropy facts are reachable through the single import, and with `ProbabilityTheory`
open a bare lemma name resolves by elaboration success rather than by namespace — so a bare
citation can silently pick the `FiniteRange`-gated vendored version and fail later with a
missing instance.  Write `ShannonInformation.foo` in full; see `ShannonInformation/API.lean`'s
"which version to cite" table.  Dot notation is the case no `open` can rescue:
`h.condEntropy_eq_entropy` and `hid.condEntropy_eq` resolve in the *head symbol's* namespace
(`ProbabilityTheory.IndepFun`, `ProbabilityTheory.IdentDistrib`) and so always find the
vendored original — write those two out and pass the hypothesis as an argument.

## `dd:` glossary — standing design decisions

A `dd:` tag records a choice made by the formalization rather than by the paper.  The
rationale for each lives in `Condensation/notes/roadmap.md`; changes to them and the
finding IDs that forced any are recorded in `Condensation/KNOWLEDGE.md`.

* `dd:finite-range` — **RETIRED 2026-08-17.  Kept in this glossary under its old key
  because older commits, the audit ledger and `Condensation/notes/finite-range-generalization-plan.md`
  refer to it by name; it is not a live decision and nothing in the library is tagged with
  it.**  It read: every random variable of a model carries `FiniteRange` (finitely many
  attained values) and `Ω` carries **no** hypothesis on its own entropy — a genuine
  type-(c) narrowing, since a geometric variable on `ℕ` is countable-discrete with finite
  entropy and was excluded, forced by the vendored entropy theorems existing only in the
  finite-range fragment.  It now reads, verbatim from Definition 3.1: a countable discrete
  probability space **with finite entropy** (`[Countable Ω] [MeasurableSingletonClass Ω]
  [IsProbabilityMeasure P]` plus the field `finiteEntropy_Ω :
  ShannonInformation.FiniteEntropyMeasure P`) carrying variables of countable discrete
  range and finite entropy (`finiteEntropy_X`).  The `Ω` clause is new — the narrowed
  version dropped it outright.  What made the retirement possible was the FAF-authored
  `ShannonInformation/FiniteEntropy/` corpus; what shows it has content is
  `Condensation.Example.geomModel`, a model of this library whose variable provably has
  infinite range.

* `dd:pplus` — `P⁺I` is the subtype `PPlus I = {A : Finset I // A.Nonempty}` (Definition
  2.2), faithful to "nonempty subsets only" with no phantom `Y_∅`.  Subfamilies
  `F ⊆ P⁺I` are `Set (PPlus I)`, which keeps the upward-closure, polar and intersection
  algebra of §4.10 and §5 as plain set algebra, and the joint variable `Y_F` is the
  dependent product over the subtype `↥F` with `MeasurableSpace.pi`.  Because Definition
  3.1's index type is finite, `P⁺I` really is the paper's `P⁺I` (all nonempty subsets,
  which are automatically finite), and finiteness of `↥F` is by instance from `[Finite I]`
  alone — via `Condensation.instFiniteFinset` and `Condensation.PPlus.instFinite`.  No
  `Fintype`/`DecidableEq` data is needed anywhere.

* `dd:bundled-model` — `RVModel I` bundles the sample space `Ω : Type u`, its
  σ-algebra/countability/singleton-class instances, the probability measure, its finite
  entropy (Definition 3.1's clause on `Ω`), the range family `R : I → Type v` with their
  instances, the variables `X i`, their measurability and their finite entropy, over a
  **finite** index type: `[Finite I]` is a class parameter
  of the structure, which is Definition 3.1's "finite family".  It is a parameter rather
  than a field because `Finite I` does not mention the model, so as a field instance
  search would never find it and a score over `I = ℕ` would elaborate with every sum
  silently empty.  `LatentModel M` bundles a `RVModel (PPlus I)` plus `π : Λ → Ω`
  (`MeasurePreserving`) plus the a.e.-function condition of Definition 3.2.  Definitions
  3.5–3.12 need models as objects of a category and 3.2/4.12 need "two latent models with
  the same underlying space", which is what bundling with explicit `Ω`/`R` fields makes
  statable.  The latent universes are **independent** of `M`'s: the full parameter list is
  `LatentModel.{u, v, w, u', v'}`, with `Λ : Type u'` and the latent ranges in `Type v'`.
  Nothing in the paper ties them, and Example 4.4 — where `X_i := Y_∋i` puts the given
  ranges in `Type (max v' w)` — is not statable in its printed generality if they are
  pinned together.  `RVModel`'s own `Type u`/`Type v` stratification remains (see
  `README.md`, "Universe stratification").

* `dd:ae-function` — "`Y` is a function of `X` almost everywhere" is
  `AEFunctionOf X Y P := ∃ f, Measurable f ∧ ∀ᵐ ω ∂P, Y ω = f (X ω)`; the everywhere
  version `FunctionOf` likewise without `∀ᵐ`.  Verbatim Definition 2.1's fifth
  convention.  The measurability conjunct is free in this setting
  (`measurable_of_countable`), but keeping it stops the definition drifting from the
  paper's.  The measure is an explicit argument, as in the vendored API.

* `dd:pullback` — the pullback `π^* X` is plain composition `X ∘ π`, and
  probability-preserving is Mathlib's `MeasureTheory.MeasurePreserving`.  Equation (2.2)
  invariance is `IdentDistrib`-based.  Repo rule: never redefine what Mathlib has.

* `dd:interaction` — Definition 2.3's `I(X;Y;Z) = I(X;Y) − I(X;Y|Z)` and its conditional
  form `I(X;Y;Z | C) = I(X;Y|C) − I(X;Y|⟨Z,C⟩)` (needed by Lemma 5.4 and Theorem 5.8) are
  FAF-authored `def`s over the vendored `mutualInfo`/`condMutualInfo`; symmetry is a
  lemma.  The shared API deliberately adds no definitions, so interaction information is
  paper-specific until a second client needs it.

* `dd:tree` — Definition 5.6's intersection tree is an inductive binary tree with the
  label of a node *computed* as the meet of its children's labels; Proposition 5.7 is
  stated as: any labeling of the tree's positions agreeing on leaves and satisfying (5.10)
  at every internal position equals the computed labeling.  A directed rooted binary tree
  with unique paths to the root *is* an inductive binary tree; the `(V, E, ℓ)`
  presentation would import graph theory for no content.  Landed in
  `Condensation/Quantitative.lean` as `ITree` (the tree), `ITree.label` (the computed
  labelling), `LTree` (an arbitrary labelling of every position, which is what Proposition
  5.7 quantifies over) and `ITree.intersections` (Definition 5.6's family (5.11), a `List`
  because the paper warns that the same intersection may recur).

* `dd:category` — Proposition 3.7 is a `CategoryTheory.Category` instance on the bundled
  type of random variable models; Proposition 3.8 uses `CategoryTheory.IsIso`; Definition
  3.9's a.e.-equality is a `Setoid` on hom-types, and 3.10–3.12 are stated over it.  No
  `Bicategory` — following the paper, which names the 2-category and declines to use it.
  Landed in `Condensation/Morphism.lean`: the object type is `RVModelObj`, which carries
  its index type as a **field** (Definition 3.5 lets a morphism change the index set, so it
  cannot be a parameter of the object type), `RVModel.Hom` carries `π`, `π_pres`, `ι`, `f`
  and `eq_ae` and *no* measurability field for `f` (the paper's own remark is that it is
  automatic on countable discrete ranges — `RVModel.Hom.measurable_f`), and the category
  laws (3.17)–(3.20) hold by `rfl`, being the corresponding laws for the three components
  with the two `Prop`-valued fields carried along.

* `dd:amalgamation` — Definition 4.11's `Λ₀` is the subtype
  `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with the discrete σ-algebra and the measure
  `∑' p, w p • dirac p`, `w (λ₁, λ₂) = P₁{λ₁} P₂{λ₂} / P_Ω{π₁ λ₁}` (zero when the
  denominator is), which is the paper's (4.53) integral evaluated on a countable discrete
  space.  Landed in `Condensation/Amalgamation.lean`, with `Λ₀` as the *primary* datum of
  `LatentAmalgamation`: the two latent variable models Definition 4.12 names are derived
  (`lat₁`, `lat₂`), so that their underlying space is `Λ₀` definitionally rather than by a
  transported type equality.  Definition 4.12 does not tie `π̃₁` to `π̃₂`, which Theorem
  4.15 needs, so the a.e. commutation is carried as the field `comm` and recorded as
  erratum 10 — and that is the *only* added field: clause (3)'s `ρₖ` are morphisms in the
  sense of Definition 3.5, i.e. of the underlying random variable models, so all that
  survives of it is `ρₖ_pres` and `ρₖ_Y` (two further fields relating `Lₖ.π ∘ ρₖ` to `π̃ₖ`
  were an over-reading and were deleted).  `LatentAmalgamation.diagonal` — a latent
  variable model amalgamated with itself along the identity — is the constructed,
  axiom-clean inhabitant that makes Theorem 4.15 and all of §5 non-vacuous.

## Files

The import order below is also the dependency order.  Two edges are worth naming because
they are not obvious and were settled by construction: `Perfect.lean` imports
`Morphism.lean` (Proposition 4.7's clause (2) *is* Definition 3.10), and `Examples.lean`
imports `Perfect.lean`, so the §3.1 witnesses — the concrete morphisms and category
objects — live at the end of `Examples.lean` rather than in `Morphism.lean`, which would
close a cycle.  `Morphism.lean` therefore imports `Model.lean` and nothing else of the
library.

| file | content |
|---|---|
| `Condensation/Probability.lean` | §2: `FunctionOf`/`AEFunctionOf`, pullback invariance (2.2), `PPlus`, interaction information, the Giry alias, **Proposition 2.5** |
| `Condensation/Model.lean` | Definitions 3.1–3.4: `RVModel` (Definition 3.1 verbatim, both finite-entropy clauses) with `RVModel.finiteEntropyOf`, `LatentModel`, joint variables, the four families `∩A`/`⊇A`/`⊋A`/`∋i` plus `incomparable`, (3.9), the scores σ/χ/ϱ, and the generic joint-variable and upward-closure lemmas §4 and §5 run on |
| `Condensation/Morphism.lean` | §3.1: Definitions 3.5, 3.6, Propositions 3.7, 3.8, Definitions 3.9, 3.10, Propositions 3.11, 3.12 |
| `Condensation/Perfect.lean` | §4 up to Proposition 4.10: Proposition 4.2, Definition 4.3, Lemma 4.5, Corollary 4.6, Proposition 4.7, Definition 4.8, **Theorem 4.9**, Proposition 4.10 |
| `Condensation/Amalgamation.lean` | Definitions 4.11, 4.12, **Lemma 4.13** (the measure construction of (4.49)–(4.53), proved), and `LatentAmalgamation.diagonal` |
| `Condensation/Comparison.lean` | Lemma 4.14, **Theorem 4.15** |
| `Condensation/Quantitative.lean` | §5: Lemma 5.4, Definitions 5.5, 5.6, Proposition 5.7, **Theorem 5.8**, Corollaries 5.9, 5.10 |
| `Condensation/Examples.lean` | Examples 4.1 and 4.4, constructed inhabitants of every boundary structure, the general non-vacuity result `LatentModel.nonempty`, the §3.1 witnesses, and `Example.geomModel` — the infinite-range model that the retired `dd:finite-range` narrowing excluded |

## Status at milestone M1

**Statements for every in-scope node have landed; seventeen proofs are still `sorry`.**  All
39 in-scope nodes of the paper's 42 carry at least one annotated declaration; the three
that do not are Examples 5.1–5.3, which are out of scope by the proposed ruling recorded
in `Condensation/notes/roadmap.md` (5.1 and 5.2 posit `[0,1]`-valued latents, outside the
paper's own countable-discrete framework; 5.3 is a prose translation of structural causal
models with no claim, and nothing downstream cites any of the three).

The `sorry`s are milestone M2's and are enumerated, per file and per declaration, in
`Condensation/README.md`.  Every one of them now sits inside a declaration that carries a
paper-node annotation; the library has no `sorry` in a supporting lemma.  They are staged
in `AxiomAudit.lean`'s `CONDENSATION-PENDING` block: an annotated endpoint whose proof is
not finished cannot go into `#assert_axioms_clean` (that command exists to catch exactly a
`sorry`), so it is listed in a comment block beside the inventory instead, and
`scripts/check-condensation-nodes.py` accepts an endpoint listed in *either* block while
failing if a name appears in both, if a pending entry names no annotated declaration, or if
the pending block is non-empty once `scripts/papers.py` registers the paper `completed`.
The block has a second section for declarations that depend on a `sorry` without being
endpoints — three of them today, small consequences of Proposition 4.2's staged inequality.
That the two sections together are *complete* is itself machine-checked, by
`scripts/check_sorry_ledger.py`, which asks Lean from the compiled environment which
declarations depend on `sorryAx` and fails on drift in either direction.  Everything not in
that block is axiom-checked in the ordinary way.

`Condensation/README.md` is the trust surface, `Condensation/KNOWLEDGE.md` the
institutional memory, and `Condensation/notes/roadmap.md` the plan and full `dd:` table.
-/
import Condensation.Probability
import Condensation.Model
import Condensation.Morphism
import Condensation.Perfect
import Condensation.Amalgamation
import Condensation.Comparison
import Condensation.Quantitative
import Condensation.Examples
