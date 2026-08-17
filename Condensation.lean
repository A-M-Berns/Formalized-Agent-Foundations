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
The vendored *theorems* are proved only for **finite-range** variables, which is strictly
narrower than the paper's standing assumption of countable discrete ranges with finite
entropy.  Every statement here that has entropy content therefore carries `FiniteRange`.
That is a disclosed narrowing (`dd:finite-range` below), not an oversight.

## `dd:` glossary — standing design decisions

A `dd:` tag records a choice made by the formalization rather than by the paper.  The
rationale for each lives in `Condensation/notes/roadmap.md`; changes to them and the
finding IDs that forced any are recorded in `Condensation/KNOWLEDGE.md`.

* `dd:finite-range` — every random variable of a model carries `FiniteRange` (finitely
  many attained values), on a countable discrete sample space (`Countable Ω`,
  `MeasurableSingletonClass Ω`, `IsProbabilityMeasure P`).  The paper's "countable
  discrete range with finite entropy" and "probability space with finite entropy" become:
  countable-discrete range types, finite range per variable, and **no** hypothesis on the
  entropy of `Ω` itself.  This is a genuine type-(c) narrowing — a geometric variable on
  `ℕ` is countable-discrete with finite entropy and is excluded — forced by the fact that
  the vendored entropy theorems are proved only in the finite-range fragment.  Finite
  range implies finite entropy, so every quantity the paper names is finite as required,
  and `Ω`'s own finite entropy is used by the paper only to secure exactly that.

* `dd:pplus` — `P⁺I` is the subtype `PPlus I = {A : Finset I // A.Nonempty}` (Definition
  2.2), faithful to "nonempty subsets only" with no phantom `Y_∅`.  Subfamilies
  `F ⊆ P⁺I` are `Set (PPlus I)`, which keeps the upward-closure, polar and intersection
  algebra of §4.10 and §5 as plain set algebra, and the joint variable `Y_F` is the
  dependent product over the subtype `↥F` with `MeasurableSpace.pi`.  Finiteness of `↥F`
  is by instance from `[Fintype I] [DecidableEq I]`.

* `dd:bundled-model` — `RVModel I` bundles the sample space `Ω : Type u`, its
  σ-algebra/countability/singleton-class instances, the probability measure, the range
  family `R : I → Type v` with their instances, the variables `X i`, their measurability
  and their finite range.  `LatentModel M` bundles a `RVModel (PPlus I)` plus
  `π : Λ → Ω` (`MeasurePreserving`) plus the a.e.-function condition of Definition 3.2.
  Definitions 3.5–3.12 need models as objects of a category and 3.2/4.12 need "two latent
  models with the same underlying space", which is what bundling with explicit `Ω`/`R`
  fields makes statable.  The universes are *pinned*: a `LatentModel M` lives in the same
  `Type u`/`Type v` as `M`.  That is a documented narrowing — see `KNOWLEDGE.md` — taken
  because independent universes force an explicit annotation at every use site for no
  mathematical gain over countable discrete spaces.  Definition 3.1's "finite family" is
  *not* a structure field: `[Fintype I] [DecidableEq I]` is required on the declarations
  that need it.

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
  presentation would import graph theory for no content.  (Not yet landed.)

* `dd:category` — Proposition 3.7 is a `CategoryTheory.Category` instance on the bundled
  type of random variable models; Proposition 3.8 uses `CategoryTheory.IsIso`; Definition
  3.9's a.e.-equality is a `Setoid` on hom-types, and 3.10–3.12 are stated over it.  No
  `Bicategory` — following the paper, which names the 2-category and declines to use it.
  (Not yet landed.)

* `dd:amalgamation` — Definition 4.11's `Λ₀` is the subtype
  `{p : Λ₁ × Λ₂ // π₁ p.1 = π₂ p.2}` with the discrete σ-algebra and the measure
  `∑' p, w p • dirac p`, `w (λ₁, λ₂) = P₁{λ₁} P₂{λ₂} / P_Ω{π₁ λ₁}` (zero when the
  denominator is), which is the paper's (4.53) integral evaluated on a countable discrete
  space.  (Not yet landed.)

## Files

| file | content |
|---|---|
| `Condensation/Probability.lean` | §2: `FunctionOf`/`AEFunctionOf`, pullback invariance (2.2), `PPlus`, interaction information, the Giry alias, **Proposition 2.5** |
| `Condensation/Model.lean` | Definitions 3.1–3.4: `RVModel`, `LatentModel`, joint variables, the four families, (3.9), the scores σ/χ/ϱ |
| `Condensation/Examples.lean` | constructed inhabitants of the boundary structures |

`Condensation/README.md` is the trust surface, `Condensation/KNOWLEDGE.md` the
institutional memory, and `Condensation/notes/roadmap.md` the plan and full `dd:` table.
-/
import Condensation.Probability
import Condensation.Model
import Condensation.Examples
