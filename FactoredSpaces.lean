/-
# Factored Space Models (Garrabrant, Mayer, Wache, Lang, Eisenstat, Dell, arXiv:2412.02579)

This is the root import for the formalization of *Factored space models: Towards
causality between levels of abstraction*.  The paper is the specification:
`FactoredSpaces/notes/2412.02579v2-main.tex` (with `meta/environment.tex` and `tables/`)
is the exact arXiv source and `FactoredSpaces/notes/2412.02579v2.pdf` the matching PDF.

Paper-facing declarations follow the repository's labeling convention.  A declaration's
docstring ends in a paper-node line naming the printed node — a `Definition`, `Lemma`,
`Proposition`, `Theorem` or `Corollary` together with its section-scoped number — with the
paper section included for navigation.  That annotation is *reserved* for the audited
surface: `scripts/check-factored-spaces-nodes.py` requires every annotated declaration to
be listed in `AxiomAudit.lean`'s FS-INVENTORY block, so internal lemmas cite the paper in
prose instead.  Declarations marked `theorem` are reserved for the paper's numbered
results; supporting mathematics is stated as `lemma`.

**Node numbering.** The paper declares one section-scoped counter,
`\newtheorem{theorem}{Theorem}[section]`, shared by `definition`, `lemma`, `corollary`,
`proposition` (and `example`/`remark`, which it never uses), so numbers read
`Lemma 4.7`, `Definition 6.1`; appendix sections are lettered (`Lemma A.1`,
`Definition C.6`); and several results are stated inside thmtools' `restatable`
wrappers, which count where first stated and not where restated.  Five nodes carry no
`\label` (Definitions 4.2, 5.1, 5.7, C.6 and Proposition 5.6), so the printed number is
the provenance key throughout — the `printed-counter-appendix` scheme in
`scripts/paper_nodes.py`.

A `dd:` tag records a choice made by the formalization rather than by the paper.  The
standing choices (each also documented in `FactoredSpaces/README.md`):

* `dd:pi-space` — the factored space `Ω = ×_{i∈I} Ω_i` of Definition 4.2 is the data
  `(I, Ω)` of an index type and a family `Ω : I → Type` of factors, with the point set
  `Pt Ω = ∀ i, Ω i`.  There is no bundled `FactoredSpace` structure: the paper's objects
  (variables, events, histories, distributions) all live over `Pt Ω`, and quantifying over
  factored spaces (Proposition 5.8) quantifies over `(I, Ω)`.  Definition 4.2's finiteness
  requirements are instance hypotheses on the statements that need them
  (`dd:finiteness-minimal`): `[Fintype I]` wherever a history (a `Finset I`) is formed,
  `[∀ i, Fintype (Ω i)]` where a distribution on `Pt Ω` is summed.  The paper does not
  require the factors to be nonempty and neither do we; where an argument needs a point of
  `Ω` the statement says so.

* `dd:splice` — the paper's merge `a_J · b_{I∖J}` of two families over complementary index
  sets is `J.piecewise a b` (Mathlib's `Finset.piecewise`: `a i` on `J`, `b i` off `J`),
  and its Cartesian product `S_J × T_{I∖J}` of two sets of families is
  `splice J S T = {J.piecewise a b | a ∈ S, b ∈ T}` — both read back inside `Ω`, which
  *is* `Ω_J × Ω_{I∖J}`, so no dependent-subtype projections or transports appear in §4.
  Definition 4.5's `C = C_J × C_{I∖J}` is nevertheless stated literally, with `C_J` the
  image of `C` under the genuine projection `proj J : Pt Ω → PtOn Ω J` (`prodSplit`);
  the splice form is the *proved* equivalent `disintegrates_iff_splice`, and it is what
  every downstream proof uses.  Where the paper's own sets of families over `J` are
  unavoidable — marginals and outer products in Appendix C — `PtOn Ω J = ∀ i : J, Ω i` is
  used directly.

* `dd:variable` — a random variable `X : Ω → Val(X)` is any function `Pt Ω → α`, and
  `Val(X)` is the codomain type `α`, not the image.  Statements quantifying over "all
  values `x ∈ Val(X)`" therefore quantify over `α`; the events `{X = x}` for unattained
  `x` are empty and carry empty histories, which is why Lemma 4.9 needs no finiteness of
  `Val(X)`.  Value spaces are `[Nonempty]` exactly where Lemma C.3's construction of `f`
  requires it (see that lemma's docstring and `notes/paper-errata.md`).

* `dd:event-indicator` — the paper's indicator `1_A : Ω → {0, 1}` is `indic A : Pt Ω → Prop`,
  `ω ↦ (ω ∈ A)`; the history of an event `H(A | C)` is `history (indic A) C`
  (`eventHistory`).  Nothing depends on the two values being `0` and `1`, only on there
  being two of them.

* `dd:dist` — a probability distribution on a finite type is its mass function
  (`Distr S`: `mass : S → ℝ`, nonnegative, summing to `1`), with `P(A) = ∑_{s∈A} P(s)`
  derived.  This is not `FiniteFactoredSets.ProbDist` (an event-based `Set S → ℝ` with
  additivity, `dd:probability` there): everything this paper does with distributions —
  Definition 4.3's pointwise factorization, the factorwise interpolation `⨂((1−λ)Q_i +
  λP_i)`, delta and outer products — is pointwise, and a mass function is the object the
  paper manipulates.  `Δ^F(Ω)` is `factorizing Ω`, `Δ^F_C(Ω)` is `factorizingPos C`,
  and `P ∈ Δ^F` is spelled `Factorizes P`.

* `dd:open-ball` — Proposition 6.6's "nonempty open `S ⊆ Δ^F(Ω)`" (open in the subspace
  topology from `ℝ^Ω`) is stated through the metric-ball criterion for the Euclidean
  distance `euclDist`: every `Q ∈ S` has an `ε`-ball within `Δ^F(Ω)` contained in `S`.
  In a metric subspace that *is* openness, and it is the form Lemma 6.5 consumes.

* `dd:cpd` — "`P` factorizes over `G`" (§5.2, eq. (4)) is the Koller–Friedman form the
  paper follows: `P(x) = ∏_v φ_v(x_v | x_pa(v))` for some family `φ` of conditional
  probability distributions, one per node and parent configuration (`FactorizesOverDAG`).
  Reading `P(x_v | x_pa(v))` as `P`'s own conditionals is undefined at parent
  configurations of probability zero, and that is exactly where Lemma 5.3's "bijective"
  fails (`notes/paper-errata.md`, E5); for strictly positive `P` the CPDs are the
  conditionals (`condCPD`) and Lemma 5.3 holds as stated (`tauPos_bijective`).

* `dd:dsep` — the paper uses d-separation without defining it. `Digraph.DSeparated` is
  the textbook notion over trails (distinct-vertex skeleton paths, colliders = interior
  vertices with both trail edges incoming) with the *endpoint convention*: endpoints are
  non-colliders and block when in `Z`, so the zero-edge trail `v — v` is blocked iff
  `v ∈ Z`. This is the reading the paper's own proof of Proposition 5.8 uses, and the only
  one under which Proposition 5.5 holds for arbitrary `V₁, V₂, V₃` (E8). Proposition 5.5
  is proved directly (`ConditionalHistory.lean`, `ActiveTrails.lean`), not through the
  cited soundness/completeness of d-separation.

* `dd:finiteness-minimal` — as in the sibling formalizations: finiteness and
  decidability hypotheses are carried only where they are used.
-/
import FactoredSpaces.Basic
import FactoredSpaces.History
import FactoredSpaces.Independence
import FactoredSpaces.Probability
import FactoredSpaces.Soundness
import FactoredSpaces.LocalToGlobal
import FactoredSpaces.Completeness
import FactoredSpaces.MainTheorem
import FactoredSpaces.Semigraphoid
import FactoredSpaces.BayesNet
import FactoredSpaces.DSeparation
import FactoredSpaces.ConditionalHistory
import FactoredSpaces.ActiveTrails
import FactoredSpaces.Separation
import FactoredSpaces.PerfectMap
import FactoredSpaces.Examples
import FactoredSpaces.API
