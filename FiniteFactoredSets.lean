/-
# Finite Factored Sets (Garrabrant, arXiv:2109.11513)

This is the root import for the formalization of *Temporal Inference with Finite
Factored Sets*.  The paper is the specification:
`FiniteFactoredSets/notes/2109.11513-main.tex` is the exact arXiv source and
`FiniteFactoredSets/notes/2109.11513.pdf` is the matching PDF.

Paper-facing declarations follow the repository's labeling convention.  A declaration's
docstring ends in a paper-node line naming the printed node — a `Definition`,
`Proposition`, `Theorem`, `Lemma`, `Corollary` or `Example` together with its number —
with the paper section included for navigation.  That annotation is *reserved* for the
audited surface: `scripts/check-finite-factored-sets-nodes.py` requires every annotated
declaration to be listed in `AxiomAudit.lean`'s FFS-INVENTORY block, so internal lemmas
cite the paper in prose instead.  Declarations marked `theorem` are reserved for the
paper's numbered results; supporting mathematics is stated as `lemma`.

**Node numbering.** This paper declares its theorem environments *without* a `[section]`
argument and without sharing counters, so each environment numbers independently and
never resets: `Definition 1`…`Definition 50` run the length of the paper alongside
`Proposition 1`…`Proposition 36`.  That is the `printed-independent` scheme in
`scripts/paper_nodes.py` — a different counter discipline from ModalAgents' single
section-scoped counter, not a variant of it.  Note also that the paper declares a
`lemma` environment it never uses and a second `lemma2` environment that also prints
"Lemma" and carries all three printed Lemmas; the checker fails closed on that
ambiguity rather than guessing.

A `dd:` tag records a choice made by the formalization rather than by the paper.  The
standing choices (each also documented in `FiniteFactoredSets/README.md`):

* `dd:partition` — the paper's Definition 2 partition (a set `X ⊆ 𝒫(S)` of nonempty
  blocks covering `S` disjointly) is modeled as a `Setoid S`, matching the choice
  already made in `CartesianFrames/`.  Definition 5's `∼_X` is the setoid relation and
  Definition 4's `[s]_X` is `part`.  Proposition 1 is then discharged by the setoid's
  own `iseqv` rather than reproved.

* `dd:order-flip` — **the paper's order glyphs are inverted relative to Mathlib's.**
  The paper writes `X ≥_S Y` for "`X` is finer than `Y`" (Definition 6), so the paper's
  `≥_S` is Mathlib's `≤` on `Setoid`; and Definition 8's *common refinement* `⋁_S(C)` —
  a join in the paper's notation — is Mathlib's `sInf`.  Mathlib's `⊥` (equality) is the
  paper's `Dis_S`, and `⊤` is `Ind_S`.  The formalization uses Mathlib's order
  throughout and never introduces the paper's glyphs, so that no statement has to be
  read under two conventions at once.

* `dd:finiteness-minimal` — finiteness hypotheses are carried only where they are used,
  never globally.  `FactoredSet` takes an arbitrary `S : Type u` with no `Finite`
  constraint; §3–§4 (history, orthogonality, time, subpartitions, conditional
  orthogonality) are stated with `Finite B` alone; and `Finite S` enters at §5.  The reason
  it enters there is exact: `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b` has monomials of finite
  degree `|B|`, but its *sum* ranges over `E ⊆ S`, so once `E` is infinite the `finsum`
  collapses to `0` and it is not the intended polynomial.  This is what the paper means by
  having assumed finiteness "fairly gratuitously" (§7.2), and it is what makes Conjecture 1
  — the finite-*dimensional* fundamental theorem — statable in this library at all.

  The rule is applied per statement, not per section, so §5 is *not* uniformly finite-`S`:
  Propositions 26 and 29 and several supporting lemmas carry `Finite B` alone or no
  finiteness at all, and do apply over an infinite `S`.  `API.lean`'s "Finiteness" section
  is the maintained per-declaration register; read it there rather than assuming a
  section-wide hypothesis.

* `dd:subpartition` — Definition 20's subpartition (a partition of a subset `E ⊆ S`) is
  modeled as a **partial equivalence relation** on `S` — a symmetric, transitive relation —
  whose domain (Definition 21) is `{s | r s s}`, rather than as `Σ E : Set S, Setoid E`.
  The two are in canonical bijection, exhibited by `Subpartition.toSetoid`,
  `Subpartition.ofSetoidOn` and their round-trip lemmas; the payoff is that every §4
  statement is free of dependent subtypes and domain transports.  A partition of `S` is
  the total case (`Subpartition.ofSetoid`); Definition 22's `X|E` is
  `Subpartition.restrict`; the order and common refinement follow `dd:order-flip`
  (`X ≤ Y` is relation inclusion; the paper's `X ∨_E Y` is `X ⊓ Y`); the paper's block
  inclusion "`X ⊆ Z`" is `Subpartition.Subset`.

* `dd:poly` — §5's `Poly^F` is `MvPolynomial (Set S) ℝ` (`Poly S`): the paper's variables
  are the subsets `𝒫(S)` themselves, and under `dd:partition` a block `[s]_b` *is* the set
  `part b s`, hence a variable verbatim.  Definition 29's evaluation `p(f)` is
  `MvPolynomial.eval f p` and Definition 30's support `supp(p)` is `MvPolynomial.vars p`
  (both Mathlib-rendered, no declaration of ours); Proposition 31's "irreducible" is
  Mathlib's `Irreducible` (over `ℝ` the units are the nonzero constants, so it coincides
  with the paper's "no factorization into two polynomials of nonempty support").  Sums and
  products over sets are `finsum`/`finprod`, so the definitions carry no finiteness and
  each statement carries the weakest finiteness its own proof consumes — this is where
  finite *size* genuinely enters, for the sum over `E ⊆ S`, but not on every §5 statement
  (Propositions 26 and 29 need `Finite B` alone; `API.lean` has the register).
  `mono`/`monos`/`poly` take no `F` (the paper's superscript is notational; they depend on
  `C` only); `Q` and `Irr` do.

* `dd:probability` — §5.4's probability distributions are formalized **elementarily, as
  the paper writes them**, with no measure theory anywhere in the statement.  Definition
  36's distribution on a set is the structure `ProbDist S`: a function `P : Set S → ℝ`
  together with `nonneg`, `empty` (`P ∅ = 0`), `univ` (`P Set.univ = 1`) and `additive`
  (`P (E₀ ∪ E₁) = P E₀ + P E₁` for `Disjoint E₀ E₁`) — the paper's four clauses, in order.
  Definition 37's distribution on a factored set is the predicate
  `FactoredSet.IsDistribution P`, namely `P {s} = ∏ᶠ b ∈ B, P (part b s)`, and Definition
  29's evaluation `Q^F_E(P)` is `MvPolynomial.eval P.P (F.Q E)` under `dd:poly`.

  Three consequences worth stating.  A `MeasureTheory.ProbabilityMeasure` would **not** be
  faithful here: the paper's `P` is a function on the full powerset with finite additivity
  and no σ-algebra, and Theorem 3 quantifies over *all* such `P` — a measure-theoretic
  rendering would silently change what the theorem ranges over.  A bridge to Mathlib's
  probability vocabulary is extra credit and must stay a separate lemma, never a stand-in.
  Second, the paper's standing "finite set `S`" is carried by the *statements* that need it
  (Proposition 32 and Theorem 3), not by the structure, per `dd:finiteness-minimal`;
  `ProbDist S` typechecks over any `S`.  Third, Theorem 3's independence conclusion is the
  paper's own **division-free** `P(x∩z) · P(y∩z) = P(x∩y∩z) · P(z)`, so it is meaningful
  when `P(z) = 0` and never introduces a conditional probability.

* `dd:quotient` — Definition 9's Cartesian product `∏(B)` (functions choosing one block
  from each partition) is modeled as the dependent product `(b : B) → Quotient b`, and
  Definition 10's `π` as `fun s b => ⟦s⟧`.  `Quotient b` is canonically the set of
  blocks of `b`, so this is a change of presentation, not of content.

* `dd:model` — Definition 38's model `M = (F, f)` of a sample space is the structure
  `Model Ω`, bundling four things: an implicit carrier `S`, a `FactoredSet S`, the map
  `f : S → Ω`, and — because Definition 38 says *finite* factored set — a `Finite S`
  **field**, registered as an instance.  The finiteness is therefore part of the object
  rather than a hypothesis on statements, which is the one place §6 departs from
  `dd:finiteness-minimal` and does so deliberately: Definitions 43 and 45 quantify over
  models, so "for all models" must already mean "for all finite ones" or the definitions
  say something else.  The consequence a reader should carry is that **no §6 declaration
  carries a finiteness binder of its own**, and `Finite M.F.B` is found by instance search
  wherever an `M : Model Ω` is in scope, which is what lets §6 proofs call the §3–§4
  endpoints unencumbered.

  Definition 39 is rendered by Mathlib and has no carrier: `f⁻¹(ω)` and `f⁻¹(E)` are
  `Set.preimage`, and `f⁻¹(X)` for a partition `X` of `Ω` is `Setoid.comap f X`, whose
  blocks are exactly the nonempty preimages of blocks of `X` — the paper's
  `{f⁻¹(x) | x ∈ X, f⁻¹(x) ≠ {}}` verbatim, with the emptiness side condition supplied by
  `Setoid.classes` rather than written out.  `Model.pullback` is a named alias for that
  third clause and carries no paper-node annotation.  Definition 40's database is the
  structure `OrthDatabase Ω` with two sets of triples; Definition 41's two notations are
  `Orth` and `NotOrth`, and it is worth stating that `NotOrth` is a positive assertion *of
  the database* and not the negation of `Orth` — a database may assert both, in which case
  Definition 43 fails, or neither, in which case Definition 44 fails.
-/
import FiniteFactoredSets.Basic
import FiniteFactoredSets.Examples
import FiniteFactoredSets.History
import FiniteFactoredSets.Orthogonality
import FiniteFactoredSets.Subpartition
import FiniteFactoredSets.SubpartitionHistory
import FiniteFactoredSets.ConditionalOrthogonality
import FiniteFactoredSets.Polynomial
import FiniteFactoredSets.Factoring
import FiniteFactoredSets.CharacteristicOrthogonality
import FiniteFactoredSets.Probability
import FiniteFactoredSets.Inference
import FiniteFactoredSets.InferenceExamples
