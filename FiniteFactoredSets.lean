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
  orthogonality) are stated with `Finite B` alone; and `Finite S` enters only at §5.  The
  boundary is exact: `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b` has monomials of finite degree
  `|B|`, but its *sum* ranges over `E ⊆ S`, so once `S` is infinite it is not a polynomial
  and none of §5 applies to it.  This is what the paper means by having assumed finiteness
  "fairly gratuitously" (§7.2), and it is what makes Conjecture 1 — the
  finite-*dimensional* fundamental theorem — statable in this library at all.

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

* `dd:quotient` — Definition 9's Cartesian product `∏(B)` (functions choosing one block
  from each partition) is modeled as the dependent product `(b : B) → Quotient b`, and
  Definition 10's `π` as `fun s b => ⟦s⟧`.  `Quotient b` is canonically the set of
  blocks of `b`, so this is a change of presentation, not of content.
-/
import FiniteFactoredSets.Basic
import FiniteFactoredSets.Examples
import FiniteFactoredSets.History
import FiniteFactoredSets.Orthogonality
import FiniteFactoredSets.Subpartition
import FiniteFactoredSets.SubpartitionHistory
import FiniteFactoredSets.ConditionalOrthogonality
