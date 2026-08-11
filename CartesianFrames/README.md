# Cartesian Frames

A Lean 4 formalization of Garrabrant, Herrmann, and Lopez-Wild,
[*Cartesian Frames*](https://arxiv.org/abs/2109.10996) (arXiv:2109.10996v1).

Scope: all 60 numbered nodes of the paper, including both appendices.  The current
checked layer covers frames, morphisms, the category `Chu(W)`, the transpose
functor, the full equivalence layer (isomorphism, biextensionality, the collapse,
biextensional equivalence, Appendix A's homotopy machinery — Claims 8, 38–40), the
world-level functors of §2.3 (Definitions 10–11 with the footnote fact), and the
general subagency layer: `⊥`-frames, the categorical/currying/covering definitions
of `◁` (Definitions 12–14, 50) with their equivalences and basic properties proved
(Claims 15–17, 51–53).  One paper erratum found so far (Claim 53's printed proof;
see `notes/cartesian-frames-paper-errata.md`).  Additive/multiplicative subagents,
the operations calculus, and the remaining Appendix B claims are staged next; see
`KNOWLEDGE.md` for settled design decisions and the correspondence table.

[`Examples.lean`](Examples.lean) carries the paper's two worked matrices — §2.1's
driver and §2.2's duplicate-row pair — as concrete `Frame ℕ`s, together with the
non-vacuity witnesses that keep the equivalence layer from being trivially true:
biextensional and homotopy equivalence are *strictly* weaker than isomorphism,
`Homotopic` is neither equality nor the total relation, `BiextEquiv` is not the total
relation, and the collapse genuinely deletes (`dup.collapse ≅ dedup`, while `dup` is
not isomorphic to its own collapse).  These are `lemma`s, not paper claims; they cite
the paper's unnumbered examples in prose and are inventoried in `AxiomAudit.lean`
alongside the definitions they constrain.

The paper is committed verbatim as
[`notes/2109.10996v1-main.tex`](../notes/2109.10996v1-main.tex), with the matching
[`notes/2109.10996v1.pdf`](../notes/2109.10996v1.pdf).  Unlike the Logical Induction
paper, most numbered nodes have no LaTeX `\label`.  Their stable source identifiers
are therefore the printed `Definition n`, `Claim n`, and `Theorem n` numbers.  Every
paper-facing Lean declaration records that identifier in a final `Paper node:`
docstring line; `scripts/check-cartesian-frames-nodes.py` checks it against the TeX
source.  As in the Logical Induction development, `theorem` is reserved for a
statement appearing as a paper claim or theorem, while supporting results are
`lemma`s — and for this library `scripts/lint_paper_labels.py` requires every
`theorem` to name a numbered `Claim` or `Theorem`, since a bare section reference is
not a provenance key here.

There are currently no `sorry` terms and no `axiom` declarations in this library.
The public surface is inventoried in `AxiomAudit.lean` (CF-INVENTORY block):
`#assert_axioms_clean` over every endpoint and `#assert_fields` freezing the boundary
structures (`Frame`, `Frame.Hom`, `Frame.Biextensional`).

`scripts/check-cartesian-frames-nodes.py` enforces the annotation contract
fail-closed, in three parts:

1. **validity** — every node cited in a `Paper node:` line is numbered in the
   committed TeX, and a line that parses to *no* node is itself a violation (so a
   typo cannot silently disable the check);
2. **anchoring** — the literal string `Paper node:` is reserved for the audited
   surface: it must be the last line of a `/-- … -/` docstring attached to a *named*
   declaration.  Anonymous instances therefore cannot carry annotations, and internal
   lemmas and worked examples cite the paper in prose instead;
3. **coverage, per declaration** — every annotated declaration is itself listed in
   CF-INVENTORY.  Sharing a node with some other listed declaration is not enough:
   the annotation claims the node for *that* statement, so that statement is what
   gets axiom-checked.  Identity is namespace-aware and matched on fully qualified
   names, with no bare-suffix matching.

## Modeling boundary

Three standing design decisions, tagged at their sites and defined in
[`CartesianFrames.lean`](../CartesianFrames.lean):

- **`dd:universe`** — Definition 1 permits sets of arbitrary cardinality.  Lean
  represents these as types, and `Frame W` places `W`, `Agent`, and `Env` in one
  universe.  This is not a finiteness restriction; universe lifting can represent
  larger presentations.
- **`dd:cat`** — the paper states Definitions 9–11 as functors, so the
  formalization adopts Mathlib's category theory from the start: `Chu(W)` is a
  `LargeCategory` instance on `Frame W`, and the paper's functors are bundled
  `Functor`s.  Mathlib's categorical vocabulary is therefore part of the trust
  surface.  Mathlib has no strict "isomorphism of categories", so Appendix B's
  Claim 46 will be stated as an `Equivalence` together with the definitional
  involution `(C*)* = C`.
- **`dd:eq-to-iso`** — where the paper asserts a literal equality of frames that
  Lean's subtype/quotient encoding makes unstateable (e.g. Claim 35's idempotence),
  the theorem states the canonical isomorphism instead: one rung below equality,
  and only the forced rung.  Each site carries the tag.

## Build and source checks

```sh
lake build                                        # library + AxiomAudit
python3 scripts/check-cartesian-frames-nodes.py
python3 scripts/lint_paper_labels.py
```
