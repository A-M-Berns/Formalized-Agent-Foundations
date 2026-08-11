# Cartesian Frames

A Lean 4 formalization of Garrabrant, Herrmann, and Lopez-Wild,
[*Cartesian Frames*](https://arxiv.org/abs/2109.10996) (arXiv:2109.10996v1).

Scope: all 60 numbered nodes of the paper, including both appendices.  The current
checked layer covers frames, morphisms, the category `Chu(W)`, the transpose
functor, and the full equivalence layer: isomorphism, biextensionality, the
biextensional collapse, biextensional equivalence, and Appendix A's homotopy
machinery, with Claims 8, 38, 39, and 40 proved (Definitions 1–7, 9, 36–37).
World-level functors (§2.3) and the subagency calculus (§2.4, Appendix B) are
staged next; see `KNOWLEDGE.md` for the settled design decisions and correspondence
table.

The paper is committed verbatim as
[`notes/2109.10996v1-main.tex`](../notes/2109.10996v1-main.tex), with the matching
[`notes/2109.10996v1.pdf`](../notes/2109.10996v1.pdf).  Unlike the Logical Induction
paper, most numbered nodes have no LaTeX `\label`.  Their stable source identifiers
are therefore the printed `Definition n`, `Claim n`, and `Theorem n` numbers.  Every
paper-facing Lean declaration records that identifier in a final `Paper node:`
docstring line; `scripts/check-cartesian-frames-nodes.py` checks it against the TeX
source.  As in the Logical Induction development, `theorem` is reserved for a
statement appearing as a paper claim or theorem, while supporting results are
`lemma`s.

There are currently no `sorry` terms and no `axiom` declarations in this library.
The public surface is inventoried in `AxiomAudit.lean` (CF-INVENTORY block):
`#assert_axioms_clean` over every endpoint, `#assert_fields` freezing the boundary
structures (`Frame`, `Frame.Hom`, `Frame.Biextensional`), and
`scripts/check-cartesian-frames-nodes.py` checking both that every cited node exists
in the paper TeX and that every annotated node has an inventoried endpoint.

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
lake build CartesianFrames
python3 scripts/check-cartesian-frames-nodes.py
python3 scripts/lint_paper_labels.py
```
