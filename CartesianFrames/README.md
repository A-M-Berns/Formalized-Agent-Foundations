# Cartesian Frames

A Lean 4 formalization of Garrabrant, Herrmann, and Lopez-Wild,
[*Cartesian Frames*](https://arxiv.org/abs/2109.10996) (arXiv:2109.10996v1).

This formalization is at its foundation stage.  The initial checked layer covers the
paper's Cartesian frames, morphisms and composition, isomorphism, biextensionality,
duality, change of possible worlds, currying, and the bottom frame (Definitions 1–4 and
9–12).  The biextensional collapse and the paper's claims and subagency calculus remain
future work.

The paper is committed verbatim as
[`notes/2109.10996v1-main.tex`](../notes/2109.10996v1-main.tex), with the matching
[`notes/2109.10996v1.pdf`](../notes/2109.10996v1.pdf).  Unlike the Logical Induction
paper, most numbered nodes have no LaTeX `\\label`.  Their stable source identifiers are
therefore the printed `Definition n`, `Claim n`, and `Theorem n` numbers.  Every
paper-facing Lean declaration records that identifier in a final `Paper node:` docstring
line; `scripts/check-cartesian-frames-nodes.py` checks it against the TeX source.  As in
the Logical Induction development, `theorem` is reserved for a statement appearing as a
paper claim or theorem, while supporting results are `lemma`s.

There are currently no `sorry` terms and no `axiom` declarations in this library.  The
first paper theorem has not yet been claimed as formalized, so the Cartesian Frames
surface has not yet been added to `AxiomAudit.lean`.

## Modeling boundary

`dd:universe`: Definition 1 permits sets of arbitrary cardinality.  Lean represents
these as types, and the initial `Frame W` places `W`, `Agent`, and `Env` in one universe.
This is not a finiteness restriction; universe lifting can represent larger
presentations.  It is nevertheless a formalization choice and is recorded here and at
the definition.

## Build and source checks

```sh
lake build CartesianFrames
python3 scripts/check-cartesian-frames-nodes.py
python3 scripts/lint_paper_labels.py
```

