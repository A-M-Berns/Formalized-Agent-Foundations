/-
# Cartesian Frames (Garrabrant–Herrmann–Lopez-Wild, arXiv:2109.10996)

This is the root import for the formalization.  The paper is the specification:
`notes/2109.10996v1-main.tex` is the exact arXiv source and
`notes/2109.10996v1.pdf` is the matching PDF.

Paper-facing declarations follow the Logical Induction labeling convention.  A
declaration's docstring ends in `Paper node: Definition n`, `Claim n`, or
`Theorem n`, with the paper section included for navigation.  Declarations marked
`theorem` are reserved for the paper's claims and theorem; supporting mathematics is
stated as `lemma`.

A `dd:` tag records a choice made by the formalization rather than by the paper.
The initial development has one such choice:

* `dd:universe` — a frame over `W : Type u` has agent and environment types in the
  same universe `u`.  Universe lifting can represent larger presentations, but the
  paper itself imposes no universe stratification.
-/
import CartesianFrames.Basic
