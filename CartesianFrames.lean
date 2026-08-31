/-
# Cartesian Frames (Garrabrant–Herrmann–Lopez-Wild, arXiv:2109.10996)

This is the root import for the formalization.  The paper is the specification:
`CartesianFrames/notes/2109.10996v1-main.tex` is the exact arXiv source and
`CartesianFrames/notes/2109.10996v1.pdf` is the matching PDF.

Paper-facing declarations follow the Logical Induction labeling convention.  A
declaration's docstring ends in a paper-node line naming the printed node — a
`Definition`, `Claim`, or `Theorem` together with its number — with the paper section
included for navigation.  That annotation is *reserved* for the audited surface:
`scripts/check-cartesian-frames-nodes.py` requires every annotated declaration to be
listed in `AxiomAudit.lean`'s CF-INVENTORY block, so internal lemmas and worked
examples cite the paper in prose instead.  Declarations marked `theorem` are reserved
for the paper's claims and theorem; supporting mathematics is stated as `lemma`.

A `dd:` tag records a choice made by the formalization rather than by the paper.
The standing choices (each also documented in `CartesianFrames/README.md`):

* `dd:universe` — a frame over `W : Type u` has agent and environment types in the
  same universe `u`.  Universe lifting can represent larger presentations, but the
  paper itself imposes no universe stratification.

* `dd:cat` — the paper's Definitions 9–11 are stated as functors, so the categorical
  structure is part of the main-body specification.  The formalization therefore
  provides the `Category (Frame W)` instance from the start and states those
  definitions as bundled `Functor`s in Mathlib's vocabulary; Appendix B's claims are
  stated natively (`Limits.IsInitial`, `Equivalence`, …).  Mathlib has no strict
  "isomorphism of categories", so Claim 46 is rendered as an `Equivalence` together
  with the strict involution `(C*)* = C`.

* `dd:eq-to-iso` — where the paper asserts a literal *equality* of frames that is
  *false* under Lean's subtype/quotient encoding (e.g. Claim 35's idempotence:
  committing changes the agent's *type*, so `(C.commit B).commit _ = C.commit B` is a
  well-typed equation of `Frame W`s whose two sides have different `Agent` types), the
  declaration states the canonical *isomorphism* instead — one rung below equality.  At
  the Claim 35 sites that rung is forced by the encoding; at the `⊥ = ⊥_W` site
  (`botOfUnivIsoBot`) it is a consequence of `instBot` taking `Agent := W` rather than
  `↥Set.univ`, the paper's own literal shape.  An `≅`
  is data rather than a proposition, so such a site is a `def`, not a `theorem`.
  Each affected site carries this tag; biextensional-equivalence corollaries follow
  via Claim 8/40 where downstream wants them.
-/
import CartesianFrames.Basic
import CartesianFrames.Biextensional
import CartesianFrames.Worlds
import CartesianFrames.Subagent
import CartesianFrames.AdditiveMultiplicative
import CartesianFrames.Operations
import CartesianFrames.Categorical
import CartesianFrames.Examples
