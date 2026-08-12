# Cartesian Frames

A Lean 4 formalization of Garrabrant, Herrmann, and Lopez-Wild,
[*Cartesian Frames*](https://arxiv.org/abs/2109.10996) (arXiv:2109.10996v1).

Scope: all 60 numbered nodes of the paper, including both appendices.  **Every
numbered node has a Lean carrier** (modulo the Claim 35 ruling below).  One file per
layer of the paper:

- [`Basic.lean`](Basic.lean) — frames, morphisms, the category `Chu(W)`, and the
  transpose functor (§2.1, Definitions 1–2, 9).
- [`Biextensional.lean`](Biextensional.lean) — the equivalence layer: isomorphism,
  biextensionality, the collapse, biextensional equivalence, and Appendix A's
  homotopy machinery (Definitions 3–7, 36–37; Claims 8, 38–40).
- [`Worlds.lean`](Worlds.lean) — the world-level functors of §2.3, with Definition
  10's footnote fact (Definitions 10–11).
- [`Subagent.lean`](Subagent.lean) — `⊥`-frames and the categorical, currying, and
  covering definitions of `◁`, with their equivalences and basic properties
  (Definitions 12–14, 50; Claims 15–17, 51–53).
- [`AdditiveMultiplicative.lean`](AdditiveMultiplicative.lean) — the
  additive/multiplicative refinement with its equivalence claims, properties, and the
  Decomposition Theorem (Definitions 18–21; Claims 22–23, 41–44; Theorem 24).
- [`Operations.lean`](Operations.lean) — the operations calculus of §2.4.1:
  sub-environments with the collapse of the multiplicative notions, committing,
  assuming, externalizing, internalizing, the subagency claims they generate, and
  idempotence (Definitions 25–33; Claims 27, 30, 34/45, 35).
- [`Categorical.lean`](Categorical.lean) — Appendix B's categorical layer: the
  transpose equivalence with its composites definitionally the identity functors,
  initial and terminal frames, `1_S`, and the categorical and sub-environment
  characterizations of subagency (Definitions 47, 49, 54, 57, 58; Claims 46, 48,
  55–56, 59–60).

Paper errata found so far are collected in `notes/paper-errata.md` (the printed
proofs of Claims 53 and 43 are incomplete though both statements are sound;
Definition 50's "equivalently, `h` surjective" parenthetical is false; Claim 35 is
partially ill-typed).  **Claim 35 is formalized only in part, by ruling:** its
Commit/Assume half is proved (at canonical-isomorphism strength, `dd:eq-to-iso`),
while its External/Internal half is ill-typed as printed — `B` partitions `A`, not
`A/B` — and is deliberately left unformalized.  See `KNOWLEDGE.md` for settled
design decisions and the correspondence table.

[`Examples.lean`](Examples.lean) carries the paper's two worked matrices — §2.1's
driver and §2.2's duplicate-row pair — as concrete `Frame ℕ`s, together with the
non-vacuity witnesses that keep the equivalence layer from being trivially true:
biextensional and homotopy equivalence are *strictly* weaker than isomorphism,
`Homotopic` is neither equality nor the total relation, `BiextEquiv` is not the total
relation, and the collapse genuinely deletes (`dup.collapse ≅ dedup`, while `dup` is
not isomorphic to its own collapse).  The same file pins down the §2.4 subagency
relations on the paper's own examples — the driver committing to skip a route, and the
two-member team — showing that each sits *strictly* between biextensional equivalence
and the total relation: `◁₊` and `◁ₓ` hold there between frames that are not
biextensionally equivalent, both fail in the reverse direction (so the relations are
oriented as the paper orients them), and on a four-option variant `◁` holds while
neither `◁₊` nor `◁ₓ` does.  That last pair also makes Theorem 24's decomposition
non-trivial: every intermediate frame it can produce is biextensionally distinct from
both endpoints.  The file's last sections carry the same treatment to §2.4.1's
operations and to Appendix B: externalizing at a two-cell partition of the four-option
frame, and assuming a sub-environment of the driver, each yield a frame that is
genuinely smaller (related by the paper's relation but *not* biextensionally
equivalent), while a
one-row frame with duplicate columns, paired with the one-by-one frame, shows that
Definition 54's factorization *up to homotopy* is load-bearing at the level of the
relation — the relation holds on that pair while the variant demanding exact
factorization through a single morphism fails — and that the definition's "unique
morphism" remark cannot mean uniqueness of the hom-set element (erratum 7).  These are
`lemma`s, not paper claims; they cite the paper's unnumbered examples in prose and are
inventoried in `AxiomAudit.lean` alongside the definitions they constrain.

The paper is committed verbatim as
[`notes/2109.10996v1-main.tex`](notes/2109.10996v1-main.tex), with the matching
[`notes/2109.10996v1.pdf`](notes/2109.10996v1.pdf).  Unlike the Logical Induction
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
  surface.  Mathlib has no strict "isomorphism of categories" type, so Appendix
  B's Claim 46 is stated as an `Equivalence` (`Frame.dualEquivalence`, whose unit
  and counit are both the identity natural isomorphism) — but the concession is
  purely nominal: both composites are definitionally the identity functors
  (`dualEquivalence_functor_comp_inverse` and its mirror, both `rfl`, carrying the
  Claim 46 annotation), alongside the involution `(C*)* = C`.
- **`dd:eq-to-iso`** — where the paper asserts a literal equality of frames that
  Lean's subtype/quotient encoding makes unstateable (e.g. Claim 35's idempotence),
  the declaration states the canonical isomorphism instead: one rung below equality,
  and only the forced rung.  An `≅` is data rather than a proposition, so these
  sites are `def`s (`Frame.commit_commit_self` and kin, `Frame.botOfUnivIsoBot` and
  its transpose `Frame.oneOfUnivIsoOne`), inventoried like any other endpoint.  Each
  site carries the tag.

## Build and source checks

```sh
lake build                                        # library + AxiomAudit
python3 scripts/check-cartesian-frames-nodes.py
python3 scripts/lint_paper_labels.py
```
