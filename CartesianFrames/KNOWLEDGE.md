# Formalization Knowledge — Cartesian Frames (arXiv:2109.10996)

Permanent, curated facts for fresh-context harness agents.  Read
`CartesianFrames/README.md`, `CartesianFrames.lean`, and the paper before adding
entries.  Scope of the formalization: **all 60 numbered nodes**, both appendices
(user ruling, 2026-08-11).

## Correspondence table

| Paper node | Lean declaration | Status |
|---|---|---|
| Definition 1 | `CartesianFrames.Frame`, `Frame.image` | defined |
| Definition 2 | `Frame.Hom`, `Frame.Hom.comp`, `LargeCategory (Frame W)` instance | defined; category laws hold by `rfl` |
| Definition 9 | `Frame.dual`, `Frame.Hom.dual`, `Frame.dualFunctor` | defined; `(C*)* = C` is `rfl` |
| Definitions 3–8, 10–58, Claims, Theorem 24 | — | not started |

## Design decisions (settled with Anson, 2026-08-11)

- `dd:universe`: all three carrier types of a frame live in one Lean universe.
- `dd:cat` (**user-decided**): all-in Mathlib category theory from `Basic.lean`.
  Rationale: the paper's own Definitions 9–11 say "the functor …" in the main body;
  a late categorical layer would leave two parallel spellings of composition.
  Consequence: Mathlib's `Functor`/`Iso`/`Limits` vocabulary is part of the trust
  surface.  Claim 46 will be an `Equivalence` (Mathlib has no strict isomorphism of
  categories) plus the strict `dual_dual : C.dual.dual = C`.
- `dd:eq-to-iso` (**user-decided**): where the paper asserts literal frame
  *equality* that the subtype/quotient encoding makes unstateable (Claim 35
  idempotence and kin), state the canonical *isomorphism* `≅` — the strongest
  expressible form — with a per-site disclosure.  Do **not** weaken such sites to
  biextensional equivalence; add `≃`-corollaries only as one-line consequences.
- Primary definitions: the paper's *first-presented* definition of each subagency
  relation owns the plain name/notation — categorical (Def 13) for `◁`, committing
  (Def 18) for `◁₊`, externalizing (Def 19) for `◁ₓ`.  The other seven definitions
  (14, 20, 21, 50, 54, 57, 58) are named variants with iff-theorems (Claims 15, 22,
  51–53, 55–56, 59–60).  Proofs may route through whichever variant is convenient.
- Subset-flavored operations (Defs 18, 28, 29) use `Set`/subtype rendering:
  `Commit` takes `B : Set C.Agent` and produces agent carrier `↥B`.
- Partitions (Defs 31–33) will be modeled as `Setoid`; the paper's `A/B` (choice
  functions selecting one element per cell) becomes
  `{q : Quotient s → A // ∀ c, ⟦q c⟧ = c}`.  Search Mathlib's partition API before
  writing this (`Setoid.IsPartition`, `Quotient.out`, …).
- The paper overloads `≃` for biextensional equivalence (main text) and homotopy
  equivalence (Appendix A), proving them equivalent only at Claim 39.  Keep two
  distinct Lean names; biextensional equivalence gets the notation; Claim 39 is the
  bridge.  Do not overload prematurely.
- Unnumbered load-bearing facts become named internal lemmas annotated to their
  surrounding definition: morphisms `C ⟶ ⊥` biject with `C.Env` (used by Claims 51,
  53, 55), and `p°` preserves biextensional equivalence (Def 10's footnote).

## Deferred interpretation question (do not resolve unilaterally)

**Claim 35 is partially ill-typed in the paper's own set theory.**  `Commit`/`Assume`
idempotence is fine (`B ⊆ B`).  But `External^B(C)` has agent `A/B`, and `B` is a
partition of `A`, not of `A/B`, so `External^B(External^B(C))` is not well-formed as
written; likewise `Internal`.  The claim's binder line also garbles indices
(`Assume^B` with `B ⊆ A`; `External^F` with `F` a partition of `E`, contradicting
Definition 32).  Plan of record: before Stage 4, consult the original AI Alignment
Forum sequence (Garrabrant 2020, paper footnote 1) for the intended statement,
propose a reading, and **escalate to Anson** as a concrete decision + paper-errata
note.  Auditors: flag any formalization of Claim 35's External/Internal half that
was not preceded by that ruling.

## Pitfalls

- A frame morphism's environment map reverses direction.  Consequently
  `(f ≫ g).env = f.env ∘ g.env`.
- Definition 10's TeX names the mapped carriers `B` and `F`, but the intended functor
  leaves the agent and environment carriers unchanged; only outcomes are mapped by
  `p`.
- Category laws and `dual_dual` hold by `rfl` (definitional eta for structures and
  functions).  Prefer `rfl` before reaching for `ext` in this layer.
