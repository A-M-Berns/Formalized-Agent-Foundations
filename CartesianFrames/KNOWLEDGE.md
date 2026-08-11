# Formalization Knowledge — Cartesian Frames (arXiv:2109.10996)

Permanent, curated facts for fresh-context harness agents.  Read
`CartesianFrames/README.md`, `CartesianFrames.lean`, and the paper before adding entries.

## Correspondence table

| Paper node | Lean declaration | Status |
|---|---|---|
| Definition 1 | `CartesianFrames.Frame`, `Frame.image` | defined |
| Definition 2 | `Frame.Hom`, `Hom.comp` | defined; category laws proved as internal lemmas |
| Definition 3 | `Frame.Isomorphic` | defined |
| Definition 4 | `Frame.Biextensional` | defined |
| Definitions 5–7 | — | biextensional collapse/equivalence not started |
| Claim 8 | — | not started; do not credit `isomorphic_refl` as the paper claim |
| Definition 9 | `Frame.dual` | defined; involutivity proved |
| Definition 10 | `Frame.mapWorlds` | object map defined; functorial morphism layer pending |
| Definition 11 | `Frame.curry` | object map defined; functorial morphism layer pending |
| Definition 12 | `Frame.bottom` | defined |

## Design decisions and disclosures

- `dd:universe`: all three carrier types of a frame live in the same Lean universe.
- The paper uses `C \\simeq D` for biextensional equivalence in the main text and again
  for homotopy equivalence in Appendix A, where it proves the notions equivalent.  Keep
  distinct Lean names until Claim 39 is proved; do not overload notation prematurely.
- Most nodes are numbered manually in TeX and have no `\\label`.  Use the printed node
  kind and number as provenance.  The source checker validates those identifiers.

## Pitfalls

- A frame morphism's environment map reverses direction.  Consequently
  `(g.comp f).env = f.env ∘ g.env`.
- Definition 10's TeX names the mapped carriers `B` and `F`, but the intended functor
  leaves the agent and environment carriers unchanged; only outcomes are mapped by `p`.

