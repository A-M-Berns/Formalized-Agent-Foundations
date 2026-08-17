# Paper errata — Garrabrant, *Temporal Inference with Finite Factored Sets* (arXiv:2109.11513)

Defects found in the paper while formalizing it.  None so far changes any statement; each
is recorded so that a reader comparing the Lean against the printed page is not misled.
Numbering follows the paper's printed, independent-per-environment counters
(`Definition 1`…`50`, `Proposition 1`…`36`, `Lemma 1`…`3`, `Theorem 1`…`3`).

| # | Where | Printed | Should read | Found |
|---|---|---|---|---|
| E1 | Proposition 23, clause 1 | `h^F(X) ⊆ h^Y(Y)` | `h^F(X) ⊆ h^F(Y)` (superscript typo) | stage 4 (§4.2 shard) |
| E2 | Lemma 2, proof, the `|X| = 2` case | `h^F(X) ∪ h^F(Y|x_0) ∪ h^F(Y|x_0)` | second term is `h^F(Y|x_1)` | stage 4 |
| E3 | Proposition 23, clause 2, proof (displayed equations) | `X ≤_E (⋁_E (h^F(X))|E)` | the common refinement is over `S`: `⋁_S` | stage 4 |
| E4 | Proposition 36, proof, first paragraph | "Since `X ⊥_D Y \| {Ω}`, `H_X ∩ H_V = {}`" | the database asserts `X ⊥_D V \| {Ω}`; `(X,Y,{Ω})` is in neither `O` nor `N` | stage 6 (§6.2 shard) |
| E5 | Proposition 36, proof, third paragraph | "`H_X` and `H_V` are nonempty, because `¬(X ⊥_D Z \| {Ω})` and `¬(Y ⊥_D Z \| {Ω})`" | the second citation is `¬(V ⊥_D Z \| {Ω})`, which is what `N` contains | stage 6 |
| E6 | Proposition 36, proof, last paragraph | `h^F(f⁻¹(Z)\|y) ⊆ h^F(f⁻¹(Z) ∨_S f⁻¹(Y)) = h_Z ∪ H_Y` | `H_Z ∪ H_Y` (case typo) | stage 6 |
| E7 | Proposition 34, proof | `H_X ⊆ h^F(f⁻¹(Y) ∨_S f⁻¹(V)) = H_Y ∩ H_V` (and the `X`/`V` swap) | `H_Y ∪ H_V`: Proposition 13 clause 2 gives `h^F(X ∨_S Y) = h^F(X) ∪ h^F(Y)`, and the next sentence uses the union | stage 6 (Example 1 shard) |

Not errata, but worth knowing beside them: the Lean proof of Lemma 2 does not follow
the paper's `|X| = 2` / `|X| ≥ 3` case split — the `|X| = 2` computation runs as the step
of an induction over the finite family `{h^F(Y|x) | x ∈ X}` (finite because each member
lies in `B`, so `S` need not be finite); and Theorem 2's contraction proof needs no
`y ∩ z = ∅` branch, since Mathlib's `Setoid.classes` presents every block with a witness.
