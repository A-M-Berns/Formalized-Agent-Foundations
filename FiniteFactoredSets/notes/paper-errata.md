# Paper errata — Garrabrant, *Temporal Inference with Finite Factored Sets* (arXiv:2109.11513)

Defects found in the paper while formalizing it.  None so far changes any statement of the
Lean development; each
is recorded so that a reader comparing the Lean against the printed page is not misled.
E8–E14 came out of the final (round 11) audit and are the first rows outside §4.2 and §6.2.
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
| E7 | Proposition 34, proof | `H_X ⊆ h^F(f⁻¹(Y) ∨_S f⁻¹(V)) = H_Y ∩ H_V` | `H_Y ∪ H_V`: Proposition 13 clause 2 gives `h^F(X ∨_S Y) = h^F(X) ∪ h^F(Y)`, and the next sentence uses the union. This is the *only* defect in Prop 34's proof — its citation of `X ⊥_D V \| {Ω}` is correct, unlike Prop 36's (E4) | stage 6 (Example 1 shard) |
| E8 | Definition 22 (§4.1) | "a partition `X` of `S` … `X\|E = {[e]_X ∩ E \| e ∈ E}`" | the index set is `S ∩ E`: `[e]_X` is undefined for `e ∈ E ∖ S`. The definition is also stated only for partitions of `S` although §4.2–§4.3 apply `X\|E` to *subpartitions* throughout, and its set-builder admits empty members once `E ⊄ dom(X)`, contradicting Definition 2. Lean sidesteps all three by typing `E : Set S` and defining `Subpartition.restrict` for subpartitions with `dom = X.dom ∩ E`, keeping only nonempty traces | round 11 |
| E9 | Proposition 21, proof (§4.1) | "the equivalent definition from Proposition 20 that `C ⊢^F X` iff `X ≤_S ⋁_S(C)`" | that is Proposition 10's clause, for partitions of `S`. Proposition 20 clause 7 for a *subpartition* is the conjunction `X ≤_E (⋁_S(C)\|E)` **and** `χ^F_C(E,E) = E`, and the paper stresses two paragraphs earlier that the second conjunct is not removable. Parts 1–4 are repairable (the missing conjunct depends only on the shared `C` and `E`); the Lean does not copy the gap, proving clauses 1–4 through the relational form `generatesSub_iff_rel` | round 11 |
| E10 | Lemma 3, proof, the `2 → 1` direction (§5.3) | "`p` divides `Q^F_{y∩z}` for all `y ∈ I`"; "`p` divides neither `Q^F_{x∩z}` nor `Q^F_{x∩z}`" | `for all y ∈ Y`, and the second polynomial is `Q^F_{y∩z}`. Two independent typos in one paragraph; `orthogonalGiven_tfae` clause 2 quantifies over `Y` correctly | round 11 |
| E11 | Theorem 3, proof (§5.5) | `Q^F_{[s]_b}(f) = poly^F_{b}([s]_b) · poly^F_{B∖{b}}(S)` | the right-hand side is missing its evaluation `(f)` — a polynomial identity read as an identity of reals. The next display restores it. The Lean keeps the two apart, proving the polynomial identity and evaluating separately | round 11 |
| E12 | Definition 36 (§5.4) | clauses 2 and 3, `P(∅) = 0` and `P(S) = 1` | unsatisfiable when `S = ∅`, which the paper never says, although Theorem 3 is stated for every finite factored set and Proposition 9 clause 1 discusses the size-0 case explicitly. The Lean does not copy it: `Examples.isEmpty_probDist_empty` proves `IsEmpty (ProbDist Empty)` and `Examples.orthogonalGiven_emptyFS` proves the theorem's *left* side holds there too, so the biconditional is true-but-uninformative rather than false. (Clause 2 is also redundant — it follows from clause 4 at `E₀ = E₁ = ∅` — and is kept as a field to mirror the paper's four clauses) | round 11 |
| E13 | Definition 47 (§7.3) | `X = {x₀, …, xₙ₋₁}` | silently assumes `X` is finite and numbered, and the numbering is never used. `ObservesPartition` indexes the sub-agent family by `X.classes` instead, which is strictly more general and needs no finiteness | round 11 |
| E14 | Proposition 36, proof (§6.2) | `b_y` introduced, `b_Y` argued about; and `h^F(f⁻¹(Z)\|(S∖y))` formed without comment | the two names denote the same object (cosmetic, but it is why a reader may think two factors are in play in the `p₀`/`p₁` splice); and the `p₁` argument needs `S ∖ y` to be a *block* of `f⁻¹(Y)`, which holds here only because every model of `D` forces `f⁻¹(Y)` to have exactly two parts. The Lean supplies that step explicitly (`compl_mem_classes`, from `exists_point`) | round 11 |

Not errata, but worth knowing beside them: the Lean proof of Lemma 2 does not follow
the paper's `|X| = 2` / `|X| ≥ 3` case split — the `|X| = 2` computation runs as the step
of an induction over the finite family `{h^F(Y|x) | x ∈ X}` (finite because each member
lies in `B`, so `S` need not be finite); and Theorem 2's contraction proof needs no
`y ∩ z = ∅` branch, since Mathlib's `Setoid.classes` presents every block with a witness.
Two printed steps are asserted rather than argued, and the Lean has to isolate each: in
Proposition 31's proof "every variable clearly has degree at most 1 in `poly^F_C(E)`" is
Corollary 1 applied at `C ⊆ B`, which is `degreeOf_poly_le`; and the same proof's
`poly^F_C(E) = r₀r₁ · poly^F_C(χ^F_{C₀}(E,E))` silently uses `r₀r₁ = 1` (all coefficients
are 1, which is `coeff_poly`).  Lemma 2's `|X| ≥ 3` reduction likewise applies
`h^F(⋁) = ⋃ h^F` to a family indexed by the blocks of `X`, where Proposition 23 clause 2
gives only the binary case — the Lean inducts over the family of *histories* instead, which
is why its Lemma 2 needs `[Finite F.B]` alone and holds for arbitrarily many blocks over an
arbitrary `S`.
