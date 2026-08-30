# Paper errata — Garrabrant, *Temporal Inference with Finite Factored Sets* (arXiv:2109.11513)

Defects found in the paper while formalizing it.  None so far changes any statement of the
Lean development; each
is recorded so that a reader comparing the Lean against the printed page is not misled.
E8–E14 came out of the final (round 11) audit and are the first rows outside §4.2 and §6.2.
E15–E18 came out of the 2026-08-30 cross-family (codex) statement sweep, the re-run of the
sweep parked at round 11 (its Proposition 34 ∩/∪ finding independently reconfirmed E7).
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
| E12 | Definition 36 (§5.4) | clauses 2 and 3, `P(∅) = 0` and `P(S) = 1` | unsatisfiable when `S = ∅`, which the paper never says, although Theorem 3 is stated for every finite factored set and Proposition 9 clause 1 discusses the size-0 case explicitly. The Lean copies the definition exactly — `ProbDist` carries both fields, and `Examples.isEmpty_probDist_empty` proves `IsEmpty (ProbDist Empty)` — but not the consequence: `Examples.orthogonalGiven_emptyFS` proves Theorem 3's *left* side holds there too, so the biconditional is true-but-uninformative rather than false. (Clause 2 is also redundant — it follows from clause 4 at `E₀ = E₁ = ∅` — and is kept as a field to mirror the paper's four clauses) | round 11 |
| E13 | Definition 47 (§7.3) | `X = {x₀, …, xₙ₋₁}` | silently assumes `X` is finite and numbered, and the numbering is never used. `ObservesPartition` indexes the sub-agent family by `X.classes` instead, which is strictly more general and needs no finiteness | round 11 |
| E14 | Proposition 36, proof (§6.2) | `b_y` introduced, `b_Y` argued about; and `h^F(f⁻¹(Z)\|(S∖y))` formed without comment | the two names denote the same object (cosmetic, but it is why a reader may think two factors are in play in the `p₀`/`p₁` splice); and the `p₁` argument needs `S ∖ y` to be a *block* of `f⁻¹(Y)`, which holds here only because every model of `D` forces `f⁻¹(Y)` to have exactly two parts. The Lean supplies that step explicitly (`compl_mem_classes`, from `exists_point`) | round 11 |
| E15 | Proposition 3, proof (§2.2) | "Let `F = (S, B)` be a finite factored set" | the proposition is stated for an arbitrary factored set and its proof uses only injectivity of the coordinate map, never finiteness; the Lean theorem carries no `Finite` hypothesis | codex sweep (2026-08-30) |
| E16 | Proposition 21, proof (§4.1) | "the equivalent definition from Proposition 20 that `C ⊢^F X` iff `X ≤_E (⋁_S(C)\|E)`" alone | subpartition generation also requires Proposition 20 clause 7's second conjunct `χ^F_C(E,E) = E`, which the paper itself stresses is not removable; the refinement inequality alone is a false characterization (this sharpens E9, which recorded the mis-citation). The Lean proves the clauses through `generatesSub_iff_rel` without the false equivalence | codex sweep (2026-08-30) |
| E17 | Theorem 2, weak-union proof (§4.3) | restriction-history equality asserted "for each `w ∈ W`" | Lemma 1 applies only when `w ∩ z` is a nonempty block of `W\|z`; for `w` disjoint from `z` the asserted equality is not available. The conclusion needs only nonempty intersections, and the Lean's `Setoid.classes` formulation ranges over exactly those | codex sweep (2026-08-30) |
| E18 | Proposition 30, proof (§5.2) | enumeration `C_0, …, C_(n-1)` with final step at `k = n-1` | assumes `Irr^F(E) ≠ ∅`; on the one-point factored set (`B = ∅`), `E = S` is nonempty with `Irr^F(E) = ∅`. The conclusion still holds (`Q^F_E` and the empty product are both `1`), and the Lean's `finprod` statement covers the case | codex sweep (2026-08-30) |

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
