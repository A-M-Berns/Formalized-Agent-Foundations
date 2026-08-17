import FiniteFactoredSets.ConditionalOrthogonality

/-!
# Finite Factored Sets consumer API

The supported downstream import for factored-set research is:

```lean
import FiniteFactoredSets.API
```

**Status: the formalization is in progress** (§2–§4 of Garrabrant, arXiv:2109.11513, are
formalized; §5–§7 are not yet claimed).  This boundary is therefore an *incremental*
consumer surface: it is stable in shape but grows as sections land.  What is here is
supported now; consult `FiniteFactoredSets/README.md` for the exact trust surface.

## Vocabulary

Everything lives in the `FiniteFactoredSets` namespace, with the factored-set operations
under `FiniteFactoredSets.FactoredSet` (use `open FiniteFactoredSets` and dot notation on
`F : FactoredSet S`).

* **Partitions** are `Setoid S` (`dd:partition`); a block is `part b s` (Definition 4);
  the paper's finer/coarser order is Mathlib's `≤` on `Setoid` **with the paper's glyphs
  inverted** (`dd:order-flip`): the paper's `X ≤_S Y` is `Y ≤ X`, its `X ∨_S Y` is `X ⊓ Y`,
  its `⋁_S(C)` is `commonRefinement C = sInf C` — whose defining property is
  `commonRefinement_iff` — and `Dis_S`/`Ind_S` are `⊥`/`⊤`.  `IsTrivialPartition` is the
  one-block partition (Definition 3).  Propositions 1 and 2 are `equivalence_setoid` and
  `bot_le_and_le_top`, and `classes_top` names the blocks of `Ind_S` over a nonempty `S`
  (a single block; Mathlib has no `Setoid.classes_top`).
* **Factorizations and factored sets**: `IsFactorization B` (Definition 10),
  `FactoredSet S` with fields `B` and `isFactorization` (Definition 11), the coordinate
  equivalence `FactoredSet.coord : S ≃ ((b : F.B) → Quotient b)`, `IsTrivialFactorization`,
  and `size`/`dim` (Definition 15, as `Cardinal`s, with the `@[simp]` unfoldings
  `size_eq_mk`/`dim_eq_mk` and `dim_eq_zero_iff`).  The §2.2–§2.4 theorems are
  `FactoredSet.eq_of_forall_rel` (Proposition 3), `isFactorization_iff_existsUnique`
  (Theorem 1), `FactoredSet.eq_of_part_eq` (Corollary 1),
  `existsUnique_trivialFactorization` (Proposition 5), and
  `FactoredSet.finite_basis_of_finite` (Proposition 6).  `isFactorization_empty_iff` and
  `isFactorization_singleton_bot_iff` are the two degenerate-basis certificates a client
  reaches for when building a concrete `FactoredSet`.
* **Chimera functions**: `chimeraFun`, `chimera C s t`, `chimeraImage C T R` and their
  specification `chimera_spec` (Proposition 4's eleven clauses) with the pointwise
  `chimera_rel_of_mem`/`chimera_rel_of_notMem` and `coord_chimera`.  Clauses 3–8, 10 and 11
  are also available one at a time as `chimera_self`, `chimera_sdiff`, `chimera_union`,
  `chimera_inter`, `chimera_left_idem`, `chimera_right_idem`, `chimera_left_comm`,
  `chimera_basis` and `chimera_empty`, which is what a rewrite wants.
* **Generation and history** (§3.1–§3.2): `Generates C X` (Definition 16),
  `generates_tfae` (Proposition 10; `generates_iff_rel` and `generates_iff_sInf_le` are its
  clauses 6 and 7 isolated), `generates_spec` (Proposition 11), `history X`
  (Definition 17), `history_isLeast` (Proposition 12), `history_spec` (Proposition 13),
  and the workhorse bridges `generates_iff_history_subset` and `le_iff_history_subset`.
* **Orthogonality and time** (§3.3–§3.4): `Orthogonal`, `Entangled` (Definition 18),
  `Before`, `StrictlyBefore` (Definition 19), and Propositions 14–19
  (`orthogonal_iff_exists`, `orthogonal_spec`, `before_iff_forall_sInf`,
  `before_iff_forall_orthogonal`, `before_spec`, `history_eq_setOf_before`), with the
  unfolding lemmas `orthogonal_def`, `orthogonal_iff_forall_notMem`, `entangled_iff`,
  `before_def`, `strictlyBefore_def`, `StrictlyBefore.before`.
* **Subpartitions** (§4.1): `Subpartition S` (Definition 20) is a *partial equivalence
  relation* on `S` under `dd:subpartition`, not a `Σ E, Setoid E`; `X.dom` (Definition 21)
  is `{s | X s s}`, `X.classes` its blocks, and `X.restrict E` (Definition 22) the paper's
  `X|E`.  The bridge to partitions is `ofSetoid : Setoid S → Subpartition S` (total PERs),
  with `ofSetoidOn E Y : Subpartition S` for a partition `Y : Setoid E` of a client's own
  subset and `toSetoid : Setoid X.dom` the inverse; `ofSetoidOn_toSetoid` and
  `toSetoid_ofSetoidOn` are the two round trips, `dom_ofSetoidOn` computes
  `(ofSetoidOn E Y).dom = E`, and `ofSetoidOn_univ` is the compatibility with `ofSetoid`
  on `Set.univ`.  `indiscrete E` is `Ind_E`; the order is Mathlib's
  again (`X ⊓ Y` is the paper's `X ∨_E Y`, `Y ≤ X` its `X ≤_E Y`), and `Subset` is the
  paper's inclusion *as sets of blocks*, which is a different relation from `≤`.  The
  restriction glue a client actually reaches for is `restrict_univ`,
  `restrict_restrict_of_subset`, `dom_restrict_ofSetoid`, `part_restrict_ofSetoid`,
  `restrict_ofSetoid_inf` — that one being `(X ∨_S Y)|E = (X|E) ∨_E (Y|E)` — and
  `restrict_inter_subset_restrict_inf`, all of them in `Subpartition.lean`.  Generation is
  `GeneratesSub C X` (Definition 23) with `generatesSub_tfae` (Proposition 20; the working
  form is `generatesSub_iff_rel`), `generatesSub_spec` (Proposition 21), and
  `generatesSub_ofSetoid` identifying it with `Generates` on partitions of `S`.
* **History of a subpartition** (§4.2): `historySub X` (Definition 24),
  `historySub_isLeast_and_eq_history` (Proposition 22 — both halves: least generating
  subset, and agreement with `history` on `ofSetoid X`), `historySub_spec`
  (Proposition 23), and the two facts Theorem 2 runs on,
  `historySub_restrict_part_eq` (Lemma 1) and `historySub_inf_eq` (Lemma 2), together with
  `generatesSub_historySub` and `generatesSub_iff_historySub_subset`.
* **Conditional orthogonality** (§4.3): `OrthogonalSub`, `BeforeSub`, `StrictlyBeforeSub`
  (Definition 25's three clauses on subpartitions), `OrthogonalGivenSet X Y E`
  (Definition 26, the paper's `X ⊥^F Y | E`) and `OrthogonalGiven X Y Z` (Definition 27,
  quantified over `Z.classes`).  The endpoints are
  `orthogonal_iff_orthogonalGiven_top` (Proposition 24: `X ⊥^F Y ↔ X ⊥^F Y | Ind_S`),
  `orthogonalGiven_semigraphoid` (Theorem 2: symmetry, decomposition, weak union,
  contraction, composition, in that order — the paper's `∨_S` being `⊓`), and
  `orthogonalGiven_self_iff` (Proposition 25: `X ⊥^F X | Y ↔ Y ≤ X`).  Unfolding and
  bridging lemmas: `orthogonalSub_def`, `beforeSub_def`, `strictlyBeforeSub_def`,
  `StrictlyBeforeSub.beforeSub`, `orthogonalSub_iff_forall_notMem`,
  `orthogonalSub_ofSetoid`, `beforeSub_ofSetoid`, `orthogonalGivenSet_def`,
  `orthogonalGiven_def`, and `historySub_restrict_inf`.

## Finiteness

`FactoredSet` carries no finiteness at all (`dd:finiteness-minimal`).  The definitions of
`history`, `Orthogonal`, `Before` are unrestricted, and so are Propositions 10 and 11
(`generates_tfae`, `generates_spec`), which take no finiteness hypothesis either.
`[Finite F.B]` — finite *dimension*, never finite `S` — appears exactly where the paper's
proofs use it, from Proposition 12 (`history_isLeast`) onwards: the history is shown to
generate by writing it as a *finite* intersection of generating subsets, and that step
genuinely fails for an infinite basis.

§4 keeps the same boundary, and it falls in the same place: **all of §4.1 is
finiteness-free** — `GeneratesSub`, `generatesSub_ofSetoid`, `generatesSub_iff_rel`,
`generatesSub_tfae` (Proposition 20) and `generatesSub_spec` (Proposition 21) take no
`Finite` hypothesis, exactly as Propositions 10 and 11 do not.  `[Finite F.B]` reappears at
Definition 24's well-definedness and stays: it is carried by
`historySub_isLeast_and_eq_history` (Proposition 22), `generatesSub_historySub`,
`generatesSub_iff_historySub_subset`, `historySub_spec` (Proposition 23),
`historySub_restrict_part_eq` (Lemma 1), `historySub_inf_eq` (Lemma 2),
`historySub_restrict_inf`, `orthogonalSub_ofSetoid`, `beforeSub_ofSetoid`, and all three
§4.3 endpoints — `orthogonal_iff_orthogonalGiven_top`, `orthogonalGiven_semigraphoid`,
`orthogonalGiven_self_iff`.  The `historySub` *definition*, Definition 25's three
relations, Definitions 26 and 27, their unfolding lemmas, and the `Subpartition`
restriction glue carry none.

Hypotheses of the form `[Finite S]` are never global here: one appears only where the
paper's own statement has it, on `finite_basis_of_finite` (Proposition 6, which *derives*
`Finite F.B` from it).  The `Cardinal` forms of Propositions 7–9 (`size_eq_prod`,
`isTrivialFactorization_of_isFactorization`, `dim_spec`) take none, deriving what
finiteness they need from their own hypotheses.

`Finite F.B` is found by instance search whenever `Finite S` is.  `Fintype F.B` is not —
and not for the reason one first suspects: under `open scoped Classical`, `Setoid` does
have a `DecidableEq`, and `Fintype ↥({b₀, b₁} : Set (Setoid S))` is synthesized by
`Set.fintypeInsert`.  What blocks it is that a concrete basis is a non-reducible `def`,
which instance search will not unfold to find the `insert`/`singleton` structure
underneath.  Pass `Fintype.ofFinite _` explicitly — and have it in scope at *statement*
elaboration time — if the ℕ form of Proposition 7 (`natCard_eq_prod`) is wanted.

## What this boundary excludes

`FiniteFactoredSets.Examples` — the constructed witnesses (`boolFS`, `coordFS`, `emptyFS`,
`unitFS`) and the §2.5/§3 vocabulary computed over them.  Import it explicitly when a
concrete factored set is useful; it is a regression fixture, not a dependency surface.
-/
