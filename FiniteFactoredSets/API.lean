import FiniteFactoredSets.Orthogonality

/-!
# Finite Factored Sets consumer API

The supported downstream import for factored-set research is:

```lean
import FiniteFactoredSets.API
```

**Status: the formalization is in progress** (§2–§3 of Garrabrant, arXiv:2109.11513, are
formalized; §4–§7 are not yet claimed).  This boundary is therefore an *incremental*
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
  `bot_le_and_le_top`.
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
  `chimera_rel_of_mem`/`chimera_rel_of_notMem` and `coord_chimera`.
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

## Finiteness

`FactoredSet` carries no finiteness at all (`dd:finiteness-minimal`).  The definitions of
`history`, `Orthogonal`, `Before` are unrestricted, and so are Propositions 10 and 11
(`generates_tfae`, `generates_spec`), which take no finiteness hypothesis either.
`[Finite F.B]` — finite *dimension*, never finite `S` — appears exactly where the paper's
proofs use it, from Proposition 12 (`history_isLeast`) onwards: the history is shown to
generate by writing it as a *finite* intersection of generating subsets, and that step
genuinely fails for an infinite basis.

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
