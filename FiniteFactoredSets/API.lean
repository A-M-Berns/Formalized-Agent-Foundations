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

* **Partitions** are `Setoid S` (`dd:partition`); a block is `part b s`; the paper's
  finer/coarser order is Mathlib's `≤` on `Setoid` **with the paper's glyphs inverted**
  (`dd:order-flip`): the paper's `X ≤_S Y` is `Y ≤ X`, its `X ∨_S Y` is `X ⊓ Y`, its
  `⋁_S(C)` is `commonRefinement C = sInf C`, and `Dis_S`/`Ind_S` are `⊥`/`⊤`.
  `IsTrivialPartition` is the one-block partition (Definition 3).
* **Factorizations and factored sets**: `IsFactorization B` (Definition 10),
  `FactoredSet S` with fields `B` and `isFactorization` (Definition 11), the coordinate
  equivalence `FactoredSet.coord : S ≃ ((b : F.B) → Quotient b)`, `IsTrivialFactorization`,
  and `size`/`dim` (Definition 15, as `Cardinal`s, with `size_eq_mk`/`dim_eq_mk`).
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
`history`, `Orthogonal`, `Before` are unrestricted; every §3 *theorem* takes `[Finite F.B]`
(finite dimension, never finite `S`), because for an infinite basis the defining
intersection of `history` need not generate.  `Finite F.B` is found by instance search
whenever `Finite S` is; `Fintype F.B` is not (`Setoid` has no `DecidableEq`) — pass
`Fintype.ofFinite _` explicitly to `natCard_eq_prod` if the ℕ form of Proposition 7 is
wanted.  Nothing in this API needs `S` finite; the `Cardinal` forms of Propositions 7–9
(`size_eq_prod`, `isTrivialFactorization_of_isFactorization`, `dim_spec`) derive it from
their hypotheses.

## What this boundary excludes

`FiniteFactoredSets.Examples` — the constructed witnesses (`boolFS`, `coordFS`, `emptyFS`,
`unitFS`) and the §2.5/§3 vocabulary computed over them.  Import it explicitly when a
concrete factored set is useful; it is a regression fixture, not a dependency surface.
-/
