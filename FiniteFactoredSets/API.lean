import FiniteFactoredSets.ConditionalOrthogonality
import FiniteFactoredSets.Factoring

/-!
# Finite Factored Sets consumer API

The supported downstream import for factored-set research is:

```lean
import FiniteFactoredSets.API
```

**Status: the formalization is in progress** (§2–§4 and §5.1–§5.2 of Garrabrant,
arXiv:2109.11513, are formalized; §5.3 onwards and §6–§7 are not yet claimed).  This
boundary is therefore an *incremental* consumer surface: it is stable in shape but grows
as sections land.  What is here is supported now; consult
`FiniteFactoredSets/README.md` for the exact trust surface.

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
* **Characteristic polynomials** (§5.1): `Poly S` (Definition 28) is
  `MvPolynomial (Set S) ℝ` under `dd:poly` — an `abbrev`, so the whole `MvPolynomial` API
  applies to it unchanged, and a block `part b s` is a *variable* of the ring verbatim
  (`MvPolynomial.X (part b s)`).  Definitions 29 and 30 have no declaration of ours:
  evaluation `p(f)` is `MvPolynomial.eval f p` and the support `supp(p)` is
  `MvPolynomial.vars p`.  `FactoredSet.Q E` is the characteristic polynomial `Q^F_E`
  (Definition 31), with `Q_eq_finsum_mono` unfolding it.  **`mono C s`, `monos C E` and
  `poly C E` (Definitions 32–34) are namespace-level and take no `F`** — the paper's
  superscript `F` on them is vestigial, exactly as on `size` (`FiniteFactoredSets.mono`,
  not `FactoredSet.mono`; write `poly C E`, never `F.poly C E`).  `Q` and
  `irr` do take `F`.  The endpoints are `Q_eq_poly` (Proposition 26:
  `Q^F_E = poly^F_B(E)`), `poly_union_chimeraImage` (Proposition 27, the paper's
  `factor1`) and `eq_C_mul_poly_of_dvd_Q` (Proposition 28, `factor2` — every divisor of
  `Q^F_E` is `r · poly^F_C(E)` for some real `r` and some `C ⊆ B`), with the supporting
  `degreeOf_Q_le`, `Q_ne_zero`, `vars_disjoint_of_mul_eq_Q` and the upstreamable generic
  `coeff_add_mul_of_split`.  Rewriting glue: `Q_eq_sum` and `poly_eq_sum_image` turn the
  `finsum`/`finprod` definitions into `Finset` sums, and `mono_eq_prod`, `mono_congr`,
  `mono_union`, `poly_empty` are the elementary `mono`/`poly` identities.  The
  monomial-level description of `poly^F_C(E)` is exposed too, because §5.2 and any client
  computing with these polynomials needs it: `coeff_poly` (every coefficient is `0` or `1`,
  and `1` exactly on `monos^F_C(E)`), `mem_support_poly`, `poly_ne_zero`,
  `monos_eq_of_support_eq` (the monomial set is recoverable from the polynomial), and — for
  `C ⊆ B`, where Corollary 1 makes the monomials squarefree — `mono_eq_iff`,
  `degreeOf_poly_le` and `mem_vars_poly`.  A trap worth knowing before computing:
  `monos C E` is an *image*, so coincident monomials collapse and `poly^F_C(E)` can have
  strictly fewer summands than `E` has elements — Proposition 26 is the statement that this
  does not happen at `C = B`.
* **Factoring characteristic polynomials** (§5.2): `FactoredSet.irr E` is `Irr^F(E)`
  (Definition 35), the minimal nonempty `C ⊆ B` with `χ^F_C(E,E) = E`, unfolded by
  `mem_irr`.  `irr_partition` (Proposition 29) says those sets partition `B`, with
  `irr_isPartition` restating it in §4's vocabulary as a `Subpartition` of `Setoid S`
  with domain `B`; `Q_eq_finprod_poly_irr` (Proposition 30) factors
  `Q^F_E = ∏_{C ∈ Irr^F(E)} poly^F_C(E)`, with `poly_dvd_Q` its divisibility corollary; and
  `irreducible_poly_of_mem_irr`
  (Proposition 31) says each factor is `Irreducible` in `Poly S` — Mathlib's
  `Irreducible`, whose units over `ℝ` are the nonzero constants, which is the paper's
  "no factorization into two polynomials of nonempty support".  Definition 35's minimality
  clause is vacuous at a singleton (`∅` is the only strict subset of `{b}`, and it is not
  nonempty), so a one-element `C` is in `Irr^F(E)` as soon as `χ^F_C(E,E) = E`.

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

Hypotheses of the form `[Finite S]` are not global here either, and through §2–§4 exactly
one appears, where the paper's own statement has it: on `finite_basis_of_finite`
(Proposition 6, which *derives* `Finite F.B` from it).  The `Cardinal` forms of
Propositions 7–9 (`size_eq_prod`, `isTrivialFactorization_of_isFactorization`,
`dim_spec`) take none, deriving what finiteness they need from their own hypotheses.

**§5 is where `[Finite S]` genuinely enters** — the first place the paper's standing
"finite factored set" is doing mathematical work rather than sitting in the preamble, and
the reason `dd:finiteness-minimal` draws its line here.  `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B}
[s]_b` sums over `E ⊆ S`, so with `S` infinite it is not a polynomial at all: as a
`finsum` over an infinite support it collapses to `0`, and divisibility, `Irr^F(E)` and
irreducibility have nothing to say about that junk value.  The exact carriers:

* `[Finite S]` **is** carried by nineteen public §5 statements, and no others.  In §5.1:
  the paper endpoints `Q_eq_poly` (Proposition 26), `poly_union_chimeraImage`
  (Proposition 27) and `eq_C_mul_poly_of_dvd_Q` (Proposition 28); the `Q`-level supporting
  facts `Q_eq_sum`, `degreeOf_Q_le`, `Q_ne_zero` and `vars_disjoint_of_mul_eq_Q`; and the
  monomial-level description of `poly^F_C(E)` — `poly_eq_sum_image`, `coeff_poly`,
  `mem_support_poly`, `poly_ne_zero`, `monos_eq_of_support_eq`, `degreeOf_poly_le` and
  `mem_vars_poly`.  In §5.2: `irr_partition` (Proposition 29), `irr_isPartition`,
  `Q_eq_finprod_poly_irr` (Proposition 30), `poly_dvd_Q` and
  `irreducible_poly_of_mem_irr` (Proposition 31).  All of these quantify over a *subset*
  `E ⊆ S`, and it is `E`'s finiteness — reached through `Set.toFinite` — that they consume.
* Exactly one public §5 statement carries `[Finite F.B]` instead: `mono_eq_iff`, which
  compares two `C`-monomials for `C ⊆ B` and so needs only the *dimension* to be finite.
  Nothing in §5 carries `[Finite F.B]` on top of `[Finite S]`, because it does not have to:
  `Finite F.B` is synthesized from `Finite S` by instance search (see below), so both
  `mono_eq_iff` and the §3–§4 endpoints these proofs call are supplied automatically to a
  client who has `[Finite S]`.
* Finiteness is **not** carried by any §5 *definition*, unfolding or elementary identity:
  `Poly`, `mono`, `monos`, `poly`, `Q`, `Q_eq_finsum_mono`, `poly_empty`, `mono_eq_prod`,
  `mono_congr`, `mono_union`, `irr`, `mem_irr` and the generic, upstreamable
  `coeff_add_mul_of_split` are all finiteness-free — thirteen of them — so a client may
  write down `Q^F_E` over an infinite `S` and gets the junk value, with no theorem of ours
  applying to it.  (`mono_eq_prod` and `mono_union` take a `Set.Finite` *hypothesis* on the
  factor set rather than an instance, which is a different thing: they are statements about
  a finite `C`, over an arbitrary `S`.)

`Finite F.B` is found by instance search whenever `Finite S` is.  `Fintype F.B` is not —
and not for the reason one first suspects: under `open scoped Classical`, `Setoid` does
have a `DecidableEq`, and `Fintype ↥({b₀, b₁} : Set (Setoid S))` is synthesized by
`Set.fintypeInsert`.  What blocks it is that a concrete basis is a non-reducible `def`,
which instance search will not unfold to find the `insert`/`singleton` structure
underneath.  Pass `Fintype.ofFinite _` explicitly — and have it in scope at *statement*
elaboration time — if the ℕ form of Proposition 7 (`natCard_eq_prod`) is wanted.

## What this boundary excludes

`FiniteFactoredSets.Examples` — the constructed witnesses (`boolFS`, `coordFS`, `emptyFS`,
`unitFS`) and the §2.5, §3, §4 and §5.1–§5.2 vocabulary computed over them.  Import it
explicitly when a concrete factored set is useful; it is a regression fixture, not a
dependency surface.
-/
