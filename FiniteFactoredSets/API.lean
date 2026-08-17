import FiniteFactoredSets.ConditionalOrthogonality
import FiniteFactoredSets.Factoring
import FiniteFactoredSets.Inference
import FiniteFactoredSets.InferenceExamples
import FiniteFactoredSets.Probability

/-!
# Finite Factored Sets consumer API

The supported downstream import for factored-set research is:

```lean
import FiniteFactoredSets.API
```

**Status: the formalization is in progress** (§2–§6 of Garrabrant, arXiv:2109.11513, are
formalized; §7 is not yet claimed).  This
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
  `chimera_basis` and `chimera_empty`, which is what a rewrite wants.  Since §3–§5 quantify
  over the *setwise* `chimeraImage`, the three setwise facts they run on are here too:
  `mem_chimeraImage_self` (clause 3 setwise — `u ∈ T` and `u ∈ R` put `u` in `χ^F_C(T,R)`),
  `chimeraImage_univ_univ` (`χ^F_C(S,S) = S`) and `chimeraImage_sdiff` (clause 4 setwise —
  `χ^F_{B∖C}(T,R) = χ^F_C(R,T)`).
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
  `degreeOf_poly_le` and `mem_vars_poly`.  `mono_basis_injective` is the separation
  underneath Proposition 26: distinct elements of `S` have distinct `B`-monomials.  A trap
  worth knowing before computing:
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
  nonempty), so a one-element `C` is in `Irr^F(E)` as soon as `χ^F_C(E,E) = E`.  Two
  working lemmas come with it: `subset_chimeraImage_self` (`E ⊆ χ^F_C(E,E)` always, so
  Definition 35's condition is only ever the `⊆` half) and `mem_iff_part_mem_vars`
  (Proposition 31's opening step, which recovers `C` from `poly^F_C(E)`: for `C ⊆ B`,
  `b ∈ B` and any `s ∈ E`, `b ∈ C ↔ [s]_b ∈ supp(poly^F_C(E))`).
* **Characteristic polynomials and orthogonality** (§5.3): `orthogonalGiven_tfae` is
  Lemma 3 (`CPO`), the bridge from §4's combinatorics to §5.4–§5.5's probability — for
  partitions `X, Y, Z` of `S`, the three conditions `X ⊥^F Y | Z`,
  `Q^F_z ∣ Q^F_{x∩z} · Q^F_{y∩z}` and `Q^F_z · Q^F_{x∩y∩z} = Q^F_{x∩z} · Q^F_{y∩z}` (both
  quantified over blocks `x ∈ X.classes`, `y ∈ Y.classes`, `z ∈ Z.classes`) are equivalent.
  The two directions the fundamental theorem consumes are isolated as
  `Q_mul_Q_eq_of_orthogonalGiven` (1 → 3) and `orthogonalGiven_of_Q_mul_Q_eq` (3 → 1), so
  a client who wants one of them does not have to project a `TFAE` — and does not hit the
  autoparam trap that `List.TFAE.out` has in term position.  The divisibility clause 2 is
  reachable only through the `TFAE`.  `eq_of_Q_eq` is the injectivity of `E ↦ Q^F_E` that
  the `2 → 1` direction runs on: a characteristic polynomial determines its set.
* **Probability distributions** (§5.4): `ProbDist S` (Definition 36) is the paper's
  *elementary* distribution under `dd:probability` — a structure bundling `P : Set S → ℝ`
  with `nonneg`, `empty` (`P ∅ = 0`), `univ` (`P Set.univ = 1`) and `additive` (finite
  additivity on `Disjoint` sets).  There is no measure theory here and nothing stands in
  for it; a `CoeFun` instance lets a client write `P E` for `P.P E`.  Note the paper's
  "given a finite set `S`" is carried by the *statements*, not the structure, so
  `ProbDist S` typechecks over any `S`.  Definition 36's additivity iterated is
  `ProbDist.eq_sum_singleton` (`P ↑T = ∑ s ∈ T, P {s}` for a `Finset T`) and
  `ProbDist.eq_sum_singleton_of_finite` (the `Set` form, taking `hE : E.Finite` as a
  hypothesis rather than an instance) — the sentence Proposition 32 quotes, and neither
  carries any finiteness of its own.  `FactoredSet.IsDistribution P` (Definition 37) is
  the predicate that makes it a distribution on the factored set:
  `P {s} = ∏ᶠ b ∈ F.B, P (part b s)` for every `s`.  `ProbDist.diracAt s₀` is the point
  mass, with `diracAt_apply` its unfolding, and `isDistribution_diracAt` says it is a
  distribution on **every** factored set of finite dimension — which is the general reason
  the family the next two statements quantify over is nonempty whenever `S` is, and the
  first distribution a client can reach for without building one.
  `isDistribution_iff` (Proposition 32)
  is the characterization by evaluation — `IsDistribution P ↔ ∀ E, P E = eval P.P (F.Q E)`,
  with `eval` Definition 29 and `F.Q` Definition 31 — which is the sentence that lets a
  client compute a probability by evaluating a polynomial and vice versa.
* **The fundamental theorem of finite factored sets** (§5.5):
  `orthogonalGiven_iff_forall_isDistribution` (Theorem 3) says `X ⊥^F Y | Z` holds if and
  only if for every distribution `P` on `F` and all blocks `x ∈ X.classes`,
  `y ∈ Y.classes`, `z ∈ Z.classes`, `P(x∩z) · P(y∩z) = P(x∩y∩z) · P(z)`.  Two things about
  the shape are worth knowing before using it.  The independence statement is the paper's
  own **division-free** form, so it is meaningful at `P z = 0` and needs no conditional
  probability; and it is an `iff`, so the theorem is a *test*: the forward direction turns
  a combinatorial orthogonality certificate into a numerical identity in every
  distribution, and the backward direction turns a single failing distribution — which is
  what `Examples` exhibits on the diagonal — into a refutation of conditional
  orthogonality.
* **Factored set models and temporal inference** (§6.1, `dd:model`): `Model Ω`
  (Definition 38) is a *model of a sample space* — a carrier `S` (an implicit field, so
  `M.S` is read off the model rather than supplied), a `FactoredSet S`, a map `f : S → Ω`,
  and a `Finite S` **field**.  That last point is the one to know before writing any §6
  statement: the paper's Definition 38 says *finite* factored set, so under `dd:model` the
  finiteness is part of the object and not a hypothesis on statements.  A client
  constructing a `Model` has it discharged by instance search at the construction site and
  never carries `[Finite S]` afterwards — and `Finite M.F.B` is then found by instance
  search too, which is what lets a §6 proof call the §3–§4 endpoints (Proposition 25, say)
  with no binder of its own.  `Model.finite` is a registered instance, so `M.S` is a
  `Finite` type wherever an `M : Model Ω` is in scope.
  Definition 39 has no declaration of ours: `f⁻¹(ω)` and `f⁻¹(E)` are `Set.preimage` and
  `f⁻¹(X)` for a partition `X` of `Ω` is `Setoid.comap M.f X`, whose blocks are exactly the
  nonempty preimages of blocks of `X` — the paper's set-builder verbatim.  `Model.pullback`
  is a named alias for that third clause, with `pullback_apply` (`M.pullback X s t ↔
  X (M.f s) (M.f t)`) the unfolding a client rewrites with; neither is a paper node.
  `OrthDatabase Ω` (Definition 40) is the pair of sets of triples, with `Orth` and `NotOrth`
  (Definition 41) their memberships — note `NotOrth` is a *positive assertion of the
  database*, not the negation of `Orth`, so a database may assert both (and then has no
  model) or neither (and then is not `Complete`).  `Models M D` (Definition 42),
  `Consistent` (Definition 43), `Complete` (Definition 44) and `OrthDatabase.Before`
  (Definition 45, the paper's `X <_D Y`) are the four predicates a temporal-inference
  client works in.  Three facts about their shape are worth having before use, each
  exhibited on a witness in `Examples`: `Consistent` is cheap on `O` alone (a one-point
  model satisfies every orthogonality assertion at once, since a zero-dimensional factored
  set has no factors), so it is `N` that constrains a model; `Consistent` and `Complete`
  are independent; and `Before` quantifies over models of `D`, so on an *inconsistent* `D`
  it holds of every pair vacuously — `X <_D Y` is an inference only once `D` is known
  consistent.  §6.2's two worked databases are `Example1.D` and `Example2.D`, with
  `Example1.X/Y/V` and `Example2.X/Y/Z/V` the partitions they are stated over, and
  Propositions 33–36 (`D_consistent`, `before_X_Y`, `before_X_Y_Z`) the paper's own
  consistency and inference results on them.

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

**§5 is where `[Finite S]` enters** — the first place the paper's standing "finite factored
set" does mathematical work rather than sitting in the preamble, and the reason
`dd:finiteness-minimal` draws its line here.  `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b` sums over
`E ⊆ S`, so with `E` infinite it is not the intended polynomial at all: as a `finsum` over
an infinite support it collapses to `0`, and divisibility, `Irr^F(E)` and irreducibility
have nothing to say about that junk value.

It does **not** enter uniformly, though, and the register below is the exact split.  The
§5 statements that carry no sum over `E` — Proposition 26's monomial bijection,
Proposition 29's minimal-element argument over subsets of `B`, and the squarefreeness of a
single monomial — need only the *dimension* to be finite, and are stated that way.

The count is **50 public §5 declarations**: 27 in `Polynomial.lean`, 9 in
`Factoring.lean`, 4 in `CharacteristicOrthogonality.lean` and 10 in `Probability.lean` —
the last ten being `ProbDist`, its `CoeFun` instance, `eq_sum_singleton`,
`eq_sum_singleton_of_finite`, `diracAt`, `diracAt_apply`, `IsDistribution`,
`isDistribution_diracAt`, `isDistribution_iff` and
`orthogonalGiven_iff_forall_isDistribution`.  Auto-generated
field projections (`ProbDist.P`, `.nonneg`, `.empty`, `.univ`, `.additive`) are not
counted, matching how `FactoredSet.B` is not counted in §2.  Recount mechanically before
editing this register; it has drifted three times.  The mechanical count is
`grep -cE '^(noncomputable )?(abbrev|def|lemma|theorem|structure|instance|class) |^instance :'`
per file — `private` and attribute-prefixed declarations do not start a line with the
keyword, which is exactly the filter wanted here.  Of those 50:

* `[Finite S]` is carried by **twenty-one** of them, and no others.  In §5.1: the paper
  endpoints `poly_union_chimeraImage` (Proposition 27) and `eq_C_mul_poly_of_dvd_Q`
  (Proposition 28); the `Q`-level supporting facts `Q_eq_sum`, `Q_ne_zero` and
  `vars_disjoint_of_mul_eq_Q`; and the monomial-level description of `poly^F_C(E)` —
  `poly_eq_sum_image`, `coeff_poly`, `mem_support_poly`, `poly_ne_zero`,
  `monos_eq_of_support_eq` and `mem_vars_poly`.  In §5.2: `Q_eq_finprod_poly_irr`
  (Proposition 30), `poly_dvd_Q`, `irreducible_poly_of_mem_irr` (Proposition 31) and
  `mem_iff_part_mem_vars`.  In §5.3: all four of `orthogonalGiven_tfae` (Lemma 3), its two
  isolated directions `Q_mul_Q_eq_of_orthogonalGiven` and `orthogonalGiven_of_Q_mul_Q_eq`,
  and `eq_of_Q_eq`.  In §5.4–§5.5:
  `isDistribution_iff` (Proposition 32) and
  `orthogonalGiven_iff_forall_isDistribution` (Theorem 3).  Five of those six §5.3–§5.5
  statements consume it for the same reason the §5.1 ones do — each has a `Q^F_E` in it,
  so an infinite `E` replaces the polynomial by the junk value `0`.  **Theorem 3 is the
  exception**: its statement mentions no polynomial at all, only `P(x∩z) · P(y∩z) =
  P(x∩y∩z) · P(z)`, and its `[Finite S]` is consumed entirely in the proof — by Lemma 3,
  whose statement does have a `Q^F_E`, and by the construction of the auxiliary
  distribution `P_f` from a positive assignment `f` (the sum `Q^F_S(f)` has to be a finite
  positive number).  So relaxing Theorem 3's hypothesis to `[Finite F.B]` is not a matter
  of tightening the proof: the resulting statement is literally Conjecture 1, the
  finite-*dimensional* fundamental theorem, which the paper leaves open and which this
  development's scope ruling puts in as a stated-and-deliberately-unproved `Prop` (see
  `KNOWLEDGE.md` for its status in the literature).
  Back in §5.1, two different things are being consumed, and it is worth keeping them
  apart.  `Q_eq_sum` and `poly_eq_sum_image` need `Set.toFinite E` *in the statement*, to
  write the `Finset`.  The rest need `E` finite in the proof — an infinite `E` sends the
  `finsum` to `0` and makes each of them false, not merely unproved.  The five
  monomial-layer lemmas additionally quantify over an **arbitrary** `C : Set (Setoid S)`
  with no `C ⊆ B` hypothesis, so they consume `Finite (Setoid S)` as well; that too comes
  from `Finite S`, via `instFiniteSetoid`.
* `[Finite F.B]` — finite dimension, `S` unrestricted — is carried by **seven**: `mono_eq_iff`,
  `mono_basis_injective`, `Q_eq_poly` (Proposition 26) and `degreeOf_Q_le` in §5.1,
  `irr_partition` (Proposition 29) and `irr_isPartition` in §5.2, and
  `isDistribution_diracAt` in §5.4.  Read the extra content
  honestly: over an infinite `E` the `Q`-level §5.1 statements are `0 = 0`-style identities
  between junk values, so what the relaxation really records is that their *proofs* never
  touch `|S|`.
  Proposition 29 is not degenerate in that way — `Irr^F(E)` is a genuine partition of `B`
  for every `E`, finite or not; nor is `mono_basis_injective`, which is about elements of
  `S` and not about `E` at all.  Nor is `isDistribution_diracAt`, whose binder is
  load-bearing in the strongest sense: over an infinite basis it is *false*, because
  Definition 37's `∏ᶠ b ∈ F.B` returns the junk value `1` as soon as infinitely many
  factors separate `s` from `s₀`, while `P {s}` is `0` there.
  Nothing in §5 carries `[Finite F.B]` on top of
  `[Finite S]`, because it does not have to: `Finite F.B` is synthesized from `Finite S` by
  instance search (see below), so these seven, and the §3–§4 endpoints the §5 proofs call,
  are supplied automatically to a client who has only `[Finite S]`.
* Finiteness is carried by **none** of the remaining twenty-two — every §5 definition,
  unfolding and elementary identity, plus a few proved statements.  `Poly`, `mono`, `monos`,
  `poly`, `Q`, `Q_eq_finsum_mono`, `poly_empty`, `mono_eq_prod`, `mono_congr`, `mono_union`,
  `irr`, `mem_irr`, `subset_chimeraImage_self` and the generic, upstreamable
  `coeff_add_mul_of_split` are
  finiteness-free, so a client may write down `Q^F_E` over an infinite `S` and get the junk
  value.  So are all three §5.4 *definitions* — `ProbDist`, its `CoeFun` instance, and
  `IsDistribution` — which is a deliberate `dd:probability` choice and not an oversight:
  the paper says "given a finite set `S`", but nothing in Definitions 36–37 needs it (the
  product `∏ᶠ b ∈ F.B` is a `finprod`, so an infinite basis gives `1` rather than a type
  error), and putting `[Finite S]` on the structure would force it onto every statement
  that merely *mentions* a distribution.  Finiteness sits on Proposition 32 and Theorem 3
  instead, where it is genuinely consumed.  So are the point mass `diracAt` and its
  unfolding `diracAt_apply`, which are a construction on an arbitrary `S` — the finiteness
  enters only at `isDistribution_diracAt`, one bullet up.  So are `eq_sum_singleton` and
  `eq_sum_singleton_of_finite`, which iterate Definition 36's additivity over a `Finset`
  and over a set carrying a `Set.Finite` *hypothesis*: the finiteness they need is the
  set's, not `S`'s.  So is `degreeOf_poly_le`: every variable has
  degree at most one in `poly^F_C(E)`
  for `C ⊆ B` whatever the cardinalities, because both junk values respect the bound (an
  infinite `C` gives the empty-product `1`, an infinite monomial set the empty-sum `0`).
  (`mono_eq_prod` and `mono_union` take a `Set.Finite` *hypothesis* on the factor set rather
  than an instance, which is a different thing: they are statements about a finite `C`, over
  an arbitrary `S`.)

`Finite F.B` is found by instance search whenever `Finite S` is.  `Fintype F.B` is not —
and not for the reason one first suspects: under `open scoped Classical`, `Setoid` does
have a `DecidableEq`, and `Fintype ↥({b₀, b₁} : Set (Setoid S))` is synthesized by
`Set.fintypeInsert`.  What blocks it is that a concrete basis is a non-reducible `def`,
which instance search will not unfold to find the `insert`/`singleton` structure
underneath.  Pass `Fintype.ofFinite _` explicitly — and have it in scope at *statement*
elaboration time — if the ℕ form of Proposition 7 (`natCard_eq_prod`) is wanted.

**§6 carries no finiteness hypothesis anywhere**, and that is not a relaxation but a
relocation: Definition 38 says *finite* factored set, so `dd:model` puts `Finite S` in the
structure as a field.  Every §6 declaration — `Model`, `pullback`, `pullback_apply`,
`OrthDatabase`, `Orth`, `NotOrth`, `Models`, `Consistent`, `Complete`,
`OrthDatabase.Before`, and §6.2's databases and propositions — is stated with no binder of
its own, because the models it quantifies over each carry their own.  Read a §6 statement
accordingly: "for all models" already means "for all *finite* factored sets with a map to
`Ω`", and the sample space `Ω` itself is unconstrained.

## What this boundary excludes

`FiniteFactoredSets.Examples` — the constructed witnesses (`boolFS`, `coordFS`, `emptyFS`,
`unitFS`, the distributions `uniform`, `biased`, `diagDist`, `unitDist` and
`boolUniform`, and the §6 models `coordModel`, `boolModel`, `fstModel`, `pointModel` with
the databases `emptyDB`, `contradictoryDB`, `totalDB`, `nonconstDB`, `coordDB`) and the
§2.5, §3, §4, §5 and §6 vocabulary computed over them.  Import it
explicitly when a concrete factored set or model is useful; it is a regression fixture, not
a dependency surface.  §6.2's `Example1` and `Example2` are *not* excluded — they are the
paper's own numbered examples and part of this boundary.
-/
