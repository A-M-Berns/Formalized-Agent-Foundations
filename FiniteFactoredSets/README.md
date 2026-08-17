# Finite Factored Sets — trust surface

Formalization of Scott Garrabrant, *Temporal Inference with Finite Factored Sets*
([arXiv:2109.11513](https://arxiv.org/abs/2109.11513)). The paper is the specification:
`notes/2109.11513-main.tex` is the exact arXiv source and `notes/2109.11513.pdf` the
matching PDF.

**Status: in progress — §2, §3, §4 and §5.1–§5.2 formalized (63 of the 96 in-scope nodes
carry a Lean declaration of ours; two more, §5.1's Definitions 29 and 30, are rendered by
Mathlib vocabulary and are tabulated below with the six such nodes of §2.1), with
non-vacuity discharged by construction: four factored sets are built, and the §2.5, §3,
§4 and §5.1–§5.2 vocabulary — `size`, `dim`, `Generates`, `history`, `Orthogonal`,
`Entangled`, `Before`, `StrictlyBefore`, `Subpartition`, `GeneratesSub`, `historySub`,
`OrthogonalSub`, `OrthogonalGivenSet`, `OrthogonalGiven`, `Q`, `mono`, `monos`, `poly`,
`irr` — is computed over them rather than merely defined.**
Nothing here is complete, and this file says what is claimed and what is not.

## What is claimed

| § | Content | Nodes |
|---|---|---|
| 2.1 | Partitions, their order, common refinement | Definitions 3, 4, 8; Propositions 1, 2 |
| 2.2 | Factorizations and factored sets | Definitions 10, 11; Proposition 3 |
| 2.3 | The chimera function | Theorem 1; Corollary 1; Definitions 12, 13; Proposition 4 |
| 2.4 | Trivial factorizations | Definition 14; Proposition 5 |
| 2.5 | Finite factored sets | Definition 15; Propositions 6, 7, 8, 9 |
| 3.1 | Generating a partition with factors | Definition 16; Propositions 10, 11 |
| 3.2 | History | Definition 17; Propositions 12, 13 |
| 3.3 | Orthogonality | Definition 18; Propositions 14, 15 |
| 3.4 | Time | Definition 19; Propositions 16, 17, 18, 19 |
| 4.1 | Subpartitions, restriction, generating a subpartition | Definitions 20, 21, 22, 23; Propositions 20, 21 |
| 4.2 | History of a subpartition | Definition 24; Propositions 22, 23; Lemmas 1, 2 |
| 4.3 | Conditional orthogonality, the semigraphoid axioms | Definitions 25, 26, 27; Propositions 24, 25; Theorem 2 |
| 5.1 | The polynomial ring, characteristic polynomials, `factor1` and `factor2` | Definitions 28, 31, 32, 33, 34; Propositions 26, 27, 28 |
| 5.2 | Factoring characteristic polynomials into irreducibles | Definition 35; Propositions 29, 30, 31 |

§5.1's Definitions 29 (evaluation) and 30 (support) are the two nodes of these sections
with no declaration of ours; they are in the Mathlib-rendered table below, which is why
the rows above sum to 63 rather than 65.

Five of those nodes are stated in halves — four in two, one in three — and every half is
carried, so those nodes appear in the inventory more than once. The 63 nodes above are
cited by 69 annotations:

| Node | Carriers |
|---|---|
| Definition 13 (chimera) | `chimera` is `χ^F_C(s,t)`; `chimeraImage` is the setwise `χ^F_C(T,R)` that §3 onward quantifies over |
| Definition 15 (size, dimension) | `size` is `\|S\|`; `dim` is `dim(F)`. Its third sentence — "finite" / "finite-dimensional" — has no carrier at all: under `dd:finiteness-minimal` those are the typeclass hypotheses `[Finite S]` and `Finite F.B`, and they now have a row in the Mathlib-rendered table below, `[Finite S]` having become load-bearing at §5.1 |
| Definition 18 (orthogonality) | `Orthogonal` is `X ⊥^F Y`; `Entangled` is the second sentence's negation of it |
| Definition 19 (time) | `Before` is `≤^F`; `StrictlyBefore` is `<^F` |
| Definition 25 (subpartition orthogonality and time) | three clauses, three carriers: `OrthogonalSub` is `⊥^F` on subpartitions, `BeforeSub` is `≤^F`, `StrictlyBeforeSub` is `<^F` |

Every one of those carries a `Paper node:` docstring line and an entry in
`AxiomAudit.lean`'s FFS-INVENTORY block, checked both ways by
`scripts/check-finite-factored-sets-nodes.py`. Zero `sorry`; every endpoint is clean at
`[propext, Classical.choice, Quot.sound]`.

## What is not claimed

§5.3 onwards (characteristic polynomials and orthogonality, probability, and the
Fundamental Theorem), §6 (inferring time), and §7's in-scope material have **no Lean
statements yet**. The trust-surface guide reports the shortfall by kind rather than
listing it.

An earlier feasibility spike proved several §5 results — the disjoint-support coefficient
lemma behind Proposition 28, multilinearity of `Q^F_E`, and the Fundamental Theorem's
"vanishes on an open set" step — against a throwaway structure. That file has been
retired rather than kept alongside the real one; the code is preserved at commit
`19a2254` and its findings are in `notes/spike-2026-08-15.md`. The first of the three has
been re-landed against `FactoredSet` as `coeff_add_mul_of_split` in `Polynomial.lean`
(generic in the index type, and upstreamable); the third belongs to §5.3 and is still to
come.

**Scope (settled 2026-08-16): 96 of 98 nodes.** In: §1–§6 in full, §7's Definitions
46–50, and Conjecture 1 stated as a `Prop` and deliberately not proved. Out: Examples 3
and 4 only — both concern *infinite* factored sets, the case the paper itself expects the
fundamental theorem to fail in (Example 3 is its intended counterexample).

A consequence worth knowing before reading any §3–§4 statement: **finiteness is kept
minimal.** `FactoredSet` carries no `Fintype S`, and §3–§4 are stated with `Finite B`
only, because none of that material touches polynomials. `|S|` finite enters at §5, where
`Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b` stops being the intended polynomial once `E` is
infinite — the `finsum` collapses to `0`.

It does not enter across the board, and it would be wrong to read §5 as a
finite-`S`-only section. Of the 33 public §5 declarations, fourteen carry `[Finite S]`,
five carry `[Finite F.B]` only, and fourteen carry no finiteness at all. So there are
statements of ours that *do* apply over an infinite `S`, and a client working there gets
more than the definitions:

* with no hypothesis whatever — `poly_empty`, `mono_eq_prod`, `mono_congr`, `mono_union`,
  `Q_eq_finsum_mono`, `mem_irr`, the upstreamable `coeff_add_mul_of_split`, and
  `degreeOf_poly_le` (every variable has degree at most one in `poly^F_C(E)` for `C ⊆ B`,
  junk values included);
* with `Finite B` alone — `mono_eq_iff`, `Q_eq_poly` (Proposition 26), `degreeOf_Q_le`,
  and Proposition 29 with its §4 restatement (`irr_partition`, `irr_isPartition`), so
  `Irr^F(E)` partitions `B` over an infinite `S` too.

Of those, the three §5.1 `Finite B` statements are degenerate over an infinite `E` — both
sides are junk values — while Proposition 29 is not. The rest of §5 genuinely needs `|S|`
finite: an infinite `E` makes `Q_ne_zero`, `coeff_poly`, `mem_vars_poly` and Propositions
27, 28, 30 and 31 false rather than merely unproved. The exact per-declaration register,
with what each hypothesis is consumed for, is the "Finiteness" section of `API.lean`. That
boundary is also what makes Conjecture 1 — the finite-*dimensional* fundamental theorem —
statable here at all. See `KNOWLEDGE.md` for its status in the literature.

## Nodes rendered by Mathlib vocabulary, with no declaration of ours

These are *not* gaps in coverage but they are also not endpoints, so they are recorded
here rather than inventoried — there is no declaration of this project's to axiom-check.

| Paper node | Rendered as | Tag |
|---|---|---|
| Definition 1 (disjoint union `⊔S`) | absorbed into `Setoid` / the dependent product; it appears in the paper only inside Definitions 2 and 9 | `dd:partition`, `dd:quotient` |
| Definition 2 (partition) | `Setoid S` | `dd:partition` |
| Definition 5 (`∼_X`) | the setoid relation | `dd:partition` |
| Definition 6 (finer / coarser) | Mathlib's `≤` on `Setoid` | `dd:order-flip` |
| Definition 7 (`Dis_S`, `Ind_S`) | `⊥`, `⊤` | `dd:order-flip` |
| Definition 9 (`∏(B)`) | the dependent product `(b : B) → Quotient b` | `dd:quotient` |
| Definition 15, third sentence (finite / finite-dimensional factored set) | the typeclass hypotheses `[Finite S]` and `Finite F.B`, carried per statement | `dd:finiteness-minimal` |
| Definition 29 (`p(f)`, evaluation) | `MvPolynomial.eval f p` | `dd:poly` |
| Definition 30 (`supp(p)`, support) | `MvPolynomial.vars p` | `dd:poly` |
| Proposition 31's "irreducible" (no factorization into two polynomials of nonempty support) | Mathlib's `Irreducible` in `Poly S`; over `ℝ` its units are the nonzero constants, so the two readings coincide | `dd:poly` |
| Proposition 2, first sentence (`≥_S` is a partial order) | Mathlib's `PartialOrder (Setoid S)` instance | `dd:order-flip` |

Six of those rows are whole nodes (Definitions 1, 2, 5, 6, 7, 9); the other four are
*partial* entries — a clause of a node whose remaining clauses do have a carrier, recorded
here so that nothing in a printed node is silently unaccounted for:

* **Proposition 2, first sentence.** `bot_le_and_le_top` carries the `Proposition 2`
  annotation but states only the proposition's second sentence (the `Dis`/`Ind` bounds).
  Anyone reading the trust-surface card will see the full printed proposition beside a Lean
  statement covering half of it; that is why the row is here.
* **Definition 15, third sentence.** "Finite" and "finite-dimensional" are not a
  definition this library makes: under `dd:finiteness-minimal` they are the typeclass
  hypotheses `[Finite S]` and `Finite F.B`, carried on the individual statements that use
  them rather than bundled into a `FiniteFactoredSet` structure. §3–§4 carry `Finite F.B`
  only; §5.1–§5.2 carry whichever of the two each statement's proof consumes, which is
  `[Finite S]` for most of them but `Finite F.B` for Propositions 26 and 29 (see the
  finiteness paragraph above and `API.lean`'s register).
* **Definition 29 and Definition 30.** Evaluation and support are `MvPolynomial.eval` and
  `MvPolynomial.vars` — whole nodes, but of §5.1 rather than §2.1.
* **Proposition 31's word "irreducible."** The proposition itself is carried
  (`irreducible_poly_of_mem_irr`); it is the *meaning* of the word that is Mathlib's, and
  the two readings agreeing is a fact about `ℝ` worth stating rather than assuming.

None of this is to be confused with the five multi-carrier nodes tabulated above
(Definitions 13, 15, 18, 19, 25): those are nodes stated in halves, with *every* half
carried, not nodes stated in part. Definition 15 appears in both lists, because two of its
sentences have carriers and the third does not.

## Modeling decisions

Defined in full in the glossary at `FiniteFactoredSets.lean`. In brief:

* **`dd:partition`** — partitions are `Setoid`s, as in `CartesianFrames/`. Consequence
  worth stating: Proposition 1 (that `∼_X` is an equivalence relation) is discharged by
  the setoid's own `iseqv` rather than proved. The paper's content is real; under this
  modeling it is free.
* **`dd:order-flip`** — the paper's order glyphs are *inverted* relative to Mathlib's.
  The paper writes `X ≥_S Y` for "`X` is finer than `Y`", so the paper's `≥_S` is
  Mathlib's `≤`; Definition 8's common refinement `⋁_S(C)` — a join in the paper's
  notation — is Mathlib's `sInf`. The library uses Mathlib's convention throughout and
  never introduces the paper's glyphs.
* **`dd:quotient`** — Definition 9's `∏(B)` is the dependent product of the quotients.
* **`dd:poly`** — Definition 28's `Poly^F` is `MvPolynomial (Set S) ℝ`. The paper's
  variables are the subsets of `S`, and under `dd:partition` a block `[s]_b` *is* the set
  `part b s`, so a block is a variable of the ring verbatim — no indexing type is
  introduced and no correspondence has to be maintained. `Poly` is an `abbrev`, so the
  whole `MvPolynomial` API applies to it unchanged. Sums and products over sets
  (`∑_{s ∈ E}`, `∏_{b ∈ B}`) are `finsum`/`finprod`, which is what lets the *definitions*
  carry no finiteness while `[Finite S]` sits on exactly the statements the paper makes
  for finite factored sets. Irreducibility is Mathlib's `Irreducible` in this ring.

There are **no type-`(c)` modeling substitutions** so far: nothing weaker stands in for
one of the paper's objects.

## One thing to check carefully

`IsFactorization` carries a `nontrivial` field, because Definition 10 defines a
factorization as a set of **nontrivial** partitions. Dropping it is not harmless: the
indiscrete partition of a one-element set would become a legal factor, so both `{}` and
`{Ind}` would factor that set, falsifying Proposition 5's uniqueness claim.

The rendering is `¬ IsTrivialPartition`, where `IsTrivialPartition b := Nonempty S ∧ ∀ s
t, b s t`. The `Nonempty S` conjunct is what makes this "exactly one block" (Definition
3) rather than "at most one": over the empty set, Definition 7 sets `Ind_S = {}`, which
has *no* blocks and is therefore not trivial. Rendering nontriviality as the more obvious
`∃ s t, ¬ b s t` would wrongly exclude every partition of the empty set.

## Non-vacuity

**Discharged by construction** in `FiniteFactoredSets/Examples.lean`, which is inventoried
in the FFS-INVENTORY block alongside the nodes it de-vacuates. Four witnesses:

| Witness | Shape | What it rules out |
|---|---|---|
| `boolFS` | `Bool`, `B = {⊥}` — size 2, dimension 1 | `FactoredSet` uninhabited |
| `coordFS` | `Bool × Bool`, `B = {fstFactor, sndFactor}` — size 4, dimension 2 | Proposition 4 being near-tautologous: `not_subsingleton_coordFS_basis` shows the basis really has two factors, and `coordFS_chimera_corners` shows the four `C`-corners of `χ^F_C((true,true),(false,false))` are pairwise distinct |
| `emptyFS` | `Empty`, `B = {⊥}` | the `|S| = 0` case; `not_isFactorization_empty_basis` confirms `B = ∅` is *not* a factorization of the empty set, matching Proposition 5 |
| `unitFS` | `Unit`, `B = ∅` | the `|S| = 1` case; `unitFS_basis_unique` proves this is the *only* factorization of a one-element set, again matching Proposition 5 |

The two structure fields are also independent, and the same file carries both halves:
`not_isFactorization_singleton_fstFactor` shows `{fstFactor}` satisfies `nontrivial` and
fails `bijective`, and `not_isFactorization_unit_singleton_top` shows `{⊤}` over `Unit`
satisfies `bijective` and fails `nontrivial`. Both are inventoried.

**Constructing the factored sets is not on its own enough**, because §2.5 and §3 add
vocabulary — `size`, `dim`, `Generates`, `history`, `Orthogonal`, `Entangled`, `Before`,
`StrictlyBefore` — that a bare witness never exercises. The same file therefore runs that
vocabulary over the witnesses, and every declaration below is inventoried:

| Claim | Declarations | What it rules out |
|---|---|---|
| §2.5 has content on a witness | `size_coordFS`, `dim_coordFS`, `size_eq_prod_coordFS`, `dim_spec_coordFS`, `boolFS_trivial` | Propositions 7–9 never being applied: `coordFS` has size 4 and dimension 2, `∏_b \|b\| = 4`, and `4 = 2·2` puts `dim` in `[1,2]` |
| Generation and history are computed, not just defined | `generates_singleton_fstFactor`, `history_fstFactor`, `history_sndFactor`, `history_top`, `history_bot`, `history_eq_basis_of` | `history` being an intersection nobody has ever evaluated. `h(fstFactor) = {fstFactor}`, `h(Ind_S) = {}`, `h(Dis_S) = B`. `history_fstFactor` is also re-derived in the file *without* Proposition 13 clause 4, so the witness does not merely echo the endpoint it tests |
| Orthogonality is neither empty nor total | `orthogonal_fstFactor_sndFactor`, `not_orthogonal_fstFactor_self`, `not_orthogonal_bot_fstFactor`, `entangled_xorPart_fstFactor` | `Orthogonal` holding vacuously or universally; `Entangled` never being witnessed |
| Time is neither empty nor total | `before_fstFactor_bot`, `strictlyBefore_fstFactor_bot`, `not_before_fstFactor_sndFactor`, `history_eq_setOf_before_coordFS` | `Before` / `StrictlyBefore` being trivial relations; Proposition 19's `[Finite F.B] [Nonempty S]` being unsatisfiable together |
| `Before` really is only a preorder | `xorPart`, `history_xorPart`, `history_not_injective`, `before_xorPart_bot_and_back` | reading Proposition 18 as a partial order. The XOR partition and `Dis_S` are *distinct* partitions with the same history, so each is before the other — which is why Proposition 18 claims reflexivity and transitivity and stops |
| `Nonempty S` in §3 is load-bearing | `emptyFS_history_bot`, `emptyFS_history_ne_singleton`, `emptyFS_history_ne_setOf_before` | reading the `Nonempty S` on Proposition 13 clause 4 and Proposition 19 as decoration. Over `Empty` both conclusions are false as stated |

§4 adds a second layer of vocabulary — subpartitions, their restriction and generation,
`historySub`, and conditional orthogonality — none of which the §2–§3 witnesses touch. The
same file therefore restricts `coordFS`'s two factors to two subsets of `Bool × Bool`: the
block `Efst = {p | p.1 = true}` of `fstFactor`, on which the factors stay independent, and
the diagonal `Ediag = {p | p.1 = p.2}` (a block of `xorPart`), on which the first
coordinate determines the second. Every declaration below is inventoried:

| Claim | Declarations | What it rules out |
|---|---|---|
| Definitions 20–22 have a computed instance | `Efst`, `Ediag`, `sndOnEfst`, `indDiag`, `fstOnEdiag`, `sndOnEdiag`, `classes_sndOnEfst`, `restrict_restrict_sndOnEfst` | `Subpartition` / `restrict` never being evaluated. `sndFactor\|Efst` has domain `Efst` and its blocks are computed to the two singletons — it is the *discrete* partition of `Efst`, not a stand-in |
| Definition 23 is neither empty nor total | `generatesSub_sndOnEfst`, `not_generatesSub_fst_sndOnEfst`, `generatesSub_empty_indDiag`, `generatesSub_tfae_on_sndOnEfst`, `generatesSub_iff_on_sndOnEfst` | `GeneratesSub` holding vacuously or universally, and Proposition 20's TFAE never being projected at a concrete subpartition |
| Generation of a subpartition is **not** superset-monotone | `generatesSub_not_superset_monotone`, `not_generatesSub_fst_indDiag`, `historySub_indDiag` | the naive §4 analogue of `generates_iff_history_subset`. `∅ ⊢ Ind_Ediag` and `h^F(Ind_Ediag) = ∅ ⊆ {fstFactor}`, yet `{fstFactor}` does not generate it |
| Proposition 20 clause 7's second conjunct is load-bearing | `clause7_second_conjunct_loadbearing` | reading clause 7 as its order half alone. On `Ediag` the order half holds and the membership half `χ^F_C(E,E) = E` fails |
| Definition 24 takes nondegenerate values | `historySub_sndOnEfst`, `historySub_indDiag`, `historySub_fstOnEdiag`, `historySub_sndOnEdiag`, `historySub_ofSetoid_fstFactor`, `historySub_ofSetoid_sndFactor`, `historySub_botInfIndEfalse` | `historySub` being an intersection nobody has evaluated. The witnesses realize `{sndFactor}`, `{fstFactor}`, `∅` and `B` |
| Proposition 23 clause 2's `hE` is load-bearing | `Efalse`, `botInfIndEfalse`, `historySub_spec_hE_loadbearing` | reading `X.dom = Y.dom` as decoration. With `X = Dis_S` and `Y = Ind_Efalse` the union formula is false, and the left-hand history is the nondegenerate `{sndFactor}` rather than `∅` |
| `Subset` is exhibited both ways, and `dd:subpartition`'s bijection runs | `subset_indDiag_xorPart`, `not_subset_sndOnEfst_snd`, `ofSetoidOn_bot_Efst`, `roundtrip_sndOnEfst`, `roundtrip_bot_Efst` | Proposition 21 clause 6 / Proposition 23 clause 3 being vacuous, and the `Σ E, Setoid E` correspondence of `dd:subpartition` being asserted rather than exhibited on a concrete `E` |
| Lemmas 1 and 2 apply to a real factored set | `historySub_disjoint_coord`, `lemma1_coordFS`, `lemma1_coordFS'`, `lemma2_lhs_coordFS`, `lemma2_rhs_coordFS` | their hypothesis sets (`X.dom = Y.dom`, disjoint histories, a point of the domain) being jointly unsatisfiable. Lemma 2's two sides are each computed to `B` *without* invoking Lemma 2 — the left from Proposition 22, the right from Lemma 1 — so the pair cross-checks Lemma 2 on `coordFS` |
| Restriction can **entangle**, so §4.3 is not §3.3 | `not_orthogonalGivenSet_Ediag`, `Ediag_mem_xorPart_classes`, `not_orthogonalGiven_fst_snd_xorPart`, `orthogonalGiven_nondegenerate` | `OrthogonalGiven` being silently total, or implied by Definition 18. `fstFactor ⊥^F sndFactor` holds, yet conditioning on `xorPart` fails — and Proposition 24 explains only the `Ind_S` case |
| Proposition 25 and Theorem 2 hold and fail on a witness | `orthogonalGiven_fst_snd_top`, `orthogonalGiven_fst_fst_fst`, `not_orthogonalGiven_fst_fst_top`, `thm2_decomposition_coordFS`, `thm2_weakUnion_coordFS` | `X ⊥^F X \| Z` being trivially true or trivially false, and Theorem 2's clauses never being instantiated |
| Definitions 26–27 have degenerate corners a client should know about | `orthogonalGivenSet_empty`, `orthogonalGiven_bot` | reading `OrthogonalGivenSet` as always meaningful. Conditioning on `∅`, or on `Dis_S`, makes every pair orthogonal — faithful to the paper (a block is never empty), but a trap |

§5.1–§5.2 adds a third layer — the ring `Poly^F`, the characteristic polynomial `Q^F_E`,
the monomials `mono`/`monos`/`poly`, and the irreducible parts `Irr^F(E)` — and again the
§2–§4 witnesses touch none of it. The same file therefore computes `coordFS`'s
characteristic polynomial outright: `Q^{coordFS}_S` is the four-term multilinear
polynomial `∑_{a,b} X_{[·]₁=a} · X_{[·]₂=b}` over the four variables `vfst true`,
`vfst false`, `vsnd true`, `vsnd false`. `[Finite S]` — the hypothesis §5 introduces and
§2–§4 never needed — is discharged by instance search on `Bool × Bool`. The §5 vocabulary
is then run at four subsets — `S`, the block `Efst`, the diagonal `Ediag` and `∅` — which
is what makes `poly^F_C(E)` and `Irr^F(E)` visibly depend on `E` and the `E.Nonempty`
hypotheses visibly load-bearing. Every declaration below is inventoried:

| Claim | Declarations | What it rules out |
|---|---|---|
| Definition 31 is computed, not just written down | `vfst`, `vsnd`, `Q_coordFS_univ_eq`, `Q_coordFS_univ_ne_zero`, `degreeOf_Q_coordFS_univ_le_one` | `Q^F_E` being an unevaluated `finsum` of `finprod`s, or being `0`. The `finsum`/`finprod` are eliminated, the polynomial evaluates to `4` at all-ones, and every variable has degree ≤ 1 in it — Corollary 1 doing the work Proposition 28's proof needs |
| Definition 33's image *collapses*, and Proposition 26 is the statement that it does not at `C = B` | `mono_singleton_fst_true_false`, `poly_singleton_fst_univ`, `poly_singleton_snd_univ`, `mono_coordFS_basis_injective` | reading `monos^F_C(E)` as indexed by `E`. `S` has four points but `poly^F_{fst}(S)` has *two* summands; at `C = B` the collapse does not happen, and `mono_coordFS_basis_injective` proves that on the witness by separating evaluation rather than by citing Proposition 3 |
| Proposition 26 is cross-checked, and separately applied | `poly_coordFS_basis_univ_eq`, `prop26_coordFS_crosscheck`, `prop26_coordFS_applied`, `Q_coordFS_Efst_eq`, `poly_coordFS_basis_Efst_eq`, `prop26_coordFS_Efst_crosscheck`, `prop26_coordFS_Efst_applied` | a witness that "checks" an endpoint by applying it. `Q_coordFS_univ_eq` and `poly_coordFS_basis_univ_eq` compute their own sides to the same explicit polynomial and neither mentions `Q_eq_poly`, so the cross-check re-derives Proposition 26 here; the application is recorded as the separate claim it is. The same pair runs again at `E = Efst`, where the polynomial is a different one |
| Definition 34 takes a different value at a third subset | `poly_singleton_fst_Efst`, `poly_singleton_snd_Efst` | `poly^F_C(E)` being insensitive to `E`. On the block `Efst` the first coordinate is constant, so `poly^F_{fst}(Efst)` collapses to a *single variable* while `poly^F_{snd}(Efst)` keeps both of its — which is what makes Propositions 27 and 30 factor `Q^F_{Efst}` into two visibly *different* polynomials, where at `E = S` the two factors are symmetric |
| Definition 35 takes different values at different `E` | `mem_irr_singleton_fst_univ`, `mem_irr_singleton_snd_univ`, `irr_coordFS_univ`, `chimeraImage_singleton_fst_Ediag_ne`, `chimeraImage_singleton_snd_Ediag_ne`, `irr_coordFS_Ediag`, `irr_coordFS_Efst`, `irr_coordFS_empty` | `Irr^F` being empty, a singleton by construction, or independent of `E`. `Irr^{coordFS}(S) = {{fstFactor}, {sndFactor}}` while `Irr^{coordFS}(Ediag) = {B}` — the §5 shadow of the §4 fact that restricting to the diagonal entangles two orthogonal factors. Note the minimality clause of Definition 35 is *vacuous* at a singleton, `∅` being the only strict subset and not nonempty. At `Efst` the value is the two singletons again, so `Irr^F` agreeing at two subsets does *not* mean the factorizations do |
| Proposition 30's factorization is cross-checked, and separately applied | `Q_coordFS_univ_eq_mul_poly`, `prop30_coordFS_univ_applied`, `prop30_coordFS_Ediag_applied`, `prop30_coordFS_Efst_applied`, `prop30_coordFS_Efst_crosscheck` | the same defect as above one section on. The factorization `Q^F_S = poly^F_{fst}(S) · poly^F_{snd}(S)` is obtained by expanding both sides from Definitions 31 and 34, mentioning neither `Q_eq_finprod_poly_irr` nor `Irr^F`; the applications land on the same product, and at `Ediag` degenerate into Proposition 26's statement. At `Efst` the two factors are genuinely different polynomials, so the product structure is visible rather than symmetric |
| Proposition 27 is applied at a nontrivial split, and its chimera's orientation is pinned | `prop27_coordFS_applied`, `prop27_coordFS_crosscheck`, `prop27_reversed_false` | Proposition 27 being exercised only where it degenerates. The split is `C₀ = {fstFactor}`, `C₁ = {sndFactor}` — disjoint, both nonempty, union `B` — with `E₀ = Efst ≠ S = E₁`; the cross-check recomputes the identity without `poly_union_chimeraImage`; and reading the spliced set as `χ^F_{C₀}(E₁, E₀)` instead of `χ^F_{C₀}(E₀, E₁)` makes the conclusion *false* here, so the argument order is not a convention |
| Proposition 28's conclusion is doing work, not restating its hypothesis | `poly_singleton_fst_dvd_Q_coordFS_univ`, `prop28_coordFS_scaled_applied`, `prop28_r_loadbearing`, `prop28_coordFS_const_applied`, `prop28_const_forces_empty` | Proposition 28 quantifying over divisors that do not exist, *and* a witness that exhibits its conclusion where the conclusion is free. `poly^F_{fst}(S)` really divides `Q^F_S` (computed, not read off the endpoint) — but asserting `p = C r · poly^F_C(S)` at `p := poly^F_{fst}(S)` is a triviality, provable for every `C ⊆ B` and every `E` with none of the proposition's hypotheses (the probe `example` in `Examples.lean` proves exactly that). The two informative divisors are `2 · poly^F_{fst}(S)`, which is *no* `poly^F_C(S)`, so the real coefficient `r` cannot be dropped; and a nonzero constant, where the returned `C` is forced to `∅` |
| Proposition 29 is applied and cross-checked, and its `Subpartition` form is inhabited | `prop29_coordFS_univ_applied`, `sUnion_irr_coordFS_univ_crosscheck`, `prop29_coordFS_Ediag_applied`, `sUnion_irr_coordFS_Ediag_crosscheck`, `irr_isPartition_coordFS_univ_applied` | Proposition 29 asserting a constant. It is applied at the two subsets where `Irr^F` differs, and in each case the cover clause — `⋃₀ Irr^F(E) = B`, the endpoint's own third conjunct, not a set identity standing in for it — is re-derived by rewriting with the computed `Irr^F(E)`, without mentioning `irr_partition` |
| Proposition 31 is applied, and `Irreducible` is not vacuously total here | `prop31_coordFS_fst_applied`, `prop31_coordFS_snd_applied`, `not_isUnit_poly_singleton_fst_univ`, `not_isUnit_poly_singleton_snd_univ`, `not_irreducible_Q_coordFS_univ` | Proposition 31 calling units irreducible, or being true because everything in sight is irreducible. Both factors are irreducible and neither is a unit, while `Q^F_S` itself is *reducible* |
| The remaining §5.1 endpoints are applied, not merely shadowed | `Q_ne_zero_coordFS_applied`, `degreeOf_Q_le_coordFS_applied`, `vars_disjoint_coordFS_applied` | the computed facts standing in for the endpoints. Each of `Q_ne_zero`, `degreeOf_Q_le` and `vars_disjoint_of_mul_eq_Q` is instantiated on `coordFS` beside its computed counterpart |
| The `E.Nonempty` hypotheses of §5 are load-bearing, and Proposition 29's disclosed exception is real | `poly_empty_eq_zero`, `Q_coordFS_empty`, `prop28_hE_loadbearing`, `prop30_hE_loadbearing`, `prop31_hE_loadbearing`, `irr_partition_holds_at_empty` | reading `hE` as decoration. At `E = ∅` both `Q^F_∅` and every `poly^F_C(∅)` are `0`, and Propositions 28, 30 and 31 each fail outright — 30's on the zero-dimensional `unitFS`, where `Irr^F(∅) = ∅` makes the empty product `1`. Proposition 29 is the exception its docstring discloses, and the computation at `E = ∅` is what backs that — `irr_partition_holds_at_empty` states all three of the proposition's conjuncts there, not just the cover |
| `poly^F_C(E)` is total in `C`, so it has junk values off the paper's `C ⊆ B` | `poly_top_univ_junk`, `top_notMem_coordFS_basis` | reading a §5 statement as covering every `C`. At `C = {Ind_S}` the value is a single variable, and `Ind_S ∉ B`, so no `C ⊆ B` hypothesis of §5.1–§5.2 is satisfied by it |

Several of those rows carry a discipline worth naming, since it is the defect an earlier
audit round caught here: **a witness advertised as a cross-check must not mention the
endpoint it checks.** `prop26_coordFS_crosscheck`, `prop26_coordFS_Efst_crosscheck`,
`Q_coordFS_univ_eq_mul_poly`, `prop30_coordFS_Efst_crosscheck`,
`prop27_coordFS_crosscheck`, `sUnion_irr_coordFS_univ_crosscheck` and
`sUnion_irr_coordFS_Ediag_crosscheck` compute their claim from Definitions 31–35 and
elementary algebra. A second half of the same discipline, which a later round had to
repair here: a cross-check must also *state* what the endpoint states. The two
`sUnion_irr_*` lemmas once read `⋃₀ {{fst}, {snd}} = B` and `⋃₀ {B} = B` — true set
identities that mention no `Irr^F` at all, so they checked nothing; they now state
`⋃₀ Irr^F(E) = B` and get there by rewriting with the computed `Irr^F(E)`. The honest
applications, recorded as the separate claims they are, are `prop26_coordFS_applied`,
`prop30_coordFS_univ_applied`,
`prop30_coordFS_Ediag_applied`, `prop30_coordFS_Efst_applied`, `prop27_coordFS_applied`,
`prop29_coordFS_univ_applied`, `prop29_coordFS_Ediag_applied`, `prop31_coordFS_*_applied`
and the `prop28_*_applied` pair.

**How that separation is checked, and how it is not.** The check is *textual*: a
cross-check names no endpoint, so reading the declaration — or grepping the file for the
endpoint's name — is what verifies it. `#print axioms` does **not** verify it now that the
§5 endpoints are proved: every declaration in both groups reports the same
`[propext, Classical.choice, Quot.sound]`, so the command separates the two groups only
while an endpoint is still `sorry`d, when the applications pick up `sorryAx` and the
cross-checks do not. It is a useful regression tripwire during development and an inert
one afterwards; do not read a clean `#print axioms` as evidence that a witness is
independent of the endpoint it checks.

One friction point a client will meet, recorded at the site: `Finite F.B` — the
hypothesis every §3.2–§3.4 theorem carries (Propositions 10 and 11 need none, and nothing
in §3 needs `S` finite) — is discharged by instance search on every witness, but
`Fintype F.B` is not. The reason is not a missing `DecidableEq`: under `open scoped
Classical`, `Setoid (Bool × Bool)` has one and `Fintype ↥({fstFactor, sndFactor} : Set _)`
is synthesized by `Set.fintypeInsert`. It is that `coordBasis` and `coordFS.B` are
non-reducible `def`s, which instance search will not unfold to reach that `insert`. A
client passes `Fintype.ofFinite _` by hand, and `natCard_eq_prod` needs it in scope at
*statement* elaboration time.
