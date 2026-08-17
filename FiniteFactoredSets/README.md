# Finite Factored Sets — trust surface

Formalization of Scott Garrabrant, *Temporal Inference with Finite Factored Sets*
([arXiv:2109.11513](https://arxiv.org/abs/2109.11513)). The paper is the specification:
`notes/2109.11513-main.tex` is the exact arXiv source and `notes/2109.11513.pdf` the
matching PDF.

**Status: in progress — §2, §3 and §4 formalized (51 of the 96 in-scope nodes), with
non-vacuity discharged by construction: four factored sets are built, and the §2.5, §3 and
§4 vocabulary — `size`, `dim`, `Generates`, `history`, `Orthogonal`, `Entangled`, `Before`,
`StrictlyBefore`, `Subpartition`, `GeneratesSub`, `historySub`, `OrthogonalSub`,
`OrthogonalGivenSet`, `OrthogonalGiven` — is computed over them rather than merely
defined.**
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

Five of those nodes are stated in halves — four in two, one in three — and every half is
carried, so those nodes appear in the inventory more than once. The 51 nodes above are
cited by 57 annotations:

| Node | Carriers |
|---|---|
| Definition 13 (chimera) | `chimera` is `χ^F_C(s,t)`; `chimeraImage` is the setwise `χ^F_C(T,R)` that §3 onward quantifies over |
| Definition 15 (size, dimension) | `size` is `\|S\|`; `dim` is `dim(F)`. Its third sentence — "finite" / "finite-dimensional" — has no carrier at all: under `dd:finiteness-minimal` those are the typeclass hypotheses `[Finite S]` and `Finite F.B`, and they get a row in the Mathlib-rendered table below once the layered finite-`S` notion lands at §5 |
| Definition 18 (orthogonality) | `Orthogonal` is `X ⊥^F Y`; `Entangled` is the second sentence's negation of it |
| Definition 19 (time) | `Before` is `≤^F`; `StrictlyBefore` is `<^F` |
| Definition 25 (subpartition orthogonality and time) | three clauses, three carriers: `OrthogonalSub` is `⊥^F` on subpartitions, `BeforeSub` is `≤^F`, `StrictlyBeforeSub` is `<^F` |

Every one of those carries a `Paper node:` docstring line and an entry in
`AxiomAudit.lean`'s FFS-INVENTORY block, checked both ways by
`scripts/check-finite-factored-sets-nodes.py`. Zero `sorry`; every endpoint is clean at
`[propext, Classical.choice, Quot.sound]`.

## What is not claimed

§5 (polynomials and probability, including the Fundamental Theorem), §6 (inferring
time), and §7's in-scope material have **no Lean statements yet**. The trust-surface
guide reports the shortfall by kind rather than listing it.

An earlier feasibility spike proved several §5 results — the disjoint-support coefficient
lemma behind Proposition 28, multilinearity of `Q^F_E`, and the Fundamental Theorem's
"vanishes on an open set" step — against a throwaway structure. That file has been
retired rather than kept alongside the real one; the code is preserved at commit
`19a2254` and its findings are in `notes/spike-2026-08-15.md`. It is to be re-landed
against `FactoredSet` in the §5 stage.

**Scope (settled 2026-08-16): 96 of 98 nodes.** In: §1–§6 in full, §7's Definitions
46–50, and Conjecture 1 stated as a `Prop` and deliberately not proved. Out: Examples 3
and 4 only — both concern *infinite* factored sets, the case the paper itself expects the
fundamental theorem to fail in (Example 3 is its intended counterexample).

A consequence worth knowing before reading any §3–§4 statement: **finiteness is kept
minimal.** `FactoredSet` carries no `Fintype S`, and §3–§4 are stated with `Finite B`
only, because none of that material touches polynomials. `|S|` finite enters only at §5,
where `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b` stops being a polynomial once `S` is infinite.
That is what makes Conjecture 1 — the finite-*dimensional* fundamental theorem — statable
here at all. See `KNOWLEDGE.md` for its status in the literature.

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
| Proposition 2, first sentence (`≥_S` is a partial order) | Mathlib's `PartialOrder (Setoid S)` instance | `dd:order-flip` |

That last row is the only *partial* entry in the table: `bot_le_and_le_top` carries the
`Proposition 2` annotation but states only the proposition's second sentence (the `Dis`/`Ind`
bounds). The first sentence is Mathlib's instance. Anyone reading the trust-surface card
will see the full printed proposition beside a Lean statement covering half of it; that is
why the row is here.

It is not to be confused with the five multi-carrier nodes tabulated above (Definitions 13,
15, 18, 19, 25): those are nodes stated in halves, with *every* half carried, not nodes
stated in part.

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
| Lemmas 1 and 2 apply to a real factored set | `historySub_disjoint_coord`, `lemma1_coordFS`, `lemma1_coordFS'`, `lemma2_lhs_coordFS`, `lemma2_rhs_coordFS` | their hypothesis sets (`X.dom = Y.dom`, disjoint histories, a point of the domain) being jointly unsatisfiable. Lemma 2's two sides are computed independently, both to `B` |
| Restriction can **entangle**, so §4.3 is not §3.3 | `not_orthogonalGivenSet_Ediag`, `Ediag_mem_xorPart_classes`, `not_orthogonalGiven_fst_snd_xorPart`, `orthogonalGiven_nondegenerate` | `OrthogonalGiven` being silently total, or implied by Definition 18. `fstFactor ⊥^F sndFactor` holds, yet conditioning on `xorPart` fails — and Proposition 24 explains only the `Ind_S` case |
| Proposition 25 and Theorem 2 hold and fail on a witness | `orthogonalGiven_fst_snd_top`, `orthogonalGiven_fst_fst_fst`, `not_orthogonalGiven_fst_fst_top`, `thm2_decomposition_coordFS`, `thm2_weakUnion_coordFS` | `X ⊥^F X \| Z` being trivially true or trivially false, and Theorem 2's clauses never being instantiated |
| Definitions 26–27 have degenerate corners a client should know about | `orthogonalGivenSet_empty`, `orthogonalGiven_bot` | reading `OrthogonalGivenSet` as always meaningful. Conditioning on `∅`, or on `Dis_S`, makes every pair orthogonal — faithful to the paper (a block is never empty), but a trap |

One friction point a client will meet, recorded at the site: `Finite F.B` — the
hypothesis every §3.2–§3.4 theorem carries (Propositions 10 and 11 need none, and nothing
in §3 needs `S` finite) — is discharged by instance search on every witness, but
`Fintype F.B` is not. The reason is not a missing `DecidableEq`: under `open scoped
Classical`, `Setoid (Bool × Bool)` has one and `Fintype ↥({fstFactor, sndFactor} : Set _)`
is synthesized by `Set.fintypeInsert`. It is that `coordBasis` and `coordFS.B` are
non-reducible `def`s, which instance search will not unfold to reach that `insert`. A
client passes `Fintype.ofFinite _` by hand, and `natCard_eq_prod` needs it in scope at
*statement* elaboration time.
