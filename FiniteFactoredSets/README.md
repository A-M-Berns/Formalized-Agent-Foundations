# Finite Factored Sets — trust surface

Formalization of Scott Garrabrant, *Temporal Inference with Finite Factored Sets*
([arXiv:2109.11513](https://arxiv.org/abs/2109.11513)). The paper is the specification:
`notes/2109.11513-main.tex` is the exact arXiv source and `notes/2109.11513.pdf` the
matching PDF.

**Status: complete — §2 through §7 formalized. All 96 in-scope nodes are accounted for:
87 carry a Lean declaration of ours, and the remaining nine are rendered outright by
Mathlib vocabulary (Definitions 1, 2, 5, 6, 7, 9, 29, 30 and 39 — tabulated below), so
87 + 9 = 96.** Non-vacuity is discharged by construction: four finite factored sets, two
factored sets outside §5's finiteness boundary, five probability distributions on the
finite witnesses and one on an infinite carrier, five
factored set models and six orthogonality databases are built, and the §2.5, §3, §4, §5,
§6 and §7 vocabulary — `size`, `dim`, `Generates`, `history`, `Orthogonal`, `Entangled`,
`Before`, `StrictlyBefore`, `Subpartition`, `GeneratesSub`, `historySub`,
`OrthogonalGivenSet`, `OrthogonalGiven`, `Q`, `mono`, `monos`, `poly`, `irr`, `ProbDist`,
`IsDistribution`, `Model`, `Model.pullback`, `OrthDatabase`, `Models`, `Consistent`,
`Complete`, `OrthDatabase.StrictlyBefore`, `eventPartition`, `Observes`,
`ObservesPartition`,
`Counterfactable`, `CounterfactableRel`, `BeforeGivenSet` — is computed over them rather
than merely defined. `OrthogonalSub` is deliberately *not* in that list: the witness file
unfolds it on `coordFS` (an anonymous `example` restating `orthogonalSub_def`) but computes
no verdict from it, so it is exercised rather than evaluated.

Two things are deliberately *not* claimed and are set out below: Examples 3 and 4 are out
of scope by ruling, and Conjecture 1 is stated as a `Prop` and deliberately left unproved.
This file says what is claimed and what is not.

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
| 5.3 | Characteristic polynomials and conditional orthogonality | Lemma 3 |
| 5.4 | Probability distributions on finite factored sets | Definitions 36, 37; Proposition 32 |
| 5.5 | The fundamental theorem of finite factored sets | Theorem 3 |
| 6.1 | Factored set models, orthogonality databases, consistency, completeness, inferred time | Definitions 38, 40, 41, 42, 43, 44, 45 |
| 6.2 | The two worked examples | Examples 1, 2; Propositions 33, 34, 35, 36 |
| 7.2 | The fundamental theorem for finite-dimensional factored sets, **stated as a `Prop` and deliberately not proved** | Conjecture 1 |
| 7.3 | Embedded observations, counterfactability, conditional time | Definitions 46, 47, 48, 49, 50 |

§5.1's Definitions 29 (evaluation) and 30 (support) and §6.1's Definition 39 (preimages)
are the three nodes of these sections
with no declaration of ours. All three are left out of the rows above and appear in the
Mathlib-rendered table below instead, which is why those rows name 87 nodes rather than 90.

§7's two rows are of different kinds and should not be read together. §7.3 is *definitions
only* — the paper states no theorem about Definitions 46–50 — so what is claimed there is
that each definition is rendered faithfully through the §3–§4 vocabulary, in
`EmbeddedAgency.lean`. §7.2's row claims that Conjecture 1's *statement* is formalized, in
`Conjecture.lean`, and nothing more: see "What is not claimed" below before reading that
row as a result.

Six of those nodes are stated in halves — five in two, one in three — and every half is
carried, so those nodes appear in the inventory more than once. The 87 nodes above are
cited by 94 annotations:

| Node | Carriers |
|---|---|
| Definition 13 (chimera) | `chimera` is `χ^F_C(s,t)`; `chimeraImage` is the setwise `χ^F_C(T,R)` that §3 onward quantifies over |
| Definition 15 (size, dimension) | `size` is `\|S\|`; `dim` is `dim(F)`. Its third sentence — "finite" / "finite-dimensional" — has no carrier at all: under `dd:finiteness-minimal` those are the typeclass hypotheses `[Finite S]` and `Finite F.B`, and they now have a row in the Mathlib-rendered table below, `[Finite S]` having become load-bearing at §5.1 |
| Definition 18 (orthogonality) | `Orthogonal` is `X ⊥^F Y`; `Entangled` is the second sentence's negation of it |
| Definition 19 (time) | `Before` is `≤^F`; `StrictlyBefore` is `<^F` |
| Definition 25 (subpartition orthogonality and time) | three clauses, three carriers: `OrthogonalSub` is `⊥^F` on subpartitions, `BeforeSub` is `≤^F`, `StrictlyBeforeSub` is `<^F` |
| Definition 41 (database notation) | `Orth` is `X ⊥_D Y \| Z`; `NotOrth` is `¬(X ⊥_D Y \| Z)`. These are two *independent* assertions of the database, not a proposition and its negation — a database may make both (and then has no model) or neither (and then is not complete) |

Every one of those carries a `Paper node:` docstring line and an entry in
`AxiomAudit.lean`'s FFS-INVENTORY block. `scripts/check-finite-factored-sets-nodes.py`
enforces that one direction — annotation ⇒ inventory — together with the validity of each
cited node against the committed TeX and the anchoring of each annotation to a named
declaration. It does **not** enforce the converse: the inventory also holds the
non-vacuity witnesses, so it has far more entries than there are annotations, and a line
naming a declaration that does not exist passes the checker and is caught only when
`AxiomAudit.lean` is elaborated, by `#assert_axioms_clean` failing to resolve the name.
Node *coverage* is machine-checked since 2026-08-17: `notes/scope-manifest.json` records
the ruling (Examples 3–4 out) and the nine Mathlib-rendered nodes, and the same checker
fails unless (numbered nodes in the TeX) − out-of-scope − Mathlib-rendered equals the
annotated node set in both directions — so removing the only carrier of an in-scope node,
or annotating a node the manifest says is rendered, is a CI failure, and the `87 + 9 = 96`
above is an invariant, not prose. (Recount by hand with
`grep -rho "Paper node: [A-Za-z]* [0-9]*" FiniteFactoredSets/*.lean | sort -u` if you like;
editing the manifest is a scope change and needs a ruling recorded here.) Every endpoint — §2–§7, witnesses included —
is `sorry`-free and clean at `[propext, Classical.choice, Quot.sound]`; the library has no
open proof obligation. **Zero `sorry`, zero `axiom`.** Conjecture 1 is not an exception to
that and should not be read as one: `FundamentalTheoremFiniteDim` is a `def … : Prop` with
no proof anywhere, which is a *definition* and not a `sorry` — it carries no `sorryAx`, adds
no axiom, and cannot weaken any statement of ours except by appearing among that statement's
hypotheses, which nothing in §2–§7 does.

## Audit trail and what is still owed

The final fresh-context adversarial audit (harness round 11) and an independent external
review are filed under `notes/audit/`: `round-11-findings.json` (38 raw findings with ids),
`round-11-resolution.md` (disposition of each), `round-11-adjudication-prompts.md` (the
cross-family sweeps that could not run — codex quota; re-run when it resets), and
`external-audit-gpt56sol-2026-08-17.md` (GPT-5.6 Sol's read-only review of head `4cbb1a7`:
mathematical PASS, process CONDITIONAL PASS). Two of its conditions are still open and are
recorded rather than hidden: **the human read-through of the frozen statement surface** —
`notes/statement-readthrough-checklist.md` is the checklist, unsigned until Anson performs
it — and the per-finding cross-family adjudication of round 11. Neither is a mathematical
gap; both are trust-accounting obligations of the repo's own standard.

## What is not claimed

Two things, and both are rulings rather than gaps.

**Examples 3 and 4 are out of scope.** Both concern `S = 𝒫(ℕ)` — *infinite* factored sets
— and the paper itself expects the fundamental theorem to fail there; Example 3 is its
intended counterexample. Excluding exactly the case the paper predicts is false is the
line; there is no partial formalization of either example hiding anywhere. That said, the
factored set they are about is built, as a *witness* with no paper-node annotation:
`InfiniteExamples.lean` carries `infFS` on `ℕ → Bool`, the coordinate factorization that is
the paper's `𝒫(ℕ)` factored set, and uses it to pin the finiteness hypotheses of §5 (see
the non-vacuity section). Reading that file as a formalization of Examples 3 or 4 would be
a misreading: it exhibits the object, and claims nothing the paper claims about it.

**Conjecture 1 is stated and deliberately not proved.**
`FundamentalTheoremFiniteDim` in `Conjecture.lean` is a `def … : Prop` — Theorem 3's
statement with `[Finite S]` weakened to `[Finite F.B]` — and **no declaration anywhere in
this library has that type**. The development takes no position on it and no prover time
should be spent on it. Its finite instance needs no separate statement: it simply **is**
Theorem 3, `orthogonalGiven_iff_forall_isDistribution`. What exercises the `Prop`'s shape
is the three `example`s that take it *as a hypothesis* and instantiate it at a witness —
two in `InfiniteExamples.lean` and one in `APITests/FiniteFactoredSets.lean` — and those
are the only uses of it anywhere.

A second thing is not claimed here, and it is a boundary of the *statement* rather than of
the effort. Weakening Theorem 3's `[Finite S]` to `[Finite F.B]` does not only change the
hypothesis; it changes what `ProbDist S` ranges over. Definition 36 defines a probability
distribution only "given a finite set `S`", and §7.2's one sentence says nothing about
what one is on an infinite carrier, so over an infinite `S` the Lean `Prop` quantifies over
the merely finitely-additive functions on the full powerset — no countable additivity, no
σ-algebra — including objects the paper never contemplated (a finitely-additive density
with every singleton `0` satisfies Definitions 36 and 37 vacuously). Those strengthen the
`→` direction of the biconditional and weaken the `←` direction. So
`FundamentalTheoremFiniteDim` is one particular *sharpening* of an informal conjecture, and
**proving or refuting it would not by itself settle the paper's §7.2 question.** The
alternative sharpenings all want a measure-theoretic `P`, which `dd:probability` rules out
as a substitution for Definition 36.

On its status in the
literature (recorded at length in `KNOWLEDGE.md`): Matthias Georg Mayer has since proved
the fundamental theorem for finitely factored *measurable* spaces (*A Theory of Structural
Independence*, arXiv:2412.00847), but that is the **unconditional** statement and it carries
measurable structure a bare finite-dimensional factored set does not, so the accurate claim
is **resolved in a measurable refinement, not as literally stated**. That is precisely why
it sits here as an open `Prop` with the note attached.

§5, §6 and §7 are otherwise complete: all five §5.3–§5.5 nodes, all fourteen §6 nodes and
all five §7.3 nodes are stated and — where the paper states a result about them — proved.
§6 is Definitions 38–45, Examples 1 and 2 as constructed databases, and Propositions 33–36
with the paper's own models (`Example1.idModel`, `Example2.model`) discharging the two
consistency claims. §7.3 is *definitions only*, because the paper proves nothing about
them; that is faithfulness, not a shortfall.

An earlier feasibility spike proved several §5 results — the disjoint-support coefficient
lemma behind Proposition 28, multilinearity of `Q^F_E`, and the Fundamental Theorem's
"vanishes on an open set" step — against a throwaway structure. That file has been
retired rather than kept alongside the real one; the code is preserved at commit
`19a2254` and its findings are in `notes/spike-2026-08-15.md`. All three have since been
re-landed against `FactoredSet`: the first as `coeff_add_mul_of_split` in
`Polynomial.lean` (generic in the index type, and upstreamable); the second as
`degreeOf_poly_le` and `degreeOf_Q_le` there; and the third — the step Theorem 3's hard
direction needs — as the private `eq_zero_of_eval_pos_eq_zero` in `Probability.lean`,
which is `MvPolynomial.funext_set` at `Set.Ioi 0`.

**Scope (settled 2026-08-16): 96 of 98 nodes**, all now landed. In: §1–§6 in full, §7's
Definitions 46–50, and Conjecture 1 stated as a `Prop` and deliberately not proved. Out:
Examples 3 and 4 only, as above.

A consequence worth knowing before reading any §3–§4 statement: **finiteness is kept
minimal.** `FactoredSet` carries no `Fintype S`, and §3–§4 are stated with `Finite B`
only, because none of that material touches polynomials. `|S|` finite enters at §5, where
`Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b` stops being the intended polynomial once `E` is
infinite — the `finsum` collapses to `0`. §6 is the one place the per-statement discipline
does not apply, and it departs in the strict direction: Definition 38 says *finite*
factored set and Definitions 43 and 45 quantify over models, so `dd:model` puts `Finite S`
in the `Model` structure as a field and **no §6 statement carries a finiteness binder at
all**.

It does not enter across the board, and it would be wrong to read §5 as a
finite-`S`-only section. Of the 50 public §5 declarations, twenty-one carry `[Finite S]`,
seven carry `[Finite F.B]` only, and twenty-two carry no finiteness at all. So there are
statements of ours that *do* apply over an infinite `S`, and a client working there gets
more than the definitions:

* with no hypothesis whatever — `poly_empty`, `mono_eq_prod`, `mono_congr`, `mono_union`,
  `Q_eq_finsum_mono`, `mem_irr`, `subset_chimeraImage_self`, the upstreamable
  `coeff_add_mul_of_split`,
  `degreeOf_poly_le` (every variable has degree at most one in `poly^F_C(E)` for `C ⊆ B`,
  junk values included), the two forms of Definition 36's iterated additivity
  (`ProbDist.eq_sum_singleton`, `ProbDist.eq_sum_singleton_of_finite` — the finiteness
  they need is the *set's*, taken as a `Finset` or a hypothesis, not `S`'s), the point mass
  `ProbDist.diracAt` with its unfolding `diracAt_apply`, and all three
  §5.4 definitions — `ProbDist`, its `CoeFun`
  instance, and `IsDistribution`, which are stated over an arbitrary `S` on purpose
  (`dd:probability`), so that `[Finite S]` sits on Proposition 32 and Theorem 3 rather
  than on every statement that merely mentions a distribution;
* with `Finite B` alone — `mono_eq_iff`, `mono_basis_injective`, `Q_eq_poly`
  (Proposition 26), `degreeOf_Q_le`,
  Proposition 29 with its §4 restatement (`irr_partition`, `irr_isPartition`), so
  `Irr^F(E)` partitions `B` over an infinite `S` too, and `isDistribution_diracAt` — the
  point mass is a distribution on *every* factored set of finite dimension, which is the
  general reason Definition 37 is inhabited whenever `S` is.

Of those, the `Q`-level §5.1 `Finite B` statements are degenerate over an infinite `E` —
both sides are junk values — while Proposition 29, `mono_basis_injective` and
`isDistribution_diracAt` are not (the last is outright *false* for an infinite basis: the
`finprod` in Definition 37 returns `1` once infinitely many factors separate the two
points, where the singleton probability is `0`). The
rest of §5 genuinely needs `|S|` finite: an infinite `E` makes `Q_ne_zero`, `coeff_poly`,
`mem_vars_poly` and Propositions 27, 28, 30 and 31 false rather than merely unproved, and
the same goes for every §5.3 statement and for Proposition 32, each of which has a
`Q^F_E` in it.

**Theorem 3 is the exception, and the exception matters.** Its statement mentions no
polynomial — it is `P(x∩z) · P(y∩z) = P(x∩y∩z) · P(z)` for every distribution `P` — and
its `[Finite S]` is consumed entirely inside the proof, by Lemma 3 (whose statement *does*
have a `Q^F_E`) and by the construction of the auxiliary distribution `P_f` from a positive
assignment. So relaxing it to `Finite F.B` would not be a proof-tightening exercise: the
relaxed statement is literally **Conjecture 1**, the finite-*dimensional* fundamental
theorem, which the paper leaves open. The exact per-declaration register,
with what each hypothesis is consumed for, is the "Finiteness" section of `API.lean`. The
minimal-finiteness boundary is also what makes Conjecture 1 statable here at all. See
`KNOWLEDGE.md` for its status in the literature.

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
| Definition 8, second sentence (`X ∨_S Y`) | Mathlib's `X ⊓ Y` on `Setoid`, which is how §3 onward states it; `commonRefinement_pair` is the bridge to the set form `⋁_S({X, Y})` that Definition 8's carrier `commonRefinement` renders | `dd:order-flip` |
| Definition 15, third sentence (finite / finite-dimensional factored set) | the typeclass hypotheses `[Finite S]` and `Finite F.B`, carried per statement | `dd:finiteness-minimal` |
| Definition 29 (`p(f)`, evaluation) | `MvPolynomial.eval f p` | `dd:poly` |
| Definition 30 (`supp(p)`, support) | `MvPolynomial.vars p` | `dd:poly` |
| Definition 39 (`f⁻¹(ω)`, `f⁻¹(E)`, `f⁻¹(X)`) | `Set.preimage` for the first two; `Setoid.comap f X` for the partition, whose blocks are exactly the nonempty preimages of blocks of `X` — the definition's own side condition, supplied by `Setoid.classes` rather than written out. `Model.pullback` is a *named alias* for that third clause and deliberately carries no node annotation | `dd:model` |
| Proposition 31's "irreducible" (no factorization into two polynomials of nonempty support) | Mathlib's `Irreducible` in `Poly S`. The two readings do **not** coincide: over `ℝ` the units are the nonzero constants, and `Irreducible` demands `¬ IsUnit p` on top of the paper's condition, which every nonzero constant and `0` satisfy. They agree exactly on nonzero non-units, which is all Proposition 31 ranges over — so the Lean statement is the strictly stronger, safe reading | `dd:poly` |
| Proposition 2, first sentence (`≥_S` is a partial order) | Mathlib's `PartialOrder (Setoid S)` instance | `dd:order-flip` |

Nine of those thirteen rows are whole nodes (Definitions 1, 2, 5, 6, 7, 9, 29, 30, 39 — the
last three outside §2.1, where Mathlib's `eval`, `vars`, `Set.preimage` and `Setoid.comap`
render them outright); the
other four are *partial* entries — a clause of a node whose remaining clauses do have a
carrier, recorded here so that nothing in a printed node is silently unaccounted for:

* **Proposition 2, first sentence.** `bot_le_and_le_top` carries the `Proposition 2`
  annotation but states only the proposition's second sentence (the `Dis`/`Ind` bounds).
  Anyone reading the trust-surface card will see the full printed proposition beside a Lean
  statement covering half of it; that is why the row is here.
* **Definition 8, second sentence.** `commonRefinement` carries the `Definition 8`
  annotation and renders the set form `⋁_S(C)`. The binary `X ∨_S Y = ⋁_S({X, Y})` is
  Mathlib's `X ⊓ Y`, which is what Propositions 11, 13, 15 and 18 are stated with; the
  identification of the two is `commonRefinement_pair`, a bridge lemma with no annotation
  of its own. Before it landed this was the one order translation in §3 asserted only in
  prose.
* **Definition 15, third sentence.** "Finite" and "finite-dimensional" are not a
  definition this library makes: under `dd:finiteness-minimal` they are the typeclass
  hypotheses `[Finite S]` and `Finite F.B`, carried on the individual statements that use
  them rather than bundled into a `FiniteFactoredSet` structure. §3–§4 carry `Finite F.B`
  only; §5.1–§5.2 carry whichever of the two each statement's proof consumes, which is
  `[Finite S]` for most of them but `Finite F.B` for Propositions 26 and 29 (see the
  finiteness paragraph above and `API.lean`'s register).
* **Proposition 31's word "irreducible."** The proposition itself is carried
  (`irreducible_poly_of_mem_irr`); it is the *meaning* of the word that is Mathlib's, and
  the two readings agreeing is a fact about `ℝ` worth stating rather than assuming.

None of this is to be confused with the six multi-carrier nodes tabulated above
(Definitions 13, 15, 18, 19, 25, 41): those are nodes stated in halves, with *every* half
carried by an *annotated* declaration, not nodes stated in part. Definition 15 appears in
both lists, because two of its sentences have carriers and the third does not; Definition 8
appears only here, because its second sentence's Lean fact (`commonRefinement_pair`) is a
bridge lemma rather than a second carrier.

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
* **`dd:subpartition`** — Definition 20's subpartition (a partition of a subset `E ⊆ S`) is
  a **partial equivalence relation** on `S`, with Definition 21's domain as `{s | r s s}`,
  rather than a `Σ E : Set S, Setoid E`. Record the reason accurately, because the obvious
  one is wrong: Mathlib **does** have partitions of a subset —
  `Mathlib/Order/Partition/Basic.lean`'s `Partition (E : Set α)`, with `Partition.Rel` (the
  induced partial equivalence relation), `rel_rfl_iff` (the domain), `partOf`, the
  refinement order in the same orientation as `Subpartition`'s `≤`, and a `SemilatticeInf`
  whose `⊓` is the paper's `∨_E`. What it does not have is an *un-indexed* carrier: its
  `Partition E` carries its support in the type, so `SubPart(S)` would be `Σ E, Partition E`
  with no restriction across supports, and §4's pervasive equal-domain hypotheses
  (`X.dom = Y.dom` in Proposition 23, Lemmas 1 and 2) would become type-level transports.
  That, not an absence of API, is why the PER carrier was chosen; anyone upstreaming §4
  should start from Mathlib's `Partition`.
* **`dd:poly`** — Definition 28's `Poly^F` is `MvPolynomial (Set S) ℝ`. The paper's
  variables are the subsets of `S`, and under `dd:partition` a block `[s]_b` *is* the set
  `part b s`, so a block is a variable of the ring verbatim — no indexing type is
  introduced and no correspondence has to be maintained. `Poly` is an `abbrev`, so the
  whole `MvPolynomial` API applies to it unchanged. Sums and products over sets
  (`∑_{s ∈ E}`, `∏_{b ∈ B}`) are `finsum`/`finprod`, which is what lets the *definitions*
  carry no finiteness while `[Finite S]` sits on exactly the statements the paper makes
  for finite factored sets. Irreducibility is Mathlib's `Irreducible` in this ring —
  strictly stronger than the paper's Proposition 31 phrasing rather than equivalent to it
  (see the Mathlib-rendered table above), so the Lean statement is the safe reading.
* **`dd:probability`** — §5.4's probability distributions are elementary, exactly as the
  paper writes them. Definition 36 is the structure `ProbDist S` — a function
  `P : Set S → ℝ` with the paper's four clauses as fields (`nonneg`, `empty`, `univ`,
  `additive`) — and Definition 37 is the predicate `IsDistribution` saying
  `P {s} = ∏_{b ∈ B} P([s]_b)`. **No measure theory appears, and none is a substitute
  here**: the paper's `P` is defined on the whole powerset with finite additivity and no
  σ-algebra, and Theorem 3 quantifies over *all* such `P`, so a
  `MeasureTheory.ProbabilityMeasure` rendering would change what the theorem ranges over.
  A bridge to Mathlib's probability vocabulary would be extra credit and would have to be
  a separate lemma. Two further consequences: the paper's "finite set `S`" is carried by
  the statements that consume it, not by the structure; and Theorem 3's conclusion is the
  paper's **division-free** `P(x∩z)·P(y∩z) = P(x∩y∩z)·P(z)`, so it stays meaningful when
  `P(z) = 0` and never introduces a conditional probability.

* **`dd:model`** — §6.1's model of a sample space is the structure `Model Ω`: an implicit
  carrier `S`, a `FactoredSet S`, the map `f : S → Ω`, and a `Finite S` **field**,
  registered as an instance. Definition 38 says *finite* factored set, and Definitions 43
  and 45 quantify over models, so the finiteness has to be part of the object — otherwise
  "for all models" would range over the wrong class. This is the one place the library
  departs from `dd:finiteness-minimal`, and it is a departure in the strict direction: **no
  §6 declaration carries a finiteness binder of its own**, because every model it quantifies
  over carries one. `Finite M.F.B` is then found by instance search wherever an
  `M : Model Ω` is in scope, which is what lets a §6 proof call a §3–§4 endpoint
  (Proposition 25, in the case of `nonconstDB_forces_nonconstant`) with no hypothesis of
  its own. The sample space `Ω` is unconstrained. One narrowing is disclosed rather than
  discharged: `Model : Type u → Type (u+1)` pins the carrier to `Ω`'s own universe, so
  Definitions 43 and 45 quantify over models with a `Type u` carrier rather than over models
  in every universe — forced by Lean, and empty in content since every carrier is finite and
  so equivalent to one in `Type 0`, but the library proves no transport along that
  equivalence.

  Definition 39 has no carrier and is in the Mathlib-rendered table above.
  Definition 40's database is `OrthDatabase Ω`, a pair of sets of triples of partitions;
  Definition 41's two notations are the memberships `Orth` and `NotOrth`, and the point to
  hold on to is that `NotOrth` is a positive assertion *of the database*, not the negation
  of `Orth` — so a database may assert both (Definition 43 then fails) or neither
  (Definition 44 then fails). Both are witnessed in `Examples.lean`.
* **`dd:conjecture`** — §7.2's Conjecture 1 is a `def … : Prop`,
  `FundamentalTheoremFiniteDim`, universe-polymorphic and quantifying over every carrier,
  every factored set on it and every triple of partitions. Its body is Theorem 3's
  statement with `[Finite S]` weakened to `[Finite F.B]` and **nothing else changed**, which
  is the whole content of the conjecture — the paper's §7.2 asks exactly whether the
  finiteness it assumed "fairly gratuitously" can be dropped to finite *dimension*.
  Stating it costs nothing and claims nothing: no declaration has that type, its finite
  instance is Theorem 3 itself rather than a separate restatement, and
  the reason the `Prop` can be written down at all is that `dd:finiteness-minimal` and
  `dd:probability` between them keep `ProbDist` and `IsDistribution` free of any finiteness
  of their own. One thing the tag owes a disclosure for, spelled out under "What is not
  claimed": because Definition 36 is stated by the paper only for a finite `S`, dropping
  `[Finite S]` also widens the family the biconditional quantifies over, so the `Prop` is a
  sharpening of §7.2's sentence rather than a transcription of it. See "What is not
  claimed" for that and for its status in the literature.

  §7.3's renderings are consequences of `dd:partition` and `dd:order-flip` rather than
  decisions of their own, and two are worth stating here because they change how a
  definition reads. Definition 46's auxiliary `X_E` is `eventPartition E`, namely
  `Setoid.comap (· ∈ E) ⊥` — related iff you agree on membership in `E` — whose blocks are
  the *nonempty* ones among `E` and `S \ E`, so the paper's case split (`{S}` when `E` is
  empty or all of `S`, `{E, S \ E}` otherwise) is absorbed by `Setoid.classes` rather than
  written out; `eventPartition` takes no `F` and carries no paper-node annotation, Definition
  46's carrier being `Observes`. And Definition 47's sub-agents `Aᵢ` are indexed by the
  **blocks** of `X` (`As : X.classes → Setoid S`) rather than by a numbering
  `X = {x₀, …, xₙ₋₁}`, with `⋁_S {Aᵢ}` as `sInf (Set.range As)`; that is what keeps
  Definition 47 free of the finiteness its printed notation implies. Definition 50's
  `h^F(X | E)` is `historySub ((ofSetoid X).restrict E)`, Definition 26's own spelling, and
  none of Definitions 46–50 carries a finiteness binder.

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

**Discharged by construction** in `FiniteFactoredSets/Examples.lean` — with
`FiniteFactoredSets/InfiniteExamples.lean` carrying the witnesses that live outside §5's
finiteness boundary, kept separate because everything in `Examples.lean` is finite by
construction — both inventoried in the FFS-INVENTORY block alongside the nodes
they de-vacuate. Four finite witnesses:

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
| Proposition 25 and Theorem 2 hold and fail on a witness | `orthogonalGiven_fst_snd_top`, `orthogonalGiven_fst_fst_fst`, `not_orthogonalGiven_fst_fst_top`, `thm2_decomposition_coordFS`, `thm2_weakUnion_coordFS`, and a third decomposition instance at a genuinely non-degenerate `W` (`Examples.lean`) | `X ⊥^F X \| Z` being trivially true or trivially false, and Theorem 2's clauses never being instantiated |
| Definitions 26–27 have degenerate corners a client should know about | `orthogonalGivenSet_empty`, `orthogonalGiven_bot` | reading `OrthogonalGivenSet` as always meaningful. Conditioning on `∅`, or on `Dis_S`, makes every pair orthogonal — faithful to the paper (a block is never empty), but a trap |

Read the Theorem 2 row for exactly what it says, since two of its three instances are
degenerate on purpose and one is not. `thm2_decomposition_coordFS` takes `W = ⊤`, which
makes its first conjunct the already-proved `orthogonalGiven_fst_snd_top` and its second a
consequence of Proposition 23 clause 4 alone; `thm2_weakUnion_coordFS` takes `W = Y`. The
third instance is the one that meters decomposition, at `Z = ⊤`, `Y = fstFactor`,
`W = sndFactor` and `X` the XOR partition. Contraction, composition and symmetry —
Theorem 2's remaining clauses, and the two whose proofs consume Lemma 2 and Proposition 23
clause 2 — have no concrete instantiation here; `orthogonalGiven_semigraphoid` carries all
five, and the witnesses meter three.

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

§5.3–§5.5 adds the last layer — the divisibility characterization of conditional
orthogonality, probability distributions on a set and on a factored set, and the
fundamental theorem — and `ProbDist` in particular is a bare structure that nothing built
before this stage. The same file therefore constructs three distributions on `Bool × Bool`
and runs the two *conditional* notions — Lemma 3's clauses 2 and 3, and Theorem 3 — at
*both* of the conditioning partitions §4.3 already separates on `coordFS`: `Ind_S`, where
the two coordinate factors are orthogonal, and the `xorPart` block `Ediag`, where they are
entangled. In each of those cases the two answers differ. The two *unconditional* notions
have no such axis, so they are separated along their own: Proposition 32 at two subsets
(`Efst` and the three-element `E3`) under two distributions, and Definitions 36–37 at the
single point `(true, true)`. Three further groups keep the §5.4–§5.5 quantifiers honest —
the two directions the fundamental theorem consumes run *forward* with their hypotheses
discharged, the degenerate carriers over `Empty` and `Unit` are recorded, and Theorem 3's
right-hand side is refuted on the one-dimensional `boolFS`.
Every declaration below is inventoried:

| Claim | Declarations | What it rules out |
|---|---|---|
| Definition 31 is computed at the remaining blocks Lemma 3 and Theorem 3 range over | `Q_coordFS_singleton`, `Q_coordFS_vfst`, `Q_coordFS_vsnd`, `Q_coordFS_vsnd_true`, `Q_coordFS_Ediag`, `Q_coordFS_E3` | the §5.3 witnesses quantifying over blocks whose characteristic polynomial nobody has evaluated. `Q^F_{Ediag}` is the two-term polynomial that makes the diagonal's failure computable, and `Q_coordFS_vfst`/`Q_coordFS_vsnd` cover *every* block of each factor, which is what lets clause 3 be proved for all pairs at once |
| Lemma 3's clause 3 is cross-checked, separately applied, and **fails** where §4.3 says it must | `lemma3_clause3_coordFS_top_crosscheck`, `lemma3_clause3_coordFS_top_applied`, `lemma3_clause3_coordFS_Ediag_fails` | clause 3 being vacuous or total. At `z = S` both products expand, from Definition 31 alone, to the same polynomial; at the `xorPart` block `Ediag` one separating `coordSep` evaluation sends them to `310` and `100`. That failure is the polynomial shadow of `¬ (fstFactor ⊥^F sndFactor \| xorPart)` |
| Lemma 3's clause 2 — the divisibility — is exercised too, at the same two conditionings | `lemma3_clause2_top_crosscheck`, `lemma3_clause2_top_applied`, `lemma3_clause2_Ediag_fails` | clause 2 being reachable only through the `TFAE` and therefore never run. The cross-check exhibits the cofactor `Q^F_{(t,t)}` from Definition 31 and states the same divisibility the application projects with `.out 0 1`; on the diagonal divisibility fails, refuted by a single *zero* of the divisor (`coordZero`) rather than by a separating value |
| Lemma 3's `3 → 1` direction runs **forward**, with its hypothesis discharged | `clause3_fst_snd_top`, `orthogonalGiven_from_clause3` | the direction §5.5 actually consumes being exercised only under a `by_contra` or as an assumed binder. Clause 3 is proved for *every* pair of blocks by computation, and the endpoint turns it into `fstFactor ⊥^F sndFactor \| Ind_S` — a route to that fact independent of Proposition 24's |
| Definitions 36 and 37 are inhabited, the second is strictly stronger, and neither names one particular distribution | `uniform`, `uniform_isDistribution`, `biased`, `biased_isDistribution`, `biased_ne_uniform`, `diagDist`, `not_isDistribution_diagDist` | `ProbDist` being uninhabited — which would make Theorem 3's right-hand side vacuously true and Proposition 32 unexercised — Definition 37's product condition being decoration, and Definition 37 being read as naming *the* uniform distribution. `uniform` (`P(E) = \|E\|/4`) and `biased` (a product of two `1/3`-biased coins) are two different distributions on `coordFS`; `diagDist` (`P(E) = \|E ∩ Ediag\|/2`) satisfies all four of Definition 36's clauses and is **not** a distribution on `coordFS`, since `P{(t,t)} = 1/2` while `P([s]_fst)·P([s]_snd) = 1/4` |
| Proposition 32 is cross-checked and separately applied, at two subsets under two distributions | `prop32_coordFS_Efst_crosscheck`, `prop32_coordFS_Efst_applied`, `prop32_biased_Efst_crosscheck`, `prop32_biased_Efst_applied`, `E3`, `prop32_biased_E3_crosscheck`, `prop32_biased_E3_applied` | a witness that "checks" the characterization by applying it, and one that checks it only where the evaluation collapses. `E = Efst` is chosen because `Q^F_{Efst}` has two terms, so the evaluation is a genuine sum — under `uniform` its two summands coincide (`1/2·1/2 + 1/2·1/2`), under `biased` they do not (`1/9 + 2/9`); `E3` has three of the four points, so the polynomial has three terms taking two distinct values and neither side is symmetric |
| Theorem 3 runs in **both** directions on the discriminating pair, and its converse also runs forward | `thm3_coordFS_top_crosscheck`, `thm3_coordFS_top_applied`, `thm3_coordFS_Ediag_fails`, `thm3_coordFS_xorPart_witness`, `thm3_coordFS_xorPart_applied`, `orthogonalGiven_from_independence` | the fundamental theorem being exercised only where it degenerates, its existential being exhibited at its own witness form, and its converse being reached only by contraposition. Forward at `Z = Ind_S`: `uniform` makes the factors independent, `1/2·1/2 = 1/4·1`, computed and separately derived from `orthogonalGiven_fst_snd_top`. Backward at `Z = xorPart`: `¬ (fst ⊥^F snd \| xorPart)` yields, through the endpoint, the existence of a distribution and blocks breaking independence — and the cross-check *names* them, `uniform` at `z = Ediag`, where `1/4 · 1/4 = 1/16` but `1/4 · 1/2 = 1/8`. `orthogonalGiven_from_independence` then discharges the converse's hypothesis outright, giving a third independent derivation of `fst ⊥^F snd \| Ind_S` |
| The quantifier "for every distribution `P` on `F`" is neither empty nor unconstraining | `isEmpty_probDist_empty`, `orthogonalGiven_emptyFS`, `unitDist`, `subsingleton_probDist_unit`, `unitDist_isDistribution`, `boolUniform`, `boolFS_isDistribution`, `not_orthogonalGiven_bot_bot_top_boolFS` | reading Theorem 3 as informative everywhere, and reading its right-hand side as possibly universal. Over `Empty` there is *no* distribution and both sides of the theorem hold, so the theorem is consistent there and nothing more; over `Unit` there is exactly one, and it is a distribution on the zero-dimensional `unitFS`, the empty product being `1`. On the one-dimensional `boolFS` every `ProbDist Bool` is a distribution on the factored set, and `boolUniform` refutes `Dis_S ⊥^F Dis_S \| Ind_S` with `1/2 · 1/2` against `0 · 1`. The general positive half lives in `Probability.lean`, not here: `isDistribution_diracAt` says the point mass is a distribution on **every** factored set of finite dimension, so the family is empty exactly when `S` is |

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

§5.3–§5.5 runs the same discipline: `lemma3_clause3_coordFS_top_crosscheck`,
`lemma3_clause2_top_crosscheck`, `prop32_coordFS_Efst_crosscheck`,
`prop32_biased_Efst_crosscheck`, `prop32_biased_E3_crosscheck`,
`thm3_coordFS_top_crosscheck` and
`thm3_coordFS_xorPart_witness` compute their claims from Definitions 31–37 and mention
none of `orthogonalGiven_tfae`, `Q_mul_Q_eq_of_orthogonalGiven`, `isDistribution_iff` or
`orthogonalGiven_iff_forall_isDistribution`; `lemma3_clause3_coordFS_top_applied`,
`lemma3_clause2_top_applied`, `prop32_coordFS_Efst_applied`,
`prop32_biased_Efst_applied`, `prop32_biased_E3_applied`, `thm3_coordFS_top_applied` and
`thm3_coordFS_xorPart_applied` are the applications, each stating the *same* proposition
as its partner. `lemma3_clause2_top_crosscheck` is the one to read first if the second
half of the discipline is in question: it states the endpoint's *divisibility*, exhibiting
the cofactor, rather than the cofactor identity — which would be a different proposition
sitting beside its twin.

**How that separation is checked, and how it is not.** The check is *textual*: a
cross-check names no endpoint, so reading the declaration — or grepping the file for the
endpoint's name — is what verifies it. `#print axioms` does **not** verify it once an
endpoint is proved: both groups then report the same
`[propext, Classical.choice, Quot.sound]`, so the command separates them only
while an endpoint is still `sorry`d, when the applications pick up `sorryAx` and the
cross-checks do not (during stage 5b's drafting it split the four §5.3–§5.5 pairs
exactly; with every endpoint now proved it is inert throughout §5). Do not read a clean
`#print axioms` as evidence that a witness is independent of the endpoint it checks.

§6 changes what is quantified over rather than adding vocabulary to `FactoredSet`:
Definitions 42–45 range over **models** of a sample space, so none of the §2–§5 witnesses
touches them. The same file therefore builds four models of two sample spaces and six
databases, and uses them to separate `Consistent`, `Complete` and `<_D` from each other.
The paper's own Examples 1 and 2 are *not* among them — those are §6.2's numbered nodes,
formalized in `InferenceExamples.lean`, and `Examples.lean` deliberately does not import
that file, so no witness below can lean on a §6.2 proof. Every *witness* below is in the
FFS-INVENTORY block; the two general statements the last row instantiates
(`OrthDatabase.not_strictlyBefore_self_of_consistent` and
`OrthDatabase.strictlyBefore_of_not_consistent`) are in the consumer-conveniences
`#assert_axioms_clean` block near the end of `AxiomAudit.lean` instead, since neither is a
paper node:

| Claim | Declarations | What it rules out |
|---|---|---|
| Definition 38 is inhabited, including where `f` is not a bijection and where the carrier is empty | `coordModel`, `boolModel`, `fstModel`, `pointModel`, `voidModel` | `Model` being uninhabited, and being read as "a factorization of `Ω`". `fstModel` is `coordFS` observed through `Prod.fst`: `S` has four points where `Ω` has two, which is the latent structure Definition 38 exists to allow. `pointModel` is the opposite extreme, a one-point carrier, and `voidModel` the degenerate end Definition 38 also admits — an empty carrier, where `<^F` is empty because there are no blocks to compare |
| Definition 39 is computed, and moves in both directions | `pullback_fstModel_bot`, `history_pullback_fstModel_bot`, `pullback_pointModel` | `f⁻¹` being a formality. Under `fstModel` the pullback of `Dis_Ω` — the *finest* partition of the sample space — is a *factor* of `S`, whose §3 history is the singleton `{fstFactor}`; under `pointModel` every partition of `Ω` pulls back to `Ind_S`. So a §6 statement is a statement about `S`, not about `Ω` |
| Definition 43 is a real condition, and Definition 42's two clauses are both exercised | `emptyDB`, `models_emptyDB`, `emptyDB_consistent`, `contradictoryDB`, `not_contradictoryDB_consistent`, `coordDB`, `models_coordDB`, `coordDB_consistent` | `Consistent` holding of everything, or of nothing. The empty database is modeled by every model; the database asserting one triple *both* ways has no model at all; and `models_coordDB` discharges both clauses of Definition 42 at once on the identity model of `coordFS`, from §4.3's own computations (`orthogonalGiven_fst_snd_top` and `not_orthogonalGiven_fst_fst_top`) rather than from anything in §6 |
| `Consistent` is **cheap on `O` alone** — it is `N` that constrains | `totalDB`, `totalDB_complete`, `totalDB_consistent`, `nonconstDB`, `nonconstDB_consistent`, `nonconstDB_forces_nonconstant`, `pullback_pointModel` | reading a large `O` as hard to satisfy. A database asserting *every* triple orthogonal is consistent, because a one-point model satisfies all of `O` simultaneously (a zero-dimensional factored set has no factors). What excludes that model is a single `N` entry: `(Dis_Ω, Dis_Ω, Ind_Ω)` forces every model's map to be non-constant, through Proposition 25 |
| `Consistent` and `Complete` are independent, in **both** directions | `not_emptyDB_complete`, `completeInconsistentDB` with `completeInconsistentDB_complete` and `not_completeInconsistentDB_consistent`, `totalDB_complete` with `totalDB_consistent`, `not_coordDB_complete` with `coordDB_consistent` | reading Definition 44 as a strengthening of Definition 43, as its converse, or as incompatible with it. `emptyDB` is consistent and not complete; `completeInconsistentDB` — asserting every triple *both* ways — is complete and not consistent, which is the direction the other witnesses leave open; `totalDB` is both; `coordDB` repeats the consistent-and-not-complete corner with both of its clauses non-empty |
| Definition 45 is irreflexive where it is informative and **vacuously total** where it is not, and infers nothing from an empty `N` | `OrthDatabase.not_strictlyBefore_self_of_consistent` and `OrthDatabase.strictlyBefore_of_not_consistent` (`Inference.lean`), instantiated by `not_nonconstDB_strictlyBefore_self`, `contradictoryDB_strictlyBefore_all`, together with `not_emptyDB_strictlyBefore` | `X <_D Y` being read as an inference regardless of `D`. It quantifies over models of `D`, so on an inconsistent database it holds of *every* pair; on a consistent one it is irreflexive, `<^F` being a strict inclusion of histories. This is why the paper proves consistency (Propositions 33 and 35) before it infers time (Propositions 34 and 36), and the consistency the second witness uses is computed here rather than cited from §6.2 |

The informative *positive* instances of Definition 45 — an actual inferred `X <_D Y` — are
Propositions 34 and 36 themselves. Nothing in `Examples.lean` stands in for them, and the
degenerate `contradictoryDB_strictlyBefore_all` is recorded precisely so that no reader
mistakes a vacuous `<_D` for one. At the other end, `not_emptyDB_strictlyBefore` closes the
loop on `emptyDB_consistent`: a database with `N = ∅` is consistent and infers *nothing*,
because `voidModel` — the empty-carrier model Definition 38 admits — models it and kills
`<^F` outright. Consistency is therefore not evidence of inferential content.

§7 adds the last layer, and it splits in two. §7.3's five definitions are stated over the
§3–§4 vocabulary, so nothing in §2–§6 exercises them; `Examples.lean` therefore runs them
over `coordFS` and its partitions. §7.2's Conjecture 1 is a `Prop` about
finite-*dimensional* factored sets, and **every factored set built for §2–§6 has a finite
carrier**, so none of them is in the part of the conjecture's range that Theorem 3 does not
already cover; a separate file, `InfiniteExamples.lean`, supplies factored sets outside §5's
finiteness boundary. The claims below are what those two files discharge; the rows name the
claim rather than every declaration, since the §7 witness sets are read most usefully as
claims. Two names in this section are *not* in the FFS-INVENTORY block, and neither is an
omission: `eventPartition` is an unannotated auxiliary and is inventoried nowhere (see the
§7.3 register in `AxiomAudit.lean`), and the general §7.3 relations a client reasons with
(`counterfactableRel_of_counterfactable`, `counterfactableRel_top`,
`beforeGivenSet_univ_iff`, `beforeGivenSet_empty`) live on the consumer surface — in
`EmbeddedAgency.lean` and `ConditionalOrthogonality.lean` — rather than in the witness
files:

| Claim | Witnesses | What it rules out |
|---|---|---|
| Definition 46's case split is real, and `eventPartition` computes on **both** sides of it | `eventPartition` evaluated on `coordFS` at an event that is neither empty nor all of `S` and at one that is (`Examples.lean`) | reading the `Setoid.comap (· ∈ E) ⊥` rendering as a reformulation nobody checked. The paper's two cases — `{S}`, and `{E, S \ E}` — are both realized by `Setoid.classes` of the same definition, which is the entire content of absorbing the split |
| Definition 46 is neither empty nor total, and its negative side is the paper's own reading | a positive `Observes` instance on `coordFS`, together with the paper's Newcomb and counterfactual-mugging configurations as *negative* instances (`Examples.lean`) | `Observes` holding vacuously or universally. The negatives matter more than the positive here: §7.3's point is that an agent may fail to observe an event it "knows", and a witness file that only exhibited positives would leave that unexercised |
| Definition 46's **second** clause is metered, not merely satisfied | a positive `Observes` instance whose conditioning set is not a block of the world model, so `h^F(W\|Eᶜ) ≠ ∅` (`Examples.lean`) | a positive witness that discharges clause 2 for a reason independent of the agent. Where `Eᶜ` *is* a block of `W`, `W\|Eᶜ` is indiscrete and clause 2 holds for **every** agent — which is the shape of the first positive instance, disclosed rather than repaired |
| Definition 47 is inhabited over a block-indexed family, so the reindexing is not vacuous | an `ObservesPartition` instance on `coordFS` (`Examples.lean`) | the `As : X.classes → Setoid S` rendering being unsatisfiable, or satisfiable only at a one-block `X` where the family carries no information |
| Definition 47's sub-agent decomposition does work, so it is not Definition 46 read blockwise | an `ObservesPartition` instance with a **non-constant** family `As`, and one whose clause-2 obligations are not automatic (`Examples.lean`) | reading `∃ As, A = ⋁_S(range As) ∧ …` as decoration. At a constant family `sInf (Set.range As) = A` by `sInf_singleton`, so the existential carries no information, and the earlier positive instance is exactly that case |
| Definition 48 separates partitions, and the separating example is the paper's | `Counterfactable` holding at a factor of `coordFS` and **failing** at the XOR / bleen-grue partition (`Examples.lean`) | `Counterfactable` being total. `X = ⋁_S(h^F(X))` is an equation, and the XOR partition is exactly the paper's illustration of a partition whose history recovers strictly more than itself |
| Definition 49 is inhabited, and separately from Definition 48 | a `CounterfactableRel` instance on `coordFS` (`Examples.lean`) | reading the relative notion as the absolute one with a spectator argument |
| Definition 50 is computed at a conditioning set that is not `S` | a `BeforeGivenSet` instance on `coordFS` (`Examples.lean`) | conditional time being exercised only where `restrict` is the identity, which is where it reduces to Definition 19 |
| Conjecture 1's range contains factored sets Theorem 3 does not reach — and factored sets *it* does not reach either | `natBoolFS` on `ℕ × Bool` (finite dimension, infinite carrier: inside the conjecture, outside Theorem 3) and `infFS` on `ℕ → Bool` (infinite dimension: outside both) (`InfiniteExamples.lean`) | reading Conjecture 1 as a restatement of Theorem 3, and reading it as a claim about arbitrary factored sets. The paper expects the *arbitrary*-dimensional version to be **false**, so the second witness marks a boundary rather than a gap |
| `isDistribution_diracAt`'s `[Finite F.B]` is load-bearing, not decorative | `infFS` (`InfiniteExamples.lean`) | reading that binder as a proof convenience. Over an infinite basis Definition 37's `∏ᶠ b ∈ B` returns the junk value `1` as soon as infinitely many factors separate two points, while the singleton probability there is `0` — so the statement is *false*, not merely unproved |
| Conjecture 1's right-hand side **discriminates** at `natBoolFS`, so its two sides are not identified there | `rich`, `rich_isDistribution`, `rich_discriminates` (`InfiniteExamples.lean`) | the conjecture's distribution family being inhabited only by point masses. `ProbDist.diracAt` satisfies `P(x∩z)·P(y∩z) = P(x∩y∩z)·P(z)` for **arbitrary** sets, so a family of point masses makes the right-hand side true at every triple and separates nothing — and, taken as the whole of `IsDistribution`, would make the right-hand side hold at a triple whose left-hand side `not_orthogonal_natFactor_self` refutes. `rich` is a non-point-mass Definition-37 distribution on `natBoolFS` at which the identity fails, which is the finite side's `not_orthogonalGiven_bot_bot_top_boolFS` moved outside the finiteness boundary |
| Conjecture 1's shape is exercised as a hypothesis, not just written down | the three `example`s that take `FundamentalTheoremFiniteDim` as a hypothesis and instantiate it at a witness (two in `InfiniteExamples.lean`, one in `APITests/FiniteFactoredSets.lean`) | the `Prop` being stated in a shape nothing ever applies. Its finite instance needs no separate declaration — that is Theorem 3 itself — so these three uses are the only check that the `Prop`'s binders are usable |

`APITests/FiniteFactoredSets.lean` carries the client-side half of the §7 non-vacuity, and
it is deliberately a different half: it consumes `FundamentalTheoremFiniteDim` as a
*hypothesis* and composes it with Proposition 24, applies Theorem 3 against Proposition 25,
and records the reductions
a client needs before reading a §7.3 fact as a §7 fact — Definition 46 at `E = ∅` is
Definition 18, Definition 50 at `E = S` is Definition 19, `Ind_S` observes everything, and
every factor is counterfactable. Those are compositions, not restatements, and none of them
imports `Examples.lean` or `InfiniteExamples.lean`.

One friction point a client will meet, recorded at the site: `Finite F.B` — the
hypothesis every §3.2–§3.4 theorem carries (Propositions 10 and 11 need none, and nothing
in §3 needs `S` finite) — is discharged by instance search on every witness, but
`Fintype F.B` is not. The reason is not a missing `DecidableEq`: under `open scoped
Classical`, `Setoid (Bool × Bool)` has one and `Fintype ↥({fstFactor, sndFactor} : Set _)`
is synthesized by `Set.fintypeInsert`. It is that `coordBasis` and `coordFS.B` are
non-reducible `def`s, which instance search will not unfold to reach that `insert`. A
client passes `Fintype.ofFinite _` by hand, and `natCard_eq_prod` needs it in scope at
*statement* elaboration time.
