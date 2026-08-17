# Finite Factored Sets — knowledge base

Institutional memory for this formalization: settled design decisions, the
correspondence table, paper errata, and pitfalls. Committed on purpose — a future
session (or auditor) reads this before touching the library. See `README.md` for the
trust surface and `FiniteFactoredSets.lean` for the `dd:` glossary.

## Settled design decisions

| Tag | Decision | Why |
|---|---|---|
| `dd:partition` | Partitions are `Setoid S` | Matches `CartesianFrames/`; repo coherence beats a bespoke `Finpartition`-based encoding. Note Mathlib *does* now have a bundled `Setoid.Partitions` with a `CompleteLattice` instance (`Mathlib/Data/Setoid/Partition.lean`), which the CF library's comment predates — but `Setoid` is what the whole lattice API is stated over, so it stays. |
| `dd:order-flip` | Use Mathlib's order, never the paper's glyphs | Carrying both conventions in one file is how sign errors get proved. |
| `dd:quotient` | `∏(B)` is `(b : B) → Quotient b` | Canonical; a presentation change, not a content change. |
| `dd:poly` | `Poly S := MvPolynomial (Set S) ℝ`; eval = `MvPolynomial.eval`, supp = `vars`, irreducible = Mathlib `Irreducible`; set sums via `finsum`/`finprod` | Blocks are variables verbatim under `dd:partition`. Definitions carry no finiteness; `[Finite S]` sits on the §5.1–5.2 *theorems* and helper lemmas whose statements quantify over `E ⊆ S` (the exact list is in API.lean, maintained per round — round 6 caught an undercount). `mono`/`monos`/`poly` take no `F` (paper superscript notational) — the `size` trap avoided at design time. |
| `dd:probability` | Definition 36 = `structure ProbDist S` (`P : Set S → ℝ`, nonneg, `P ∅ = 0`, `P univ = 1`, finitely additive); Definition 37 = predicate `FactoredSet.IsDistribution F P := ∀ s, P {s} = ∏ᶠ b ∈ F.B, P (part b s)`; `Q^F_E(P)` = `MvPolynomial.eval P.P (F.Q E)`; Theorem 3 stated division-free | Verbatim the paper's elementary definitions — no measure theory, no type-(c) substitution; a Mathlib-probability bridge would be a separate lemma, never a stand-in. Definitions carry no finiteness (finprod). A Dirac point mass IS a distribution on every factored set (product of point-mass marginals) — the non-distribution witness is `diagDist` (uniform on the diagonal). |
| `dd:subpartition` | A subpartition of `S` is a partial equivalence relation on `S` (`structure Subpartition`), domain `{s | r s s}` | Mathlib has no PER structure and `Σ E, Setoid E` would put dependent subtypes and domain transports into every §4 statement. The correspondence is exhibited (`toSetoid`, `ofSetoidOn`, round-trip lemmas). Payoff observed by the §4.1 shard: `X (χ_C s t) s` already implies `χ_C s t ∈ dom X` (`mem_dom_of_rel`), so half of Proposition 20's "extra condition" is free and Prop 21 clause 5 needs no `χ(E,E) = E` bookkeeping. |
| `dd:model` | Definition 38's model is `structure Model Ω`: implicit carrier `S`, a `FactoredSet S`, `f : S → Ω`, and — because Definition 38 says *finite* factored set — a `Finite S` **field**, registered as an instance | Finiteness is part of the object, not a hypothesis on statements: the one place §6 departs from `dd:finiteness-minimal`, and it departs in the strict direction, since Definitions 43 and 45 quantify over models, so "for all models" must already mean "for all finite ones". Consequence to carry: **no §6 declaration carries a finiteness binder**, and `Finite M.F.B` is found by instance search wherever `M : Model Ω` is in scope (`Model.finite` → `instFiniteSetoid` → `Subtype.finite`). `Ω` is unconstrained. Definition 39 is Mathlib-rendered (`Set.preimage`, `Setoid.comap`); `Model.pullback` is a named alias for its third clause carrying no node annotation. Definition 41's `NotOrth` is a positive assertion *of the database*, not the negation of `Orth` — a database may assert both (Definition 43 then fails) or neither (Definition 44 fails). |
| history | `history X := ⋂₀ {C | C ⊆ F.B ∧ Generates C X}` | Definition 17's "smallest generating subset". `history_isLeast` (Proposition 12) is what earns "smallest", and it needs `[Finite F.B]` **genuinely**: over `S = ℕ → Bool` with the coordinate factors, every cofinite subset of `B` generates the "eventually equal" partition, so the intersection of all generating subsets is `∅`, which generates nothing. All of §3 is stated with `Finite F.B` (finite *dimension*) and never `Finite S`. |

## The order inversion — read this before writing any order statement

**The paper's order glyphs run opposite to Mathlib's.** This is the single most likely
source of a silently-wrong statement in this development.

* Definition 6: "`X` is finer than `Y`" means `s₀ ∼_X s₁ → s₀ ∼_Y s₁`. Mathlib's
  `Setoid.le_def` says exactly this for `X ≤ Y`. So **paper-finer = Mathlib `≤`**.
* But the paper *writes* finer as `X ≥_S Y` (Proposition 2: "`Dis_S ≥_S X` and
  `X ≥_S Ind_S`"). So **the paper's `≥_S` is Mathlib's `≤`**, and vice versa.
* Definition 8's common refinement `⋁_S(C)` is defined by `s₀ ∼ s₁ ↔ ∀ Y ∈ C, s₀ ∼_Y s₁`.
  That is relation *intersection*, i.e. Mathlib's `sInf` — `Setoid.sInf_iff` is the
  defining property verbatim. **The paper's join glyph is Mathlib's meet.**
* `Dis_S` (discrete) is Mathlib's `⊥`; `Ind_S` (indiscrete) is Mathlib's `⊤`.

When reading a card in `docs/trust-surface.html`, this is the one place the paper
statement and the Lean statement will look like they disagree when they do not.

## Triviality and the empty set — a real trap

Definition 3 calls a partition trivial when `|X| = 1`, and Definition 7 sets `Ind_S = {}`
when `S` is empty. So **the empty set's indiscrete partition has no blocks and is not
trivial.**

Hence `IsTrivialPartition b := Nonempty S ∧ ∀ s t, b s t`, not just `∀ s t, b s t`. The
`Nonempty S` conjunct is `|X| = 1` rather than `|X| ≤ 1`.

The consequence runs the other way too: rendering *non*triviality as the obvious
`∃ s t, ¬ b s t` (which the feasibility spike did) is **wrong** — it is false over the
empty type, so it would wrongly forbid every partition of the empty set from being a
factor. Use `¬ IsTrivialPartition`.

And nontriviality is load-bearing, not decoration: Definition 10 builds it into the
definition of a factorization, and Corollary 1 (`basisdisjoint`) is proved from it. Drop
it and the indiscrete partition of a one-element set becomes a legal factor, so both `{}`
and `{Ind}` factor that set — falsifying Proposition 5's *uniqueness* of the trivial
factorization. This was the spike's main finding; see `notes/spike-2026-08-15.md`.

## Pitfalls

* **`Setoid.trans` / `symm` / `refl` take the setoid as an instance argument.** Any proof
  with two setoids in scope (which, in a paper about *sets of* partitions, is most of
  them) will resolve to the wrong one and fail with a confusing "synthesized type class
  instance is not definitionally equal" error. Use the primed `b.trans'`, `b.symm'`,
  `b.refl'`, which take it explicitly. Expect to need these everywhere.
* **`h ▸ e` often picks the wrong rewrite direction** on `part` equalities. Bind the
  rewritten fact with an explicit `have hs : s ∈ part b t := h ▸ …` and then use `hs`;
  the type ascription pins the motive.
* **`exact absurd (Finset.mem_antidiagonal.2 rfl) h` loops in `whnf`** (200k heartbeats)
  on the `Finsupp` antidiagonal instance. `simp only [Finset.mem_antidiagonal] at h`
  first is instant. This will matter again in §5.
* **`lake build -j4` is not valid on this toolchain (Lake 5 / Lean 4.31 has no `-j`).** It
  dies with `unknown short option '-j'`, and piped through `tee` the pipeline exits 0 — a
  30-second "green build" that compiled nothing. Cap with
  `LAKE_NUM_JOBS=4 LEAN_NUM_THREADS=4 lake build <target>`; if you pipe, read
  `${PIPESTATUS[0]}`. (Same trap explains a fixer's report that
  `check-finite-factored-sets-nodes.py` "exits 0 on violations" — it exits 1; `$?` after
  `| tail` was `tail`'s.)
* **`#assert_axioms_clean` reports only the first tainted declaration in its list.** One
  error line does not mean one tainted endpoint; enumerate with `#print axioms` in a
  scratch file when several could be affected.
* **Never write the literal string `Paper node:` in prose** — not even in a `/-! -/` block
  explaining the convention. The node checker greps the bare string and reports it as a
  malformed, unanchored annotation. Say "the annotated paper statements" instead.
* **All setoids on an empty type are equal**: `Setoid.ext fun a _ => (IsEmpty.false a).elim`
  proves `X = Y` outright (this is stronger than the `(⊥ : Setoid Empty) = ⊤` note above),
  which is how Proposition 17's "if `S` is empty then `X = Y`" branch is discharged.
* **`Setoid.refl'` is `@[refl]`**, so the `rfl` that `rw` tries afterwards closes `X s s`
  goals by itself; a following `exact X.refl' s` fails with "no goals".  Bit again in
  stage 6 — the failure is confusing because the error points at the *next* tactic, not the `rw`.
* **`List.TFAE.out` has autoparam arguments**: `((h.out 0 5).1 hyp) s t` fails to elaborate
  in term mode. Bind with an explicitly typed `have h6 : ∀ s t, … := (h.out 0 5).1 hyp` first
  (the in-file `example` in `History.lean` demonstrates it).
* **`Set.Finite.induction_on`'s motive takes the set and its finiteness proof**, so every
  hypothesis mentioning the set must be to the right of the colon (arrow form) — otherwise
  `induction 𝒞, hfin using Set.Finite.induction_on` fails to generalize. Case names are
  `empty` and `insert`, binders implicit: `| @insert a s _ _ ih =>`. Proposition 12 is proved
  by threading a generating `D` through the induction (`generates_inter_sInter`) so the
  empty base case is `D ∩ ⋂₀ ∅ = D`; that is how the paper's "nonempty collection, since
  `B ⊢ X`" side condition is discharged (instantiate `D := F.B` at the end).
* **`Setoid`'s `≤` is a bare `∀ ⦃x y⦄, r x y → s x y`**, not routed through an order-class
  projection: `h : Y ≤ X` applies directly as `h hxy`, and `intro s t hst` works straight
  off a `commonRefinement C ≤ X` goal. No `Setoid.le_def` glue needed.
* **`part X s ∈ X.classes` is `X.mem_classes s` by delta** — no `show`, no rewrite.
* **`Set.diff_subset` is deprecated** for `Set.sdiff_subset` in this Mathlib.
* **A `def` under `variable (F : FactoredSet S)` that does not mention `F` in its body does
  not take `F`.** `size` was stated that way in stage 2: it was inventoried, axiom-clean, and
  unusable — `F.size` did not elaborate — and survived a full audit round because nothing
  exercised it. Now `def size (_F : FactoredSet S)`. Every endpoint gets an in-file `example`
  applying it the way a client would; this is the defect class that rule exists for.
* **Do not `cd` into `.lake/packages/…` and run `lake` there.** It creates a nested
  `.lake` with its own package clones *inside* the dependency, and cleaning it up is easy
  to overdo — deleting `.lake/packages/mathlib/.lake` also deletes mathlib's built
  oleans. Recovery is `lake exe cache get` (fast); the lesson is to use absolute paths
  from the repo root.

## Correspondence table

Paper node → Lean declaration. Extended as nodes land.

| Node | Lean | File |
|---|---|---|
| Definition 3 (trivial partition) | `IsTrivialPartition` | `Basic.lean` |
| Definition 4 (`[s]_X`) | `part` | `Basic.lean` |
| Definition 8 (common refinement) | `commonRefinement` | `Basic.lean` |
| Definition 10 (factorization) | `IsFactorization` | `Basic.lean` |
| Definition 11 (factored set) | `FactoredSet` | `Basic.lean` |
| Definition 12 (chimera function) | `FactoredSet.chimeraFun` | `Basic.lean` |
| Definition 13 (`χ^F_C(s,t)` and setwise `χ^F_C(T,R)`) | `FactoredSet.chimera`, `FactoredSet.chimeraImage` | `Basic.lean` |
| Proposition 1 | `equivalence_setoid` | `Basic.lean` |
| Proposition 2 | `bot_le_and_le_top` | `Basic.lean` |
| Proposition 3 | `FactoredSet.eq_of_forall_rel` | `Basic.lean` |
| Proposition 4 | `FactoredSet.chimera_spec` | `Basic.lean` |
| Theorem 1 | `isFactorization_iff_existsUnique` | `Basic.lean` |
| Corollary 1 | `FactoredSet.eq_of_part_eq` | `Basic.lean` |
| Definition 14 (trivial factorization) | `IsTrivialFactorization` | `Basic.lean` |
| Definition 15 (size, dimension) | `FactoredSet.size`, `FactoredSet.dim` | `Basic.lean` |
| Proposition 5 (both sentences: `.1` uniqueness, `.2.1`/`.2.2` the identification) | `existsUnique_trivialFactorization` | `Basic.lean` |
| Proposition 6 | `FactoredSet.finite_basis_of_finite` | `Basic.lean` |
| Proposition 7 | `FactoredSet.size_eq_prod` (ℕ form: `natCard_eq_prod`) | `Basic.lean` |
| Proposition 8 | `isTrivialFactorization_of_isFactorization` | `Basic.lean` |
| Proposition 9 | `FactoredSet.dim_spec` | `Basic.lean` |
| Definition 16 (generates, `C ⊢^F X`) | `FactoredSet.Generates` | `History.lean` |
| Proposition 10 | `FactoredSet.generates_tfae` (clause 6: `generates_iff_rel`; clause 7: `generates_iff_sInf_le`) | `History.lean` |
| Proposition 11 | `FactoredSet.generates_spec` | `History.lean` |
| Definition 17 (history `h^F`) | `FactoredSet.history` | `History.lean` |
| Proposition 12 | `FactoredSet.history_isLeast` (helpers `generates_history`, `generates_iff_history_subset`, `le_iff_history_subset`) | `History.lean` |
| Proposition 13 | `FactoredSet.history_spec` | `History.lean` |
| Definition 18 (orthogonal, `X ⊥^F Y`; entangled) | `FactoredSet.Orthogonal`, `FactoredSet.Entangled` | `Orthogonality.lean` |
| Proposition 14 | `FactoredSet.orthogonal_iff_exists` | `Orthogonality.lean` |
| Proposition 15 | `FactoredSet.orthogonal_spec` | `Orthogonality.lean` |
| Definition 19 (before, strictly before) | `FactoredSet.Before`, `FactoredSet.StrictlyBefore` | `Orthogonality.lean` |
| Proposition 16 | `FactoredSet.before_iff_forall_sInf` | `Orthogonality.lean` |
| Proposition 17 | `FactoredSet.before_iff_forall_orthogonal` | `Orthogonality.lean` |
| Proposition 18 | `FactoredSet.before_spec` | `Orthogonality.lean` |
| Proposition 19 | `FactoredSet.history_eq_setOf_before` | `Orthogonality.lean` |
| Definition 20 (subpartition) | `Subpartition` (`dd:subpartition`) | `Subpartition.lean` |
| Definition 21 (domain) | `Subpartition.dom` | `Subpartition.lean` |
| Definition 22 (`X|E`) | `Subpartition.restrict` (for a partition of `S`: `(ofSetoid X).restrict E`) | `Subpartition.lean` |
| Definition 23 (generating a subpartition) | `FactoredSet.GeneratesSub` (working clause 5: `generatesSub_iff_rel`) | `Subpartition.lean` |
| Proposition 20 | `FactoredSet.generatesSub_tfae` | `Subpartition.lean` |
| Proposition 21 | `FactoredSet.generatesSub_spec` | `Subpartition.lean` |
| Definition 24 (history of a subpartition) | `FactoredSet.historySub` | `SubpartitionHistory.lean` |
| Proposition 22 | `FactoredSet.historySub_isLeast_and_eq_history` (`.1 X` least; `.2 X` agrees with `history` on `ofSetoid X`) | `SubpartitionHistory.lean` |
| Proposition 23 | `FactoredSet.historySub_spec` | `SubpartitionHistory.lean` |
| Lemma 1 | `FactoredSet.historySub_restrict_part_eq` | `SubpartitionHistory.lean` |
| Lemma 2 | `FactoredSet.historySub_inf_eq` | `SubpartitionHistory.lean` |
| Definition 25 (`⊥`, `≤`, `<` on subpartitions) | `FactoredSet.OrthogonalSub`, `BeforeSub`, `StrictlyBeforeSub` | `ConditionalOrthogonality.lean` |
| Definition 26 (`X ⊥ Y | E`) | `FactoredSet.OrthogonalGivenSet` | `ConditionalOrthogonality.lean` |
| Definition 27 (`X ⊥ Y | Z`) | `FactoredSet.OrthogonalGiven` | `ConditionalOrthogonality.lean` |
| Proposition 24 | `FactoredSet.orthogonal_iff_orthogonalGiven_top` | `ConditionalOrthogonality.lean` |
| Theorem 2 (semigraphoid) | `FactoredSet.orthogonalGiven_semigraphoid` | `ConditionalOrthogonality.lean` |
| Proposition 25 | `FactoredSet.orthogonalGiven_self_iff` | `ConditionalOrthogonality.lean` |
| Definition 28 (`Poly^F`) | `Poly` (abbrev; depends on `S` only) | `Polynomial.lean` |
| Definition 29 (evaluation) | Mathlib `MvPolynomial.eval` (rendered, README table) | — |
| Definition 30 (support) | Mathlib `MvPolynomial.vars` (rendered, README table) | — |
| Definition 31 (`Q^F_E`) | `FactoredSet.Q` (`Q_eq_finsum_mono`, `Q_eq_sum`) | `Polynomial.lean` |
| Definition 32 (`mono^F_C(s)`) | `mono` (no `F`) | `Polynomial.lean` |
| Definition 33 (`monos^F_C(E)`) | `monos` (no `F`; an *image*, so coincident monomials collapse) | `Polynomial.lean` |
| Definition 34 (`poly^F_C(E)`) | `poly` (no `F`; `poly_eq_sum_image`, `poly_empty`) | `Polynomial.lean` |
| Proposition 26 | `FactoredSet.Q_eq_poly` | `Polynomial.lean` |
| Proposition 27 (`factor1`) | `FactoredSet.poly_union_chimeraImage` | `Polynomial.lean` |
| Proposition 28 (`factor2`) | `FactoredSet.eq_C_mul_poly_of_dvd_Q` | `Polynomial.lean` |
| Definition 35 (`Irr^F(E)`) | `FactoredSet.irr` (`mem_irr`) | `Factoring.lean` |
| Proposition 29 | `FactoredSet.irr_partition` (§4 restatement `irr_isPartition`) | `Factoring.lean` |
| Proposition 30 | `FactoredSet.Q_eq_finprod_poly_irr` (divisibility form `poly_dvd_Q`) | `Factoring.lean` |
| Proposition 31 | `FactoredSet.irreducible_poly_of_mem_irr` | `Factoring.lean` |
| Lemma 3 (`CPO`) | `FactoredSet.orthogonalGiven_tfae` (isolated: `Q_mul_Q_eq_of_orthogonalGiven` = `.out 0 2`, `orthogonalGiven_of_Q_mul_Q_eq` = `.out 2 0`) | `CharacteristicOrthogonality.lean` |
| Definition 36 (probability distribution on `S`) | `ProbDist` (fields frozen) | `Probability.lean` |
| Definition 37 (distribution on `F`) | `FactoredSet.IsDistribution` | `Probability.lean` |
| Proposition 32 | `FactoredSet.isDistribution_iff` | `Probability.lean` |
| Theorem 3 (fundamental theorem) | `FactoredSet.orthogonalGiven_iff_forall_isDistribution` | `Probability.lean` |
| Definition 38 (model of a sample space) | `Model` (`dd:model`; `Finite S` is a field) | `Inference.lean` |
| Definition 39 (preimages under `f`) | Mathlib `Set.preimage` (points, subsets) and `Setoid.comap` (partitions), rendered — README table; convenience alias `Model.pullback` (`pullback_apply`), no node line | — |
| Definition 40 (orthogonality database) | `OrthDatabase` | `Inference.lean` |
| Definition 41 (asserted orthogonal / asserted not orthogonal) | `OrthDatabase.Orth`, `OrthDatabase.NotOrth` (two carriers, one per written form) | `Inference.lean` |
| Definition 42 (a model models a database) | `OrthDatabase.Models` | `Inference.lean` |
| Definition 43 (consistent) | `OrthDatabase.Consistent` | `Inference.lean` |
| Definition 44 (complete) | `OrthDatabase.Complete` | `Inference.lean` |
| Definition 45 (`X <_D Y`) | `OrthDatabase.Before` | `Inference.lean` |
| Example 1 | `Example1.D` | `InferenceExamples.lean` |
| Proposition 33 | `Example1.D_consistent` | `InferenceExamples.lean` |
| Proposition 34 | `Example1.before_X_Y` | `InferenceExamples.lean` |
| Example 2 | `Example2.D` | `InferenceExamples.lean` |
| Proposition 35 | `Example2.D_consistent` | `InferenceExamples.lean` |
| Proposition 36 | `Example2.before_X_Y_Z` | `InferenceExamples.lean` |

Nodes deliberately rendered by Mathlib vocabulary with no declaration of ours
(Definitions 2, 5, 6, 7, 9) are tabulated in `README.md`.

## Node numbering — how to cite

The paper's counters are **independent and global per environment**: no `[section]`
argument, no shared counters, no resets. `Definition 1`…`Definition 50` run the length of
the paper alongside `Proposition 1`…`Proposition 36`. This is the `printed-independent`
scheme in `scripts/paper_nodes.py`, added for this paper.

Two source hazards, both handled in `paper_nodes.py`:

* the environments from `miritools.sty` are declared inside an `\if@environments`
  conditional, while `main.tex` declares `example`, `conjecture`, `proposition`,
  `corollary` and `lemma2` itself;
* **`lemma2` is a second counter that also prints "Lemma"**, and it carries all three
  printed Lemmas — the `lemma` counter is never used. A checker emulating `lemma` finds
  zero lemmas. `paper_nodes.py` maps environments to printed names explicitly and fails
  closed if two environments sharing a printed name are both used.

Do not trust a node number recalled from memory. The spike miscited `factor2` as
"Proposition 20" (it is **Proposition 28**; 20 is `equivsgen`) and Theorem 1 as
"Theorem 2". Recompute with `printed_independent_declarations` or run the checker.

## Intentional deviations

**Proposition 4 is stated for unrestricted `C, D`.** The paper fixes `C, D ⊆ B`;
`chimera_spec` leaves them arbitrary. This is *stronger*, not weaker: `chimera` consults
`C` only at `b ∈ F.B`, so `chimera C = chimera (C ∩ F.B)`, and all eleven clauses survive
(clauses 4 and 10 are the ones that could have broken; they don't). The price is that
clause 1 carries an explicit `c ∈ F.B` guard the paper gets for free — a client holding
`hC : C ⊆ F.B` discharges it as `hC hc`, and that implication is compiled. Raised as a
faithfulness defect in round 1 (R1-F05) and refuted; do not re-raise.

**Definition 16's `Generates C X` is likewise stated for unrestricted `C`** (the paper takes
`C ⊆ B`), for the same reason: `chimera` ignores non-factors, so
`Generates C = Generates (C ∩ F.B)`. All six clauses of Proposition 11 hold with `C`, `D`
arbitrary — clause 5 (monotonicity) goes through Proposition 4's union clause rather than
`sInf`-monotonicity. `C ⊆ B` is load-bearing in exactly one *generation* step: the `7 → 1` leg of
Proposition 10 (`sInf C ≤ X → Generates C X`), which is why `generates_tfae` and
`generates_iff_sInf_le` take `hC : C ⊆ F.B`; `6 → 7` needs no subset hypothesis. Executable
witness (round 2): over `coordFS`, `C = {⊥} ⊄ B` satisfies clause 7 but not clause 1. The
*history* lemmas `history_subset_of_generates`, `generates_iff_history_subset`,
`le_iff_history_subset` also take `hC`, for a different reason — membership in `history`'s
defining family `{C | C ⊆ F.B ∧ Generates C X}` requires it definitionally. Do not add subset
hypotheses to `generates_spec` "for symmetry", and do not strip them from those three.

**Definitions 32–34's `mono`/`monos`/`poly` are stated for unrestricted `C`** (the paper takes
`C ⊆ B`); forced by `dd:poly` (they take no `F`, so there is nothing to state `C ⊆ B`
against) and harmless — every theorem needing squarefreeness carries `hC : C ⊆ F.B`. Third
instance of the Proposition 4 / Definition 16 pattern; do not re-raise.

**Propositions 7–9 are stated over `Cardinal`s with no `[Finite S]`** (Props 7 and 9 over
`size`/`dim`; Prop 8 over `Cardinal.mk S`, since it quantifies over a bare basis with no
`FactoredSet` in scope — `size` is definitionally `Cardinal.mk S`, bridged by `size_eq_mk`). The
paper's standing "finite factored set" hypothesis is implied by each clause's own
hypothesis (`= 0`, `= 1`, `= p`, `= l.prod`), and Proposition 7 holds for every factored
set (`size_eq_prod` is `Cardinal.mk_congr F.coord` + `Cardinal.mk_pi`). Proposition 9's
"product of `k ≥ 2` primes" is a `List ℕ` of primes of length `≥ 2` whose product is the
size. This is `dd:finiteness-minimal` applied to §2.5, not a strengthening anyone should
re-audit as drift.

## Open trust-surface caveats

**Reopened by stage 5a, closing in round 6.** Props 27 and 31 had no witness when §5.1–5.2
landed (Lens A, R6-F03); round 6 lands them. Non-vacuity is discharged by construction in
`Examples.lean` — §2 witnesses in round 1 (R1-F01), §3 witnesses on `coordFS` (history,
orthogonality, time, the XOR partition) in round 2 (R2-F03), §4 witnesses (subpartition
histories, the superset-non-monotonicity counterexample, conditioning on the XOR partition
entangling the coordinate factors, Lemmas 1–2 / Theorem 2 instantiated) in round 4
(R4-F01 — every stage that lands new vocabulary reopens this caveat until its witnesses
land; the stage commit itself does not close it). This section exists so that a future
session reading only this file learns of any caveat the README carries — round 1 found the
two registers out of step, which is exactly the failure this heading prevents.

## Disclosures

None. There are no type-`(c)` modeling substitutions in the current surface.

## Paper errata

Recorded in `notes/paper-errata.md` (registered in `scripts/papers.py`) — that file is
canonical; read it before concluding a Lean proof diverges from the printed one. Seven
typos so far, none changing a statement. E1–E3 in §4.2 (E1 `h^Y(Y)` for `h^F(Y)` in Prop
23(1); E2 `x_0` for `x_1` in Lemma 2's proof; E3 `⋁_E` for `⋁_S` in Prop 23(2)'s proof).
E4–E7 in §6.2's proofs: E4 Prop 36 cites `X ⊥_D Y | {Ω}` for `H_X ∩ H_V = {}` where the
database asserts `X ⊥_D V | {Ω}`; E5 Prop 36 cites `¬(Y ⊥_D Z | {Ω})` where `N` contains
`(V,Z,{Ω})`; E6 `h_Z` for `H_Z`; E7 Prop 34's proof writes `H_Y ∩ H_V` where Prop 13
clause 2 gives the union (Prop 36 states the same step correctly). E4, E5 and E7 matter to
anyone diffing the Lean against the page — the Lean cites different database entries, and
uses the union; do not re-raise as divergences.

## Open questions

* ~~Scope of §7~~ — **settled by Anson, 2026-08-16.**  See "Scope" below.
* ~~How `B`'s finiteness is carried into §5~~ — **settled.** Proposition 6 is proved
  (`FactoredSet.finite_basis_of_finite`), so `Finite F.B` is *derived* from `Finite S`, not
  assumed. The supporting `instFiniteSetoid` (`Finite α → Finite (Setoid α)`, absent from
  Mathlib) is repo-generic and upstreamable. Note the converse fails — a finite-dimensional
  factored set may have infinite size — which is exactly why `dd:finiteness-minimal` keeps
  the two conditions apart rather than collapsing them into one `Fintype`.

## Scope (Anson's ruling, 2026-08-16): 96 of 98 nodes

**In:** §1–§6 in full; §7's Definitions 46–50 (embedded agency); and **Conjecture 1,
stated as a Lean `Prop` and deliberately not proved**, carrying a citation.

**Out:** Examples 3 and 4 only. Both are about `S = 𝒫(ℕ)` — *infinite* factored sets —
and the paper itself expects the fundamental theorem to fail there; Example 3 is its
intended counterexample. Excluding exactly the case the paper predicts is false is a
defensible line; "we stopped at §6" is not.

### Consequence: keep finiteness minimal, starting now

Stating Conjecture 1 at all requires the definitions to *admit* the finite-dimensional
case — `B` finite, `S` possibly infinite. So:

* `FactoredSet` stays over an arbitrary `S : Type u` with **no** `Fintype S`. It already
  is; keep it that way.
* §3–§4 (history, orthogonality, time, subpartitions, conditional orthogonality, the
  semigraphoid axioms) must be stated with **`Finite B` only**. None of that material
  touches polynomials, so none of it needs `|S|` finite.
* A separate `FiniteFactoredSet` notion (finite `S`) is layered on top and introduced
  only where §5 demands it — *not* as the primitive.

Why §5 is the boundary, precisely: `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b`. With `|B|` finite
each monomial still has finite degree `|B|`, but the **sum ranges over `E ⊆ S`**. If `S`
is infinite, `Q^F_E` is not a polynomial — `MvPolynomial` is inapplicable, "divides" is
meaningless, `Irr^F(E)` does not exist, and Theorem 3's "vanishes on an open set ⇒ zero
polynomial" step has nothing to apply to. **The §5 apparatus is the sole reason `|S|`
must be finite**, which is exactly what the paper means by having assumed finiteness
"fairly gratuitously" (§7.2).

### On Conjecture 1's status — state it, do not attempt it

Do not spend prover time on it. Garrabrant expects it true and expects the
*arbitrary*-dimensional version false. Matthias Georg Mayer has since proved the
fundamental theorem for finitely factored **measurable** spaces — finitely many factors,
infinite state space — in "The Fundamental Theorem for measurable factor spaces"
(LessWrong, 2023-11-12) and, in mature form, *A Theory of Structural Independence*
(arXiv:2412.00847), which carries a `history` function directly descended from this
paper's. Two caveats before calling the conjecture closed: the published form is the
*unconditional* statement (orthogonal iff independent in all product distributions),
whereas Theorem 3 is conditional on a partition `Z`; and measurable structure is an extra
hypothesis a bare finite-dimensional factored set does not carry. So the accurate claim is
**resolved in a measurable refinement, not as literally stated** — which is precisely why
it belongs in the library as a stated open `Prop` with this note attached.

## Stage 3 (Props 7–9, §3) — durable lessons

* **`le_iff_history_subset`** (`History.lean`): for `C ⊆ B`, `commonRefinement C ≤ X ↔
  F.history X ⊆ C` — Proposition 10 clause 7 composed with Proposition 12, and literally the
  sentence the paper opens Proposition 16's proof with. Every §3.3–§3.4 proof runs on it plus
  `orthogonal_iff_forall_notMem`; once they exist, §3.3–§3.4 is pure set algebra over
  `history` and no finiteness argument is redone. Budget §4 similarly.
* Proposition 15 clause 1 and the forward direction of Proposition 17 need neither
  `Finite F.B` nor `Nonempty S`; the theorems carry `[Finite F.B]` uniformly for legibility.
* Proposition 9 clause 4 counts with `Ω` (`ArithmeticFunction.cardFactors`), additive over
  products and `≥ 1` on every factor `≥ 2`; `card_le_length_of_prod_eq` in `Basic.lean` is
  the three-line version of the paper's "impossible since `|S|` is a product of `k` primes".
* `one_lt_natCard_quotient` is where Propositions 8–9's *counting* uses Definition 10's
  nontriviality (Prop 9's `size = 1` clause uses it again through
  `isFactorization_singleton_bot_iff`); it needs `Nonempty S` and genuinely fails over the
  empty set (`emptyFS`: `Nat.card (Quotient ⊥) = 0`).

## Round 2 audit — durable lessons

* **Round 2 verdict shape**: 22 findings, 0 blockers, all six MAJORs refuted or reduced by
  cross-family adjudication (codex up this round; every channel ran); the residue was
  register drift and unexercised endpoints. Both codex sweeps completed with JSON arrays.
* **§3 order glyphs are executably pinned on `coordFS`** (lens A2): the reversed readings of
  Prop 10(7), 13(1), 13(2) (`⊔` for `⊓`), 15(2), 18(3) are each refutable; discriminators
  `X = fstFactor, Y = ⊤` (`h ⊤ = ∅`, `h fst = {fst}`), and for Prop 10(7) `C = {fstFactor},
  X = ⊥` (the reversed reading is vacuous at `X = ⊥` via `bot_le` and both readings hold at
  `⊤`). Reuse before re-litigating any §4 glyph.
* **`coordFS` landmarks**: `history fst = {fst}`, `history ⊥ = {fst, snd}`, `history ⊤ = ∅`,
  `Orthogonal fst snd`, `¬Orthogonal fst fst`, `¬Before ⊥ fst`, `¬Before fst snd`;
  `fstFactor ⊓ sndFactor = ⊥` is `Setoid.ext fun p q => ⟨fun h => Prod.ext h.1 h.2, fun h =>
  ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩`. **`history` is not injective**: the XOR
  partition `Setoid.comap (fun p => p.1 != p.2) ⊥` has `history = B = history ⊥` while
  `≠ ⊥`, so `Before` is a preorder that is genuinely not antisymmetric — do not "fix" it into
  a partial order; Definition 19 is history-inclusion.
* **`[Finite F.B]` is genuinely consumed by every §3.2–§3.4 theorem** (delete it and the
  proofs fail at the first `history_spec`/`le_iff_history_subset` call), though Prop 13
  clauses 1 and 4 and Prop 15(1)/Prop 17(→) are provable without it; uniform `[Finite F.B]`
  is a legibility choice. `Finite F.B` resolves by instance search on every concrete witness
  (`instFiniteSetoid` + `Subtype.finite`); `Fintype F.B` does NOT — and **not** because `Setoid` lacks
  `DecidableEq` (under `open scoped Classical`, `#synth DecidableEq (Setoid (Bool × Bool))`
  succeeds and so does `Fintype ↥{fstFactor, sndFactor}`); it fails because `coordBasis` /
  `coordFS.B` are non-reducible `def`s that instance search will not unfold. Pass
  `Fintype.ofFinite _` explicitly to `natCard_eq_prod` (round 3 correction, R3-F09).
* **`Nonempty S` in Prop 13(4) and Prop 19 is load-bearing**: both are false on `emptyFS`
  (`h ⊥ = ∅` there, yet `⊥ ∈ B`). Witnessed in `Examples.lean`.
* Cleared suspicions (do not re-raise): `Setoid.classes` is the paper's block set including
  empty `S` (`classes = ∅ = Ind_∅`); `isTrivialFactorization_of_isFactorization`'s
  conclusion containing its hypothesis is Definition 14's shape; `natCard_eq_prod`'s
  `[Fintype]` is forced by `∏` notation and it is an internal helper — `size_eq_prod` is the
  Prop 7 endpoint; the FFS-INVENTORY block deliberately lists non-vacuity witnesses
  alongside nodes (the checker enforces annotated ⊆ inventory, not equality);
  `instFiniteSetoid`/`subsingleton_setoid`/`cardFactors_finsetProd` are genuinely absent
  from Mathlib; the repo has no shared utility library, so repo-generic helpers living in a
  paper directory is the existing convention.
* Tactic traps: `decide` never works on a `Setoid` relation (no `DecidableRel`; with
  `Classical` it whnf-sticks) — write relation facts by hand (`rfl` / `Bool.noConfusion`);
  `commonRefinement {b} ≤ X` needs `commonRefinement_iff`, not `sInf_singleton`-by-`rfl`;
  `Cardinal` arithmetic (`2 * 2 = 4`) is `norm_num`, not `rfl`; `List.TFAE.out` indices are
  0-based (`.out 0 5` = clause 6) and need a typed `have` in both directions;
  `obtain`-introduced class hypotheses are local instances (don't clean them to `-`);
  `open scoped Classical` at Basic.lean's chimera block scopes to its `end FactoredSet` —
  the later §2.5 block and client examples are outside it (which is why `by decide` on
  `Nat.Prime` works there).
* **`Cardinal.eq_one_iff_unique : #α = 1 ↔ Subsingleton α ∧ Nonempty α`** is the `|S| = 1`
  bridge — do not write a local one; also `Cardinal.mk_eq_one`, `Nat.card_eq_one_iff_unique`,
  and `Cardinal.prod_const'` (unprimed `prod_const` carries `lift`s and won't close a
  same-universe goal). `rw [funext h]` turns `Cardinal.prod fun b => …` into a constant
  product directly; there is no `Cardinal.prod_congr`.
* `one_lt_natCard_quotient` takes `[Finite (Quotient b)]`, the minimal form (R2-F02); callers
  with `Finite S` get it via `Quotient.finite`. `size_eq_mk`/`dim_eq_mk` (`@[simp]`) and
  `dim_eq_zero_iff` are public (R2-F16) but deliberately uninventoried — the inventory lists
  annotated endpoints + witnesses, not every public lemma.
* Definition 15's third sentence (finite / finite-dimensional) has no Lean carrier — it is
  `[Finite S]` / `Finite F.B` under `dd:finiteness-minimal`; record it in the README's
  Mathlib-rendered table when the layered finite-`S` notion lands at §5.

## Stage 4 (§4) — durable lessons

* **A skeleton helper was false and a fixer caught it**: `GeneratesSub C X ↔ historySub X ⊆ C`
  (the naive §4 analogue of `generates_iff_history_subset`) is FALSE — subpartition
  generation is closed under union but **not under supersets** (the paper says so after
  Prop 21). Compiled counterexample on `coordFS`: `E = {(false,false),(true,true)}`,
  `X = indiscrete E`: `historySub X = ∅ ⊆ {fstFactor}` but `χ_{fst}((f,f),(t,t)) = (f,t) ∉ E`.
  The true form carries Prop 20 clause 7's second half:
  `↔ historySub X ⊆ C ∧ ∀ s ∈ X.dom, ∀ t ∈ X.dom, χ_C s t ∈ X.dom`. **Never reason as if
  `GeneratesSub` were monotone in `C`.** The reusable replacement for monotonicity is
  `generatesSub_union_of_dom_eq` (private, `SubpartitionHistory.lean`): `C ⊢ X`, `D ⊢ Z`,
  `X.dom = Z.dom` ⇒ `C ∪ D ⊢ X`. Landed in `Examples.lean` in round 4 (R4-F01).
* **Lemma 2 needs no `|X| = 2` / `|X| ≥ 3` split**: run the paper's two-block computation as
  the step of an induction adjoining one `h(Y|x)` at a time (`A ⊢ X`, `r ∈ X.dom` ⇒
  `A ∪ h(Y|[r]_X) ⊢ X`); the family `{h(Y|[r]_X)}` is finite because each member ⊆ `B`, so
  `X` may have infinitely many blocks and `S` stays arbitrary. Theorem 2's contraction needs
  no `y ∩ z = ∅` branch either (`Setoid.classes` blocks come with a witness).
* Prop 21 clause 1 (`Y ≤ X → C ⊢ Y → C ⊢ X`) **genuinely needs `hE : X.dom = Y.dom`**
  (`Y ≤ X` gives only `Y.dom ⊆ X.dom`), and so does `historySub_mono`. Prop 23 clause 3
  (`Subset`, block inclusion) is the tool when domains differ (weak union in Theorem 2) — not
  clause 1.
* `restrict_part_subset_inf`'s `hE`/`hs` are provably redundant (`X.part s = ∅` off the
  domain) and kept for readability with a local `set_option linter.unusedVariables false`.
* Finiteness in §4: all of §4.1 is finiteness-free; `[Finite F.B]` starts at Def 24's
  well-definedness (`historySub_isLeast_and_eq_history`) and is carried by everything
  downstream of it, including all three §4.3 endpoints.
* Duplication debt paid in round 4 (R4-F04/F05): the nine `chimera_*` projections of Prop 4
  are one public block in Basic.lean after `chimera_spec` (clauses 3,4,5,6,7a,7b,8,10,11);
  the `Subpartition.restrict_*` glue lives in Subpartition.lean; `classes_top` in Basic.lean.
* Tactic traps: `intro -` is a syntax error (use `intro _`; `rintro -` is fine) and the parse
  error is reported at the enclosing block; `fun ⟨-, -, h⟩ => …` likewise — use `_`;
  dot notation `h.before hb` fails because `F` is explicit (write `StrictlyBefore.before F h`);
  `Subpartition.ext` proves by `cases; cases; congr 1; funext; propext` (not `mk.injEq`);
  rewriting a chimera chain in place makes `chimera_sdiff` fire on the outer occurrence —
  extract the inner step as a `have`; `Set.union_empty_iff` (not `union_eq_empty`);
  `lake env lean` on an *importing* scratch file sees the stale olean of a just-edited
  upstream — `lake build` first (bit again in stage 6 wearing a new costume: `Model` and
  `OrthDatabase` reported as *unknown identifiers* with autoImplicit hints, purely because
  `API.lean`'s olean predated its new `Inference` import — it reads as a missing `open`).
* The node checker is whole-directory: during parallel shards it stays red until the last
  shard's inventory rows land; read the file names in its output, not the count.

## Stage 6 (§6) — durable lessons

* **Registers after stage 6: 81 carriers / 88 annotations — 81 of the 96 in-scope nodes.**
  Recount mechanically before editing any register:
  `grep -rho "Paper node: [A-Za-z]* [0-9]*" FiniteFactoredSets/*.lean | sort -u | wc -l`.
  The stage-6 fix packet itself carried an off-by-one (it said 82) because **Definition 39
  has no carrier** — `Model.pullback` is a named alias with no node line — so §6 adds 13
  carriers, not 14: Defs 38, 40–45 (7), Examples 1–2 (2), Props 33–36 (4). Definition 41 is
  the sixth multi-carrier node (`Orth`, `NotOrth`); Defs 29, 30, 39 are the three
  Mathlib-rendered nodes that still get a correspondence row.
* **`Consistent` is cheap on `O` alone, and this is the §6 fact most likely to be
  mis-audited.** A database asserting *every* triple orthogonal (`O = univ`, `N = ∅`) IS
  consistent, witnessed by a one-point model: on `unitFS` the basis is `∅`, so
  `historySub X ⊆ B = ∅` for every subpartition and `OrthogonalGiven` holds for all triples.
  All of Definition 43's content lives in `N`. Minimal mechanism:
  `nonconstDB_forces_nonconstant` — the single `N`-entry `(⊥, ⊥, ⊤)` gives, through
  Proposition 25 at `X = f⁻¹(⊥) = ker f`, `Y = f⁻¹(⊤) = ⊤`, exactly "`f` is not constant".
  Do not write a witness asserting `O = univ, N = ∅` is inconsistent.
* **Definition 45 (`X <_D Y`) is vacuously TOTAL on an inconsistent database**
  (`before_of_not_consistent`: it quantifies over models, and there are none); on a
  consistent one it is irreflexive (`not_before_self_of_consistent` — `StrictlyBefore` is
  `history X ⊂ history Y` and `Set`'s `⊂` is defeq to `<`, so `lt_irrefl` applies directly).
  Both witnessed in Examples.lean. This is why the paper proves consistency (Props 33, 35)
  before it infers time (Props 34, 36): a `<_D` claim read without a consistency proof beside
  it certifies nothing, and an auditor meeting a positive `Before` witness should check which
  side of that line it is on first.
* **Proposition 36's `r_ij` family is symmetric in `X` and `V`, and exploiting that halves the
  proof.** The paper says "symmetrically, …" twice and the naive reading is that the whole
  `r_ij = χ^F_{H_X}(s_i, t_j)` construction must be redone with `χ^F_{H_V}(t_j, s_i)`. It need
  not: package the family as five properties — first bit `i`, agreement `j`, all four
  `∼_b` for `b ∈ B \ {b_X, b_V}`, `b_X` sees only `i`, `b_V` only `j` — and the `H_V`-oriented
  construction satisfies exactly the same five. The only residual asymmetry is which of `b_X`,
  `b_V` lies in `C`: a two-branch case split giving `χ^F_C(r_ij, r_i'j') = r_ij'` or `= r_i'j`,
  both landing in the opposite `f⁻¹(Y)`-block at `(i',j') = (!i,!j)`, so the block argument is
  written once. The `y`-block bookkeeping runs on **one Bool identity — the second bit of
  `f (r i j)` is `(i == j)`** — from which four `by decide` lemmas suffice; deriving block
  membership from it rather than by ad-hoc case analysis is what keeps it short.
* **Proposition 35 needs only the ⊆ halves** of the paper's conditional histories
  (`h(X'|y_i) = h(V'|y_i) = {X',V'}`, `h(f⁻¹Z|y_i) = {Z'}`): all six verdicts consume those
  plus one nonemptiness (`historySub_spec` clause 4). That matters because the ⊇ halves are
  genuinely harder than in the unconditional case — `generatesSub_iff_historySub_subset`
  carries the extra `χ^F_C(E,E) = E` conjunct (§4 non-monotonicity), so there is no
  subpartition analogue of `le_iff_history_subset` to refute with. Budget separately if a
  future round wants the exact equalities as landmarks. Proposition 36 by contrast *does*
  prove an exact conditional history (`histSub_restrict_X_eq : h^F(f⁻¹X|y) = H_Y`), whose
  lower bound comes from the block dichotomy, not from generation.
* **Definition 39's pullbacks are definitional in the §6.2 examples.** `M.pullback A = A'`
  for comap-of-`⊥` partitions is `Setoid.ext fun _ _ => Iff.rfl`; `M.pullback ⊤ = ⊤` and
  `Model.pullback ⟨F, id⟩ X = X` are `rfl` (both `@[simp]` in `Inference.lean`), so inside a
  `Models` obligation for a model built as `⟨F, id⟩` a bare `show F.OrthogonalGiven X V ⊤`
  discharges the defeq check — no `Setoid.ext`-based transport lemma is needed, contrary to
  the natural expectation. Mathlib has **no `Setoid.comap_id` and no `Setoid.comap_top`**;
  do not go looking, the one-liners are shorter than the search. (For a constant map into a
  subsingleton carrier, `M.pullback X = ⊤` does need `cases` on both points first.)
* **`show <plain equation> from h` is the reliable way to unfold a `Setoid.comap g ⊥`
  relation.** For a factor `b := Setoid.comap g ⊥`, `hr : b p q` is definitionally
  `g p = g q`, but `simp [b]` cannot see it and `decide` is banned on `Setoid` relations
  (existing entry); the ascription converts it to a `noConfusion`-able goal in one step, and
  dually `have hr : b p q := rfl` proves the relation from the equation. Every
  factor-distinctness and nontriviality proof in Example 2's model runs on this. Refuting a
  `Setoid` equality is a one-liner with `Setoid.ext_iff`: `X ≠ V` is
  `fun h => Bool.noConfusion ((Setoid.ext_iff.1 h (true, true) (true, false)).1 rfl)`, and
  `V ≠ ⊤` the same with `.2 trivial`.
* **Four general §2.3/§3 helpers are parked in `Inference.lean`** under a block headed "§3
  working forms of Definition 17" — `FactoredSet.rel_of_forall_mem_history`,
  `exists_not_rel_of_mem_history`, `mem_history_of_not_rel`, `chimera_eq_right` — only
  because §6.2 was the first consumer and no stage-6 fixer owned `History.lean`/`Basic.lean`.
  Public and uninventoried. **Relocation candidates**: the first three to `History.lean`
  (after `le_iff_history_subset`), `chimera_eq_right` to `Basic.lean`'s `chimera_*`
  conveniences block. Same shape: `not_before_self_of_consistent` and
  `before_of_not_consistent` are general facts about any `Ω`, `D` but live in `Examples.lean`,
  which the API deliberately does not export — so the §6 APITests examples re-derive them.
  That is not a rule-2b duplicate (the client genuinely cannot reach them), but both belong
  on the consumer surface in `Inference.lean` beside `pullback_apply`. Proposal for the
  convergence round, not done in stage 6 (`Inference.lean` was declared final).
* **`mem_history_of_not_rel` needs NO `b ∈ F.B` hypothesis** — and Lean's `unusedVariables`
  linter is what found that. If `b ∉ B` the hypothesis `∀ c ∈ B, c ≠ b → c s t` degenerates
  to `∀ c ∈ B, c s t`, forcing `s = t` by Proposition 3 and contradicting `¬ X s t`. Do not
  add the binder back "for symmetry" with `exists_not_rel_of_mem_history`.
* Gate facts, both of which make a green run mean less than it looks:
  **`check_endpoint_coverage.py` scans `LogicalInduction/` only** (`LIB =
  Path("LogicalInduction")` is hard-coded; its output "68 labels have an inventory endpoint,
  0 uncovered" looks project-wide and is not — adding three FFS inventory rows left the count
  at 68, which is the tell). The FFS gate is `scripts/check-finite-factored-sets-nodes.py`.
  And **`lake build AxiomAudit` stays green with sorried declarations in the same file as
  long as they are not listed** — a green AxiomAudit is a claim about the *listed* names
  only; `grep -rn sorry FiniteFactoredSets/` separately before believing a directory is clean.
* **A single `instance : Finite carrierFS.B := basis_finite.to_subtype` right after the
  model's `def carrierFS` suffices** — it is found for goals about `carrierFS.B` *and*
  through `model.F.B` inside `Models model D`, so the model need not be an `abbrev` and no
  `haveI` sprinkling is needed (the opposite was budgeted for). In the model-generic half,
  by contrast, every lemma opens with `haveI : Finite M.F.B := M.F.finite_basis_of_finite`,
  since `Model` carries `[Finite S]` and Proposition 6 is what converts it.
* **Extracting a triple from a database set literal:** `h : D.Orth A B C` is definitionally
  the disjunction, so `have h' : (A,B,C) = (X,V,⊤) ∨ … := h` type-ascribes it with no
  `unfold` and no `Set.mem_insert_iff`; per branch,
  `simp only [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl, rfl⟩ := h'` handles both nesting levels
  at once (`rw [Prod.mk.injEq]` has to be repeated). Asserting membership in the other
  direction is just `Or.inl rfl` / `Or.inr (Or.inl rfl)`.
* **State restriction lemmas over an explicit block representative, not an abstract block.**
  `lemma … (v : Carrier) : F.GeneratesSub C ((ofSetoid A).restrict {x | Y' x v})` makes
  `hs : s ∈ {x | Y' x v}` definitionally `s.2.1 = v.2.1`, usable as
  `show s.2.1 = v.2.1 from hs`; at the call site `rintro z ⟨v, rfl⟩` on `z ∈ Y'.classes`
  produces exactly that shape (`Setoid.classes r = {s | ∃ y, s = {x | r x y}}`). Each chimera
  argument becomes three `have`s. The model-generic half uses `obtain ⟨v, rfl⟩ := hy`.
* Clause indices used constantly in §6.2, worth memorizing: `(F.history_spec A B).1` is Prop
  13(1) `B ≤ A → history A ⊆ history B`; `.2.1` is clause 2
  `history (A ⊓ B) = history A ∪ history B`; `.2.2.1` is clause 3 `history A = ∅ ↔ A = ⊤`;
  `.2.2.2` is clause 4, which takes `Nonempty S` *then* `∀ b ∈ F.B`. And
  `(F.orthogonal_spec A B C).2.2.2` is Prop 15(4) `Orthogonal A A ↔ A = ⊤`, keyed on the
  *first* argument.
* Naming: the Example-2 model is **`Example2.carrierFS` / `Example2.model`, not `F` / `M`** —
  Proposition 36's section binds `variable {M : Model Ω}` in the same namespace, and a section
  variable shadowing a namespace-level `def` is a readability hazard even where it elaborates.
  Matches `Examples.lean`'s `coordFS`/`boolFS`. Example 1's factored set is `{X, V}` (first
  bit, agreement), **not** `coordFS`'s `{fstFactor, sndFactor}`; `Example1.V` and
  `Examples.xorPart` are the same partition mathematically but different Lean terms (no lemma
  about one applies to the other without a `Setoid.ext`) — moot in practice, since
  `InferenceExamples.lean` imports only `FiniteFactoredSets.Inference`, which does not reach
  `Examples.lean`. Build the §6.2 witnesses locally.
* Inventory: **the bare name `Model` is ambiguous inside AxiomAudit's FFS-INVENTORY block** —
  under its `open FiniteFactoredSets in`, `ProvabilityLogic/Kripke/Basic.lean`'s root-namespace
  `structure Model` collides and the build fails with `ambiguous identifier 'Model'`. Write
  `FiniteFactoredSets.Model`; the node checker allows (but does not require) the root prefix.
* Tactic traps (stage 6): `have : b ∈ _ ∩ _ := ⟨hb, hb'⟩` fails ("the expected type … is not
  an inductive type") when the sets are metavariables — `Set.mem_inter hb hb'` elaborates
  instantly (this bit twice in one file); `rw [if_pos h]` cannot see through the beta-redex
  left by `refine ⟨fun i => if P s₀ = i then s₀ else s₁, …⟩` ("did not find an occurrence") —
  prefix each branch with an explicit `show`, which is also the standard shape for a
  `Bool`-indexed WLOG (`exists_boolIndexed`): discharge "without loss of generality, assume
  `f(s₀) ∈ x₀`" by re-indexing the separated pair by the statistic that separates it;
  `Option.noConfusion` fails in `exact` position where `Bool.noConfusion` succeeds (with
  `exact`'s expected type still a metavariable its universe/motive metavariables never get
  solved) — use `exact absurd (show (none : Option Bool) = some true from h) (by simp)`;
  `rw [pullback_coordModel, pullback_coordModel, pullback_coordModel]` fails when two of the
  three pullbacks are at the *same* partition (`rw` instantiates the explicit `X` from the
  first match, then rewrites all occurrences of that instance) — `simp only
  [pullback_coordModel]` is instance-count-independent; under `InferenceExamples.lean`'s
  file-level `open scoped Classical`, `revert`-then-`decide` also reverts a hypothesis whose
  `Decidable` instance goes through `Classical.propDecidable` and sticks on `Classical.choice`
  — `clear h` first (the error names `Classical.choice` and reads as "decide can't do this at
  all"; it can, you dragged a classical hypothesis into the goal).
* Merge and registers: the three stage-6 fixers merged with **only disjoint AxiomAudit-row
  conflicts** — stage 5b's rule (pre-assign the AxiomAudit preamble to one shard) plus
  per-shard row blocks was enough, and no statement file conflicted. Surfaces a stage's counts
  stale, all of which must be swept at merge: `FiniteFactoredSets/README.md`, `API.lean`'s
  status line, this file, and the **repo-root `CLAUDE.md`**, which carries its own FFS register
  (node count *and* file count) and appears in no shard packet. `docs/trust-surface.html` needs
  `python3 scripts/gen-trust-surface.py` (requires `latex2mathml`) and should be assigned an
  owner at merge, or every shard re-reports it stale.
* Calibration: both §6.2 shards came in well under budget — one to two compile iterations each
  (Proposition 36's ~460 lines took four trivial fixes: beta-redex `rw`, `@[refl]`
  double-close, two `Set.mem_inter`s, one `set`-vs-`show` mismatch). The cost was entirely in
  writing the proof plan — which lemma carries which paragraph, and spotting the `r_ij`
  symmetry — not in tactics. Same lesson as stage 5a: for §4–§6 the cost centre is *choosing
  which lemmas carry the paper's steps*. Everything in Example 1 lives on `Bool × Bool`, so
  `revert`-then-`decide` discharges the factorization's injectivity, the surjectivity witness,
  and both order facts (`Y ⊓ V ≤ X`, `Y ⊓ X ≤ V`) outright.

## Round 9 audit — durable lessons (§5.3–5.5 convergence round)

* Verdict: codex statement sweep `[]`; Lens A no drift; residue = the recorded APITests
  `dirac` duplication (now paid), one byte-identical in-module/APITests example pair (Lemma 3
  clause 2), and three register sentences. Cross-check discipline mechanically verified for all
  seven §5.3–5.5 pairs.
* **Infinite-dimensional factored set exists in compiled form** (`ScratchR9A_inf.lean` →
  land it in Examples when Conjecture 1 is stated): `W = ℕ → Bool`, `coordSetoid n =
  Setoid.comap (· n) ⊥`, `B = Set.range coordSetoid`, via `isFactorization_iff_existsUnique`.
  It pins: `isDistribution_diracAt`'s `[Finite F.B]` (false there); `[Finite S]` on Lemma 3
  (`S = ℕ × ℕ`, `X = Y = fst`, `Z = ⊤`: all `Q`s junk `0`, clause 3 holds, clause 1 fails by
  Prop 25) and on `eq_of_Q_eq` (`Q ℕ = 0 = Q ∅`). Refute-by-finprod-junk idiom:
  `rw [finprod_mem_def]; finprod_of_infinite_mulSupport`.
* **Untracked files in `FiniteFactoredSets/` redden three gates for everyone auditing the
  checkout** (node checker, wiring, trust surface glob every `.lean`) — do not hold a stage
  skeleton uncommitted in the paper directory during an audit round; keep it in scratch or
  commit it transiently. Also `ProbDist.diracAt` needs `open scoped Classical` in a client.
* Lemma 3 clause 3 and Theorem 3 present their sides in opposite orders — the paper's own.
  `mem_chimeraImage_self` is a consequence of clause 3, not the clause. A
  `ProbDist.ofWeights` constructor would collapse `uniform`/`biased`/`boolUniform`/`diracAt`'s
  near-identical `additive` proofs — a deliberate future de-slop, not a rule-2b defect now.
  No instance in FiniteFactoredSets is axiom-checked (established convention). Round-9 fix:
  the APITests §5.3 example is now *uniqueness of the divisibility cofactor*
  (`Q_ne_zero` + `mul_left_cancel₀`); the README's rendered-node table accounting is 8 whole
  + 3 partial = 11; API's `[Finite F.B]` bullet says seven at both ends (grep the whole
  bullet for the numeral when it changes).

## Round 8 audit — durable lessons (first audit of §5.3–5.5)

* Verdict shape: codex statement sweep `[]`; Lens A found no statement drift; the residue was
  private-scoping duplication (the recorded three, plus a fourth: `chimeraImage_univ_univ`
  private in Probability.lean vs public coordFS copy in Examples — a bare-name collision) and
  register drift (public §5 count 43 not 41 — `ProbDist.eq_sum_singleton{,_of_finite}` were
  public but on neither surface; README still said "proofs outstanding" after they landed;
  the finiteness register said every §5.3–5.5 statement has a `Q^F_E` — **Theorem 3's has
  none**: its `[Finite S]` is consumed in the proof, and relaxing it to `Finite F.B` is
  literally Conjecture 1). Rule for stage commits: grep the README for "outstanding/still to
  come/stated" before squashing.
* Executable pins: Theorem 3's trailing `* P z` is load-bearing (drifted reading false at
  `Z = ⊥` on `coordFS`/`uniform`, 1/16 vs 1/4; NOT refutable at `z = univ`); `ProbDist Empty`
  is uninhabited, so over empty `S` Theorem 3's RHS and LHS are both vacuous — consistent.
* Cleared: `IsDistribution`'s finprod junk unreachable; `isDistribution_iff`'s `[Finite S]`
  genuinely consumed (`S = ℕ`: `Q univ = 0` vs `P univ = 1`); CoeFun transparent; the paper's
  `x ∩ z = ∅` branch absorbed by nonempty classes; `Irreducible.prime` rests on the
  arbitrary-σ UFD instance; the set-quantified prime dichotomy is honest; `eq_of_Q_eq`
  non-circular; `generatesSub_sdiff_of_dvd` uses `hCirr` only for `C ⊆ B` (fine, matches paper);
  `Q_mul_Q_eq_of_orthogonalGiven`/`orthogonalGiven_of_Q_mul_Q_eq` are TFAE projections in the
  conveniences block (mirrors §3). `ProbDist.eq_sum_singleton` is not a Mathlib duplicate
  (Mathlib's additivity lemmas are for `Measure`).
* Mechanical public-count: `grep -cE '^(noncomputable )?(abbrev|def|lemma|theorem|structure|instance|class) |^instance :'` per file
  (after round 8: 47 public §5 decls = 27/9/4/7, split 21 `[Finite S]` / 6 `[Finite F.B]` /
  20 free — the register had drifted a THIRD time). Round-8 promotions: `mem_chimeraImage_self`
  (two-set form, load-bearing), `chimeraImage_univ_univ`, `chimeraImage_sdiff` in Basic.lean;
  `subset_chimeraImage_self`, `mem_iff_part_mem_vars` public in Factoring; `mono_basis_injective`
  public in Polynomial; `eq_of_Q_eq` public in CharacteristicOrthogonality; all in the
  conveniences block + API doc. **Conjecture 1 is not yet stated in Lean** — the scope ruling
  is a plan; doc text must not say it is stated until §7 lands. `ProbDist S` inhabited iff `S`
  nonempty; the point mass `diracAt s₀` is a distribution on every `[Finite F.B]` factored set
  (so Theorem 3's RHS is non-vacuous over every nonempty `S`); a product of biased coins is a
  distribution on `coordFS` (Def 37 ≠ uniform); `boolFS` makes Def 37 a tautology yet Theorem 3
  still discriminates there (`¬ OrthogonalGiven ⊥ ⊥ ⊤` via uniform on `Bool`); divisibility of
  characteristic polynomials is refuted by a separating *zero* of the divisor (`coordZero`),
  not by evaluation into nonzero reals; `Set.ncard_coe_Finset` does not exist; `decide +kernel`
  sticks on `MvPolynomial` equations. After fixer B: register = **50** public §5 decls
  (27/9/4/10; 21 `[Finite S]` / 7 `[Finite F.B]` / 22 free); `ProbDist.diracAt`,
  `diracAt_apply`, `isDistribution_diracAt [Finite F.B]` public in Probability.lean (the
  latter's `[Finite F.B]` is load-bearing — FALSE for infinite bases, like Prop 29's; do not
  relax); Lemma 3 clause 2's cross-check must state the `∣` with the cofactor as the
  `Dvd.dvd` witness (half (ii) again); three independent derivations of
  `OrthogonalGiven fst snd ⊤` are deliberate. (The APITests `dirac` duplication was retired in round 9;
  its examples now consume `ProbDist.diracAt`/`isDistribution_diracAt`.)

## Stage 5b (§5.3–5.5) — durable lessons

* All five nodes proved first pass, no stalls; the cost centre was again *choosing which
  lemmas carry the paper's steps*, not tactics. Theorem 3's converse: the paper's `P_f`
  (`E ↦ Q^F_E(f)/Q^F_S(f)`, positive `f`) built as a genuine `ProbDist` (private
  `normalized`); its `IsDistribution` needs one lemma the paper glosses — `poly C univ =
  ∏ᶠ b ∈ C, poly {b} univ` for `C ⊆ B` (private `poly_univ_finprod`, Prop 27 iterated at
  `C₀ = {b}`) — the only genuinely new mathematics beyond §5.1–5.3; the analytic step is
  `MvPolynomial.funext_set` at `Set.Ioi 0` (`eq_zero_of_eval_pos_eq_zero`, private in
  Probability.lean; needs `import Mathlib.Order.Interval.Set.Infinite` for `Set.Ioi_infinite`).
  The paper's `isEmpty_or_nonempty S` split is absorbed: `x ∈ X.classes` yields a point of `S`.
* Lemma 3: `MvPolynomial σ R` is a `UniqueFactorizationMonoid` for ARBITRARY `σ`
  (`Mathlib.RingTheory.Polynomial.UniqueFactorization`, not transitively imported) — no
  `Fintype (Set S)` detour; `Irreducible.prime` applies. `B \ h(X|z) ⊢ Y|z` is one
  application of the public `generatesSub_iff_historySub_subset`. The paper's `x ∩ z = ∅`
  branch has no counterpart (`classes_restrict` yields only nonempty traces). Private
  `eq_of_Q_eq : Q E = Q E' → E = E'` (via `monos_eq_of_support_eq` + injectivity) is the
  polynomial→set step; promotion candidate.
* **Duplication debt (round-8 de-slop):** three private §5.1–5.2 helpers were restated in
  CharacteristicOrthogonality.lean because `private` is module-scoped —
  `subset_chimeraImage_self` (as `mem_chimeraImage_self`), `mem_iff_part_mem_vars`,
  `mono_basis_injective` (inside `eq_of_Q_eq`). Promote the originals to public and delete
  the copies. `ProbDist.eq_sum_singleton{,_of_finite}` are public-but-uninventoried helpers
  (Prop 32's finite additivity) — add to API.lean + conveniences block together.
* Registers: 68 carriers / 74 annotations; §5 binder register 41 public decls =
  19 `[Finite S]` / 5 `[Finite F.B]` / 17 free (recount mechanically). Two shards edited the
  same AxiomAudit preamble line — pre-assign the preamble to one shard next stage.
* Witnesses (Examples.lean, four subsets + `xorPart`): Lemma 3 clause 3 holds at `z = S`
  and FAILS at `Ediag` (`coordSep` 310 vs 100); `uniform` (`P E = ncard E / 4`) is a
  distribution on `coordFS`; `diagDist` is a `ProbDist` but not one on `coordFS`
  (`P{(t,t)} = 1/2 ≠ 1/4`); Theorem 3 at `Ind_S` reads `1/2·1/2 = 1/4·1`, at `Ediag`
  **1/16 ≠ 1/8** — conditional independence genuinely fails given the diagonal; the Dirac
  point mass is used only for the zero-probability-block case (why Theorem 3 is division-free).
* Traps: `rw [set_eq]` also rewrites a variable `X set` on the RHS — use `conv_lhs`; set-membership
  `if_congr` rewrites fail on Decidable-instance mismatch (`cases … <;> norm_num`); `push_neg`
  is deprecated (`push Not at h`); `dsimp only` as first tactic in a structure-field proof
  errors "no progress"; `Set.union_diff_cancel` → `Set.union_sdiff_cancel`;
  `Set.disjoint_sdiff_right` exists; `Set.Finite.induction_on` takes `s` and `hs` explicit
  (`| @insert b C hbC hfin ih`); prefer `Finset.induction_on` when the carrier is a Finset;
  `mul_div_mul_right (hc : c ≠ 0)` (GroupWithZero) for the `P_f([s]_b)` cancellation;
  `Set.ncard_union_eq` autoparams discharge over a Fintype; `lake env lean` ignores
  `autoImplicit := false`; the node checker does not scan `APITests/`; UTF-8-dense lines
  break byte-length lint (`awk length`).

## Round 7 audit — durable lessons (§5.1–5.2 convergence round)

* Verdict shape: codex statement sweep `[]`; Lens A no drift; the residue was minimality and
  register hygiene. Two paper-node binders relaxed under `dd:finiteness-minimal` (Anson's
  standing ruling, as §3–§4 were): **Prop 26 `Q_eq_poly` and Prop 29 `irr_partition` /
  `irr_isPartition` take `[Finite F.B]`** — their proofs used `Finite S` only to obtain
  `Finite F.B`. For infinite `E`, Prop 26's both sides are the finsum junk value `0`, so the
  extra content is degenerate (recorded in the docstring; do not oversell).
  `degreeOf_poly_le` needs no finiteness; `coeff_add_mul_of_split` needs no `DecidableEq`.
* **Cross-check discipline has two halves**: (i) the witness must not name the endpoint, and
  (ii) it must state *the same proposition* as its applied twin. Round 7 caught a Prop 29
  "cross-check" that was `⋃₀ {B} = B` (a Set identity) beside an applied
  `⋃₀ irr Ediag = B`. When auditing a pair, diff the two statements first.
* Lean `.support` (Mathlib coefficient support, exponent vectors) is not the paper's `supp`
  (`vars`); `mem_support_poly`/`monos_eq_of_support_eq` use the former — translate. Compiled
  discriminator: `Ediag` and the antidiagonal have equal `(poly B ·).vars` but different
  `monos`. Mathlib `Irreducible` excludes `0`; the paper's wording would count `0`
  irreducible — the concrete reason the stronger rendering is safe. `mem_vars_poly`'s `hC` is
  used-but-removable (vars ignores multiplicity); kept for uniformity with `degreeOf_poly_le`.
* Minimality audit of the public §5 surface: `coeff_poly`, `mem_support_poly`,
  `monos_eq_of_support_eq`, `poly_ne_zero`, `mem_vars_poly` genuinely need `[Finite S]`
  (infinite `monos` ⇒ junk `0`); `mono_eq_iff`'s `[Finite F.B]` is minimal (infinite `C`
  ⇒ `mono C s = 1`). `Finite F.B` is `inferInstance` from `[Finite S]` — the three
  `haveI : Finite F.B := F.finite_basis_of_finite` lines were dead weight.
* Refuted (do not re-raise): `prod_X_eq_monomial` is not Mathlib's `prod_X_pow` (indexes
  through a possibly non-injective `f`, needed for `C ⊄ B`); Mathlib has no
  `IsUnit p → p.vars = ∅` beyond `isUnit_iff_eq_C_of_isReduced` + `vars_C`, and no
  coefficient-of-product-under-disjoint-vars lemma. `MvPolynomial.support_subset_vars_of_mem_support`
  exists and replaces the hand reconstruction.
* Docstrings must not carry commit hashes / spike history (consolidation rule); provenance
  lives here and in `notes/`.
* Round-7 fix outcomes: `Q_eq_poly`, `degreeOf_Q_le`, `irr_partition`, `irr_isPartition` at
  `[Finite F.B]`; `degreeOf_poly_le` finiteness-free (both finsum/finprod junk values respect
  the bound — generic private `degreeOf_finsum_mem_le` + `degreeOf_mono_le`);
  `coeff_add_mul_of_split` DecidableEq-free. **Binder inventory (33 public §5 decls): 14
  `[Finite S]` / 5 `[Finite F.B]` / 14 free** — recount mechanically before editing the
  register (it drifted twice). The §5.1 relaxations are degenerate over infinite `E` (junk `0`),
  Prop 29's is not — keep the two cases separated in prose. `monoExp_apply` takes
  `(hCfin : C.Finite)`. `open scoped Classical`'s *position* in Polynomial.lean matters (nothing
  above it has `DecidableEq (Set S)`); `X v ≠ 1` via `congrArg (eval fun _ => 0)`; the additive
  `finsum_*` junk lemmas are `to_additive` images — grep the multiplicative name;
  `support_subset_vars_of_mem_support`, `degreeOf_monomial_eq`, `Set.disjoint_singleton` exist;
  don't byte-length-lint these files (`wc -m`).

## Round 6 audit — durable lessons (first audit of §5.1–5.2)

* Verdict shape: codex statement sweep `[]`; Lens A no statement drift (executable pins:
  Def 35's `D.Nonempty` is load-bearing since `χ_∅(E,E) = E`; Prop 27's argument order
  discriminates at `E₀ = {(t,t)}, E₁ = {(f,f)}`; Mathlib `Irreducible` is strictly stronger
  than the paper's phrasing and both extras hold); the MAJORs were repo hygiene:
  `vars_eq_empty_of_isUnit` re-proves `MvPolynomial.isUnit_iff_eq_C_of_isReduced` + `vars_C`
  (rule 2b — grep the fact; the KB's own "workhorse" note had entrenched the hand route), the
  two exponent-vector layers (known), and two register overclaims — API.lean's "ten `[Finite S]`
  statements and no others" (seven more public ones), and README's "`#print axioms` is the
  mechanical check" for cross-check witnesses, which is **inert once the endpoints are proved**
  (all six print the same axioms). The cross-check discipline is a *textual* property: the
  witness's proof must not name the endpoint; `#print axioms` separates them only while the
  endpoint is sorried.
* `hE : E.Nonempty` is used-but-removable in `vars_disjoint_of_mul_eq_Q` and `poly_dvd_Q`
  (both true at `E = ∅`) but genuinely needed in Props 30/31 (`E = ∅, B = ∅`: `Q ∅ = 0 ≠ 1`;
  `E = ∅, B ≠ ∅`: `poly {b} ∅ = 0` is not irreducible). Prop 30 at `B = ∅` is consistent
  (`|S| = 1`). Prop 29's first conjunct is definitionally free (Def 35 clause 1) — faithful to
  Def 2, not padding.
* `set_option linter.unusedVariables false in` silences the WHOLE declaration; the
  `lake env lean` unused-binder audit gives a false all-clear there (Prop 29). Repo-root
  scratch copies are safe for the node checker (it scans `FiniteFactoredSets/` only).
* `mono`/`monos`/`poly` are stated for unrestricted `C` (third instance of the Prop 4 / Def 16
  pattern) — recorded under Intentional deviations.
* Lens C6 landmarks: `irr Efst = irr univ = irr ∅ = {{fst},{snd}}` — `Efst` does not
  discriminate (`χ_C(Efst,Efst) = Efst` for every `C`); `Ediag` is the only subset so far
  where `Irr` differs. At `E = Efst` Prop 30's two factors are *different* polynomials.
  `coordSep` evaluation landmarks: `poly ∅ S ↦ 1`, `poly {fst} S ↦ 5`, `poly {snd} S ↦ 12`,
  `poly B S ↦ 60` — with `subset_coordFS_basis_cases`, one `congrArg (eval coordSep)` refutes
  "p = some `poly C S`" in four `norm_num` lines (how `r ≠ 1` in Prop 28 is shown load-bearing).
  Junk values: `poly C ∅ = 0`; `poly ∅ E = 1` (nonempty E); `poly {⊤} univ = X univ`. Prop 30's
  `hE` needs the zero-dimensional `unitFS` to fail (`B = ∅`: empty finprod `= 1`, `Q ∅ = 0`).
  Prop 28 at a unit divisor forces `C = ∅` (`vars_C_mul`, `mem_vars_poly`). Traps: `if_pos rfl`
  fails on set-membership `if`s (use `if_pos (Set.mem_singleton _)`); a `Set.mem_insert_iff`
  singleton branch leaves `x ∈ {x}` for `rfl`. Names: `C_injective`, `vars_C_mul`,
  `not_irreducible_zero`, `Irreducible.isUnit_or_isUnit`, `isUnit_zero_iff`.
* Round-6 fixes: **the exponent-vector layer is single**, private `monoExp` in Polynomial.lean
  (`ev`/`vset` deleted); it won because it is unconditionally correct (`mono C s = monomial
  (monoExp C s) 1` needs only `C.Finite`; `C ⊆ B` enters at `monoExp_apply`) — *represent the
  exponent vector, not the variable set*. Public in `monos` vocabulary: `coeff_poly`,
  `mem_support_poly`, `monos_eq_of_support_eq`, `poly_ne_zero`, `mono_eq_iff` (now
  `[Finite F.B]`), `degreeOf_poly_le`, `mem_vars_poly`. `private` is module-scoped: a public
  lemma whose statement mentions a private def is unusable downstream. `Q_eq_poly` (Prop 26)
  no longer *needs* `[Finite S]` (only `Finite F.B`) — binder kept deliberately as a paper-node
  statement; a candidate for a minimality ruling. Redundant `haveI : Finite F.B` lines remain
  in Basic.lean (599, 706) and `irr_partition` — de-slop candidates. Witnesses now run at four
  subsets (`S`, `Efst`, `Ediag`, `∅`); `poly_singleton_fst_dvd_Q_coordFS_univ` replaced the
  trivially-satisfiable-shape witness; a witness that exhibits an existential conclusion at
  the existential's own witness form certifies nothing (pin the data or the object outside the
  family). `poly C ∅ = 0` vs `poly ∅ E = 1` — adjacent corners with opposite values.
* Public §5 helpers with no external consumer (candidates for API doc or de-slop):
  `poly_eq_sum_image`, `Q_eq_sum`, `poly_dvd_Q`; finiteness-free: `poly_empty`,
  `mono_eq_prod`, `mono_congr`, `mono_union`.

## Stage 5a (§5.1–5.2) — durable lessons

* **Proposition 28 (`factor2`) was not the crux it was budgeted as**: with the (A)–(G)
  decomposition written out first (disjoint supports via `coeff_add_mul_of_split`; all
  p-coefficients equal one `r`; each factor's variables lie entirely in one side; the
  witness set `C := {b ∈ B | part b s₀ ∈ p.vars}`; supports as images; `C_mul_monomial`) it
  compiled first try. The cost centre of §5 is *designing the monomial layer*, not proving.
* **Two parallel private exponent-vector layers now exist** (de-slop debt for round 6):
  Polynomial.lean's `ev`/`vset` (`mono_eq_monomial`, `mono_eq_iff`, `mono_basis_injective`)
  and Factoring.lean's `monoExp` (`monoExp_apply`, `coeff_poly`, `mem_support_poly`,
  `poly_ne_zero`, `mono_eq_iff` again, `degreeOf_poly_le`, `mem_vars_poly`). Both are
  correct; unify into one public block in Polynomial.lean (Factoring's `mono_eq_iff`,
  `degreeOf_poly_le`, `mem_vars_poly`, `poly_ne_zero` are the reusable statements) and delete
  the other. `poly_empty` was deduplicated at merge (now public, finiteness-free, in
  Polynomial.lean).
* Prop 27's proof deviates from the printed support-intersection argument (uses
  `mono_eq_iff` at `C₀ ∪ C₁`) — proof route only, disclosed in the docstring, no
  disclosure warranted. Prop 29's `E.Nonempty` is not needed (`Irr(∅) = {{b} | b ∈ B}`)
  and is kept for faithfulness with a disclosed linter silence — same route as
  `restrict_part_subset_inf`; and Definition 35's minimality clause is *vacuous at a
  singleton* (`∅ ⊂ {b}` but `∅` is not nonempty).
* Prop 26's subtlety is real and witnessed: `monos` is an image, so `poly {fst} S` has two
  summands over the four-point `S`; `Q_eq_poly` needs `mono F.B` injective (Prop 3 + Cor 1).
* Mathlib workhorses: `degreeOf_mul_eq` (NoZeroDivisors) gives `IsUnit p → p.vars = ∅`,
  `vars (p*q) = vars p ∪ vars q` (nonzero p, q), and the degree-2 contradiction;
  `Set.Finite.exists_minimal` needs `(s := {x | P x})` explicit; `Minimal.eq_of_subset`;
  `MvPolynomial.support_nonempty`; `prod_X_pow`; `finprod_mem_pair`, `finsum_mem_image`,
  `Fintype.sum_prod_type`, `Fintype.sum_bool`; `Set.ssubset_singleton_iff`;
  `degreeOf_X i j : if i = j` (first argument on the left).
* Traps: `Set.Finite` is a Prop, so `(Set.toFinite C).toFinset` = `hC.toFinset` by proof
  irrelevance — internal lemmas can take an explicit `hC : C.Finite`; `example`s do NOT warn
  on `sorry` use — grep textually; `Finset.sum_nbij` needs a type-ascribed bijection and a
  beta-reduced `heq`; `rw [Finset.sum_image h]` fails (implicit `s`/`g`) — shape the goal
  then `exact`; ℕ-`Finsupp` support membership via values + `omega`, not `support_add`;
  `Finsupp.filter_apply` leaves a `Decidable` instance mismatch — `simp [h]`; `open
  MvPolynomial` makes a local named `C` shadow `MvPolynomial.C` — the statement's `C r`
  is fully qualified; `obtain ⟨s, hs⟩ := hE` clears `hE` — use `id hE`; `congr 1` on
  `monomial d₁ 1 = monomial d₂ 1` descends to coefficients — prove `d₁ = d₂` separately;
  `set_option … in` precedes the docstring; scratch full-file copies inside
  `FiniteFactoredSets/` double every `Paper node:` for the checker — delete before commit.
* Witness technique: prove monomials distinct by ONE separating `MvPolynomial.eval` into ℝ
  (variables ↦ 2,3,5,7) — ten lines for `Function.Injective (mono coordFS.B)`. Cross-check
  pairs (`prop26_coordFS_crosscheck`, `Q_coordFS_univ_eq_mul_poly`,
  `poly_singleton_fst_dvd_Q_coordFS_univ` (was `dvd_Q_coordFS_univ_prop28_shape`)) vs applications (`prop26_coordFS_applied`,
  `prop30_coordFS_*_applied`): while the endpoints were sorried, `#print axioms` split them
  exactly — a mechanical certificate of independence. `subset_coordFS_basis_cases` enumerates
  the four subsets of `coordFS.B`.
* Landmarks on `coordFS`: `Q S = X(vfst t)X(vsnd t) + X(vfst t)X(vsnd f) + X(vfst f)X(vsnd t)
  + X(vfst f)X(vsnd f)`; `poly {fst} S = X(vfst t) + X(vfst f)`; `Irr(S) = {{fst},{snd}}`;
  `Irr(Ediag) = {B}` (restriction entangles, §5 shadow of §4).
* Node accounting convention (confirmed): counts are *carriers*, so §5.1–5.2 add 12 (Defs
  29–30 rendered): 63 carriers / 69 annotations after stage 5a.

## Round 5 audit — durable lessons (§4 convergence round)

* Verdict shape: no statement changed since round 4 (diff the extracts first — that is now
  the cheapest opening move of any re-audit); Lens A and the codex statement sweep found
  nothing; the one MAJOR was cross-family (codex + Lens B): `lemma2_rhs_coordFS` "computed"
  Lemma 2's right side by applying Lemma 2 — a witness that *applies* an endpoint and one
  that *cross-checks* it are different things, and the register said the latter. **Rule:
  a witness advertised as a cross-check must not mention the endpoint it checks.**
* **Mathlib's `Order/Partition/Basic.lean` (`Partition (s : α)`, with a `Rel` documented as
  "the partial equivalence relation induced by a partition") is NOT a substitute for
  `dd:subpartition`**: it is indexed by its support, so `SubPart(S)` would again be
  `Σ E, Partition E`, and §4 takes `⊓` of subpartitions with *different* domains
  (`botInfIndEfalse = ofSetoid ⊥ ⊓ indiscrete Efalse`), which `Partition s` cannot type.
  A future auditor will find it and suspect duplication; it is not.
* Executable pins added: Lemma 2's X/Y pairing is oriented (the half-swap
  `h(X) ∪ ⋃_{s ∈ Y.dom} h(X|[s]_Y)` is false at `fst`/`snd`: LHS `= B`, drifted RHS `= {fst}`;
  the full swap is true by commutativity, so only the half-swap discriminates); Prop 20
  clause 7a is oriented (`C = ∅`, `X = ofSetoid ⊥`: reversed 7a and true 7b both hold yet
  `GeneratesSub ∅ (ofSetoid ⊥)` fails).
* Cleared: Prop 21(4) at `dom = ∅`; `classes`/`classes_restrict` exclude empty blocks
  because paper Definition 2 requires nonempty blocks; `Subset` is strictly stronger than
  `≤` (do not substitute); `Setoid.classes_top` absent from Mathlib; Theorem 2 has no
  disjointness hypothesis by the paper's own closing remark; the last
  ConditionalOrthogonality example (`OrthogonalGivenSet X Y univ → Orthogonal X Y`) is not
  derivable from Prop 24 over empty `S` (strictly stronger there).
* Cheap audits worth repeating: `lake env lean <file>` (~5 s/file) with the
  `unusedVariables` linter is a real unused-binder audit (it fires on theorem binders);
  paste every backticked name from API.lean into a `#print axioms` scratch to check the doc
  names nothing nonexistent and everything is clean (80 names at 0f1022c).
* **You cannot walk a theorem's proof-term dependency graph in this toolchain**:
  `ConstantInfo.value?` is `none` for theorems (async elaboration), so a hand-rolled
  `getUsedConstants` walk sees only the *type*'s constants and answers "independent of X"
  for every X — a checker that passes for the wrong reason. Use declaration order within a
  module (Lemma 1 at SubpartitionHistory.lean:307 precedes Lemma 2 at :388, so the RHS
  witness path cannot reach Lemma 2) or `#print axioms`, never a naive walk.
* `lemma2_lhs_coordFS`/`lemma2_rhs_coordFS` are a cross-check pair: neither may mention
  `historySub_inf_eq` (left: Prop 22 + `history_bot`; right: Lemma 1 + Prop 22 + set algebra).
  `commonRefinement_history_le` is an internal §3.3 helper, deliberately off the consumer
  surface (not in API.lean/APITests/conveniences block). The two round trips are
  `ofSetoidOn_toSetoid` and `toSetoid_ofSetoidOn`; `ofSetoidOn_univ` is a third, unrelated
  compatibility fact. `unusedSimpArgs` warnings survive a "green" build — grep the log for
  your filenames.
* `APITests.clientPairFS` is definitionally `Examples.coordFS`; any *fact* proved about it
  should be checked against Examples' lemmas first (the reconstruction is ratified, verbatim
  re-derivations of facts are not).

## Round 4 audit — durable lessons (first audit of §4)

* Verdict shape: both codex sweeps clean (`[]`, valid); no mathematical finding from any
  channel; three Opus lenses independently raised the same MAJOR (no §4 witnesses landed
  with the stage) plus two structural debts (three private `chimera_*` copies; restriction
  lemmas parked in the §4.3 file). **Rule for future stages: witnesses land in the stage
  commit, not the round after** — Lens C's compiled file should be folded in before the
  squash.
* §4 order glyphs executably pinned on `coordFS`: Prop 21(1) reversed fails at
  `C = {fst}, X = ofSetoid ⊥, Y = ofSetoid fst`; Prop 23(1) reversed at `X = ofSetoid ⊥,
  Y = ofSetoid ⊤`; Prop 25 reversed (`↔ X ≤ Y`) at `X = ⊥, Y = ⊤`; Theorem 2's weak union
  with `⊔` at `X = Y = Z = ⊥, W = ⊤`.
* `hE : X.dom = Y.dom` is load-bearing in Prop 23 clause 2 (not just clause 1): `X = ofSetoid ⊥`,
  `Y = indiscrete {(f,f),(f,t)}` gives `historySub (X ⊓ Y) = {sndFactor}` while
  `historySub X ∪ historySub Y = B`.
* Landmarks: `sndFactor` restricted to the `fst = true` block is the discrete subpartition
  of that block with `historySub = {sndFactor}`; `historySub (indiscrete Ediag) = ∅`;
  restricting either coordinate factor to the diagonal `Ediag = {(f,f),(t,t)}` gives
  `historySub = B`, so `Orthogonal fst snd` but `¬ OrthogonalGivenSet fst snd Ediag` and
  `¬ OrthogonalGiven fst snd xorPart` (`Ediag ∈ xorPart.classes`) — conditioning entangles.
  Degenerate corners (faithful, but client traps): `OrthogonalGivenSet X Y ∅` and
  `OrthogonalGiven X Y ⊥` hold for all `X, Y`, so `OrthogonalGiven` does not refine
  `Orthogonal` (`OrthogonalGiven fst fst ⊥` holds while `¬ Orthogonal fst fst`).
* Computing `historySub` *upward* cannot go through `generatesSub_iff_historySub_subset`
  contrapositively (non-monotonicity); prove `∀ C, GeneratesSub C X → b ∈ C` from
  `generatesSub_iff_rel` and use `Set.mem_sInter`.
* Lemmas 1–2 take `X`, `Y` implicit (determined only via `hE`): clients pass `(X := …) (Y := …)`.
* Lemma 2's union and Lemma 1's block are indexed by *points* (`s ∈ dom`), which is why
  Theorem 2's contraction needs no `y ∩ z = ∅` branch.
* Cleared: the `Min` + `SemilatticeInf` pair on `Subpartition` is not a harmful diamond
  (`#synth Min` → `instMin`; `dom_inf`/`inf_apply` fire); `hC` in
  `generatesSub_iff_historySub_subset` is used forward only (not unused);
  `restrict_part_subset_inf`'s redundant binders are a disclosed readability choice;
  errata E1–E3 re-verified; Lemma 1's hypothesis set is satisfiable (`X = ofSetoid fst`,
  `Y = ofSetoid snd`) and Lemma 2 cross-checks on both sides.
* Prop 21 clauses 3–6 and Prop 23 clauses 3–5 are unconditional in the paper but bundled
  under `hE`; recover the unconditional clause with `Y := X`, `hE := rfl`.
* `xorPart p q` unfolds by delta to `(p.1 != p.2) = (q.1 != q.2)`; to show `Ediag ∈
  xorPart.classes` supply witness `(false,false)` and close with `show … ; simp`.
* Round-4 fixes: the nine `chimera_*` projections are public in Basic.lean (and listed in
  the AxiomAudit conveniences block + API doc — ratified: promoting private lemmas creates
  public endpoints, which the hygiene rule says AxiomAudit tracks in the same change);
  `Subpartition.restrict_*` glue and `restrict_inter_subset_restrict_inf` live in
  Subpartition.lean, `classes_top` in Basic.lean §2.1. §4 witnesses in Examples.lean:
  `sndOnEfst`, `indDiag`, `fstOnEdiag`, `sndOnEdiag`, `botInfIndEfalse` over
  `Efst`/`Ediag`/`Efalse` — reuse before building new ones. APITests deliberately rebuilds a
  two-dimensional client factored set (`clientPairFS`) rather than importing Examples (the
  API boundary excludes Examples; §4.3 needs dimension ≥ 2) — not a rule-2b duplication.
* Traps: `hle h` with `hle : X ≤ Y` on `Setoid` in argument position without an expected
  type mis-assigns the strict-implicits — ascribe `(hle h : X a b)`; term-mode projection
  `h.2 s hs t ht` in argument position needs parentheses; `ofSetoid X ⊓ indiscrete E` needs
  no `noncomputable`; `check_trust_surface.py` is staled by any Examples/AxiomAudit/README
  change — regenerate at merge (not in the four-script fixer gate); a piped `lake build`'s
  reported exit code is `tail`'s even in the harness's own task notification.

## Round 3 audit — durable lessons (convergence round)

* Verdict shape: Lens A found nothing (ten reversed-reading refutations compiled); codex
  statement sweep `[]`; every finding was documentation/consumer-surface drift, most of it
  stale relative to round 2's own fixes plus one false docstring in the smoke tests (a
  "common coarsening ... contained in either history" gloss on `history X ⊆ history (X ⊓ Y)`
  — the order-flip trap surfacing in prose, not in a statement). Hardening cap reached.
* Reversed-reading pins extended (Lens A): Prop 11(1) `C={fst}, Y=fst, X=⊥`; Prop 16
  swapped `X=fst, Y=⊥, C={fst}`; Prop 17 swapped `X=snd, Y=⊥, Z=fst`; Prop 19 as
  `{b | Before X b}` at `X=⊥`. **Prop 14's reversed reading is TRUE at `(fst, snd)`** — the
  discriminator is `X = Y = ⊤`. Prop 13(2)'s `⊔` reading refutes via clause 1 with
  `le_sup_left/right`, no need to compute `fst ⊔ snd`. The `⊓`-vs-`⊔` clauses Prop 11(2),
  15(3), 18(4) are NOT refutable by counterexample (the `⊔` reading is weaker-true); their
  orientation is pinned only by being the strictly stronger, paper-matching claim.
* Prop 5's identification clauses recover the paper's literal `B = {⊥}` / `B = ∅` in three
  lines from the theorem (`obtain ⟨⟨B₀, _, huniq⟩, h1, h2⟩ := existsUnique_trivialFactorization S`,
  then `(huniq B hB).trans (huniq _ (h1 h)).symm`). Not drift.
* Claims with no dedicated carrier, disclosed at the site (cleared; do not re-raise): Prop 2
  sentence 1 (`PartialOrder (Setoid S)`), Definition 14 sentence 2 (`IsTrivialFactorization
  F.B`), Definition 15 sentence 3 (`[Finite S]` / `Finite F.B`). Corollary 1 is carried
  contrapositively (`part b₀ s = part b₁ t → b₀ = b₁`) — equivalent since `classes` is the
  image of `part`, and the form §5 needs. Prop 10 clauses 1↔2 and 5↔6 are `Iff.rfl`, as the
  paper's own "by definition".
* `existsUnique_trivialFactorization (S : Type u)` takes `S` explicitly. `fstFactor p q`
  unfolds by delta to `p.1 = q.1` (close by type ascription; `congrArg Prod.fst` is for `⊥`
  on the product). `open scoped Classical` at namespace level (Examples.lean) covers the whole
  file, unlike Basic.lean's block-scoped one.
* API.lean is a pure re-export (module doc + one import): its whole risk surface is prose
  accuracy — treat every sentence there as an assertion to check. The in-module `example`s
  and the APITests examples must not be copies of each other; the API tests exist to prove
  *different* downstream facts through the curated import.
* `cardFactors_listProd` is derivable from `Nat.primeFactorsList_unique` + `List.Perm.length_eq`;
  not a duplicate of a named fact, but the shorter route exists if §5 touches it.
* Unused public lemmas (candidates for the de-slop pass, not defects): `isTrivialPartition_top`,
  `not_isTrivialPartition_of_isEmpty`, `mem_chimeraImage`, `chimeraFun_rel`, `part_eq_iff`.
* `IsFactorization`'s two fields are independent, now witnessed in Examples (R3-F07):
  `not_isFactorization_singleton_fstFactor` (nontrivial, not bijective) and
  `not_isFactorization_unit_singleton_top` (bijective, not nontrivial — the fact that keeps
  Proposition 5's uniqueness true).
* **`[Finite F.B]` starts at Proposition 12**, not at §3: Props 10–11 carry no finiteness;
  `history_isLeast` is the first endpoint that needs it. `[Finite S]` is never global — only
  `finite_basis_of_finite` (Prop 6) carries it, where the paper's statement has it.
* `#assert_axioms_clean` emits nothing on success; a green `lake build AxiomAudit` is the only
  signal (and it reports only the first tainted declaration on failure).
* From inside `namespace FiniteFactoredSets.Examples`, bare `rw [size_eq_mk]` does not resolve
  (the lemma lives in `FactoredSet`); write `rw [coordFS.size_eq_mk]`. The workaround lemmas
  `size_coordFS_eq_mk`/`dim_coordFS_eq_mk` were deleted in round 3 — do not reintroduce.
* `((F.generates_tfae hC X).out 2 6).1 h` works in term position; the typed-`have` rule
  applies when the *result* is a strict-implicit `∀ ⦃x y⦄` clause you then apply.

## Round 1 audit — durable lessons

* **`part b s` is definitionally Mathlib's equivalence class `{x | b x s}`**, so
  `Setoid.mem_classes` and `Setoid.eq_of_mem_classes` apply with no glue. Before adding any
  lemma about `part`, read `Mathlib/Data/Setoid/Partition.lean` first: `mem_classes`,
  `eq_of_mem_classes`, `rel_iff_exists_classes`, `classes_inj`, `empty_notMem_classes` are
  already there under different names. Round 1 found `part_eq_of_mem` re-deriving one of
  them (R1-F09); it now cites Mathlib.
* **`hB` in `isFactorization_iff_existsUnique` is load-bearing, not decoration**, even
  though the forward direction never uses it. Drop it and the iff is *false*: take
  `S = Unit`, `B = {⊤}` — the right-hand side holds, but `IsFactorization {⊤}` fails its
  `nontrivial` field. Do not "simplify" it away.
* **`Setoid α` is extensional** — `Equivalence r` is `Prop`-valued, so proof irrelevance
  applies to `iseqv` and distinct `Setoid` terms cannot share a relation. This is what makes
  `dd:partition` faithful to "a partition *is* its set of blocks". Consequence:
  `(⊥ : Setoid Empty) = ⊤`, matching Definition 7's `Dis_∅ = Ind_∅ = {}`.
* **Proving the `bijective` field's surjectivity**: `exact Eq.trans (Quotient.sound h)
  (Quotient.out_eq _)` fails with an application-type mismatch (the `out_eq` metavariable is
  solved too early). Use `refine Eq.trans (Quotient.sound (?_ : b _ _)) (Quotient.out_eq _)`
  and close the side goal with `rfl`; postponement is what makes it elaborate.
* **`b ∈ ({x} : Set (Setoid S))` does not `rintro rfl`.** Use
  `simp only [Set.mem_singleton_iff] at hb; subst hb`. For a pair `{x, y}`,
  `rcases hb with rfl | rfl` *does* work, since `Set.insert` membership unfolds to a
  disjunction of equations definitionally.  Stage-6 refinement: this is specific to
  *singletons* — `rintro b (rfl | rfl | rfl)` works on membership in a `def`-wrapped
  `insert`-shaped literal too (`def basis : Set (Setoid S) := {X', V', Z'}`), since rcases
  whnfs through both the `def` and `Set.insert`.
* **`open ... in` scopes to the next command only.** `AxiomAudit.lean`'s FFS-INVENTORY block
  works because there is exactly one `#assert_axioms_clean` inside the markers. Adding a
  second would silently lose the `open` and fail to resolve unqualified names.
* **The trust-surface generator renders plain `def` cards as signature only**, while
  `structure` cards show their fields. Seven of thirteen FFS nodes are Definitions, so a
  human read-through of the guide alone cannot check an FFS *definition* against the paper —
  including `IsTrivialPartition`, the one this file flags as the trap. Open the source. This
  is repo-wide generator behaviour, not FFS-specific, but it bites hardest here.
* **A concurrent session can switch the shared checkout out from under you**, with a clean
  `git status` and no warning. `Scratch*.lean` is in `.git/info/exclude`, so scratch probes
  survive the switch and look like they still belong to the branch you started on. Check
  `git branch --show-current` before trusting a build result, and read shard files with
  `git show <branch>:<path>`. This work now lives in its own worktree for that reason.
* **When the first erratum lands**, create `notes/paper-errata.md` *and* point
  `scripts/papers.py`'s `errata` field at it — the registry currently says `None`, and
  `check_paper_wiring.py` does not look at this file's errata section.
