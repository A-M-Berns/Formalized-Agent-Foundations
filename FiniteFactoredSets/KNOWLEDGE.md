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
  goals by itself; a following `exact X.refl' s` fails with "no goals".
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
| Definition 13 (`χ^F_C`) | `FactoredSet.chimera` | `Basic.lean` |
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

**None outstanding.** Non-vacuity was the one open caveat and it is discharged by
construction in `Examples.lean` — §2 witnesses in round 1 (R1-F01), §3 witnesses on
`coordFS` (history, orthogonality, time, the XOR partition) in round 2 (R2-F03). This section exists so that a future
session reading only this file learns of any caveat the README carries — round 1 found the
two registers out of step, which is exactly the failure this heading prevents.

## Disclosures

None. There are no type-`(c)` modeling substitutions in the current surface.

## Paper errata

None found yet. The source's labels are working names (`templabel1`, `templabel2`,
`templabel4`), which is not the label hygiene of a paper whose proofs have all been
checked — budget for errata as §3–§5 land.

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
  (`instFiniteSetoid` + `Subtype.finite`); `Fintype F.B` does NOT (`Setoid` has no
  `DecidableEq`) — pass `Fintype.ofFinite _` explicitly to `natCard_eq_prod`.
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
  disjunction of equations definitionally.
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
