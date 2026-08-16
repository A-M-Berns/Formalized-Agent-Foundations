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

## Open trust-surface caveats

**None outstanding.** Non-vacuity was the one open caveat and it is now discharged by
construction in `Examples.lean` (round 1, R1-F01). This section exists so that a future
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
* **How `B`'s finiteness is carried** into §5. Proposition 6 proves that a finite factored
  set is finite-dimensional, so `Fintype F.B` should be *derived*, not assumed. Assuming
  it would be premise smuggling; prove Proposition 6 before the polynomial section needs
  finite products.

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
