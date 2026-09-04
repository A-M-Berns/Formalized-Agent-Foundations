# Safe Pareto Improvements for Delegated Game Playing — scoping note

**Status:** draft for discussion (2026-09-04). Nothing here is settled; every item marked
*RULING* needs Anson's call before M0 lands. No Lean has been written.

**Paper.** Caspar Oesterheld and Vincent Conitzer, *Safe Pareto Improvements for
Delegated Game Playing*, JAAMAS 36 (2022), doi 10.1007/s10458-022-09574-6; short
version AAMAS 2021. The committed copy `notes/oesterheld-conitzer-2022-spi.pdf` is the
authors' "equal to the JAAMAS version except for formatting" preprint (57 pp.). There is
**no arXiv ID and no TeX source** — arXiv 2403.05103 is the later *expected-utility
maximizers in program games* paper, not this one — so, as for Condensation, the
committed source the node checker reads is the `pdftotext -layout` extraction
`notes/oesterheld-conitzer-2022-spi.txt` (`source_format: text-extraction`).

**Requested scope.** "Everything before §8." The paper has seven sections (§7 is the
conclusion) plus appendices A–E carrying the proofs of Theorems 1, 9, 15 and Lemma 4.
*RULING 0:* I read the request as **the whole main text, §2–§6, with the appendix
proofs of every main-text theorem**, and treat the appendix-only nodes (Lemmas 19–22,
Propositions 23–26, Definition 8, Lemma 28) as in scope exactly insofar as Theorem 9 is.
Say if you meant something narrower.

---

## 1. Node inventory

Numbering: Definitions and Assumptions each carry their own global counter; Theorem /
Lemma / Proposition / Corollary **share one global counter** (Theorem 1, Lemma 2,
Theorem 3, Lemma 4, Proposition 5, …, Lemma 28). Examples are headed
`Proposition (Example) n`. This is a `printed-independent`-style scheme read off header
lines of the text extraction; the checker will assert the exact node set (38 headers).

| § | Node | Content | Proposed status |
|---|---|---|---|
| 2 | (unnumbered) | game, subset game, strict dominance, (strict) Pareto improvement, Pareto-optimal relative to `S`, game isomorphism | carriers with `§2` provenance, no node label |
| 3 | Def 1 | SPI, strict SPI | in |
| 3.1 | Def 2 | unilateral subset game / unilateral SPI | in |
| 3.2 | Thm 1 | every SPI is played in some program equilibrium (proof App. A: Thm 17 = Tennenholtz, cited; Prop 18) | in, **own tranche** (§4 below) |
| 4.1 | (unnumbered) | multivalued functions, `id`, `all`, inverse, composition, single-valued | Mathlib `SetRel` |
| 4.2 | Def 3 | outcome correspondence `Γ ∼_Φ Γ'` | in |
| 4.2 | Lemma 2 (1–7) | reflexivity, symmetry, transitivity, weakening, `all`, elimination (two forms) | in |
| 4.2 | (unnumbered) | equivalence relation `R` (∃ single-valued bijection), preorder `⪰` (∃ Pareto-improving Φ) | carriers; `⪰` is a correspondence-level tool, not the §6 selection problem (see §6) |
| 4.3 | Def 4 | Pareto-improving outcome correspondence | in |
| 4.3 | **Thm 3** | SPI ⟺ ∃ Pareto-improving outcome correspondence | in (the keystone) |
| 4.4 | Assumption 1, 2 | elimination; isomorphism | in, as predicates on the representative model |
| 4.4.2 | Lemma 4 | Pareto-improvingness transfers across isomorphisms (App. C) | in |
| 4.4.3 | (unnumbered) | **consistency of A1 + A2** ("book" representatives) | in as the **N± non-vacuity witness** — see §3.6 |
| 4.5 | Prop 5–8 | PD, Demand Game, Temptation, Complicated Temptation | in (concrete games double as witnesses) |
| 4.6 | Def 5 | (strict) (unilateral) SPI decision problem | in, as a derivation system — §3.7 |
| 4.6 | Thm 9 | NP-complete (App. D: Lemmas 19–22, Def 8, Lemma 27 cited, Lemma 28, Props 23–26) | **tranched**: mathematics in, complexity-class wrapper *RULING 6* |
| 4.6 | Prop 10 | `O(m^l)` when reducible to size `l` | mathematics in (finite search bound), runtime claim *RULING 6* |
| 5.1 | (unnumbered) | `C(Γ)`, perfect-coordination token game `(Aˢ, uˢ, uᵉ)` | carriers |
| 5.1 | Def 6 | perfect-coordination (strict) SPI | in |
| 5.2 | Def 7 | strict full-coordination SPI decision problem | in |
| 5.2 | Lemma 11 | Pareto-optimality in `C(Γ)` decidable by LP | mathematics in (LP characterization), "polynomial time" *RULING 6* |
| 5.2 | Prop 12 | Algorithm 1 decides Def 7 | correctness iff in; runtime *RULING 6* |
| 5.3 | Lemma 13 | WLOG isomorphic-copy token games, conditional-expectation equality | in, on `supp Π(Γ)` (§3.4; D6, D7) |
| 5.3 | Cor 14 | safely-achievable expected payoffs form a convex polytope | in |
| 5.3 | Thm 15 | two-player geometric characterization (L1, L2, L3; App. E) | in, **own tranche** (2-D convex geometry) |
| 5.3 | Prop 16 | a Pareto improvement with no perfect-coordination SPI (Table 7) | in; needs a constructed Π with prescribed play probabilities (§3.6) |
| 6 | — | SPI selection problem: prose only, no nodes | no node; what this paper can and cannot offer the selection problem is stated in §6 — RULING 9 |
| App. B | — | Sen/Raub discussion, no nodes | out |
| App. A | Thm 17 | Tennenholtz 2004 | cited external; **not** re-proved (we prove Prop 18 directly, which does not use Thm 17) |
| App. D | Lemma 27 | subgraph isomorphism NP-complete (Cook 1971) | cited external; the only way to carry it is as a named axiom in complexity tranche |

Out of the 38 headers, 36 are candidates for carriers; Thm 17 and Lemma 27 are citations.

---

## 2. Substrate: EconCSLib

`gametheoryinlean/EconCSLib` (Apache-2.0, main @ `cef01c7`, 2026-08-04, tag `v0.1.0`)
is the requested source for the basic game theory. What it gives us, and what it does
not:

**Usable now (`EconCSLib.GameTheory.StrategicGame.*`, ~1.2k lines):**
`StrategicGame N U` (`strategy : N → Type*`, `payoff : Profile → N → U`), `deviate`,
`IsBestResponse`, `WeaklyDominates` / `StrictlyDominates` / `IsStrictlyDominant`,
`IsNashEquilibrium`, mixed strategies over `stdSimplex U`, `expectedPayoff`,
`IsMixedNashEq`, `Survives` (simultaneous-round IESDS) / `IsRationalizable` /
`IsDominanceSolvable`, Nash existence via Brouwer, a two-player matrix-game layer with
`maximin` / `minimax` and the minimax theorem (over `ℝ`, via Loomis), LP strong duality,
Farkas.

**Missing, we build:** subset games as *sets* (EconCSLib's strategy spaces are types);
game isomorphism; single-step (path-dependent) elimination and its path independence
(EconCSLib only has simultaneous rounds; Assumption 1 is one action at a time, and
Lemma 19 is exactly the bridge); n-player threat point over independent mixtures
(`min_{σ₋ᵢ ∈ ×ⱼ Δ(Aⱼ)} max_{σᵢ}`, needed by Theorem 1 — EconCSLib's minimax is
two-player matrix only, which covers `n = 2` and the LP remark); correlated feasible set
`C(Γ)` (Mathlib `convexHull`); everything about representatives.

**Toolchain.** EconCSLib pins Lean/Mathlib v4.30.0; this repo is on v4.31.0. Probe done
today: the seven strategic-game modules we would import compile unmodified against our
Mathlib (one unused-simp-arg linter warning in `IESDS.lean`, nothing else). So a real lake
dependency is viable — Lake will warn about the conflicting Mathlib rev and take ours,
and only imported modules get built.

*RULING 1 — dependency vs. vendor.* Options:

- **(a) `require` EconCSLib at a pinned commit** (recommended). Honest provenance, upstream
  gets our fixes, the FAF consumer API can re-export EconCSLib names. Risk: it is a
  four-month-old library with visible API churn (`Nash.lean` still carries a parallel
  `mixedNashEquilibrium` next to `IsMixedNashEq`); a pin insulates us, and a bump is a
  deliberate act. Wiring gate: a lake dependency is not a `lean_lib`, so
  `check_paper_wiring.py` needs no exemption.
- (b) Vendor the strategic-game slice at upstream module paths with a `PROVENANCE.md`,
  the PFR pattern. Only worth it if (a)'s Mathlib-version coupling bites at the next
  toolchain bump.

Either way the paper library never names an EconCSLib internal directly on its trust
surface: the paper's set-based `Game` maps to `StrategicGame` through one bridge
(`Game.toStrategic`), and the paper-facing definitions of strict dominance, Nash, etc.
are *stated through the bridge* and characterized by set-level lemmas that read exactly as
the paper's §2 sentences. That is what makes EconCSLib the source rather than an
ornament.

---

## 3. Design decisions (proposed `dd:` glossary)

The paper is explicit (footnote 6, §4.4.3) that it never fixes what the objects of the
action sets are or how Assumptions 1–2 quantify over games, and that the formal
consistency of A1 + A2 is left informal. Those gaps are ours to close, and the closure is
most of the representation work.

### 3.1 `dd:universe` — a fixed action universe per player

```
variable {N : Type} [Fintype N] [DecidableEq N] (𝒜 : N → Type u)

structure Game (N) (𝒜 : N → Type u) where
  S : ∀ i, Finset (𝒜 i)          -- A_i
  nonempty : ∀ i, (S i).Nonempty
  u : (∀ i, 𝒜 i) → N → ℝ          -- meaningful on `profiles := {a | ∀ i, a i ∈ S i}`
```

Every game a given set of representatives can be asked to play lives over the same
per-player universe `𝒜`. Consequences: a subset game is literally `Sˢ i ⊆ S i`;
Assumption 1's `A_i − {ã_i}` is `Finset.erase`; outcomes of *all* games share one type,
so multivalued functions, composition and inverse never cross types; Assumption 1's
"A₁, …, Aₙ pairwise disjoint" is automatic (different players' actions are different
types — which is what the clause is for). The representative model `Π` is total on
`Game N 𝒜`, so every counterfactual instruction (unilateral changes, tokenized copies,
"as if the counterpart had not participated") is in its domain. Finite, nonempty
strategy sets are the paper's standing assumption (payoff matrices; Π(Γ) ∈ A needs
`A ≠ ∅`).

Under this reading Assumptions 1–2 constrain `Π` on fewer games, so *more* models
satisfy them, so a theorem quantified over all such models is *stronger*; the
consistency theorem must build a model over an arbitrary universe. The restriction is a
disclosed narrowing of the paper's (unspecified) quantification domain, not a claim that
nothing is lost: a reader who wants Assumption 2 across games over different universes
must transport them into one first. Note also that `Game` is the paper's *subset-game
instruction* only; programs and other instructions (§3.2, App. A) are a different kind
of object and are **not** games — see §3.8 and §6. §5's token games need *room*: "`Aˢᵢ ∩ Aᵢ = ∅`" is a
hypothesis that `𝒜 i` has enough elements outside `S i`, discharged in examples by
taking `𝒜 i := ℕ` or a sum type. The paper assumes fresh tokens exist silently; we say
so.

### 3.2 `dd:total-utility` — `u` total on universe profiles, equality "on profiles"

The paper's own conventions force this: Definition 2 writes `uˢᵢ = uᵢ` for functions on
different domains (`Aˢ ⊊ A`), so equality of payoff functions already means *agreement on
the smaller game's profiles*. We keep `u` total and define `Game.EqOn` (same strategy
sets, payoffs agree on profiles); Definition 5's "the resulting games are not equal"
uses it, never Lean `=`.

### 3.3 `dd:certainty` — "with certainty" is a filter; the paper's case is `ae μ`

Definition 3 and everything through Theorem 3 use "with certainty" only through: it is
monotone, closed under finite conjunction, and (for strictness) non-degenerate. Those
are the filter axioms; the paper's "with certainty" is `∀ᵐ ω ∂μ` (`Filter.ae`), and
"with positive probability" is `∃ᶠ ω in ae μ` (Mathlib: `∃ᶠ` in `ae μ` ⟺ positive
measure). Proposal:

Codex's review (§9, F2) correctly objects that a public filter-level lemma *plus* an
`ae`-level paper theorem of the same shape is exactly the parallel-copy surface
`CLAUDE.md` forbids. So: **one authoritative declaration per result.** Two admissible
arrangements, pick one:

- **(i) Paper nodes at the filter level** (recommended): Definition 3, Lemma 2, Definition
  4, Theorem 3 stated for a family `X : Game N 𝒜 → Ω → (∀ i, 𝒜 i)` and `L : Filter Ω`
  (`[L.NeBot]` where strictness appears); "with certainty" is `∀ᶠ ω in L`, "with
  positive probability" is `∃ᶠ ω in L`. The `Representatives` model instantiates
  `L := ae μ` *by notation*, not by a second theorem; the only `ae`-specific lemma is
  `∃ᶠ ω in ae μ ↔ μ {…} ≠ 0` (Mathlib `frequently_ae_iff`). These nodes are then
  `strengthened` in the coverage table, with the paper's `ae` case named in each
  docstring.
- (ii) Paper nodes at `ae` only, filter versions as *private* proof lemmas that never
  reach the consumer surface.

Why the generality is worth having: footnote 2 offers the *set-of-models* reading of
safety (dominance across all models of Π, no probabilities) — that is `L = ⊤` on a
model space, and it is the natural home for later work that does not want to posit a
distribution over how delegates play. *RULING 2:* (i) or (ii).

### 3.4 `dd:representatives` — the model of Π

```
structure Representatives (N) (𝒜 : N → Type u) where
  Ω : Type v
  [mΩ : MeasurableSpace Ω]
  μ : Measure Ω
  [prob : IsProbabilityMeasure μ]
  play : Game N 𝒜 → Ω → (∀ i, 𝒜 i)                      -- Π(Γ)
  mem  : ∀ Γ ω, play Γ ω ∈ Γ.profiles                     -- "random variable over A"
  fiber : ∀ Γ a, MeasurableSet {ω | play Γ ω = a}         -- enough for P(Π(Γ)=a), E, E[·|Π(Γ)=a]
```

All games are played on **one** probability space — that is what makes
`Π(Γ') ∈ Φ(Π(Γ))` a statement about a joint distribution, which is the whole content of
Definition 3. Membership is everywhere rather than a.s. (harmless: it is the codomain of
the paper's random variable). Per-player components `Πᵢ(Γ) := (play Γ ω) i` are what
Appendix A speaks about; they come for free.

**Support.** `supp Π(Γ) := {a | μ {ω | play Γ ω = a} ≠ 0}` (finite, inside
`Γ.profiles`) is load-bearing for Algorithm 1, Prop 12, Lemma 13, Cor 14 and Thm 15 and
gets its own carrier. Lemma 13's conditional expectations are stated **on the support
only**; Mathlib's `ProbabilityTheory.cond` on a null event is the zero measure, so the
paper's "for all `a ∈ A`" must be read as "for all `a ∈ supp Π(Γ)`", with `uᵉ` on
unplayed token outcomes set to any value `≥ u(a)` in `C(Γ)` (e.g. `u(a)` itself) and
proved almost surely unplayed. Corollary 14 is stated with the explicit
`Π`-dependent formula: the achievable set is the Minkowski sum over `a ∈ supp Π(Γ)` of
`P(Π(Γ)=a) • {y ∈ C(Γ) | y ≥ u(a)}`, a convex polytope in `ℝⁿ`.

Assumptions 1 and 2 are `Prop`-valued predicates on `Representatives N 𝒜`
(`SatisfiesA1 Π`, `SatisfiesA2 Π`); "Under Assumptions 1 and 2, Γˢ is an SPI on Γ" is
`∀ Π, SatisfiesA1 Π → SatisfiesA2 Π → IsSPI Π Γ Γˢ`.

### 3.5 `dd:iso` — game isomorphism = per-player bijections, strictly positive scaling

Two readings the printed definition leaves open, both forced by later use:

- `λ ∈ ℝⁿ₊` must mean **`λᵢ > 0`**. With `λᵢ = 0` allowed, "isomorphic" is not
  symmetric (the inverse relation needs `1/λᵢ`), the §4.4.3 book argument composes
  isomorphisms through their inverses, and Lemma 4's proof solves for `λ` from two
  distinct values.
- `Φᵢ : Aᵢ → A'ᵢ` must be **bijections**. §2 does not say so; Appendix C ("by
  bijectivity of Φ, Ψ"), Lemma 13's "WLOG" relabeling, and §4.4.3 all use it, and with
  non-surjective "isomorphisms" Assumption 2 becomes absurd (it would force the
  representatives of a larger reduced game into the image of a smaller one).

Both go in `paper-errata.md`. The carrier is `GameIso Γ Γ' := { toFun : ∀ i, 𝒜 i → 𝒜 i,
bij : ∀ i, Set.BijOn (toFun i) (Γ.S i) (Γ'.S i), λ : N → ℝ, λ_pos, c : N → ℝ, affine : ∀
a ∈ Γ.profiles, ∀ i, Γ.u a i = λ i * Γ'.u (Φ a) i + c i }`.

### 3.6 `dd:book` — the consistency of A1 + A2 is a theorem, not a remark

Every "Under Assumptions 1 and 2" result is vacuous unless some `Representatives` model
satisfies both. §4.4.3 argues this informally and says the formal version "would need to
specify what the set of games looks like." Under `dd:universe` we can: choose (by
`Classical.choice`) a representative of each isomorphism class of fully reduced games
over `𝒜` and, for each reduced game, an isomorphism onto its representative; let the
"page" for a representative be a random outcome on `Ω`; define
`play Γ := Φ_{reduce Γ}⁻¹ ∘ page (class (reduce Γ))`. Proof obligations: path
independence of iterated strict dominance (Lemma 19 → a canonical `Game.reduce`);
composite of isomorphisms is an isomorphism (needs `dd:iso`); pages chosen with the
same `ω` for both games in Assumption 2.

This is an **N±** node in the repo's sense, and it should be built so that the page
distribution is a *parameter*: Proposition 16 needs a model satisfying A1 + A2 with
`P(Π(Γ) = (a,b)) = P(Π(Γ) = (b,a)) = p`, and Proposition 6's strictness clause needs
`P(Π(Γ) = (DM,DM)) > 0`. One construction serves all three.

### 3.7 `dd:derivation` — Definition 5 as a derivation system

Definition 5 asks whether an SPI can be *proved* from single applications of A1, A1 in
reverse (via Lemma 2.2) and A2. That is a syntactic object:

```
-- root Γ₀ fixed: every game in a Definition-5 chain is a subset game of Γ₀ (item 2)
inductive Step (Γ₀ : Game N 𝒜) :
    (Γ Γ' : Game N 𝒜) → Γ ⊆ Γ₀ → Γ' ⊆ Γ₀ → SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) → Type
| elim   (h : StrictlyDominated Γ i ã) : Step Γ (Γ.erase i ã) _ _ (elimRel i ã)
    -- Assumption 1: from the larger game to the erased one
| unelim (h : StrictlyDominated Γ i ã) : Step (Γ.erase i ã) Γ _ _ (elimRel i ã).inv
    -- Assumption 1 read backwards via Lemma 2.2: from the erased game back to the larger one
| iso    (h : Reduced Γ) (h' : Reduced Γ') (φ : GameIso Γ Γ') : Step Γ Γ' _ _ φ.rel
    -- Assumption 2, with the *chosen* isomorphism recorded

-- a chain of steps with composite relation; `Deriv Γ₀ Γ Γ' Φ`
```

(The first sketch of this had `unelim` pointing the wrong way and no root invariant —
codex F3.) Semantics is deliberately **not** "`Deriv Γ₀ Γ Γ' Φ → Γ ∼_Φ Γ'` under A1 +
A2": Assumption 2 supplies *some* isomorphism, not the recorded `φ`, so that statement
is false. What is true, and is what Definition 5 and Theorem 9 actually use, is:

- **Normalization** (Lemma 21, via Lemmas 19–20): every derivation has an equivalent one
  of shape `elim* ; iso ; unelim*` with the same composite relation.
- **SPI soundness** (Lemma 22 + Lemma 4 + Theorem 3): if some derivation from `Γ₀` to
  `Γˢ` has a Pareto-improving composite, then for every `Π` satisfying A1 + A2 there is
  *some* Pareto-improving correspondence `Γ₀ ∼_Ψ Γˢ`, hence `Γˢ` is an SPI on `Γ₀`. The
  isomorphism step is discharged by Lemma 4 exactly as the paper's "we will be lax"
  paragraph after Lemma 4 licenses.
- **Certificate form** (the unnumbered restatement after Lemma 21, corrected — see D9):
  a Pareto-improving derivation exists iff there is a subset game of `Γ₀`, fully reduced,
  isomorphic to `reduce Γ₀` by a Pareto-improving isomorphism (and `Γˢ` reduces to it).
  This is what Theorem 9's membership algorithm and Proposition 10's search enumerate.

Definition 5 is then: `∃ Γˢ ⊆ Γ₀, ∃ Φ, ∃ d : Deriv Γ₀ Γ₀ Γˢ Φ, Nontrivial ∧
ParetoImproving Φ` with the strict / unilateral clauses (items 4–5) as stated.

### 3.8 `dd:program-game` — Theorem 1

Appendix A's program game is abstract (`PROG = ∏ PROGᵢ`, nondeterministic `exec`,
`U = E[u ∘ exec]`), and Algorithm 2 needs three language features: compare the whole
profile of source codes with one's own, play a fixed mixed strategy, and call
`Πᵢ(Γ')` for a subset game `Γ'`. Following the implementation-independence rule we
already use elsewhere: (i) an abstract `ProgramGame Γ Π` interface — program types,
`exec`, the induced utility; (ii) a concrete minimal language `Prog` closed under those
three instructions, with `exec` by structural recursion and the player index as a
runtime input, as the paper does it so that everyone submits identical code; (iii)
Proposition 18 over (i) with the concrete realization proved to satisfy it.

Two design constraints codex's review (F4) sharpened:

- **Randomness.** `exec` must not simply live on `Π.Ω`: Algorithm 2's punishers play the
  mixed profile `minimax(i, ·)`, and the threat-point bound `E[uᵢ] ≤ vᵢ` holds only if
  the deviator's realized action is **independent** of the punishers' randomization
  (the threat point is a max against a *fixed* product mixture). So the program game
  carries its own product of private seeds `Ω_exec = Π.Ω × ∏ᵢ Ωᵢ`; the `Πᵢ(Γ')` call
  reads `Π.Ω`, a `play σ` instruction reads player `i`'s own seed, and the equilibrium
  proof uses independence explicitly. This is a disclosed reading — the paper says
  nothing about where `exec`'s randomness comes from.
- **Code equality.** Tennenholtz's trick compares source code, so `Prog` needs
  `DecidableEq`. A `Game` embedded as data carries `ℝ`-valued payoffs, so structural
  decidable equality is classical. Options: accept classical `DecidableEq` (the meta-game
  is a mathematical object, and the paper's programs contain real payoffs too), or refer
  to games through identifiers resolved by an environment. The former is simpler and
  honest; ruling below.

Two statement-level corrections will be needed and disclosed: the deviator's payoff is
*at most* the threat point, not equal to it (the paper says "is"); and the threat point
minimizes over **independent** mixtures `×ⱼ≠ᵢ Δ(Aⱼ)`, which for `n > 2` is a compact
non-convex program — existence by compactness, no LP, and EconCSLib's two-player
minimax covers only the `n = 2` remark.

*RULING 3:* build the concrete language with private seeds and classical code equality
(recommended), or stop at the abstract interface with the Algorithm-2 profile's
existence as a structure field (weaker, and the kind of "assume the antecedent" the repo
standard warns against)?

### 3.9 `dd:complexity` — complexity claims

Theorem 9, Proposition 10, Lemma 11, Proposition 12 each bundle a mathematical statement
with a complexity-class or runtime statement. The mathematics is fully formalizable:

- Thm 9 membership: the certificate characterization (§3.7) — an SPI derivation exists
  iff there is a reduced subset game of `Γ` isomorphic to `reduce Γ` by a
  Pareto-improving isomorphism (plus the unilateral/strict variants).
- Thm 9 hardness: Lemma 28's construction `graphs ↦ games` and the **iff** "G is a
  subgraph of Ĝ ⟺ the constructed game has a (strict/unilateral) SPI" — a combinatorial
  theorem about payoff matrices, no machine model needed.
- Prop 10: the search space is the set of per-player injections from the `l` reduced
  actions into the `m` original ones; `Decidable` with an explicit `m^l` bound on
  `Fintype.card` of the certificate type.
- Lemma 11: `y` is Pareto-optimal in `C(Γ)` ⟺ the stated LP has optimum `0`.
- Prop 12: `∃` strict perfect-coordination SPI ⟺ `∃ a ∈ supp Π(Γ)` with `u a`
  Pareto-suboptimal in `C(Γ)` (Algorithm 1 correctness).

"NP-complete", "`O(m^l)`", "polynomial time" are claims about encodings and machines
the paper does not specify beyond "explicit payoff matrix". Rendering them faithfully
means a cost model for games-as-inputs plus reductions — the `dd:fuel` liability all
over again, and `complexitylib` is not obviously the right vehicle for `NP` over
matrix encodings.

Codex (F9) is right that the certificate iffs are *not* Theorem 9, and that the
repository's rule is that the statement is the trust surface. So the honest accounting
is the coverage table's existing vocabulary: with tranche F deferred, Theorem 9,
Proposition 10, Lemma 11 and Proposition 12 are carried as **qualified** nodes — the
`Paper node:` label sits on the mathematical content, the docstring says which
clause of the printed statement is not rendered and why, and the paper is **not**
`completed` in the registry until either tranche F lands or you rule those four nodes
out of scope. No exact-tier claim will be attached to a certificate substitute.
*RULING 6:* accept qualified status for those four nodes for now (recommended), rule
them out of scope, or require tranche F as part of the initial scope.

---

## 4. Tranches and effort

Units per the standing convention: total faithful-formalization difficulty, in Cartesian
Frames (CF) and Finite Factored Sets (FFS) multiples, built from representation
difficulty, missing substrate, forced substitutions, source defects, and completion
overhead. No line-count ratios.

| Tranche | Content | Representation | Substrate | Defects | Estimate |
|---|---|---|---|---|---|
| **A. Core** | §2 carriers, Defs 1–4, Lemma 2, Thm 3, A1/A2, Lemma 4, Props 5–8, `⪰`, EconCSLib bridge | `dd:universe`, `dd:total-utility`, `dd:certainty`, `dd:representatives`, `dd:iso` — five decisions, none a research question | EconCSLib dependency; Mathlib `SetRel`, `ae`, `convexHull` not yet | D1–D5 below | **0.4–0.6 FFS ≈ 0.5–0.8 CF** |
| **B. Consistency** | `dd:book` model; Lemma 19 and canonical `reduce`; page distribution as a parameter; Prop 16 and Prop 6-strictness witnesses | one construction, one genuine proof (path independence) | none new | §4.4.3 is informal in the paper: this is **supplied** mathematics | **0.3–0.4 FFS** |
| **C. Derivations and Thm 9 mathematics** | `dd:derivation`, soundness, Lemmas 20–22, the certificate characterization, Def 8, Lemma 28 as an iff, Prop 10 as `Decidable` + bound | derivation-system design | none | Lemma 21's statement is garbled across a page break in the source; App. D proofs are sketches | **0.4–0.6 FFS** |
| **D. §5 coordination** | `C(Γ)`, token games, Defs 6–7, Lemma 11 (LP iff), Prop 12 (iff), Lemma 13, Cor 14, **Thm 15**, Prop 16 | conditional expectation on finite-range variables; 2-D Pareto frontier as a curve and the segments L1–L3 | Mathlib has `ProbabilityTheory.cond`, `convexHull_add`; **no** Pareto-frontier-of-a-polygon API — that is the missing substrate | D6, D7 | **0.6–1.0 FFS**, Thm 15 dominates |
| **E. Program equilibrium** | `dd:program-game` interface + concrete language, Prop 18, Thm 1, n-player threat point | language design; threat point over independent mixtures | EconCSLib minimax for `n = 2` only | D8 | **0.3–0.5 FFS** (abstract-only: 0.1) |
| **F. Complexity wrappers** | NP-completeness / `O(m^l)` / poly-time as machine statements | cost model for matrix-encoded games; Lemma 27 as an axiom | essentially all missing | none | **1.5–3 FFS**, and a permanent `(c)`-type liability; recommend deferring |
| Completion overhead | registry, text-extraction checker (Condensation's parser adapted), inventory, README/KNOWLEDGE/errata, consumer API + client tests, audits, read-through | — | — | — | **0.3 FFS** on top of A–E |

Total for A–E with F deferred: roughly **2–3 FFS ≈ 3–4 CF**; A alone is a clean,
shippable first milestone with Theorem 3 and the four worked examples proved.

Codex (F12) judges B, D and E under-estimated because each contains statement repair or
semantic design, not just proofs: B needs a canonical global reduction and a
measurable, parametric book; D cannot be priced until Theorem 15's projections are
ruled on (D12); E's language needs private seeds and a code-equality decision. I
agree the ranges should be read as *conditional on the rulings in §8* and expect B and
E toward the top of their ranges. Point estimates for D are withdrawn until RULING 8.

---

## 5. Source defects found on the first reading (to become `paper-errata.md`)

- **D1** Definition 1, strictness clause: `uᵢ(Π(Γˢ)) > uᵢ(Π(Γˢ))` should read
  `uᵢ(Π(Γˢ)) > uᵢ(Π(Γ))`.
- **D2** Definition 4: "such that `Γ ∼_Φ Γ'`" should be `Γˢ`; `Φ : A → Aˢ` should be
  `⊸`. Lemma 4 is stated for arbitrary isomorphic `Γ, Γ'` but "Pareto-improving" is only
  defined when `Γ'` is a subset game of `Γ` — the hypothesis is missing.
- **D3** Theorem 3's proof quantifies "for `i = 1, 2`" in an `n`-player statement, and
  the ⇒ direction opens with the inequality reversed (`uᵢ(Π(Γ)) ≥ uᵢ(Π(Γˢ))`).
- **D4** Lemma 2.7's proof cites "reflexivity (Lemma 2.1)" for symmetry (2.2). Prop 6's
  proof writes `Ψ(Φ(Γˢ))` for `Ψ(Φ(a₁, a₂))`. Prop 7's proof eliminates "Player 1's
  `R₁`" and "Player 2's `R`": in Table 6 the eliminated strategies are Player 1's `R`
  and then Player 2's `F` (`T` dominates `R`; with `R` gone, `C` dominates `F`), reaching
  `({T}, {C})`. (My first draft said `R` and `C` — codex F16 caught it.)
- **D5** Isomorphism (§2): `λ ∈ ℝⁿ₊` ambiguous between `≥ 0` and `> 0`; bijectivity
  unstated. Both needed (§3.5); codex F17 supplies the two-line counterexamples (a
  one-action zero game "into" a two-action zero game; `λ = 0` making isomorphism
  asymmetric).
- **D6** *(downgraded, codex F18)* Lemma 13's "WLOG assume Φ maps `aᵢ ↦ âᵢ`" is a
  proof-level relabeling of fresh tokens, not a statement defect: the token copy has the
  same payoff range as `Γ`, so any A2-supplied isomorphism is payoff-preserving
  (`λ = 1, c = 0` where nonconstant) and the hats can be re-indexed along it. In Lean the
  proof defines `uᵉ` along the supplied isomorphism explicitly; no statement change.
- **D7** Corollary 14 says "convex polygon" for an `n`-player set (a polytope); and
  Lemma 13 / Corollary 14 condition on `Π(Γ) = a` for every `a ∈ A` including
  null events. Rendered on `supp Π(Γ)` with the explicit weighted-polytope formula
  (§3.4).
- **D8** Proposition 18's proof: "`exec(c₋ᵢ, c'ᵢ)` **is** the threat point" — it is at
  most the threat point (`≤ vᵢ`), which is what the chain needs; and the bound
  requires the deviator's action to be independent of the punishers' randomization
  (§3.8).
- **D9** *(replaced, codex F21)* Lemma 21's statement reads continuously across the page
  break; the genuine typos are `Γ'ₘ = Γₘ` for `Γ'ₘ = Γₖ` (line 2293 of the extraction)
  and "`Γˢ'ʳᵉᵈ` is isomorphic to `Γˢ'ʳᵉᵈ`" for "… to `Γʳᵉᵈ`" in the concise restatement
  (line 2311).
- **D10** *(codex F11)* Definition 7 is *named* the **strict** full-coordination decision
  problem but its body asks only for a perfect-coordination SPI; Proposition 12 (which
  it serves) is about strict SPIs. *RULING 7:* read "strict" into the body (recommended,
  it is what Algorithm 1 decides) or carry the body as printed.
- **D11** *(codex F11)* Proposition 23 sits in the *omnilateral* subsection D.2.1 and its
  algorithm builds an omnilateral SPI, but its statement says "unilateral". Lemma 19's
  discussion says the lemma "does not by itself prove … path dependence" where
  independence is meant.
- **D12** *(codex F7, the serious one)* **Theorem 15 as printed can name nonexistent
  points.** `PF(C)` is the *strong* Pareto frontier (no `y' ≥ y` with a strict
  coordinate), and the theorem projects `x₁ᵐⁱⁿ`, `x₁ᵐᵃˣ`, `x₂ᵐⁱⁿ`, `x₂ᵐᵃˣ` onto `PF(C(Γ))`
  with `πᵢ(x, PF(C(Γ)))`, which exists only if `x` is a coordinate of a frontier point.
  Counterexample: a `2×2` game with payoffs `(0,0), (1,0), (0,1), (1,1)` has
  `C(Γ) = [0,1]²` and `PF = {(1,1)}`; if `Π(Γ)` plays the `(0,0)` outcome surely, Case A's
  premise holds (`(1,1)` dominates the support) but `π₁(0, PF)` does not exist. The
  paper's own remark ("such a `y'` exists iff `x` is `i`'s utility in some feasible
  payoff vector") is about `πᵢ(x, C(Γ))`, i.e. projection onto `C(Γ)` (the *weak*
  frontier), which always exists for feasible `x`. *RULING 8:* read the projections as
  `πᵢ(x, C(Γ))` and re-verify Appendix E under that reading (recommended), or make `πᵢ`
  partial and add existence hypotheses. Either way this is a statement-level erratum
  and Theorem 15's tranche cannot start before the ruling.

None of these threatens a headline result except that D12 changes Theorem 15's
statement; D5, D8, D10, D12 change *statements*, so they are disclosures, not
proof-level fixes.

---

## 6. Research hooks the substrate should not foreclose

Anson's stated interests: participation independence, foreknowledge independence, SPI
selection. As I understand the (post-2022, CLR research-agenda) usage — verify me on
this — PI says an agent's demands under the SPI equal its demands had the counterpart
not participated, and FI says they equal its demands had it known in advance the
counterpart would not participate. Both are statements comparing `Πᵢ` across
*instruction profiles* in the meta-game, and FI additionally distinguishes what an
agent knew *before* choosing its instruction from what it learns afterwards.

Codex's review (F1, F5, F6) is right that my first draft overclaimed here, and the
correction matters for the design. A `Game N 𝒜` is the paper's *subset-game
instruction* — one payload a player can hand a representative — not the instruction
type. The meta-game of §3.2 / Appendix A has each player independently submitting a
program that can *observe the other programs*, and §6's selection problem is about
mismatched demands and conditional acceptance, neither of which is a statement about
games. So what this formalization provides for PI / FI / selection is narrower and
should be stated as such:

- **Provided by tranche A:** `Π` total on all games over one universe, per-player
  components on one `Ω`, the `⪰` preorder on games as a *correspondence-level tool*,
  and (under `dd:certainty` (i)) a safety notion that also works for set-valued
  uncertainty.
- **Provided by tranche E, if built as §3.8 says:** a paper-neutral
  `Instruction i` / `InstructionProfile` layer with an execution semantics, of which
  "play subset game `Γ'`" is one constructor and Algorithm 2 is one program. This is the
  object PI is a property of ("`Πᵢ` under the SPI profile equals `Πᵢ` under the profile
  where `j` submits its *default* instruction"), so the layer must carry an explicit
  notion of default / non-participation instruction from the start. **Nothing in the
  2022 paper needs that**, so it is a substrate decision made for the research goal and
  will be recorded as one.
- **Not provided, and should not be pretended:** FI's two-stage information structure
  (knowing ex ante versus learning ex post) — it needs a model of what the agent knows
  when it chooses, which no object in this paper has; a notion of "demand" beyond the
  instruction; any bargaining-solution structure; and the §6 selection problem itself,
  which needs candidate demands, a compatibility/resolution rule for mismatched
  profiles, and maximality on *the original players'* payoffs (subset-game utilities
  are not the players' utilities, so the game preorder does not order SPIs for them).

*RULING 9:* is designing tranche E's instruction layer for PI (default instruction as a
first-class object, execution semantics parametric enough to compare counterfactual
profiles) part of this project's scope, or is the 2022 paper's own Theorem 1 enough and
the research layer a separate follow-up?

---

## 7. Proposed file layout (`SafeParetoImprovements/`)

| file | content |
|---|---|
| `Game.lean` | `Game`, profiles, `EqOn`, subset games, `erase`, bridge `toStrategic`, §2 dominance / Pareto vocabulary via EconCSLib with set-level characterizations |
| `Isomorphism.lean` | `GameIso`, composition/inverse, Lemma 4 |
| `Reduction.lean` | one-step elimination, Lemma 19, canonical `reduce`, `Reduced` |
| `Representatives.lean` | `Representatives`, certainty as `ae`, `IsSPI` / `IsStrictSPI` / `Unilateral` (Defs 1–2) |
| `Correspondence.lean` | multivalued functions on `SetRel`, Def 3, Lemma 2 (filter substrate + paper layer), Def 4, **Thm 3**, `⪰` |
| `Assumptions.lean` | A1, A2 as predicates; the lax-use lemma after Lemma 4 |
| `Book.lean` | `dd:book` consistency model with parametric page distribution (N±) |
| `Examples.lean` | Tables 1–7 as concrete games; Props 5–8; Prop 16's witness |
| `Derivation.lean` | `dd:derivation`, soundness, Lemmas 20–22, certificate characterization, Def 5, Thm 9 mathematics, Prop 10 |
| `Coordination.lean` | `C(Γ)`, token games, Defs 6–7, Lemma 11, Prop 12, Lemma 13, Cor 14 |
| `Frontier.lean` | 2-D Pareto frontier, L1–L3, **Thm 15** |
| `ProgramGame.lean` | `dd:program-game` interface, concrete `Prog`, threat point, Prop 18, **Thm 1** |
| `API.lean` | the documented consumer import (`CLAUDE.md`, consumer readiness): games, representatives, SPI, correspondence, the substrate lemmas — with `APITests/SafeParetoImprovements.lean` as the client-style test; both mandatory before `completed` |
| `SafeParetoImprovements.lean` | aggregator + `dd:` glossary |
| `notes/` | paper PDF + extraction (committed), this note, the codex review, `paper-errata.md`, roadmap |

Registry entry: `"safe-pareto-improvements"`, `scheme: printed-independent`,
`source_format: text-extraction`, `api` / `api_test` as above, checker
`scripts/check-safe-pareto-improvements-nodes.py` adapted from Condensation's
header-line parser, asserting the 38 distinct node headers (restatements in Appendices
C and E and the split "Theorem 17" header must be deduplicated by the parser).

---

## 8. Open rulings, collected

0. Scope = §2–§6 with appendix proofs (no §8 exists).
1. EconCSLib as a pinned lake dependency (recommended) vs. vendored slice.
2. Certainty: paper nodes at the filter level, `strengthened` (recommended) vs. `ae`
   nodes with private filter lemmas. No duplicated surface either way.
3. Theorem 1: concrete program language with private seeds and classical code equality
   (recommended) vs. abstract interface only.
4. `dd:universe` / `dd:total-utility` / `dd:iso` as stated.
5. The A1 + A2 consistency model as a required N± node with parametric page
   distribution.
6. Complexity: Theorem 9 / Prop 10 / Lemma 11 / Prop 12 carried as **qualified** nodes
   with tranche F deferred, paper not `completed` until F lands or they are ruled out
   (recommended) vs. out of scope vs. tranche F in initial scope.
7. Definition 7: read "strict" into the body (recommended) vs. as printed.
8. Theorem 15: projections onto `C(Γ)` rather than the strong frontier `PF(C(Γ))`
   (recommended, re-verifying Appendix E) vs. partial `πᵢ` with existence hypotheses.
9. Tranche E's instruction layer designed for participation independence (default
   instruction first-class) as part of this project vs. a separate follow-up.

## 9. Codex review, 2026-09-04

Full findings in `codex-review-2026-09-04.md` (prompt alongside). Disposition:

| Finding | Verdict | Action |
|---|---|---|
| F3 `dd:derivation` unsound as sketched (orientation, no root, false soundness) | **accepted** | §3.7 rewritten |
| F4 program game: code equality, randomness independence | **accepted** | §3.8 rewritten; RULING 3 revised |
| F5 / F1 / F6 PI-FI-selection readiness overstated; `Game` is not an instruction | **accepted** | §6 rewritten; RULING 9 added; §3.1 wording fixed |
| F7 Theorem 15 projections may not exist | **accepted, verified** | D12; RULING 8 |
| F8 support undefined; Lemma 13 on null events | **accepted** | §3.4 support paragraph; D7 |
| F9 certificate iffs are not Theorem 9 | **accepted** | §3.9 reframed as qualified nodes; RULING 6 revised |
| F2 duplicated filter/`ae` surface | **accepted** | §3.3 one declaration per result; RULING 2 revised |
| F10 API.lean / APITests missing from layout | accepted | §7 |
| F11 Def 7 / Prop 23 / Lemma 19 defects | **accepted, verified** | D10, D11; RULING 7 |
| F12 estimates under-costed | accepted in part | §4 caveat |
| F13–F15, F17, F19, F20 (D1, D2, D3, D5, D7, D8 confirmed) | — | unchanged |
| F16 my Prop 7 correction was itself wrong | accepted | D4 fixed |
| F18 D6 refuted as a statement defect | **accepted** | D6 downgraded to proof-level |
| F21 D9 refuted; real Lemma 21 typos supplied | **accepted, verified** | D9 replaced |

Codex's summary also endorsed: the `Game → StrategicGame` bridge (EconCSLib's
`StrictlyDominates` coincides with the paper's definition on the bridged game because
`deviate` erases the deviator's own coordinate); a pinned dependency over vendoring;
and the book construction (automorphisms harmless because A2 is existential, singleton
reductions fine, ties by choice) once isomorphisms are positive-affine bijections.
