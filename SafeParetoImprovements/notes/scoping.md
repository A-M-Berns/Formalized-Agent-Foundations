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
| 4.2 | (unnumbered) | equivalence relation `R` (∃ single-valued bijection), preorder `⪰` (∃ Pareto-improving Φ) | carriers; `⪰` is the §6 SPI-selection object |
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
| 5.3 | Lemma 13 | WLOG isomorphic-copy token games, conditional-expectation equality | in (needs care, §5 defect D6) |
| 5.3 | Cor 14 | safely-achievable expected payoffs form a convex polytope | in |
| 5.3 | Thm 15 | two-player geometric characterization (L1, L2, L3; App. E) | in, **own tranche** (2-D convex geometry) |
| 5.3 | Prop 16 | a Pareto improvement with no perfect-coordination SPI (Table 7) | in; needs a constructed Π with prescribed play probabilities (§3.6) |
| 6 | — | SPI selection problem: prose only, no nodes | no node; the `⪰` preorder, maximal SPIs and symmetric SPIs get carriers as the research hook |
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

Under this reading the positive results get *stronger* (Assumptions 1–2 quantify over
fewer games, the theorems over fewer models), and the consistency theorem must build
a model over an arbitrary universe. §5's token games need *room*: "`Aˢᵢ ∩ Aᵢ = ∅`" is a
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

- **Substrate layer** (supporting `lemma`s, consumer-visible): outcome correspondence,
  Lemma 2, Theorem 3, Pareto-improving correspondences stated for a family
  `X : Game N 𝒜 → Ω → (∀ i, 𝒜 i)` and an arbitrary `L : Filter Ω` (`[L.NeBot]` where
  strictness appears).
- **Paper layer** (the `theorem`s carrying `Paper node:`): the same statements at
  `L = ae Π.μ` on a `Representatives` model. One-line specializations, so the trust
  surface reads exactly as the paper and the read-through cost is the paper's.

Why bother: footnote 2 offers the *set-of-models* reading of safety (dominance across all
models of Π, no probabilities) — that is `L = ⊤` on a model space, and it is the natural
home for later work that does not want to posit a distribution over how delegates play.
*RULING 2:* accept the two-layer arrangement, or state paper nodes directly at the filter
level (then they are `strengthened` in the coverage table), or drop the generality.

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
Appendix A and any participation-style condition speak about; they come for free.

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
inductive Deriv : Game N 𝒜 → Game N 𝒜 → SetRel (∀ i, 𝒜 i) (∀ i, 𝒜 i) → Type
| elim   (h : StrictlyDominated Γ i ã)  : Deriv Γ (Γ.erase i ã) (elimRel i ã)
| unelim (h : StrictlyDominated Γ' i ã) : Deriv Γ' Γ'.erase… (elimRel i ã).inv   -- Lemma 2.2
| iso    (h : Reduced Γ) (h' : Reduced Γ') (φ : GameIso Γ Γ') : Deriv Γ Γ' φ.rel
| trans  : Deriv Γ Γ' Φ → Deriv Γ' Γ'' Ψ → Deriv Γ Γ'' (Φ.comp Ψ)
```

with **soundness** (`Deriv Γ Γ' Φ → ∀ Π, A1 Π → A2 Π → Γ ∼_Φ Γ'` — note A2 only gives
*some* isomorphism, so soundness of `iso` goes through Lemma 4 and is only for
Pareto-improving use; this is precisely the "we will be lax" paragraph after Lemma 4 and
must be rendered as the paper renders it, i.e. soundness is stated for the SPI
conclusion, not for the correspondence). Lemma 21 is then a **normalization theorem**
(every derivation ≃ eliminations ; one isomorphism ; reverse eliminations), Lemma 22 its
Pareto-improving refinement, and the unnumbered "conciser way to state" paragraph after
Lemma 21 is the characterization that Theorem 9's NP membership and Proposition 10's
search are built on. This is also the object an SPI-*selection* study wants: the set of
SPIs derivable from a given assumption set, ordered by `⪰`.

### 3.8 `dd:program-game` — Theorem 1

Appendix A's program game is abstract (`PROG = ∏ PROGᵢ`, nondeterministic `exec`,
`U = E[u ∘ exec]`), and Algorithm 2 needs three language features: compare the whole
profile of source codes with one's own, play a fixed mixed strategy, and call
`Πᵢ(Γ')` for a subset game `Γ'`. Following the implementation-independence rule we
already use elsewhere: (i) an abstract `ProgramGame Γ Π` interface — program types,
`exec` on `Π.Ω` (so `exec` and `Π` are jointly distributed, as the proof needs), the
induced utility; (ii) a concrete minimal language `Prog` (an inductive type with
decidable equality — code comparison is what Tennenholtz's trick runs on — closed under
those three instructions, with `exec` by structural recursion; the player index is a
runtime input, as the paper does it so that everyone submits identical code); (iii)
Proposition 18 over (i) with the concrete realization proved to satisfy it. Two
statement-level corrections will be needed and disclosed: the deviator's payoff is
*at most* the threat point, not equal to it (the paper says "is"); and the threat point
minimizes over **independent** mixtures `×ⱼ≠ᵢ Δ(Aⱼ)`, which for `n > 2` is a compact
non-convex program — existence by compactness, no LP, and EconCSLib's two-player
minimax covers only the `n = 2` remark.

*RULING 3:* build the concrete language, or stop at the abstract interface with the
Algorithm-2 profile's existence as a structure field (weaker, and the kind of "assume the
antecedent" the repo standard warns against)?

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
matrix encodings. *RULING 6:* carry the mathematics exactly and disclose the
complexity-class wrappers as **stated, not proved** (Prop 10 / Lemma 11 / Prop 12 as
`Decidable` + explicit bounds, Thm 9 as the two iffs), **or** open a complexity tranche
(E below) later. The former is my recommendation for the first pass.

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
  `R₁`" and "Player 2's `R`" for `R` and `C`.
- **D5** Isomorphism (§2): `λ ∈ ℝⁿ₊` ambiguous between `≥ 0` and `> 0`; bijectivity
  unstated. Both needed (§3.5).
- **D6** Lemma 13's "WLOG assume Φ maps `aᵢ ↦ âᵢ`" is not WLOG: Assumption 2 supplies
  *some* isomorphism, and for a game with a nontrivial payoff-preserving automorphism
  the identity labeling can be the wrong one, in which case the conditional-expectation
  *equality* fails (the SPI property survives via Lemma 4). Repair: define `uᵉ` along the
  isomorphism that Assumption 2 provides — the lemma is an existence statement and stays
  true. Corollary 14 inherits the repair.
- **D7** Corollary 14 says "convex polygon" for an `n`-player set (a polytope; the
  Minkowski sum of `P(Π(Γ)=a)`-scaled polytopes `{y ∈ C(Γ) | y ≥ u(a)}`); and its
  statement as printed conditions on nothing about `P(Π(Γ) = a) = 0` outcomes, which
  the proof of Lemma 13 needs to handle separately.
- **D8** Proposition 18's proof: "`exec(c₋ᵢ, c'ᵢ)` **is** the threat point" — it is at
  most the threat point (`≤ vᵢ`), which is what the chain needs; and the equilibrium
  requires the deviator's action to be independent of the punishers' randomization.
- **D9** Lemma 21's statement is split across a page break with a dangling "`m ≤ k` and
  `l` such that"; the intended structure is recoverable from its "conciser" restatement
  and Lemma 22.

None of these threatens a headline result; D5, D6, D8 change *statements*, so they are
disclosures, not proof-level fixes.

---

## 6. Research hooks the substrate should not foreclose

Anson's stated interests: participation independence, foreknowledge independence, SPI
selection. As I understand the (post-2022, CLR research-agenda) usage — verify me on
this — PI says an agent's demands under the SPI equal its demands had the counterpart
not participated, and FI says they equal its demands had it known in advance the
counterpart would not participate. Both are statements comparing `Πᵢ` across
*instruction profiles* in the meta-game. What the design above already provides:

- `Π` total on all games over the universe, with per-player components: counterfactual
  instruction profiles (unilateral changes, "the game with `j`'s instruction reverted")
  are ordinary `Game N 𝒜` values, and `Πᵢ Γ` versus `Πᵢ Γ'` is a plain comparison of
  random variables on the same `Ω`.
- The meta-game itself (`dd:program-game`) as a first-class object once tranche E
  lands; PI/FI are then properties of program profiles, not of games.
- The `⪰` preorder and the derivable-SPI set (`dd:derivation`) for SPI selection:
  maximal derivable SPIs, symmetric SPIs of symmetric games (§6's suggestion), and the
  filter-level safety notion for comparing SPIs under set-valued rather than
  probabilistic uncertainty.

What it does *not* provide and should not pretend to: a notion of "demand" beyond the
instruction itself, or any bargaining-solution structure. Those are the later papers'
objects and belong to their formalizations.

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
| `SafeParetoImprovements.lean` | aggregator + `dd:` glossary |
| `notes/` | paper PDF + extraction (committed), this note, `paper-errata.md`, roadmap |

Registry entry: `"safe-pareto-improvements"`, `scheme: printed-independent`,
`source_format: text-extraction`, checker `scripts/check-safe-pareto-improvements-nodes.py`
adapted from Condensation's header-line parser, asserting 38 headers.

---

## 8. Open rulings, collected

0. Scope = §2–§6 with appendix proofs (no §8 exists).
1. EconCSLib as a pinned lake dependency (recommended) vs. vendored slice.
2. Certainty: filter substrate + `ae`-level paper nodes (recommended) vs. filter-level
   nodes vs. no generality.
3. Theorem 1: concrete program language (recommended) vs. abstract interface only.
4. `dd:universe` / `dd:total-utility` / `dd:iso` as stated.
5. The A1 + A2 consistency model as a required N± node with parametric page
   distribution.
6. Complexity: mathematics exact, class/runtime claims disclosed as stated-not-proved
   (recommended) vs. a complexity tranche now.
