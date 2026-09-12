# Tranche D design note — §5, SPIs under improved coordination

**Status:** rulings 10–13b given 2026-09-12 (`scoping.md` §8); D1 landed (`Coordination.lean`,
`Examples/Chicken.lean`, `Examples/TokenWitnesses.lean`, with the round-4 blocker fixed per
`.harness/adjudication/token-games-investigation.md`: §5 examples over `X ⊕ ℕ`, `HasRoomOutside`,
label-free kernel for Proposition 16). D2–D4 to follow under those rulings; Corollary 14's
polytope clause is to be attempted (RULING 12). Covers §5.1–§5.3 minus Theorem 15
(RULING 8: deferred, erratum D12). Nodes: the unnumbered `C(Γ)` and token games, Definition 6,
Definition 7 (RULING 7: "strict" read into the body, erratum D10), Lemma 11, Algorithm 1,
Proposition 12, Lemma 13, Corollary 14, Proposition 16. Errata already recorded that bind the
design: D6 (Lemma 13's "WLOG" is a relabelling along the supplied isomorphism) and D7 (Lemma
13's conditional expectations exist only on the support; Corollary 14's "polygon").

## 0. What the paper gives us

* `C(Γ) := u(Δ(A))`, the payoff vectors feasible by correlated strategies — the convex hull
  of `u(A)` (l. 1280–1294).
* A **perfect-coordination token game** `(Aˢ, uˢ, uᵉ)`: a game `(Aˢ, uˢ)` for the
  representatives whose actions are fresh tokens (`Aˢᵢ ∩ Aᵢ = ∅`), and an assignment
  `uᵉ : Aˢ → C(Γ)` by the original players of a correlated strategy of `Γ` to each token
  outcome (l. 1295–1315).
* **Definition 6**: a perfect-coordination SPI is a token game with `uᵉ(Π(Aˢ, uˢ)) ≥ u(Π(Γ))`
  with certainty; strict if some player gains with positive probability.
* **Definition 7 / Algorithm 1 / Lemma 11 / Proposition 12**: deciding whether a *strict*
  perfect-coordination SPI exists reduces, under Assumption 2 and given `supp Π(Γ)`, to
  checking whether some supported outcome is Pareto-suboptimal in `C(Γ)`, which is a linear
  program.
* **Lemma 13**: every perfect-coordination SPI `Γ′` can be replaced by an *isomorphic copy* of
  `Γ` with `uᵉ` chosen so that the conditional expected payoffs agree; **Corollary 14**: the
  achievable expected payoffs form a convex set.
* **Proposition 16**: a game (Table 7) and representatives for which a Pareto improvement is
  not safely achievable.

## 1. Carriers

```
Game.feasible (Γ) : Set (N → ℝ) := convexHull ℝ (Γ.u '' Γ.profiles)          -- C(Γ)
structure TokenGame (Γ : Game N 𝒜) where
  game : Game N 𝒜                       -- (Aˢ, uˢ), what the representatives play
  fresh : ∀ i, Disjoint (game.S i) (Γ.S i)
  ue : (∀ i, 𝒜 i) → N → ℝ               -- uᵉ, total like every payoff (dd:total-utility)
  ue_mem : ∀ a ∈ game.profiles, ue a ∈ Γ.feasible
TokenGame.IsSPI (X : Play) (L) (T) : Prop := ∀ᶠ ω in L, Γ.u (X.play Γ ω) ≤ T.ue (X.play T.game ω)
TokenGame.IsStrictSPI … := T.IsSPI ∧ ∃ i, ∃ᶠ ω in L, Γ.u (X.play Γ ω) i < T.ue (X.play T.game ω) i
```

* `C(Γ)` is Mathlib's `convexHull` of a finite set; the paper's mixture description is a
  lemma (`Finset.mem_convexHull`), not the definition. `dd:feasible`.
* Token games live over the same universe as `Γ` (`dd:universe`); freshness is a field, and
  the constructions that *build* token games (Proposition 12 ←, Lemma 13, Corollary 14 ⊇)
  need **room**: `Game.HasRoom Γ := ∀ i, ∃ t : 𝒜 i → 𝒜 i, Set.InjOn t (Γ.S i) ∧ ∀ a ∈ Γ.S i,
  t a ∉ Γ.S i`. The paper assumes fresh tokens exist silently; here it is a hypothesis on the
  universe, discharged in examples by `𝒜 i := ℕ` or a sum type (`dd:room`, already
  announced under `dd:universe`).
* Definition 6 is stated at the certainty-filter level like Definitions 1–4 (`dd:certainty`),
  with the `ae μ` realization iff in `Representatives.lean`'s style.

## 2. The isomorphism problem, and the shape of the constructions

Assumption 2 supplies *some* isomorphism between the full reductions of two isomorphic
games. When the token game is an isomorphic copy of `Γ`, the supplied isomorphism `φ` need
not be the natural copy map: composing the two gives a payoff-preserving automorphism of
`reduce Γ`, and for games with payoff symmetries that automorphism may permute the support.
Two consequences the design must respect:

1. **Every token game we build is built *after* `φ` is known** — `uᵉ` is defined along `φ`
   (this is exactly what erratum D6 says the paper's "WLOG" amounts to). Hence Definition 7,
   Proposition 12, Lemma 13 and Corollary 14 are all stated **for a given `Π`** satisfying the
   assumptions (`∀ X, SatisfiesA1 → SatisfiesA2 → …`), with the token game existentially
   quantified *inside*. This matches the paper, whose Algorithm 1 takes `supp Π(Γ)` as data
   and whose Lemma 13 says the original players "will in general not be able to construct
   `Γˢ`" without knowing `Π`'s distribution. **RULING 10 needed:** confirm this per-`Π`
   reading (the alternative — a single token game that is an SPI for *every* `Π` satisfying
   the assumptions — is provable for Proposition 12 by improving the whole payoff class of
   the suboptimal outcome, but is not what the paper states and fails for Lemma 13).
2. **Assumption 1 joins Assumption 2** as a hypothesis of Lemma 13, Corollary 14 and
   Proposition 12 whenever `Γ` is not assumed reduced: Assumption 2 speaks only about the
   full reductions, and without Assumption 1 the representatives may play a dominated action
   of `Γ` about which the isomorphism says nothing. The paper writes "under Assumption 2"
   but works throughout §4–§5 under both; the alternative is to state the nodes for reduced
   `Γ` only. **RULING 11 needed:** add Assumption 1 (recommended, and disclosed at the
   statements) vs. restrict to reduced games.

## 3. Nodes

* **Lemma 11** (qualified, `dd:complexity`): the mathematics is the LP characterization
  `y ∈ C(Γ) → (Γ.ParetoOptimalIn y C(Γ) ↔ ∀ p ∈ Δ(A), u(p) ≥ y → ∑ᵢ (uᵢ(p) − yᵢ) = 0)`; the
  "by linear programming, in polynomial time" clause is not rendered and the docstring says
  so. `Game.ParetoOptimalIn` (Game.lean) is the carrier of "Pareto-optimal in".
* **Definition 7** (D10, RULING 7): `StrictPerfectCoordinationSPIDecision X L Γ := ∃ T :
  TokenGame Γ, T.IsStrictSPI X L`, for a given play family — per RULING 10.
* **Proposition 12** (qualified): Algorithm 1's correctness as an iff, under Assumptions 1–2
  and room: `(∃ T, T.IsStrictSPI …) ↔ ∃ a ∈ Π.support Γ, ¬ Γ.ParetoOptimalIn (Γ.u a) C(Γ)`;
  the "polynomial time" clause is not rendered. `→`: a positive-probability strict-gain
  event is covered by finitely many outcomes, one of which is in the support and dominated
  by a feasible point. `←`: the token copy of `Γ` along the supplied `φ`, with `uᵉ` equal to
  `u` transported except at `φ(a₀)`, where it is the dominating point. Algorithm 1 itself is
  the decision procedure this iff describes; it gets no separate carrier.
* **Lemma 13** (D6, D7): for `Π` under Assumptions 1–2 with room, for every token game `Γ′`
  that is a perfect-coordination SPI, there is `uᵉ` on the token copy `(Â, û)` of `Γ` such
  that the copy is a perfect-coordination SPI and, for every `a ∈ supp Π(Γ)`,
  `E[uᵉ(Π(Â,û)) | Π(Γ) = a] = E[u′(Π(Γ′)) | Π(Γ) = a]`, hence the unconditional
  expectations agree. Conditional expectation is Mathlib's `ProbabilityTheory.cond` on the
  event `{Π(Γ) = a}`, which is measurable (`measurableSet_fiber`) and non-null on the
  support; on unplayed token outcomes `uᵉ` is `û` itself (any admissible value, as D7
  records). Stated for `Representatives`, since expectations are integrals.
* **Corollary 14** (D7): with `S := supp Π(Γ)` and `P(a) := μ{Π(Γ) = a}`, the set
  `{E[uᵉ(Π(Γ′))] | Γ′ perfect-coordination SPI on Γ}` equals the weighted Minkowski sum
  `∑_{a ∈ S} P(a) • {y ∈ C(Γ) | y ≥ u(a)}` and is **convex** (and compact). "Convex polygon"
  is the paper's `n = 2` wording; the polytope claim (finitely many vertices) is not rendered
  — Mathlib has no Weyl–Minkowski — and the docstring says so. **RULING 12 needed:** accept
  convex-and-compact with the explicit formula as the carrier (recommended) vs. attempt the
  polytope clause.
* **Proposition 16**: Table 7 with representatives playing `(a, b)` and `(b, a)` each with
  probability ½ (`Book.prescribedRandom` on a fair coin, satisfying Assumptions 1–2), and
  the outcome `(c, c)` with payoff `(3, 3)`: no perfect-coordination SPI has expected payoff
  `(3, 3)`, because `(4, 0)` and `(0, 4)` are Pareto-optimal in `C(Γ)` (so `uᵉ` is forced
  there) and the total payoff of any feasible point is at most `6` (`convexHull_min` against
  the half-space), giving `E[u₁ + u₂] ≤ 6 − 4p < 6`. Self-contained; the strongest
  non-vacuity witness of the tranche.
* **Theorem 15**: deferred (RULING 8). Its Appendix E proof is the only consumer of the
  two-player Pareto-frontier geometry, so no frontier API is built in this tranche.

## 4. Tranche plan

D1. `Coordination.lean`: `Game.feasible`, `TokenGame`, `Game.HasRoom`, Definition 6 with its
    `ae` realization, `Game.tokenCopy` (the isomorphic copy along a room witness, with the
    `GameIso`), Lemma 11.
D2. Proposition 12 (both directions), Definition 7; the support machinery it needs
    (`Representatives.support` exists; add the finite-partition lemma
    `∫ f = ∑_{a ∈ supp} ∫_{Π = a} f`).
D3. Lemma 13 and Corollary 14 (conditional expectation on the support).
D4. Proposition 16 (Table 7 in `Examples/Chicken.lean`), plus a §5 witness file: a game with
    room, a token game that is a strict perfect-coordination SPI, and the iff of Proposition
    12 exercised on the Demand Game (`(DM, DM)` is Pareto-suboptimal in `C(Γ)`).

Effort ≈ 0.6 FFS (D3 dominates: conditional expectations and the finite total-expectation
identity). Rulings needed before Lean: 10, 11, 12 above; `dd:feasible`, `dd:room` go into
the glossary when D1 lands.
