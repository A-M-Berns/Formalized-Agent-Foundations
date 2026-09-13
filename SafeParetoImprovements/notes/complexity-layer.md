# Tranche F — the complexity nodes (§4.6, Appendix D.2–D.3)

Design note for Theorem 9, Proposition 10, Propositions 23–26, Definition 8 and Lemma 28,
written before the Lean, in the same role as `instruction-layer.md` and
`coordination-layer.md`.  RULING 6 governs: these nodes are *qualified*.  The mathematics
of each printed statement is rendered exactly; the complexity-class and running-time
clauses ("NP-complete", "non-deterministic polynomial time", "`O(m^l)`", "linear time")
are disclosed at each declaration as not rendered, because the paper fixes no cost model
beyond "explicit payoff matrices" and the repository attaches no exact-tier claim to a
certificate substitute (`dd:complexity`, scoping note §3.9).  Lemma 27 (Cook 1971 via
[12]) is a cited external result and is **not carried**, exactly as Theorem 17 is not:
no declaration cites it, and no axiom stands in for it.

## 1. What each node says, and what is rendered

| Node | Printed content | Rendered content | Not rendered |
|---|---|---|---|
| Prop 23 | the guess-injections algorithm "runs in NP time and returns True iff there is a (strict) SPI" | `SPIDecision Γ ↔ ∃ c : Certificate Γ, c.Check`, and the strict variant | "NP time" |
| Prop 25 | the unilateral algorithm (three checks) "… iff there is a (strict) unilateral SPI" | `UnilateralSPIDecision Γ ↔ ∃ i c, c.UnilateralCheck i`, and the strict variant | "NP time" |
| Prop 24 / Prop 10 | omnilateral problem solvable in `O(m^l)` | `Fintype.card (Certificate Γ) ≤ m ^ l` with `m = Σᵢ|Aᵢ|`, `l = Σᵢ|Aʳᵉᵈᵢ|`; the decision is a search over that finite type | "solved in `O(m^l)`" |
| Prop 26 / Prop 10 | unilateral problem in `O(m^l)` | `Fintype.card (N × Certificate Γ) ≤ n · m ^ l` | same |
| Def 8 | subgraph isomorphism problem | `Graph.SubgraphIso a â φ`, `Graph.SubgraphIsoProblem a â` | — |
| Lemma 27 | subgraph isomorphism is NP-complete | cited, not carried | all of it |
| Lemma 28 | linear-time reduction, so the four SPI problems are NP-hard | `SubgraphIsoProblem a â ↔ (hardnessGame a â ε).SPIDecision`, and the same for the strict, unilateral and strict-unilateral problems; the instance size of the constructed game | "linear time", "NP-hard" (needs Lemma 27) |
| Thm 9 | the four problems are NP-complete, even for 2 players | the conjunction: membership certificates (Props 23/25, any `n`) and the hardness reduction (Lemma 28, `N = Two`) | "NP-complete" |

Theorem 9 therefore gets its `Paper node:` on the same declarations that carry
Propositions 23/25 and Lemma 28 (a `Paper node:` line may list several labels) plus a
wrapper theorem `spiDecision_theorem9` stating the conjunction over `Two`-player games,
so the trust surface has one place that says what "Theorem 9" means here.

## 2. Certificates (D.2.1, D.2.2)

```
structure Game.Certificate (Γ) :=            -- per-player injections Φᵢ : Aʳᵉᵈᵢ ↪ Aᵢ
  Φ : ∀ i, {x // x ∈ Γ.reduce.S i} ↪ {x // x ∈ Γ.S i}
```

As a `Fintype` it is the search space of Propositions 24/26.  `c.toFun i : 𝒜 i → 𝒜 i` is
`Φᵢ` on `Aʳᵉᵈᵢ` and the identity elsewhere; `c.map a = (Φ₁(a₁), …, Φₙ(aₙ))`;
`c.image i = (Γ.reduce.S i).map (c.Φ i)`.

* `c.ParetoImproving : ∀ a ∈ Γ.reduce.profiles, Γ.u a ≤ Γ.u (c.map a)` and
  `c.StrictlyParetoImproving` (some `a` with `Γ.u a < Γ.u (c.map a)`, `<` on `ℝⁿ`).
* `c.Nontrivial : ∃ i, c.image i ≠ Γ.reduce.S i` — Definition 5's non-triviality in the
  repaired reading (`dd:nontrivial`, erratum D13).  **The printed algorithm omits this
  check**: the identity injections always pass it, and the game they build is
  `reduce Γ` itself, which is not a non-trivial SPI under either reading of item 1.
  Recorded as erratum D17.
* `c.game : Game N 𝒜` — the paper's `Γˢ`: action sets `c.image i`, payoffs
  `uˢ(aˢ) = u(Φ⁻¹(aˢ))` on its profiles (the paper's `uˢ`; total elsewhere by `Γ.u`).
  It is an exact copy of `reduce Γ` along `c` (`Game.ExactCopy`), hence reduced.
* Proposition 23: `Γ.SPIDecision ↔ ∃ c, c.ParetoImproving ∧ c.Nontrivial`, and
  `Γ.StrictSPIDecision ↔ ∃ c, c.StrictlyParetoImproving ∧ c.Nontrivial`.  Proof: the
  certificate form `exists_paretoImproving_deriv_iff` (Lemma 22) in both directions;
  `→` restricts the isomorphism, `←` takes `Γˢ = c.game`.

Unilateral (D.2.2).  For a player `i`, `c.unilateralGame i` is the paper's
`Γˢ = ((A₋ᵢ, Φᵢ(Aʳᵉᵈᵢ)), (u₋ᵢ, uˢᵢ))`: player `i`'s action set is `c.image i`, every
other player keeps `Γ.S j`; `uˢᵢ = uᵢ ∘ Φ⁻¹` on `Φ(Aʳᵉᵈ)` and `uᵢ` elsewhere (the
paper's "arbitrary"), `uˢⱼ = uⱼ`.  The three checks:

1. `c.ParetoImproving` (resp. strict);
2. `c.Affine i : ∀ j ≠ i, ∃ λ > 0, ∃ κ, ∀ a ∈ Γ.reduce.profiles, Γ.u a j = λ * Γ.u (c.map a) j + κ`;
3. `c.ReducesToImage i : ∀ j, (c.unilateralGame i).reduce.S j = c.image i`.

Proposition 25: `Γ.UnilateralSPIDecision ↔ ∃ i c, c.ParetoImproving ∧ c.Nontrivial ∧
c.Affine i ∧ c.ReducesToImage i`, strict likewise.  The `←` direction builds the
isomorphism `reduce Γ ≅ reduce (c.unilateralGame i)` with scale `1` for `i` and the
`(λⱼ, κⱼ)` of check 2 for the others.  The `→` direction is where the paper says "we can
assume `Γˢ,ʳᵉᵈ` and `Γˢ` have the same action sets for Player `i`": the Lean proof does
not assume it but *transfers the elimination chain* `Γˢ →* reduce Γˢ` to the game with
player `i` cut down to `c.image i` (every step removes an action of some `j ≠ i`, whose
dominator survives because player `j`'s actions and payoffs are untouched, and
removing player `i`'s actions only shrinks the opponent profiles a dominator must beat;
steps removing player `i`'s own actions are skipped).  That transfer lemma
(`ElimStar.restrictPlayer`) is the one piece of new general reduction theory.

The fourth problem of Definition 5, the **strict unilateral** one, has had no carrier so
far; `Game.StrictUnilateralSPIDecision` is added to `Derivation.lean` with a
`Definition 5` node so that Lemma 28's "(strict) (unilateral)" can be stated four ways.

## 3. The search bound (Propositions 24, 26; Proposition 10)

`Fintype.card (Γ.Certificate) = ∏ᵢ mᵢ.descFactorial lᵢ ≤ ∏ᵢ mᵢ ^ lᵢ ≤ m ^ l`.  The
paper's `O(m^l)` is this cardinality together with "each certificate is checked in
polynomial time", which is the clause not rendered.  The unilateral search space is
`N × Certificate Γ`, of cardinality `≤ n · m ^ l`; the paper absorbs the factor `n` into
its `O`, and the docstring says so.  Proposition 10 is the main-text restatement of
Propositions 24 and 26 and shares their declarations.

## 4. Hardness (D.3): graphs, Table 9, Table 10, Lemma 28

*Graphs.*  A simple directed graph on `[n]` is `a : Fin n → Fin n → Bool` (the diagonal
is meaningless, as printed).  `SubgraphIso a â φ` for `φ : Fin n ↪ Fin n̂` is
`∀ j l, j ≠ l → a j l ≤ â (φ j) (φ l)` (Bool's `false ≤ true`); Definition 8 is
`∃ φ, SubgraphIso a â φ`.

*Actions.*  The paper's `[2n+2]` is carried as `Fin n ⊕ Fin n ⊕ Bool` — the block `[n]`,
the block `{n+1, …, 2n}` indexed by `j ↦ j+n`, and the two corner actions `2n+1`
(`false`) and `2n+2` (`true`).  This is a relabelling of `[2n+2]` that lets the payoff
formula be written by cases instead of by inequalities on `Fin (2n+2)`.
Player 1's actions in `Γᶜ` are `Fin n ⊕ Fin n ⊕ Bool ⊕ (Fin n̂ ⊕ Fin n̂ ⊕ Bool)` read as
`{T} × [2n+2] ⊔ {R} × [2n̂+2]`, and player 2's the same type read as `{D} × … ⊔ {P} × …`.
`N = Two`.

*Table 9 as a formula.*  `tableNine n a ε δ` takes a shift `δ ∈ {0, 1}` for player 1's
`4`/`3` entries so that `Γ̂` is the same definition with `δ = 1` ("5 instead of 4 … and 4
instead of 3").  The printed formula and Table 9 disagree at eight entries: the formula
gives player 1 `ε` in columns `2n+1, 2n+2` for rows `i ∈ [2n]`, and player 2 `ε` in rows
`2n+1, 2n+2` for columns `j ∈ [2n]`, where the table prints `0`.  **The disagreement is
material**: with the formula's `ε`, player 2 receives exactly `ε` against rows `2n̂+1`
and `2n̂+2` in *every* column of `Γ̂`, so no column of the unilateral candidate `Γˢ` is
ever strictly dominated once those rows are present, and the paper's step "`(P, 2n̂+1)`
and `(P, 2n̂+2)` strictly dominate `(P, i)`" (which it justifies by "inspecting Table 9")
fails; the unilateral half of Lemma 28's first claim is then false for the formula's
game.  The carrier follows the **table** (`0`), under which every step of the printed
proof checks.  Recorded as erratum D18.  The other entries agree.

*`ε`.*  The paper fixes `ε < 1/2n` for `Γ` and builds `Γ̂` "analogously".  Where the
constraint is actually used is in `Γ̂`: `5 + (n̂+i)ε < 6` for `i ≤ n̂`, so that
`(2n̂+1, 2n̂+1)` is the only outcome of `Γ̂` worth `6` to player 1.  The carrier takes
`ε` as a parameter with `0 < ε` and `ε * (2 * n̂) < 1`; the `Γ`-side bound is not needed
for any step of the formal proof and is not assumed.  Positivity is used for
`0 < ε` (the corner entries beat the table's `0`).  The "WLOG `n, n̂ ≥ 2`" is not needed
either — the two opponent moves the proof of item (c) wants are `(D, i)` and
`(D, n+i)`, which exist for every `i ∈ [n]`.

*Lemma 28 as an iff.*  `subgraphIsoProblem_iff_spiDecision : SubgraphIsoProblem a â ↔
(hardnessGame a â ε).SPIDecision` and the three variants.  The proof has the paper's two
halves, but half 2 is organised around the product structure of an isomorphism rather
than the printed items (a)–(d):

1. *Subgraph iso ⇒ strict unilateral SPI.*  `reduce Γᶜ` is the `Γ` block (every `R`
   action is strictly dominated by every `T` action: `−2 < uᵢ ≥ −1` against `D` and
   `max û₁ ≤ 6 < 10` against `P`; then every `P` action by every `D` action:
   `−10 < u₂ ≥ −1`; and the `Γ` block is reduced — each action is the unique best reply to
   some opponent action, except the corner `2n+2` (resp. `2n+1` for player 2), which is
   only *weakly* dominated).  `Ψ` maps `(T, i) ↦ (R, φ i)`, `(T, n+i) ↦ (R, n̂+φ i)`,
   `(T, 2n+b) ↦ (R, 2n̂+b)` and likewise for player 2.  `Γˢ` is the unilateral game with
   player 1 restricted to `Ψ₁(T)`; its reduction is the `Ψ`-block (the printed three
   cases), which is an exact copy of the `Γ` block along `Ψ` (player 2's payoffs are
   *equal*, player 1's are `u₁ ∘ Ψ⁻¹` by definition); `Ψ` is Pareto-improving under `uᶜ`
   (the printed case table; `a(i,j) ≤ â(φ i, φ j)` is the subgraph condition) and strict
   at `((T, 2n+1), (D, 1))` (`3 < 4`).
2. *Any SPI ⇒ subgraph iso.*  By the certificate form (Lemma 22) there is a
   Pareto-improving `ψ : reduce Γᶜ ≅ reduce Γˢ` whose action sets differ from the
   `Γ` block's.  Pareto-improvement forbids images in `T × P` (`u₂ = −10`) and `R × D`
   (`u₁ = −2`); since the image of a product map is a product, either
   `ψ(AΓ) ⊆ T × D` — then both action sets are permuted in place, contradicting
   non-triviality (this is where the repaired clause D13 does the work the paper's
   item (a) does with the `ε`-ladder) — or `ψ(AΓ) ⊆ R × P`.  In the latter case
   `ψ₁(2n+1) = 2n̂+1` and `ψ₂(2n+2) = 2n̂+2` (the unique outcomes worth `6`), so the
   `[2n]` blocks map into `[2n̂]`; a first-block `i` cannot map into the second block
   (it would lose against all but one of the two moves `(D, i)`, `(D, n+i)`), and
   `ψ₂(i) = ψ₁(i)` on `[n]` (else `2 ≤ 1`).  `φ := ψ₁|[n]` is then injective with
   `a(i,j) ≤ â(φ i, φ j)`.

*Instance size.*  `(hardnessGame a â ε).size = 2 * (2n+2) + 2 * (2n̂+2)`, the paper's
"linear increase in problem instance size" for its `m`; "linear time" is not rendered.

## 5. Files

* `Complexity.lean` — certificates, Propositions 23–26, Proposition 10, the transfer
  lemma, the Theorem 9 wrapper.
* `Hardness.lean` — graphs, Definition 8, `tableNine`, `hardnessGame`, Lemma 28.
* `Examples/ComplexityWitnesses.lean` — a Demand-Game certificate (Proposition 23
  two-sided through the existing yes/no instances), the transfer lemma exercised on the
  Complicated Temptation Game (Proposition 25's "yes"), and Lemma 28 on concrete graphs:
  the one-edge graph into the two-cycle (yes) and the two-cycle into the one-edge graph
  (no), each carried through to the `SPIDecision` verdict on the constructed game.

## 6. Rulings

* RULING 14 (proposed, proceeding under it): Lemma 27 is cited only — no axiom, no
  declaration — and Theorem 9's carrier is the conjunction of membership and reduction
  named above.  A named axiom would fail the axiom audit and would certify nothing.
* RULING 15 (proposed, proceeding under it): the hardness games follow Table 9 where it
  disagrees with the printed formula (erratum D18), because that is the reading under
  which the paper's own proof is correct, and the formula's reading falsifies the
  unilateral clause.
