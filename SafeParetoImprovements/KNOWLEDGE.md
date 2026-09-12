# Formalization Knowledge — Safe Pareto Improvements for Delegated Game Playing (Oesterheld & Conitzer 2022), branch `spi-delegated-games`

Permanent, curated facts about this formalization. Committed with the code; read by every
harness agent before working. Add an entry only if a future fresh-context agent would act
differently for knowing it. Cross-reference finding IDs (RN-Fxx) where an entry originated
from an audit. The scoping note (`notes/scoping.md`) and the errata file
(`notes/paper-errata.md`) hold the longer rationale; this file is the operational digest.

## Correspondence table

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| §2 game `(A, u)`, `A = A₁ × ⋯ × Aₙ` | `Game N 𝒜` (`S i : Finset (𝒜 i)`, `u : (∀ i, 𝒜 i) → N → ℝ`) | over a fixed per-player universe `𝒜` (`dd:universe`); `u` total (`dd:total-utility`) |
| §2 outcomes `A` | `Game.profiles`, `Game.profilesFinset` | |
| §2 equality of games | `Game.EqOn` | **never** Lean `=` |
| §2 subset game `A'ᵢ ⊆ Aᵢ` | `Game.IsSubsetGameOf Γ' Γ` | payoffs unconstrained |
| §2 `(A₋ᵢ, Aᵢ − {ãᵢ}, u\|…)` | `Game.erase Γ i ã h` | `h` = nonemptiness of the remainder |
| §2 strict dominance | `Game.StrictlyDominates`, `Game.IsStrictlyDominated` | EconCSLib's notion on `Game.toStrategic`; `strictlyDominates_iff` is the paper's sentence |
| §2 Pareto improvement `y ≥ y'` / strict | Mathlib `≤` / `<` on `N → ℝ` | not re-defined |
| §2 Pareto-optimal relative to `S` | `Game.ParetoOptimalIn` | |
| §2 game isomorphism | `GameIso Γ Γ'`, `Game.Isomorphic` | bijections + `λᵢ > 0` (`dd:iso`, erratum D5) |
| §3 `Π(Γ)` | `Play.play Γ ω`; `Representatives.play` | one sample space for all games (`dd:representatives`) |
| §3 "with certainty" / "with positive probability" | `∀ᶠ ω in L` / `∃ᶠ ω in L` for a filter `L` | `dd:certainty`; the paper's instance is `L = ae μ` (`Representatives.certainty`) |
| Def 1 SPI, strict SPI | `Play.IsSPI`, `Play.IsStrictSPI` | erratum D1 in the strictness clause |
| Def 2 unilateral | `Game.Unilateral`, `Play.IsUnilateralSPI` | |
| §4.1 `Φ : M ⊸ N`, `Φ⁻¹`, `Ψ ∘ Φ`, `id`, `all` | Mathlib `SetRel`, `.inv`, `Φ ○ Ψ` (**diagrammatic**), `SetRel.id` / `Game.partialId`, `Game.allRel` | `Ψ ∘ Φ` (paper) = `Φ ○ Ψ` (Lean) |
| Def 3 `Γ ∼_Φ Γ'` | `Play.Corresponds` | |
| Lemma 2.1–2.7 | `Play.corresponds_id`, `Corresponds.inv`, `.trans`, `.mono_rel`, `corresponds_allRel`, `.ne_of_at_eq_empty`, `.ne_of_inv_at_eq_empty` | |
| §4.2 equivalence `R`, preorder `⪰` | `Play.BijEquiv`, `Play.Improves Γ₀` | `⪰` relative to a base game's payoffs |
| Def 4 | `Play.ParetoImprovingCorrespondence` | typed on the two profile sets |
| Thm 3 | `Play.isSPI_iff_exists_paretoImprovingCorrespondence` | |
| Assumption 1 / 2 | `Play.SatisfiesA1`, `Play.SatisfiesA2` | predicates; A2 existential over isomorphisms |
| Assumption 1's `Φ` | `Game.elimRel` | |
| Lemma 4 | `GameIso.paretoImproving_of_paretoImproving`, `…strictly…` | via the automorphism `Φ⁻¹ ∘ Ψ` (`GameIso.payoff_eq_of_self`) |
| "`Γ ∼_Φ Γ'` by Assumption 2" (lax use) | `Play.exists_paretoImproving_corresponds_of_assumption2` | |
| §4.4.3 book representatives | `Book`, `Book.toPlay`, `Book.satisfiesA1/2`, `exists_play_satisfiesA1_satisfiesA2` | `dd:book`; pages parametric |
| iterated elimination / "fully reduce" | `Game.Elim`, `Game.ElimStar`, `Game.reduce`, `Game.Reduced` | `reduce` canonical by `reduced_unique` (Church–Rosser) |
| Lemma 19 | `Game.isStrictlyDominated_erase` | |
| Lemma 20 | (absorbed) `Game.elim_diamond` | |
| Lemma 21 / 22 | `Game.Deriv.exists_iso`, `Game.Deriv.normal`, `Game.exists_paretoImproving_deriv_iff` | `dd:derivation` |
| Def 5 | `Game.Step`, `Game.Deriv`, `Game.SPIDecision`, `Game.StrictSPIDecision`, `Game.UnilateralSPIDecision` | |
| Props 5, 6, 7, 8 | `Examples.prisonersDilemma_isStrictSPI`, `demandGame_isSPI`/`_isStrictSPI`, `temptation_isStrictSPI`, `complicatedTemptation_isUnilateralSPI` | |
| footnote 5 | `Play.isSPI_of_paretoDominant` | |
| `supp Π(Γ)` (§5) | `Representatives.support` | |

## Design decisions

Full rationale in `notes/scoping.md` §3; rulings by Anson 2026-09-12 in its §8.

- **`dd:universe`** — every game lives over one fixed per-player action universe `𝒜 : N → Type`; Assumptions 1–2 quantify over games over that universe. Forced in any case by universe levels; makes subset games literal inclusions and Assumption 1's disjointness automatic. §5's fresh tokens will be a *room* hypothesis on the universe.
- **`dd:total-utility`** — `u` is total on universe profiles; the paper's game equality is `Game.EqOn` (Definition 2 already equates payoff functions on different domains). Lean `=` on `Game` is never the paper's equality; `reduced_unique` is the one place Lean `=` is proved, and it holds because elimination chains keep `u` literally.
- **`dd:certainty`** — §3–§4 stated for an arbitrary certainty filter; paper nodes at that level are `strengthened`. `Representatives.lean` realizes the paper's instance (`ae μ`, non-degenerate, `∀ᵐ`, `μ {…} ≠ 0`) by definitional iffs, not by second theorems. Assumptions are read "for every game, with certainty" (the weaker quantifier order).
- **`dd:representatives`** — `Play` = random solver with the measure left off (membership everywhere); `Representatives` adds a probability measure and measurable fibers only. No rationality built in.
- **`dd:iso`** — per-player bijections, `λᵢ > 0`, constants as data (`scale`, `shift`) so composition/inverse compute.
- **`dd:book`** — the §4.4.3 consistency argument is a theorem: quotient of games by isomorphism, `Quotient.out` representatives, `Classical.choice` translations, pages parametric. Holds at every sample point.
- **`dd:derivation`** — Definition 5 is a Prop-valued derivation system inside a root game; the empty derivation records the typed identity `Game.partialId`. Soundness is for the SPI *conclusion* (via Lemma 4), never for the recorded correspondence.
- **`dd:complexity`** (planned) — Theorem 9 / Prop 10 / Lemma 11 / Prop 12 carried as *qualified* nodes: mathematics exact, complexity-class and runtime clauses disclosed as not rendered.
- **EconCSLib** is a pinned lake dependency (`cef01c7`, Mathlib v4.30.0 upstream; builds against our v4.31.0). The paper library names EconCSLib only through `Game.toStrategic` and the dominance definitions.

## Intentional deviations from the paper

- **Filter-level statements** (Definitions 1, 3, 4; Lemma 2; Theorem 3; Assumptions 1–2; Propositions 5–8): the paper says "with certainty" = probability one; the Lean says "eventually in `L`" for any filter `L` (`[L.NeBot]` where strictness appears). Instantiating `L := ae μ` gives the printed statement verbatim (`Representatives.isSPI_iff` etc.). Ruled 2026-09-12.
- **Isomorphism is bijective with `λᵢ > 0`** (erratum D5): the printed §2 definition omits both; both are forced.
- **Lemma 4 is stated for `GameIso Γ Γ'` with Pareto-improvingness under `Γ`'s total `u`** — no subset-game hypothesis is needed because `u` is total (erratum D2 records that the paper needs one).
- **Lemma 20 has no carrier of its own**: its content (elimination steps commute) is `Game.elim_diamond`, which is what confluence needs; the paper's phrasing (reverse-then-forward reordering) is not separately stated.
- **Lemma 21's normal form is stated as the pair `Deriv.exists_iso` + `Deriv.normal`** rather than as a statement about reordering a given chain: derivations are `Prop`-valued, so "the same chain reorganized" is not expressible; what is expressible and what the paper uses is that the same endpoints admit a normal-form derivation whose composite is the graph of an isomorphism of the full reductions.
- **Proposition 6's strictness clause** is proved for *whichever* isomorphism Assumption 2 supplies (all of Table 2's outcomes are worth more than `−3` to player 1), not by identifying the isomorphism.

## Disclosures (residual modeling substitutions)

None.

## Paper errata

See `notes/paper-errata.md` (D1–D12). Statement-level: D1, D2, D5, D8, D10, D12. Rulings pending on D10 (Definition 7's "strict") and D12 (Theorem 15's projections).

## Pitfalls

- `Π` is Lean's pi-binder token: name the representatives model `R`, never `Π`.
- Superscript identifiers (`Γˢ`, `aˢ`) are not valid Lean identifiers; use `Γs`.
- `SetRel` is `Set (α × β)`; membership hypotheses come as `(a, b).1 ∈ …` — `dsimp only at h` or the `mem_*` iff lemmas before `subst`/`rfl` patterns.
- `Function.update` at a different player only simplifies with an explicit `Function.update_of_ne (show j ≠ i by decide)` in the simp set.
- In `cases s with | @elim Γ i ã …`, names for constructor arguments already determined by unification are silently dropped; refer to the outer binder instead.
- `norm_num [game, …]` unfolds the game *inside* `X.play game ω` and breaks rewriting with play hypotheses; use a `u_apply` lemma and `simp only [u_apply, h…]` first.
- Lake: the repo does not `require` Mathlib directly, so `lake update <newdep>` re-resolves Mathlib from the new dependency's manifest and downgrades everything. Add manifest entries by hand.
- The worktree-isolation hook refuses `lake`/`git` invocations that mention the main checkout, shell variables, heredocs containing the word `git`, or `.git` paths; run scripts from files with `lake env bash /abs/path.sh`.
