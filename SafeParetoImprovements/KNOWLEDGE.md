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
| §2 equality of games | `Game.EqOn` | **never** Lean `=`; transports dominance and reducedness (`Game.EqOn.reduced_iff`, R2-F01) |
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
| §4.1 `Φ : M ⊸ N`, `Φ⁻¹`, `Ψ ∘ Φ`, `id_A`, `all` | Mathlib `SetRel`, `.inv`, `Φ ○ Ψ` (**diagrammatic**), `Game.partialId` (the typed identity; Lemma 2.1 uses it), `Game.allRel` | `Ψ ∘ Φ` (paper) = `Φ ○ Ψ` (Lean) |
| Def 3 `Γ ∼_Φ Γ'` | `Play.Corresponds` | |
| Lemma 2.1–2.7 | `Play.corresponds_id`, `Corresponds.inv`, `.trans`, `.mono_rel`, `corresponds_allRel`, `.ne_of_at_eq_empty`, `.ne_of_inv_at_eq_empty` | |
| §4.2 equivalence `R`, preorder `⪰` | `Play.BijEquiv`, `Play.Improves Γ₀` | `⪰` relative to a base game's payoffs |
| Def 4 | `Play.ParetoImprovingCorrespondence` | field `typed : Φ ⊆ Γ.profiles ×ˢ Γs.profiles` (R1-F05) |
| Thm 3 | `Play.isSPI_iff_exists_paretoImprovingCorrespondence` | |
| Assumption 1 / 2 | `Play.SatisfiesA1`, `Play.SatisfiesA2` | predicates; A2 existential over isomorphisms |
| Assumption 1's `Φ` | `Game.elimRel` | |
| Lemma 4 | `GameIso.paretoImproving_of_paretoImproving`, `…strictly…` | via the automorphism `Φ⁻¹ ∘ Ψ` (`GameIso.payoff_eq_of_self`) |
| "`Γ ∼_Φ Γ'` by Assumption 2" (lax use) | `Play.exists_paretoImproving_corresponds_of_assumption2` (+ `paretoImprovingCorrespondence_of_iso`) | `isSPI_of_assumption2` deleted (R1-F12: its hypotheses forced equal action sets) |
| §4.4.3 book representatives | `Book`, `Book.toPlay`, `Book.satisfiesA1/2`, `exists_play_satisfiesA1_satisfiesA2`, `exists_representatives_satisfiesA1_satisfiesA2`, `Book.prescribed`, `Book.varying` | `dd:book`; pages parametric; `Book.prescribed` plays a chosen outcome on every game with a given reduction (Prop 6 strict witness in `Examples/Witnesses.lean`); `Book.varying` (sample space `∀ i, 𝒜 i`) hits every surviving outcome — `exists_play_satisfiesA1_satisfiesA2_hits` is the generic A1 ∧ A2 ∧ positive-probability witness (R2-F18) |
| iterated elimination / "fully reduce" | `Game.Elim`, `Game.ElimStar`, `Game.reduce`, `Game.Reduced` | `reduce` canonical by `reduced_unique` (Church–Rosser) |
| Lemma 19 | `Game.isStrictlyDominated_erase` | |
| Lemma 20 | (absorbed) `Game.elim_diamond` | |
| Lemma 21 / 22 | `Game.Deriv.exists_normalForm` / `Game.exists_paretoImproving_normalForm` | `dd:derivation`; supporting: `Deriv.exists_iso`, `Deriv.normal`, `exists_paretoImproving_deriv_iff` (no labels). Lemma 21's wrapper has eight components; the `Step Γ₀ Γ.reduce Γ'.reduce ψ.rel` conjunct is the single Assumption 2 move (R2-F14). Lemma 22 does not tie `ψ` back to the input `Φ` — the paper only asks the new composite to be Pareto-improving |
| Def 5 | `Game.Step`, `Game.Deriv`; `Game.SPIDecision`, `StrictSPIDecision`, `UnilateralSPIDecision` (repaired, `dd:nontrivial`); `…Printed` variants (constant-true, D13) | soundness: `Play.isSPI_of_deriv`, `isUnilateralSPI_of_deriv`, `isStrictSPI_of_deriv` (no `[Nonempty]`, no separate subset-game hypothesis — the derivation supplies it). Yes-instances of all three repaired predicates: `Examples.demandGame_spiDecision`, `demandGame_strictSPIDecision`, `complicatedTemptation_unilateralSPIDecision` (R2-F05); `Step.iso` requires both endpoints `Reduced`, matching Assumption 2 as printed |
| Props 5, 6, 7, 8 | `Examples.prisonersDilemma_isStrictSPI`, `demandGame_isSPI`/`_isStrictSPI`, `temptation_isStrictSPI` + `temptation_isUnilateralSPI` (unilaterality is §4.5 prose, l. 1116), `complicatedTemptation_isUnilateralSPI` | non-vacuity witnesses in `Examples/Witnesses.lean` carry `SatisfiesA1 ⊤ ∧ SatisfiesA2 ⊤` inside their statements (R2-F11) |
| footnote 5 | `Play.isSPI_of_paretoDominant` | |
| App. A `Δ(Aᵢ)`, `uᵢ(σ)` | `Game.Mixed` (= EconCSLib `MixedStrategy Γ.toStrategic i`), `Game.expected` (= `expectedPayoff`) | independent mixtures; `Game.pureMixed`, `expected_pure` |
| App. A threat point `vᵢ`, `minimax(i, ·)` | `Game.threatPoint`, `Game.minimax` (with `Game.bestValue`) | both extrema by compactness (`isCompact_univ` on the product of standard simplices, `IsCompact.continuous_sSup`); minimiser chosen once per player; `threatPoint_le_of_bestResponse`: a pure Nash equilibrium certifies `vᵢ ≤ uᵢ(a)` |
| App. A program game, `U(c) = E[u(exec(c))]`, program equilibrium | `ProgramGame` (`Instr`, `exec`, `measurable_exec`), `ProgramGame.payoff`, `ProgramGame.toStrategic`, `ProgramGame.IsProgramEquilibrium` (= EconCSLib `IsNashEquilibrium`) | `dd:program-game`, `dd:exec-kernel`; `ProgramGame.Plays c f` is "`exec(c) = f`" |
| App. A instruction language, `Πᵢ(Γ′)` calls | `Prog` (`play`, `delegate`, `ifAllSame`), `Prog.execAt`, `Prog.programGame` (realization) | `dd:code-eq`; the differing-player choice is classical, not "first" |
| Algorithm 2 | `Prog.algorithm2` | erratum D15: punishes `j` with `minimax j i`, not the printed `minimax(i, j)` |
| Proposition 18 | `Prog.algorithm2_isProgramEquilibrium` (via `ProgramGame.isProgramEquilibrium_of_algorithm2`) | deviator's payoff `≤ vᵢ` (erratum D8) |
| Theorem 1 | `Prog.exists_programEquilibrium_plays` | for the program game `Prog.programGame`; threat-point guarantee as the hypothesis `∀ i, vᵢ ≤ E[uᵢ(Π(Γ₀))]` |
| (beyond the paper) default instruction, PI, information stage, FI | `ProgramGame.DefaultInstr`, `ProgramGame.ParticipationIndependent`, `ProgramGame.Policy`, `ProgramGame.ForeknowledgeIndependent`; `Prog.default`, `Prog.dove` | RULING 9, `dd:default-instr`; witnesses in `Examples/ProgramGameWitnesses.lean`; no theorems |
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
- **`dd:nontrivial`** — Definition 5's non-triviality clause is read as "the full reductions have different action sets" (`Γs.reduce.S ≠ Γ.reduce.S`), the reading Appendix D's hardness proof uses (the identity action map is the trivial case); the printed clause is constant-true (erratum D13) and is carried alongside as `…Printed` with its triviality theorem. Ruled 2026-09-12.
- **`dd:program-game`** — Appendix A's program game is an abstract interface (`ProgramGame`) with EconCSLib's `StrategicGame`/`IsNashEquilibrium` as the induced game and program equilibrium, and a concrete language `Prog` realized as an instance; Proposition 18 is proved once over the interface from Algorithm 2's two semantic properties (`Plays` = `Π(Γˢ)`, punishers play `minimax i ·`) and instantiated at the term `Prog.algorithm2`, which is where the paper node sits. Theorem 17 is not used.
- **`dd:exec-kernel`** — execution returns each player's *mixed* action given `Π`'s sample point `ω`, with the players independent given `ω`. This is the design note's "private seeds" collapsed to the distributions they induce: it is what erratum D8's independence needs, and it avoids all product-measure Fubini bookkeeping (payoffs are `∫ ω, expected (exec c ω) i`, a bounded measurable function). Deterministic outcomes are `pureMixed`.
- **`dd:code-eq`** — `Prog` is player-agnostic and code equality is classical (`open Classical` in `execAt`); when several players' code differs, the punished player is a fixed classical choice (the paper's loop takes the first in `1, …, n`; `N` is unordered). Immaterial for program equilibrium.
- **`dd:default-instr`** — a `ProgramGame.DefaultInstr` is a per-player instruction executing as `Π(Γ₀)`; in `Prog` it is `delegate Γ₀`. PI and FI are defined against it; they are research hooks (RULING 9), carry no `Paper node`, and come only with two-sided non-vacuity witnesses.
- **`dd:complexity`** (planned) — Theorem 9 / Prop 10 / Lemma 11 / Prop 12 carried as *qualified* nodes: mathematics exact, complexity-class and runtime clauses disclosed as not rendered.
- **EconCSLib** is a pinned lake dependency (`cef01c7`, Mathlib v4.30.0 upstream; builds against our v4.31.0). The paper library names EconCSLib only through `Game.toStrategic` and the dominance definitions.

## Intentional deviations from the paper

- **Filter-level statements** (Definitions 1, 3, 4; Lemma 2; Theorem 3; Assumptions 1–2; Propositions 5–8): the paper says "with certainty" = probability one; the Lean says "eventually in `L`" for any filter `L` (`[L.NeBot]` where strictness appears). Instantiating `L := ae μ` gives the printed statement verbatim (`Representatives.isSPI_iff` etc.). Ruled 2026-09-12.
- **Isomorphism is bijective with `λᵢ > 0`** (erratum D5): the printed §2 definition omits both; both are forced.
- **Lemma 4 is stated for `GameIso Γ Γ'` with Pareto-improvingness under `Γ`'s total `u`** — no subset-game hypothesis is needed because `u` is total (erratum D2 records that the paper needs one).
- **Lemma 20 has no carrier of its own**: its content (elimination steps commute) is `Game.elim_diamond`, which is what confluence needs; the paper's phrasing (reverse-then-forward reordering) is not separately stated.
- **Lemma 21 is carried qualitatively** (R1-F20/F21, codex-adjudicated): the labelled statements assert the existence of an isomorphism of the full reductions realized by a derivation of shape eliminations / one isomorphism move / reverse eliminations, exposed through the `ElimStar` witnesses, `Step.iso` and the composite identity — NOT "the same chain reorganized" (a `Prop`-valued derivation can still express restricted chains through `ElimStar`, so the earlier "not expressible" justification was over-broad and is retracted). The printed length bound `m ≤ k` is not rendered and is false as printed (erratum D14). The normal form's composite is *contained in* the original composite on the reduced outcomes, never equal to it (a `refl` derivation from a non-reduced game has the partial identity on all outcomes).
- **Definition 5's non-triviality clause is repaired** (R1-F18, ruled 2026-09-12, erratum D13): the carrier requires the reduced *action sets* to differ (`Γs.reduce.S ≠ Γ.reduce.S`, `dd:nontrivial`); the printed clause (reductions not `EqOn`) is constant-true under payoff shifts and is carried alongside as `…Printed` with its triviality theorem.
- **`Play` is a larger class than the paper's `Π`** (R1-F01, refuted by cross-examination): it need not respect `Game.EqOn`, so a hand-built play can distinguish two Lean games that are the same paper game. Every paper node quantifies universally over `X : Play`, so this only strengthens them (same pattern as `dd:certainty`), and Assumption 2 forbids the phenomenon: any `GameIso` between `EqOn`-equal games preserves payoffs, so under A2 there is no strict SPI between `EqOn`-equal reduced games (library lemma). The book witness is `EqOn`-invariant up to payoffs, not outcomes (`Game.chosenIso` is chosen per Lean game). Do NOT add a `play_eqOn` field.
- **Proposition 6's strictness clause** is proved for *whichever* isomorphism Assumption 2 supplies (all of Table 2's outcomes are worth more than `−3` to player 1), not by identifying the isomorphism.
- **Assumption 2's R1-F01 corollary is about *reduced* `EqOn`-equal presentations only** (R2-F02/F09): Assumption 2 quantifies over games without strictly dominated actions, so it says nothing about a non-reduced `EqOn`-equal pair, on which a `Play` family may still exhibit the phenomenon. `GameIso.payoff_eq_of_eqOn` itself is unconditional.
- **`dd:nontrivial` is narrower than Appendix D's "the identity action map is trivial"** — it also excludes a Pareto-improving *permutation* of the same reduced action set. Nothing is lost (R2, lenses A and C, cleared): such a permutation is a bijection of the finite reduced profile set, so the payoff sum is invariant and pointwise weak improvement forces equality; for the strict problem the two readings coincide.
- **`Representatives.measurableSet_fiber` is exercised only trivially** (R2-F10): every sample space the development instantiates (`Unit`, the finite profile space of `Book.varying`) is discrete, so the field is discharged by `trivial`. Disclosed at `exists_representatives_satisfiesA1_satisfiesA2` and `Book.toRepresentatives`; a non-discrete witness would be cosmetic until a probabilistic result needs it.

- **Definition 4's carrier is typed** (R1-F05): `Play.ParetoImprovingCorrespondence` carries `typed : Φ ⊆ Γ.profiles ×ˢ Γs.profiles`; Theorem 3 quantifies over the structure alone.
- **Lemma 2.1 uses the typed identity** `Game.partialId` (the paper's `id_A`), and Lemma 2.4's hypothesis is containment at outcomes of `Γ` only (R1-F06/F07/F35).
- **`Game.ParetoOptimalIn` is a one-liner over Mathlib's `Pi` order**, not a redefinition of EconCSLib's fair-division `IsParetoOptimal` (R1-F02, refuted); it becomes load-bearing in §5.

## Disclosures (residual modeling substitutions)

None.

## Paper errata

See `notes/paper-errata.md` (D1–D14). Statement-level: D1, D2, D5, D8, D10, D12, D13. D10 ruled (Definition 7 reads "strict"); D12 deferred with Theorem 15. Erratum D2 covers two separate defects (Definition 4's `Γ ∼_Φ Γ'` for `Γ ∼_Φ Γˢ`, and Lemma 4's "Pareto-improving" on non-subset targets).

## Pitfalls

Round-1 audit clearances (checked, do not re-raise): Mathlib `SetRel` composition is diagrammatic (`Data/Rel.lean`), so `Corresponds.trans` concluding `Φ ○ Ψ` is the paper's `Ψ ∘ Φ`; EconCSLib `StrictlyDominates G i s s'` means `s` dominates `s'`, and `IsStrictlyDominated i a := ∃ a', StrictlyDominates i a' a` puts the dominator first; `Game.Elim`/`ElimStar`/`reduce` are not duplicates of EconCSLib's simultaneous-round `Survives` (one action at a time, shrinking the game, with confluence — EconCSLib has neither); the Prisoner's Dilemma in `Examples/` is Table 3, not EconCSLib's example (different payoffs); all 48 table cells of Tables 1–6 were verified executably; `GameIso.payoff_eq_of_self` needs `[Fintype N]` genuinely (surjectivity direction of the max/min argument); `Game.chosenIso` is well-defined despite `Classical.choice` (`Nonempty` is a `Prop`); `Lean.collectAxioms` traverses inductive constructors, so inventorying `Game.Step`/`Game.Deriv` is real coverage; `Representatives.isStrictSPI_iff` is `frequently_ae_iff`, not `Iff.rfl`; `hsub` in Theorem 3 is load-bearing in the ⇐ direction; `Play.IsStrictSPI` is `False` at `L = ⊥` while `IsSPI` is `True` — endpoints concluding strictness from non-frequently hypotheses carry `[L.NeBot]`, Proposition 6's strict clause gets it from its `∃ᶠ` hypothesis.

- `GameIso.affine` is oriented *source payoff = scale · image payoff + shift*; hence `ctIso.shift .two = -1` for Table 5's "player 2's utilities equal up to the constant 1". Check the direction before "fixing" a sign.
- A `GameIso Γ Γ'` together with `Γ'.IsSubsetGameOf Γ` forces equal action sets (bijection ⇒ equal cardinality ⇒ equality): never state an Assumption-2 helper with both hypotheses on one pair; the paper's isomorphisms relate the two *full reductions*.
- A subset game's payoffs are unconstrained and `EqOn` compares payoffs: any predicate combining "subset game" with "reductions not `EqOn`" is satisfied by a payoff shift (this is erratum D13).
- Off-profile payoffs of the SPI subset games are `0` (`spiPayoff`, `ctSPIPayoff₁`); unobservable by construction (`Play.mem`, `IsSPI` under the original `u`, `Unilateral` on the subset game's profiles) — covered by `dd:total-utility`.
- The paper prints the §4.5 examples as "Proposition (Example) n"; the registered node ids are the bare `Proposition n` (`scripts/paper_nodes.py` normalizes) — the labels are correct though not verbatim substrings.
- Building a `GameIso` inside a tactic proof with `have` erases its body (it is data); use `let`/a top-level `def` so `ψ.map a` reduces.
- The mechanical Tier-2 set for this paper (`SurfaceProbe.lean`'s `#surface_types` over SPI-INVENTORY) is `Game`, `GameIso`, `Play`, `Play.ParetoImprovingCorrespondence`; freezes are maintained by hand in `AxiomAudit.lean`.
- Prescribed-page books: `page q ω := if h : T.cls = q then (T.chosenIso q h).map a else …` plays `a` on every game whose full reduction is `T` (`GameIso.symm_map_map` + proof irrelevance on the positive branch) — the witness pattern for Proposition 6's strictness clause and Proposition 16.

- `Π` is Lean's pi-binder token: name the representatives model `R`, never `Π`.
- Superscript identifiers (`Γˢ`, `aˢ`) are not valid Lean identifiers; use `Γs`.
- `SetRel` is `Set (α × β)`; membership hypotheses come as `(a, b).1 ∈ …` — `dsimp only at h` or the `mem_*` iff lemmas before `subst`/`rfl` patterns.
- `Function.update` at a different player only simplifies with an explicit `Function.update_of_ne (show j ≠ i by decide)` in the simp set.
- In `cases s with | @elim Γ i ã …`, names for constructor arguments already determined by unification are silently dropped; refer to the outer binder instead.
- `norm_num [game, …]` unfolds the game *inside* `X.play game ω` and breaks rewriting with play hypotheses; use a `u_apply` lemma and `simp only [u_apply, h…]` first.
- Lake: the repo does not `require` Mathlib directly, so `lake update <newdep>` re-resolves Mathlib from the new dependency's manifest and downgrades everything. Add manifest entries by hand.
- The worktree-isolation hook refuses `lake`/`git` invocations that mention the main checkout, shell variables, heredocs containing the word `git`, or `.git` paths; run scripts from files with `lake env bash /abs/path.sh`. It also refuses heredocs whose body contains `{`, `~`, a bare `<`, or double quotes — write files with the Write tool and run them by absolute path.

Round-2 audit clearances and traps (checked, do not re-raise):

- **Non-vacuity witnesses must carry the assumption clauses in their statements** (R2-F11): a bare `∃ X, <conclusion>` is provable by a hand-built play family (`play G _ i := if a₀ ∈ G.S i then a₀ else a₁`) that violates Assumption 1, so it witnesses nothing about the proposition's hypotheses. Reusable adversarial probe.
- **The D13 payoff-shift witnesses (`Game.shiftReduce`, `Game.bumpPayoff`) never serve the repaired Definition 5**: both are `Reduced` with `reduce.S` unchanged, so they fail `Γs.reduce.S ≠ Γ.reduce.S` by construction. A yes-instance must change the action labels of the reduction (`demandIso`, `ctIso` do).
- **Deterministic books cannot witness positive-probability side conditions**: `Book.const`/`Book.prescribed` pages ignore `ω`, and on `Ω = Unit` no play family hits two distinct outcomes. `Play.isStrictSPI_of_deriv`'s `hpos` (every surviving outcome with positive probability) is witnessed by `Book.varying` on `Ω := ∀ i, 𝒜 i` (`exists_play_satisfiesA1_satisfiesA2_hits`); `hpos` already implies `L.NeBot` since `reduce.profiles` is nonempty.
- `[L.NeBot]` on an endpoint whose conclusion *negates* strictness is removable (`Play.IsStrictSPI` is `False` at `⊥`): `rcases L.eq_or_neBot with rfl | hne`, `⊥` branch by `simp` on the `∃ᶠ`. The round-1 note about carrying `[L.NeBot]` applies to *positive* strictness conclusions only.
- `[DecidableEq N]` is spurious on `Fintype N`-indexed results unless the *statement* mentions `profilesFinset`, `erase`, `reduce`, `Reduced` or dominance; inside proofs `classical` supplies it (R2-F08). Removing an instance binder never breaks call sites.
- `GameIso.symm` bakes its `Nonempty` instance in from the game; no downstream hazard (`Nonempty` is a `Prop`, `Function.invFunOn` built from any instance is defeq). Do not re-add `[∀ i, Nonempty (𝒜 i)]` to callers; `Game.nonempty_universe` derives it wherever needed.
- `Game.reduce_of_reduced h : G.reduce = G` rewrites the whole game; a goal about `.S` then usually needs a trailing `rfl`.
- `Book.prescribed_play` needs `Γ.reduce = T` in Lean's `=`, not `EqOn` (elimination keeps `u` literally); a game only `EqOn`-equal to one reducing to `T` is played through a possibly different `chosenIso`.
- `Game.Deriv.normalRel ψ` (namespace `Game.Deriv`) with `mem_normalRel` is the practical `Φ` for concrete Definition 5 instances; `GameIso.cast`/`cast_map` move an example's isomorphism between `reducedGame` and `Γ.reduce`. `Play.isStrictSPI_of_deriv`'s player index is implicit — pass `(i := …)` when `hstrict` is a `by` block.
- `Examples/Witnesses.lean` imports `SafeParetoImprovements.Derivation` (added R2); missing-import errors there read like missing declarations ("Invalid field cast").
- `Play.Improves` uses *global* monotonicity while `ParetoImprovingCorrespondence.improving` is typed; not drift — `Φ` is existential in `Improves` and the global form is what `Improves.trans` needs. Do not harmonize.
- `hsub` in Theorem 3 cannot be dropped even with `typed`: at `L = ⊥`, `Φ = ∅` inhabits the right-hand side for any pair of games.
- `Game.Unilateral` (`∃ i, ∀ j ≠ i, …`) permits the degenerate all-agree case exactly as the paper's "all but one" does; `Game.ParetoOptimalIn` over Mathlib's `Pi` strict order is the paper's "strictly Pareto-dominates"; `Game.Reduced` quantifies over the universe type harmlessly (domination entails membership).
- `MeasurableSpace Unit` (and every discrete space) is `⊤`: `MeasurableSet s` closes by `trivial`, and `ae (dirac ())` on `Unit` is `⊤`, so witnesses at `L = ⊤` are the paper's probability-one instance.
- `scripts/check-safe-pareto-improvements-nodes.py` does not check that inventory names resolve — only `#assert_axioms_clean` does, at build time. Eight declarations cite `Definition 5` (legal; printed vs repaired carriers are distinguished only in docstrings).
- `Reduction.lean` was in no round-2 shard although `Book.satisfiesA1/A2` rest on `reduce_erase`/`reduce_of_reduced`; shard it explicitly in the next round.

Tranche E (program games) traps:

- `MixedStrategy G i` is `stdSimplex ℝ (G.strategy i)`, a subtype of `↥(Γ.S i) → ℝ`; `Nonempty (Γ.S i)` (from `Γ.nonempty`) gives `Nonempty` and `CompactSpace` instances for free, so `isCompact_univ` on `∀ j, Γ.Mixed j` is available without any construction. `Fintype.prod_sum` turns `∑ₛ ∏ⱼ σⱼ(sⱼ)` into `∏ⱼ ∑ σⱼ = 1`.
- Structure fields typed `∀ i, P.Instr i` do not unify syntactically with `N → Prog Γ₀` even when `P.Instr _ = Prog Γ₀` definitionally: `rw` with a lemma about `Function.update c j p` fails against the goal's `Function.update (c : ∀ a, P.Instr a) j p`. Restate the goal with `show` at the plain type first (the two are defeq), then rewrite.
- `Prog.noConfusion this` on `this : default Γ₀ = ifAllSame …` does not elaborate (the left side is a definition, not a constructor application); `cases this` after unfolding the definitions closes such goals.
- `variable (Γ₀) in` must precede the docstring of the declaration it modifies, not sit between docstring and `def`.
- Algorithm 2's failure of participation independence is stated *conditionally* (`Prog.not_participationIndependent_algorithm2`: the punishment `minimax j i` differs from the default play at some `ω`); no instance is computed, because in the Prisoner's Dilemma the minimax punishment *is* Defect, the default, so Algorithm 2 there happens to be participation independent. A game with a strictly mixed minimax profile would witness the hypothesis; computing `Game.minimax` on a concrete game is open work.
- `Representatives.measurable_comp_play`/`integrable_comp_play`: any real function of `Π(Γ)` is measurable and integrable (finite range on measurable fibers); use these rather than re-proving measurability of `u ∘ play`.
