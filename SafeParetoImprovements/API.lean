import SafeParetoImprovements.Game
import SafeParetoImprovements.Play
import SafeParetoImprovements.Correspondence
import SafeParetoImprovements.Ordering
import SafeParetoImprovements.Isomorphism
import SafeParetoImprovements.Assumptions
import SafeParetoImprovements.Reduction
import SafeParetoImprovements.Representatives
import SafeParetoImprovements.Book
import SafeParetoImprovements.Derivation
import SafeParetoImprovements.TwoPlayer
import SafeParetoImprovements.ProgramGame
import SafeParetoImprovements.Instruction
import SafeParetoImprovements.Independence
import SafeParetoImprovements.Coordination
import SafeParetoImprovements.PerfectCoordination
import SafeParetoImprovements.Polytope
import SafeParetoImprovements.Characterization
import SafeParetoImprovements.Complexity
import SafeParetoImprovements.Hardness

/-!
# Safe Pareto Improvements consumer API

The supported downstream import for research on safe Pareto improvements, delegated
game playing and program equilibria is:

```lean
import SafeParetoImprovements.API
```

**Status.**  §2–§6 and the appendix proofs of Oesterheld & Conitzer 2022 are formalized
with two boundaries the README records: **Theorem 15** (the two-player geometric
characterization of the safely achievable payoffs) is *deferred* by ruling — its printed
statement projects onto a Pareto frontier where the projection need not exist (erratum
D12) — and the **complexity nodes** (Theorem 9, Proposition 10, Lemma 11, Propositions 12
and 23–26, Lemma 28) are carried as *qualified* nodes: their mathematics is rendered
exactly and their complexity-class / running-time clauses are disclosed as not rendered
(`dd:complexity`).  Lemma 27 (Cook) and Theorem 17 (Tennenholtz) are cited external
results with no carrier.  `SafeParetoImprovements/README.md` is the trust surface;
`SafeParetoImprovements.lean` carries the `dd:` glossary of modeling decisions; this file
is the map from the paper's vocabulary to the supported Lean names.

The worked examples (`SafeParetoImprovements/Examples/`) are *not* imported here: they are
witnesses, not interface.  Import `SafeParetoImprovements.Examples.Witnesses`,
`….Examples.ProgramGameWitnesses`, `….Examples.TokenWitnesses` or
`….Examples.ComplexityWitnesses` when a concrete game of the paper is wanted.

## Games (§2)

Everything lives in the `SafeParetoImprovements` namespace.  A game is
`Game N 𝒜`: a finite nonempty action set `S i : Finset (𝒜 i)` per player and a payoff
function `u : (∀ i, 𝒜 i) → N → ℝ` that is *total on the universe* (`dd:universe`,
`dd:total-utility`) — only its values on `Γ.profiles` (`= {a | ∀ i, a i ∈ Γ.S i}`, also
`Γ.profilesFinset`) are meaningful, and the paper's equality of games is `Game.EqOn`, not
`=`.  Subset games are `Game.IsSubsetGameOf`; `Game.restrict` and `Game.erase` build them;
unilateral subset games (Definition 2) are `Game.Unilateral Γ Γs`.  Strict dominance is
EconCSLib's through the bridge `Game.toStrategic`, read back as the paper's sentence by
`Game.strictlyDominates_iff` (`Game.StrictlyDominates`, `Game.IsStrictlyDominated`,
`Game.Reduced`).  For two-player tables use `Two`, `Two.pair`, `Two.strictlyDominates_one_iff`
/ `_two_iff`, `Two.not_isStrictlyDominated_{one,two}_of_bestResponse` and `Two.reduced_iff`
(`SafeParetoImprovements/TwoPlayer.lean`).

Game isomorphisms (`dd:iso`, erratum D5) are `GameIso Γ Γ'`: per-player maps `toFun` that
are bijections `Γ.S i → Γ'.S i` (`bijOn`) with strictly positive scales and shifts
(`affine`); `GameIso.map`, `.symm`, `.trans`, `.refl`, `Game.Isomorphic`, and the exact
relabelings `Game.ExactCopy` (scale `1`, shift `0`).  `GameIso.ParetoImproving` and
`StrictlyParetoImproving` are Lemma 4's hypotheses.

## Representatives and SPIs (§3)

The representatives are a **play family** `Play N 𝒜 Ω` (`play : Game → Ω → outcome`,
always an outcome of the game) and a **certainty filter** `L : Filter Ω`
(`dd:certainty`): `Play.IsSPI X L Γ Γs`, `IsStrictSPI`, `IsUnilateralSPI` are Definitions
1–2 with "with certainty" read as `∀ᶠ ω in L` and "with positive probability" as
`∃ᶠ ω in L`.  The probabilistic model of the paper is `Representatives N 𝒜` — a
probability space with a play family — whose certainty filter is `R.certainty = ae R.μ`;
`Representatives.isSPI_iff`, `isStrictSPI_iff`, `corresponds_iff` unfold the filter forms
to the printed probability statements (`dd:representatives`).  `R.support Γ` is
`supp Π(Γ)`; `R.fiber Γ a` the event `{Π(Γ) = a}`.

## Outcome correspondence and Theorem 3 (§4.1–§4.3)

`Play.Corresponds X L Γ Γ' Φ` is Definition 3 for a relation `Φ : SetRel outcome outcome`
(Mathlib's `SetRel`, composed diagrammatically: `Φ ○ Ψ` is the paper's `Ψ ∘ Φ`), with
Lemma 2 as `Play.corresponds_id`, `Corresponds.inv`, `.trans`, `.mono_rel`,
`corresponds_allRel`, `.ne_of_at_eq_empty`, `.ne_of_inv_at_eq_empty`.  A Pareto-improving
correspondence (Definition 4) is the structure `Play.ParetoImprovingCorrespondence`, and
**Theorem 3** is `Play.isSPI_iff_exists_paretoImprovingCorrespondence`.  The §4.2
relations obtained by quantifying the correspondence away are in `Ordering.lean`.

## Assumptions, reduction, derivations (§4.4–§4.6)

`Play.SatisfiesA1 X L` and `SatisfiesA2` are Assumptions 1–2.  Their joint satisfiability
is a theorem: any **book** `Book N 𝒜 Ω` (a page per isomorphism class of reduced games,
`dd:book`) yields `Book.toPlay` with `Book.satisfiesA1`/`satisfiesA2`, and the book's play
is a function of the paper's game (`Play.RespectsEqOn`, `Book.toPlay_respectsEqOn`: it is
routed through the canonical presentation `Game.canon`, which zeroes payoffs off the
profiles and is shared by `EqOn`-equal games);
`Book.const`, `Book.prescribed`, `Book.prescribedRandom`, `Book.varying` are the ready-made
books, `Book.toRepresentatives` lifts a measurable book to `Representatives`, and
`exists_representatives_satisfiesA1_satisfiesA2` is the existence statement.

Iterated elimination: `Game.Elim`, `Game.ElimStar` (single/iterated steps), the canonical
full reduction `Game.reduce` with `reduce_reduced`, `reduce_of_reduced`, `elimStar_reduce`,
`reduce_eq_of_reduced_of_elimStar`, path independence `reduced_unique` (Lemma 19 is
`isStrictlyDominated_erase`), and the bulk tools `Game.elimStar_of_dominated` (eliminate a
whole dominated set) and `Game.ElimStar.transfer` (replay a chain after cutting one player's
actions).  Reduction respects the paper's equality of games (`Game.EqOn.reduce_eqOn`,
`EqOn.reduce_eq_withPayoffs`) and transports along isomorphisms
(`Game.Reduced.of_iso`; `GameIso.imageGame`, `GameIso.reduce_eq_imageGame`,
`GameIso.restrictReduce`: `reduce Γ' = Φ(reduce Γ)`).

Definition 5's derivation system: `Game.Step`, `Game.Deriv Γ₀ Γ Γ' Φ` (Assumption 1
forward and backward, Assumption 2), `Game.ParetoImprovingFor`, the decision problems
`Game.SPIDecision`, `StrictSPIDecision`, `UnilateralSPIDecision`,
`StrictUnilateralSPIDecision` (non-triviality repaired, `dd:nontrivial`, erratum D13; the
printed forms `…Printed` are kept with their triviality theorems), Lemmas 21–22
(`Game.Deriv.exists_normalForm`, `Game.exists_paretoImproving_normalForm`), the certificate
forms `Game.exists_paretoImproving_deriv_iff` / `exists_strictParetoImproving_deriv_iff`,
and **soundness**: `Play.isSPI_of_deriv`, `isStrictSPI_of_deriv`, `isUnilateralSPI_of_deriv`
turn a derivation into an actual SPI for every play family satisfying Assumptions 1–2.

**Certificates** (Appendix D.2, `Game.Certificate Γ`: one injection `Aʳᵉᵈᵢ ↪ Aᵢ` per player,
a `Fintype`): `Certificate.toFun`, `map`, `image`, `game` (the candidate `Γˢ`), `iso`,
the checks `ParetoImproving`, `StrictlyParetoImproving`, `Nontrivial`, `Affine i`,
`ReducesToImage i`, the identity certificate `Certificate.refl` (erratum D17), and the
**certificate characterizations** `Game.spiDecision_iff_certificate`,
`strictSPIDecision_iff_certificate`, `unilateralSPIDecision_iff_certificate`,
`strictUnilateralSPIDecision_iff_certificate` (Propositions 23, 25) with the search bounds
`Game.card_certificate_le` (`≤ m ^ l`) and `card_unilateralCertificate_le'` (the pairs
(player, certificate) are also `≤ m ^ l`) — Propositions 24, 26, Proposition 10.  `Certificate.reducesToImage_of_dominated` is the practical way to
discharge check 3.

**Hardness** (Appendix D.3, namespace `Hardness`): `Graph n`, `SubgraphIso`,
`SubgraphIsoProblem` (Definition 8), Table 9's `tableU₁`/`tableU₂` on
`TableAct n = Fin n ⊕ Fin n ⊕ Bool`, Table 10's `hardnessGame a a' ε` with
`reduce_hardnessGame` and `size_hardnessGame`, Lemma 28 as
`subgraphIsoProblem_iff_spiDecision` and its strict / unilateral / strict-unilateral
variants (hypotheses `1 ≤ n`, `0 < ε`, `ε * (2 * n) < 1`, `ε * (2 * n') < 1`), and Theorem 9's
carrier `Hardness.theorem9`.

## Program games (§3.2, Appendix A)

Mixed strategies and expected payoffs are EconCSLib's (`Game.Mixed`, `Game.expected`,
`expected_pure`, `abs_expected_le`); the threat point and a minimax profile against `i`
exist by compactness (`Game.threatPoint`, `Game.minimax`, bounded by
`threatPoint_le_of_bestResponse` and `le_threatPoint_of_guarantee`).  A **program game**
over a base game is the interface `ProgramGame Γ₀ R` (`dd:program-game`, `dd:exec-kernel`):
instructions `Instr i`, an execution kernel `exec` giving each player a mixed action at each
sample point, `payoff`, `toStrategic`, `IsProgramEquilibrium` (EconCSLib's Nash), `Plays`.
The concrete instruction language is `Prog Γ₀` (`play`, `delegate`, `ifAllSame`,
`dd:code-eq`) with `Prog.programGame`, `Prog.algorithm2` (erratum D15), **Proposition 18**
`Prog.algorithm2_isProgramEquilibrium` (also over the interface,
`ProgramGame.isProgramEquilibrium_of_algorithm2`) and **Theorem 1**
`Prog.exists_programEquilibrium_plays`.  Beyond the paper (RULING 9): default instructions
`ProgramGame.DefaultInstr`, `ParticipationIndependent`, information stages `Policy` and
`ForeknowledgeIndependent` (`Independence.lean`), with `Prog.default`, `Prog.dove`.

## Coordination (§5)

`Game.Correlated` (a distribution on outcomes; `Correlated.pure`, `.mix`, `.payoff`, and the
`stdSimplex` adapters `toStdSimplex`/`ofStdSimplex`), `Game.feasible` = `C(Γ)`
(`dd:feasible`; `feasible_eq_convexHull`, `convex_feasible`, `isCompact_feasible`,
`u_mem_feasible`), `Game.ParetoOptimalIn`, and **Lemma 11** `paretoOptimalIn_feasible_iff`
(the LP characterization, `lpObjective`).  Token games are `TokenGame Γ` (`game`, `fresh`,
`ue`, `ue_mem`, over a universe with room: `Game.HasRoomOutside`, `hasRoomOutside_of_infinite`,
`dd:room`), with **Definition 6** `TokenGame.IsSPI`/`IsStrictSPI`, the exact copy
`Game.tokenCopy`/`tokenIso`, and the reassignment `TokenGame.reassign`.  **Definition 7** is
`Play.StrictPerfectCoordinationSPIDecision` and **Proposition 12**
`Representatives.strictPerfectCoordinationSPIDecision_iff` (Algorithm 1's correctness,
under Assumptions 1–2 and room `Game.HasRoom`).  Conditional expectation on the play's fibers is
`Representatives.condExp` (a Bochner integral against `ProbabilityTheory.cond`;
`integral_eq_sum_condExp` is the law of total expectation), **Lemma 13** is
`Representatives.exists_reassignment_condExp_eq` (the replacement is an exact token copy of
`Γ` itself, `TokenGame.reassign`), the safely achievable payoffs are
`Representatives.achievable` with **Corollary 14** `achievable_eq_improvementSum`,
`convex_achievable`, `isCompact_achievable`, `isPolytope_achievable`, and the polytope
substrate (`IsPolytope`, `IsPolytope.inter_halfspace`, `inter_Ici`) is `Polytope.lean`.
-/
