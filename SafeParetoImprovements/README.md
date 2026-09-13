# Safe Pareto Improvements for Delegated Game Playing — formalization and trust surface

A Lean 4 formalization of Caspar Oesterheld and Vincent Conitzer, *Safe Pareto
Improvements for Delegated Game Playing*, Autonomous Agents and Multi-Agent Systems 36
(2022), doi [10.1007/s10458-022-09574-6](https://doi.org/10.1007/s10458-022-09574-6)
(short version at AAMAS 2021), built on Mathlib and the game-theory library EconCSLib,
with a research layer beyond the paper for participation independence and foreknowledge
independence after the CLR safe-Pareto-improvements research agenda.

**Status.**  Of the paper's 37 numbered nodes, 35 carry a proved Lean statement annotated
to them; the two that do not are Theorem 15, deferred by ruling as the final scope (§3
below), and Lemma 27 (Cook's theorem), a cited external result that is neither re-proved
nor assumed.  There is no `sorry` and no axiom beyond Lean's three standard ones anywhere
in the library; every public declaration of the library (854) is named on the axiom gate.  The registry status is
`in-progress` because the human read-through of the statement surface is outstanding;
nothing else gates `completed`.

This file is the trust surface: what is claimed, what is disclosed, what is deliberately
not claimed, and why each modelling choice was made.  Companion documents:

| document | what it holds |
|---|---|
| `SafeParetoImprovements.lean` | the root import, the one-line glossary of every `dd:` design tag, and the file map |
| `SafeParetoImprovements/API.lean` | the supported consumer import: a documented map from the paper's vocabulary to the Lean names |
| `APITests/SafeParetoImprovements.lean` | client-style tests that use only the API |
| `SafeParetoImprovements/KNOWLEDGE.md` | the correspondence table, settled decisions and pitfalls, maintained for whoever works on the code next |
| `SafeParetoImprovements/notes/scoping.md` | the scoping note: rationale for every design decision (§3), the rulings that fixed them (§8), an early external review (§9) |
| `SafeParetoImprovements/notes/paper-errata.md` | the 24 defects found in the source paper, each with extraction line numbers |
| `docs/trust-surface.html` | the generated read-through page for every paper in this repository; this paper's section is a correspondence view with the qualifications listed in its preamble |

**Verifying.**  From the repository root:

```
lake build SafeParetoImprovements APITests AxiomAudit
python3 scripts/check-safe-pareto-improvements-nodes.py
python3 scripts/lint_paper_labels.py
python3 scripts/check_endpoint_coverage.py
python3 scripts/check_paper_wiring.py
```

The first command elaborates the library, the client tests, and the axiom gate
(`AxiomAudit.lean`, whose `SPI-INVENTORY` block names every endpoint under
`#assert_axioms_clean` and freezes the field *names* of the boundary structures under
`#assert_fields`).  The node checker verifies that every `Paper node:` annotation names a
node the paper prints and that every annotated declaration is on the axiom gate, and it
*prints* which printed nodes have no annotated carrier (currently Theorem 15 and Lemma 27)
without failing on them — coverage is a claim of this README, checked by reading that
readout, not a gate.  The label linter requires `theorem` only for paper-facing statements;
the wiring check that the registry, API and tests are in place.  All of this runs in CI on
every push.

---

## 1. The paper in one page

Two principals delegate the playing of a normal-form game `Γ` to representatives whose
behaviour `Π(Γ)` they cannot predict but can constrain: each principal may instruct their
representative to play a *subset game* `Γˢ` (restricted action sets, possibly different
payoffs) instead.  A subset game is a **safe Pareto improvement** (SPI) on `Γ` if
`u(Π(Γˢ)) ≥ u(Π(Γ))` *with certainty* — whatever the representatives would have done — where
`u` is the original players' payoff.  The paper's spine:

* **§3** — SPIs, strict SPIs, unilateral SPIs (Definitions 1–2); every SPI is played in some
  program equilibrium of the delegation game (Theorem 1, proved in Appendix A through
  Proposition 18 and a punishing instruction, Algorithm 2).
* **§4** — *outcome correspondences* `Γ ∼_Φ Γ'` between games (Definition 3, Lemma 2); the
  keystone **Theorem 3**: `Γˢ` is an SPI on `Γ` iff there is a Pareto-improving outcome
  correspondence from `Γ` to `Γˢ` (Definition 4); two behavioural assumptions on the
  representatives — they never play strictly dominated actions (Assumption 1) and play
  isomorphic games isomorphically (Assumption 2) — under which SPIs can be *derived*
  (Lemma 4, the worked examples Propositions 5–8: Prisoner's Dilemma, Demand Game,
  Temptation Games); and the SPI decision problem (Definition 5), NP-complete (Theorem 9,
  Appendix D), with a search bound (Proposition 10).
* **§5** — SPIs under improved coordination: token games and the perfect-coordination SPI
  (Definitions 6–7), Algorithm 1 and its correctness (Lemma 11, Proposition 12), the
  structure of safely achievable expected payoffs (Lemma 13, Corollary 14), a two-player
  geometric characterization (Theorem 15, Appendix E), and a limiting example (Proposition
  16).
* **§6** — the SPI selection problem, prose only.

## 2. What is formalized

Every row is a Lean declaration whose docstring ends with a `Paper node:` line naming the
printed node, checked by the node checker.  Statements at the level of §3–§4 are made for
an arbitrary *certainty filter* and are therefore strengthened relative to the printed ones
(§4.2 below); the parenthetical notes give the statement-level qualifications a reader must
hold in mind — hypotheses beyond the paper's, clauses not rendered — each of which is also
in the declaration's docstring.

| paper node | carrier(s) | file |
|---|---|---|
| Definition 1 (SPI, strict SPI) | `Play.IsSPI`, `Play.IsStrictSPI` | `Play.lean` |
| Definition 2 (unilateral subset game, unilateral SPI) | `Game.Unilateral`, `Play.IsUnilateralSPI` | `Play.lean` |
| Definition 3 (outcome correspondence) | `Play.Corresponds` | `Correspondence.lean` |
| Lemma 2, items 1–7 | `Play.corresponds_id`, `Play.Corresponds.inv`, `.trans`, `.mono_rel`, `Play.corresponds_allRel`, `Play.Corresponds.ne_of_at_eq_empty`, `.ne_of_inv_at_eq_empty` | `Correspondence.lean` |
| Definition 4 (Pareto-improving correspondence) | `Play.ParetoImprovingCorrespondence` | `Correspondence.lean` |
| **Theorem 3** | `Play.isSPI_iff_exists_paretoImprovingCorrespondence` | `Correspondence.lean` |
| Assumption 1, Assumption 2 | `Play.SatisfiesA1`, `Play.SatisfiesA2` | `Assumptions.lean` |
| Lemma 4 (weak and strict forms) | `GameIso.paretoImproving_of_paretoImproving`, `GameIso.strictlyParetoImproving_of_strictlyParetoImproving` | `Isomorphism.lean` |
| Lemma 19 (path independence, local form) | `Game.isStrictlyDominated_erase` | `Reduction.lean` |
| Lemma 20 (the diamond property of single-step elimination; the printed first alternative `Γ = Γ̂` corrected to `Γ = Γ̃`, erratum D20) | `Game.elim_diamond` | `Reduction.lean` |
| Definition 5 (SPI decision problem, strict and unilateral variants) as a derivation system | `Game.Step`, `Game.Deriv`; repaired non-triviality (`dd:nontrivial`, erratum D13): `Game.SPIDecision`, `Game.StrictSPIDecision`, `Game.UnilateralSPIDecision`; printed forms kept alongside: `Game.SPIDecisionPrinted` (constant-true for non-empty `N`, `Game.spiDecisionPrinted_of_nonempty`), `…UnilateralSPIDecisionPrinted` (constant-true on fully reduced games, `unilateralSPIDecisionPrinted_of_reduced`), and `…StrictSPIDecisionPrinted`, which *keeps content* — it fails on one-action games, `not_strictSPIDecisionPrinted_of_card_le_one` | `Derivation.lean` |
| Lemma 21 (normal form of derivations: eliminations, one isomorphism, reverse eliminations; the printed length bound is not rendered, erratum D14) | `Game.Deriv.exists_normalForm` | `Derivation.lean` |
| Lemma 22 (symmetry-free Pareto-improving chain to the reduction of the SPI candidate) | `Game.exists_paretoImproving_normalForm` | `Derivation.lean` |
| **Proposition 18** (Algorithm 2 is a program equilibrium executing `Π(Γˢ)`; the deviator's payoff is *at most* the threat point, erratum D8; Algorithm 2's punishment index repaired, erratum D15) | `Prog.algorithm2_isProgramEquilibrium` | `Instruction.lean` |
| Definition 5, the fourth problem (strict unilateral) | `Game.StrictUnilateralSPIDecision` | `Derivation.lean` |
| **Proposition 23** (the omnilateral algorithm is correct: certificate iffs for the plain and strict problems; "NP time" not rendered, `dd:complexity`; non-triviality check restored, erratum D17) | `Game.spiDecision_iff_certificate`, `Game.strictSPIDecision_iff_certificate` | `Complexity.lean` |
| **Proposition 25** (the unilateral algorithm is correct: certificate iffs with the three checks; the printed "WLOG same action sets for player `i`" discharged by `ElimStar.transfer`) | `Game.unilateralSPIDecision_iff_certificate`, `Game.strictUnilateralSPIDecision_iff_certificate` | `Complexity.lean` |
| **Propositions 24, 26** and **Proposition 10** (the search bound `card ≤ m ^ l`, for the unilateral pairs (player, certificate) as well; "solved in `O(m^l)`" not rendered) | `Game.spiDecision_search`, `Game.unilateralSPIDecision_search` (bounds `Game.card_certificate_le`, `card_unilateralCertificate_le'`) | `Complexity.lean` |
| **Definition 8** (subgraph isomorphism problem) | `Hardness.SubgraphIsoProblem` | `Hardness.lean` |
| **Lemma 28** (subgraph isomorphism reduces to each of the four SPI problems on the two-player game of Table 10, as an iff; "linear time" and "NP-hard" not rendered; Table 9 followed over the printed formula, erratum D18) | `Hardness.subgraphIsoProblem_iff_spiDecision` and the strict / unilateral / strict-unilateral variants | `Hardness.lean` |
| **Theorem 9** (the certificate characterizations of the four problems over any finite player set, together with Lemma 28's reductions over two-player games; the size bound that makes the characterizations membership-shaped is `Game.card_certificate_le`, stated separately; "NP-complete" not rendered) | `Hardness.theorem9` | `Hardness.lean` |
| **Definition 6** (perfect-coordination SPI, strict variant) | `TokenGame.IsSPI`, `TokenGame.IsStrictSPI` | `Coordination.lean` |
| Lemma 11 (Pareto-optimality in `C(Γ)` as a linear program, stated for an arbitrary target vector `y` — an infeasible `y` makes both sides hold vacuously; the polynomial-time clause not rendered, `dd:complexity`) | `Game.paretoOptimalIn_feasible_iff` | `Coordination.lean` |
| **Definition 7** (strict perfect-coordination SPI decision problem; "strict" read in, RULING 7; per play family, RULING 10) | `Play.StrictPerfectCoordinationSPIDecision` | `PerfectCoordination.lean` |
| **Proposition 12** (Algorithm 1's correctness as an iff, under Assumptions 1–2 and room; the polynomial-time clause not rendered) | `Representatives.strictPerfectCoordinationSPIDecision_iff` | `PerfectCoordination.lean` |
| **Lemma 13** (every perfect-coordination SPI is replaced by an exact token copy of `Γ` with `uᵉ` along Assumption 2's isomorphism between the reductions, same conditional expectations on the support; hypotheses Assumption 1 — an addition to the printed "under Assumption 2", needed to move the play into the reduction — Assumption 2, and room `Γ.HasRoom`; errata D6, D7, D19) | `Representatives.exists_reassignment_condExp_eq` | `Characterization.lean` |
| **Corollary 14** (the safely achievable expected payoffs: the weighted Minkowski-sum formula, convex, compact, and a polytope; the same three hypotheses as Lemma 13; the formula is the characterization the paper omits) | `Representatives.achievable_eq_improvementSum`, `convex_achievable`, `isCompact_achievable`, `isPolytope_achievable` | `Characterization.lean` |
| **Proposition 16** (Table 7 over `CAct ⊕ ℕ`, `dd:room`: a Pareto improvement no perfect-coordination SPI achieves, for the one play family the paper's description determines — the fair coin at `p = ½`; the statement cannot be universalized over `Π`, since other representatives satisfying Assumptions 1–2 on the same game do admit the improvement, `chicken_spi_for_other_representatives`; also in a label-free form over feasible payoff vectors, `chicken_no_feasible_dominating_of_mean_cc`) | `Examples.chicken_no_perfectCoordinationSPI` | `Examples/Chicken.lean` |
| **Theorem 1** (every SPI is played in a program equilibrium of the program game with delegation instructions, given the threat-point guarantee) | `Prog.exists_programEquilibrium_plays` | `Instruction.lean` |
| Proposition 5 (Prisoner's Dilemma, Table 3) | `Examples.prisonersDilemma_isStrictSPI` | `Examples/PrisonersDilemma.lean` |
| Proposition 6 (Demand Game, Tables 1–2), both clauses; the strict clause takes the paper's "if `(DM, DM)` is played with positive probability" as an explicit `∃ᶠ` hypothesis | `Examples.demandGame_isSPI`, `Examples.demandGame_isStrictSPI` | `Examples/DemandGame.lean` |
| Proposition 7 (Temptation Game, Table 6) | `Examples.temptation_isStrictSPI` | `Examples/Temptation.lean` |
| Proposition 8 (Complicated Temptation Game, Tables 4–5) | `Examples.complicatedTemptation_isUnilateralSPI` | `Examples/ComplicatedTemptation.lean` |

**Carriers without a paper node of their own.**  The §2 vocabulary — games, subset games,
strict dominance, the bridge to EconCSLib's `StrategicGame` — in `Game.lean`; game
isomorphism (`GameIso`, `Game.Isomorphic`) in `Isomorphism.lean`; the §4.2 relations `R`
and `⪰` obtained by quantifying the correspondence away (`Ordering.lean`); the probabilistic
model `Representatives` with the **realization at probability one** — `ae μ` is a filter,
non-degenerate for a probability measure, and Definitions 1 and 3 at `L = ae μ` unfold to the
printed statements (`isSPI_iff`, `isStrictSPI_iff`, `corresponds_iff` in
`Representatives.lean`); the canonical full reduction `Game.reduce`, with confluence and
uniqueness from Lemmas 19–20 (`Reduction.lean`); and the **book representatives** of
§4.4.3, which prove Assumptions 1 and 2 jointly satisfiable with the page distribution as a
parameter (`Book.lean`).  Every sample space the development instantiates is discrete
(`Unit`, `Bool`, a finite profile space), so the measurability field of `Representatives`
is discharged trivially in every witness; the probabilistic content exercised is the fair
coin's genuinely random play, not a non-trivial σ-algebra.

**Non-vacuity is proved, not asserted.**  Every Proposition 5–8 conclusion is reached by a
play family that *also* satisfies Assumptions 1 and 2 inside the same statement
(`Examples/Witnesses.lean`); the repaired Definition 5 predicates have proved yes-instances
(the Demand Game, the Complicated Temptation Game) next to their no-instance; Theorem 1's
hypotheses are witnessed twice, deterministically in the Prisoner's Dilemma and with a
genuinely random `Π(Γ₀)` in the Demand Game (a fair coin), and its threat-point hypothesis
is shown to have content by a book that violates it (`Examples/ProgramGameWitnesses.lean`);
Definition 6 has strict and equality-only witnesses, with `uᵉ` defined along the book's
isomorphism (`Examples.conflictStrictToken_isStrictSPI`, `conflictPlainToken_isSPI` in
`Examples/TokenWitnesses.lean`); Definition 7 is two-sided through Proposition 12
(`Examples/DecisionWitnesses.lean`); Lemma 13 and Corollary 14 are applied, with all their
hypotheses discharged, on the conflict game with book representatives, where the
achievable set is not a singleton, and — separately, on a hand-built play family that
satisfies neither assumption — the conditional expectation `Representatives.condExp` is
shown to be a genuine average rather than a point evaluation
(`Examples/CharacterizationWitnesses.lean`); the complexity nodes have certificates that
pass, certificates that fail a specific check, and a subgraph-isomorphism yes-instance
carried through Lemma 28 to a yes-instance of the strict unilateral decision problem
(`Examples/ComplexityWitnesses.lean`); the client tests then carry such an instance through
soundness to an actual strict unilateral SPI at probability one
(`APITests/SafeParetoImprovements.lean`).

## 3. What is not claimed

* **Theorem 15** (the two-player geometric characterization) has no carrier.  Its printed
  statement projects onto the strong Pareto frontier `PF(C(Γ))`, where the projections need
  not exist (erratum D12); its proof in Appendix E is a sketch that sets aside degenerate
  cases and contains a step that is not a general fact.  Deferring it is the final scope by
  ruling (RULING 16); the substrate a future attempt would need is in place (Lemma 13,
  Corollary 14's formula, the feasible polytope).
* **Complexity-class and running-time clauses** are not rendered anywhere.  Nine nodes
  are carried as *qualified* nodes — Theorem 9, Proposition 10, Lemma 11, Proposition 12,
  Propositions 23–26, Lemma 28 (with Definition 8) — meaning the exact mathematics of their
  statements is proved (certificate characterizations, the search bound `card ≤ m ^ l`
  where `m` is the total number of actions of the game and `l` that of its full reduction,
  the linear program, the correctness iff of Algorithm 1, the reductions) without
  "NP-complete", "in polynomial time", "`O(m^l)`" or "linear time".  `Hardness.theorem9` is
  a conjunction of certificate iffs and Lemma 28's reductions, nothing more.
* **Cited external results are not re-proved**: Theorem 17 (Tennenholtz's folk theorem for
  program equilibrium, cited by Theorem 1's proof and not needed by the Lean route) and
  Lemma 27 (Cook's theorem, cited only).  Neither is assumed as an axiom.
* **§6** and Appendix B contribute no nodes and are not rendered.
* **Two narrowings** of the paper's generality are disclosed at their carriers: Theorem 1 is
  proved for the program game whose instructions are exactly the three-instruction
  language `Prog` (play a mixed action; delegate a subset game to the representatives; test
  whether everybody submitted the same code and punish otherwise), not for "any programming
  language such as Lisp"; and the program-game interface returns each player a mixed
  action given the representatives' sample point, with the players independent given it,
  so Theorem 1 and Proposition 18 over the interface cover independent-execution program
  games.
* **Nothing is executable.**  Algorithms 1 and 2 are carried as correctness statements
  (an iff for Algorithm 1, an equilibrium theorem for Algorithm 2 as a term), not as
  programs one can run.

## 4. Formalization choices

Every choice below carries a `dd:` tag, defined in one line in `SafeParetoImprovements.lean`
and argued in `notes/scoping.md` §3; the rulings that fixed them are in §4.9.  The
governing principle: when the paper is ambiguous or defective, the Lean statement takes
the reading under which the paper's own proofs are correct, keeps the printed reading
alongside where it has content, and says so in the docstring.

### 4.1 Games

* **Fixed action universe** (`dd:universe`).  A `Game N 𝒜` is a finite nonempty subset
  `S i` of a fixed per-player universe `𝒜 i`, with a payoff `u`.  The paper never says
  what the actions of a subset game are drawn from; fixing a universe makes subset games
  and isomorphisms first-class and makes every universally quantified theorem stronger.
  §5's fresh token actions are then a *hypothesis* (`Game.HasRoom`, see 4.7) rather than a
  global assumption.
* **Total payoffs and the paper's equality of games** (`dd:total-utility`).  `Game.u` is
  total on universe profiles, so Lean's `=` on `Game` is *not* the paper's equality: two
  presentations can differ only off the profiles.  The paper's equality is `Game.EqOn`
  (same action sets, payoffs agreeing on the smaller game's profiles), forced by Definition
  2's `uˢᵢ = uᵢ` across different domains, and every paper-facing statement uses it.  Where
  the paper's `Π` must be a function of the paper's game, play families satisfying
  `Play.RespectsEqOn` are required, and the book representatives are routed through a
  canonical presentation `Game.canon` so that they do.
* **Finite action sets** (erratum D23): the paper never says so but every payoff matrix
  and Lemma 4's proof need it; `S i` is a `Finset`.
* **The game-theory substrate is EconCSLib** (a pinned dependency), reached through one
  bridge `Game.toStrategic`; strict dominance, mixed strategies, expected payoffs and Nash
  equilibrium are EconCSLib's, each characterised by a lemma that reads as the paper's
  sentence, and no paper-facing statement names an EconCSLib declaration.

### 4.2 Certainty and the representatives

* **The representatives are a random solver** (`dd:representatives`).  The paper compares
  `Π(Γ)` with `Π(Γˢ)` *at the same sample point*, so all the `Π(Γ)` are jointly
  distributed: a sample point is one complete way the representatives could behave, a
  function from games to outcomes.  `Play N 𝒜 Ω` is that object (`play : Game → Ω →
  outcome`, membership everywhere); `Representatives` adds a probability measure and
  measurable outcome fibers.  No rationality is built in — Assumptions 1 and 2 are separate
  predicates, read literally as "for every game, with certainty".
* **"With certainty" is a filter** (`dd:certainty`).  Every argument in §3–§4 uses only two
  facts about certainty — it is preserved under weakening and under conjunction — which
  are the axioms of a `Filter`.  Definitions 1–4, Lemma 2, Theorem 3, Assumptions 1–2 and
  Propositions 5–8 are therefore stated for an arbitrary filter `L` on the sample space
  ("with certainty" is `∀ᶠ ω in L`, "with positive probability" is `∃ᶠ ω in L`), which
  *strengthens* them relative to the print.  The paper's own instance, probability one, is
  the almost-everywhere filter `ae μ`, and `Representatives.lean` proves that at `L = ae μ`
  the definitions unfold to the printed statements — by iffs, never by a second copy of a
  theorem.  Footnote 2's dominance-across-models reading comes by instantiation.
* **What the generalization costs, and does not hide.**  At the trivial filter `L = ⊥`
  every "with certainty" statement is vacuously true, so every subset game is an SPI there
  and no strict SPI exists; the universally quantified nodes are therefore strictly
  stronger than the print, while any *existence* statement is only as strong as the filter
  it is made at.  Existence and strictness statements accordingly carry their filter
  explicitly: the paper's "with positive probability" becomes an `∃ᶠ` hypothesis where the
  print states one (Proposition 6's strict clause, strict soundness of derivations) and a
  `[L.NeBot]` instance where the print's positive-probability claim is unconditional
  (Propositions 5 and 7); `ae μ` is non-degenerate for a probability measure.  The client
  tests demonstrate the `⊥` vacuity so that no reader takes an existence at an
  unconstrained filter for a result.

### 4.3 Isomorphisms

* **Bijective, strictly positive scaling** (`dd:iso`, erratum D5).  §2 says `λ ∈ ℝⁿ₊` and
  leaves bijectivity unstated; Lemma 4 and Assumption 2 need both, so `GameIso` is a
  per-player family of bijections with `λᵢ > 0`.  Isomorphisms transport reductions
  (`GameIso.imageGame`, `reduce_eq_imageGame`), which is what lets Lemma 13 copy the whole
  game rather than its reduction.

### 4.4 Assumptions 1–2 and their consistency

* **Assumption 1** is rendered as the paper states it, as an *outcome correspondence*:
  for every game, player and strictly dominated action, the play of the game corresponds
  with certainty to the play of the game with that action removed, under the relation that
  deletes the dominated action and is the identity elsewhere — so the representatives never
  play the dominated action *and* removing it leaves their play unchanged, which is
  stronger than merely selecting surviving actions.  **Assumption 2** is "isomorphic
  *reduced* games are played isomorphically, with certainty", with the isomorphism
  existential.  Both are predicates on a play family and a filter.
* **The book** (`dd:book`).  §4.4.3 sketches that the assumptions are jointly satisfiable
  by representatives who look up each reduced game's isomorphism class in a book of pages.
  `Book.lean` constructs those representatives with the page distribution as a *parameter*
  (deterministic, `ω`-dependent, or varying across every surviving outcome), proves both
  assumptions hold at every sample point, and is the source of every non-vacuity witness
  that needs a rational `Π`.

### 4.5 Reduction and the decision problem

* **The full reduction is canonical.**  `Game.reduce` is the result of iterated strict
  elimination; Lemma 19 is the local path-independence fact, the diamond lemma gives
  confluence, and uniqueness of the normal form follows.
* **Definition 5 is a derivation system** (`dd:derivation`).  The paper's SPI decision
  problem asks for a chain of eliminations and isomorphisms from `Γ` to a subset game.
  `Game.Step`/`Game.Deriv` are that chain as an inductive relation; Lemma 21 is its normal
  form (eliminations, one isomorphism, reverse eliminations; the printed length bound
  `m ≤ k` is false, erratum D14, and is not rendered), Lemma 22 the symmetry-free chain to
  the reduction, and soundness (`Play.isSPI_of_deriv` and the unilateral variant) turns a
  derivation into an SPI under Assumptions 1–2 — the derivation supplies the subset-game
  hypothesis itself; the strict variant needs in addition the paper's side condition that
  every outcome surviving elimination is played with positive probability (an `∃ᶠ`
  hypothesis; the paper states it in prose after Definition 5).  A derivation records the
  correspondence it was built from, while Assumption 2 supplies *some* isomorphism of the
  reductions, so soundness goes through Lemma 21's normal form rather than the recorded
  relation directly.
* **The non-triviality clause is repaired** (`dd:nontrivial`, erratum D13).  As printed,
  "the reductions are not equal" is satisfied by any payoff shift of a subset game, so the
  printed plain and unilateral problems are constant-true.  The carriers require the
  reduced *action sets* to differ, the reading Appendix D's hardness proof uses; the printed
  forms are kept alongside as `…Printed` with their triviality theorems, and the strict
  printed form is shown to keep content.

### 4.6 Program games and Theorem 1

* **An interface, then a language** (`dd:program-game`).  Appendix A's program game is
  the structure `ProgramGame Γ₀ R`: an instruction type per player and an execution kernel
  giving each player a mixed action at each sample point of the representatives; its
  induced game is EconCSLib's strategic game and program equilibrium is EconCSLib's Nash
  equilibrium.  Proposition 18 is proved *once* over the interface from Algorithm 2's two
  semantic properties (everybody-cooperating executes `Π(Γˢ)`, punishers play the minimax
  profile) and instantiated at the term `Prog.algorithm2`.
* **Execution kernel** (`dd:exec-kernel`).  Execution returns mixed actions independent
  given the representatives' sample point.  This is what erratum D8 needs — Proposition
  18's bound requires the deviator's action to be independent of the punishers'
  randomization — and it avoids product-measure bookkeeping: payoffs are
  `∫ ω, expected (exec c ω) i`.
* **The language `Prog`** (`dd:code-eq`): mixed actions, delegation of a subset game to the
  representatives, and the "same code?" test with a punishment per differing player.  Code
  equality is classical (programs contain real numbers); when several players' code
  differs the punished player is a fixed classical choice (the paper's loop takes the
  first, but `N` is unordered), forced under a unilateral deviation.  Algorithm 2's
  punishment index is corrected (erratum D15).  Theorem 1 is carried for this language —
  the narrowing in §3.
* **Threat points** exist by compactness (`Game.threatPoint`, `Game.minimax`), metered from
  above by a pure best response and from below by a pure guarantee.

### 4.7 Coordination (§5)

* **The feasible set** `C(Γ)` (`dd:feasible`) is the paper's own formula — payoff vectors
  of correlated strategies — proved equal to Mathlib's convex hull of the pure payoffs;
  convexity and membership come from the formula, everything geometric from the hull.
* **Token games** (`TokenGame Γ`) carry two payoff maps, as §5 does: the game the
  representatives are handed has its own payoff `uˢ`, and the original players assign each
  token outcome a feasible payoff vector `uᵉ ∈ C(Γ)`; Definition 6 compares `uᵉ` of the
  token play with `u` of the base play.
* **Token games need room** (`dd:room`).  §5's token actions must be fresh, `Aˢᵢ ∩ Aᵢ = ∅`;
  over a fixed universe their existence is the hypothesis `Game.HasRoom Γ`, an injective
  copy of each action set avoiding `Γ`'s own.  The §5 examples live over universes with
  infinite room (`X ⊕ ℕ`, or `ℕ` itself), where `hasRoomOutside_of_infinite` supplies it;
  over a finite universe the class of token games can be *empty*, which would make every
  impossibility statement vacuous — the reason Proposition 16's Chicken game is stated over
  `CAct ⊕ ℕ` and additionally carried in a label-free form that quantifies over feasible
  payoff vectors rather than token games.
* **Definition 7 reads "strict"** (erratum D10, RULING 7): the problem is named the strict
  problem but its body omits strictness.
* **Lemma 13 copies `Γ` itself**, with the token payoff `uᵉ` defined along whichever
  isomorphism of reductions Assumption 2 supplies (errata D6, D19; RULINGS 10–11), and its
  conditional expectations are stated on the support of `Π(Γ)`, where they are defined
  (erratum D7; `Representatives.condExp` through `ProbabilityTheory.cond`).  Lemma 13 and
  Corollary 14 take **Assumption 1 in addition** to the printed "under Assumption 2":
  Assumption 2 speaks only about reduced games, so Assumption 1 is what lets the copy be
  played through its reduction (RULING 11).
* **Corollary 14 is carried as the characterization the paper omits**: the safely
  achievable expected payoffs are exactly the weighted Minkowski sum
  `∑ₐ P(Π(Γ)=a) • {y ∈ C(Γ) | y ≥ u(a)}` (`achievable_eq_improvementSum`), from which
  convexity, compactness and the printed "convex polygon" clause follow (`isPolytope_achievable`,
  through a half-space section theorem for polytopes in `Polytope.lean` that Mathlib lacks).

### 4.8 The complexity nodes

Carried as *qualified* nodes (`dd:complexity`, RULING 6; design note
`notes/complexity-layer.md`).  A **certificate** is a tuple of injections `Aʳᵉᵈᵢ ↪ Aᵢ`;
Propositions 23 and 25 say each of the four (strict) (unilateral) decision problems holds
iff some certificate passes the appendix's checks — with the non-triviality check the
printed algorithms omit restored (erratum D17) — and Propositions 24, 26 and 10 are the
bound `card ≤ m ^ l` on the certificate type.  Definition 8 and Lemma 28 render the
hardness construction: subgraph isomorphism reduces to each of the four problems on the
two-player games of Tables 9–10, as an iff, following Table 9 where it disagrees with the
printed formula (erratum D18, RULING 15), with the hypotheses `0 < ε` the paper omits
(erratum D21) and `1 ≤ n` in place of the printed "WLOG `n, n̂ ≥ 2`".  Theorem 9 conjoins
the characterizations and the reductions.

### 4.9 Rulings

All recorded in `notes/scoping.md` §8 with their dates.

| ruling | decision |
|---|---|
| 0 | scope is §2–§6 with the appendix proofs; complexity nodes qualified |
| 1 | EconCSLib as a pinned dependency, reached through one bridge |
| 2 | certainty parametric in a filter, paper nodes at that level, probability one by realization iffs |
| 3 | program games: a concrete instruction language, classical code equality, independent execution given the sample point |
| 5 | the book construction as a theorem with a parametric page distribution |
| 6 | Theorem 9 / Proposition 10 / Lemma 11 / Proposition 12 as qualified nodes |
| 7 | Definition 7 reads "strict" into its body |
| 8, 16 | Theorem 15 deferred; the deferral is the final scope |
| 9 | participation and foreknowledge independence stateable in the instruction layer |
| 10–13 | §5: `uᵉ` along Assumption 2's isomorphism; Assumption 1 moves play into the reduction; Corollary 14's polytope clause proved from the formula; examples over `X ⊕ ℕ` with room as a hypothesis |
| 14 | Lemma 27 (Cook) cited, not axiomatized |
| 15 | Table 9 followed over the printed formula |

No ruling numbered 4 was issued.  The remaining design tags (`dd:universe`,
`dd:total-utility`, `dd:representatives`, `dd:iso`, `dd:derivation`) were accepted as
proposed in the scoping note without a numbered ruling.

## 5. Defects found in the paper

Twenty-four, recorded in `notes/paper-errata.md` with extraction line numbers and, where
the defect is a false claim, a counterexample.  The `Level` column there is authoritative.
Statement-level defects carried as **disclosures** at the Lean statements: D1, D2, D5, D8,
D10, D12, D13, D15, D17, D18, D21, D23.  Statement-level typos or clauses simply not
rendered: D7, D9, D11, D14, D20.  Proof- or notation-level: D3, D4, D6, D16, D19, D24.
A false claim in the prose, affecting no node: D22.  In brief:

* **D1** Definition 1's strictness clause compares `uᵢ(Π(Γˢ))` with itself; read
  `uᵢ(Π(Γˢ)) > uᵢ(Π(Γ))`.
* **D2** Definition 4 writes `Γ'` for `Γˢ` and `→` for `⊸`; Lemma 4's hypothesis that `Γ'`
  is a subset game of `Γ` is missing.  The Lean repair is not to add the hypothesis but to
  define "Pareto-improving" with the source game's payoff on any target, so Definition 4's
  structure and Lemma 4 hold for arbitrary targets and specialize to subset games.
* **D3** Theorem 3's proof quantifies over `i = 1, 2` in an `n`-player statement and opens
  the ⇒ direction with the inequality reversed.
* **D4** Proof-level slips: Lemma 2.7 cites reflexivity for symmetry; Proposition 6 writes
  `Ψ(Φ(Γˢ))`; Proposition 7 names the wrong eliminated strategies.
* **D5** Isomorphism (§2): `λ ∈ ℝⁿ₊` ambiguous between `≥ 0` and `> 0`, bijectivity
  unstated; both are needed (`dd:iso`).
* **D6** *(downgraded)* Lemma 13's "WLOG" relabeling is proof-level, not a statement
  defect.
* **D7** Corollary 14 says "polygon" for an `n`-player polytope; Lemma 13 and Corollary 14
  condition on null events — rendered on `supp Π(Γ)`.
* **D8** Proposition 18's proof: the deviator's payoff is *at most* the threat point, and
  the bound needs the deviator's action independent of the punishers' randomization.
* **D9** Lemma 21: `Γ'ₘ = Γₘ` for `Γ'ₘ = Γₖ`, and "`Γˢ'ʳᵉᵈ` is isomorphic to `Γˢ'ʳᵉᵈ`" for
  "… to `Γʳᵉᵈ`" in the concise restatement.
* **D10** Definition 7 is named the *strict* problem but its body omits strictness —
  RULING 7 (2026-09-12) reads "strict" into the carrier
  (`Play.StrictPerfectCoordinationSPIDecision`).
* **D11** Proposition 23 says "unilateral" in the omnilateral subsection; Lemma 19's
  discussion says "path dependence" for independence.
* **D12** Theorem 15 as printed projects onto the strong Pareto frontier `PF(C(Γ))`, where
  the projections need not exist; the paper's own remark is about `C(Γ)`.  RULING 8
  (2026-09-12) **defers** Theorem 15: no carrier until the projection reading is settled.
* **D13** Definition 5's non-triviality clause is satisfied by every payoff shift of a
  subset game, so the printed (unilateral) SPI decision problem is constant-true.  RULING
  (2026-09-12): the carrier requires the reduced *action sets* to differ (`dd:nontrivial`);
  the printed clause is carried alongside as `…Printed` with its triviality theorem.
* **D14** Lemma 21's length bound `m ≤ k` on the reorganized chain is false; the bound is
  not rendered and the wrappers carry the qualitative shape only.
* **D15** Algorithm 2 line 3 prints `minimax(i, j)`, which is *player `j`'s* strategy; the
  punisher must play her own coordinate `minimax(j, i)` (`Prog.algorithm2`).
* **D16** Proposition 16's proof sketch writes `u(Π(Γˢ))` where Definition 6 requires
  `uᵉ(Π(Aˢ, uˢ))`; `u` is not defined on token outcomes.  Notation only — the carrier
  states the expectation with `uᵉ`.
* **D17** The algorithms of Appendix D.2 perform no non-triviality check, so the identity
  injections make them return *True* on every game; the carriers add the check
  (`Certificate.Nontrivial`), and `Certificate.refl` records the defect.
* **D18** Table 9 and the printed payoff formulas disagree on the corner blocks (`0`
  vs. `ε`, `8n` cells), and the disagreement decides whether the unilateral half of Lemma
  28's first claim holds; the carriers follow the table (RULING 15).
* **D19** Lemma 13's display and Corollary 14's set-builder write `u` on token outcomes
  where `uᵉ` is meant (the same slip as D16); the carriers use `uᵉ`.
* **D20** Lemma 20's cancellation alternative names `Γ̂` for `Γ̃`; no carrier is affected.
* **D21** The hardness construction never states `0 < ε`, which it needs; the carriers
  assume it.
* **D22** The prose claim that pure strict elimination removes exactly the
  non-rationalizable strategies in two-player games is false (it needs mixed dominance).
* **D23** §2 never states that action sets are finite, which Lemma 4's proof and every
  payoff matrix need; `Game` has `Finset` action sets.
* **D24** Lemma 28's second-claim proof mis-states which outcomes pay `≥ 6` outside `Γ̂`
  and carries several index slips; the Lean route does not follow it.

## 6. Beyond the paper: participation and foreknowledge independence

The CLR research agenda asks of an SPI implementation two properties the paper does not
name: **participation independence** (a player who declines the scheme is met with the
baseline play, not a punishment) and **foreknowledge independence** (a player behaves the
same towards a non-participant whether or not she knew in advance).  This layer makes
them stateable and works them out; it carries no paper node and claims no theorem of the
paper.

**Execution level** (`Independence.lean`, `dd:default-instr`, RULING 9).  Over any
`ProgramGame`, a *default instruction* per player executes as the paper's baseline
`Π(Γ₀)`; "player `j` did not participate" is the profile with `j` at her default.
`ParticipationIndependent` says that when `j` drops out, `i` realises the same mixed
action as under everybody's default, at every sample point of the representatives; an
*information stage* `Policy` chooses an instruction from a signal that may announce a
counterpart's non-participation, and `ForeknowledgeIndependent` says the mixed action
realised towards a drop-out is the same whether the instruction was chosen uninformed or
informed.  Both are equalities of conditional action distributions given the
representatives' sample point (the execution kernel has no private seeds to couple);
they compare behaviour *towards a non-participant* and say nothing about demands during
participation.  What is proved: the **dove profile**
(comply with the SPI when everybody submits the same code, otherwise play the baseline)
executes the SPI, is participation independent for every player, and is a program
equilibrium whenever each player's expected *ex-post* best reply to the baseline — the
best reply computed sample point by sample point, which a program need not be able to
realise — is at most her expected SPI payoff (`Prog.dove_isProgramEquilibrium`, from the
interface-level `ProgramGame.isProgramEquilibrium_of_fallback`; a sufficient criterion
only, and a demanding one — failing it says nothing); Algorithm 2 is *not*
participation independent whenever its minimax punishment differs from the baseline, which
it does in the Demand Game; a participation-independent instruction paired with the
default as the informed choice is foreknowledge independent.  On the paper's own examples
(`Examples/IndependenceExamples.lean`) the dove profile is a participation-independent
program equilibrium in the Prisoner's Dilemma and in the Demand Game at the conflict
outcome, where Proposition 18's threat-point hypothesis fails.

**Program-choice level** (`FullStrategy.lean`), after Anthony DiGiovanni, *CLR's Safe
Pareto Improvements Research Agenda* (LessWrong, 20 April 2026), Appendix B.1–B.2: an SPI
as a transformation of program profiles that weakly Pareto-improves every profile of a
space (`IsSPITransformation`); a *full strategy* `(𝐟, 𝐩)`; and demand preservation,
participation independence and foreknowledge independence defined through the two
counterfactual program choices `𝐩ᴾᵢ(𝐟)` and `𝐩ᶠᵢ(𝐟)`.  The source leaves "the program agent
`i` would have chosen had …" informal; here it is data, a *choice model* giving each
agent's input program as a function of the *other* agents' programs (used, resp. believed),
with a consistency clause tying `𝐩` to the model.  B.2's own argument — under simultaneous
commitment participation independence is immediate from demand preservation — is
`participationIndependent_of_simultaneous`.

**DiGiovanni's renegotiation example** (`Examples/Renegotiation.lean`, Appendix B.4) is
formalized with the source's pseudocode as an execution model over the `ProgramGame`
interface: a program is a base strategy (a demand from the three the source mentions,
50%, 60%, 80%, and whether a doomsday device backs it) or a renegotiation program built on
a base strategy *and its own renegotiation logic*; conflict pays both players alike (`t`
for a takeover attempt, `d` for a doomsday);
`run` forms both proposals with the two programs' logics, so the pseudocode's "take it if
our proposals match" has content (a conceding logic makes the proposals differ and both
fall back).  Proved: demand preservation as a property of B.4's logic; the 50%/80%/doomsday
numbers; `rn` is a B.1 SPI on all base-strategy profiles for `d ≤ t` and strictly so on the
B.4 profile for `d < t` (the source gives no conflict payoffs, so they are parameters);
participation independence at both levels together; the fall-back policy's foreknowledge
independence; and B.2's "PI but not FI" agent — demands 60% whether or not the counterpart
participates, would have demanded 50% had she known — participation independent and not
foreknowledge independent at both levels.  Boundaries: those representatives supply only
the baseline and are not claimed to satisfy Assumptions 1–2 (the negotiation game has no
strictly dominated action, so Assumption 1 is not what separates them from the paper's
results; their arbitrary play on other games is); B.3 (surrogate goals, concession
equivalence) is not rendered; no general bridge between the two levels or between
`IsSPITransformation` and the paper's `Play.IsSPI` is claimed.

**What a researcher can state today**: SPI implementability without punishment and its
sufficient equilibrium criterion; execution-level PI/FI over any program game; B.1/B.2
demand preservation and PI/FI over an abstract program space; the safely achievable payoff
polytope as a selection substrate.  **Not yet**: surrogate goals and concession
equivalence; a bridge between the two PI/FI levels; individual-rationality conditions for
SPIs in the sense of DiGiovanni et al. (2024).

## 7. Using the formalization

```lean
import SafeParetoImprovements.API
```

`API.lean` is documentation-only: it imports every library module (no example files) and
maps the paper's vocabulary to the supported names, section by section.  The client tests
in `APITests/SafeParetoImprovements.lean` show the intended style — they build their own
games and compose endpoints: a reduced game on its whole universe has no SPI; Theorem 3 on
a client play family; soundness turning a derivation into an SPI at probability one; a
subgraph isomorphism between client graphs carried through Lemma 28 and soundness to an
actual strict unilateral SPI; feasible-set convexity and Pareto optimality; threat-point
bounds; and, for the research layer, a capped-demand transformation that is a B.1 SPI, a
choice model in which participation independence follows from simultaneity, and a
foreknowledge-independence failure by a demand mismatch.  The example files under
`SafeParetoImprovements/Examples/` are the paper's own games and the non-vacuity witnesses;
they are importable but are not part of the supported surface.

## 8. Provenance and verification

**Numbering.**  The paper numbers on global counters that never reset: Definitions on one
(`Definition 1` … `Definition 8`), Assumptions on another, and Theorem, Lemma, Proposition
and Corollary on a single shared counter (`Theorem 1`, `Lemma 2`, `Theorem 3`, …
`Lemma 28`); examples are headed `Proposition (Example) n` and cited as `Proposition n`.
The paper labels nothing, so the printed kind-and-number pair is the provenance key.  An
annotation is a docstring's last line, ``Paper node: `Lemma 4` ``.

**Source.**  There is no arXiv record and no TeX (arXiv 2403.05103 is a later paper by
the same authors).  The committed source is `notes/oesterheld-conitzer-2022-spi.txt`, a
`pdftotext -layout` extraction of the committed PDF, and the node checker reads the printed
numbers off its header lines and asserts that exactly 37 nodes are derived (8 Definitions,
2 Assumptions, 4 Theorems, 10 Lemmas, 12 Propositions, 1 Corollary), so a re-extraction that
mangles a header fails rather than silently shrinking the set of nodes an annotation may
name.  Theorem 17's header is torn by a display delimiter in the extraction and is
deliberately not parsed.

**The axiom gate.**  `AxiomAudit.lean`'s `SPI-INVENTORY` block names every public
declaration of the library (854 names: paper-node carriers, witnesses, and every
supporting definition and lemma) under `#assert_axioms_clean`, which fails the build on `sorryAx` or any axiom
beyond `propext`, `Classical.choice` and `Quot.sound`, and freezes the field *names* of
the boundary structures (`Game`, `Play`, `Representatives`, `GameIso`,
`Play.ParetoImprovingCorrespondence`, `Book`, `ProgramGame`, `ProgramGame.DefaultInstr`,
`ProgramGame.Policy`, `FullStrategy`, `ChoiceModel`, `Game.Correlated`, `TokenGame`, …)
under `#assert_fields`, so that a premise cannot be added as a new field without the gate
noticing; a strengthening hidden inside an existing field's type would pass it, which is
why the boundary structures are part of the human read-through.  `theorem` is reserved for
paper-facing statements; supporting results are `lemma`s.

**Audit history.**  The formalization was built under an orchestrated audit loop: nine
rounds of fresh-context adversarial audits over statements, definitions and proofs,
combining auditors from two independent model families in every round where the second
family's channel was available (two rounds ran on one family only, and are recorded as
such), with the pre-publication audit run blind to this project's own conclusions (given
the paper, the source and the user's rulings, but not the knowledge base or errata; it
rediscovered twenty of the recorded errata independently) and the last two rounds reviewing
the whole written surface as a CLR final project.  Across the rounds 202 findings were raised, 198
fixed and 4 refuted with a recorded reason.  Four were blockers when raised — a source
defect (Definition 5's printed non-triviality clause, D13), a vacuous impossibility
statement caught before anything relied on it (Proposition 16's first carrier lived over a
finite universe, where no token game exists), a tautological agreement test in the first
renegotiation model, and a false README row — and all four are fixed; none is open.  Statement-level findings that changed a carrier are
recorded at the carrier; the notable ones were that Definition 5's printed non-triviality
clause is constant-true, that the book's play must be a function of the paper's game rather
than of its Lean presentation, that Lemma 13 must copy `Γ` rather than its reduction, and
that Table 9 and the printed payoff formula disagree materially.

## 9. File map

| file | contents |
|---|---|
| `Game.lean` | §2: games over a fixed universe, `EqOn`, subset games, strict dominance, the EconCSLib bridge |
| `Play.lean` | §3: play families, Definitions 1–2 at the certainty-filter level |
| `Correspondence.lean` | §4.2–4.3: outcome correspondences, Lemma 2, Definition 4, Theorem 3 |
| `Ordering.lean` | §4.2: the relations `R` and `⪰` |
| `Isomorphism.lean` | §2/§4.4: game isomorphisms, Lemma 4, transport of reductions |
| `Assumptions.lean` | §4.4: Assumptions 1–2 |
| `Reduction.lean` | §4.6/App. D: iterated strict elimination, Lemma 19, confluence, the canonical reduction |
| `Representatives.lean` | §3: the probability space, probability-one realization, support, conditional expectation |
| `Book.lean` | §4.4.3: the book representatives satisfying Assumptions 1–2 |
| `Derivation.lean` | §4.6/App. D: Definition 5 as a derivation system, Lemmas 21–22, soundness, the non-triviality repair |
| `TwoPlayer.lean` | the player type `Two` and table-checking lemmas |
| `ProgramGame.lean` | App. A: mixed strategies, threat points, the program-game interface, Proposition 18 over it, best replies |
| `Instruction.lean` | App. A: the language `Prog`, Algorithm 2, Proposition 18, Theorem 1 |
| `Independence.lean` | beyond the paper: default instructions, PI, information stages, FI, the dove profile |
| `FullStrategy.lean` | beyond the paper: DiGiovanni's B.1–B.2 at the level of program choice |
| `Coordination.lean` | §5.1: `C(Γ)`, token games, Definition 6, room, Lemma 11 |
| `PerfectCoordination.lean` | §5.2: Definition 7, the reassignment construction, Proposition 12 |
| `Polytope.lean` | polytopes as convex hulls of finite sets and their half-space sections |
| `Characterization.lean` | §5.3: Lemma 13, Corollary 14 with the Minkowski formula |
| `Complexity.lean` | §4.6/App. D.2: certificates, Propositions 23–26, Proposition 10 |
| `Hardness.lean` | App. D.3: Definition 8, Tables 9–10, Lemma 28, Theorem 9 |
| `API.lean` | the consumer guide |
| `Examples/` | the paper's games (Propositions 5–8, 16), the non-vacuity witnesses, the PI/FI examples, DiGiovanni's renegotiation example |

## 10. Limitations and directions

* Theorem 15 is the one in-scope node without a carrier; a future attempt should read the
  projections as `πᵢ(x, C(Γ))`, state the conclusion as membership in
  `Representatives.achievable`, and reprove from the Minkowski formula, since Appendix E's
  argument does not go through as printed.
* The instruction language `Prog` is the minimal one Algorithm 2 needs; a theorem
  quantifying over *all* deviations in a richer language would be substantively stronger
  than what is carried at `Prog`.
* The two PI/FI levels are exhibited together on one example but not related in general;
  DiGiovanni et al.'s (2024) individual-rationality conditions and Appendix B.3's surrogate
  goals are natural next targets on this substrate.
* The program-choice-level definitions follow a source that calls them working
  formalizations; if the source's terminology changes, `FullStrategy.lean` is the one file
  to revise.
