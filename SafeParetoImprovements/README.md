# Safe Pareto Improvements for Delegated Game Playing — Lean formalization

This directory is a Lean 4 formalization of *Safe Pareto Improvements for
Delegated Game Playing* by Caspar Oesterheld and Vincent Conitzer (Autonomous Agents and
Multi-Agent Systems, 2022, doi
[10.1007/s10458-022-09574-6](https://doi.org/10.1007/s10458-022-09574-6)). Its purpose is to
harden trust in the original SPI formulation, and develop a reusable formal framework for future
SPI research, especially semi-automated research conducted by LLMs.

## Formalization layout

The following table lists every Lean file in the library and their contents. The initial section of the table includes
files that directly formalize content from the paper, while the final section lists auxiliary files that do not directly
formalize paper results. For example, these auxiliary files demonstrate witnesses for the joint satisfiability of hypotheses,
and extensions beyond the paper into further SPI results such as participation independence and foreknowledge independence.

| file | paper nodes | Lean |
|---|---|---|
| `Play.lean` | Definitions 1, 2 | `Play.IsSPI`, `Play.IsStrictSPI` (Def. 1); `Game.Unilateral`, `Play.IsUnilateralSPI` (Def. 2) |
| `Correspondence.lean` | Definition 3, Lemma 2, Definition 4, **Theorem 3** | `Play.Corresponds` (Def. 3); `Play.corresponds_id`, `Corresponds.inv`, `.trans`, `.mono_rel`, `corresponds_allRel`, `Corresponds.ne_of_at_eq_empty`, `.ne_of_inv_at_eq_empty` (Lemma 2, items 1–7); `Play.ParetoImprovingCorrespondence` (Def. 4); `Play.isSPI_iff_exists_paretoImprovingCorrespondence` (Thm. 3) |
| `Assumptions.lean` | Assumptions 1, 2 | `Play.SatisfiesA1`, `Play.SatisfiesA2` |
| `Isomorphism.lean` | Lemma 4 | `GameIso.paretoImproving_of_paretoImproving` (weak), `GameIso.strictlyParetoImproving_of_strictlyParetoImproving` (strict) |
| `Reduction.lean` | Lemmas 19, 20 | `Game.isStrictlyDominated_erase` (Lemma 19), `Game.elim_diamond` (Lemma 20) |
| `Derivation.lean` | Definition 5, Lemmas 21, 22 | `Game.Step`, `Game.Deriv` (derivations); `Game.SPIDecision`, `StrictSPIDecision`, `UnilateralSPIDecision`, `StrictUnilateralSPIDecision` (the four problems), with `…Printed` variants keeping the printed non-triviality clause; `Game.Deriv.exists_normalForm` (Lemma 21), `Game.exists_paretoImproving_normalForm` (Lemma 22) |
| `Examples/PrisonersDilemma.lean` | Proposition 5 | `Examples.prisonersDilemma_isStrictSPI` |
| `Examples/DemandGame.lean` | Proposition 6 | `Examples.demandGame_isSPI` (weak clause), `demandGame_isStrictSPI` (strict clause) |
| `Examples/Temptation.lean` | Proposition 7 | `Examples.temptation_isStrictSPI` |
| `Examples/ComplicatedTemptation.lean` | Proposition 8 | `Examples.complicatedTemptation_isUnilateralSPI` |
| `Instruction.lean` | **Theorem 1**, **Proposition 18** | `Prog.exists_programEquilibrium_plays` (Thm. 1), `Prog.algorithm2_isProgramEquilibrium` (Prop. 18); the instruction language `Prog` and Algorithm 2 |
| `Coordination.lean` | **Definition 6**, Lemma 11 | `TokenGame.IsSPI`, `TokenGame.IsStrictSPI` (Def. 6); `Game.paretoOptimalIn_feasible_iff` (Lemma 11) |
| `PerfectCoordination.lean` | **Definition 7**, **Proposition 12** | `Play.StrictPerfectCoordinationSPIDecision` (Def. 7), `Representatives.strictPerfectCoordinationSPIDecision_iff` (Prop. 12) |
| `Characterization.lean` | **Lemma 13**, **Corollary 14** | `Representatives.exists_reassignment_condExp_eq` (Lemma 13); `Representatives.achievable_eq_improvementSum`, `convex_achievable`, `isCompact_achievable`, `isPolytope_achievable` (Cor. 14) |
| `Examples/Chicken.lean` | **Proposition 16** | `Examples.chicken_no_perfectCoordinationSPI` |
| `Complexity.lean` | **Propositions 23–26**, **Proposition 10** | `Game.spiDecision_iff_certificate` and its `strict`, `unilateral`, `strictUnilateral` variants (Props. 23, 25); `Game.spiDecision_search`, `unilateralSPIDecision_search` (Props. 24, 26, 10) |
| `Hardness.lean` | **Definition 8**, **Lemma 28**, **Theorem 9** | `Hardness.SubgraphIsoProblem` (Def. 8); `Hardness.subgraphIsoProblem_iff_spiDecision` and its `strict`, `unilateral`, `strictUnilateral` variants (Lemma 28); `Hardness.theorem9` |
| `Game.lean` | §2 vocabulary | games over a fixed action universe, `Game.EqOn` (the paper's equality of games), subset games, strict dominance, the EconCSLib bridge `Game.toStrategic` |
| `Ordering.lean` | §4.2 relations | the relations `R` and `⪰` |
| `Representatives.lean` | §3 probabilistic model | `Representatives` (a play family plus a probability measure); `isSPI_iff`, `isStrictSPI_iff`, `corresponds_iff` (the filter-level definitions at probability one); `support` |
| `Book.lean` | §4.4.3 consistency argument | the book representatives, which satisfy Assumptions 1 and 2 at every sample point: `Book`, `Book.const`, `prescribed`, `prescribedRandom`, `varying`, `exists_representatives_satisfiesA1_satisfiesA2` |
| `TwoPlayer.lean` | — | the player type `Two` and lemmas turning the set-based definitions into finite checks over a payoff table |
| `ProgramGame.lean` | Appendix A setup | mixed strategies, `Game.threatPoint`, `Game.minimax`, the interface `ProgramGame`, `IsProgramEquilibrium`, `isProgramEquilibrium_of_algorithm2` (Prop. 18 over the interface), `Game.bestReply` |
| `Polytope.lean` | — | polytopes as convex hulls of finite sets; a polytope cut by a half-space or an orthant is a polytope (`IsPolytope.inter_halfspace`, `inter_Ici`). Needed for Corollary 14, absent from Mathlib |
| `Independence.lean` | beyond the paper | execution-level participation and foreknowledge independence: `ProgramGame.DefaultInstr`, `ParticipationIndependent`, `Policy`, `ForeknowledgeIndependent`; `Prog.fallback`, `fallback_isProgramEquilibrium` |
| `FullStrategy.lean` | beyond the paper | DiGiovanni's program-choice-level definitions: `IsSPITransformation`, `FullStrategy`, `ChoiceModel`, `DemandPreserving`, `ParticipationIndependent`, `ForeknowledgeIndependent`, `participationIndependent_of_simultaneous` |
| `API.lean` | — | the consumer import: every library module, with the paper's vocabulary mapped to the supported names |
| `Examples/Witnesses.lean` | — | play families at which Propositions 5–8 have all hypotheses satisfied; yes-instances of the repaired Definition 5 problems; `unitRepresentatives` |
| `Examples/Coin.lean` | — | the fair coin on `Bool` |
| `Examples/ProgramGameWitnesses.lean` | — | Theorem 1's hypotheses satisfied deterministically (Prisoner's Dilemma) and randomly (Demand Game); the PI/FI predicates neither always true nor always false; Algorithm 2 not participation independent in the Demand Game |
| `Examples/IndependenceExamples.lean` | — | the fallback profile as a participation-independent program equilibrium in the Prisoner's Dilemma and the Demand Game |
| `Examples/Renegotiation.lean` | — | DiGiovanni's renegotiation example (CLR agenda, Appendix B.4), with the agent who is participation independent but not foreknowledge independent |
| `Examples/TokenWitnesses.lean` | — | a strict and an equality-only perfect-coordination SPI on a 2×2 game with a fresh token copy |
| `Examples/DecisionWitnesses.lean` | — | a yes- and a no-instance of Definition 7, via Proposition 12 |
| `Examples/CharacterizationWitnesses.lean` | — | Lemma 13 and Corollary 14 applied with all hypotheses satisfied; a play family on which `condExp` is a genuine average |
| `Examples/ComplexityWitnesses.lean` | — | certificates that pass and that fail a specific check; 144 certificates for the Demand Game against the bound 4096; Lemma 28 carried to a yes- and a no-instance |

Every declaration that carries a paper node (i.e. a direct result from the paper) has a docstring whose last line reads
`Paper node:` followed by the printed node. For a deeper comparison between the paper results and their corresponding
formalizations, see the SPI section of `docs/trust-surface.html`.

## Formalization choices

Each modeling choice taken in this formalization is recorded with a corresponding tag notated `dd:name`.
The tags are defined in one line each in `SafeParetoImprovements.lean` and argued at length (LLM writing)
in section 3 of `notes/scoping.md`.

**Games** (§2; `dd:universe`, `dd:total-utility`, `dd:representatives`). We want different games 
to be comparable, meaning that actions across all games must live in a single shared universe, 
with a unique type per player. This choice makes the SPI criterion u(Π(Γˢ)) ≥ u(Π(Γ)) well defined, 
since the shared universe means we can apply Γ's payoff to a profile of Γˢ. Likewise, the representatives are 
modeled as a single random function from games to outcomes (dd:representatives), so that Π(Γ) and Π(Γˢ) can be compared 
at every sample point rather than only in distribution. The game objec here is connected to `StrategicGame` from 
EconCSLib through `Game.toStrategic`, allowing for the use of their pre-existing formalizations of strict dominance, 
mixed strategies, and Nash equilibrium.

**Certainty** (§3; `dd:certainty`). The paper's "with certainty" means "with probability
one", but the arguments of §3 and §4 use only two properties of it: a certain statement
stays certain when weakened, and two certain statements are certain together. Those are
the axioms of a filter. Definitions 1–4, Lemma 2, Theorem 3, the two assumptions and
Propositions 5–8 are therefore stated for an arbitrary filter `L` on the sample space,
reading "with certainty" as `∀ᶠ ω in L` and "with positive probability" as `∃ᶠ ω in L`.
Every universally quantified statement is then stronger than the printed one, and the
printed one is recovered by taking `L` to be the almost-everywhere filter of the
probability measure. One consequence needs care. At the trivial filter every "with
certainty" claim holds vacuously, so every subset game is an SPI and no strict SPI exists.
Existence and strictness statements are therefore never left at an unconstrained filter:
they take a positive-probability hypothesis where the paper states one, and a
non-triviality assumption on `L` where the paper's claim is unconditional.

**Iterated elimination and the decision problem** (§4.6, Appendix D.1; `dd:derivation`,
`dd:nontrivial`). Iterated elimination of strictly dominated actions has a unique end
result. This follows from Lemma 19 through the diamond property of Lemma 20 and a
standard confluence argument. Definition 5 asks whether a game can be turned into a subset
game by a chain of eliminations, reverse eliminations and isomorphisms; that chain is the
inductive relation `Game.Deriv`. Lemma 21 gives its normal form, except that the bound the
paper prints on the length of the normal form is false (erratum D14) and is left out. A
soundness theorem shows that a derivation yields an SPI under Assumptions 1 and 2. The
paper's non-triviality condition, "the full reductions are not equal", is satisfied by
shifting the payoffs of any subset game, so the printed decision problem is true of every
game (erratum D13). Our decision problems require instead that the reduced action sets
differ, which is the condition the hardness proof in Appendix D actually relies on. The
printed versions are kept alongside, with theorems showing that they are constant.

**Program games** (Appendix A; `dd:program-game`, `dd:exec-kernel`, `dd:code-eq`). The
program game of Appendix A is modeled as an interface, `ProgramGame Γ₀ R`: a type of
instructions for each player, and an execution rule that, given everyone's instructions
and a sample point of the representatives, gives each player a mixed action. Program
equilibrium is Nash equilibrium of the induced game. Proposition 18 is proved once over
this interface, from two properties of Algorithm 2: when everyone runs it the SPI is
played, and when one player deviates the others play their minimax strategies against
her. It is then instantiated at the concrete language `Prog`, in which equality of code is
decided classically. Two slips in the paper are corrected on the way. Algorithm 2 names
the wrong player's minimax strategy (erratum D15), and the proof of Proposition 18 equates
a deviator's payoff with the threat point when it is only bounded by it (erratum D8).
Threat points exist by compactness.

**Token games and improved coordination** (§5; `dd:feasible`, `dd:room`). The feasible
set `C(Γ)` is defined as in the paper, as the payoff vectors of correlated strategies, and
then proved equal to the convex hull of the pure payoffs. A token game carries two payoff
functions, as in the paper: the payoff `uˢ` handed to the representatives, and the
assignment `uᵉ` of feasible payoff vectors to token outcomes, which is what the original
players receive. The paper takes for granted that fresh token actions exist. Over a fixed
universe that is a hypothesis, `Game.HasRoom`, which holds whenever the universe has
infinitely many unused actions. Over a finite universe there may be no token games at all,
and an impossibility result about them would then say nothing; this is why Proposition
16's game is placed over the universe `CAct ⊕ ℕ`, and why the proposition is also stated
in a form that does not mention tokens. Definition 7 is titled the strict decision problem
but its body leaves strictness out; we read it in (erratum D10). Lemma 13 replaces a
perfect-coordination SPI by an exact token copy of the game, with `uᵉ` defined along
whichever isomorphism Assumption 2 provides. It needs Assumption 1 in addition to the
paper's "under Assumption 2", and it is stated on the support of the play, because off
the support the conditional expectations it speaks of are undefined (erratum D7).
Corollary 14 is proved in the form the paper says it omits: the set of safely achievable
expected payoffs is the weighted Minkowski sum `∑ₐ P(Π(Γ)=a) • {y ∈ C(Γ) | y ≥ u(a)}`, from
which convexity, compactness and the polytope property follow.

**Certificates and the hardness construction** (Appendix D.2–D.3; `dd:complexity`). A
certificate for the decision problem is a tuple of injections from the reduced action sets
into the original ones. Propositions 23 and 25 are proved as characterizations: a game is
a yes-instance exactly when some certificate passes the checks of Appendix D. One check is
added that the printed algorithms lack, the non-triviality check; without it the identity
certificate makes every game a yes-instance (erratum D17). The hardness games of Lemma 28
follow Table 9 where it disagrees with the printed payoff formula (erratum D18), and they
assume `0 < ε`, which the paper needs and does not state (erratum D21). Nothing is proved
about complexity classes or running times; see Future work.

## BParticipation and foreknowledge independence

These two notions come from the CLR research agenda rather than from the paper. An SPI
implementation is participation independent if a player who declines to take part is met
with the baseline play rather than a punishment, and foreknowledge independent if a player
treats a non-participant the same way whether or not she knew in advance that they would
not participate. Both are defined at two levels.

At the level of execution (`Independence.lean`, `dd:default-instr`), each player has a
default instruction that executes as the baseline play, and the two notions compare the
mixed action a player ends up realizing towards someone who has dropped out. The fallback
profile, in which each player complies with the SPI if everyone submitted the same code
and otherwise plays the baseline, executes the SPI, is participation independent, and is a
program equilibrium whenever each player's expected best reply to the baseline, computed
sample point by sample point, is at most her expected payoff under the SPI. Algorithm 2,
by contrast, is not participation independent in the Demand Game.

At the level of program choice (`FullStrategy.lean`), following Appendix B of DiGiovanni's
research agenda, an SPI is a transformation of program profiles, and the two notions
compare the program an agent chose with the one she would have chosen under a
counterfactual. The counterfactual choices are supplied by a choice model, a function of
the other agents' programs. DiGiovanni's renegotiation example is worked out in
`Examples/Renegotiation.lean`, including his agent who is participation independent but
not foreknowledge independent. Surrogate goals (his Appendix B.3) are not covered, and
nothing general is proved about how the two levels relate.

## Paper errata

Twenty-four defects are recorded in `notes/paper-errata.md`, grouped by seriousness. Each
is presented with an explanation and, where the defect is a false claim, a counterexample.
Errata affecting the formalization's modeling decisions are mentioned in this README where
relevant.

## Future work

* **Theorem 15** is not included in this formalization. As printed, its statement is undefined
  (erratum D12), and under the obvious repair the proof in Appendix E does not go through. The
  following LLM-written paragraph gives concrete examples of both.
  ```
  Let Γ be the two-player game whose outcomes pay (0,0), (1,0), (0,1), (1,1), so C(Γ) = [0,1]² and the
  strong Pareto frontier is the single point (1,1); if the representatives surely play the (0,0) outcome,
  then x₁ᵐⁱⁿ = x₁ᵐᵃˣ = 0 and Case A's premise holds, but L₁ needs π₁(0, PF(C(Γ))), a frontier point with
  first coordinate 0, and none exists, so the theorem cannot even be stated although all its hypotheses
  hold; the repair the figures and the paper's own existence remark describe is to project onto C(Γ)
  instead, giving π₁(0, C(Γ)) = (0,1). Under that repair the proof in Appendix E still fails: Case A
  reassigns each outcome a to its northward projection π₁(u(a), L₁), justified by "all outcomes lie below
  the line L₁, so π₁ is linear", but for the game whose outcomes pay (0,0), (2,0), (1,1), (2,1) with
  support {(0,0), (2,0), (1,1)}, L₁ is the segment from (0,0) to (2,1), the premise of Case A holds since
  (2,1) dominates the support, yet the support point (1,1) lies strictly above L₁, and the proof's
  reassignment sends it to (1, ½), which is worse for player 2, so the token game the proof constructs is
  not an SPI. The theorem's conclusion happens to hold here by another reassignment, so the example
  refutes the printed argument rather than the repaired statement, but a proof would have to be built
  afresh from Corollary 14's characterization, and none has been.
  ```
* Memberships in **complexity classes** are not proved in full here. Theorem 9,
  Proposition 10, Lemma 11, Proposition 12, Propositions 23 to 26 and Lemma 28 are carried
  as *qualified* nodes. That means the exact mathematical content of each statement is
  proved: the certificate characterizations of the decision problems, the search bound
  `card ≤ m^l` where `m` is the total number of actions in the game and `l` the total
  number in its full reduction, the linear program of Lemma 11, the correctness of
  Algorithm 1 as an if-and-only-if, and the reductions from subgraph isomorphism. What is
  not proved is anything the paper phrases as "NP-complete", "in polynomial time", "in
  `O(m^l)`" or "in linear time". 
* **Two prior results** that the paper cites are currently absent from the formalization. Theorem 17 is Tennenholtz's
  folk theorem for program equilibrium, and Lemma 27 is Cook's theorem. These are currently neither
  proved nor assumed in Lean.
* **Languages for program games** are currently limited to general interface claims, with only a single
  toy instantiation using the three-instruction language `Prog` (see `Instruction.lean` and `ProgramGame.lean`). Thus,
  paper claims about languages like LISP are currently unformalized.

## Mechanical verification

The following commands perform mechanistic checks that the formalization builds correctly, 
is free of axioms and sorry, and that the API and scope are as intended.

```
lake build SafeParetoImprovements APITests AxiomAudit
python3 scripts/check-safe-pareto-improvements-nodes.py
python3 scripts/lint_paper_labels.py
python3 scripts/check_paper_wiring.py
```
