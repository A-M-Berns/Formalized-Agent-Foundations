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
modeled as a single random function from games to outcomes (`dd:representatives`), so that Π(Γ) and Π(Γˢ) can be compared 
at every sample point rather than only in distribution. The game object here is connected to `StrategicGame` from 
EconCSLib through `Game.toStrategic`, allowing for the use of their pre-existing formalizations of strict dominance, 
mixed strategies, and Nash equilibrium.

 [Temporarily LLM]

**Certainty** (§3; `dd:certainty`). The paper's "with certainty" means probability one, but its 
arguments only use that certainty survives weakening and conjunction, which are the axioms of a filter. 
We therefore state Definitions 1–4, Theorem 3, the assumptions and Propositions 5–8 for an arbitrary 
filter `L` on the sample space, reading "with certainty" as `∀ᶠ ω in L` and "with positive probability" 
as `∃ᶠ ω in L`; probability one is the special case `L = ae μ`. This makes the universally quantified 
results stronger than printed. It also means every existence or strictness result must pin down its 
filter, since at the trivial filter every subset game is vacuously an SPI.

**Iterated elimination and the decision problem** (§4.6, Appendix D.1; `dd:derivation`, `dd:nontrivial`). 
Definition 5's chain of eliminations, reverse eliminations and isomorphisms is the inductive relation 
`Game.Deriv`, with Lemma 21 as its normal form (minus the printed length bound, which is false) and a 
soundness theorem turning derivations into SPIs under Assumptions 1 and 2. The paper's non-triviality 
condition, that the full reductions are not equal, is satisfied by shifting payoffs, so the printed 
decision problem is true of every game (erratum D13). We require instead that the reduced action sets 
differ, which is what the hardness proof in Appendix D actually uses, and keep the printed versions 
alongside with proofs that they are constant.

**Program games** (Appendix A; `dd:program-game`, `dd:exec-kernel`, `dd:code-eq`). We model the program 
game as an interface `ProgramGame Γ₀ R`: an instruction type per player and an execution rule that maps 
everyone's instructions and a sample point to a mixed action for each player, with program equilibrium 
as Nash equilibrium of the induced game. Proposition 18 is proved once over the interface from two 
properties of Algorithm 2 (everyone running it plays the SPI; a deviator is met with minimax play) and 
then instantiated in the three-instruction language `Prog`, where code equality is decided classically. 
Along the way we correct the punishment index in Algorithm 2 (erratum D15) and weaken the proof's 
"equals the threat point" to "at most the threat point" (erratum D8).

**Token games and improved coordination** (§5; `dd:feasible`, `dd:room`). The feasible set `C(Γ)` is 
defined by the paper's formula and proved equal to the convex hull of the pure payoffs. Fresh token 
actions are not automatically available in a fixed universe, so their existence is a hypothesis 
`Game.HasRoom`; without it the class of token games can be empty and an impossibility result like 
Proposition 16 would be vacuous, which is why its game lives over `CAct ⊕ ℕ`. Definition 7 gets the 
"strict" its title promises but its body omits (erratum D10). Lemma 13 needs Assumption 1 as well as 
Assumption 2 and is stated on the support of the play, where its conditional expectations exist. 
Corollary 14 is proved in the form the paper omits: the achievable set is the weighted Minkowski sum 
`∑ₐ P(Π(Γ)=a) • {y ∈ C(Γ) | y ≥ u(a)}`, hence a convex polytope.

**Certificates and the hardness construction** (Appendix D.2–D.3; `dd:complexity`). A certificate is a 
tuple of injections from the reduced action sets into the original ones, and Propositions 23 and 25 say 
a game is a yes-instance exactly when some certificate passes the checks of Appendix D. We add the 
non-triviality check the printed algorithms omit, without which the identity certificate accepts every 
game (erratum D17). The hardness games of Lemma 28 follow Table 9 where it disagrees with the printed 
formula and assume `0 < ε`. Nothing is proved about complexity classes or running times; see Future work.

**Witnesses** (`dd:book`). Every hypothesis the theorems take is shown to be satisfiable. Assumptions 1 
and 2 hold together for the book representatives, who look up each reduced game's isomorphism class in 
a book and play what its page says; the page distribution is a parameter, so the same construction 
yields deterministic or random representatives as needed. Each proposition and definition is exercised 
on a concrete game with all hypotheses discharged, and the decision problems and independence 
predicates have both yes- and no-instances; see `Examples/`.

## Participation and foreknowledge independence

These notions come from the CLR research agenda, not the paper. An SPI implementation is participation 
independent if a non-participant is met with the baseline play rather than a punishment, and 
foreknowledge independent if a player treats a non-participant the same whether or not she knew in 
advance. We define both at two levels. At the execution level (`Independence.lean`, `dd:default-instr`), 
each player has a default instruction executing as the baseline play, and the notions compare what a 
player actually does towards someone who dropped out; the fallback profile (comply with the SPI if 
everyone submitted the same code, else play the baseline) is participation independent and is a program 
equilibrium under a best-reply criterion, whereas Algorithm 2 is not participation independent in the 
Demand Game. At the program-choice level (`FullStrategy.lean`, after Appendix B of DiGiovanni's agenda), 
an SPI is a transformation of program profiles and the notions compare an agent's chosen program with a 
counterfactual choice supplied by a choice model; DiGiovanni's renegotiation example, including his 
agent that is participation independent but not foreknowledge independent, is worked out in 
`Examples/Renegotiation.lean`. Surrogate goals (B.3) and any general relation between the two levels 
are not covered.

[/LLM]

## Paper errata

Twenty-four issues are recorded in `notes/paper-errata.md`, grouped by seriousness. Each
is presented with an explanation of the content and implications of the issue and, where relevant,
a counterexample. Errata affecting the formalization's modeling decisions are mentioned in this 
README where relevant.

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
* Memberships in **complexity classes** are not proved in full here. This affects Theorem 9,
  Proposition 10, Lemma 11, Proposition 12, Propositions 23 to 26 and Lemma 28. See above in the "certificates
  and hardness" section for an explanation of what is proved in terms of the math underlying the complexity results.
  In the formalization of Logical Induction (2016) in this repo, we make use of complexitylib as a substrate
  for complexity-theoretic results, i.e., there is an existing library including concepts like P and NP that could be
  used for this paper's results. This would be a substantial original project bridging the two libraries, however.
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
