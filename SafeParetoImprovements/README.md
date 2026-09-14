# Safe Pareto Improvements for Delegated Game Playing — Lean formalization

A Lean 4 formalization of Oesterheld and Conitzer, *Safe Pareto Improvements for Delegated
Game Playing* (JAAMAS 2022, doi [10.1007/s10458-022-09574-6](https://doi.org/10.1007/s10458-022-09574-6)),
on Mathlib and the game-theory library EconCSLib, plus a layer beyond the paper for
participation independence and foreknowledge independence.

**Status.** 35 of the paper's 37 numbered nodes carry a proved Lean statement annotated to
them. The two that do not are Theorem 15 (deferred by ruling as the final scope) and
Lemma 27 (Cook's theorem, cited and neither re-proved nor assumed). No `sorry`; no axiom
beyond Lean's three standard ones; all 854 public declarations are named on the axiom gate.
The registry status stays `in-progress` until the human read-through of the statement
surface is done.

## The paper

Two principals delegate the playing of a normal-form game `Γ` to representatives whose
behaviour `Π(Γ)` they cannot predict but can constrain: each may instruct their
representative to play a *subset game* `Γˢ` (restricted action sets, possibly different
payoffs) instead. `Γˢ` is a **safe Pareto improvement** (SPI) on `Γ` if `u(Π(Γˢ)) ≥ u(Π(Γ))`
with certainty, `u` the original payoff.

* §3: SPIs, strict and unilateral SPIs (Definitions 1–2); every SPI is played in a program
  equilibrium of the delegation game (Theorem 1, via Appendix A).
* §4: outcome correspondences (Definition 3, Lemma 2); **Theorem 3**, `Γˢ` is an SPI iff
  there is a Pareto-improving outcome correspondence `Γ → Γˢ` (Definition 4); two
  behavioural assumptions on the representatives (Assumption 1: never play strictly
  dominated actions; Assumption 2: play isomorphic games isomorphically) under which SPIs
  can be derived (Lemma 4, examples Propositions 5–8); the SPI decision problem
  (Definition 5), NP-complete (Theorem 9, Appendix D), with a search bound (Proposition 10).
* §5: SPIs under improved coordination: token games and perfect-coordination SPIs
  (Definitions 6–7), Algorithm 1 (Lemma 11, Proposition 12), the safely achievable expected
  payoffs (Lemma 13, Corollary 14), a two-player geometric characterization (Theorem 15),
  a limiting example (Proposition 16).
* §6: the SPI selection problem, prose only.

## What is formalized

| file | paper nodes | Lean |
|---|---|---|
| `Play.lean` | Definitions 1–2 | `Play.IsSPI`, `IsStrictSPI`, `Game.Unilateral`, `Play.IsUnilateralSPI` |
| `Correspondence.lean` | Definition 3, Lemma 2 (1–7), Definition 4, **Theorem 3** | `Play.Corresponds`, `corresponds_id`, `.inv`, `.trans`, `.mono_rel`, `corresponds_allRel`, `.ne_of_at_eq_empty`, `.ne_of_inv_at_eq_empty`, `Play.ParetoImprovingCorrespondence`, `Play.isSPI_iff_exists_paretoImprovingCorrespondence` |
| `Assumptions.lean` | Assumptions 1–2 | `Play.SatisfiesA1`, `Play.SatisfiesA2` |
| `Isomorphism.lean` | Lemma 4 (weak, strict) | `GameIso.paretoImproving_of_paretoImproving`, `…strictlyParetoImproving…` |
| `Reduction.lean` | Lemmas 19–20 | `Game.isStrictlyDominated_erase`, `Game.elim_diamond` |
| `Derivation.lean` | Definition 5 (four problems), Lemmas 21–22 | `Game.Step`, `Game.Deriv`; `Game.SPIDecision`, `StrictSPIDecision`, `UnilateralSPIDecision`, `StrictUnilateralSPIDecision`, printed forms `…Printed`; `Game.Deriv.exists_normalForm`, `Game.exists_paretoImproving_normalForm` |
| `Examples/PrisonersDilemma.lean` | Proposition 5 | `Examples.prisonersDilemma_isStrictSPI` |
| `Examples/DemandGame.lean` | Proposition 6 | `Examples.demandGame_isSPI`, `demandGame_isStrictSPI` |
| `Examples/Temptation.lean` | Proposition 7 | `Examples.temptation_isStrictSPI` |
| `Examples/ComplicatedTemptation.lean` | Proposition 8 | `Examples.complicatedTemptation_isUnilateralSPI` |
| `Instruction.lean` | **Theorem 1**, **Proposition 18** | `Prog.exists_programEquilibrium_plays`, `Prog.algorithm2_isProgramEquilibrium` |
| `Coordination.lean` | **Definition 6**, Lemma 11 | `TokenGame.IsSPI`, `IsStrictSPI`, `Game.paretoOptimalIn_feasible_iff` |
| `PerfectCoordination.lean` | **Definition 7**, **Proposition 12** | `Play.StrictPerfectCoordinationSPIDecision`, `Representatives.strictPerfectCoordinationSPIDecision_iff` |
| `Characterization.lean` | **Lemma 13**, **Corollary 14** | `Representatives.exists_reassignment_condExp_eq`, `achievable_eq_improvementSum`, `convex_achievable`, `isCompact_achievable`, `isPolytope_achievable` |
| `Examples/Chicken.lean` | **Proposition 16** | `Examples.chicken_no_perfectCoordinationSPI` |
| `Complexity.lean` | **Propositions 23–26**, **Proposition 10** | `Game.spiDecision_iff_certificate` (+ strict, unilateral, strict unilateral), `Game.spiDecision_search`, `unilateralSPIDecision_search` |
| `Hardness.lean` | **Definition 8**, **Lemma 28**, **Theorem 9** | `Hardness.SubgraphIsoProblem`, `Hardness.subgraphIsoProblem_iff_spiDecision` (+ three variants), `Hardness.theorem9` |
| `Game.lean` | §2 (unnumbered) | games over a fixed universe, `Game.EqOn`, subset games, strict dominance, the EconCSLib bridge `Game.toStrategic` |
| `Ordering.lean` | §4.2 (unnumbered) | the relations `R` and `⪰`, the correspondence quantified away |
| `Representatives.lean` | §3 (unnumbered) | `Representatives`, the probability-one realization `isSPI_iff`, `isStrictSPI_iff`, `corresponds_iff`, `support` |
| `Book.lean` | §4.4.3 (unnumbered) | the book representatives satisfying Assumptions 1–2: `Book`, `Book.const`, `prescribed`, `prescribedRandom`, `varying`, `exists_representatives_satisfiesA1_satisfiesA2` |
| `TwoPlayer.lean` | — | the player type `Two` and the table-checking lemmas Theorem 9 and the examples use |
| `ProgramGame.lean` | Appendix A (unnumbered) | mixed strategies, `Game.threatPoint`, `Game.minimax`, the interface `ProgramGame`, `IsProgramEquilibrium`, Proposition 18 over the interface (`isProgramEquilibrium_of_algorithm2`), `Game.bestReply` |
| `Polytope.lean` | — | polytopes as convex hulls of finite sets and their half-space sections (`IsPolytope.inter_halfspace`, `inter_Ici`), which Corollary 14 needs and Mathlib lacks |
| `Independence.lean` | beyond the paper | `ProgramGame.DefaultInstr`, `ParticipationIndependent`, `Policy`, `ForeknowledgeIndependent`; `Prog.fallback`, `fallback_isProgramEquilibrium` |
| `FullStrategy.lean` | beyond the paper | `IsSPITransformation`, `FullStrategy`, `ChoiceModel`, `DemandPreserving`, `ParticipationIndependent`, `ForeknowledgeIndependent`, `participationIndependent_of_simultaneous` |
| `API.lean` | — | the consumer import, mapping the paper's vocabulary to the supported names |
| `Examples/Witnesses.lean` | — | play families at which Propositions 5–8 and the Definition 5 yes-instances have all hypotheses discharged; `unitRepresentatives` |
| `Examples/Coin.lean` | — | the fair coin on `Bool`, for the examples that need a random `Π` |
| `Examples/ProgramGameWitnesses.lean` | — | Theorem 1's hypotheses discharged deterministically (Prisoner's Dilemma) and randomly (Demand Game); the PI/FI predicates two-sided; Algorithm 2 not participation independent in the Demand Game |
| `Examples/IndependenceExamples.lean` | — | the fallback profile as a participation-independent program equilibrium in the Prisoner's Dilemma and the Demand Game |
| `Examples/Renegotiation.lean` | — | DiGiovanni's Appendix B.4 renegotiation example, with the "PI but not FI" agent at both levels |
| `Examples/TokenWitnesses.lean` | — | strict and equality-only perfect-coordination SPIs on a `2 × 2` game with a fresh token copy |
| `Examples/DecisionWitnesses.lean` | — | Definition 7 two-sided through Proposition 12: a yes-instance and a no-instance |
| `Examples/CharacterizationWitnesses.lean` | — | Lemma 13 and Corollary 14 applied with all hypotheses discharged; `condExp` a genuine average on a hand-built play family |
| `Examples/ComplexityWitnesses.lean` | — | certificates that pass and fail, the count `144 ≤ 4096`, and Lemma 28 carried to a yes- and a no-instance |

Every node carrier's docstring ends with a `Paper node:` line naming the printed node,
checked both ways by `scripts/check-safe-pareto-improvements-nodes.py`, and states in one
or two sentences what differs from the print.  The files after `Hardness.lean` carry no
node: they are the paper's unnumbered vocabulary, the infrastructure the nodes rest on,
the layer beyond the paper, and the non-vacuity witnesses, each of which reaches a
paper-facing conclusion with all hypotheses discharged.

## What is not claimed

* **Theorem 15.** Its printed statement projects onto the strong Pareto frontier, where
  the projections need not exist (erratum D12), and Appendix E's proof is a sketch with a
  step that is not a general fact. Deferred as the final scope (RULING 16).
* **Complexity classes and running times.** Theorem 9, Proposition 10, Lemma 11,
  Proposition 12, Propositions 23–26 and Lemma 28 are *qualified*: the exact mathematics
  of each statement is proved (certificate characterizations, the search bound `card ≤ m^l`
  with `m` the number of actions and `l` that of the reduction, the linear program, the
  correctness iff of Algorithm 1, the reductions) without "NP-complete", "polynomial time",
  "`O(m^l)`" or "linear time".
* **Cited external results** are not re-proved and not assumed: Theorem 17 (Tennenholtz)
  and Lemma 27 (Cook).
* **Theorem 1 is narrowed** to the program game whose instructions are the
  three-instruction language `Prog` (play a mixed action; delegate a subset game; test
  whether everybody submitted the same code and punish otherwise), not "any programming
  language"; and program-game execution returns each player a mixed action independent
  of the others given the representatives' sample point.
* **Nothing is executable.** Algorithms 1 and 2 are carried as correctness statements.

## Formalization choices

Each carries a `dd:` tag, defined in `SafeParetoImprovements.lean` and argued in
`notes/scoping.md` §3; the rulings that fixed them are in its §8. The governing rule: where
the paper is ambiguous or defective, take the reading under which its own proofs are
correct, keep the printed reading alongside where it has content, and say so in the
docstring.

**Games** (`dd:universe`, `dd:total-utility`). A game is a finite nonempty subset `S i` of
a fixed per-player universe `𝒜 i`, with a payoff total on all universe profiles. Subset
games and isomorphisms are then first-class and every universally quantified theorem is
stronger. The cost: Lean's `=` on `Game` is not the paper's equality, since two
presentations can differ off the profiles; the paper's equality is `Game.EqOn`, and every
paper-facing statement uses it. Action sets are finite (`Finset`), which the paper never
states but every matrix needs (erratum D23). Dominance, mixed strategies and Nash
equilibrium are EconCSLib's through one bridge `Game.toStrategic`.

**Representatives** (`dd:representatives`). The paper compares `Π(Γ)` and `Π(Γˢ)` at the
same sample point, so all the `Π(Γ)` are jointly distributed: a sample point is one
complete way the representatives could behave, a function from games to outcomes
(`Play`), and `Representatives` adds a probability measure. No rationality is built in;
Assumptions 1 and 2 are separate predicates. Assumption 1 is rendered as the paper's
outcome correspondence (removing a dominated action leaves the play unchanged), Assumption
2 with the isomorphism existential.

**Certainty is a filter** (`dd:certainty`). §3–§4 use only that certainty is preserved by
weakening and by conjunction, so Definitions 1–4, Lemma 2, Theorem 3, Assumptions 1–2 and
Propositions 5–8 are stated for an arbitrary filter `L` ("with certainty" is `∀ᶠ ω in L`,
"with positive probability" `∃ᶠ ω in L`), which strengthens the universally quantified
nodes; probability one is the instance `ae μ`, recovered by iffs. At the trivial filter
every SPI statement is vacuous, so existence and strictness statements carry their filter
explicitly (`∃ᶠ` hypotheses where the print states them, `[L.NeBot]` where it does not).

**Isomorphisms** (`dd:iso`) are per-player bijections with strictly positive scaling; the
paper leaves both unstated and needs both (erratum D5).

**The book** (`dd:book`). §4.4.3's sketch that Assumptions 1 and 2 are jointly
satisfiable is a theorem: representatives who look up each reduced game's isomorphism
class in a book of pages satisfy both at every sample point, with the page distribution a
parameter.

**Reduction and Definition 5** (`dd:derivation`, `dd:nontrivial`). Iterated strict
elimination has a canonical normal form (Lemma 19, the diamond property Lemma 20,
Church–Rosser). Definition 5's chain of eliminations and isomorphisms is an inductive
relation `Game.Deriv`; Lemma 21 is its normal form (the printed length bound is false,
erratum D14, and not rendered), and soundness turns a derivation into an SPI under
Assumptions 1–2. The printed non-triviality clause "the reductions are not equal" is
satisfied by any payoff shift, making the printed plain and unilateral problems
constant-true (erratum D13); the carriers require the reduced *action sets* to differ, the
reading Appendix D's hardness proof uses, with the printed forms kept alongside.

**Program games** (`dd:program-game`, `dd:exec-kernel`, `dd:code-eq`). Appendix A's
program game is an interface `ProgramGame Γ₀ R` — instructions per player, an execution
kernel giving each player a mixed action at each sample point of the representatives,
EconCSLib's Nash equilibrium as program equilibrium. Proposition 18 is proved once over the
interface from Algorithm 2's two semantic properties and instantiated at the language
`Prog`, where code equality is classical. Algorithm 2's punishment index is corrected
(erratum D15), and the deviator's payoff is bounded by the threat point from above
(erratum D8). Threat points exist by compactness.

**Coordination** (`dd:feasible`, `dd:room`). `C(Γ)` is the paper's formula (payoffs of
correlated strategies), proved equal to the convex hull of the pure payoffs. Token games
carry both the representatives' payoff `uˢ` and the original players' assignment
`uᵉ ∈ C(Γ)`. Fresh token actions are a hypothesis `Game.HasRoom`, supplied over universes
with infinite room; over a finite universe the class of token games can be empty, which is
why Proposition 16's game lives over `CAct ⊕ ℕ` and is also stated label-free. Definition 7
reads "strict" into its body (erratum D10). Lemma 13 copies `Γ` itself with `uᵉ` along
whichever isomorphism of reductions Assumption 2 supplies, needs Assumption 1 in addition
to the printed "under Assumption 2", and is stated on the support of `Π(Γ)` where its
conditional expectations exist (erratum D7). Corollary 14 is carried as the
characterization the paper omits: the achievable set is the weighted Minkowski sum
`∑ₐ P(Π(Γ)=a) • {y ∈ C(Γ) | y ≥ u(a)}`, hence convex, compact and a polytope.

**Complexity** (`dd:complexity`). Certificates are tuples of injections `Aʳᵉᵈᵢ ↪ Aᵢ`;
Propositions 23 and 25 say each decision problem holds iff some certificate passes the
appendix's checks, with the non-triviality check the printed algorithms omit restored
(erratum D17). Lemma 28's hardness games follow Table 9 where it disagrees with the printed
formula (erratum D18) and assume `0 < ε` (erratum D21).

**Defects found in the paper.** Twenty-four, in `notes/paper-errata.md` with extraction
line numbers and counterexamples where the claim is false. Those that change a Lean
statement: D1, D2, D5, D8, D10, D12, D13, D15, D17, D18, D21, D23.

## Beyond the paper: participation and foreknowledge independence

The CLR research agenda asks two things of an SPI implementation that the paper does not
name: a player who declines the scheme is met with the baseline play, not a punishment
(participation independence), and a player behaves the same towards a non-participant
whether or not she knew in advance (foreknowledge independence).

* **Execution level** (`Independence.lean`, `dd:default-instr`): over any `ProgramGame`,
  a default instruction executes as the baseline `Π(Γ₀)`; PI and FI compare the mixed
  action realized towards a drop-out. The *fallback* profile (comply with `Γˢ` when
  everybody submits the same code, otherwise the baseline) executes the SPI, is
  participation independent, and is a program equilibrium whenever each player's expected
  ex-post best reply to the baseline is at most her SPI payoff (a sufficient criterion);
  Algorithm 2 is not participation independent in the Demand Game.
* **Program-choice level** (`FullStrategy.lean`, after DiGiovanni's agenda, Appendix
  B.1–B.2): SPIs as transformations of program profiles, full strategies, demand
  preservation, and PI/FI through the two counterfactual program choices, rendered as a
  *choice model* over the other agents' programs. DiGiovanni's renegotiation example (B.4)
  is worked in `Examples/Renegotiation.lean` with its pseudocode as the execution model,
  including the "PI but not FI" agent at both levels.
* Not rendered: surrogate goals (B.3); a general bridge between the two levels.

## Verifying and reading

```
lake build SafeParetoImprovements APITests AxiomAudit
python3 scripts/check-safe-pareto-improvements-nodes.py
python3 scripts/lint_paper_labels.py
python3 scripts/check_paper_wiring.py
```

`AxiomAudit.lean`'s `SPI-INVENTORY` block names every declaration under
`#assert_axioms_clean` and freezes the field names of the boundary structures. The node
checker prints which nodes lack a carrier (Theorem 15, Lemma 27). The statements were
audited in nine fresh-context adversarial rounds from two model families, with the
pre-publication round blind to this project's own conclusions.

| where | what |
|---|---|
| `SafeParetoImprovements/API.lean` | the consumer import: the paper's vocabulary mapped to the supported Lean names |
| `APITests/SafeParetoImprovements.lean` | client-style tests using only that import |
| `SafeParetoImprovements.lean` | the `dd:` glossary and file map |
| `KNOWLEDGE.md` | correspondence table, settled decisions, pitfalls, for maintainers |
| `notes/scoping.md` | rationale for every choice (§3) and the rulings (§8) |
| `notes/paper-errata.md` | the 24 defects |
| `docs/trust-surface.html` | the generated read-through page |
