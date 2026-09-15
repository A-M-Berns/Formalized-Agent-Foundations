# Safe Pareto Improvements for Delegated Game Playing — Lean formalization

This directory is a Lean 4 formalization of the paper *Safe Pareto Improvements for
Delegated Game Playing* by Caspar Oesterheld and Vincent Conitzer (Autonomous Agents and
Multi-Agent Systems, 2022, doi
[10.1007/s10458-022-09574-6](https://doi.org/10.1007/s10458-022-09574-6)). It is built on
Mathlib and on the game-theory library EconCSLib. It also contains a layer that goes beyond
the paper: definitions and worked examples for participation independence and
foreknowledge independence, two properties of SPI implementations that the CLR research
agenda asks about.

**Status.** The paper has 37 numbered nodes (definitions, assumptions, lemmas,
propositions, theorems and one corollary). 35 of them have a proved Lean statement whose
docstring names that node. The two that do not are Theorem 15, which has been deferred by
ruling and will stay deferred, and Lemma 27, which is Cook's theorem: the paper cites it
and so do we, without re-proving it and without assuming it as an axiom. There is no
`sorry` anywhere in the library, and no axiom beyond Lean's three standard ones. All 854
public declarations are named on the axiom gate. The registry status stays `in-progress`
until the human read-through of the statement surface has been done.

## The paper

Two principals each delegate the playing of a normal-form game `Γ` to a representative.
The principals cannot predict how the representatives will play, but they can constrain
it: each principal may instruct their representative to play a *subset game* `Γˢ` instead,
meaning a game with restricted action sets and possibly different payoffs. The subset game
`Γˢ` is a **safe Pareto improvement** (SPI) on `Γ` if the outcome of playing `Γˢ` is at least
as good for every principal as the outcome of playing `Γ`, with certainty, where "good" is
measured by the original payoff `u` and `Π(Γ)` denotes whatever the representatives would
play in `Γ`.

* Section 3 defines SPIs, strict SPIs and unilateral SPIs (Definitions 1 and 2) and shows
  that every SPI is played in some program equilibrium of the delegation game (Theorem 1,
  proved in Appendix A).
* Section 4 introduces outcome correspondences between games (Definition 3 and Lemma 2)
  and proves the central result, Theorem 3: `Γˢ` is an SPI on `Γ` exactly when there is a
  Pareto-improving outcome correspondence from `Γ` to `Γˢ` (Definition 4). It then states
  two behavioural assumptions about the representatives, namely that they never play
  strictly dominated actions (Assumption 1) and that they play isomorphic games
  isomorphically (Assumption 2), under which SPIs can be derived (Lemma 4 and the worked
  examples in Propositions 5 to 8). It closes with the SPI decision problem (Definition
  5), which is NP-complete (Theorem 9, proved in Appendix D) and has a search bound
  (Proposition 10).
* Section 5 studies SPIs under improved coordination: token games and perfect-coordination
  SPIs (Definitions 6 and 7), Algorithm 1 for finding them (Lemma 11 and Proposition 12),
  the structure of the expected payoffs that can be safely achieved (Lemma 13 and
  Corollary 14), a geometric characterization for two players (Theorem 15), and an example
  showing the limits of the approach (Proposition 16).
* Section 6 discusses the SPI selection problem in prose and contains no numbered results.

## What is formalized

The table lists every Lean file in the library, in the order in which its contents are
built up. For a file that carries paper nodes, the middle column names them and the right
column names the Lean declarations that state them. For a file that carries no node, the
middle column says which part of the paper it supports, and the right column describes
its contents.

| file | paper nodes | Lean |
|---|---|---|
| `Play.lean` | Definitions 1 and 2 | `Play.IsSPI` and `Play.IsStrictSPI` are Definition 1; `Game.Unilateral` and `Play.IsUnilateralSPI` are Definition 2. |
| `Correspondence.lean` | Definition 3, Lemma 2 (items 1 to 7), Definition 4, **Theorem 3** | `Play.Corresponds` is Definition 3. The seven items of Lemma 2 are `Play.corresponds_id`, `Play.Corresponds.inv`, `Play.Corresponds.trans`, `Play.Corresponds.mono_rel`, `Play.corresponds_allRel`, `Play.Corresponds.ne_of_at_eq_empty` and `Play.Corresponds.ne_of_inv_at_eq_empty`. `Play.ParetoImprovingCorrespondence` is Definition 4, and `Play.isSPI_iff_exists_paretoImprovingCorrespondence` is Theorem 3. |
| `Assumptions.lean` | Assumptions 1 and 2 | `Play.SatisfiesA1` and `Play.SatisfiesA2`. |
| `Isomorphism.lean` | Lemma 4, in its weak and its strict form | `GameIso.paretoImproving_of_paretoImproving` and `GameIso.strictlyParetoImproving_of_strictlyParetoImproving`. |
| `Reduction.lean` | Lemmas 19 and 20 | `Game.isStrictlyDominated_erase` is Lemma 19 and `Game.elim_diamond` is Lemma 20. |
| `Derivation.lean` | Definition 5 (all four decision problems), Lemmas 21 and 22 | `Game.Step` and `Game.Deriv` are the derivations of Definition 5. The four decision problems are `Game.SPIDecision`, `Game.StrictSPIDecision`, `Game.UnilateralSPIDecision` and `Game.StrictUnilateralSPIDecision`; the versions with the printed non-triviality clause are kept alongside them under the suffix `Printed`. `Game.Deriv.exists_normalForm` is Lemma 21 and `Game.exists_paretoImproving_normalForm` is Lemma 22. |
| `Examples/PrisonersDilemma.lean` | Proposition 5 | `Examples.prisonersDilemma_isStrictSPI`. |
| `Examples/DemandGame.lean` | Proposition 6 | `Examples.demandGame_isSPI` is the weak clause and `Examples.demandGame_isStrictSPI` the strict clause. |
| `Examples/Temptation.lean` | Proposition 7 | `Examples.temptation_isStrictSPI`. |
| `Examples/ComplicatedTemptation.lean` | Proposition 8 | `Examples.complicatedTemptation_isUnilateralSPI`. |
| `Instruction.lean` | **Theorem 1**, **Proposition 18** | `Prog.exists_programEquilibrium_plays` is Theorem 1 and `Prog.algorithm2_isProgramEquilibrium` is Proposition 18. |
| `Coordination.lean` | **Definition 6**, Lemma 11 | `TokenGame.IsSPI` and `TokenGame.IsStrictSPI` are Definition 6; `Game.paretoOptimalIn_feasible_iff` is Lemma 11. |
| `PerfectCoordination.lean` | **Definition 7**, **Proposition 12** | `Play.StrictPerfectCoordinationSPIDecision` is Definition 7 and `Representatives.strictPerfectCoordinationSPIDecision_iff` is Proposition 12. |
| `Characterization.lean` | **Lemma 13**, **Corollary 14** | `Representatives.exists_reassignment_condExp_eq` is Lemma 13. Corollary 14 is carried by `Representatives.achievable_eq_improvementSum` (the formula for the achievable set) together with `convex_achievable`, `isCompact_achievable` and `isPolytope_achievable`. |
| `Examples/Chicken.lean` | **Proposition 16** | `Examples.chicken_no_perfectCoordinationSPI`. |
| `Complexity.lean` | **Propositions 23 to 26**, **Proposition 10** | Propositions 23 and 25 are the four certificate characterizations `Game.spiDecision_iff_certificate`, `Game.strictSPIDecision_iff_certificate`, `Game.unilateralSPIDecision_iff_certificate` and `Game.strictUnilateralSPIDecision_iff_certificate`. Propositions 24 and 26, and with them Proposition 10, are the search bounds `Game.spiDecision_search` and `Game.unilateralSPIDecision_search`. |
| `Hardness.lean` | **Definition 8**, **Lemma 28**, **Theorem 9** | `Hardness.SubgraphIsoProblem` is Definition 8. Lemma 28 is the four reductions `Hardness.subgraphIsoProblem_iff_spiDecision`, `Hardness.subgraphIsoProblem_iff_strictSPIDecision`, `Hardness.subgraphIsoProblem_iff_unilateralSPIDecision` and `Hardness.subgraphIsoProblem_iff_strictUnilateralSPIDecision`. `Hardness.theorem9` is Theorem 9. |
| `Game.lean` | the unnumbered vocabulary of Section 2 | Games over a fixed action universe, the paper's notion of equality of games (`Game.EqOn`), subset games, strict dominance, and the bridge `Game.toStrategic` to EconCSLib's strategic games. |
| `Ordering.lean` | the unnumbered relations of Section 4.2 | The relations the paper writes `R` and `⪰`, obtained by quantifying the outcome correspondence away. |
| `Representatives.lean` | the probabilistic model of Section 3 | The structure `Representatives`, which packages a play family with a probability measure; the realization lemmas `isSPI_iff`, `isStrictSPI_iff` and `corresponds_iff`, which show that at probability one the filter-level definitions unfold to the paper's printed statements; and the support of the play. |
| `Book.lean` | the consistency argument of Section 4.4.3 | The book representatives, which satisfy Assumptions 1 and 2 at every sample point: the structure `Book`, the books `Book.const`, `Book.prescribed`, `Book.prescribedRandom` and `Book.varying`, and the theorem `exists_representatives_satisfiesA1_satisfiesA2`. |
| `TwoPlayer.lean` | none | The player type `Two` and the lemmas that turn the general set-based definitions into finite checks over a payoff table. Theorem 9 and all the examples are stated over it. |
| `ProgramGame.lean` | the unnumbered setup of Appendix A | Mixed strategies and expected payoffs, the threat point `Game.threatPoint` and the minimax profile `Game.minimax`, the interface `ProgramGame` with its notion of program equilibrium `IsProgramEquilibrium`, Proposition 18 proved over that interface as `isProgramEquilibrium_of_algorithm2`, and the best-reply value `Game.bestReply`. |
| `Polytope.lean` | none | Polytopes as convex hulls of finite sets, and the fact that cutting a polytope by a half-space or an orthant gives a polytope (`IsPolytope.inter_halfspace`, `IsPolytope.inter_Ici`). Corollary 14 needs this and Mathlib does not have it. |
| `Independence.lean` | beyond the paper | The execution-level definitions of participation independence and foreknowledge independence: `ProgramGame.DefaultInstr`, `ProgramGame.ParticipationIndependent`, `ProgramGame.Policy` and `ProgramGame.ForeknowledgeIndependent`; the fallback instruction `Prog.fallback` and the theorem `Prog.fallback_isProgramEquilibrium`. |
| `FullStrategy.lean` | beyond the paper | The program-choice-level definitions after DiGiovanni: `IsSPITransformation`, `FullStrategy`, `ChoiceModel`, `FullStrategy.DemandPreserving`, `FullStrategy.ParticipationIndependent`, `FullStrategy.ForeknowledgeIndependent`, and the theorem `participationIndependent_of_simultaneous`. |
| `API.lean` | none | The consumer import. It imports every library module and maps the paper's vocabulary to the supported Lean names. |
| `Examples/Witnesses.lean` | none | Play families at which Propositions 5 to 8 have all their hypotheses satisfied, so that their conclusions are actually reached; yes-instances of the repaired Definition 5 problems; and the representatives `unitRepresentatives`. |
| `Examples/Coin.lean` | none | The fair coin on `Bool`, used by the examples that need a play family with real randomness. |
| `Examples/ProgramGameWitnesses.lean` | none | Theorem 1's hypotheses satisfied twice, once by deterministic representatives in the Prisoner's Dilemma and once by random representatives in the Demand Game; witnesses that the participation and foreknowledge independence predicates are neither always true nor always false; and the proof that Algorithm 2 is not participation independent in the Demand Game. |
| `Examples/IndependenceExamples.lean` | none | The fallback profile shown to be a participation-independent program equilibrium in the Prisoner's Dilemma and in the Demand Game at its conflict outcome. |
| `Examples/Renegotiation.lean` | none | DiGiovanni's renegotiation example from Appendix B.4 of the CLR agenda, with its pseudocode as the execution model, and the agent who is participation independent but not foreknowledge independent, at both levels. |
| `Examples/TokenWitnesses.lean` | none | A strict and an equality-only perfect-coordination SPI on a two-by-two game with a fresh token copy, showing Definition 6 is satisfiable. |
| `Examples/DecisionWitnesses.lean` | none | A yes-instance and a no-instance of Definition 7, both obtained through Proposition 12. |
| `Examples/CharacterizationWitnesses.lean` | none | Lemma 13 and Corollary 14 applied with every hypothesis satisfied, and a hand-built play family on which the conditional expectation `condExp` is a genuine average rather than the value at a single point. |
| `Examples/ComplexityWitnesses.lean` | none | Certificates that pass the checks of Propositions 23 and 25 and certificates that fail a specific check; the count of 144 certificates for the Demand Game against the bound of 4096; and Lemma 28 carried through to a yes-instance and a no-instance of the decision problem. |

Every declaration that carries a paper node has a docstring whose last line reads
`Paper node:` followed by the printed node. The script
`scripts/check-safe-pareto-improvements-nodes.py` checks this in both directions: every
cited node is one the paper prints, and every annotated declaration is on the axiom gate.
The docstring also says, in one or two sentences, what the Lean statement changes relative
to the printed one.

## What is not claimed

* **Theorem 15** has no Lean statement. As printed, it projects points onto the strong
  Pareto frontier of the feasible set, and that projection need not exist (this is erratum
  D12). The proof in Appendix E is a sketch, and one of its steps is not a general fact. The
  theorem has been deferred by ruling (RULING 16), and the deferral is the final scope of
  this formalization.
* **No complexity classes and no running times** are proved anywhere. Theorem 9,
  Proposition 10, Lemma 11, Proposition 12, Propositions 23 to 26 and Lemma 28 are carried
  as *qualified* nodes. That means the exact mathematical content of each statement is
  proved: the certificate characterizations of the decision problems, the search bound
  `card ≤ m^l` where `m` is the total number of actions in the game and `l` the total
  number in its full reduction, the linear program of Lemma 11, the correctness of
  Algorithm 1 as an if-and-only-if, and the reductions from subgraph isomorphism. What is
  not proved is anything the paper phrases as "NP-complete", "in polynomial time", "in
  `O(m^l)`" or "in linear time".
* **Two cited results are neither re-proved nor assumed.** Theorem 17 is Tennenholtz's
  folk theorem for program equilibrium, and Lemma 27 is Cook's theorem. The paper cites
  both; the Lean neither proves them nor adds them as axioms.
* **Theorem 1 is proved for one programming language.** The paper states it for "any
  programming language such as Lisp". The Lean proves it for the program game whose
  instructions are the three-instruction language `Prog`: play a mixed action, delegate a
  subset game to the representatives, or test whether everybody submitted the same code
  and punish otherwise. In addition, the execution of a program game returns each player a
  mixed action that is independent of the other players' actions once the representatives'
  sample point is fixed.
* **Nothing is executable.** Algorithms 1 and 2 are present as correctness statements about
  what they compute, not as programs that can be run.

## Formalization choices

Every choice below has a tag of the form `dd:name`. The tags are defined in one line each
in `SafeParetoImprovements.lean` and argued at length in section 3 of `notes/scoping.md`;
the rulings that fixed them are recorded in section 8 of the same note. One rule governs
all of them: where the paper is ambiguous or defective, take the reading under which the
paper's own proofs go through, keep the printed reading alongside it wherever the printed
reading still has content, and say in the docstring what was done.

**Games** (`dd:universe`, `dd:total-utility`). A game is a finite nonempty subset `S i` of
a fixed per-player universe of actions `𝒜 i`, together with a payoff function that is
defined on every profile of the universe, not only on the profiles of the game. Fixing a
universe makes subset games and isomorphisms first-class objects, and it makes every
theorem quantified over games stronger. The cost is that Lean's equality on `Game` is not
the paper's equality of games: two presentations of the same game can differ in their
payoffs at profiles outside the game. The paper's equality is the relation `Game.EqOn`,
and every paper-facing statement uses it rather than Lean's equality. Action sets are
finite, which the paper never states but which every payoff matrix requires (erratum D23).
Strict dominance, mixed strategies and Nash equilibrium are taken from EconCSLib through
a single bridge, `Game.toStrategic`.

**Representatives** (`dd:representatives`). The paper compares `Π(Γ)` with `Π(Γˢ)` at the
same sample point, which only makes sense if the plays of all games are jointly
distributed. So a sample point is one complete way the representatives could behave, that
is, a function from games to outcomes; this is the structure `Play`. The structure
`Representatives` adds a probability measure on the sample space. No rationality is built
into either structure. Assumptions 1 and 2 are separate predicates that a play family may
or may not satisfy. Assumption 1 is rendered as the paper states it, as an outcome
correspondence: removing a strictly dominated action leaves the representatives' play
unchanged. Assumption 2 asks for the existence of an isomorphism along which the plays of
two isomorphic reduced games correspond.

**Certainty is a filter** (`dd:certainty`). The arguments of Sections 3 and 4 use only two
facts about "with certainty": a certain statement stays certain when weakened, and two
certain statements are certain together. These are the axioms of a filter. Definitions 1
to 4, Lemma 2, Theorem 3, Assumptions 1 and 2 and Propositions 5 to 8 are therefore stated
for an arbitrary filter `L` on the sample space, reading "with certainty" as `∀ᶠ ω in L`
and "with positive probability" as `∃ᶠ ω in L`. This makes every universally quantified
node stronger than the printed one. The paper's own instance, probability one, is the
almost-everywhere filter `ae μ`, and the realization lemmas show that at that filter the
definitions become the printed statements. One consequence has to be kept in mind: at the
trivial filter every statement of the form "with certainty" is vacuously true, so every
subset game is an SPI there and no strict SPI exists. For that reason every existence
statement and every strictness statement carries its filter explicitly, as an `∃ᶠ`
hypothesis where the paper states one and as a non-triviality assumption on the filter
where the paper's claim is unconditional.

**Isomorphisms** (`dd:iso`). A game isomorphism is a family of bijections between action
sets, one per player, together with a strictly positive scaling of the payoffs. The paper
leaves both the bijectivity and the strict positivity unstated, and its later results
need both (erratum D5).

**The book** (`dd:book`). Section 4.4.3 sketches an argument that Assumptions 1 and 2 can
be satisfied together: representatives who look up each reduced game's isomorphism class
in a book and play what the book says. This sketch is a theorem in `Book.lean`. The book
representatives satisfy both assumptions at every sample point, and the distribution of
the book's pages is a parameter, so the same construction supplies the representatives
each example needs.

**Reduction and Definition 5** (`dd:derivation`, `dd:nontrivial`). Iterated elimination
of strictly dominated actions has a canonical normal form, proved from Lemma 19 through
the diamond property of Lemma 20 and a Church–Rosser argument. Definition 5 describes a
chain of eliminations and isomorphisms leading from a game to a subset game; in Lean this
chain is the inductive relation `Game.Deriv`. Lemma 21 is its normal form, except that the
printed bound on the length of the normal form is false (erratum D14) and is not rendered.
A soundness theorem turns a derivation into an SPI under Assumptions 1 and 2. The printed
non-triviality clause of Definition 5 says that the full reductions of the two games are
not equal; that clause is satisfied by shifting the payoffs of any subset game, so the
printed plain and unilateral decision problems are true of every game (erratum D13). The
Lean decision problems require instead that the reduced *action sets* differ, which is the
reading the hardness proof of Appendix D actually uses. The printed versions are kept
alongside, with theorems showing they are constant.

**Program games** (`dd:program-game`, `dd:exec-kernel`, `dd:code-eq`). The program game of
Appendix A is an interface, `ProgramGame Γ₀ R`: a type of instructions for each player and
an execution kernel that, given everybody's instructions and a sample point of the
representatives, gives each player a mixed action. Program equilibrium is EconCSLib's Nash
equilibrium of the induced game. Proposition 18 is proved once over this interface, from
two semantic properties of Algorithm 2, and then instantiated at the concrete language
`Prog`, in which code equality is classical. Two corrections to the paper are made along
the way: Algorithm 2's punishment index is repaired (erratum D15), and the deviator's
payoff is bounded from above by the threat point rather than equated with it (erratum
D8). Threat points exist by a compactness argument.

**Coordination** (`dd:feasible`, `dd:room`). The feasible set `C(Γ)` is defined by the
paper's own formula, as the payoffs of correlated strategies, and proved equal to the
convex hull of the pure payoffs. A token game carries two payoff maps, as in the paper:
the payoff `uˢ` the representatives are given, and the assignment `uᵉ` of feasible payoff
vectors to token outcomes for the original players. The paper assumes that fresh token
actions exist; over a fixed universe this is a hypothesis, `Game.HasRoom`, which holds
over any universe with infinitely many spare actions. Over a finite universe the class of
token games can be empty, and an impossibility statement about it would then be vacuous.
That is why Proposition 16's game is placed over the universe `CAct ⊕ ℕ`, and why the
proposition is also stated in a form that mentions no tokens at all. Definition 7 is
printed as the strict problem but its body omits strictness; the Lean reads "strict" into
the body (erratum D10). Lemma 13 replaces a perfect-coordination SPI by an exact token
copy of the game itself, with `uᵉ` defined along whichever isomorphism of reductions
Assumption 2 supplies. It needs Assumption 1 in addition to the printed "under Assumption
2", and it is stated on the support of the play, where the conditional expectations it
speaks of exist (erratum D7). Corollary 14 is carried as the characterization that the
paper says it omits: the set of safely achievable expected payoffs equals the weighted
Minkowski sum `∑ₐ P(Π(Γ)=a) • {y ∈ C(Γ) | y ≥ u(a)}`, from which it follows that the set is
convex, compact and a polytope.

**Complexity** (`dd:complexity`). A certificate is a tuple of injections from the reduced
action sets into the original ones. Propositions 23 and 25 say that each decision problem
holds exactly when some certificate passes the checks of Appendix D, with one check added
that the printed algorithms omit: the non-triviality check, without which the identity
certificate would make every game a yes-instance (erratum D17). The hardness games of
Lemma 28 follow Table 9 of the paper where it disagrees with the printed payoff formula
(erratum D18), and they assume `0 < ε`, which the paper needs and does not state (erratum
D21).

**Defects found in the paper.** Twenty-four defects are recorded in
`notes/paper-errata.md`, grouped by seriousness, each with line numbers into the committed
text extraction and, where the defect is a false claim, a counterexample. Five printed
statements are false or empty as written (D12, D13, D14, D17, D18); three printed proofs
do not establish their claim (D6, D8, D24); the rest are ambiguities resolved by ruling,
missing hypotheses, typos and notational slips, and one false remark in prose. Twelve of
the twenty-four change a Lean statement relative to the print: D1, D2, D5, D8, D10, D12,
D13, D15, D17, D18, D21 and D23.

## Beyond the paper: participation and foreknowledge independence

The CLR research agenda asks two things of an SPI implementation that the paper does not
name. A player who declines to take part in the scheme should be met with the baseline
play rather than with a punishment; this is participation independence. And a player
should behave the same way towards a non-participant whether or not she knew in advance
that they would not participate; this is foreknowledge independence.

* **At the level of execution** (`Independence.lean`, `dd:default-instr`). Over any
  program game, a default instruction per player executes as the paper's baseline play
  `Π(Γ₀)`. Participation independence and foreknowledge independence then compare the
  mixed action a player realizes towards a player who has dropped out. The *fallback*
  profile, in which every player complies with `Γˢ` when everybody has submitted the same
  code and plays the baseline otherwise, executes the SPI, is participation independent,
  and is a program equilibrium whenever each player's expected best reply to the baseline,
  computed sample point by sample point, is at most her expected payoff from the SPI. That
  criterion is sufficient, not necessary. Algorithm 2, by contrast, is not participation
  independent in the Demand Game.
* **At the level of program choice** (`FullStrategy.lean`), following Appendix B of
  DiGiovanni's agenda. An SPI is a transformation of program profiles; a full strategy is
  such a transformation together with the programs it is applied to; demand preservation,
  participation independence and foreknowledge independence are defined through two
  counterfactual program choices, which are rendered as a *choice model* giving each
  agent's program as a function of the other agents' programs. DiGiovanni's renegotiation
  example from Appendix B.4 is worked out in `Examples/Renegotiation.lean`, with his
  pseudocode as the execution model, including the agent who is participation independent
  but not foreknowledge independent.
* Not rendered: surrogate goals (Appendix B.3 of the agenda), and any general relation
  between the two levels beyond their coincidence on the worked example.

## Verifying and reading

The following commands, run from the repository root, check everything that can be
checked mechanically:

```
lake build SafeParetoImprovements APITests AxiomAudit
python3 scripts/check-safe-pareto-improvements-nodes.py
python3 scripts/lint_paper_labels.py
python3 scripts/check_paper_wiring.py
```

The first command elaborates the library, the client tests and the axiom gate. The block
`SPI-INVENTORY` of `AxiomAudit.lean` names every public declaration of the library under
`#assert_axioms_clean`, which fails the build if any of them depends on `sorry` or on an
axiom beyond the standard three, and it freezes the field names of the boundary
structures so that a hypothesis cannot be added to one of them unnoticed. The node
checker reports which numbered nodes have no annotated carrier; at present those are
Theorem 15 and Lemma 27. The statements were audited in nine rounds by fresh-context
adversarial readers drawn from two independent model families, and the pre-publication
round was run without access to this project's own conclusions.

| where | what |
|---|---|
| `SafeParetoImprovements/API.lean` | The consumer import. It maps the paper's vocabulary to the supported Lean names. |
| `APITests/SafeParetoImprovements.lean` | Client-style tests that use only the consumer import. |
| `SafeParetoImprovements.lean` | The root import, with the one-line glossary of every `dd:` tag and a file map. |
| `KNOWLEDGE.md` | The correspondence table, the settled decisions and the pitfalls, written for whoever maintains the code. |
| `notes/scoping.md` | The rationale for every choice, in section 3, and the rulings that fixed them, in section 8. |
| `notes/paper-errata.md` | The twenty-four defects found in the paper. |
| `docs/trust-surface.html` | The generated read-through page, one section per paper in the repository. |
