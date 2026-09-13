# Safe Pareto Improvements for Delegated Game Playing — trust surface

Formalization of Caspar Oesterheld and Vincent Conitzer, *Safe Pareto Improvements for
Delegated Game Playing*, Autonomous Agents and Multi-Agent Systems 36 (2022),
doi [10.1007/s10458-022-09574-6](https://doi.org/10.1007/s10458-022-09574-6); short
version at AAMAS 2021.  Registered as `safe-pareto-improvements` in `scripts/papers.py`,
library `SafeParetoImprovements/`, status **`in-progress`**, milestone **M0**.

This file is the trust surface: what is claimed, what is disclosed, and what is not yet
there.  `SafeParetoImprovements.lean` carries the `dd:` glossary;
`SafeParetoImprovements/notes/scoping.md` is the scoping note with the rationale for every
design decision, the rulings that fixed them (§8), and the codex review (§9).

## What the paper is

Two principals delegate the playing of a normal-form game `Γ` to representatives whose
behaviour `Π(Γ)` they cannot predict but can constrain: each principal may instruct their
representative to play a *subset game* `Γˢ` (restricted action sets, possibly a different
payoff function) instead.  A subset game is a **safe Pareto improvement** (SPI) on `Γ` if
`u(Π(Γˢ)) ≥ u(Π(Γ))` *with certainty* — whatever the representatives would have done.
The paper's spine is:

* §3 — SPIs, strict SPIs, unilateral SPIs (Definitions 1–2); every SPI is played in some
  program equilibrium (Theorem 1, proved in Appendix A).
* §4 — *outcome correspondence* `Γ ∼_Φ Γ'` between games (Definition 3, Lemma 2), the
  keystone **Theorem 3**: `Γˢ` is an SPI on `Γ` iff there is a Pareto-improving outcome
  correspondence from `Γ` to `Γˢ` (Definition 4); two behavioural assumptions on the
  representatives — they never play strictly dominated actions (Assumption 1) and play
  isomorphic games isomorphically (Assumption 2) — under which SPIs can be *derived*
  (Lemma 4, the worked examples Propositions 5–8); and the SPI decision problem
  (Definition 5), NP-complete (Theorem 9, Appendix D), with a search bound (Proposition
  10).
* §5 — SPIs under improved coordination: token games, the perfect-coordination SPI
  (Definitions 6–7), Algorithm 1 and its correctness (Lemma 11, Proposition 12), the
  structure of safely achievable expected payoffs (Lemma 13, Corollary 14), the two-player
  geometric characterization (Theorem 15, Appendix E), and a limiting example
  (Proposition 16).
* §6 — the SPI selection problem, prose only.

## Status: milestone M0

**What is formalized so far**, all at the certainty-filter level (`dd:certainty`) and all
proved — there is no `sorry` in `SafeParetoImprovements/`:

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
| Definition 5 (SPI decision problem, strict and unilateral variants) as a derivation system | `Game.Step`, `Game.Deriv`; repaired non-triviality (`dd:nontrivial`, erratum D13): `Game.SPIDecision`, `Game.StrictSPIDecision`, `Game.UnilateralSPIDecision`; printed, constant-true: `Game.SPIDecisionPrinted`, `…StrictSPIDecisionPrinted`, `…UnilateralSPIDecisionPrinted` | `Derivation.lean` |
| Lemma 21 (normal form of derivations: eliminations, one isomorphism, reverse eliminations; the printed length bound is not rendered, erratum D14) | `Game.Deriv.exists_normalForm` | `Derivation.lean` |
| Lemma 22 (symmetry-free Pareto-improving chain to the reduction of the SPI candidate) | `Game.exists_paretoImproving_normalForm` | `Derivation.lean` |
| **Proposition 18** (Algorithm 2 is a program equilibrium executing `Π(Γˢ)`; the deviator's payoff is *at most* the threat point, erratum D8; Algorithm 2's punishment index repaired, erratum D15) | `Prog.algorithm2_isProgramEquilibrium` | `Instruction.lean` |
| Definition 5, the fourth problem (strict unilateral) | `Game.StrictUnilateralSPIDecision` | `Derivation.lean` |
| **Proposition 23** (the omnilateral algorithm is correct: certificate iffs for the plain and strict problems; "NP time" not rendered, `dd:complexity`; non-triviality check restored, erratum D17) | `Game.spiDecision_iff_certificate`, `Game.strictSPIDecision_iff_certificate` | `Complexity.lean` |
| **Proposition 25** (the unilateral algorithm is correct: certificate iffs with the three checks; the printed "WLOG same action sets for player `i`" discharged by `ElimStar.transfer`) | `Game.unilateralSPIDecision_iff_certificate`, `Game.strictUnilateralSPIDecision_iff_certificate` | `Complexity.lean` |
| **Propositions 24, 26** and **Proposition 10** (the search bound `card ≤ m ^ l`, resp. `n · m ^ l`; "solved in `O(m^l)`" not rendered) | `Game.card_certificate_le`, `Game.spiDecision_search`, `Game.unilateralSPIDecision_search` | `Complexity.lean` |
| **Definition 8** (subgraph isomorphism problem) | `Hardness.SubgraphIsoProblem` | `Hardness.lean` |
| **Lemma 28** (subgraph isomorphism reduces to each of the four SPI problems on the two-player game of Table 10, as an iff; "linear time" and "NP-hard" not rendered; Table 9 followed over the printed formula, erratum D18) | `Hardness.subgraphIsoProblem_iff_spiDecision` and the strict / unilateral / strict-unilateral variants | `Hardness.lean` |
| **Theorem 9** (membership for the four problems together with the reduction, over two-player games; "NP-complete" not rendered) | `Hardness.theorem9` | `Hardness.lean` |
| **Definition 6** (perfect-coordination SPI, strict variant) | `TokenGame.IsSPI`, `TokenGame.IsStrictSPI` | `Coordination.lean` |
| Lemma 11 (Pareto-optimality in `C(Γ)` as a linear program; the polynomial-time clause not rendered, `dd:complexity`) | `Game.paretoOptimalIn_feasible_iff` | `Coordination.lean` |
| Definition 6 witnesses (strict and equality-only perfect-coordination SPIs with `uᵉ` defined along the book's isomorphism) | `Examples.conflictStrictToken_isStrictSPI`, `conflictPlainToken_isSPI` | `Examples/TokenWitnesses.lean` |
| **Definition 7** (strict perfect-coordination SPI decision problem; "strict" read in, RULING 7; per play family, RULING 10) | `Play.StrictPerfectCoordinationSPIDecision` | `PerfectCoordination.lean` |
| **Proposition 12** (Algorithm 1's correctness as an iff, under Assumptions 1–2 and room; the polynomial-time clause not rendered) | `Representatives.strictPerfectCoordinationSPIDecision_iff` | `PerfectCoordination.lean` |
| **Lemma 13** (every perfect-coordination SPI is replaced by an isomorphic copy of the reduced game with `uᵉ` along Assumption 2's isomorphism, same conditional expectations on the support; errata D6, D7) | `Representatives.exists_reassignment_condExp_eq` | `Characterization.lean` |
| **Corollary 14** (the safely achievable expected payoffs: the weighted Minkowski-sum formula, convex, compact, and a polytope) | `Representatives.achievable_eq_improvementSum`, `convex_achievable`, `isPolytope_achievable` | `Characterization.lean` |
| **Proposition 16** (Table 7 over `CAct ⊕ ℕ`, `dd:room`: a Pareto improvement no perfect-coordination SPI achieves; also in label-free form `chicken_no_feasible_dominating_of_mean_cc`; `Π` existential, see `chicken_spi_for_other_representatives`) | `Examples.chicken_no_perfectCoordinationSPI` | `Examples/Chicken.lean` |
| **Theorem 1** (every SPI is played in a program equilibrium of the program game with delegation instructions, given the threat-point guarantee) | `Prog.exists_programEquilibrium_plays` | `Instruction.lean` |
| Proposition 5 (Prisoner's Dilemma, Table 3) | `Examples.prisonersDilemma_isStrictSPI` | `Examples/PrisonersDilemma.lean` |
| Proposition 6 (Demand Game, Tables 1–2), both clauses | `Examples.demandGame_isSPI`, `Examples.demandGame_isStrictSPI` | `Examples/DemandGame.lean` |
| Proposition 7 (Temptation Game, Table 6) | `Examples.temptation_isStrictSPI` | `Examples/Temptation.lean` |
| Proposition 8 (Complicated Temptation Game, Tables 4–5) | `Examples.complicatedTemptation_isUnilateralSPI` | `Examples/ComplicatedTemptation.lean` |

Beside these, without a paper node of their own: the §2 carriers (`Game`, `Game.EqOn`,
subset games, the EconCSLib bridge and strict dominance in `Game.lean`); game isomorphism
(`GameIso`, `Game.Isomorphic`); the §4.2 relations `R` and `⪰` obtained by quantifying the
correspondence away (`Ordering.lean`); the probabilistic model `Representatives` with the
**realization at probability one** — `ae μ` is a filter, non-degenerate for a probability
measure, and Definitions 1 and 3 at `L = ae μ` unfold to the printed statements
(`isSPI_iff`, `isStrictSPI_iff`, `corresponds_iff` in `Representatives.lean`); the
canonical full reduction `Game.reduce` with confluence and uniqueness (`Reduction.lean`);
and the **book representatives** of §4.4.3, proving that Assumptions 1 and 2 are jointly
satisfiable with the page distribution as a parameter (`Book.lean`, `dd:book`); and the
**non-vacuity witnesses** (`Examples/Witnesses.lean`): every Proposition 5–8 conclusion is
reached by a play family that *also* satisfies Assumptions 1 and 2 inside the same
statement, the repaired Definition 5 predicates have proved yes-instances (the Demand Game
and the Complicated Temptation Game) alongside their no-instance, and the strict soundness
result's positive-probability side condition is discharged by the page-varying book
`Book.varying`, which hits every surviving outcome.

Beside these, for Appendix A (`ProgramGame.lean`, `Instruction.lean`): mixed strategies
and expected payoffs are EconCSLib's, the threat point `vᵢ` and the minimax profile
against `i` exist by compactness (`Game.threatPoint`, `Game.minimax`), the program-game
interface `ProgramGame` has EconCSLib's Nash equilibrium as program equilibrium
(`dd:program-game`, `dd:exec-kernel`), Proposition 18 is proved over the interface
(`ProgramGame.isProgramEquilibrium_of_algorithm2`) and instantiated at the instruction
language `Prog` (`dd:code-eq`), and the threat point is metered from above by a pure best
response (`Game.threatPoint_le_of_bestResponse`) and from below by a pure guarantee
(`Game.le_threatPoint_of_guarantee`).  Theorem 1 is carried for the program game whose
instructions are exactly `Prog` — a deliberate narrowing of the paper's "any programming
language", disclosed at the endpoint — and its hypotheses are witnessed twice in
`Examples/ProgramGameWitnesses.lean`: deterministically in the Prisoner's Dilemma and with
a genuinely random `Π(Γ₀)` in the Demand Game (a fair coin, `Book.prescribedRandom`);
the threat-point hypothesis is shown to have content (it fails for the book that plays
`(DM, DM)`).  Beyond the paper, `Independence.lean`
makes participation independence and foreknowledge independence stateable (RULING 9,
`dd:default-instr`): definitions, the dove-ish and punishing `Prog` instructions as
two-sided witnesses (including that Algorithm 2 is *not* participation independent in the
Demand Game), and no theorem about either.

**The complexity nodes** (§4.6, Appendix D.2–D.3; tranche F, design note
`notes/complexity-layer.md`) are carried as *qualified* nodes under RULING 6.
`Complexity.lean` renders Propositions 23 and 25 as certificate characterizations — each
of the four (strict) (unilateral) SPI decision problems holds iff some tuple of injections
`Aʳᵉᵈᵢ ↪ Aᵢ` passes the appendix's checks, with the non-triviality check the printed
algorithms omit restored (erratum D17) — and Propositions 24 and 26 / Proposition 10 as the
bound `card ≤ m ^ l` on the certificate type.  `Hardness.lean` renders Definition 8 and
Lemma 28: subgraph isomorphism reduces to each of the four problems on the two-player games
of Tables 9–10, as an iff, following Table 9 where it disagrees with the printed formula
(erratum D18, RULING 15).  `Hardness.theorem9` conjoins membership and reduction over
two-player games; "NP-complete", "non-deterministic polynomial time", "`O(m^l)`" and
"linear time" are the clauses disclosed as not rendered.  Lemma 27 (Cook) is cited and not
carried (RULING 14), exactly as Theorem 17 is not.

**Not yet formalized:** of §5, only Theorem 15 (deferred, RULING 8); Lemma 20's content
is `Game.elim_diamond`.  Theorem 17 and Lemma 27 are cited external results and are not
carried.

**Consumer readiness.**  There is no `SafeParetoImprovements/API.lean` and no
`APITests/SafeParetoImprovements.lean` yet; both are mandatory before the registry status
can become `completed` (root `CLAUDE.md`, *Consumer readiness is part of paper
completion*), as are a human read-through and a fresh-context audit.

## Scope

Requested scope: "everything before §8" — read (RULING 0, assumed rather than confirmed)
as the whole main text §2–§6 with the appendix proofs of every main-text theorem, the
appendix-only nodes in scope exactly insofar as Theorem 9 is.  Condensed from
`notes/scoping.md` §1:

| § | nodes | status |
|---|---|---|
| 2 | unnumbered: game, subset game, strict dominance, Pareto improvement, isomorphism | carriers with `§2` provenance, no node label |
| 3, 3.1 | Definitions 1–2 | **in, landed** |
| 3.2 | Theorem 1 (proof App. A via Proposition 18; Theorem 17 cited) | **in, landed** (`Prog.exists_programEquilibrium_plays`, `dd:program-game`) |
| 4.1 | unnumbered: multivalued functions | Mathlib `SetRel` |
| 4.2–4.3 | Definition 3, Lemma 2, Definition 4, **Theorem 3** | **in, landed** |
| 4.4 | Assumptions 1–2, Lemma 4, consistency of A1 + A2 (unnumbered) | **in, landed** (`dd:book` for the consistency) |
| 4.5 | Propositions 5–8 (examples) | **in, landed**; concrete games double as witnesses |
| 4.6 | Definition 5, Theorem 9, Proposition 10 | Definition 5 **landed** as a derivation system with soundness (`Play.isSPI_of_deriv`); Theorem 9 / Proposition 10 **landed** as qualified nodes (RULING 6): `Complexity.lean`, `Hardness.lean`, `Examples/ComplexityWitnesses.lean` |
| 5 | Definitions 6–7, Lemma 11, Proposition 12, Lemma 13, Corollary 14, Theorem 15, Proposition 16 | **all landed except Theorem 15** (deferred, RULING 8): `Coordination.lean`, `PerfectCoordination.lean`, `Characterization.lean`, `Polytope.lean`, `Examples/{Chicken,TokenWitnesses,DecisionWitnesses}.lean`; Lemma 11 / Proposition 12 complexity clauses qualified; `dd:feasible`, `dd:room`, RULINGS 10–13b |
| 6 | no nodes | prose only |
| App. A | Proposition 18; Theorem 17 (Tennenholtz 2004) | Proposition 18 **landed** (`Prog.algorithm2_isProgramEquilibrium`); Theorem 17 cited external, **not** re-proved |
| App. B | no nodes (Sen / Raub discussion) | out |
| App. D | Lemmas 19–22, Propositions 23–26, Definition 8, Lemma 27 (Cook 1971, cited), Lemma 28 | **all landed** except Lemma 27 (cited external, RULING 14) — Lemmas 19, 21, 22 in `Reduction.lean` / `Derivation.lean` (Lemma 20 is absorbed by the confluence proof), Propositions 23–26 in `Complexity.lean`, Definition 8 and Lemma 28 in `Hardness.lean` |

Open rulings (`notes/scoping.md` §8): scope confirmation (0); Definition 7's missing
"strict" (7); Theorem 15's projections onto `C(Γ)` rather than the strong frontier (8);
the instruction layer of tranche E (9); the §5 modelling walk-through (10).

## Numbering and provenance

The paper numbers on **global counters that never reset**: Definitions on one
(`Definition 1` … `Definition 8`), Assumptions on another (`Assumption 1`,
`Assumption 2`), and Theorem, Lemma, Proposition and Corollary on a single shared counter
(`Theorem 1`, `Lemma 2`, `Theorem 3`, `Lemma 4`, `Proposition 5`, … `Lemma 28`).  Examples
are headed `Proposition (Example) n` and are cited as `Proposition n`.  The paper labels
nothing, so the printed kind-and-number pair is the provenance key, and the kind is part
of it.  An annotation is a docstring's last line, ``Paper node: `Lemma 4` ``; the paper's
item references (`Lemma 2.2`) name items, not nodes.

There is **no arXiv record and no TeX source** (arXiv 2403.05103 is a later paper by the
same authors).  The committed source is therefore
`notes/oesterheld-conitzer-2022-spi.txt`, a `pdftotext -layout` extraction of the
committed PDF `notes/oesterheld-conitzer-2022-spi.pdf`, and
`scripts/check-safe-pareto-improvements-nodes.py` reads the printed numbers off its header
lines (scheme `printed-global`, `source_format: text-extraction`, parser in
`scripts/paper_nodes.py`).  Because the extraction is itself provenance-bearing, the
checker asserts that exactly **37** nodes are derived — 8 Definitions, 2 Assumptions, 4
Theorems, 10 Lemmas, 12 Propositions, 1 Corollary — so a re-extraction that mangles a
header fails rather than silently shrinking the set of nodes an annotation may name.  The
paper prints 38 headers; `Theorem 17`'s is torn across two lines by a display delimiter in
the extraction and is deliberately not parsed (it is a cited external result the
formalization does not carry).  `Lemma 4` is printed twice (§4.4.2 and Appendix C) and one
cross-reference in the proof of Lemma 21 is header-shaped; the parser keeps the first
occurrence of each id.

Every annotated declaration is listed in `AxiomAudit.lean`'s `SPI-INVENTORY` block
(`#assert_axioms_clean`) or staged in its `SPI-PENDING` block (statement final, proof
pending; empty at M0).  `scripts/lint_paper_labels.py` requires every `theorem` in this
library to name a result node (`Theorem`/`Lemma`/`Proposition`/`Corollary`, bare integer).

## Standing design decisions

Full rationale in `notes/scoping.md` §3, rulings in §8, one-line glossary in
`SafeParetoImprovements.lean`.

* **`dd:universe`** — every game lives over a fixed per-player action universe
  `𝒜 : N → Type*`; a `Game` is a finite nonempty subset of each `𝒜 i` with a payoff
  function.  A disclosed narrowing of the paper's unspecified quantification domain, in
  the direction that makes every theorem stronger.
* **`dd:total-utility`** — `Game.u` is total on universe profiles, so **Lean `=` on `Game`
  is not the paper's equality of games**.  The paper's equality is `Game.EqOn` (same
  strategy sets, payoffs agreeing on the smaller game's profiles — forced by Definition
  2's `uˢᵢ = uᵢ` across different domains), and every paper-facing statement uses it.
* **`dd:certainty`** — "with certainty" is a filter on the sample space; Definitions 1–4,
  Lemma 2 and Theorem 3 are stated at that generality and are **strengthened** relative to
  the printed statements (RULING 2, option (i)).  The paper's probability-one instance is
  `ae μ`, realized by iffs in `Representatives.lean`, never by a second copy of a theorem.
* **`dd:representatives`** — the representatives are a random solver: one sample space,
  `play : Game N 𝒜 → Ω → outcome` with membership everywhere and measurable outcome
  fibers; no rationality built in.  Assumptions 1–2 are separate predicates, read
  literally as "for every game, with certainty".
* **`dd:iso`** — game isomorphisms are per-player **bijections** with **strictly positive**
  scaling; both readings are forced by later use (erratum D5).
* **`dd:book`** — joint satisfiability of Assumptions 1 and 2 is a theorem (N±), with the
  page distribution parametric (RULING 5).
* **`dd:derivation`**, **`dd:program-game`**, **`dd:complexity`** — see the glossary in
  `SafeParetoImprovements.lean`; `dd:complexity` is now realized for every complexity node
  (Lemma 11, Proposition 12, Propositions 23–26, Proposition 10, Lemma 28, Theorem 9), each
  a qualified node whose docstring names the clause not rendered.

Payoffs are in `ℝ`; players are finite; action sets are finite and nonempty.  The §2
vocabulary comes from EconCSLib (pinned in `lakefile.lean`, RULING 1) through the bridge
`Game.toStrategic`, with each notion characterised by a lemma that reads as the paper's
sentence.

## Errata

The erratum file is [`notes/paper-errata.md`](notes/paper-errata.md): twelve source defects
D1–D12 found on the first reading, several confirmed or corrected by the codex review
(`notes/codex-review-2026-09-04.md`), and six more (D13–D18) found while formalizing.  In
brief:

* **D1** Definition 1's strictness clause compares `uᵢ(Π(Γˢ))` with itself; read
  `uᵢ(Π(Γˢ)) > uᵢ(Π(Γ))`.
* **D2** Definition 4 writes `Γ'` for `Γˢ` and `→` for `⊸`; Lemma 4's hypothesis that `Γ'`
  is a subset game of `Γ` is missing.
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
* **D18** Table 9 and the printed payoff formulas disagree at eight corner entries (`0`
  vs. `ε`), and the disagreement decides whether the unilateral half of Lemma 28's first
  claim holds; the carriers follow the table (RULING 15).

The `Level` column of `notes/paper-errata.md` is authoritative.  Statement-level and
carried as **disclosures** at the Lean statements: **D1, D2, D5, D8, D10, D12, D13** (the
list `KNOWLEDGE.md` keeps), together with **D15** at Algorithm 2, **D17** at the
certificate checks and **D18** at Table 9.  Also statement-level but either printing typos
or clauses simply not rendered: D7 (rendered on `supp Π(Γ)`), D9, D11 (Proposition 23),
D14 (the `m ≤ k` bound).  D3, D4, D6 and D16 are proof- or notation-level only.
