/-
# Safe Pareto Improvements for Delegated Game Playing (Oesterheld & Conitzer, 2022)

This is the root import for the formalization of Caspar Oesterheld and Vincent Conitzer,
*Safe Pareto Improvements for Delegated Game Playing*, Autonomous Agents and Multi-Agent
Systems 36 (2022), doi 10.1007/s10458-022-09574-6 (short version AAMAS 2021).

This module is the *aggregator*: it re-exports every file of the formalization and carries
the `dd:` glossary, but it is not a curated boundary and says nothing about what is
supported.  The formalization is at milestone M0 and registered `in-progress` in
`scripts/papers.py`; there is no `SafeParetoImprovements/API.lean` consumer entrypoint
yet, and the completed-status flip is gated on one (root `CLAUDE.md`, *Consumer readiness
is part of paper completion*).

The paper is the specification:
`SafeParetoImprovements/notes/oesterheld-conitzer-2022-spi.pdf` is the authors' copy of the
article ("equal to the JAAMAS version except for formatting", 57 pp.) and
`SafeParetoImprovements/notes/oesterheld-conitzer-2022-spi.txt` is the committed
`pdftotext -layout` extraction that the node checker reads.  There is no arXiv record and
no TeX source in hand, so the printed node numbers are the provenance keys.  The paper
numbers on **global counters that never reset**: Definitions on one (`Definition 1` …
`Definition 8`), Assumptions on another (`Assumption 1`, `Assumption 2`), and Theorem,
Lemma, Proposition and Corollary on a single shared counter (`Theorem 1`, `Lemma 2`,
`Theorem 3`, `Lemma 4`, `Proposition 5`, … `Lemma 28`).  Examples are set as
`Proposition (Example) n` and are cited as `Proposition n`.  `Theorem 17` (Tennenholtz
2004) and `Lemma 27` (Cook 1971) are cited external results; the former's header is torn
by a display delimiter in the extraction and is deliberately not in the node set
(`scripts/check-safe-pareto-improvements-nodes.py`).

Paper-facing declarations follow the repository's labeling convention: the docstring ends
in a paper-node line naming the printed kind and global number, backticked (the marker
line of `Play.SatisfiesA1` in `Assumptions.lean` names `Assumption 1`).  The kind is part
of the key —
`Lemma 2` and `Definition 2` are different nodes — and the paper's item references
(`Lemma 2.2`) name items, not nodes: the annotation says `Lemma 2` and the docstring names
the item in prose.  That annotation is reserved for the audited surface; internal lemmas
cite the paper in prose instead.  `theorem` is reserved for the paper's numbered results,
paper-facing `def`s and `structure`s (Definitions, Assumptions) carry the annotation too,
and supporting mathematics is stated as `lemma`.  Every annotated declaration is listed in
`AxiomAudit.lean`'s `SPI-INVENTORY` block (axiom-checked) or staged in its `SPI-PENDING`
block (statement final, proof pending); `scripts/check-safe-pareto-improvements-nodes.py`
enforces both directions.

**Substrate.**  Games are stated over a fixed per-player action universe (`dd:universe`)
with payoffs in `ℝ`; the §2 game-theoretic vocabulary (strict dominance, and later best
response, Nash equilibrium, mixed strategies) is *not* re-defined here but taken from
EconCSLib's `StrategicGame` through the bridge `Game.toStrategic`
(`SafeParetoImprovements/Game.lean`), pinned as a dependency in `lakefile.lean`.
Paper-facing statements never name an EconCSLib notion directly; each is characterised by
a lemma that reads as the paper's sentence (`strictlyDominates_iff`).  Multivalued
functions (§4.1) are Mathlib's `SetRel`, composed diagrammatically — `Φ ○ Ψ` is the
paper's `Ψ ∘ Φ`.

## `dd:` glossary — standing design decisions

A `dd:` tag records a choice made by the formalization rather than by the paper.  The
rationale for each lives in `SafeParetoImprovements/notes/scoping.md` §3, and the rulings
that fixed them in §8 of the same note; `SafeParetoImprovements/README.md` is the trust
surface.  Tags marked *realized* are in force in the Lean below; tags marked *planned* are
ruled on but not yet carried by any declaration.

* `dd:universe` — *realized* (`Game.lean`).  Every game a given set of representatives can
  be asked to play lives over one fixed per-player action universe `𝒜 : N → Type*`; a
  `Game` is a finite nonempty subset of each `𝒜 i` plus a payoff function.  A subset game
  is literally `Sˢ i ⊆ S i`, Assumption 1's `Aᵢ − {ãᵢ}` is `Finset.erase`, outcomes of all
  games share one type, and the paper's "`A₁, …, Aₙ` pairwise disjoint" is automatic.  A
  disclosed narrowing of the paper's unspecified quantification domain, in the direction
  that makes the theorems stronger.
* `dd:total-utility` — *realized* (`Game.lean`).  `Game.u` is total on universe profiles,
  so Lean's `=` on `Game` is **not** the paper's equality of games; the paper's equality
  (agreement of strategy sets and of payoffs on the smaller game's profiles, forced by
  Definition 2's `uˢᵢ = uᵢ` across different domains) is `Game.EqOn`, and every
  paper-facing statement uses it.
* `dd:certainty` — *realized* (`Play.lean`, `Correspondence.lean`, `Representatives.lean`).
  "With certainty" is a filter `L` on the sample space: `∀ᶠ ω in L`, and "with positive
  probability" is `∃ᶠ ω in L`.  Definitions 1–4, Lemma 2 and Theorem 3 are stated at that
  generality (RULING 2, option (i)) and are *strengthened* relative to the printed ones;
  the paper's own instance, probability one, is `ae μ`, and `Representatives.lean` proves
  the realization iffs (`isSPI_iff`, `isStrictSPI_iff`, `corresponds_iff`) rather than a
  second copy of any theorem.
* `dd:representatives` — *realized* (`Play.lean`, `Representatives.lean`).  The
  representatives are a **random solver**: one sample space on which every `Π(Γ)` is
  defined, `play : Game N 𝒜 → Ω → (∀ i, 𝒜 i)` with membership in the game's profiles
  everywhere and measurable outcome fibers, and nothing else built in.  Assumptions 1 and 2
  are separate predicates (`Play.SatisfiesA1`, `Play.SatisfiesA2`); "under Assumptions 1
  and 2" is a quantifier over play families satisfying them.
* `dd:iso` — *realized* (`Isomorphism.lean`).  A game isomorphism is a per-player family of
  **bijections** `Aᵢ → A'ᵢ` with **strictly positive** scaling `λᵢ > 0` and shifts `cᵢ`,
  carried as data (`GameIso`); both readings are forced by later use and recorded as
  errata D5.
* `dd:book` — *realized* (`Book.lean`).  The joint satisfiability of Assumptions 1 and 2
  (§4.4.3, which the paper leaves informal) is a theorem, not a remark: the "book"
  representatives fully reduce a game (`Game.reduce`, `Reduction.lean`), read a random
  page for the reduced game's isomorphism class, and translate back through a chosen
  isomorphism.  The page distribution is a parameter, so the same construction serves
  Proposition 16 and the strictness clause of Proposition 6.
* `dd:derivation` — *realized* (`Derivation.lean`).  Definition 5's "(strict) (unilateral)
  SPI decision problem" is a syntactic derivation system — single applications of
  Assumption 1, Assumption 1 in reverse via Lemma 2.2, and Assumption 2 with the chosen
  isomorphism recorded — whose semantics is SPI soundness through Lemma 4 and Theorem 3
  (`Play.isSPI_of_deriv` and the strict/unilateral variants), not "the composite
  correspondence holds" (which is false).  Lemmas 21–22 are carried qualitatively
  (`Deriv.exists_normalForm`, `exists_paretoImproving_normalForm`); the printed length bound
  `m ≤ k` is not rendered and is false as printed (erratum D14).
* `dd:nontrivial` — *realized* (`Derivation.lean`).  Definition 5's non-triviality clause is
  read as "the full reductions have different action sets" (`Γs.reduce.S ≠ Γ.reduce.S`),
  the reading Appendix D's hardness proof uses; the printed clause ("not equal") is
  satisfied by any payoff shift of a subset game and so is constant-true (erratum D13,
  harness round 1).  The printed predicates are carried alongside as `…Printed` with the
  theorems that they are constant-true, and the repaired one has a "no" instance
  (`not_spiDecision_of_card_le_one`).  Ruled 2026-09-12.
* `dd:program-game` — *realized* (`ProgramGame.lean`, `Instruction.lean`).  Theorem 1's
  program game is an abstract interface (`ProgramGame`: instruction sets, an execution
  map, measurable fibers) with the induced game an EconCSLib `StrategicGame` and program
  equilibrium its `IsNashEquilibrium`, plus a concrete minimal language `Prog` closed under
  exactly the three instructions Algorithm 2 needs (RULING 3), realized as a program game
  by `Prog.programGame`; Proposition 18 is proved directly over the interface and
  instantiated at Algorithm 2, without Theorem 17.  Threat points are the paper's
  min–max over independent mixtures (EconCSLib's `MixedStrategy`/`expectedPayoff`), with
  both extrema by compactness and the minimiser chosen once per player (`Game.minimax`).
* `dd:exec-kernel` — *realized* (`ProgramGame.lean`).  Execution returns, for each player,
  a **mixed** action given the representatives' sample point `ω`, and the players' actions
  are independent given `ω`: each program's own randomness is private, the only shared
  randomness is `Π`'s.  This is what the paper's `exec : PROG ⇝ A` leaves implicit and
  what the threat-point bound in Proposition 18 needs (erratum D8); it replaces the
  design note's per-player seed spaces by their outcome distributions.
* `dd:code-eq` — *realized* (`Instruction.lean`).  A `Prog` is player-agnostic (the player
  index is a run-time input, so Algorithm 2 is submitted verbatim by everybody) and code
  equality is classical: programs contain real payoffs and probabilities, and the
  meta-game is a mathematical object, as the paper's is.  When several players' code
  differs the paper punishes the first in the order `1, …, n`; `N` is unordered, so a fixed
  classical choice stands in (immaterial for unilateral deviations).
* `dd:default-instr` — *realized* (`Independence.lean`, beyond the paper).  A distinguished
  non-participation instruction per player, executing as `Π(Γ₀)`, is what makes
  participation independence and foreknowledge independence stateable (RULING 9); in
  `Prog` it is "play `Πᵢ(Γ₀)`".  No theorem beyond non-vacuity is claimed for either
  notion.
* `dd:feasible` — *realized* (`Coordination.lean`).  `C(Γ)` is defined by the paper's own
  formula — the payoff vectors of correlated strategies (`Game.Correlated`, weights on the
  outcomes) — and proved equal to Mathlib's `convexHull ℝ (u '' A)`; convexity and
  membership of pure payoffs come from the formula, everything geometric from the hull.
* `dd:room` — *realized* (`Coordination.lean`).  §5's token actions must be fresh,
  `Aˢᵢ ∩ Aᵢ = ∅`; over a fixed universe (`dd:universe`) their existence is the hypothesis
  `Game.HasRoomOutside Γ B` (an injective copy of each of `Γ`'s action sets avoiding `B`),
  from which `Game.tokenCopy` and its natural isomorphism are built.  The avoided set is a
  parameter because §5 tokenizes `Γ.reduce` but must be fresh for `Γ`;
  `Game.HasRoom Γ := Γ.HasRoomOutside Γ.S` is the special case.  The paper assumes the
  tokens exist silently.  §5's *examples* discharge it by choosing a universe with infinite
  room, `𝒜 i := X ⊕ ℕ` with the board in `inl` and off-board payoffs `0`
  (`Game.hasRoomOutside_of_infinite`); this is forced, since a game using its whole finite
  universe has `TokenGame Γ` empty and any impossibility over it vacuous.  Where the
  argument permits, an impossibility is additionally stated label-free, so that it does not
  depend on how rich the universe is
  (`Examples.chicken_no_feasible_dominating_of_mean_cc`).
* `dd:complexity` — *planned* for Theorem 9 / Proposition 10; *realized* for **Lemma 11**
  (`Coordination.lean`: the LP characterization is the node's content, the "by linear
  programming, in polynomial time" clause is disclosed as not rendered) and for
  **Proposition 12** (`PerfectCoordination.lean`: Algorithm 1's correctness as an iff is
  the node's content, the "can be decided in polynomial time" clause is disclosed as not
  rendered).  Theorem 9, Proposition 10, Lemma 11 and Proposition 12 are
  carried as **qualified** nodes: the paper-node label sits on the mathematical content
  (certificate characterizations, Lemma 28's reduction as an iff, the LP characterization,
  Algorithm 1's correctness) and the docstring says which complexity-class or runtime
  clause of the printed statement is not rendered and why (RULING 6, tranche F deferred).

## Files

| file | content |
|---|---|
| `SafeParetoImprovements/Game.lean` | §2: `Game` over a fixed universe, `Game.EqOn`, subset games, `Game.restrict`/`Game.erase`, the EconCSLib bridge `Game.toStrategic`, strict dominance (`strictlyDominates_iff`) |
| `SafeParetoImprovements/Play.lean` | §3: the play family `Play`, Definitions 1–2 (`Play.IsSPI`, `Play.IsStrictSPI`, `Game.Unilateral`, `Play.IsUnilateralSPI`) at the certainty-filter level |
| `SafeParetoImprovements/Correspondence.lean` | §4.1–§4.3: multivalued functions as `SetRel`, Definition 3 (`Play.Corresponds`), Lemma 2 (items 1–7), Definition 4 (`Play.ParetoImprovingCorrespondence`), **Theorem 3** (`Play.isSPI_iff_exists_paretoImprovingCorrespondence`) |
| `SafeParetoImprovements/Ordering.lean` | §4.2 prose after Lemma 2: the equivalence relation `R` (single-valued bijective correspondence) and the preorder `⪰` relative to a base game; unnumbered carriers |
| `SafeParetoImprovements/Isomorphism.lean` | §2 game isomorphism (`GameIso`, `Game.Isomorphic`), the automorphism argument, Lemma 4 in both its weak and strict forms |
| `SafeParetoImprovements/Assumptions.lean` | §4.4: Assumption 1 (`Play.SatisfiesA1`) and Assumption 2 (`Play.SatisfiesA2`) as predicates, and the Lemma-4 transfer that makes Assumption 2's existential usable |
| `SafeParetoImprovements/Reduction.lean` | Appendix D.1: single-step elimination `Game.Elim` and its closure, **Lemma 19** (`Game.isStrictlyDominated_erase`), confluence, uniqueness of the fully reduced game, and the canonical `Game.reduce` |
| `SafeParetoImprovements/Representatives.lean` | `Representatives`: the probabilistic model, support, and the realization of the certainty interface at `ae μ` |
| `SafeParetoImprovements/Book.lean` | §4.4.3: the book representatives and the joint satisfiability of Assumptions 1 and 2 (`dd:book`), with the page distribution as a parameter |
| `SafeParetoImprovements/Examples/TwoPlayer.lean` | the two-element player type and the finite-check lemmas the §4.5 tables need |
| `SafeParetoImprovements/Examples/PrisonersDilemma.lean` | Table 3 and **Proposition 5** (`Examples.prisonersDilemma_isStrictSPI`), also the non-vacuity witness for `Play.IsStrictSPI` |
| `SafeParetoImprovements/Examples/DemandGame.lean` | Tables 1–2 and **Proposition 6**, both clauses (`Examples.demandGame_isSPI`, `Examples.demandGame_isStrictSPI`) |
| `SafeParetoImprovements/Examples/Temptation.lean` | Table 6 and **Proposition 7** (`Examples.temptation_isStrictSPI`) |
| `SafeParetoImprovements/Examples/ComplicatedTemptation.lean` | Tables 4–5 and **Proposition 8** (`Examples.complicatedTemptation_isUnilateralSPI`) |
| `SafeParetoImprovements/Examples/Witnesses.lean` | non-vacuity witnesses: a play family over `Unit` at which each of Propositions 5–8 has all its hypotheses satisfied (the strict clause of 6 through `Book.prescribed`), the yes-instances of the repaired Definition 5, and the `Representatives` inhabitant `Examples.unitRepresentatives` |
| `SafeParetoImprovements/ProgramGame.lean` | Appendix A: mixed strategies and expected payoffs from EconCSLib, threat points and the minimax profile by compactness, the `ProgramGame` interface (`dd:exec-kernel`), program equilibrium as EconCSLib Nash, and Proposition 18 over the interface |
| `SafeParetoImprovements/Instruction.lean` | Appendix A: the instruction language `Prog` (`dd:code-eq`), its execution, the realization theorem `Prog.programGame`, Algorithm 2 as a term, **Proposition 18** (`Prog.algorithm2_isProgramEquilibrium`) and **Theorem 1** (`Prog.exists_programEquilibrium_plays`) |
| `SafeParetoImprovements/Independence.lean` | beyond the paper (RULING 9): default instructions (`dd:default-instr`), participation independence, the information stage and foreknowledge independence, with the dove-ish and punishing instructions as witnesses |
| `SafeParetoImprovements/Coordination.lean` | §5.1: `C(Γ)` (`Game.feasible`, `dd:feasible`), perfect-coordination token games (`TokenGame`), **Definition 6** (`TokenGame.IsSPI`, `IsStrictSPI`), room and the token copy (`Game.HasRoomOutside`, `Game.HasRoom`, `Game.hasRoomOutside_of_infinite`, `Game.tokenCopy`, `Game.tokenIso`, `dd:room`), **Lemma 11** (`Game.paretoOptimalIn_feasible_iff`, LP characterization) |
| `SafeParetoImprovements/PerfectCoordination.lean` | §5.2: **Definition 7** (`Play.StrictPerfectCoordinationSPIDecision`, RULINGS 7/10), the reassignment construction (`TokenGame.reassign`, `Play.exists_tokenGame_ue_eq`: `uᵉ` along the isomorphism Assumption 2 supplies), **Proposition 12** as Algorithm 1's correctness iff (`Representatives.strictPerfectCoordinationSPIDecision_iff`, RULING 11, `dd:complexity`) |
| `SafeParetoImprovements/Polytope.lean` | Mathlib-shaped substrate: polytopes as convex hulls of finite sets, closure under scaling and Minkowski sums, and the half-space / orthant section theorems (`IsPolytope.inter_halfspace`, `inter_Ici`) that Corollary 14's polytope clause needs and Mathlib lacks |
| `SafeParetoImprovements/Characterization.lean` | §5.3: conditional expectation on the play's fibers (`Representatives.condExp`, law of total expectation), **Lemma 13** (`Representatives.exists_reassignment_condExp_eq`), **Corollary 14** as the weighted Minkowski-sum formula (`achievable_eq_improvementSum`), convexity, compactness and the polytope clause (`isPolytope_achievable`, RULING 12) |
| `SafeParetoImprovements/Examples/DecisionWitnesses.lean` | Definition 7 two-sided through Proposition 12: the conflict game is a "yes" instance, Table 7 a "no" instance |
| `SafeParetoImprovements/Examples/CharacterizationWitnesses.lean` | non-vacuity for §5.3: Lemma 13 and Corollary 14 applied on the conflict game (including to a three-action perfect-coordination SPI that is *not* isomorphic to the reduction), `achievable` shown not a singleton and wider than the constant reassignments, and the hand-built play family for which `Representatives.condExp` is a strict average rather than a point evaluation (R5-F11) |
| `SafeParetoImprovements/Examples/Coin.lean` | the fair coin on `Bool`, shared by the examples that need a genuinely random `Π` |
| `SafeParetoImprovements/Examples/Chicken.lean` | Table 7 over `CAct ⊕ ℕ` (`dd:room`) and **Proposition 16** (`Examples.chicken_no_perfectCoordinationSPI`): a Pareto improvement that no perfect-coordination SPI achieves in expectation, with its label-free kernel (`chicken_no_feasible_dominating_of_mean_cc`), the token games of every size that make the class non-empty, and the `Π`-dependence disclosure |
| `SafeParetoImprovements/Examples/TokenWitnesses.lean` | the positive side of **Definition 6**: a `2 × 2` game over `Bool ⊕ ℕ` with a fresh token copy, a perfect-coordination SPI with equality at every sample point, and a *strict* one built by the paper's Demand-Game recipe with `uᵉ` defined along the book's isomorphism (erratum D6, RULING 10) |
| `SafeParetoImprovements/Examples/ProgramGameWitnesses.lean` | non-vacuity for the program-game layer: Theorem 1's hypotheses jointly satisfied in the Prisoner's Dilemma (pure Nash equilibrium ⇒ threat-point guarantee), and the PI/FI predicates neither constant-true nor constant-false |
-/
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
import SafeParetoImprovements.Examples.TwoPlayer
import SafeParetoImprovements.Examples.PrisonersDilemma
import SafeParetoImprovements.Examples.DemandGame
import SafeParetoImprovements.Examples.Temptation
import SafeParetoImprovements.Examples.ComplicatedTemptation
import SafeParetoImprovements.Examples.Witnesses
import SafeParetoImprovements.ProgramGame
import SafeParetoImprovements.Instruction
import SafeParetoImprovements.Independence
import SafeParetoImprovements.Examples.ProgramGameWitnesses
import SafeParetoImprovements.Coordination
import SafeParetoImprovements.Examples.Coin
import SafeParetoImprovements.Examples.Chicken
import SafeParetoImprovements.PerfectCoordination
import SafeParetoImprovements.Examples.DecisionWitnesses
import SafeParetoImprovements.Polytope
import SafeParetoImprovements.Characterization
import SafeParetoImprovements.Examples.TokenWitnesses
import SafeParetoImprovements.Examples.CharacterizationWitnesses
