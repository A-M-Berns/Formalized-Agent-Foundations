import SafeParetoImprovements.Book
import SafeParetoImprovements.Derivation
import SafeParetoImprovements.Examples.PrisonersDilemma
import SafeParetoImprovements.Examples.DemandGame
import SafeParetoImprovements.Examples.Temptation
import SafeParetoImprovements.Examples.ComplicatedTemptation
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Non-vacuity witnesses for the §4.5 propositions and for `Representatives`

Propositions 5–8 are stated "under Assumptions 1 and 2" (and, for the strictness clause of
Proposition 6, under a positive-probability hypothesis on the play of the Demand Game).
The repository standard is that a statement is only honest if its hypotheses are
satisfiable, so this file exhibits, for each of them, a play family over a one-point sample
space at which every hypothesis holds — and hence the conclusion is actually reached
(R1-F15, R1-F32).

Nothing here is a paper node: these are witnesses, not claims of the paper.  The general
constructions they use live where they belong — `exists_play_satisfiesA1_satisfiesA2` and
`Book.prescribed` in `Book.lean`, `demandGame.reduce_eq` in `DemandGame.lean` — and this
file only instantiates them.  It is imported by the aggregator and by
`Examples/ProgramGameWitnesses.lean`, which builds the Appendix-A witnesses on top of it.

* Propositions 5, 7, 8 and the weak clause of 6 need only Assumptions 1 and 2, so the
  deterministic book (`Book.const`) discharges them.
* The strict clause of Proposition 6 additionally needs `(DM, DM)` to be played in the
  Demand Game with positive probability.  That is what a *prescribed* book supplies: since
  the Demand Game fully reduces to `reducedGame` (`demandGame.reduce_eq`), a book whose
  page for that class is `(DM, DM)` plays `(DM, DM)` in the Demand Game at every sample
  point, while still satisfying both assumptions.
* `Representatives` — the probabilistic model of §3 — is inhabited by the deterministic
  book on `(Unit, δ)`.
* The soundness result `Play.isStrictSPI_of_deriv` needs *every* surviving outcome to be
  played with positive probability, which no play family over a one-point sample space can
  do once the reduction has two outcomes; its witness therefore lives on the profile space
  and uses the page-varying book (`Book.varying`).

Each of the four "not vacuous" statements carries the Assumption 1 and 2 clauses of the
proposition it witnesses inside its own statement (R2-F11): a bare `∃ X, <conclusion>` is
provable by a hand-built play family that violates Assumption 1 and would witness nothing.

This file also carries the "yes" instances of the repaired Definition 5 predicates
(R2-F05), for the same reason: `Game.not_spiDecision_of_card_le_one` alone would leave
open that the repaired clause is never satisfied.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter MeasureTheory

/-! ### Propositions 5, 7, 8 and the weak clause of 6 -/

/-- The Prisoner's Dilemma subset game in which both players cooperate: the `Γs` of
Proposition 5. -/
def prisonersDilemmaCooperate : Game Two PDUniverse where
  S _ := {PD.cooperate}
  nonempty _ := ⟨.cooperate, Finset.mem_singleton_self _⟩
  u a i := pdPayoff (a .one) (a .two) i

/-- **Proposition 5 is not vacuous**: some play family satisfies Assumptions 1 and 2 at a
non-degenerate filter, and for it the cooperative subset game really is a strict SPI on the
Prisoner's Dilemma.  The assumption clauses are part of the statement (R2-F11): without
them the same conclusion is reachable by a hand-built play family that violates
Assumption 1, and the witness would say nothing about the proposition's hypotheses. -/
lemma prisonersDilemma_isStrictSPI_witnessed :
    ∃ X : Play Two PDUniverse Unit, X.SatisfiesA1 ⊤ ∧ X.SatisfiesA2 ⊤ ∧
      X.IsStrictSPI ⊤ prisonersDilemma prisonersDilemmaCooperate := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := PDUniverse) Unit
  exact ⟨X, (hX ⊤).1, (hX ⊤).2, prisonersDilemma_isStrictSPI X ⊤ (hX ⊤).1 _ fun _ => rfl⟩

/-- **The weak clause of Proposition 6 is not vacuous** (with its assumption clauses,
R2-F11). -/
lemma demandGame_isSPI_witnessed :
    ∃ X : Play Two DUniverse Unit, X.SatisfiesA1 ⊤ ∧ X.SatisfiesA2 ⊤ ∧
      X.IsSPI ⊤ demandGame demandSPI := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := DUniverse) Unit
  exact ⟨X, (hX ⊤).1, (hX ⊤).2, demandGame_isSPI X ⊤ (hX ⊤).1 (hX ⊤).2⟩

/-- **Proposition 7 is not vacuous** (with its assumption clauses, R2-F11). -/
lemma temptation_isStrictSPI_witnessed :
    ∃ X : Play Two TemptUniverse Unit, X.SatisfiesA1 ⊤ ∧ X.SatisfiesA2 ⊤ ∧
      X.IsStrictSPI ⊤ temptation temptationCommit := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := TemptUniverse) Unit
  exact ⟨X, (hX ⊤).1, (hX ⊤).2, temptation_isStrictSPI X ⊤ (hX ⊤).1⟩

/-- **Proposition 8 is not vacuous** (with its assumption clauses, R2-F11). -/
lemma complicatedTemptation_isUnilateralSPI_witnessed :
    ∃ X : Play Two CTUniverse Unit, X.SatisfiesA1 ⊤ ∧ X.SatisfiesA2 ⊤ ∧
      X.IsUnilateralSPI ⊤ complicatedTemptation complicatedTemptationSPI := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := CTUniverse) Unit
  exact ⟨X, (hX ⊤).1, (hX ⊤).2,
    complicatedTemptation_isUnilateralSPI X ⊤ (hX ⊤).1 (hX ⊤).2⟩

/-! ### The strict clause of Proposition 6 -/

lemma demandGame_pair_DM_mem : Two.pair DAct.DM DAct.DM ∈ demandGame.reducedGame.profiles := by
  intro i; rw [demandGame.reducedGame_S]; cases i <;> decide

/-- The book that prescribes `(DM, DM)` for the class of the reduced Demand Game. -/
noncomputable def demandBook : Book Two DUniverse Unit :=
  Book.prescribed demandGame.reducedGame demandGame_pair_DM_mem Unit

/-- **The strictness hypotheses of Proposition 6 are jointly satisfiable**: `demandBook`
satisfies Assumptions 1 and 2 at the non-degenerate filter `⊤` and plays `(DM, DM)` in the
Demand Game with positive probability (R1-F15). -/
lemma demandGame_strictSPI_hypotheses_satisfiable :
    ∃ X : Play Two DUniverse Unit,
      X.SatisfiesA1 ⊤ ∧ X.SatisfiesA2 ⊤ ∧
        ∃ᶠ ω in (⊤ : Filter Unit), X.play demandGame ω = Two.pair DAct.DM DAct.DM :=
  ⟨demandBook.toPlay, demandBook.satisfiesA1 ⊤, demandBook.satisfiesA2 ⊤,
    (Eventually.of_forall fun ω =>
      Book.prescribed_play _ demandGame_pair_DM_mem Unit demandGame
        demandGame.reduce_eq ω).frequently⟩

/-- Hence the conclusion of Proposition 6's strict clause is actually reached. -/
lemma demandGame_isStrictSPI_witnessed :
    ∃ X : Play Two DUniverse Unit, X.IsStrictSPI ⊤ demandGame demandSPI := by
  obtain ⟨X, hA1, hA2, hpos⟩ := demandGame_strictSPI_hypotheses_satisfiable
  exact ⟨X, demandGame_isStrictSPI X ⊤ hA1 hA2 hpos⟩

/-! ### "Yes" instances of the repaired Definition 5

`Game.not_spiDecision_of_card_le_one` gives a "no" instance of the repaired SPI decision
problem; these are the matching "yes" instances, without which the repaired predicates
could be uniformly false (R2-F05).  The payoff-shift witnesses of erratum D13
(`Game.shiftReduce`, `Game.bumpPayoff`) do *not* serve here: they leave `reduce.S`
unchanged and so fail the repaired non-triviality clause by construction. -/

/-- The isomorphism of the two full reductions in the Demand Game, transported onto
`demandGame.reduce` and `demandSPI.reduce`.  A top-level `def` rather than a `have` inside
a proof, so that `ψ.map a` reduces. -/
noncomputable def demandReduceIso : GameIso demandGame.reduce demandSPI.reduce :=
  demandIso.cast demandGame.reduce_eq.symm (Game.reduce_of_reduced demandSPI.reduced).symm

lemma demandReduceIso_paretoImproving : demandReduceIso.ParetoImproving := by
  intro a ha
  rw [demandReduceIso, GameIso.cast_map]
  simp only [Game.reduce_u]
  have ha' : a ∈ demandGame.reducedGame.profiles := by rw [← demandGame.reduce_eq]; exact ha
  simpa [demandGame.reducedGame_u] using demandIso_paretoImproving a ha'

lemma demandGame_reduce_S_ne : demandSPI.reduce.S ≠ demandGame.reduce.S := by
  rw [Game.reduce_of_reduced demandSPI.reduced, demandGame.reduce_eq]
  intro h
  have h1 := congrFun h Two.one
  rw [demandSPI.S_eq, demandGame.reducedGame_S] at h1
  exact absurd h1 (by decide)

/-- **The repaired SPI decision problem has a "yes" instance**: the Demand Game, with
Table 2 as the subset game.  The reduced action sets differ (`{DL, RL}` against
`{DM, RM}`), and the certificate form of Definition 5 turns the Pareto-improving
isomorphism of the two full reductions into the required derivation. -/
lemma demandGame_spiDecision : demandGame.SPIDecision := by
  refine ⟨demandSPI, demandSPI.isSubsetGameOf, demandGame_reduce_S_ne, ?_⟩
  exact (Game.exists_paretoImproving_deriv_iff demandGame demandSPI
    demandSPI.isSubsetGameOf).2 ⟨demandReduceIso, demandReduceIso_paretoImproving⟩

lemma demandGame_pair_DM_mem_reduce :
    Two.pair DAct.DM DAct.DM ∈ demandGame.reduce.profiles := by
  rw [demandGame.reduce_eq]; exact demandGame_pair_DM_mem

/-- **The repaired *strict* SPI decision problem has a "yes" instance**, again the Demand
Game: at the surviving outcome `(DM, DM)` player 1 is strictly better off under the
recorded correspondence, which here is the graph of `demandReduceIso` on
`demandGame.reduce`. -/
lemma demandGame_strictSPIDecision : demandGame.StrictSPIDecision := by
  refine ⟨demandSPI, demandSPI.isSubsetGameOf, demandGame_reduce_S_ne,
    Game.Deriv.normalRel demandReduceIso,
    Game.Deriv.normal (Game.IsSubsetGameOf.refl _) demandSPI.isSubsetGameOf demandReduceIso,
    ?_, Two.one, Two.pair DAct.DM DAct.DM, demandGame_pair_DM_mem_reduce, ?_⟩
  · rintro x y hxy
    obtain ⟨hx, rfl⟩ := (Game.Deriv.mem_normalRel demandReduceIso x y).1 hxy
    simpa only [Game.reduce_u] using demandReduceIso_paretoImproving x hx
  · rintro b hb
    obtain ⟨-, rfl⟩ :=
      (Game.Deriv.mem_normalRel demandReduceIso (Two.pair DAct.DM DAct.DM) b).1 hb
    rw [demandReduceIso, GameIso.cast_map]
    norm_num [demandGame.u_apply, demandPayoff, demandIso, GameIso.map, demilitarize, Two.pair]

/-- The isomorphism of the two full reductions in the Complicated Temptation Game. -/
noncomputable def ctReduceIso :
    GameIso complicatedTemptation.reduce complicatedTemptationSPI.reduce :=
  ctIso.cast complicatedTemptation.reduce_eq.symm complicatedTemptationSPI.reduce_eq.symm

/-- **The repaired *unilateral* SPI decision problem has a "yes" instance**: the
Complicated Temptation Game with Table 5, whose reduced action sets differ for player 2
(`{F1, F2}` against `{C1, C2}`) and whose subset game is unilateral (Proposition 8). -/
lemma complicatedTemptation_unilateralSPIDecision :
    complicatedTemptation.UnilateralSPIDecision := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := CTUniverse) Unit
  refine ⟨complicatedTemptationSPI, complicatedTemptationSPI.isSubsetGameOf, ?_, ?_,
    (complicatedTemptation_isUnilateralSPI X ⊤ (hX ⊤).1 (hX ⊤).2).1⟩
  · rw [complicatedTemptation.reduce_eq, complicatedTemptationSPI.reduce_eq]
    intro h
    have h1 := congrFun h Two.two
    rw [complicatedTemptationSPI.reducedGame_S_two,
      complicatedTemptation.reducedGame_S_two] at h1
    exact absurd h1 (by decide)
  · refine (Game.exists_paretoImproving_deriv_iff complicatedTemptation complicatedTemptationSPI
      complicatedTemptationSPI.isSubsetGameOf).2 ⟨ctReduceIso, ?_⟩
    intro a ha
    rw [ctReduceIso, GameIso.cast_map]
    simp only [Game.reduce_u]
    have ha' : a ∈ complicatedTemptation.reducedGame.profiles := by
      rw [← complicatedTemptation.reduce_eq]; exact ha
    simpa [complicatedTemptation.reducedGame_u] using ctIso_paretoImproving a ha'

/-- **The hypotheses of `Play.isStrictSPI_of_deriv` are jointly satisfiable, side condition
included, and its conclusion is reached** (R2-F18).  The side condition — every outcome
surviving iterated elimination is played with positive probability — is unsatisfiable on a
one-point sample space as soon as the reduction has two outcomes, so the witness is the
page-varying book on the profile space (`Book.varying`), not the deterministic one. -/
lemma demandGame_isStrictSPI_of_deriv_witnessed :
    ∃ X : Play Two DUniverse (∀ i, DUniverse i),
      X.SatisfiesA1 ⊤ ∧ X.SatisfiesA2 ⊤ ∧
        (∀ a ∈ demandGame.reduce.profiles,
          ∃ᶠ ω in (⊤ : Filter (∀ i, DUniverse i)), X.play demandGame ω = a) ∧
        X.IsStrictSPI ⊤ demandGame demandSPI := by
  obtain ⟨X, hA1, hA2, hhits⟩ :=
    exists_play_satisfiesA1_satisfiesA2_hits (N := Two) (𝒜 := DUniverse)
  have hPI : Game.ParetoImprovingFor demandGame (Game.Deriv.normalRel demandReduceIso) := by
    rintro x y hxy
    obtain ⟨hx, rfl⟩ := (Game.Deriv.mem_normalRel demandReduceIso x y).1 hxy
    simpa only [Game.reduce_u] using demandReduceIso_paretoImproving x hx
  refine ⟨X, hA1, hA2, hhits demandGame, ?_⟩
  refine Play.isStrictSPI_of_deriv (i := Two.one) hA1 hA2
    (Game.Deriv.normal (Game.IsSubsetGameOf.refl _) demandSPI.isSubsetGameOf demandReduceIso)
    hPI (hhits demandGame) demandGame_pair_DM_mem_reduce ?_
  rintro b hb
  obtain ⟨-, rfl⟩ :=
    (Game.Deriv.mem_normalRel demandReduceIso (Two.pair DAct.DM DAct.DM) b).1 hb
  rw [demandReduceIso, GameIso.cast_map]
  norm_num [demandGame.u_apply, demandPayoff, demandIso, GameIso.map, demilitarize, Two.pair]

/-! ### `Representatives` is inhabited -/

/-- The **representatives model** of the deterministic book on a one-point probability
space: the `Representatives` structure of §3 is inhabited (R1-F32).  `MeasurableSpace Unit`
is `⊤`, so every fiber is measurable. -/
noncomputable def unitRepresentatives : Representatives.{0, 0, 0} Two DUniverse :=
  (Book.const (N := Two) (𝒜 := DUniverse) Unit).toRepresentatives
    (μ := Measure.dirac ()) (fun _ _ => trivial)

end Examples

end SafeParetoImprovements
