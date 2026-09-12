import SafeParetoImprovements.Book
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
file only instantiates them.  It is imported by the aggregator and by nothing else.

* Propositions 5, 7, 8 and the weak clause of 6 need only Assumptions 1 and 2, so the
  deterministic book (`Book.const`) discharges them.
* The strict clause of Proposition 6 additionally needs `(DM, DM)` to be played in the
  Demand Game with positive probability.  That is what a *prescribed* book supplies: since
  the Demand Game fully reduces to `reducedGame` (`demandGame.reduce_eq`), a book whose
  page for that class is `(DM, DM)` plays `(DM, DM)` in the Demand Game at every sample
  point, while still satisfying both assumptions.
* `Representatives` — the probabilistic model of §3 — is inhabited by the deterministic
  book on `(Unit, δ)`.
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

/-- **Proposition 5 is not vacuous**: some play family satisfies Assumption 1 at a
non-degenerate filter, and for it the cooperative subset game really is a strict SPI on the
Prisoner's Dilemma. -/
lemma prisonersDilemma_isStrictSPI_witnessed :
    ∃ X : Play Two PDUniverse Unit,
      X.IsStrictSPI ⊤ prisonersDilemma prisonersDilemmaCooperate := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := PDUniverse) Unit
  exact ⟨X, prisonersDilemma_isStrictSPI X ⊤ (hX ⊤).1 _ fun _ => rfl⟩

/-- **The weak clause of Proposition 6 is not vacuous.** -/
lemma demandGame_isSPI_witnessed :
    ∃ X : Play Two DUniverse Unit, X.IsSPI ⊤ demandGame demandSPI := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := DUniverse) Unit
  exact ⟨X, demandGame_isSPI X ⊤ (hX ⊤).1 (hX ⊤).2⟩

/-- **Proposition 7 is not vacuous.** -/
lemma temptation_isStrictSPI_witnessed :
    ∃ X : Play Two TemptUniverse Unit, X.IsStrictSPI ⊤ temptation temptationCommit := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := TemptUniverse) Unit
  exact ⟨X, temptation_isStrictSPI X ⊤ (hX ⊤).1⟩

/-- **Proposition 8 is not vacuous.** -/
lemma complicatedTemptation_isUnilateralSPI_witnessed :
    ∃ X : Play Two CTUniverse Unit,
      X.IsUnilateralSPI ⊤ complicatedTemptation complicatedTemptationSPI := by
  obtain ⟨X, hX⟩ := exists_play_satisfiesA1_satisfiesA2 (N := Two) (𝒜 := CTUniverse) Unit
  exact ⟨X, complicatedTemptation_isUnilateralSPI X ⊤ (hX ⊤).1 (hX ⊤).2⟩

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

/-! ### `Representatives` is inhabited -/

/-- The **representatives model** of the deterministic book on a one-point probability
space: the `Representatives` structure of §3 is inhabited (R1-F32).  `MeasurableSpace Unit`
is `⊤`, so every fiber is measurable. -/
noncomputable def unitRepresentatives : Representatives.{0, 0, 0} Two DUniverse :=
  (Book.const (N := Two) (𝒜 := DUniverse) Unit).toRepresentatives
    (μ := Measure.dirac ()) (fun _ _ => trivial)

end Examples

end SafeParetoImprovements
