import SafeParetoImprovements.PerfectCoordination
import SafeParetoImprovements.Examples.TokenWitnesses
import SafeParetoImprovements.Examples.Chicken

/-!
# Definition 7 is two-sided, through Proposition 12

* **Yes**: the conflict game of `TokenWitnesses.lean` with the fair-coin representatives.
  Its conflict outcome `(x, x)`, worth `(0, 0)`, is played with probability ½ and is
  Pareto-dominated in `C(Γ)` by `u(y, y) = (1, 1)`, so Algorithm 1 answers *true* and
  Proposition 12 produces a strict perfect-coordination SPI — the same conclusion
  `conflictStrictToken_isStrictSPI` reaches by hand.
* **No**: Table 7 with the fair-coin representatives.  Both supported outcomes, `(a, b)` and
  `(b, a)`, are Pareto-optimal in `C(Γ)` (the two supporting half-planes of `Chicken.lean`),
  so Algorithm 1 answers *false* and, by Proposition 12, Table 7 admits no strict
  perfect-coordination SPI at all — which is why its strict witness had to come from
  another game.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter MeasureTheory Two

/-! ### The conflict game: a "yes" instance -/

lemma conflictGame_hasRoom : conflictGame.reduce.HasRoomOutside conflictGame.S :=
  conflictGame.reduce.hasRoomOutside_of_infinite _

/-- The conflict outcome is played with probability ½, hence supported. -/
lemma conflict_mem_support :
    pair (Sum.inl false) (Sum.inl false) ∈ conflictRepresentatives.support conflictGame := by
  show coin {ω : Bool | conflictRepresentatives.toPlay.play conflictGame ω =
    pair (Sum.inl false) (Sum.inl false)} ≠ 0
  rw [coin_ne_zero_iff]
  exact Or.inl (conflictRepresentatives_play true)

/-- `(0, 0)` is Pareto-dominated in `C(Γ)` by the feasible `(1, 1)`. -/
lemma conflict_not_paretoOptimal :
    ¬ Game.ParetoOptimalIn (conflictGame.u (pair (Sum.inl false) (Sum.inl false)))
      conflictGame.feasible := by
  intro hopt
  refine hopt ⟨conflictGame.u (pair (Sum.inl true) (Sum.inl true)),
    conflictGame.u_mem_feasible (conflictPages_mem false), ?_⟩
  refine Pi.lt_def.2 ⟨fun i => ?_, Two.one, ?_⟩
  · cases i <;> norm_num [conflictGame_u_inl, conflictPayoff]
  · norm_num [conflictGame_u_inl, conflictPayoff]

/-- **Definition 7 is not constant-false**: Algorithm 1 answers *true* on the conflict game,
and Proposition 12 turns that into a strict perfect-coordination SPI. -/
lemma conflictGame_strictPerfectCoordinationSPIDecision :
    conflictRepresentatives.toPlay.StrictPerfectCoordinationSPIDecision
      conflictRepresentatives.certainty conflictGame :=
  (conflictRepresentatives.strictPerfectCoordinationSPIDecision_iff conflictGame
    (conflictBook.satisfiesA1 _) (conflictBook.satisfiesA2 _) conflictGame_hasRoom).2
    ⟨_, conflict_mem_support, conflict_not_paretoOptimal⟩

/-! ### Table 7: a "no" instance -/

/-- Every supported outcome of `Π(Table 7)` is Pareto-optimal in `C(Γ)`: the support is
`{(a, b), (b, a)}` and both lie on supporting lines of `C(Γ)`. -/
lemma chicken_support_paretoOptimal :
    ∀ a ∈ chickenRepresentatives.support chicken, Game.ParetoOptimalIn (chicken.u a) chicken.feasible := by
  intro a ha
  have hmem : a ∈ Set.range chickenPages := by
    by_contra hna
    apply ha
    have : {ω | chickenRepresentatives.play chicken ω = a} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hna ⟨ω, by rw [← chickenRepresentatives_play, h]⟩
    rw [this]; exact measure_empty
  obtain ⟨ω, rfl⟩ := hmem
  rintro ⟨y, hy, hlt⟩
  obtain ⟨hle, i, hi⟩ := Pi.lt_def.1 hlt
  cases ω
  · -- tails: `(b, a)`, worth `(0, 4)`, on the line `6 y₁ + 100 y₂ = 400`
    have h₁ := hle Two.one
    have h₂ := hle Two.two
    have hf := chicken.feasible_le₂ hy
    simp only [chickenPages, chicken.u_inl, chickenPayoff] at h₁ h₂ hi
    cases i <;> linarith
  · -- heads: `(a, b)`, worth `(4, 0)`, on the line `100 y₁ + 6 y₂ = 400`
    have h₁ := hle Two.one
    have h₂ := hle Two.two
    have hf := chicken.feasible_le₁ hy
    simp only [chickenPages, chicken.u_inl, chickenPayoff] at h₁ h₂ hi
    cases i <;> linarith

/-- **Definition 7 is not constant-true**: Table 7 admits no strict perfect-coordination
SPI (Algorithm 1 answers *false*), by Proposition 12's "only if" direction. -/
lemma chicken_not_strictPerfectCoordinationSPIDecision :
    ¬ chickenRepresentatives.toPlay.StrictPerfectCoordinationSPIDecision
      chickenRepresentatives.certainty chicken := by
  rintro ⟨T, hT⟩
  obtain ⟨a, ha, hopt⟩ := chickenRepresentatives.exists_support_not_paretoOptimal_of_strictSPI chicken hT
  exact hopt (chicken_support_paretoOptimal a ha)

end Examples

end SafeParetoImprovements
