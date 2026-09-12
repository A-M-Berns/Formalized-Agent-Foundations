import SafeParetoImprovements.Independence
import SafeParetoImprovements.Examples.Witnesses

/-!
# Non-vacuity witnesses for the program-game layer

Theorem 1 and Proposition 18 assume that `Π(Γ₀)` guarantees every player at least her
threat point in expectation.  In the Prisoner's Dilemma the representatives play
`(Defect, Defect)` under Assumption 1, a pure Nash equilibrium, and a pure Nash
equilibrium certifies the guarantee (`Game.threatPoint_le_of_bestResponse`), so Theorem 1's
hypotheses are jointly satisfiable and its conclusion is reached: Algorithm 2 for the
cooperative subset game is a program equilibrium whose execution is `Π(Γˢ)`.

The same representatives witness that the participation- and foreknowledge-independence
predicates are neither constant-true nor constant-false: the dove-ish instruction is
participation independent, an instruction punishing with `Cooperate` is not (the default
play is `Defect`), a signal-blind policy is foreknowledge independent, and a policy that
switches to punishment on learning of a non-participation is not.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter MeasureTheory Prog

lemma prisonersDilemmaCooperate_isSubsetGameOf :
    prisonersDilemmaCooperate.IsSubsetGameOf prisonersDilemma := fun _ => Finset.subset_univ _

/-- The deterministic book's representatives model over `PDUniverse` on the one-point
probability space. -/
noncomputable def pdRepresentatives : Representatives.{0, 0, 0} Two PDUniverse :=
  (Book.const (N := Two) (𝒜 := PDUniverse) Unit).toRepresentatives
    (μ := Measure.dirac ()) (fun _ _ => trivial)

lemma pdRepresentatives_play (ω : Unit) :
    pdRepresentatives.play prisonersDilemma ω = fun _ => PD.defect :=
  eventually_top.1 (prisonersDilemma_play _ ⊤ ((Book.const Unit).satisfiesA1 ⊤)) ω

/-- `(Defect, Defect)` is a pure Nash equilibrium of the Prisoner's Dilemma. -/
lemma prisonersDilemma_defect_bestResponse (i : Two) (b : PD) :
    prisonersDilemma.u (Function.update (fun _ => PD.defect) i b) i ≤
      prisonersDilemma.u (fun _ => PD.defect) i := by
  cases i <;> cases b <;> simp [prisonersDilemma, pdPayoff]

/-- **Theorem 1's threat-point hypothesis holds in the Prisoner's Dilemma**: the
representatives play the pure Nash equilibrium `(Defect, Defect)`. -/
lemma pdRepresentatives_threatPoint_le (i : Two) :
    prisonersDilemma.threatPoint i ≤
      ∫ ω, prisonersDilemma.u (pdRepresentatives.play prisonersDilemma ω) i ∂pdRepresentatives.μ := by
  have hplay : (fun ω => prisonersDilemma.u (pdRepresentatives.play prisonersDilemma ω) i) =
      fun _ => prisonersDilemma.u (fun _ => PD.defect) i := by
    funext ω; rw [pdRepresentatives_play]
  rw [hplay, integral_const, probReal_univ, one_smul]
  exact prisonersDilemma.threatPoint_le_of_bestResponse (prisonersDilemma.mem_profiles _) i
    fun b _ => prisonersDilemma_defect_bestResponse i b

/-- **Theorem 1 is not vacuous**: in the Prisoner's Dilemma with the cooperative subset
game, every hypothesis of Theorem 1 holds for `pdRepresentatives`, and Algorithm 2 is a
program equilibrium executing as `Π(Γˢ)`. -/
lemma prisonersDilemma_algorithm2_isProgramEquilibrium :
    (programGame prisonersDilemma pdRepresentatives).IsProgramEquilibrium
        (fun _ => algorithm2 prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf) ∧
      (programGame prisonersDilemma pdRepresentatives).Plays
        (fun _ => algorithm2 prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf)
        fun ω => pdRepresentatives.play prisonersDilemmaCooperate ω :=
  haveI : pdRepresentatives.certainty.NeBot := IsProbabilityMeasure.ae_neBot
  algorithm2_isProgramEquilibrium pdRepresentatives _
    (prisonersDilemma_isStrictSPI _ pdRepresentatives.certainty ((Book.const Unit).satisfiesA1 _) _
      fun _ => rfl).1
    pdRepresentatives_threatPoint_le

/-- `Cooperate` as a pure mixed action of the Prisoner's Dilemma, for every player. -/
noncomputable def pdCooperateMixed : ∀ i, prisonersDilemma.Mixed i :=
  fun _ => prisonersDilemma.pureMixed PD.cooperate (Finset.mem_univ _)

lemma pdCooperateMixed_ne_defect (i : Two) (ω : Unit) :
    pdCooperateMixed i ≠ prisonersDilemma.pureMixed (pdRepresentatives.play prisonersDilemma ω i)
      (pdRepresentatives.toPlay.mem prisonersDilemma ω i) := by
  intro h
  have := congrArg (fun p => p.val ⟨PD.cooperate, Finset.mem_univ _⟩) h
  simp [pdCooperateMixed, Game.pureMixed_val, pdRepresentatives_play] at this

/-- **Participation independence is not constant-true**: in the Prisoner's Dilemma, an
instruction that punishes non-participation with `Cooperate` is not participation
independent. -/
lemma not_participationIndependent_pd (t : Prog prisonersDilemma) :
    ¬ (programGame prisonersDilemma pdRepresentatives).ParticipationIndependent
        (defaultInstr prisonersDilemma pdRepresentatives)
        (fun _ => ifAllSame t fun _ => play pdCooperateMixed) Two.one :=
  not_participationIndependent_of_punish_play pdRepresentatives _ Two.one t pdCooperateMixed rfl
    (j := Two.two) (by decide) ⟨(), pdCooperateMixed_ne_defect Two.one ()⟩

/-- **Participation independence is not constant-false**: the dove-ish instruction for the
cooperative subset game is participation independent. -/
lemma participationIndependent_pd :
    (programGame prisonersDilemma pdRepresentatives).ParticipationIndependent
      (defaultInstr prisonersDilemma pdRepresentatives)
      (fun _ => dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf) Two.one :=
  participationIndependent_dove pdRepresentatives _ _ _ Two.one rfl

/-- The policy for player 1 that complies when uninformed and punishes with `Cooperate`
when told that player 2 will not participate. -/
noncomputable def pdSwitchPolicy : (programGame prisonersDilemma pdRepresentatives).Policy Two.one where
  Signal := Option Two
  noInfo := none
  willNotParticipate := some
  policy
    | none => dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf
    | some _ => play pdCooperateMixed

/-- **Foreknowledge independence is not constant-true**: the switching policy is not
foreknowledge independent. -/
lemma not_foreknowledgeIndependent_pd (c : Two → Prog prisonersDilemma) :
    ¬ (programGame prisonersDilemma pdRepresentatives).ForeknowledgeIndependent
        (defaultInstr prisonersDilemma pdRepresentatives) c pdSwitchPolicy :=
  not_foreknowledgeIndependent_of_switch pdRepresentatives _ _ c Two.one pdCooperateMixed
    (j := Two.two) (by decide) pdSwitchPolicy rfl rfl ⟨(), pdCooperateMixed_ne_defect Two.one ()⟩

/-- The signal-blind policy for player 1: comply whatever the signal. -/
noncomputable def pdBlindPolicy : (programGame prisonersDilemma pdRepresentatives).Policy Two.one where
  Signal := Unit
  noInfo := ()
  willNotParticipate _ := ()
  policy _ := dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf

/-- **Foreknowledge independence is not constant-false**: the signal-blind policy is
foreknowledge independent. -/
lemma foreknowledgeIndependent_pd (c : Two → Prog prisonersDilemma) :
    (programGame prisonersDilemma pdRepresentatives).ForeknowledgeIndependent
      (defaultInstr prisonersDilemma pdRepresentatives) c
      pdBlindPolicy :=
  (programGame prisonersDilemma pdRepresentatives).foreknowledgeIndependent_of_const _ c _ fun _ => rfl

end Examples

end SafeParetoImprovements
