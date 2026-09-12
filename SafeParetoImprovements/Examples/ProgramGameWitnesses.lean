import SafeParetoImprovements.Independence
import SafeParetoImprovements.Examples.Witnesses

/-!
# Non-vacuity witnesses for the program-game layer

Theorem 1 and Proposition 18 assume that `Π(Γ₀)` guarantees every player at least her
threat point in expectation.  Two instances are carried here, and they differ in exactly
the way that matters for the paper's reading of `Π`:

* **the Prisoner's Dilemma instance is deterministic** — the representatives play
  `(Defect, Defect)` at every sample point, a pure Nash equilibrium, and a pure Nash
  equilibrium certifies the threat-point guarantee
  (`Game.threatPoint_le_of_bestResponse`).  It is a one-point sample space, so `Π(Γ₀)` is
  a constant;
* **the Demand-Game instance is random** — `demandRandomBook` prescribes an `ω`-dependent
  page over the fair coin `coin` on `Bool` (`Book.prescribedRandom`), so `Π(Γ₀)` really is
  a non-constant random variable (`demandRandom_play_ne`), and the threat-point hypothesis
  is discharged from the *expectation* of a genuinely mixed play, not from a single
  outcome.  This is the witness that Theorem 1 is not silently a statement about
  deterministic representatives (R3-F11).

The threat-point hypothesis is not automatic: `demandBook_not_threatPoint_le` shows it
*fails* for the `(DM, DM)`-prescribing book of Proposition 6's strictness clause, so it has
content in Theorem 1's statement.

The same representatives witness that the participation- and foreknowledge-independence
predicates are neither constant-true nor constant-false: the dove-ish instruction is
participation independent, an instruction punishing with `Cooperate` is not (the default
play is `Defect`), a policy that switches to punishment on learning of a non-participation
is not foreknowledge independent, and a policy that switches between two *different*
instructions whose behaviour after the drop-out coincides is.  Algorithm 2 itself fails
participation independence in the Demand Game
(`demandGame_algorithm2_not_participationIndependent`), which is an instance of the
conditional `Prog.not_participationIndependent_algorithm2`.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter MeasureTheory Prog

open scoped ENNReal

/-! ### The deterministic Prisoner's Dilemma instance -/

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

/-- **Theorem 1 is not vacuous, deterministic instance** (hypotheses carried inside the
statement, R2-F11/R3-F02): in the Prisoner's Dilemma with the cooperative subset game, the
SPI hypothesis and the threat-point hypothesis both hold for `pdRepresentatives`, and
Algorithm 2 is a program equilibrium executing as `Π(Γˢ)`.  Here `Π` is deterministic — the
sample space is a point. -/
lemma prisonersDilemma_algorithm2_isProgramEquilibrium :
    pdRepresentatives.toPlay.IsSPI pdRepresentatives.certainty prisonersDilemma
        prisonersDilemmaCooperate ∧
      (∀ i, prisonersDilemma.threatPoint i ≤
        ∫ ω, prisonersDilemma.u (pdRepresentatives.play prisonersDilemma ω) i
          ∂pdRepresentatives.μ) ∧
      (programGame prisonersDilemma pdRepresentatives).IsProgramEquilibrium
        (fun _ => algorithm2 prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf) ∧
      (programGame prisonersDilemma pdRepresentatives).Plays
        (fun _ => algorithm2 prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf)
        fun ω => pdRepresentatives.play prisonersDilemmaCooperate ω := by
  haveI : pdRepresentatives.certainty.NeBot := IsProbabilityMeasure.ae_neBot
  have hSPI : pdRepresentatives.toPlay.IsSPI pdRepresentatives.certainty prisonersDilemma
      prisonersDilemmaCooperate :=
    (prisonersDilemma_isStrictSPI _ pdRepresentatives.certainty
      ((Book.const Unit).satisfiesA1 _) _ fun _ => rfl).1
  exact ⟨hSPI, pdRepresentatives_threatPoint_le,
    algorithm2_isProgramEquilibrium pdRepresentatives _ hSPI pdRepresentatives_threatPoint_le⟩

/-! ### The random Demand-Game instance

The Demand Game's full reduction has both players choosing between `DM` and `RM`; the book
below prescribes `(RM, RM)` at one sample point and `(RM, DM)` at the other, over a fair
coin.  Both outcomes survive reduction, so the book satisfies Assumptions 1 and 2 like any
other, and the play is a genuine random variable. -/

/-- The two prescribed outcomes: `(RM, RM)` and `(RM, DM)`, both surviving reduction. -/
noncomputable def demandPages : Bool → ∀ i, DUniverse i
  | true => Two.pair DAct.RM DAct.RM
  | false => Two.pair DAct.RM DAct.DM

lemma demandPages_mem : ∀ b, demandPages b ∈ demandGame.reducedGame.profiles := by
  intro b i
  cases b <;> cases i <;> rw [demandGame.reducedGame_S] <;> decide

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := ⟨by
  simp [coin, Measure.smul_apply, Measure.add_apply]
  rw [ENNReal.inv_two_add_inv_two]⟩

/-- The `ω`-dependent book prescribing `demandPages` for the class of the reduced Demand
Game. -/
noncomputable def demandRandomBook : Book Two DUniverse Bool :=
  Book.prescribedRandom demandGame.reducedGame demandPages_mem

/-- The representatives of `demandRandomBook` on the fair coin: a **genuinely random**
`Π`. -/
noncomputable def demandRandomRepresentatives : Representatives.{0, 0, 0} Two DUniverse :=
  demandRandomBook.toRepresentatives (μ := coin) (fun _ _ => trivial)

lemma demandRandom_play (ω : Bool) :
    demandRandomRepresentatives.play demandGame ω = demandPages ω :=
  Book.prescribedRandom_play _ demandPages_mem demandGame demandGame.reduce_eq ω

/-- The play is genuinely random: the two sample points give different outcomes. -/
lemma demandRandom_play_ne :
    demandRandomRepresentatives.play demandGame true ≠
      demandRandomRepresentatives.play demandGame false := by
  rw [demandRandom_play, demandRandom_play]
  intro h
  have := congrFun h Two.two
  simp [demandPages, Two.pair] at this

lemma integral_coin (f : Bool → ℝ) : (∫ ω, f ω ∂coin) = 2⁻¹ * (f true + f false) := by
  rw [coin, integral_smul_measure,
    integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_dirac, integral_dirac]
  simp

lemma demandRandom_integral (i : Two) :
    (∫ ω, demandGame.u (demandRandomRepresentatives.play demandGame ω) i
        ∂demandRandomRepresentatives.μ) =
      2⁻¹ * (demandGame.u (demandPages true) i + demandGame.u (demandPages false) i) := by
  simp only [demandRandom_play]
  show (∫ ω, demandGame.u (demandPages ω) i ∂coin) = _
  rw [integral_coin]

/-- **Theorem 1's threat-point hypothesis holds for the random representatives**: each
player's threat point is at most the *expectation* of the random play's payoff. -/
lemma demandRandom_threatPoint_le (i : Two) :
    demandGame.threatPoint i ≤
      ∫ ω, demandGame.u (demandRandomRepresentatives.play demandGame ω) i
        ∂demandRandomRepresentatives.μ := by
  rw [demandRandom_integral]
  have hb : ∀ (a : ∀ j, DUniverse j), a ∈ demandGame.profiles := fun a i => Finset.mem_univ _
  cases i
  · have h := demandGame.threatPoint_le_of_bestResponse (a := Two.pair DAct.RM DAct.DM)
      (hb _) Two.one (by
        intro b _
        cases b <;> norm_num [demandGame.u_apply, demandPayoff, Two.pair,
          Function.update_of_ne (show Two.two ≠ Two.one by decide)])
    refine h.trans ?_
    norm_num [demandGame.u_apply, demandPayoff, demandPages, Two.pair]
  · have h := demandGame.threatPoint_le_of_bestResponse (a := Two.pair DAct.DM DAct.RM)
      (hb _) Two.two (by
        intro b _
        cases b <;> norm_num [demandGame.u_apply, demandPayoff, Two.pair,
          Function.update_of_ne (show Two.one ≠ Two.two by decide)])
    refine h.trans ?_
    norm_num [demandGame.u_apply, demandPayoff, demandPages, Two.pair]

/-- **Theorem 1 is not vacuous, random instance** (R3-F11, hypotheses carried inside the
statement per R2-F11): in the Demand Game with the paper's SPI, the SPI hypothesis and the
threat-point hypothesis both hold for `demandRandomRepresentatives`, whose `Π(Γ₀)` is a
non-constant random variable, and the conclusion of Theorem 1 is reached. -/
lemma demandRandom_algorithm2_isProgramEquilibrium :
    demandRandomRepresentatives.play demandGame true ≠
        demandRandomRepresentatives.play demandGame false ∧
      demandRandomRepresentatives.toPlay.IsSPI demandRandomRepresentatives.certainty
        demandGame demandSPI ∧
      (∀ i, demandGame.threatPoint i ≤
        ∫ ω, demandGame.u (demandRandomRepresentatives.play demandGame ω) i
          ∂demandRandomRepresentatives.μ) ∧
      ∃ c : ∀ _ : Two, Prog demandGame,
        (programGame demandGame demandRandomRepresentatives).IsProgramEquilibrium c ∧
          (programGame demandGame demandRandomRepresentatives).Plays c
            fun ω => demandRandomRepresentatives.play demandSPI ω := by
  have hSPI : demandRandomRepresentatives.toPlay.IsSPI demandRandomRepresentatives.certainty
      demandGame demandSPI :=
    demandGame_isSPI _ _ (demandRandomBook.satisfiesA1 _) (demandRandomBook.satisfiesA2 _)
  exact ⟨demandRandom_play_ne, hSPI, demandRandom_threatPoint_le,
    exists_programEquilibrium_plays demandRandomRepresentatives hSPI
      demandRandom_threatPoint_le⟩

/-! ### The threat-point hypothesis has content -/

/-- Player 1's threat point in the Demand Game is at least `0`: `RM` guarantees her `≥ 0`
against every profile (`Game.le_threatPoint_of_guarantee`). -/
lemma demandGame_threatPoint_one_nonneg : (0 : ℝ) ≤ demandGame.threatPoint Two.one := by
  refine demandGame.le_threatPoint_of_guarantee Two.one (a := DAct.RM) (Finset.mem_univ _) 0 ?_
  intro s hs
  show (0 : ℝ) ≤ demandPayoff _ _ Two.one
  rw [show (demandGame.ofStrategicProfile s) Two.one = DAct.RM from hs]
  cases h : (s Two.two : DAct) <;>
    simp [Game.ofStrategicProfile, h, demandPayoff]

/-- The `(DM, DM)`-prescribing book of Proposition 6's strictness clause, as
representatives on the one-point space. -/
noncomputable def demandRepresentatives : Representatives.{0, 0, 0} Two DUniverse :=
  demandBook.toRepresentatives (μ := Measure.dirac ()) (fun _ _ => trivial)

lemma demandRepresentatives_play (ω : Unit) :
    demandRepresentatives.play demandGame ω = Two.pair DAct.DM DAct.DM :=
  Book.prescribed_play _ demandGame_pair_DM_mem Unit demandGame demandGame.reduce_eq ω

lemma demandRepresentatives_integral :
    (∫ ω, demandGame.u (demandRepresentatives.play demandGame ω) Two.one
      ∂demandRepresentatives.μ) = -3 := by
  simp only [demandRepresentatives_play]
  rw [show demandGame.u (Two.pair DAct.DM DAct.DM) Two.one = -3 by
        norm_num [demandGame.u_apply, demandPayoff]]
  rw [integral_const, probReal_univ, one_smul]

/-- **Theorem 1's threat-point hypothesis is not automatic**: it *fails* in the paper's own
Demand-Game example whenever the representatives play the conflict outcome `(DM, DM)` — and
`demandBook`, the Proposition 6 strictness witness, is such a book, satisfying Assumptions
1 and 2.  So the hypothesis carries content rather than being derivable (R3-F11). -/
lemma demandBook_not_threatPoint_le :
    ¬ (∀ i, demandGame.threatPoint i ≤
        ∫ ω, demandGame.u (demandRepresentatives.play demandGame ω) i
          ∂demandRepresentatives.μ) := by
  intro h
  have h1 := h Two.one
  rw [demandRepresentatives_integral] at h1
  linarith [demandGame_threatPoint_one_nonneg]

/-! ### Participation independence -/

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

/-! #### Algorithm 2 itself fails participation independence

`Prog.not_participationIndependent_algorithm2` is conditional on the minimax punishment
differing from the default play.  In the Prisoner's Dilemma that hypothesis is false —
`Defect` is both the minimax punishment and the default play — so the Demand Game supplies
the instance (R3-F12).  Nothing here computes `Game.minimax`: the upper bound
`demandGame_threatPoint_two_le` (from a pure Nash best response) plus
`Game.expected_minimax_le_threatPoint` rule out the value `RM` for the punishment. -/

/-- Player 2's threat point in the Demand Game is at most `0`. -/
lemma demandGame_threatPoint_two_le : demandGame.threatPoint Two.two ≤ 0 := by
  have hb : ∀ (a : ∀ j, DUniverse j), a ∈ demandGame.profiles := fun a i => Finset.mem_univ _
  have h := demandGame.threatPoint_le_of_bestResponse (a := Two.pair DAct.DM DAct.RM)
    (hb _) Two.two (by
      intro b _
      cases b <;> norm_num [demandGame.u_apply, demandPayoff, Two.pair,
        Function.update_of_ne (show Two.one ≠ Two.two by decide)])
  refine h.trans ?_
  norm_num [demandGame.u_apply, demandPayoff, Two.pair]

/-- Player 1's coordinate of the minimax profile against player 2 is **not** `RM`: `RM`
against `RM` would earn player 2 a payoff of `1`, above her threat point. -/
lemma demandGame_minimax_two_one_ne_RM :
    demandGame.minimax Two.two Two.one ≠ demandGame.pureMixed DAct.RM (Finset.mem_univ _) := by
  intro heq
  have hmem : ∀ j, (Two.pair DAct.RM DAct.RM) j ∈ demandGame.S j := fun _ => Finset.mem_univ _
  have hσ : Function.update (demandGame.minimax Two.two) Two.two
      (demandGame.pureMixed DAct.RM (Finset.mem_univ _)) =
      fun j => demandGame.pureMixed ((Two.pair DAct.RM DAct.RM) j) (hmem j) := by
    funext j
    cases j
    · rw [Function.update_of_ne (show Two.one ≠ Two.two by decide), heq]; rfl
    · rw [Function.update_self]; rfl
  have h1 : demandGame.expected (Function.update (demandGame.minimax Two.two) Two.two
      (demandGame.pureMixed DAct.RM (Finset.mem_univ _))) Two.two = 1 := by
    rw [hσ, demandGame.expected_pure (Two.pair DAct.RM DAct.RM) hmem Two.two]
    norm_num [demandGame.u_apply, demandPayoff, Two.pair]
  have h2 := demandGame.expected_minimax_le_threatPoint Two.two
    (demandGame.pureMixed DAct.RM (Finset.mem_univ _))
  rw [h1] at h2
  linarith [demandGame_threatPoint_two_le]

/-- **Algorithm 2 is not participation independent**, as an instance rather than a
hypothesis: in the Demand Game with the random representatives, player 1's punishment of a
non-participating player 2 differs from her default play `RM` (R3-F12). -/
lemma demandGame_algorithm2_not_participationIndependent :
    ¬ (programGame demandGame demandRandomRepresentatives).ParticipationIndependent
        (defaultInstr demandGame demandRandomRepresentatives)
        (fun _ => algorithm2 demandSPI demandSPI.isSubsetGameOf) Two.one := by
  refine not_participationIndependent_algorithm2 demandRandomRepresentatives _ _ Two.one
    (j := Two.two) (by decide) ⟨true, ?_⟩
  have hplay : demandRandomRepresentatives.play demandGame true Two.one = DAct.RM := by
    rw [demandRandom_play]; rfl
  intro h
  exact demandGame_minimax_two_one_ne_RM (by rw [h]; congr 1)

/-! ### Foreknowledge independence -/

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

/-- The policy for player 1 with a **genuinely informative** signal: uninformed she submits
the dove-ish SPI instruction, informed that a counterpart will not participate she submits
the default instruction.  The two are *different programs*
(`dove_ne_default`); what coincides is only their behaviour once the counterpart has in
fact dropped out, and that has to be proved through the execution model. -/
noncomputable def pdFallbackPolicy :
    (programGame prisonersDilemma pdRepresentatives).Policy Two.one where
  Signal := Bool
  noInfo := false
  willNotParticipate _ := true
  policy
    | false => dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf
    | true => default prisonersDilemma

lemma dove_ne_default :
    dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf ≠
      default prisonersDilemma := by
  intro h
  unfold dove Prog.default at h
  cases h

/-- **Foreknowledge independence is not constant-false**, non-degenerately (R3-F07/F13):
`pdFallbackPolicy` reads its signal and chooses two syntactically different instructions,
yet once player 2 has dropped out player 1's realised action is the same either way —
the dove-ish instruction's own fall-back branch is the default instruction.  Unlike a
signal-blind policy, the two sides of `ForeknowledgeIndependent` here are not the same
term, and the proof runs through `Prog.execAt`. -/
lemma foreknowledgeIndependent_pd (c : Two → Prog prisonersDilemma) :
    (programGame prisonersDilemma pdRepresentatives).ForeknowledgeIndependent
      (defaultInstr prisonersDilemma pdRepresentatives) c pdFallbackPolicy := by
  intro j hj ω
  have hjtwo : j = Two.two := by cases j with | one => exact absurd rfl hj | two => rfl
  subst hjtwo
  show execAt pdRepresentatives _ Two.one _ ω = execAt pdRepresentatives _ Two.one _ ω
  simp only [Function.update_self]
  show execAt pdRepresentatives
      (Function.update (Function.update c Two.two (default prisonersDilemma)) Two.one
        (dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf))
      Two.one (dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf) ω = _
  set c' := Function.update (Function.update c Two.two (default prisonersDilemma)) Two.one
        (dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf) with hc'
  have hne : ¬ ∀ k, c' k = c' Two.one := by
    intro hall
    have h2 : c' Two.two = default prisonersDilemma := by
      rw [hc', Function.update_of_ne (show Two.two ≠ Two.one by decide), Function.update_self]
    have h1 : c' Two.one = dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf := by
      rw [hc', Function.update_self]
    have := hall Two.two
    rw [h1, h2] at this
    exact dove_ne_default this.symm
  obtain ⟨k, -, hk⟩ := execAt_ifAllSame_of_ne pdRepresentatives hne
    (delegate prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf)
    (fun _ => default prisonersDilemma) ω
  rw [show dove prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf =
        ifAllSame (delegate prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf)
          (fun _ => default prisonersDilemma) from rfl, hk]
  rfl

end Examples

end SafeParetoImprovements
