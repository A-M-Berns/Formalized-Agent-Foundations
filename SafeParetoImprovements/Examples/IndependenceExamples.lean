import SafeParetoImprovements.Independence
import SafeParetoImprovements.Examples.ProgramGameWitnesses

/-!
# Participation and foreknowledge independence, worked on the paper's own examples

The 2022 paper proves that every SPI can be implemented as a program equilibrium
(Theorem 1) by Algorithm 2, which *punishes* a non-participating player with the minimax
profile against her.  Two properties one may want of an SPI implementation, which the paper
does not name, are stateable over this formalization's program-game interface
(`Independence.lean`, RULING 9):

* **participation independence** — a player who declines the scheme is met with the
  baseline play `Π(Γ₀)`, not with a punishment (`ProgramGame.ParticipationIndependent`);
* **foreknowledge independence** — a player behaves the same towards a non-participant
  whether or not she knew in advance that he would not participate
  (`ProgramGame.ForeknowledgeIndependent`).

This file works both out on the paper's two headline examples, using the *fallback* profile
`Prog.fallback Γˢ` — "comply with `Γˢ` when everybody submits this code, otherwise play the
baseline" — as the participation-independent alternative to Algorithm 2.

* **Prisoner's Dilemma** (Proposition 5's SPI): the fallback profile is participation
  independent, executes the SPI, and is a program equilibrium
  (`pd_fallback_isProgramEquilibrium`): each player's best reply to the baseline `(D, D)` is
  worth `2`, the SPI `(C, C)` is worth `3`.  A policy that submits the fallback instruction when
  uninformed and the baseline instruction when told the counterpart will not participate is
  foreknowledge independent (`pd_fallbackPolicy_foreknowledgeIndependent`, the general route
  through `Prog.foreknowledgeIndependent_of_participationIndependent`).
* **Demand Game at the conflict outcome** (Proposition 6's SPI, representatives playing
  `(DM, DM)`): Proposition 18's threat-point hypothesis *fails* here
  (`demandBook_not_threatPoint_le`), so the paper's route to a program equilibrium is
  unavailable — yet the fallback profile is a participation-independent program equilibrium
  executing the SPI (`demand_fallback_isProgramEquilibrium`): the best reply to `(DM, DM)` is
  worth `0` to either player, and every outcome of Table 2 is worth at least `0`.  Algorithm
  2, by contrast, is not participation independent in the Demand Game
  (`demandGame_algorithm2_not_participationIndependent`).

What is *not* claimed: that the fallback profile is always an equilibrium.  The criterion
`Prog.fallback_isProgramEquilibrium` is sufficient only; with the fair-coin representatives of
`demandRandomRepresentatives` the expected best reply to the baseline is `1` while the SPI
play is worth less to player 1, so the criterion is silent there.
-/

namespace SafeParetoImprovements

namespace Examples

open Two MeasureTheory Prog

/-! ### The Prisoner's Dilemma -/

/-- The fallback profile for the cooperative subset game. -/
noncomputable def pdFallback : Two → Prog prisonersDilemma :=
  fun _ => fallback prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf

/-- Everybody fallback executes the SPI `Π(Γˢ)`. -/
lemma pdFallback_plays :
    (programGame prisonersDilemma pdRepresentatives).Plays pdFallback
      fun ω => pdRepresentatives.play prisonersDilemmaCooperate ω :=
  plays_fallback pdRepresentatives prisonersDilemmaCooperate_isSubsetGameOf

/-- Both players' fallback instructions are participation independent. -/
lemma pdFallback_participationIndependent (i : Two) :
    (programGame prisonersDilemma pdRepresentatives).ParticipationIndependent
      (defaultInstr prisonersDilemma pdRepresentatives) pdFallback i :=
  participationIndependent_fallback_all pdRepresentatives prisonersDilemmaCooperate_isSubsetGameOf i

/-- The cooperative subset game has the single outcome `(C, C)`, so that is what its play is. -/
lemma pdRepresentatives_play_cooperate (ω : Unit) :
    pdRepresentatives.play prisonersDilemmaCooperate ω = fun _ => PD.cooperate := by
  funext i
  have h := pdRepresentatives.toPlay.mem prisonersDilemmaCooperate ω i
  simpa [prisonersDilemmaCooperate] using h

/-- The best reply to `(D, D)` is worth `2` at most. -/
lemma pd_bestReply_defect_le (i : Two) :
    prisonersDilemma.bestReply i (fun _ => PD.defect) ≤ 2 := by
  refine prisonersDilemma.bestReply_le i _ fun b _ => ?_
  have := prisonersDilemma_defect_bestResponse i b
  refine this.trans ?_
  cases i <;> norm_num [prisonersDilemma, pdPayoff]

/-- **The Prisoner's Dilemma's SPI is implementable by a participation-independent program
equilibrium**: the fallback profile is a program equilibrium, because the best reply to the
baseline `(D, D)` (worth `2`) is beaten by the SPI `(C, C)` (worth `3`). -/
lemma pd_fallback_isProgramEquilibrium :
    (programGame prisonersDilemma pdRepresentatives).IsProgramEquilibrium pdFallback := by
  refine fallback_isProgramEquilibrium pdRepresentatives prisonersDilemmaCooperate_isSubsetGameOf
    fun i => ?_
  have hL : (fun ω => prisonersDilemma.bestReply i (pdRepresentatives.play prisonersDilemma ω)) =
      fun _ => prisonersDilemma.bestReply i fun _ => PD.defect := by
    funext ω; rw [pdRepresentatives_play]
  have hR : (fun ω => prisonersDilemma.u (pdRepresentatives.play prisonersDilemmaCooperate ω) i) =
      fun _ => prisonersDilemma.u (fun _ => PD.cooperate) i := by
    funext ω; rw [pdRepresentatives_play_cooperate]
  rw [hL, hR, integral_const, integral_const, probReal_univ, one_smul, one_smul]
  refine (pd_bestReply_defect_le i).trans ?_
  cases i <;> norm_num [prisonersDilemma, pdPayoff]

/-- The three properties together: the fallback profile executes the SPI, is participation
independent for both players, and is a program equilibrium. -/
lemma pd_fallback_spi_participationIndependent_equilibrium :
    (programGame prisonersDilemma pdRepresentatives).Plays pdFallback
        (fun ω => pdRepresentatives.play prisonersDilemmaCooperate ω) ∧
      (∀ i, (programGame prisonersDilemma pdRepresentatives).ParticipationIndependent
        (defaultInstr prisonersDilemma pdRepresentatives) pdFallback i) ∧
      (programGame prisonersDilemma pdRepresentatives).IsProgramEquilibrium pdFallback :=
  ⟨pdFallback_plays, pdFallback_participationIndependent, pd_fallback_isProgramEquilibrium⟩

/-- Foreknowledge independence of `pdFallbackPolicy` by the general route: its uninformed
instruction is the (participation-independent) fallback, its informed one the baseline. -/
lemma pd_fallbackPolicy_foreknowledgeIndependent (c : Two → Prog prisonersDilemma)
    (hc : c Two.one = fallback prisonersDilemmaCooperate prisonersDilemmaCooperate_isSubsetGameOf) :
    (programGame prisonersDilemma pdRepresentatives).ForeknowledgeIndependent
      (defaultInstr prisonersDilemma pdRepresentatives) c pdFallbackPolicy :=
  foreknowledgeIndependent_of_participationIndependent pdRepresentatives c pdFallbackPolicy
    hc.symm (fun _ => rfl) (participationIndependent_fallback pdRepresentatives _ _ c Two.one hc)

/-! ### The Demand Game at the conflict outcome -/

/-- The fallback profile for Table 2. -/
noncomputable def demandFallback : Two → Prog demandGame :=
  fun _ => fallback demandSPI demandSPI.isSubsetGameOf

lemma demandFallback_plays :
    (programGame demandGame demandRepresentatives).Plays demandFallback
      fun ω => demandRepresentatives.play demandSPI ω :=
  plays_fallback demandRepresentatives demandSPI.isSubsetGameOf

lemma demandFallback_participationIndependent (i : Two) :
    (programGame demandGame demandRepresentatives).ParticipationIndependent
      (defaultInstr demandGame demandRepresentatives) demandFallback i :=
  participationIndependent_fallback_all demandRepresentatives demandSPI.isSubsetGameOf i

/-- Against the conflict outcome `(DM, DM)`, neither player can do better than `0`. -/
lemma demand_bestReply_conflict_le (i : Two) :
    demandGame.bestReply i (pair DAct.DM DAct.DM) ≤ 0 := by
  refine demandGame.bestReply_le i _ fun b _ => ?_
  cases i <;> cases b <;> norm_num [demandGame.u_apply, demandPayoff, pair,
    Function.update_of_ne (show Two.two ≠ Two.one by decide),
    Function.update_of_ne (show Two.one ≠ Two.two by decide)]

/-- Every outcome of Table 2 is worth at least `0` to each player (under the *original*
payoffs, which is what an SPI is judged by). -/
lemma demandSPI_u_nonneg (i : Two) {a : ∀ j, DUniverse j} (ha : a ∈ demandSPI.profiles) :
    0 ≤ demandGame.u a i := by
  have h1 := demandSPI.mem_S.1 (ha Two.one)
  have h2 := demandSPI.mem_S.1 (ha Two.two)
  rw [eq_pair a]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> cases i <;>
    norm_num [demandGame.u_apply, demandPayoff, pair]

/-- **The Demand Game's SPI is implementable by a participation-independent program
equilibrium at the conflict outcome**, where Proposition 18's threat-point route is
unavailable (`demandBook_not_threatPoint_le`): the best reply to `(DM, DM)` is worth `0`,
and every outcome of Table 2 is worth at least `0`. -/
lemma demand_fallback_isProgramEquilibrium :
    (programGame demandGame demandRepresentatives).IsProgramEquilibrium demandFallback := by
  refine fallback_isProgramEquilibrium demandRepresentatives demandSPI.isSubsetGameOf fun i => ?_
  have hL : (fun ω => demandGame.bestReply i (demandRepresentatives.play demandGame ω)) =
      fun _ => demandGame.bestReply i (pair DAct.DM DAct.DM) := by
    funext ω; rw [demandRepresentatives_play]
  rw [hL, integral_const, probReal_univ, one_smul]
  refine (demand_bestReply_conflict_le i).trans ?_
  exact integral_nonneg fun ω => demandSPI_u_nonneg i (demandRepresentatives.toPlay.mem demandSPI ω)

/-- The contrast in one statement: at the conflict outcome, Proposition 18's hypothesis
fails while the fallback profile executes the SPI, is participation independent for both
players, and is a program equilibrium. -/
lemma demand_fallback_where_algorithm2_is_uncertified :
    ¬ (∀ i, demandGame.threatPoint i ≤
        ∫ ω, demandGame.u (demandRepresentatives.play demandGame ω) i ∂demandRepresentatives.μ) ∧
      (programGame demandGame demandRepresentatives).Plays demandFallback
        (fun ω => demandRepresentatives.play demandSPI ω) ∧
      (∀ i, (programGame demandGame demandRepresentatives).ParticipationIndependent
        (defaultInstr demandGame demandRepresentatives) demandFallback i) ∧
      (programGame demandGame demandRepresentatives).IsProgramEquilibrium demandFallback :=
  ⟨demandBook_not_threatPoint_le, demandFallback_plays, demandFallback_participationIndependent,
    demand_fallback_isProgramEquilibrium⟩

/-- A foreknowledge-independent policy for player 1 in the Demand Game: fallback when
uninformed, the baseline when told player 2 will not participate. -/
noncomputable def demandFallbackPolicy :
    (programGame demandGame demandRepresentatives).Policy Two.one where
  Signal := Bool
  noInfo := false
  willNotParticipate _ := true
  policy
    | false => fallback demandSPI demandSPI.isSubsetGameOf
    | true => default demandGame

lemma demandFallbackPolicy_foreknowledgeIndependent :
    (programGame demandGame demandRepresentatives).ForeknowledgeIndependent
      (defaultInstr demandGame demandRepresentatives) demandFallback demandFallbackPolicy :=
  foreknowledgeIndependent_of_participationIndependent demandRepresentatives demandFallback
    demandFallbackPolicy rfl (fun _ => rfl) (demandFallback_participationIndependent Two.one)

/-! ### The criterion is silent for the random representatives

With the fair coin (`demandRandomRepresentatives`, baseline `(RM, RM)` or `(RM, DM)`), the
expected best reply of player 1 to the baseline is `(2 + 0)/2 = 1`.  Whether the fallback
profile is a program equilibrium there is not settled by `Prog.fallback_isProgramEquilibrium`
and is left as what it is: a question about which programs can exploit a fallback-playing
counterpart. -/

lemma demandRandom_bestReply_integral :
    (∫ ω, demandGame.bestReply Two.one (demandRandomRepresentatives.play demandGame ω)
        ∂demandRandomRepresentatives.μ) = 1 := by
  simp only [demandRandom_play]
  show (∫ ω, demandGame.bestReply Two.one (demandPages ω) ∂coin) = _
  rw [integral_coin]
  have hT : demandGame.bestReply Two.one (demandPages true) = 2 := by
    refine le_antisymm (demandGame.bestReply_le _ _ fun b _ => ?_) ?_
    · cases b <;> norm_num [demandGame.u_apply, demandPayoff, demandPages, pair,
        Function.update_of_ne (show Two.two ≠ Two.one by decide)]
    · have := demandGame.u_update_le_bestReply Two.one (demandPages true)
        (a := DAct.DM) (Finset.mem_univ _)
      refine le_trans (le_of_eq ?_) this
      norm_num [demandGame.u_apply, demandPayoff, demandPages, pair,
        Function.update_of_ne (show Two.two ≠ Two.one by decide)]
  have hF : demandGame.bestReply Two.one (demandPages false) = 0 := by
    refine le_antisymm (demandGame.bestReply_le _ _ fun b _ => ?_) ?_
    · cases b <;> norm_num [demandGame.u_apply, demandPayoff, demandPages, pair,
        Function.update_of_ne (show Two.two ≠ Two.one by decide)]
    · have := demandGame.u_update_le_bestReply Two.one (demandPages false)
        (a := DAct.RM) (Finset.mem_univ _)
      refine le_trans (le_of_eq ?_) this
      norm_num [demandGame.u_apply, demandPayoff, demandPages, pair,
        Function.update_of_ne (show Two.two ≠ Two.one by decide)]
  rw [hT, hF]; norm_num

end Examples

end SafeParetoImprovements
