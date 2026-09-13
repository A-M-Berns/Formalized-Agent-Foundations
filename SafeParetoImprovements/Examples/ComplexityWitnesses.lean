import SafeParetoImprovements.Hardness
import SafeParetoImprovements.Examples.Witnesses

/-!
# Non-vacuity for the complexity nodes

* **Propositions 23 and 25 are two-sided.**  The Demand Game's strict SPI is a certificate
  (`demandCertificate`, read off the paper's own isomorphism) that passes the strict check
  and the non-triviality check; the Complicated Temptation Game supplies a unilateral
  certificate through Proposition 25; and a one-action game has exactly one certificate,
  the identity, which the printed algorithm would accept (erratum D17) but which fails
  non-triviality, so the repaired algorithm answers *no* (`oneAction_not_certificate`).
* **The search bound is a bound.**  The Demand Game has `144` certificates against the
  bound `8 ^ 4 = 4096` (`card_demandCertificate`).
* **Lemma 28 is two-sided on concrete graphs.**  The empty graph on two vertices embeds in
  the complete one, so the constructed game has a strict unilateral SPI; the complete
  graph does not embed in the empty one, so the constructed game has no SPI at all.  Both
  verdicts are carried through Lemma 28 to the `Game.SPIDecision` predicates themselves,
  on games with twelve actions per player (`size_hardGame`).
-/

namespace SafeParetoImprovements

namespace Examples

open Two

/-! ### Proposition 23 on the Demand Game -/

/-- The Demand Game's certificate: player 1's `DM ↦ DL`, `RM ↦ RL`, and likewise for
player 2 — the paper's `demilitarize`, read off `demandReduceIso`. -/
noncomputable def demandCertificate : demandGame.Certificate :=
  Game.Certificate.ofIso demandSPI.isSubsetGameOf demandReduceIso

/-- The certificate sends the surviving outcome `(DM, DM)` to `(DL, DL)`. -/
lemma demandCertificate_map_DM :
    demandCertificate.map (pair DAct.DM DAct.DM) = pair DAct.DL DAct.DL := by
  rw [demandCertificate, Game.Certificate.ofIso_map _ _ demandGame_pair_DM_mem_reduce,
    demandReduceIso, GameIso.cast_map]
  funext i
  cases i <;> rfl

/-- The certificate passes the strict check and the non-triviality check: Algorithm D.2.1
(with the omitted check restored) answers *yes* on the Demand Game. -/
lemma demandCertificate_check :
    demandCertificate.StrictlyParetoImproving ∧ demandCertificate.Nontrivial := by
  refine ⟨⟨fun a ha => ?_, pair DAct.DM DAct.DM, demandGame_pair_DM_mem_reduce, ?_⟩,
    Game.Certificate.ofIso_nontrivial _ _ demandGame_reduce_S_ne⟩
  · rw [demandCertificate, Game.Certificate.ofIso_map _ _ ha]
    simpa only [Game.reduce_u] using demandReduceIso_paretoImproving a ha
  · rw [demandCertificate, Game.Certificate.ofIso_map _ _ demandGame_pair_DM_mem_reduce]
    refine Pi.lt_def.2 ⟨by simpa only [Game.reduce_u] using
      demandReduceIso_paretoImproving _ demandGame_pair_DM_mem_reduce, .one, ?_⟩
    rw [demandReduceIso, GameIso.cast_map]
    show demandGame.u (pair DAct.DM DAct.DM) .one <
      demandGame.u (pair (demilitarize DAct.DM) (demilitarize DAct.DM)) .one
    norm_num [demandGame.u_apply, demandPayoff, demilitarize]

/-- Proposition 23, "yes" direction, on the Demand Game: the certificate is the witness. -/
lemma demandGame_strictSPIDecision_of_certificate : demandGame.StrictSPIDecision :=
  (demandGame.strictSPIDecision_iff_certificate).2 ⟨demandCertificate, demandCertificate_check⟩

/-- A one-action game (both players have the single action `()`) has one certificate — the
identity — which passes the printed algorithm's Pareto check but not the non-triviality
check, so Proposition 23 answers *no*, matching `not_spiDecision_of_card_le_one`. -/
def oneAction : Game Two (fun _ => Unit) where
  S _ := Finset.univ
  nonempty _ := Finset.univ_nonempty
  u _ _ := 0

lemma oneAction_certificate_eq_refl (c : oneAction.Certificate) :
    c = Game.Certificate.refl oneAction := by
  funext i
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  exact Subsingleton.elim _ _

lemma oneAction_not_certificate :
    ¬ ∃ c : oneAction.Certificate, c.ParetoImproving ∧ c.Nontrivial := by
  rintro ⟨c, -, hnt⟩
  rw [oneAction_certificate_eq_refl c] at hnt
  exact Game.Certificate.not_refl_nontrivial _ hnt

lemma oneAction_paretoImproving_refl : (Game.Certificate.refl oneAction).ParetoImproving :=
  Game.Certificate.refl_paretoImproving _

/-! ### Proposition 25 on the Complicated Temptation Game -/

/-- Proposition 25 turns the Complicated Temptation Game's unilateral SPI into a unilateral
certificate: some player `i` and injections passing all three checks. -/
lemma complicatedTemptation_unilateralCertificate :
    ∃ (i : Two) (c : complicatedTemptation.Certificate),
      c.ParetoImproving ∧ c.Nontrivial ∧ c.Affine i ∧ c.ReducesToImage i :=
  (complicatedTemptation.unilateralSPIDecision_iff_certificate).1
    complicatedTemptation_unilateralSPIDecision

/-! ### The search bound on the Demand Game -/

/-- The Demand Game has `4` actions per player and `2` per player after reduction, so
`12 · 12 = 144` certificates, against the bound `8 ^ 4 = 4096`. -/
lemma card_demandCertificate : Fintype.card demandGame.Certificate = 144 := by
  rw [Fintype.card_pi]
  have h : ∀ i : Two, Fintype.card ({x // x ∈ demandGame.reduce.S i} ↪ {x // x ∈ demandGame.S i}) = 12 := by
    intro i
    rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_coe, demandGame.reduce_eq,
      demandGame.reducedGame_S, demandGame.S_eq]
    rfl
  have h2 : Fintype.card Two = 2 := rfl
  simp [h, h2]

lemma demandGame_size : demandGame.size = 8 := rfl

lemma demandGame_reduce_size : demandGame.reduce.size = 4 := by
  have h2 : Fintype.card Two = 2 := rfl
  simp [Game.size, demandGame.reduce_eq, demandGame.reducedGame_S, h2]

lemma card_demandCertificate_le : Fintype.card demandGame.Certificate ≤ 4096 := by
  have := demandGame.card_certificate_le
  rwa [demandGame_size, demandGame_reduce_size] at this

/-! ### Lemma 28 on concrete graphs -/

open Hardness

/-- The empty graph on two vertices. -/
def emptyTwo : Graph 2 := fun _ _ => false

/-- The complete graph on two vertices. -/
def completeTwo : Graph 2 := fun _ _ => true

lemma subgraphIso_emptyTwo_completeTwo : SubgraphIsoProblem emptyTwo completeTwo :=
  ⟨Function.Embedding.refl _, fun _ _ _ => by simp [emptyTwo, completeTwo]⟩

lemma not_subgraphIso_completeTwo_emptyTwo : ¬ SubgraphIsoProblem completeTwo emptyTwo := by
  rintro ⟨φ, hφ⟩
  have := hφ 0 1 (by decide)
  simp only [completeTwo, emptyTwo] at this
  exact absurd this (by decide)

/-- The two constructed games, with `ε = 1/8` (`< 1/(2·2)`). -/
noncomputable def hardYes : Game Two (HardUniverse 2 2) := hardnessGame emptyTwo completeTwo (1/8)

noncomputable def hardNo : Game Two (HardUniverse 2 2) := hardnessGame completeTwo emptyTwo (1/8)

lemma size_hardGame : hardYes.size = 24 ∧ hardNo.size = 24 := by
  constructor <;> simp [hardYes, hardNo, size_hardnessGame]

/-- **A "yes" instance of every SPI decision problem through Lemma 28**: the game built from
`(emptyTwo, completeTwo)` has a strict unilateral SPI. -/
lemma hardYes_strictUnilateralSPIDecision : hardYes.StrictUnilateralSPIDecision :=
  (subgraphIsoProblem_iff_strictUnilateralSPIDecision emptyTwo completeTwo (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1 subgraphIso_emptyTwo_completeTwo

/-- **A "no" instance through Lemma 28**: the game built from `(completeTwo, emptyTwo)` has no
SPI of any kind. -/
lemma hardNo_not_spiDecision : ¬ hardNo.SPIDecision := fun h =>
  not_subgraphIso_completeTwo_emptyTwo
    ((subgraphIsoProblem_iff_spiDecision completeTwo emptyTwo (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2 h)

end Examples

end SafeParetoImprovements
