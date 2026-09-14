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
* **Lemma 28 is two-sided on concrete graphs.**  The one-edge graph on two vertices embeds
  in the two-cycle, so the constructed game has a strict unilateral SPI; the two-cycle does
  not embed in the one-edge graph,
  so the constructed game has no SPI at all.  Both verdicts are carried through Lemma 28 to
  the `Game.SPIDecision` predicates themselves, on games with twelve actions per player
  (`size_hardGame`).
* **The unilateral checks bite.**  The Demand Game's certificate fails check 2 for either
  player (`demandCertificate_not_affine`), and `scaledGame` is a four-action game
  whose certificate passes all of Proposition 25's checks with the affine scale forced to
  `λ = 2` (`scaledGame.cert_affine_scale_eq_two`).
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

/-- The one-edge graph on two vertices, `0 → 1`. -/
def oneEdge : Graph 2 := fun i j => decide (i = 0 ∧ j = 1)

/-- The two-cycle on two vertices, `0 → 1 → 0`. -/
def twoCycle : Graph 2 := fun i j => decide (i ≠ j)

/-- The one-edge graph embeds in the two-cycle (only as the identity or the swap; the
edge condition is exercised at the true edge `0 → 1`). -/
lemma subgraphIso_oneEdge_twoCycle : SubgraphIsoProblem oneEdge twoCycle :=
  ⟨Function.Embedding.refl _, fun j l h => by
    fin_cases j <;> fin_cases l <;> simp_all [oneEdge, twoCycle]⟩

/-- The two-cycle does not embed in the one-edge graph: whichever way the two vertices are
mapped, one of the two edges lands on a non-edge. -/
lemma not_subgraphIso_twoCycle_oneEdge : ¬ SubgraphIsoProblem twoCycle oneEdge := by
  rintro ⟨φ, hφ⟩
  have h01 := hφ 0 1 (by decide)
  have h10 := hφ 1 0 (by decide)
  simp only [twoCycle, oneEdge] at h01 h10
  have hne : φ 0 ≠ φ 1 := φ.injective.ne (by decide)
  generalize φ 0 = p at *
  generalize φ 1 = q at *
  fin_cases p <;> fin_cases q <;> simp_all <;> exact absurd ‹true ≤ false› (by decide)

/-- The two constructed games, with `ε = 1/8` (`< 1/(2·2)`). -/
noncomputable def hardYes : Game Two (HardUniverse 2 2) := hardnessGame oneEdge twoCycle (1/8)

noncomputable def hardNo : Game Two (HardUniverse 2 2) := hardnessGame twoCycle oneEdge (1/8)

lemma size_hardGame : hardYes.size = 24 ∧ hardNo.size = 24 := by
  constructor <;> simp [hardYes, hardNo, size_hardnessGame]

/-- **A "yes" instance of every SPI decision problem through Lemma 28**: the game built from
`(oneEdge, twoCycle)` has a strict unilateral SPI.  The source graph has an edge, so the
subgraph condition `a(0,1) ≤ â(φ 0, φ 1)` is checked at a true edge. -/
lemma hardYes_strictUnilateralSPIDecision : hardYes.StrictUnilateralSPIDecision :=
  (subgraphIsoProblem_iff_strictUnilateralSPIDecision oneEdge twoCycle (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).1 subgraphIso_oneEdge_twoCycle

/-- **A "no" instance through Lemma 28**: the game built from `(twoCycle, oneEdge)` has no
SPI of any kind. -/
lemma hardNo_not_spiDecision : ¬ hardNo.SPIDecision := fun h =>
  not_subgraphIso_twoCycle_oneEdge
    ((subgraphIsoProblem_iff_spiDecision twoCycle oneEdge (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2 h)

/-! ### The unilateral checks reject: the Demand Game certificate fails check 2 -/

lemma demandCertificate_map {a b : DAct} (ha : a = .DM ∨ a = .RM) (hb : b = .DM ∨ b = .RM) :
    demandCertificate.map (pair a b) = pair (demilitarize a) (demilitarize b) := by
  have hmem : pair a b ∈ demandGame.reduce.profiles := by
    rw [demandGame.reduce_eq]
    intro i; cases i
    · exact demandGame.reducedGame_mem_S.2 ha
    · exact demandGame.reducedGame_mem_S.2 hb
  rw [demandCertificate, Game.Certificate.ofIso_map _ _ hmem, demandReduceIso, GameIso.cast_map]
  funext i
  cases i <;> rfl

/-- **Check 2 bites**: the Demand Game's certificate passes Proposition 23's checks
(`demandCertificate_check`) but fails the affine check of Proposition 25 for either
player, because the other player's payoffs on `{DL, RL}²` are not a positive affine image
of hers on `{DM, RM}²`: for player 2, `(−3, 0, 2, 1)` against `(1, 0, 2, 1)`
forces `κ = 0` and then `λ = −3`. -/
lemma demandCertificate_not_affine :
    ¬ demandCertificate.Affine .one ∧ ¬ demandCertificate.Affine .two := by
  have hDD : pair DAct.DM DAct.DM ∈ demandGame.reduce.profiles := demandGame_pair_DM_mem_reduce
  have hDR : pair DAct.DM DAct.RM ∈ demandGame.reduce.profiles := by
    rw [demandGame.reduce_eq]; intro i; cases i <;> simp [demandGame.reducedGame_mem_S]
  have hRD : pair DAct.RM DAct.DM ∈ demandGame.reduce.profiles := by
    rw [demandGame.reduce_eq]; intro i; cases i <;> simp [demandGame.reducedGame_mem_S]
  constructor
  · rintro hA
    obtain ⟨l, hl, k, h⟩ := hA .two (by decide)
    have h1 := h _ hDD
    have h2 := h _ hDR
    have h3 := h _ hRD
    rw [demandCertificate_map (Or.inl rfl) (Or.inl rfl)] at h1
    rw [demandCertificate_map (Or.inl rfl) (Or.inr rfl)] at h2
    rw [demandCertificate_map (Or.inr rfl) (Or.inl rfl)] at h3
    norm_num [demandGame.u_apply, demandPayoff, demilitarize] at h1 h2 h3
    linarith
  · rintro hA
    obtain ⟨l, hl, k, h⟩ := hA .one (by decide)
    have h1 := h _ hDD
    have h2 := h _ hDR
    have h3 := h _ hRD
    rw [demandCertificate_map (Or.inl rfl) (Or.inl rfl)] at h1
    rw [demandCertificate_map (Or.inl rfl) (Or.inr rfl)] at h2
    rw [demandCertificate_map (Or.inr rfl) (Or.inl rfl)] at h3
    norm_num [demandGame.u_apply, demandPayoff, demilitarize] at h1 h2 h3
    linarith

/-! ### Check 2 with a scale other than `1`

A four-action game whose reduction is the `{a0, a1}` block and whose `{a2, a3}` block is
player 2's payoffs halved: the certificate `a0 ↦ a2`, `a1 ↦ a3` passes all of
Proposition 25's checks for `i = player 1`, and its check-2 scale for player 2 is forced to
be `λ = 2`. -/

/-- The four actions. -/
inductive SAct | a0 | a1 | a2 | a3
  deriving DecidableEq, Fintype

abbrev SUniverse : Two → Type := fun _ => SAct

/-- Player 1's payoffs: `(1, 0; 0, 1)` on the reduced block, `(2, 1; 1, 2)` on the image block,
`5` in the columns `a2, a3` of the rows `a0, a1` (so those rows dominate `a2, a3`), `−1`
elsewhere. -/
def scaledU₁ : SAct → SAct → ℝ
  | .a0, .a0 => 1 | .a0, .a1 => 0 | .a0, .a2 => 5 | .a0, .a3 => 5
  | .a1, .a0 => 0 | .a1, .a1 => 1 | .a1, .a2 => 5 | .a1, .a3 => 5
  | .a2, .a0 => -1 | .a2, .a1 => -1 | .a2, .a2 => 2 | .a2, .a3 => 1
  | .a3, .a0 => -1 | .a3, .a1 => -1 | .a3, .a2 => 1 | .a3, .a3 => 2

/-- Player 2's payoffs: `(−2, −4; −4, −2)` on the reduced block, half of it `(−1, −2; −2, −1)`
on the image block, `−5` off the blocks. -/
def scaledU₂ : SAct → SAct → ℝ
  | .a0, .a0 => -2 | .a0, .a1 => -4 | .a0, .a2 => -5 | .a0, .a3 => -5
  | .a1, .a0 => -4 | .a1, .a1 => -2 | .a1, .a2 => -5 | .a1, .a3 => -5
  | .a2, .a0 => -5 | .a2, .a1 => -5 | .a2, .a2 => -1 | .a2, .a3 => -2
  | .a3, .a0 => -5 | .a3, .a1 => -5 | .a3, .a2 => -2 | .a3, .a3 => -1

def scaledGame : Game Two SUniverse where
  S _ := Finset.univ
  nonempty _ := ⟨.a0, Finset.mem_univ _⟩
  u x := pair (scaledU₁ (x .one) (x .two)) (scaledU₂ (x .one) (x .two))

namespace scaledGame

lemma u_pair (a b : SAct) : scaledGame.u (pair a b) = pair (scaledU₁ a b) (scaledU₂ a b) := rfl

/-- The reduced block `{a0, a1}²`. -/
def block : Finset SAct := {.a0, .a1}

def reducedGame : Game Two SUniverse := ⟨fun _ => block, fun _ => ⟨.a0, by simp [block]⟩, scaledGame.u⟩

lemma reducedGame_reduced : reducedGame.Reduced := by
  rw [reduced_iff]
  constructor
  · intro x hx
    have hxm : x ∈ block := hx.mem
    revert hx
    simp only [block, Finset.mem_insert, Finset.mem_singleton] at hxm
    rcases hxm with rfl | rfl
    · refine not_isStrictlyDominated_one_of_bestResponse _ (show SAct.a0 ∈ block by simp [block])
        fun a' ha' => ?_
      change a' ∈ block at ha'
      simp only [block, Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl <;> norm_num [reducedGame, u_pair, scaledU₁]
    · refine not_isStrictlyDominated_one_of_bestResponse _ (show SAct.a1 ∈ block by simp [block])
        fun a' ha' => ?_
      change a' ∈ block at ha'
      simp only [block, Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl <;> norm_num [reducedGame, u_pair, scaledU₁]
  · intro x hx
    have hxm : x ∈ block := hx.mem
    revert hx
    simp only [block, Finset.mem_insert, Finset.mem_singleton] at hxm
    rcases hxm with rfl | rfl
    · refine not_isStrictlyDominated_two_of_bestResponse _ (show SAct.a0 ∈ block by simp [block])
        fun a' ha' => ?_
      change a' ∈ block at ha'
      simp only [block, Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl <;> norm_num [reducedGame, u_pair, scaledU₂]
    · refine not_isStrictlyDominated_two_of_bestResponse _ (show SAct.a1 ∈ block by simp [block])
        fun a' ha' => ?_
      change a' ∈ block at ha'
      simp only [block, Finset.mem_insert, Finset.mem_singleton] at ha'
      rcases ha' with rfl | rfl <;> norm_num [reducedGame, u_pair, scaledU₂]

/-- Rows `a2, a3` are dominated by `a0`; then columns `a2, a3` by `a0`. -/
lemma reduce_eq : scaledGame.reduce = reducedGame := by
  let T₁ : ∀ i, Finset (SUniverse i) := pair block Finset.univ
  have hne₁ : ∀ i, (T₁ i).Nonempty := by
    intro i; cases i
    · exact ⟨.a0, show SAct.a0 ∈ block by simp [block]⟩
    · exact ⟨.a0, Finset.mem_univ _⟩
  have hA : scaledGame.ElimStar ⟨T₁, hne₁, scaledGame.u⟩ := by
    refine Game.elimStar_of_dominated _ T₁ hne₁ (fun i => Finset.subset_univ _) fun i x hx hxT => ?_
    cases i
    · refine ⟨.a0, show SAct.a0 ∈ block by simp [block], ?_⟩
      rw [strictlyDominates_one_iff]
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, fun z _ => ?_⟩
      change x ∉ block at hxT
      have hx' : x = .a2 ∨ x = .a3 := by
        cases x <;> simp_all [block]
      rcases hx' with rfl | rfl <;> cases z <;> norm_num [u_pair, scaledU₁]
    · exact absurd (Finset.mem_univ x) hxT
  have hB : (⟨T₁, hne₁, scaledGame.u⟩ : Game Two SUniverse).ElimStar reducedGame := by
    refine Game.elimStar_of_dominated _ (fun _ => block) (fun _ => ⟨.a0, by simp [block]⟩)
      (fun i => ?_) fun i x hx hxT => ?_
    · cases i
      · exact Finset.Subset.refl _
      · exact Finset.subset_univ _
    · cases i
      · exact absurd hx hxT
      · refine ⟨.a0, by simp [block], ?_⟩
        rw [strictlyDominates_two_iff]
        refine ⟨Finset.mem_univ _, Finset.mem_univ _, fun z hz => ?_⟩
        have hx' : x = .a2 ∨ x = .a3 := by
          cases x <;> simp_all [block]
        change z ∈ block at hz
        have hz' : z = .a0 ∨ z = .a1 := by
          simpa [block] using hz
        rcases hx' with rfl | rfl <;> rcases hz' with rfl | rfl <;> norm_num [u_pair, scaledU₂]
  exact Game.reduce_eq_of_reduced_of_elimStar (hA.trans hB) reducedGame_reduced

lemma mem_reduce_S_iff (i : Two) (x : SAct) :
    x ∈ scaledGame.reduce.S i ↔ x = .a0 ∨ x = .a1 := by
  rw [reduce_eq]; simp [reducedGame, block]

/-- `a0 ↦ a2`, `a1 ↦ a3`. -/
def shift : SAct → SAct
  | .a0 => .a2 | .a1 => .a3 | x => x

/-- The certificate. -/
def cert : scaledGame.Certificate := fun i =>
  ⟨fun x => ⟨shift x.1, Finset.mem_univ _⟩, fun x y h => by
    have hx := (mem_reduce_S_iff i x.1).1 x.2
    have hy := (mem_reduce_S_iff i y.1).1 y.2
    have h' := congrArg Subtype.val h
    apply Subtype.ext
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all [shift]⟩

lemma cert_toFun {i : Two} {x : SAct} (hx : x = .a0 ∨ x = .a1) : cert.toFun i x = shift x := by
  rw [Game.Certificate.toFun_of_mem _ ((mem_reduce_S_iff i x).2 hx)]; rfl

lemma cert_map {a b : SAct} (ha : a = .a0 ∨ a = .a1) (hb : b = .a0 ∨ b = .a1) :
    cert.map (pair a b) = pair (shift a) (shift b) := by
  funext i; cases i
  · exact cert_toFun ha
  · exact cert_toFun hb

lemma mem_reduce_profiles_iff (b : ∀ i, SUniverse i) :
    b ∈ scaledGame.reduce.profiles ↔ (b .one = .a0 ∨ b .one = .a1) ∧ (b .two = .a0 ∨ b .two = .a1) := by
  rw [Game.mem_profiles]
  constructor
  · intro h; exact ⟨(mem_reduce_S_iff _ _).1 (h .one), (mem_reduce_S_iff _ _).1 (h .two)⟩
  · rintro ⟨h1, h2⟩ i; cases i
    · exact (mem_reduce_S_iff _ _).2 h1
    · exact (mem_reduce_S_iff _ _).2 h2

lemma mem_cert_image_iff (i : Two) (x : SAct) : x ∈ cert.image i ↔ x = .a2 ∨ x = .a3 := by
  simp only [Game.Certificate.image, Finset.mem_image, mem_reduce_S_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [cert_toFun hy]; rcases hy with rfl | rfl <;> simp [shift]
  · rintro (rfl | rfl)
    · exact ⟨.a0, Or.inl rfl, by rw [cert_toFun (Or.inl rfl)]; rfl⟩
    · exact ⟨.a1, Or.inr rfl, by rw [cert_toFun (Or.inr rfl)]; rfl⟩

lemma cert_paretoImproving : cert.StrictlyParetoImproving := by
  refine ⟨fun b hb => ?_, pair .a0 .a0, (mem_reduce_profiles_iff _).2 ⟨Or.inl rfl, Or.inl rfl⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := (mem_reduce_profiles_iff b).1 hb
    rw [eq_pair b, cert_map h1 h2]
    intro i
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> cases i <;>
      norm_num [u_pair, scaledU₁, scaledU₂, shift]
  · rw [cert_map (Or.inl rfl) (Or.inl rfl)]
    refine Pi.lt_def.2 ⟨fun i => by cases i <;> norm_num [u_pair, scaledU₁, scaledU₂, shift], .one, ?_⟩
    norm_num [u_pair, scaledU₁, shift]

lemma cert_nontrivial : cert.Nontrivial :=
  ⟨.one, fun h => by
    have : SAct.a0 ∈ cert.image .one := by rw [h]; exact (mem_reduce_S_iff _ _).2 (Or.inl rfl)
    rw [mem_cert_image_iff] at this
    rcases this with h | h <;> cases h⟩

/-- Check 2 for `i = player 1` holds with `λ = 2, κ = 0`. -/
lemma cert_affine : cert.Affine .one := by
  intro j hj
  cases j
  · exact absurd rfl hj
  refine ⟨2, by norm_num, 0, fun b hb => ?_⟩
  obtain ⟨h1, h2⟩ := (mem_reduce_profiles_iff b).1 hb
  rw [eq_pair b, cert_map h1 h2]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;>
    simp [u_pair, scaledU₂, shift] <;> norm_num

/-- **The scale is forced to be `2`**: any `(λ, κ)` witnessing check 2 for player 2 has
`λ = 2` (and `κ = 0`), so `Certificate.affineScale` is not always `1`. -/
lemma cert_affine_scale_eq_two (l k : ℝ)
    (h : ∀ b ∈ scaledGame.reduce.profiles, scaledGame.u b .two = l * scaledGame.u (cert.map b) .two + k) :
    l = 2 ∧ k = 0 := by
  have h1 := h (pair .a0 .a0) ((mem_reduce_profiles_iff _).2 ⟨Or.inl rfl, Or.inl rfl⟩)
  have h2 := h (pair .a0 .a1) ((mem_reduce_profiles_iff _).2 ⟨Or.inl rfl, Or.inr rfl⟩)
  rw [cert_map (Or.inl rfl) (Or.inl rfl)] at h1
  rw [cert_map (Or.inl rfl) (Or.inr rfl)] at h2
  simp [u_pair, scaledU₂, shift] at h1 h2
  constructor <;> linarith

/-- Check 3: the candidate reduces to the image block (columns `a0, a1` are dominated by `a2`
against the rows `a2, a3`). -/
lemma cert_reducesToImage : cert.ReducesToImage .one := by
  refine cert.reducesToImage_of_dominated .one cert_affine fun j hj x _ hxI => ?_
  cases j
  · exact absurd rfl hj
  refine ⟨.a2, (mem_cert_image_iff _ _).2 (Or.inl rfl), ?_⟩
  rw [strictlyDominates_two_iff]
  refine ⟨by rw [cert.unilateralGame_S_of_ne .one hj]; exact Finset.mem_univ _,
    by rw [cert.unilateralGame_S_of_ne .one hj]; exact Finset.mem_univ _, fun r hr => ?_⟩
  rw [Game.Certificate.unilateralGame_S_self, mem_cert_image_iff] at hr
  rw [cert.unilateralGame_u_of_ne .one _ hj, cert.unilateralGame_u_of_ne .one _ hj]
  have hx : x = .a0 ∨ x = .a1 := by
    rw [mem_cert_image_iff] at hxI
    cases x <;> simp_all
  rcases hr with rfl | rfl <;> rcases hx with rfl | rfl <;> norm_num [u_pair, scaledU₂]

/-- The game has a strict unilateral SPI (through Proposition 25) whose certificate carries a
non-unit affine scale. -/
lemma strictUnilateralSPIDecision : scaledGame.StrictUnilateralSPIDecision :=
  (scaledGame.strictUnilateralSPIDecision_iff_certificate).2
    ⟨.one, cert, cert_paretoImproving, cert_nontrivial, cert_affine, cert_reducesToImage⟩

end scaledGame

end Examples

end SafeParetoImprovements
