import SafeParetoImprovements.Examples.TwoPlayer

/-!
# Proposition 6: the Demand Game (Tables 1 and 2)

The Demand Game (Table 1): each country demands (`D`) or refrains (`R`), with (`M`) or
without (`L`) a military.

|    | DM     | RM    | DL     | RL     |
|----|--------|-------|--------|--------|
| DM | −3, −3 | 2, 0  | 5, −5  | 5, −5  |
| RM | 0, 2   | 1, 1  | 5, −5  | 5, −5  |
| DL | −5, 5  | −5, 5 | 1, 1   | 2, 0   |
| RL | −5, 5  | −5, 5 | 0, 2   | 1, 1   |

Militarizing strictly dominates not militarizing, so the game fully reduces to the
`{DM, RM}` game.  The SPI of Table 2 keeps only `{DL, RL}` for both players and tells the
representatives to value those outcomes as the militarized ones are valued in the
original game (`(DL, DL) ↦ (−3, −3)`, `(DL, RL) ↦ (2, 0)`, `(RL, DL) ↦ (0, 2)`,
`(RL, RL) ↦ (1, 1)`), which makes it isomorphic to the reduced game via `DM ↦ DL`,
`RM ↦ RL`.  For the *original* players, the conflict outcome `(DL, DL)` is worth `(1, 1)`
instead of `(−3, −3)`, and every other outcome is worth the same.

Proposition 6: under Assumptions 1 and 2, Table 2 is an SPI on the Demand Game; if
`(DM, DM)` is played with positive probability, it is a strict SPI.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter Two
open scoped SetRel

/-- The Demand Game's actions. -/
inductive DAct | DM | RM | DL | RL
  deriving DecidableEq, Fintype, Inhabited

/-- Both players choose from `DAct`. -/
abbrev DUniverse : Two → Type := fun _ => DAct

/-- Table 1. -/
def demandPayoff : DAct → DAct → Two → ℝ
  | .DM, .DM, _ => -3
  | .DM, .RM, .one => 2
  | .DM, .RM, .two => 0
  | .DM, .DL, .one => 5
  | .DM, .DL, .two => -5
  | .DM, .RL, .one => 5
  | .DM, .RL, .two => -5
  | .RM, .DM, .one => 0
  | .RM, .DM, .two => 2
  | .RM, .RM, _ => 1
  | .RM, .DL, .one => 5
  | .RM, .DL, .two => -5
  | .RM, .RL, .one => 5
  | .RM, .RL, .two => -5
  | .DL, .DM, .one => -5
  | .DL, .DM, .two => 5
  | .DL, .RM, .one => -5
  | .DL, .RM, .two => 5
  | .DL, .DL, _ => 1
  | .DL, .RL, .one => 2
  | .DL, .RL, .two => 0
  | .RL, .DM, .one => -5
  | .RL, .DM, .two => 5
  | .RL, .RM, .one => -5
  | .RL, .RM, .two => 5
  | .RL, .DL, .one => 0
  | .RL, .DL, .two => 2
  | .RL, .RL, _ => 1

/-- Table 2's payoffs for the representatives, on `{DL, RL}²` (and `0` elsewhere, which
is outside the subset game's profiles and therefore meaningless — `dd:total-utility`). -/
def spiPayoff : DAct → DAct → Two → ℝ
  | .DL, .DL, _ => -3
  | .DL, .RL, .one => 2
  | .DL, .RL, .two => 0
  | .RL, .DL, .one => 0
  | .RL, .DL, .two => 2
  | .RL, .RL, _ => 1
  | _, _, _ => 0

/-- The Demand Game (Table 1). -/
def demandGame : Game Two DUniverse where
  S _ := Finset.univ
  nonempty _ := ⟨.DM, Finset.mem_univ _⟩
  u a i := demandPayoff (a .one) (a .two) i

/-- The subset game of Table 2. -/
def demandSPI : Game Two DUniverse where
  S _ := {DAct.DL, DAct.RL}
  nonempty _ := ⟨.DL, Finset.mem_insert_self _ _⟩
  u a i := spiPayoff (a .one) (a .two) i

namespace demandGame

lemma S_eq (i : Two) : demandGame.S i = Finset.univ := rfl
lemma u_apply (a : ∀ i, DUniverse i) (i : Two) :
    demandGame.u a i = demandPayoff (a .one) (a .two) i := rfl

/-! ### The four eliminations -/

lemma dom1 : demandGame.IsStrictlyDominated .one .DL :=
  ⟨.DM, (strictlyDominates_one_iff _ _ _).2 ⟨Finset.mem_univ _, Finset.mem_univ _,
    fun x _ => by cases x <;> norm_num [u_apply, demandPayoff]⟩⟩

/-- After removing player 1's `DL`. -/
def g1 : Game Two DUniverse := demandGame.erase .one .DL dom1.erase_nonempty

lemma g1_u : g1.u = demandGame.u := rfl
lemma g1_S_one : g1.S .one = {DAct.DM, DAct.RM, DAct.RL} := by
  rw [g1, Game.erase_S_self]; decide
lemma g1_S_two : g1.S .two = Finset.univ := by
  rw [g1, Game.erase_S_of_ne _ _ _ _ (by decide)]; rfl

lemma dom2 : g1.IsStrictlyDominated .one .RL :=
  ⟨.DM, (strictlyDominates_one_iff _ _ _).2 ⟨by rw [g1_S_one]; decide, by rw [g1_S_one]; decide,
    fun x _ => by cases x <;> norm_num [g1_u, u_apply, demandPayoff]⟩⟩

/-- After removing player 1's `DL` and `RL`. -/
def g2 : Game Two DUniverse := g1.erase .one .RL dom2.erase_nonempty

lemma g2_u : g2.u = demandGame.u := rfl
lemma g2_S_one : g2.S .one = {DAct.DM, DAct.RM} := by
  rw [g2, Game.erase_S_self, g1_S_one]; decide
lemma g2_S_two : g2.S .two = Finset.univ := by
  rw [g2, Game.erase_S_of_ne _ _ _ _ (by decide), g1_S_two]

lemma dom3 : g2.IsStrictlyDominated .two .DL :=
  ⟨.DM, (strictlyDominates_two_iff _ _ _).2 ⟨by rw [g2_S_two]; exact Finset.mem_univ _,
    by rw [g2_S_two]; exact Finset.mem_univ _, fun a ha => by
      rw [g2_S_one] at ha
      cases a <;> simp at ha <;> norm_num [g2_u, u_apply, demandPayoff]⟩⟩

/-- After additionally removing player 2's `DL`. -/
def g3 : Game Two DUniverse := g2.erase .two .DL dom3.erase_nonempty

lemma g3_u : g3.u = demandGame.u := rfl
lemma g3_S_one : g3.S .one = {DAct.DM, DAct.RM} := by
  rw [g3, Game.erase_S_of_ne _ _ _ _ (by decide), g2_S_one]
lemma g3_S_two : g3.S .two = {DAct.DM, DAct.RM, DAct.RL} := by
  rw [g3, Game.erase_S_self, g2_S_two]; decide

lemma dom4 : g3.IsStrictlyDominated .two .RL :=
  ⟨.DM, (strictlyDominates_two_iff _ _ _).2 ⟨by rw [g3_S_two]; decide, by rw [g3_S_two]; decide,
    fun a ha => by
      rw [g3_S_one] at ha
      cases a <;> simp at ha <;> norm_num [g3_u, u_apply, demandPayoff]⟩⟩

/-- The fully reduced Demand Game `({DM, RM}, {DM, RM}, u)`. -/
def reducedGame : Game Two DUniverse := g3.erase .two .RL dom4.erase_nonempty

lemma reducedGame_u : reducedGame.u = demandGame.u := rfl
lemma reducedGame_S (i : Two) : reducedGame.S i = {DAct.DM, DAct.RM} := by
  cases i
  · rw [reducedGame, Game.erase_S_of_ne _ _ _ _ (by decide), g3_S_one]
  · rw [reducedGame, Game.erase_S_self, g3_S_two]; decide

lemma reducedGame_mem_S {i : Two} {a : DAct} :
    a ∈ reducedGame.S i ↔ a = .DM ∨ a = .RM := by
  rw [reducedGame_S]; simp

/-- The reduced Demand Game contains no strictly dominated action. -/
lemma reducedGame_reduced : reducedGame.Reduced := by
  rw [reduced_iff]
  constructor
  · rintro a ⟨a', h⟩
    rw [strictlyDominates_one_iff] at h
    obtain ⟨ha', ha, hlt⟩ := h
    rw [reducedGame_mem_S] at ha ha'
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · exact lt_irrefl _ (hlt .DM (reducedGame_mem_S.2 (Or.inl rfl)))
    · have := hlt .RM (reducedGame_mem_S.2 (Or.inr rfl))
      norm_num [reducedGame_u, u_apply, demandPayoff] at this
    · have := hlt .DM (reducedGame_mem_S.2 (Or.inl rfl))
      norm_num [reducedGame_u, u_apply, demandPayoff] at this
    · exact lt_irrefl _ (hlt .DM (reducedGame_mem_S.2 (Or.inl rfl)))
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_two_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [reducedGame_mem_S] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt .DM (reducedGame_mem_S.2 (Or.inl rfl)))
    · have := hlt .RM (reducedGame_mem_S.2 (Or.inr rfl))
      norm_num [reducedGame_u, u_apply, demandPayoff] at this
    · have := hlt .DM (reducedGame_mem_S.2 (Or.inl rfl))
      norm_num [reducedGame_u, u_apply, demandPayoff] at this
    · exact lt_irrefl _ (hlt .DM (reducedGame_mem_S.2 (Or.inl rfl)))

/-- The **full reduction** of the Demand Game is `reducedGame`: the four eliminations
`dom1`–`dom4` form an `ElimStar` chain to a game with no strictly dominated action, and
the fully reduced game is unique (`Game.reduce_eq_of_reduced_of_elimStar`).  This is what
lets a book prescribe the play of the Demand Game (R1-F15). -/
lemma reduce_eq : demandGame.reduce = reducedGame := by
  have e1 : demandGame.ElimStar g1 :=
    Relation.ReflTransGen.single ⟨.one, .DL, dom1, rfl⟩
  have e2 : demandGame.ElimStar g2 := Relation.ReflTransGen.tail e1 ⟨.one, .RL, dom2, rfl⟩
  have e3 : demandGame.ElimStar g3 := Relation.ReflTransGen.tail e2 ⟨.two, .DL, dom3, rfl⟩
  have e4 : demandGame.ElimStar reducedGame :=
    Relation.ReflTransGen.tail e3 ⟨.two, .RL, dom4, rfl⟩
  exact Game.reduce_eq_of_reduced_of_elimStar e4 reducedGame_reduced

end demandGame

namespace demandSPI

lemma S_eq (i : Two) : demandSPI.S i = {DAct.DL, DAct.RL} := rfl
lemma u_apply (a : ∀ i, DUniverse i) (i : Two) :
    demandSPI.u a i = spiPayoff (a .one) (a .two) i := rfl

lemma mem_S {i : Two} {a : DAct} : a ∈ demandSPI.S i ↔ a = .DL ∨ a = .RL := by
  rw [S_eq]; simp

lemma isSubsetGameOf : demandSPI.IsSubsetGameOf demandGame := fun _ => Finset.subset_univ _

/-- Table 2 contains no strictly dominated action. -/
lemma reduced : demandSPI.Reduced := by
  rw [reduced_iff]
  constructor
  · rintro a ⟨a', h⟩
    rw [strictlyDominates_one_iff] at h
    obtain ⟨ha', ha, hlt⟩ := h
    rw [mem_S] at ha ha'
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · exact lt_irrefl _ (hlt .DL (mem_S.2 (Or.inl rfl)))
    · have := hlt .RL (mem_S.2 (Or.inr rfl))
      norm_num [u_apply, spiPayoff] at this
    · have := hlt .DL (mem_S.2 (Or.inl rfl))
      norm_num [u_apply, spiPayoff] at this
    · exact lt_irrefl _ (hlt .DL (mem_S.2 (Or.inl rfl)))
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_two_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [mem_S] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt .DL (mem_S.2 (Or.inl rfl)))
    · have := hlt .RL (mem_S.2 (Or.inr rfl))
      norm_num [u_apply, spiPayoff] at this
    · have := hlt .DL (mem_S.2 (Or.inl rfl))
      norm_num [u_apply, spiPayoff] at this
    · exact lt_irrefl _ (hlt .DL (mem_S.2 (Or.inl rfl)))

end demandSPI

open demandGame demandSPI

/-- The relabeling `DM ↦ DL`, `RM ↦ RL` (and the identity elsewhere). -/
def demilitarize : DAct → DAct
  | .DM => .DL
  | .RM => .RL
  | .DL => .DL
  | .RL => .RL

/-- The isomorphism `Ψ` between the reduced Demand Game and Table 2: `Ψᵢ(DM) = DL`,
`Ψᵢ(RM) = RL`, with `λ = (1, 1)` and `c = (0, 0)`. -/
def demandIso : GameIso reducedGame demandSPI where
  toFun _ := demilitarize
  bijOn i := by
    rw [reducedGame_S, demandSPI.S_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [demilitarize]
    · intro a ha b hb hab
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [demilitarize] at hab ⊢
    · intro b hb; simp at hb
      rcases hb with rfl | rfl
      · exact ⟨.DM, by simp, rfl⟩
      · exact ⟨.RM, by simp, rfl⟩
  scale _ := 1
  scale_pos _ := one_pos
  shift _ := 0
  affine a ha i := by
    rw [mem_profiles_iff, reducedGame_mem_S, reducedGame_mem_S] at ha
    obtain ⟨h1, h2⟩ := ha
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> cases i <;>
      simp [reducedGame_u, demandGame.u_apply, demandSPI.u_apply, demandPayoff, spiPayoff,
        demilitarize, h1, h2]

/-- `Ψ` is Pareto-improving for the original players: it fixes the payoffs of every
outcome but the conflict outcome, which it improves from `(−3, −3)` to `(1, 1)`. -/
lemma demandIso_paretoImproving : demandIso.ParetoImproving := by
  intro a ha
  rw [mem_profiles_iff, reducedGame_mem_S, reducedGame_mem_S] at ha
  obtain ⟨h1, h2⟩ := ha
  rw [Pi.le_def]
  intro i
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> cases i <;>
    norm_num [reducedGame_u, demandGame.u_apply, demandIso, GameIso.map, demandPayoff,
      demilitarize, h1, h2]

variable {Ω : Type*} (X : Play Two DUniverse Ω) (L : Filter Ω)

/-- Under Assumption 1 the representatives play the Demand Game as they play its full
reduction. -/
lemma demandGame_play_eq (hA1 : X.SatisfiesA1 L) :
    ∀ᶠ ω in L, X.play demandGame ω = X.play reducedGame ω := by
  have h₁ := hA1 demandGame .one .DL dom1
  have h₂ := hA1 g1 .one .RL dom2
  have h₃ := hA1 g2 .two .DL dom3
  have h₄ := hA1 g3 .two .RL dom4
  filter_upwards [h₁, h₂, h₃, h₄] with ω hω₁ hω₂ hω₃ hω₄
  obtain ⟨-, -, e₁⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₁
  obtain ⟨-, -, e₂⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₂
  obtain ⟨-, -, e₃⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₃
  obtain ⟨-, -, e₄⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₄
  rw [← e₁]; change X.play g1 ω = _
  rw [← e₂]; change X.play g2 ω = _
  rw [← e₃]; change X.play g3 ω = _
  rw [← e₄]; rfl

/-- **Proposition (Example) 6**, first clause: under Assumptions 1 and 2, Table 2 is an
SPI on the Demand Game.

Paper node: `Proposition 6` -/
theorem demandGame_isSPI (hA1 : X.SatisfiesA1 L) (hA2 : X.SatisfiesA2 L) :
    X.IsSPI L demandGame demandSPI := by
  obtain ⟨ψ, hψ, hc⟩ := Play.exists_paretoImproving_corresponds_of_assumption2 hA2
    reducedGame_reduced demandSPI.reduced demandIso demandIso_paretoImproving
  refine ⟨demandSPI.isSubsetGameOf, ?_⟩
  filter_upwards [demandGame_play_eq X L hA1, hc] with ω he hω
  obtain ⟨hmem, hmap⟩ := (ψ.mem_rel _ _).1 hω
  rw [he, hmap]
  exact hψ _ hmem

/-- **Proposition (Example) 6**, second clause: if moreover `(DM, DM)` is played with
positive probability, Table 2 is a strict SPI on the Demand Game.  (Every isomorphism
sends the conflict outcome to an outcome of Table 2, all of which player 1 values above
`−3`.)

Paper node: `Proposition 6` -/
theorem demandGame_isStrictSPI (hA1 : X.SatisfiesA1 L) (hA2 : X.SatisfiesA2 L)
    (hpos : ∃ᶠ ω in L, X.play demandGame ω = pair DAct.DM DAct.DM) :
    X.IsStrictSPI L demandGame demandSPI := by
  refine ⟨demandGame_isSPI X L hA1 hA2, .one, ?_⟩
  refine (hpos.and_eventually (Eventually.of_forall fun ω => X.mem demandSPI ω)).mono ?_
  rintro ω ⟨hDM, hmem⟩
  rw [mem_profiles_iff, demandSPI.mem_S, demandSPI.mem_S] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [hDM]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    norm_num [demandGame.u_apply, demandPayoff, h1, h2]

end Examples

end SafeParetoImprovements
