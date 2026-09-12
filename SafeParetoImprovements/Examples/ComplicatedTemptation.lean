import SafeParetoImprovements.Examples.TwoPlayer

/-!
# Proposition 8: the Complicated Temptation Game (Tables 4 and 5)

Each player picks a project (`1` or `2`) and a resource policy: player 1 gives in to
temptation (`T`) or refrains (`R`), player 2 controls access (`C`) or gives free access
(`F`).  Table 4:

|    | C₁   | C₂   | F₁   | F₂   |
|----|------|------|------|------|
| T₁ | 4, 2 | 1, 1 | 6, 0 | 6, 0 |
| T₂ | 1, 1 | 2, 4 | 6, 0 | 6, 0 |
| R₁ | 0, 0 | 0, 0 | 5, 3 | 3, 2 |
| R₂ | 0, 0 | 0, 0 | 2, 2 | 3, 5 |

Player 1's `T`s strictly dominate her `R`s; with those gone, player 2's `C`s strictly
dominate his `F`s; the game reduces to the project-choice game `({T₁, T₂}, {C₁, C₂})`.
Player 1's **unilateral** SPI (Table 5) restricts her to `{R₁, R₂}` and gives her
representative the utilities `uˢ₁(Rᵢ, Fⱼ) = u₁(Tᵢ, Cⱼ)`:

|    | C₁   | C₂   | F₁   | F₂   |
|----|------|------|------|------|
| R₁ | 0, 0 | 0, 0 | 4, 3 | 1, 2 |
| R₂ | 0, 0 | 0, 0 | 1, 2 | 2, 5 |

In Table 5, player 2's `F`s strictly dominate his `C`s, and the remaining game
`({R₁, R₂}, {F₁, F₂})` is isomorphic to the reduced original via `Tᵢ ↦ Rᵢ`, `Cⱼ ↦ Fⱼ`
(player 1's utilities equal, player 2's equal up to the constant `1`).  For the original
players every outcome improves: `u(Rᵢ, Fⱼ) ≥ u(Tᵢ, Cⱼ)`.

Proposition 8: under Assumptions 1 and 2, Table 5 is a unilateral SPI on Table 4.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter Two
open scoped SetRel

/-- Player 1's actions. -/
inductive CT1 | T1 | T2 | R1 | R2
  deriving DecidableEq, Fintype, Inhabited

/-- Player 2's actions. -/
inductive CT2 | C1 | C2 | F1 | F2
  deriving DecidableEq, Fintype, Inhabited

/-- The action universe. -/
abbrev CTUniverse : Two → Type
  | .one => CT1
  | .two => CT2

instance : ∀ i, DecidableEq (CTUniverse i)
  | .one => inferInstanceAs (DecidableEq CT1)
  | .two => inferInstanceAs (DecidableEq CT2)

instance : ∀ i, Fintype (CTUniverse i)
  | .one => inferInstanceAs (Fintype CT1)
  | .two => inferInstanceAs (Fintype CT2)

instance : ∀ i, Nonempty (CTUniverse i)
  | .one => ⟨CT1.T1⟩
  | .two => ⟨CT2.C1⟩

/-- Table 4, player 1. -/
def ctPayoff₁ : CT1 → CT2 → ℝ
  | .T1, .C1 => 4 | .T1, .C2 => 1 | .T1, .F1 => 6 | .T1, .F2 => 6
  | .T2, .C1 => 1 | .T2, .C2 => 2 | .T2, .F1 => 6 | .T2, .F2 => 6
  | .R1, .C1 => 0 | .R1, .C2 => 0 | .R1, .F1 => 5 | .R1, .F2 => 3
  | .R2, .C1 => 0 | .R2, .C2 => 0 | .R2, .F1 => 2 | .R2, .F2 => 3

/-- Table 4, player 2. -/
def ctPayoff₂ : CT1 → CT2 → ℝ
  | .T1, .C1 => 2 | .T1, .C2 => 1 | .T1, .F1 => 0 | .T1, .F2 => 0
  | .T2, .C1 => 1 | .T2, .C2 => 4 | .T2, .F1 => 0 | .T2, .F2 => 0
  | .R1, .C1 => 0 | .R1, .C2 => 0 | .R1, .F1 => 3 | .R1, .F2 => 2
  | .R2, .C1 => 0 | .R2, .C2 => 0 | .R2, .F1 => 2 | .R2, .F2 => 5

/-- Table 5, player 1's *representative's* utilities (on `{R₁, R₂} × A₂`; `0` elsewhere,
outside the subset game's profiles). -/
def ctSPIPayoff₁ : CT1 → CT2 → ℝ
  | .R1, .F1 => 4 | .R1, .F2 => 1 | .R2, .F1 => 1 | .R2, .F2 => 2
  | _, _ => 0

/-- The payoff vector of Table 4. -/
def ctPayoff (a : CT1) (x : CT2) : Two → ℝ
  | .one => ctPayoff₁ a x
  | .two => ctPayoff₂ a x

/-- The payoff vector of Table 5. -/
def ctSPIPayoff (a : CT1) (x : CT2) : Two → ℝ
  | .one => ctSPIPayoff₁ a x
  | .two => ctPayoff₂ a x

/-- The Complicated Temptation Game (Table 4). -/
def complicatedTemptation : Game Two CTUniverse where
  S := fun
    | .one => Finset.univ
    | .two => Finset.univ
  nonempty := fun
    | .one => ⟨.T1, Finset.mem_univ _⟩
    | .two => ⟨.C1, Finset.mem_univ _⟩
  u a i := ctPayoff (a .one) (a .two) i

/-- Player 1's unilateral SPI (Table 5). -/
def complicatedTemptationSPI : Game Two CTUniverse where
  S := fun
    | .one => {CT1.R1, CT1.R2}
    | .two => Finset.univ
  nonempty := fun
    | .one => ⟨.R1, Finset.mem_insert_self _ _⟩
    | .two => ⟨.C1, Finset.mem_univ _⟩
  u a i := ctSPIPayoff (a .one) (a .two) i

namespace complicatedTemptation

lemma u_apply (a : ∀ i, CTUniverse i) (i : Two) :
    complicatedTemptation.u a i = ctPayoff (a .one) (a .two) i := rfl

lemma dom1 : complicatedTemptation.IsStrictlyDominated .one .R1 :=
  ⟨.T1, (strictlyDominates_one_iff _ _ _).2 ⟨Finset.mem_univ _, Finset.mem_univ _,
    fun x _ => by cases x <;> norm_num [u_apply, ctPayoff, ctPayoff₁]⟩⟩

def g1 : Game Two CTUniverse := complicatedTemptation.erase .one .R1 dom1.erase_nonempty
lemma g1_u : g1.u = complicatedTemptation.u := rfl
lemma g1_S_one : g1.S .one = {CT1.T1, CT1.T2, CT1.R2} := by
  rw [g1, Game.erase_S_self]; decide
lemma g1_S_two : g1.S .two = Finset.univ := by
  rw [g1, Game.erase_S_of_ne _ _ _ _ (by decide)]; rfl

lemma dom2 : g1.IsStrictlyDominated .one .R2 :=
  ⟨.T1, (strictlyDominates_one_iff _ _ _).2 ⟨by rw [g1_S_one]; decide, by rw [g1_S_one]; decide,
    fun x _ => by cases x <;> norm_num [g1_u, u_apply, ctPayoff, ctPayoff₁]⟩⟩

def g2 : Game Two CTUniverse := g1.erase .one .R2 dom2.erase_nonempty
lemma g2_u : g2.u = complicatedTemptation.u := rfl
lemma g2_S_one : g2.S .one = {CT1.T1, CT1.T2} := by
  rw [g2, Game.erase_S_self, g1_S_one]; decide
lemma g2_S_two : g2.S .two = Finset.univ := by
  rw [g2, Game.erase_S_of_ne _ _ _ _ (by decide), g1_S_two]

lemma dom3 : g2.IsStrictlyDominated .two .F1 :=
  ⟨.C1, (strictlyDominates_two_iff _ _ _).2 ⟨by rw [g2_S_two]; exact Finset.mem_univ _,
    by rw [g2_S_two]; exact Finset.mem_univ _, fun a ha => by
      rw [g2_S_one] at ha
      cases a <;> simp at ha <;> norm_num [g2_u, u_apply, ctPayoff, ctPayoff₂]⟩⟩

def g3 : Game Two CTUniverse := g2.erase .two .F1 dom3.erase_nonempty
lemma g3_u : g3.u = complicatedTemptation.u := rfl
lemma g3_S_one : g3.S .one = {CT1.T1, CT1.T2} := by
  rw [g3, Game.erase_S_of_ne _ _ _ _ (by decide), g2_S_one]
lemma g3_S_two : g3.S .two = {CT2.C1, CT2.C2, CT2.F2} := by
  rw [g3, Game.erase_S_self, g2_S_two]; decide

lemma dom4 : g3.IsStrictlyDominated .two .F2 :=
  ⟨.C1, (strictlyDominates_two_iff _ _ _).2 ⟨by rw [g3_S_two]; decide, by rw [g3_S_two]; decide,
    fun a ha => by
      rw [g3_S_one] at ha
      cases a <;> simp at ha <;> norm_num [g3_u, u_apply, ctPayoff, ctPayoff₂]⟩⟩

/-- The fully reduced game `({T₁, T₂}, {C₁, C₂}, u)`. -/
def reducedGame : Game Two CTUniverse := g3.erase .two .F2 dom4.erase_nonempty
lemma reducedGame_u : reducedGame.u = complicatedTemptation.u := rfl
lemma reducedGame_S_one : reducedGame.S .one = {CT1.T1, CT1.T2} := by
  rw [reducedGame, Game.erase_S_of_ne _ _ _ _ (by decide), g3_S_one]
lemma reducedGame_S_two : reducedGame.S .two = {CT2.C1, CT2.C2} := by
  rw [reducedGame, Game.erase_S_self, g3_S_two]; decide
lemma reducedGame_mem_one {a : CT1} : a ∈ reducedGame.S .one ↔ a = .T1 ∨ a = .T2 := by
  rw [reducedGame_S_one]; simp
lemma reducedGame_mem_two {x : CT2} : x ∈ reducedGame.S .two ↔ x = .C1 ∨ x = .C2 := by
  rw [reducedGame_S_two]; simp

lemma reducedGame_reduced : reducedGame.Reduced := by
  rw [reduced_iff]
  constructor
  · rintro a ⟨a', h⟩
    rw [strictlyDominates_one_iff] at h
    obtain ⟨ha', ha, hlt⟩ := h
    rw [reducedGame_mem_one] at ha ha'
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · exact lt_irrefl _ (hlt .C1 (reducedGame_mem_two.2 (Or.inl rfl)))
    · have := hlt .C1 (reducedGame_mem_two.2 (Or.inl rfl))
      norm_num [reducedGame_u, u_apply, ctPayoff, ctPayoff₁] at this
    · have := hlt .C2 (reducedGame_mem_two.2 (Or.inr rfl))
      norm_num [reducedGame_u, u_apply, ctPayoff, ctPayoff₁] at this
    · exact lt_irrefl _ (hlt .C1 (reducedGame_mem_two.2 (Or.inl rfl)))
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_two_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [reducedGame_mem_two] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt .T1 (reducedGame_mem_one.2 (Or.inl rfl)))
    · have := hlt .T1 (reducedGame_mem_one.2 (Or.inl rfl))
      norm_num [reducedGame_u, u_apply, ctPayoff, ctPayoff₂] at this
    · have := hlt .T2 (reducedGame_mem_one.2 (Or.inr rfl))
      norm_num [reducedGame_u, u_apply, ctPayoff, ctPayoff₂] at this
    · exact lt_irrefl _ (hlt .T1 (reducedGame_mem_one.2 (Or.inl rfl)))

end complicatedTemptation

namespace complicatedTemptationSPI

lemma u_apply (a : ∀ i, CTUniverse i) (i : Two) :
    complicatedTemptationSPI.u a i = ctSPIPayoff (a .one) (a .two) i := rfl
lemma S_one : complicatedTemptationSPI.S .one = {CT1.R1, CT1.R2} := rfl
lemma S_two : complicatedTemptationSPI.S .two = Finset.univ := rfl
lemma mem_one {a : CT1} : a ∈ complicatedTemptationSPI.S .one ↔ a = .R1 ∨ a = .R2 := by
  rw [S_one]; simp

lemma isSubsetGameOf : complicatedTemptationSPI.IsSubsetGameOf complicatedTemptation :=
  fun i => by cases i <;> exact Finset.subset_univ _

lemma dom1 : complicatedTemptationSPI.IsStrictlyDominated .two .C1 :=
  ⟨.F1, (strictlyDominates_two_iff _ _ _).2 ⟨Finset.mem_univ _, Finset.mem_univ _,
    fun a ha => by
      rw [mem_one] at ha
      rcases ha with rfl | rfl <;> norm_num [u_apply, ctSPIPayoff, ctPayoff₂]⟩⟩

def h1 : Game Two CTUniverse := complicatedTemptationSPI.erase .two .C1 dom1.erase_nonempty
lemma h1_u : h1.u = complicatedTemptationSPI.u := rfl
lemma h1_S_one : h1.S .one = {CT1.R1, CT1.R2} := by
  rw [h1, Game.erase_S_of_ne _ _ _ _ (by decide)]; rfl
lemma h1_S_two : h1.S .two = {CT2.C2, CT2.F1, CT2.F2} := by
  rw [h1, Game.erase_S_self, S_two]; decide

lemma dom2 : h1.IsStrictlyDominated .two .C2 :=
  ⟨.F1, (strictlyDominates_two_iff _ _ _).2 ⟨by rw [h1_S_two]; decide, by rw [h1_S_two]; decide,
    fun a ha => by
      rw [h1_S_one] at ha
      cases a <;> simp at ha <;> norm_num [h1_u, u_apply, ctSPIPayoff, ctPayoff₂]⟩⟩

/-- The fully reduced SPI game `({R₁, R₂}, {F₁, F₂}, uˢ)`. -/
def reducedGame : Game Two CTUniverse := h1.erase .two .C2 dom2.erase_nonempty
lemma reducedGame_u : reducedGame.u = complicatedTemptationSPI.u := rfl
lemma reducedGame_S_one : reducedGame.S .one = {CT1.R1, CT1.R2} := by
  rw [reducedGame, Game.erase_S_of_ne _ _ _ _ (by decide), h1_S_one]
lemma reducedGame_S_two : reducedGame.S .two = {CT2.F1, CT2.F2} := by
  rw [reducedGame, Game.erase_S_self, h1_S_two]; decide
lemma reducedGame_mem_one {a : CT1} : a ∈ reducedGame.S .one ↔ a = .R1 ∨ a = .R2 := by
  rw [reducedGame_S_one]; simp
lemma reducedGame_mem_two {x : CT2} : x ∈ reducedGame.S .two ↔ x = .F1 ∨ x = .F2 := by
  rw [reducedGame_S_two]; simp

lemma reducedGame_reduced : reducedGame.Reduced := by
  rw [reduced_iff]
  constructor
  · rintro a ⟨a', h⟩
    rw [strictlyDominates_one_iff] at h
    obtain ⟨ha', ha, hlt⟩ := h
    rw [reducedGame_mem_one] at ha ha'
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
    · exact lt_irrefl _ (hlt .F1 (reducedGame_mem_two.2 (Or.inl rfl)))
    · have := hlt .F1 (reducedGame_mem_two.2 (Or.inl rfl))
      norm_num [reducedGame_u, u_apply, ctSPIPayoff, ctSPIPayoff₁] at this
    · have := hlt .F2 (reducedGame_mem_two.2 (Or.inr rfl))
      norm_num [reducedGame_u, u_apply, ctSPIPayoff, ctSPIPayoff₁] at this
    · exact lt_irrefl _ (hlt .F1 (reducedGame_mem_two.2 (Or.inl rfl)))
  · rintro x ⟨x', h⟩
    rw [strictlyDominates_two_iff] at h
    obtain ⟨hx', hx, hlt⟩ := h
    rw [reducedGame_mem_two] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
    · exact lt_irrefl _ (hlt .R1 (reducedGame_mem_one.2 (Or.inl rfl)))
    · have := hlt .R1 (reducedGame_mem_one.2 (Or.inl rfl))
      norm_num [reducedGame_u, u_apply, ctSPIPayoff, ctPayoff₂] at this
    · have := hlt .R2 (reducedGame_mem_one.2 (Or.inr rfl))
      norm_num [reducedGame_u, u_apply, ctSPIPayoff, ctPayoff₂] at this
    · exact lt_irrefl _ (hlt .R1 (reducedGame_mem_one.2 (Or.inl rfl)))

end complicatedTemptationSPI

/-- `Tᵢ ↦ Rᵢ` (identity elsewhere). -/
def refrain : CT1 → CT1
  | .T1 => .R1 | .T2 => .R2 | .R1 => .R1 | .R2 => .R2

/-- `Cⱼ ↦ Fⱼ` (identity elsewhere). -/
def free : CT2 → CT2
  | .C1 => .F1 | .C2 => .F2 | .F1 => .F1 | .F2 => .F2

/-- The isomorphism `Ξ` of the printed proof, `Ξ₁(Tᵢ) = Rᵢ`, `Ξ₂(Cⱼ) = Fⱼ`, with
`λ = (1, 1)` and `c = (0, −1)`: player 1's representative's utilities were chosen equal,
and player 2's are equal up to the constant `1`. -/
def ctIso : GameIso complicatedTemptation.reducedGame complicatedTemptationSPI.reducedGame where
  toFun := fun
    | .one => refrain
    | .two => free
  bijOn := fun
    | .one => by
      rw [complicatedTemptation.reducedGame_S_one, complicatedTemptationSPI.reducedGame_S_one]
      refine ⟨?_, ?_, ?_⟩
      · intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [refrain]
      · intro a ha b hb hab
        simp at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [refrain] at hab ⊢
      · intro b hb; simp at hb
        rcases hb with rfl | rfl
        · exact ⟨.T1, by simp, rfl⟩
        · exact ⟨.T2, by simp, rfl⟩
    | .two => by
      rw [complicatedTemptation.reducedGame_S_two, complicatedTemptationSPI.reducedGame_S_two]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [free]
      · intro x hx y hy hxy
        simp at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [free] at hxy ⊢
      · intro y hy; simp at hy
        rcases hy with rfl | rfl
        · exact ⟨.C1, by simp, rfl⟩
        · exact ⟨.C2, by simp, rfl⟩
  scale _ := 1
  scale_pos _ := one_pos
  shift := fun
    | .one => 0
    | .two => -1
  affine a ha i := by
    rw [mem_profiles_iff, complicatedTemptation.reducedGame_mem_one,
      complicatedTemptation.reducedGame_mem_two] at ha
    obtain ⟨h1, h2⟩ := ha
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> cases i <;>
      norm_num [complicatedTemptation.reducedGame_u, complicatedTemptation.u_apply,
        complicatedTemptationSPI.reducedGame_u, complicatedTemptationSPI.u_apply,
        ctPayoff, ctSPIPayoff, ctPayoff₁, ctPayoff₂, ctSPIPayoff₁, refrain, free, h1, h2]

/-- `Ξ` is Pareto-improving for the original players. -/
lemma ctIso_paretoImproving : ctIso.ParetoImproving := by
  intro a ha
  rw [mem_profiles_iff, complicatedTemptation.reducedGame_mem_one,
    complicatedTemptation.reducedGame_mem_two] at ha
  obtain ⟨h1, h2⟩ := ha
  rw [Pi.le_def]
  intro i
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> cases i <;>
    norm_num [complicatedTemptation.reducedGame_u, complicatedTemptation.u_apply, ctIso,
      GameIso.map, ctPayoff, ctPayoff₁, ctPayoff₂, refrain, free, h1, h2]

variable {Ω : Type*} (X : Play Two CTUniverse Ω) (L : Filter Ω)

lemma complicatedTemptation_play_eq (hA1 : X.SatisfiesA1 L) :
    ∀ᶠ ω in L, X.play complicatedTemptation ω = X.play complicatedTemptation.reducedGame ω := by
  open complicatedTemptation in
  have h₁ := hA1 complicatedTemptation .one .R1 dom1
  have h₂ := hA1 g1 .one .R2 dom2
  have h₃ := hA1 g2 .two .F1 dom3
  have h₄ := hA1 g3 .two .F2 dom4
  filter_upwards [h₁, h₂, h₃, h₄] with ω hω₁ hω₂ hω₃ hω₄
  obtain ⟨-, -, e₁⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₁
  obtain ⟨-, -, e₂⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₂
  obtain ⟨-, -, e₃⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₃
  obtain ⟨-, -, e₄⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₄
  rw [← e₁]; change X.play g1 ω = _
  rw [← e₂]; change X.play g2 ω = _
  rw [← e₃]; change X.play g3 ω = _
  rw [← e₄]; rfl

lemma complicatedTemptationSPI_play_eq (hA1 : X.SatisfiesA1 L) :
    ∀ᶠ ω in L, X.play complicatedTemptationSPI ω =
      X.play complicatedTemptationSPI.reducedGame ω := by
  open complicatedTemptationSPI in
  have h₁ := hA1 complicatedTemptationSPI .two .C1 dom1
  have h₂ := hA1 h1 .two .C2 dom2
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  obtain ⟨-, -, e₁⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₁
  obtain ⟨-, -, e₂⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₂
  rw [← e₁]; change X.play h1 ω = _
  rw [← e₂]; rfl

/-- **Proposition (Example) 8**: under Assumptions 1 and 2, Table 5 is a unilateral SPI on
the Complicated Temptation Game.

Paper node: `Proposition 8` -/
theorem complicatedTemptation_isUnilateralSPI (hA1 : X.SatisfiesA1 L) (hA2 : X.SatisfiesA2 L) :
    X.IsUnilateralSPI L complicatedTemptation complicatedTemptationSPI := by
  obtain ⟨ψ, hψ, hc⟩ := Play.exists_paretoImproving_corresponds_of_assumption2 hA2
    complicatedTemptation.reducedGame_reduced complicatedTemptationSPI.reducedGame_reduced
    ctIso ctIso_paretoImproving
  refine ⟨⟨complicatedTemptationSPI.isSubsetGameOf, .one, fun j hj => ?_⟩,
    complicatedTemptationSPI.isSubsetGameOf, ?_⟩
  · cases j
    · exact absurd rfl hj
    · refine ⟨rfl, fun a ha => ?_⟩
      rw [mem_profiles_iff, complicatedTemptationSPI.mem_one] at ha
      obtain ⟨h1, -⟩ := ha
      rcases h1 with h1 | h1 <;>
        simp [complicatedTemptationSPI.u_apply, complicatedTemptation.u_apply, ctSPIPayoff,
          ctPayoff, h1]
  · filter_upwards [complicatedTemptation_play_eq X L hA1,
      complicatedTemptationSPI_play_eq X L hA1, hc] with ω he he' hω
    obtain ⟨hmem, hmap⟩ := (ψ.mem_rel _ _).1 hω
    rw [he, he', hmap]
    exact hψ _ hmem

end Examples

end SafeParetoImprovements
