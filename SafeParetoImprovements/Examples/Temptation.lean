import SafeParetoImprovements.Examples.PrisonersDilemma

/-!
# Proposition 7: the Temptation Game (Table 6)

Player 1 chooses `T` (give in to temptation) or `R` (refrain); player 2 chooses `C`
(control) or `F` (free access):

|     | C    | F    |
|-----|------|------|
| T   | 1, 2 | 5, 1 |
| R   | 0, 0 | 4, 4 |

`T` strictly dominates `R`; once `R` is gone, `C` strictly dominates `F`; so the game is
dominance-solvable to `(T, C)`.  Proposition 7: under Assumption 1, `Γs = ({R}, A₂, u)` —
player 1 commits to `R`, everything else unchanged — is a strict (unilateral) SPI, because
in `Γs` player 2's `C` is strictly dominated by `F`, so `(R, F)` is played, and
`u(R, F) = (4, 4) > (1, 2) = u(T, C)`.

The printed proof eliminates "Player 1's `R₁`" and "Player 2's `R`"; the actions are `R`
and `F` (erratum D4).
-/

namespace SafeParetoImprovements

namespace Examples

open Filter
open scoped SetRel

/-- Player 1's actions in the Temptation Game. -/
inductive T1 | T | R
  deriving DecidableEq, Fintype, Inhabited

/-- Player 2's actions in the Temptation Game. -/
inductive T2 | C | F
  deriving DecidableEq, Fintype, Inhabited

/-- The action universe of the Temptation Game: different action types per player. -/
abbrev TemptUniverse : Two → Type
  | .one => T1
  | .two => T2

instance : ∀ i, DecidableEq (TemptUniverse i)
  | .one => inferInstanceAs (DecidableEq T1)
  | .two => inferInstanceAs (DecidableEq T2)

instance : ∀ i, Fintype (TemptUniverse i)
  | .one => inferInstanceAs (Fintype T1)
  | .two => inferInstanceAs (Fintype T2)

/-- Table 6's payoffs. -/
def temptPayoff : T1 → T2 → Two → ℝ
  | .T, .C, .one => 1
  | .T, .C, .two => 2
  | .T, .F, .one => 5
  | .T, .F, .two => 1
  | .R, .C, _ => 0
  | .R, .F, _ => 4

/-- The Temptation Game (Table 6). -/
def temptation : Game Two TemptUniverse where
  S := fun
    | .one => Finset.univ
    | .two => Finset.univ
  nonempty := fun
    | .one => ⟨.T, Finset.mem_univ _⟩
    | .two => ⟨.C, Finset.mem_univ _⟩
  u a i := temptPayoff (a .one) (a .two) i

/-- The unilateral subset game `({R}, A₂, u)` of Proposition 7. -/
def temptationCommit : Game Two TemptUniverse where
  S := fun
    | .one => {T1.R}
    | .two => Finset.univ
  nonempty := fun
    | .one => ⟨.R, Finset.mem_singleton_self _⟩
    | .two => ⟨.C, Finset.mem_univ _⟩
  u := temptation.u

namespace temptation

lemma S_one : temptation.S .one = Finset.univ := rfl
lemma S_two : temptation.S .two = Finset.univ := rfl
lemma u_apply (a : ∀ i, TemptUniverse i) (i : Two) :
    temptation.u a i = temptPayoff (a .one) (a .two) i := rfl

/-- `T` strictly dominates `R` for player 1. -/
lemma dominated_R : temptation.IsStrictlyDominated .one .R := by
  refine ⟨.T, (temptation.strictlyDominates_iff _ _ _).2
    ⟨Finset.mem_univ _, Finset.mem_univ _, fun b _ => ?_⟩⟩
  cases h : b .two <;>
    norm_num [temptation, temptPayoff, h, Function.update_of_ne (show Two.two ≠ Two.one by decide)]

/-- The game after removing `R`. -/
def afterR : Game Two TemptUniverse := temptation.erase .one .R dominated_R.erase_nonempty

lemma afterR_S_one : afterR.S .one = {T1.T} := by
  rw [afterR, Game.erase_S_self]; decide

lemma afterR_S_two : afterR.S .two = Finset.univ := by
  rw [afterR, Game.erase_S_of_ne _ _ _ _ (by decide)]; rfl

/-- With `R` gone, `C` strictly dominates `F` for player 2. -/
lemma dominated_F : afterR.IsStrictlyDominated .two .F := by
  refine ⟨.C, (afterR.strictlyDominates_iff _ _ _).2
    ⟨by rw [afterR_S_two]; exact Finset.mem_univ _,
     by rw [afterR_S_two]; exact Finset.mem_univ _, fun b hb => ?_⟩⟩
  have h1 : b .one = .T := by
    have := hb .one; rw [afterR_S_one] at this; simpa using this
  norm_num [afterR, temptation, Game.erase, Game.restrict, temptPayoff, h1,
    Function.update_of_ne (show Two.one ≠ Two.two by decide)]

/-- The fully reduced game `({T}, {C}, u)`. -/
def afterF : Game Two TemptUniverse := afterR.erase .two .F dominated_F.erase_nonempty

lemma afterF_profiles (a : ∀ i, TemptUniverse i) :
    a ∈ afterF.profiles → a .one = .T ∧ a .two = .C := by
  intro ha
  have h1 := ha .one
  have h2 := ha .two
  rw [afterF, Game.erase_S_of_ne _ _ _ _ (by decide), afterR_S_one] at h1
  rw [afterF, Game.erase_S_self, afterR_S_two] at h2
  refine ⟨by simpa using h1, ?_⟩
  have := (Finset.mem_erase.1 h2).1
  cases h : a .two
  · rfl
  · exact absurd h this

end temptation

namespace temptationCommit

lemma S_one : temptationCommit.S .one = {T1.R} := rfl
lemma S_two : temptationCommit.S .two = Finset.univ := rfl

lemma isSubsetGameOf : temptationCommit.IsSubsetGameOf temptation := fun i => by
  cases i <;> exact Finset.subset_univ _

/-- In the commitment game, `F` strictly dominates `C` for player 2. -/
lemma dominated_C : temptationCommit.IsStrictlyDominated .two .C := by
  refine ⟨.F, (temptationCommit.strictlyDominates_iff _ _ _).2
    ⟨Finset.mem_univ _, Finset.mem_univ _, fun b hb => ?_⟩⟩
  have h1 : b .one = .R := by
    have := hb .one; rw [S_one] at this; simpa using this
  norm_num [temptationCommit, temptation, temptPayoff, h1,
    Function.update_of_ne (show Two.one ≠ Two.two by decide)]

/-- The reduced commitment game `({R}, {F}, u)`. -/
def afterC : Game Two TemptUniverse :=
  temptationCommit.erase .two .C dominated_C.erase_nonempty

lemma afterC_profiles (a : ∀ i, TemptUniverse i) :
    a ∈ afterC.profiles → a .one = .R ∧ a .two = .F := by
  intro ha
  have h1 := ha .one
  have h2 := ha .two
  rw [afterC, Game.erase_S_of_ne _ _ _ _ (by decide), S_one] at h1
  rw [afterC, Game.erase_S_self, S_two] at h2
  refine ⟨by simpa using h1, ?_⟩
  have := (Finset.mem_erase.1 h2).1
  cases h : a .two
  · exact absurd h this
  · rfl

end temptationCommit

open temptation temptationCommit

variable {Ω : Type*} (X : Play Two TemptUniverse Ω) (L : Filter Ω)

/-- Under Assumption 1 the representatives play `(T, C)` in the Temptation Game. -/
lemma temptation_play (hA1 : X.SatisfiesA1 L) :
    ∀ᶠ ω in L, X.play temptation ω .one = .T ∧ X.play temptation ω .two = .C := by
  have h₁ := hA1 temptation .one .R dominated_R
  have h₂ := hA1 afterR .two .F dominated_F
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  obtain ⟨-, -, e₁⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₁
  obtain ⟨-, -, e₂⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₂
  have e : X.play temptation ω = X.play afterF ω := by
    rw [← e₁]
    change X.play afterR ω = _
    rw [← e₂]
    rfl
  rw [e]
  exact afterF_profiles _ (X.mem afterF ω)

/-- Under Assumption 1 the representatives play `(R, F)` in the commitment game. -/
lemma temptationCommit_play (hA1 : X.SatisfiesA1 L) :
    ∀ᶠ ω in L, X.play temptationCommit ω .one = .R ∧ X.play temptationCommit ω .two = .F := by
  have h := hA1 temptationCommit .two .C dominated_C
  filter_upwards [h] with ω hω
  obtain ⟨-, -, e⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω
  rw [← e]
  exact afterC_profiles _ (X.mem afterC ω)

/-- **Proposition (Example) 7**: under Assumption 1, `({R}, A₂, u)` is a strict SPI on the
Temptation Game.  (Stated for any non-degenerate certainty filter, `dd:certainty`.)

Paper node: `Proposition 7` -/
theorem temptation_isStrictSPI [L.NeBot] (hA1 : X.SatisfiesA1 L) :
    X.IsStrictSPI L temptation temptationCommit := by
  have hplay := temptation_play X L hA1
  have hplay' := temptationCommit_play X L hA1
  refine ⟨⟨temptationCommit.isSubsetGameOf, ?_⟩, .one, ?_⟩
  · filter_upwards [hplay, hplay'] with ω ⟨h1, h2⟩ ⟨h1', h2'⟩
    rw [Pi.le_def]
    intro i
    cases i <;> simp only [temptation.u_apply, h1, h2, h1', h2'] <;> norm_num [temptPayoff]
  · refine ((hplay.and hplay').mono fun ω ⟨⟨h1, h2⟩, ⟨h1', h2'⟩⟩ => ?_).frequently
    simp only [temptation.u_apply, h1, h2, h1', h2']
    norm_num [temptPayoff]

/-- Proposition 7's SPI is **unilateral** (Definition 2): only player 1's instruction
changes.  The printed statement of Proposition 7 says only "strict SPI"; that the SPI is
unilateral is the surrounding prose of §4.5 (extraction l. 1116), so this lemma renders
that half of the node.  No non-degeneracy of the filter is needed: the conclusion has no
positive-probability clause, so the SPI is derived from the two play lemmas directly
rather than through the strict theorem (R1-F31).

Paper node: `Proposition 7` -/
theorem temptation_isUnilateralSPI (hA1 : X.SatisfiesA1 L) :
    X.IsUnilateralSPI L temptation temptationCommit := by
  refine ⟨⟨temptationCommit.isSubsetGameOf, .one, fun j hj => by
      cases j
      · exact absurd rfl hj
      · exact ⟨rfl, fun _ _ => rfl⟩⟩,
    temptationCommit.isSubsetGameOf, ?_⟩
  filter_upwards [temptation_play X L hA1, temptationCommit_play X L hA1] with
    ω ⟨h1, h2⟩ ⟨h1', h2'⟩
  rw [Pi.le_def]
  intro i
  cases i <;> simp only [temptation.u_apply, h1, h2, h1', h2'] <;> norm_num [temptPayoff]

end Examples

end SafeParetoImprovements
