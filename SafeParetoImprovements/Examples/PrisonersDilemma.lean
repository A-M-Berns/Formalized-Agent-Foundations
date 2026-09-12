import SafeParetoImprovements.Assumptions
import SafeParetoImprovements.Reduction
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-!
# Proposition 5: the Prisoner's Dilemma (Table 3)

Two players, actions `Cooperate` / `Defect`, payoffs

|          | Cooperate | Defect |
|----------|-----------|--------|
| Cooperate| 3, 3      | 1, 4   |
| Defect   | 4, 1      | 2, 2   |

Proposition 5: for *any* subset game `Γs` with `Aˢ₁ = Aˢ₂ = {Cooperate}` (its payoffs
are irrelevant), under Assumption 1, `Γs` is a strict SPI on the Prisoner's Dilemma.
The printed proof: Assumption 1 twice and transitivity give `Γ ∼_Φ ({Defect}, {Defect}, u)`
with `Φ` the elimination correspondence; Lemma 2.5 gives `({Defect}, {Defect}, u) ∼_all Γs`;
the composite is Pareto-improving, and strictness comes from `(3,3) > (2,2)`.

The example is also the non-vacuity witness for `Play.IsStrictSPI`.
-/

namespace SafeParetoImprovements

namespace Examples

open Filter
open scoped SetRel

/-- The two players. -/
inductive Two | one | two
  deriving DecidableEq, Fintype

/-- The Prisoner's Dilemma's actions. -/
inductive PD | cooperate | defect
  deriving DecidableEq, Fintype, Inhabited

/-- The action universe: both players choose from `PD`. -/
abbrev PDUniverse : Two → Type := fun _ => PD

/-- Table 3's payoffs, `pdPayoff a₁ a₂ i`. -/
def pdPayoff : PD → PD → Two → ℝ
  | .cooperate, .cooperate, _ => 3
  | .cooperate, .defect, .one => 1
  | .cooperate, .defect, .two => 4
  | .defect, .cooperate, .one => 4
  | .defect, .cooperate, .two => 1
  | .defect, .defect, _ => 2

/-- The Prisoner's Dilemma (Table 3), over the universe `PDUniverse`. -/
def prisonersDilemma : Game Two PDUniverse where
  S _ := Finset.univ
  nonempty _ := ⟨.defect, Finset.mem_univ _⟩
  u a i := pdPayoff (a .one) (a .two) i

namespace prisonersDilemma

@[simp] lemma S_eq (i : Two) : prisonersDilemma.S i = Finset.univ := rfl

lemma mem_profiles (a : ∀ i, PDUniverse i) : a ∈ prisonersDilemma.profiles := fun _ =>
  Finset.mem_univ _

/-- `Defect` strictly dominates `Cooperate` for player one. -/
lemma dominated_one : prisonersDilemma.IsStrictlyDominated .one .cooperate := by
  refine ⟨.defect, (prisonersDilemma.strictlyDominates_iff _ _ _).2
    ⟨by simp, by simp, fun b _ => ?_⟩⟩
  cases h : b .two <;>
    norm_num [prisonersDilemma, pdPayoff, h, Function.update_of_ne (show Two.two ≠ Two.one by decide)]

/-- The game after removing player one's `Cooperate`. -/
def afterOne : Game Two PDUniverse :=
  prisonersDilemma.erase .one .cooperate dominated_one.erase_nonempty

lemma afterOne_S_one : afterOne.S .one = {PD.defect} := by
  rw [afterOne, Game.erase_S_self]; decide

lemma afterOne_S_two : afterOne.S .two = Finset.univ := by
  rw [afterOne, Game.erase_S_of_ne _ _ _ _ (by decide)]; rfl

/-- In the remaining game, `Defect` strictly dominates `Cooperate` for player two. -/
lemma dominated_two : afterOne.IsStrictlyDominated .two .cooperate := by
  refine ⟨.defect, (afterOne.strictlyDominates_iff _ _ _).2
    ⟨by rw [afterOne_S_two]; exact Finset.mem_univ _,
     by rw [afterOne_S_two]; exact Finset.mem_univ _, fun b hb => ?_⟩⟩
  have h1 : b .one = .defect := by
    have := hb .one; rw [afterOne_S_one] at this; simpa using this
  norm_num [afterOne, prisonersDilemma, Game.erase, Game.restrict, pdPayoff, h1,
    Function.update_of_ne (show Two.one ≠ Two.two by decide)]

/-- The fully reduced game `({Defect}, {Defect}, u)`. -/
def afterTwo : Game Two PDUniverse :=
  afterOne.erase .two .cooperate dominated_two.erase_nonempty

lemma afterTwo_profiles (a : ∀ i, PDUniverse i) :
    a ∈ afterTwo.profiles ↔ a .one = .defect ∧ a .two = .defect := by
  constructor
  · intro ha
    have h1 := ha .one
    have h2 := ha .two
    rw [afterTwo, Game.erase_S_of_ne _ _ _ _ (by decide), afterOne_S_one] at h1
    rw [afterTwo, Game.erase_S_self, afterOne_S_two] at h2
    refine ⟨by simpa using h1, ?_⟩
    have := (Finset.mem_erase.1 h2).1
    cases h : a .two
    · exact absurd h this
    · rfl
  · rintro ⟨h1, h2⟩ i
    cases i
    · rw [afterTwo, Game.erase_S_of_ne _ _ _ _ (by decide), afterOne_S_one, h1]; simp
    · rw [afterTwo, Game.erase_S_self, afterOne_S_two, h2]; decide

end prisonersDilemma

open prisonersDilemma

variable {Ω : Type*} (X : Play Two PDUniverse Ω) (L : Filter Ω)

/-- Under Assumption 1, the representatives play `(Defect, Defect)` in the Prisoner's
Dilemma with certainty. -/
lemma prisonersDilemma_play (hA1 : X.SatisfiesA1 L) :
    ∀ᶠ ω in L, X.play prisonersDilemma ω = fun _ => PD.defect := by
  have h₁ := hA1 prisonersDilemma .one .cooperate dominated_one
  have h₂ := hA1 afterOne .two .cooperate dominated_two
  filter_upwards [h₁, h₂] with ω hω₁ hω₂
  obtain ⟨-, -, e₁⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₁
  obtain ⟨-, -, e₂⟩ := (Game.mem_elimRel _ _ _ _ _).1 hω₂
  have hmem := X.mem afterTwo ω
  rw [afterTwo_profiles] at hmem
  have e : X.play prisonersDilemma ω = X.play afterTwo ω := by
    rw [← e₁]
    change X.play afterOne ω = _
    rw [← e₂]
    rfl
  funext i
  cases i
  · rw [e]; exact hmem.1
  · rw [e]; exact hmem.2

/-- **Proposition (Example) 5**: let `Γ` be the Prisoner's Dilemma and `Γs` any subset
game with `Aˢ₁ = Aˢ₂ = {Cooperate}`.  Under Assumption 1, `Γs` is a strict SPI on `Γ`.
Stated for any non-degenerate certainty filter (`dd:certainty`).

Paper node: `Proposition 5` -/
theorem prisonersDilemma_isStrictSPI [L.NeBot] (hA1 : X.SatisfiesA1 L) (Γs : Game Two PDUniverse)
    (hS : ∀ i, Γs.S i = {PD.cooperate}) : X.IsStrictSPI L prisonersDilemma Γs := by
  have hplayΓs : ∀ ω, X.play Γs ω = fun _ => PD.cooperate := by
    intro ω
    funext i
    have := X.mem Γs ω i
    rw [hS] at this
    simpa using this
  have hplay := prisonersDilemma_play X L hA1
  refine ⟨⟨fun i => by rw [hS]; exact Finset.subset_univ _, ?_⟩, .one, ?_⟩
  · filter_upwards [hplay] with ω hω
    rw [hω, hplayΓs, Pi.le_def]
    intro i
    cases i <;> norm_num [prisonersDilemma, pdPayoff]
  · refine (hplay.mono fun ω hω => ?_).frequently
    rw [hω, hplayΓs]
    norm_num [prisonersDilemma, pdPayoff]

end Examples

end SafeParetoImprovements
