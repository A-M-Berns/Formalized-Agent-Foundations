import SafeParetoImprovements.Assumptions
import SafeParetoImprovements.Reduction
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-!
# Two-player helpers for the worked examples (§4.5)

The paper's examples are all two-player games given as payoff tables.  This file fixes the
two-element player type `Two` and provides the handful of lemmas that turn the general
set-based definitions into finite checks over the table: a profile of a two-player game
is a pair, strict dominance for one player is a quantifier over the other player's
actions, and a game is reduced when no action of either player is dominated.
-/

namespace SafeParetoImprovements

namespace Examples

/-- The two players. -/
inductive Two | one | two
  deriving DecidableEq, Fintype

namespace Two

variable {𝒜 : Two → Type*}

/-- The profile `(a, x)`. -/
def pair (a : 𝒜 .one) (x : 𝒜 .two) : ∀ i, 𝒜 i
  | .one => a
  | .two => x

@[simp] lemma pair_one (a : 𝒜 .one) (x : 𝒜 .two) : pair a x .one = a := rfl
@[simp] lemma pair_two (a : 𝒜 .one) (x : 𝒜 .two) : pair a x .two = x := rfl

lemma eq_pair (b : ∀ i, 𝒜 i) : b = pair (b .one) (b .two) := by
  funext i; cases i <;> rfl

@[simp] lemma update_one (b : ∀ i, 𝒜 i) (a : 𝒜 .one) :
    Function.update b .one a = pair a (b .two) := by
  funext i; cases i <;> simp [pair]

@[simp] lemma update_two (b : ∀ i, 𝒜 i) (x : 𝒜 .two) :
    Function.update b .two x = pair (b .one) x := by
  funext i; cases i <;> simp [pair]

lemma mem_profiles_iff (Γ : Game Two 𝒜) (b : ∀ i, 𝒜 i) :
    b ∈ Γ.profiles ↔ b .one ∈ Γ.S .one ∧ b .two ∈ Γ.S .two := by
  constructor
  · intro h; exact ⟨h .one, h .two⟩
  · rintro ⟨h1, h2⟩ i; cases i <;> assumption

lemma pair_mem_profiles_iff (Γ : Game Two 𝒜) (a : 𝒜 .one) (x : 𝒜 .two) :
    pair a x ∈ Γ.profiles ↔ a ∈ Γ.S .one ∧ x ∈ Γ.S .two := by
  rw [mem_profiles_iff]; rfl

/-- Strict dominance for player one, as a check over player two's actions. -/
lemma strictlyDominates_one_iff (Γ : Game Two 𝒜) (a a' : 𝒜 .one) :
    Γ.StrictlyDominates .one a a' ↔
      a ∈ Γ.S .one ∧ a' ∈ Γ.S .one ∧
        ∀ x ∈ Γ.S .two, Γ.u (pair a' x) .one < Γ.u (pair a x) .one := by
  rw [Game.strictlyDominates_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h x hx => ?_, fun h b hb => ?_⟩
  · have := h (pair a x) ((pair_mem_profiles_iff Γ a x).2 ⟨‹_›, hx⟩)
    simpa using this
  · simpa using h (b .two) (hb .two)

/-- Strict dominance for player two, as a check over player one's actions. -/
lemma strictlyDominates_two_iff (Γ : Game Two 𝒜) (x x' : 𝒜 .two) :
    Γ.StrictlyDominates .two x x' ↔
      x ∈ Γ.S .two ∧ x' ∈ Γ.S .two ∧
        ∀ a ∈ Γ.S .one, Γ.u (pair a x') .two < Γ.u (pair a x) .two := by
  rw [Game.strictlyDominates_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h a ha => ?_, fun h b hb => ?_⟩
  · have := h (pair a x) ((pair_mem_profiles_iff Γ a x).2 ⟨ha, ‹_›⟩)
    simpa using this
  · simpa using h (b .one) (hb .one)

/-- A two-player game is reduced iff no action of either player is strictly dominated. -/
lemma reduced_iff (Γ : Game Two 𝒜) :
    Γ.Reduced ↔ (∀ a : 𝒜 .one, ¬ Γ.IsStrictlyDominated .one a) ∧
      (∀ x : 𝒜 .two, ¬ Γ.IsStrictlyDominated .two x) := by
  constructor
  · intro h; exact ⟨fun a => h .one a, fun x => h .two x⟩
  · rintro ⟨h1, h2⟩ i
    cases i
    · exact h1
    · exact h2

end Two

end Examples

end SafeParetoImprovements
