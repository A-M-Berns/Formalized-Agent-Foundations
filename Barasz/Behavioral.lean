/-
  Behavioral equivalence of modal agents (Barasz, §4, p. 12).

  Main paper result:
  - `modalAgent_behavioral`: modal agents are behavioral (§4, Thm 4.8),
    formalized as a GL-level equivalence of outcome formulas.
-/

import Barasz.Cooperation

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-- GL-level behavioral equivalence restricted to modal agents. -/
def BehavEquiv (X X' : ModalAgent) : Prop :=
  ∀ Y, Modal.GL ⊢ outcome X Y 🡘 outcome X' Y

@[inherit_doc] scoped[ModalAgent] infix:50 " ≈ " => BehavEquiv

namespace BehavEquiv

open scoped ModalAgent

@[refl] lemma refl (X : ModalAgent) : X ≈ X := fun _ => E!_id

@[symm] lemma symm {X X' : ModalAgent} (h : X ≈ X') : X' ≈ X :=
  fun Y => E!_symm (h Y)

@[trans] lemma trans {X X' X'' : ModalAgent} (h₁ : X ≈ X') (h₂ : X' ≈ X'') :
    X ≈ X'' :=
  fun Y => E!_trans (h₁ Y) (h₂ Y)

end BehavEquiv

open scoped ModalAgent

/-- Cooperation is preserved under behavioral equivalence. -/
lemma Cooperates.iff_of_behavEquiv {X X' : ModalAgent} (h : X ≈ X') (Y : ModalAgent) :
    Cooperates X Y ↔ Cooperates X' Y := by
  have ⟨h⟩ := h Y
  exact ⟨fun ⟨hX⟩ => ⟨and₁ ⨀ h ⨀ hX⟩, fun ⟨hX'⟩ => ⟨and₂ ⨀ h ⨀ hX'⟩⟩

/-- Defection is preserved under behavioral equivalence. -/
lemma Defects.iff_of_behavEquiv {X X' : ModalAgent} (h : X ≈ X') (Y : ModalAgent) :
    Defects X Y ↔ Defects X' Y := by
  unfold Defects
  rw [not_iff_not]
  exact Cooperates.iff_of_behavEquiv h Y

/-- Behavioral equivalence is preserved when the equivalent agents appear as
the opponent. -/
lemma outcome_iff_of_behavEquiv {X X' : ModalAgent} (h : X ≈ X') (Z : ModalAgent) :
    Modal.GL ⊢ outcome Z X 🡘 outcome Z X' := by
  have hX := outcome_fixed_point Z X
  have hX' := outcome_fixed_point Z X'
  have hcong : Modal.GL ⊢
      Z.formula⟦substFull (outcome X Z)
        (fun j : Fin Z.arity => outcome X (Z.references j))⟧ 🡘
      Z.formula⟦substFull (outcome X' Z)
        (fun j : Fin Z.arity => outcome X' (Z.references j))⟧ := by
    apply subst_congr
    intro a
    match a with
    | 0 => exact h Z
    | k+1 =>
      show Modal.GL ⊢
        (if hk : k < Z.arity then outcome X (Z.references ⟨k, hk⟩) else .atom (k+1)) 🡘
        (if hk : k < Z.arity then outcome X' (Z.references ⟨k, hk⟩) else .atom (k+1))
      by_cases hk : k < Z.arity
      · simp only [dif_pos hk]
        exact h (Z.references ⟨k, hk⟩)
      · simp only [dif_neg hk]
        exact E!_id
  exact E!_trans hX (E!_trans hcong (E!_symm hX'))

/-- GL-level modal-agent restriction of Barasz §4, Thm 4.8. -/
theorem modalAgent_behavioral (X : ModalAgent) {Y Z : ModalAgent} (h : Y ≈ Z) :
    Modal.GL ⊢ outcome X Y 🡘 outcome X Z :=
  outcome_iff_of_behavEquiv h X
