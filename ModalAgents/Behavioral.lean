/-
  Behavioral equivalence of modal agents (Barasz, §4, p. 12).

  Main paper result:
  - `modalAgent_behavioral`: modal agents are behavioral (§4, Thm 4.8),
    formalized as a GL-level equivalence of outcome formulas.
-/

import ModalAgents.Cooperation

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

/-- Modal agents are behavioral, in the GL-level modal-agent restriction:
behaviorally equivalent opponents give GL-equivalent outcome formulas.

Paper node: Theorem 4.8 (§4). -/
theorem modalAgent_behavioral (X : ModalAgent) {Y Z : ModalAgent} (h : Y ≈ Z) :
    Modal.GL ⊢ outcome X Y 🡘 outcome X Z := by
  have hY := outcome_fixed_point X Y
  have hZ := outcome_fixed_point X Z
  have hcong : Modal.GL ⊢
      X.formula⟦substFull (outcome Y X)
        (fun j : Fin X.arity => outcome Y (X.references j))⟧ 🡘
      X.formula⟦substFull (outcome Z X)
        (fun j : Fin X.arity => outcome Z (X.references j))⟧ := by
    apply subst_congr
    intro a
    match a with
    | 0 => exact h X
    | k+1 =>
      show Modal.GL ⊢
        (if hk : k < X.arity then outcome Y (X.references ⟨k, hk⟩) else .atom (k+1)) 🡘
        (if hk : k < X.arity then outcome Z (X.references ⟨k, hk⟩) else .atom (k+1))
      by_cases hk : k < X.arity
      · simp only [dif_pos hk]
        exact h (X.references ⟨k, hk⟩)
      · simp only [dif_neg hk]
        exact E!_id
  exact E!_trans hY (E!_trans hcong (E!_symm hZ))
