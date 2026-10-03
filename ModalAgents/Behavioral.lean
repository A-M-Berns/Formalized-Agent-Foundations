/-
  Behavioral equivalence of modal agents (Barasz, §4, p. 12).

  Main paper result:
  - `modalAgent_behavioral`: modal agents are behavioral (§4, Thm 4.8),
    formalized as a GL-level equivalence of outcome formulas.
-/

import ModalAgents.Cooperation

open LogicGL Formula

/-- GL-level behavioral equivalence restricted to modal agents. -/
def BehavEquiv (X X' : ModalAgent) : Prop :=
  ∀ Y, (outcome X Y 🡘 outcome X' Y) ∈ (LogicGL : Logic ℕ)

@[inherit_doc] scoped[ModalAgent] infix:50 " ≈ " => BehavEquiv

namespace BehavEquiv

open scoped ModalAgent

@[refl] lemma refl (X : ModalAgent) : X ≈ X := fun _ => GL.iff_refl

@[symm] lemma symm {X X' : ModalAgent} (h : X ≈ X') : X' ≈ X :=
  fun Y => GL.iff_symm (h Y)

@[trans] lemma trans {X X' X'' : ModalAgent} (h₁ : X ≈ X') (h₂ : X' ≈ X'') :
    X ≈ X'' :=
  fun Y => GL.iff_trans (h₁ Y) (h₂ Y)

end BehavEquiv

open scoped ModalAgent

/-- Modal agents are behavioral, in the GL-level modal-agent restriction:
behaviorally equivalent opponents give GL-equivalent outcome formulas.

Paper node: Theorem 4.8 (§4). -/
theorem modalAgent_behavioral (X : ModalAgent) {Y Z : ModalAgent} (h : Y ≈ Z) :
    (outcome X Y 🡘 outcome X Z) ∈ (LogicGL : Logic ℕ) := by
  have hY := outcome_fixed_point X Y
  have hZ := outcome_fixed_point X Z
  have hcong :
      (X.formula⟦substFull (outcome Y X)
        (fun j : Fin X.arity => outcome Y (X.references j))⟧ 🡘
      X.formula⟦substFull (outcome Z X)
        (fun j : Fin X.arity => outcome Z (X.references j))⟧) ∈ (LogicGL : Logic ℕ) := by
    apply subst_congr
    intro a
    match a with
    | 0 => exact h X
    | k+1 =>
      show ((if hk : k < X.arity then outcome Y (X.references ⟨k, hk⟩) else .atom (k+1)) 🡘
        (if hk : k < X.arity then outcome Z (X.references ⟨k, hk⟩) else .atom (k+1))) ∈
          (LogicGL : Logic ℕ)
      by_cases hk : k < X.arity
      · simp only [dite_eq_left hk]
        exact h (X.references ⟨k, hk⟩)
      · simp only [dite_eq_right hk]
        exact GL.iff_refl
  exact GL.iff_trans hY (GL.iff_trans hcong (GL.iff_symm hZ))

namespace BehavEquiv

/-- Behavioral equivalence transports an outcome in both agent positions. -/
lemma outcome_congr {X X' Y Y' : ModalAgent} (hX : X ≈ X') (hY : Y ≈ Y') :
    (outcome X Y 🡘 outcome X' Y') ∈ (LogicGL : Logic ℕ) :=
  GL.iff_trans (hX Y) (modalAgent_behavioral X' hY)

/-- Cooperation is invariant under behavioral equivalence in both positions. -/
lemma cooperates_iff {X X' Y Y' : ModalAgent} (hX : X ≈ X') (hY : Y ≈ Y') :
    Cooperates X Y ↔ Cooperates X' Y' :=
  ⟨GL.iff_mp (outcome_congr hX hY), GL.iff_mpr (outcome_congr hX hY)⟩

/-- Defection-as-unprovability is invariant under behavioral equivalence. -/
lemma defects_iff {X X' Y Y' : ModalAgent} (hX : X ≈ X') (hY : Y ≈ Y') :
    Defects X Y ↔ Defects X' Y' :=
  not_congr (cooperates_iff hX hY)

/-- Provable defection is invariant under behavioral equivalence. -/
lemma provablyDefects_iff {X X' Y Y' : ModalAgent} (hX : X ≈ X') (hY : Y ≈ Y') :
    ProvablyDefects X Y ↔ ProvablyDefects X' Y' :=
  ⟨GL.iff_mp (GL.neg_congr (outcome_congr hX hY)),
    GL.iff_mpr (GL.neg_congr (outcome_congr hX hY))⟩

end BehavEquiv
