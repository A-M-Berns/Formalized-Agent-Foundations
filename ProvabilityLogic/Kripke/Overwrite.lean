module

public import ProvabilityLogic.Kripke.Basic

/-!
# Overwriting the valuation of a Kripke model at a single world

`Model.overwrite M t p v` is the Kripke model obtained from `M` by overwriting the
valuation of the atom `p` at the single world `t` with the truth value `v`, leaving
the frame (accessibility relation) unchanged.

This is a generic Kripke-model construction, reusable beyond any particular logic;
it was originally introduced ad hoc in `ProvabilityLogic.Logic.GL.Fixedpoint` to give a semantic
proof of SV82, Corollary 3.8 (removing a modalized atom from a provable sequent), but
the construction and its basic properties do not depend on GL or on modalized atoms.
-/

@[expose]
public section

open scoped Formula

namespace Model

variable [Nonempty κ] {M : Model κ α} {p : α}

/-- The model obtained from `M` by overwriting the valuation of the atom `p`
at the single world `t` with `v`. The frame is unchanged. -/
def overwrite (M : Model κ α) (t : κ) (p : α) (v : Prop) : Model κ α where
  Rel' := M.Rel'
  Val' := fun w a => (w = t ∧ a = p ∧ v) ∨ (¬(w = t ∧ a = p) ∧ M.Val' w a)

namespace overwrite

variable {t : κ} {v : Prop}

instance [IsTrans _ M.Rel] : IsTrans _ (M.overwrite t p v).Rel := by
  constructor; intro a b c; exact IsTrans.trans (r := M.Rel) a b c

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.overwrite t p v).Rel := by
  constructor; intro a; exact Std.Irrefl.irrefl (r := M.Rel) a

instance [M.IsFiniteGL] : (M.overwrite t p v).IsFiniteGL where
  finite := IsFiniteGL.finite (M := M)

@[simp] lemma val_self : (M.overwrite t p v).Val t p ↔ v := by
  simp [overwrite, Model.Val]

lemma val_of_ne_world {w : κ} (h : w ≠ t) {a : α} :
    (M.overwrite t p v).Val w a ↔ M.Val w a := by
  simp [overwrite, Model.Val, h]

lemma val_of_ne_atom {w : κ} {a : α} (h : a ≠ p) :
    (M.overwrite t p v).Val w a ↔ M.Val w a := by
  simp [overwrite, Model.Val, h]

/-- Forcing is unchanged at worlds that neither are `t` nor see `t`. -/
lemma forces_iff_of_not_rel [IsTrans _ M.Rel] (B : Formula α) :
    ∀ w : κ, w ≠ t → ¬M.Rel w t →
      (Model.World.Forces (M := M.overwrite t p v) w B ↔ Model.World.Forces (M := M) w B) := by
  induction B with
  | atom a =>
    intro w hne _
    exact val_of_ne_world hne
  | bot =>
    intro w _ _
    simp [Model.World.Forces]
  | imp A B ihA ihB =>
    intro w hne hr
    have := ihA w hne hr
    have := ihB w hne hr
    simp only [Model.World.Forces]
    grind
  | box A ih =>
    intro w hne hr
    simp only [Model.World.Forces]
    have hy : ∀ y : κ, M.Rel w y → y ≠ t ∧ ¬M.Rel y t := by
      intro y Rwy
      constructor
      . rintro rfl; exact hr Rwy
      . intro h'; exact hr (IsTrans.trans _ _ _ Rwy h')
    constructor
    . intro hf y Rwy
      exact (ih y (hy y Rwy).1 (hy y Rwy).2).mp (hf y Rwy)
    . intro hf y Rwy
      exact (ih y (hy y Rwy).1 (hy y Rwy).2).mpr (hf y Rwy)

end overwrite

end Model

end
