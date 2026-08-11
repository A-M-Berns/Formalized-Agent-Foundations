module

public import ProvabilityLogic.ProvabilityLogic.SolovaySentences

@[expose] public section

open scoped Formula

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {κ : Type*} [Nonempty κ]
         {α : Type*}
         {A B : _root_.Formula α}

namespace LogicGL

section

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL] {f : Realization α 𝔅}

/--
  **Arithmetical soundness of `GL`**: the interpretation of a `GL`-theorem is provable
  already in the base theory of the provability predicate (for the standard
  provability of an arithmetic theory, in `𝗜𝚺₁`).
-/
lemma arithmetical_soundness (hA : A ∈ LogicGL) : T ⊢ f A := by
  replace hA := LogicGL.iff_provableHilbert.mp hA;
  induction hA with
  | nec _ ihA => exact 𝔅.D1 (Entailment.WeakerThan.pbl ihA);
  | mdp _ _ ihAB ihA => exact ihAB ⨀ ihA;
  | modalK => exact 𝔅.D2;
  | modal4 => exact 𝔅.D3;
  | modalL => exact formalized_löb_theorem;
  | _ =>
    dsimp [Formula.interpret];
    cl_prover;

/-- Arithmetical soundness of `GL` at the object-theory level; corollary of
`arithmetical_soundness`. -/
lemma arithmetical_soundness' (hA : A ∈ LogicGL) : U ⊢ f A :=
  Entailment.WeakerThan.pbl (arithmetical_soundness hA)

end

section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]
variable {M : RootedModel κ α}

theorem arithmetical_completeness_of_infinity_height (height : T.height = (⊤ : ℕ∞)) :
  (∀ f : StandardRealization α T, T ⊢ f A) → A ∈ LogicGL := by
  contrapose!;
  intro hA;
  replace h := LogicGL.iff_forces_root.not.mp hA;
  push Not at h;
  obtain ⟨κ, _, M, _, hA⟩ := h;
  have : Fintype M.World := Fintype.ofFinite _;
  exact unprovable_realization_exists T M hA (by simp_all);

theorem arithmetical_completeness_of_finite_le {n : ℕ} (height : n ≤ T.height)
  : (∀ f : StandardRealization α T, T ⊢ f A) →  □^[n] ⊥ 🡒 A ∈ LogicGL := by
  contrapose!;
  intro hA;
  replace h := LogicGL.iff_forces_root.not.mp hA;
  push Not at h;
  obtain ⟨κ, _, M, _, hA⟩ := h;
  replace hA := Model.World.not_forces_imp.mp hA;
  have : Fintype M.World := Fintype.ofFinite _;
  apply unprovable_realization_exists T M hA.2;
  apply lt_of_lt_of_le;
  . apply Nat.cast_lt.mpr $ RootedModel.iff_height_lt_root_forces_boxItr_bot |>.mpr hA.1;
  . exact height;

lemma arithmetical_completeness_iff_of_infinity_height (height : T.height = (⊤ : ℕ∞))
  : A ∈ LogicGL ↔ (∀ f : StandardRealization α T, T ⊢ f A) := by
  constructor;
  . intro h f;
    exact arithmetical_soundness' (f := f) h;
  . exact arithmetical_completeness_of_infinity_height height;

lemma arithmetical_completeness_iff_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1]
  : A ∈ LogicGL ↔ (∀ f : StandardRealization α T, T ⊢ f A) :=
  arithmetical_completeness_iff_of_infinity_height (FirstOrder.Arithmetic.height_eq_top_of_sigma1_sound T)

theorem eq_provabilityLogic_sigma1_sound [T.SoundOnHierarchy 𝚺 1] : @LogicGL α = T.provabilityLogic := by
  ext A;
  exact LogicGL.arithmetical_completeness_iff_of_sigma1_sound;

theorem eq_provabilityLogic_peano_arithmetic : @LogicGL α = (𝗣𝗔.provabilityLogic) := LogicGL.eq_provabilityLogic_sigma1_sound

end

end LogicGL

end
