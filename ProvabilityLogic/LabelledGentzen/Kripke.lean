module

public import ProvabilityLogic.Kripke.Basic
public import ProvabilityLogic.LabelledGentzen.Basic

@[expose]
public section

open scoped Formula

/-!
Kripke semantics for the labelled sequent calculus `G3KGL` (`⊢ˡ!`), following
`[Neg14]` §5 (Definition 5.3, Theorem 5.4). A label assignment `L : M.LabelMap`
interprets the world-labels, and a labelled sequent is valid under `L` when,
whenever all relational atoms and all antecedent formulas hold, some succedent
formula holds.
-/

open LabelledGentzen

variable {κ : Type u} [Nonempty κ]
         {α : Type v}
         {M : Model κ α}


namespace LabelledGentzen.LabelledSequent

variable {S : LabelledSequent α} {R : Finset LabelRel} {Γ Δ : Finset (LabelledFormula α)}
         {lf : LabelledFormula α} {p : LabelRel}

@[grind =>]
lemma label_mem_labels_of_mem_ant (h : lf ∈ S.ant) : lf.label ∈ S.labels :=
  Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_image_of_mem _ h

@[grind =>]
lemma label_mem_labels_of_mem_suc (h : lf ∈ S.suc) : lf.label ∈ S.labels :=
  Finset.mem_union_left _ $ Finset.mem_union_left _ $ Finset.mem_union_right _ $ Finset.mem_image_of_mem _ h

@[grind =>]
lemma mem_labels_of_mem_rel_fst (h : p ∈ S.rel) : p.1 ∈ S.labels :=
  Finset.mem_union_left _ $ Finset.mem_union_right _ $ Finset.mem_image_of_mem _ h

@[grind =>]
lemma mem_labels_of_mem_rel_snd (h : p ∈ S.rel) : p.2 ∈ S.labels :=
  Finset.mem_union_right _ $ Finset.mem_image_of_mem _ h

end LabelledGentzen.LabelledSequent


namespace Model

/-- A label assignment into `M`: an interpretation of world-labels as worlds of `M`. -/
abbrev LabelMap (M : Model κ α) := Label → M.World

/-- Validity of a labelled sequent in `M` under the label assignment `L`:
if every relational atom and every antecedent formula holds under `L`, then
some succedent formula holds under `L`. -/
@[grind]
def ValidateLabelled (M : Model κ α) (L : M.LabelMap) (S : LabelledSequent α) : Prop :=
  (∀ p ∈ S.rel, L p.1 ≺ L p.2) →
  (∀ lf ∈ S.ant, L lf.label ⊩ lf.formula) →
  ∃ lf ∈ S.suc, L lf.label ⊩ lf.formula

notation:50 M " ⊧ˡ[" L "] " S:51 => Model.ValidateLabelled M L S

variable {L : M.LabelMap} {R R' : Finset LabelRel} {Γ Γ' Δ Δ' : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

lemma validate_labelled_axm : M ⊧ˡ[L] (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) := by
  intro _ h;
  exact ⟨x ∶ A, by grind, h _ (by grind)⟩;

lemma validate_labelled_botL : M ⊧ˡ[L] (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) := by
  intro _ h;
  have := h (x ∶ (⊥ : Formula α)) (by grind);
  grind;

lemma validate_labelled_wkRel (h : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ)) (hR : R ⊆ R') : M ⊧ˡ[L] (R' ⸴ Γ ⟹ˡ Δ) := by
  intro hrel hant;
  exact h (λ p hp => hrel p (hR hp)) hant;

lemma validate_labelled_wkAnt (h : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ)) (hΓ : Γ ⊆ Γ') : M ⊧ˡ[L] (R ⸴ Γ' ⟹ˡ Δ) := by
  intro hrel hant;
  exact h hrel (λ lf hlf => hant lf (hΓ hlf));

lemma validate_labelled_wkSuc (h : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ)) (hΔ : Δ ⊆ Δ') : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ') := by
  intro hrel hant;
  obtain ⟨lf, hlf, h⟩ := h hrel hant;
  exact ⟨lf, hΔ hlf, h⟩;

section WithDecidableEq

variable [DecidableEq α]

lemma validate_labelled_impL
  (h₁ : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ))
  (h₂ : M ⊧ˡ[L] (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ))
  : M ⊧ˡ[L] (R ⸴ insert (x ∶ A 🡒 B) Γ ⟹ˡ Δ) := by
  intro hrel hant;
  replace h₁ := h₁ hrel;
  replace h₂ := h₂ hrel;
  simp only [Finset.mem_insert, forall_eq_or_imp] at hant;
  grind;

lemma validate_labelled_impR
  (h : M ⊧ˡ[L] (R ⸴ insert (x ∶ A) Γ ⟹ˡ insert (x ∶ B) Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ insert (x ∶ A 🡒 B) Δ) := by
  intro hrel hant;
  by_cases hA : L x ⊩ A;
  . obtain ⟨lf, hlf, hf⟩ := h hrel (by grind);
    rcases Finset.mem_insert.mp hlf with rfl | hlf;
    . exact ⟨x ∶ A 🡒 B, by grind, by grind⟩;
    . exact ⟨lf, by grind, hf⟩;
  . exact ⟨x ∶ A 🡒 B, by grind, by grind⟩;

lemma validate_labelled_boxL
  (hxy : (x, y) ∈ R) (hxA : (x ∶ □A) ∈ Γ)
  (h : M ⊧ˡ[L] (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ) := by
  intro hrel hant;
  apply h hrel;
  intro lf hlf;
  rcases Finset.mem_insert.mp hlf with rfl | hlf;
  . exact hant (x ∶ □A) hxA (L y) (hrel (x, y) hxy);
  . exact hant lf hlf;

end WithDecidableEq

section WithDecidableEqBoxRLob

variable [DecidableEq α]

open LabelledGentzen.LabelledSequent in
lemma validate_labelled_boxRLob [M.IsGL]
  (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels)
  (h : ∀ L : M.LabelMap, M ⊧ˡ[L] (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) := by
  intro hrel hant;
  by_contra hC;
  push Not at hC;
  have hyx : y ≠ x := by
    rintro rfl;
    exact hfresh $ label_mem_labels_of_mem_suc (lf := y ∶ □A) (by grind);
  have hxA : L x ⊮ □A := hC (x ∶ □A) (by grind);
  obtain ⟨z, Rxz, hz⟩ := Model.World.not_forces_box.mp hxA;
  obtain ⟨t, ⟨Rxt, hntA⟩, ht⟩ := M.terminalOf {w | L x ≺ w ∧ w ⊮ A} ⟨z, Rxz, hz⟩;
  have hrel' : ∀ p ∈ (insert (x, y) R : Finset LabelRel),
      Function.update L y t p.1 ≺ Function.update L y t p.2 := by
    rintro p hp;
    rcases Finset.mem_insert.mp hp with rfl | hp';
    . show Function.update L y t x ≺ Function.update L y t y;
      rw [Function.update_self, Function.update_of_ne (Ne.symm hyx)];
      exact Rxt;
    . have h₁ : p.1 ≠ y := by
        intro heq;
        apply hfresh;
        have := mem_labels_of_mem_rel_fst (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) hp';
        rwa [heq] at this;
      have h₂ : p.2 ≠ y := by
        intro heq;
        apply hfresh;
        have := mem_labels_of_mem_rel_snd (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) hp';
        rwa [heq] at this;
      simpa [Function.update_of_ne h₁, Function.update_of_ne h₂] using hrel p hp';
  have hant' : ∀ lf ∈ insert (y ∶ □A) Γ,
      Function.update L y t lf.label ⊩ lf.formula := by
    rintro lf hlf;
    rcases Finset.mem_insert.mp hlf with rfl | hlf';
    . show Function.update L y t y ⊩ □A;
      rw [Function.update_self];
      intro u Rtu;
      by_contra hu;
      exact ht u ⟨_root_.trans Rxt Rtu, hu⟩ Rtu;
    . have hly : lf.label ≠ y := by
        intro hly;
        apply hfresh;
        have := label_mem_labels_of_mem_ant (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) hlf';
        rwa [hly] at this;
      rw [Function.update_of_ne hly];
      exact hant lf hlf';
  obtain ⟨lf, hlf, hf⟩ := h (Function.update L y t) hrel' hant';
  rcases Finset.mem_insert.mp hlf with rfl | hlf';
  . apply hntA;
    have : Function.update L y t y ⊩ A := hf;
    rwa [Function.update_self] at this;
  . have hly : lf.label ≠ y := by
      intro hly;
      apply hfresh;
      have := label_mem_labels_of_mem_suc (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) (lf := lf) (by grind);
      rwa [hly] at this;
    apply hC lf (by grind);
    rwa [Function.update_of_ne hly] at hf;

end WithDecidableEqBoxRLob

lemma validate_labelled_irref [Std.Irrefl M.Rel] (hxx : (x, x) ∈ R) : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ) := by
  intro hrel _;
  exact absurd (hrel (x, x) hxx) (Std.Irrefl.irrefl _);

lemma validate_labelled_trans [IsTrans _ M.Rel]
  (hxy : (x, y) ∈ R) (hyz : (y, z) ∈ R)
  (h : M ⊧ˡ[L] (insert (x, z) R ⸴ Γ ⟹ˡ Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ) := by
  intro hrel hant;
  apply h ?_ hant;
  intro p hp;
  rcases Finset.mem_insert.mp hp with rfl | hp;
  . exact _root_.trans (hrel (x, y) hxy) (hrel (y, z) hyz);
  . exact hrel p hp;

end Model


namespace LabelledGentzen.ProvableLabelledGentzen

namespace Kripke

open Model in
/--
Soundness of `G3KGL` with respect to Kripke semantics on `GL` models.

- [Neg14, Theorem 5.4]
-/
theorem soundness [DecidableEq α] {S : LabelledSequent α} (h : ⊢ˡ S) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGL] → ∀ L : M.LabelMap, M ⊧ˡ[L] S := by
  intro κ _ M _;
  induction h with
  | axm x A => exact λ _ => validate_labelled_axm;
  | botL x => exact λ _ => validate_labelled_botL;
  | wkRel _ hR ih => exact λ L => validate_labelled_wkRel (ih L) hR;
  | wkAnt _ hΓ ih => exact λ L => validate_labelled_wkAnt (ih L) hΓ;
  | wkSuc _ hΔ ih => exact λ L => validate_labelled_wkSuc (ih L) hΔ;
  | impL _ _ ih₁ ih₂ => exact λ L => validate_labelled_impL (ih₁ L) (ih₂ L);
  | impR _ ih => exact λ L => validate_labelled_impR (ih L);
  | boxL hxy hxA _ ih => exact λ L => validate_labelled_boxL hxy hxA (ih L);
  | boxRLob hfresh _ ih => exact λ L => validate_labelled_boxRLob hfresh ih;
  | irref hxx => exact λ _ => validate_labelled_irref hxx;
  | trans hxy hyz _ ih => exact λ L => validate_labelled_trans hxy hyz (ih L);

/-- A formula provable as `∅ ⸴ ∅ ⟹ˡ {x ∶ A}` is valid in every `GL` model. -/
theorem soundness_formula [DecidableEq α] {x : Label} {A : Formula α} (h : ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGL] → M.Validate A := by
  intro κ _ M _ w;
  obtain ⟨lf, hlf, hf⟩ := soundness h M (λ _ => w) (by grind) (by grind);
  grind;

end Kripke

end LabelledGentzen.ProvableLabelledGentzen

end
