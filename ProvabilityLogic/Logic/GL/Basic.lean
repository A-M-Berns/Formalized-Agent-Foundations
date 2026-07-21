module

public import ProvabilityLogic.Logic.SumQuasiNormal
public import ProvabilityLogic.Kripke.Unravelling
public import ProvabilityLogic.LabelledGentzen.Gentzen
public import ProvabilityLogic.LabelledGentzen.Completeness

@[expose]
public section

variable {α : Type u}

abbrev LogicGL {α} : Logic α := { A | ⊢ʰ A }

namespace LogicGL

theorem provability_TFAE [DecidableEq α] {A : Formula α} : [
  A ∈ LogicGL,
  ⊢ʰ A,
  ⊢ᵍ (∅ ⟹ {A}),
  ⊢ᵍᶜ (∅ ⟹ {A}),
  ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {(0 : LabelledGentzen.Label) ∶ A}),
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGL] → M.root.1 ⊩ A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLTree] → M.root.1 ⊩ A
].TFAE
  := by
  tfae_have 1 ↔ 2 := by grind;
  tfae_have 2 → 3 := ProvableGentzen.of_provableHilbert;
  tfae_have 3 → 2 := by
    intro h;
    simpa using ProvableHilbert.mdp (ProvableHilbert.of_provableGentzen (S := ∅ ⟹ {A}) h) (by simp);
  tfae_have 3 → 4 := GentzenWithCutProvable.of_without_cut;
  tfae_have 4 → 3 := ProvableGentzen.of_with_cut;
  tfae_have 3 ↔ 5 := iff_provableGentzen_provableLabelledGentzen;
  tfae_have 2 → 6 := by
    intro h κ _;
    apply ProvableHilbert.Kripke.finite_soundness h;
  tfae_have 6 → 2 := ProvableHilbert.Kripke.completeness;
  tfae_have 6 → 7 := by
    intro h κ _ M _;
    apply h;
  tfae_have 7 → 6 := by
    intro h κ _ M _ x;
    exact Model.toRootedModel.forces_same_at_root.mp $ h (M.toRootedModel x);
  tfae_have 7 → 8 := by
    intro h κ _ M _;
    exact h M;
  tfae_have 8 → 7 := by
    intro h κ _ M _;
    exact (RootedModel.unravelling.modal_equivalence_root (M := M)).mp $ h M.unravelling;
  tfae_finish;

theorem iff_provableHilbert [DecidableEq α] {A : Formula α} : A ∈ LogicGL ↔ ⊢ʰ A :=
  provability_TFAE.out 0 1

theorem iff_provableGentzen [DecidableEq α] {A : Formula α} : A ∈ LogicGL ↔ ⊢ᵍ (∅ ⟹ {A}) :=
  provability_TFAE.out 0 2

theorem iff_provableGentzenWithCut [DecidableEq α] {A : Formula α} : A ∈ LogicGL ↔ ⊢ᵍᶜ (∅ ⟹ {A}) :=
  provability_TFAE.out 0 3

theorem iff_provableLabelledGentzen [DecidableEq α] {A : Formula α} :
    A ∈ LogicGL ↔ ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {(0 : LabelledGentzen.Label) ∶ A}) :=
  provability_TFAE.out 0 4

theorem iff_forces [DecidableEq α] {A : Formula α} :
    A ∈ LogicGL ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A :=
  provability_TFAE.out 0 5

theorem iff_forces_root [DecidableEq α] {A : Formula α} :
    A ∈ LogicGL ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGL] → M.root.1 ⊩ A :=
  provability_TFAE.out 0 6

/-- GL-provability is characterized by validity over the (smaller) class of finite
GL *tree* models (`IsFiniteGLTree`): it suffices to check finite GL-models that
are trees. -/
theorem iff_forces_root_tree [DecidableEq α] {A : Formula α} :
    A ∈ LogicGL ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLTree] →
      M.root.1 ⊩ A :=
  provability_TFAE.out 0 7

theorem provableHilbert_of_provableGentzen [DecidableEq α] {A : Formula α} :
    ⊢ᵍ (∅ ⟹ {A}) → ⊢ʰ A :=
  fun h => provability_TFAE.out 2 1 |>.mp h

end LogicGL

/-- Provability of a formula in the label-free Gentzen calculus `⊢ᵍ` is decidable,
via the labelled proof search. -/
instance decidable_provableGentzen_formula (A : Formula α) [DecidableEq α] :
  Decidable (⊢ᵍ (∅ ⟹ {A})) :=
  decidable_of_iff _ (iff_provableGentzen_provableLabelledGentzen (x := 0)).symm

/-- Membership in `LogicGL` is decidable, via the labelled proof search. -/
instance LogicGL.decidableMem (A : Formula α) [DecidableEq α] : Decidable (A ∈ LogicGL) :=
  decidable_of_iff _ LogicGL.iff_provableGentzen.symm

end
