module

public import ProvabilityLogic.Kripke.Basic
public import ProvabilityLogic.Gentzen.GL.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finite.Prod

@[expose]
public section

open scoped Formula

variable {κ : Type u} [Nonempty κ]
         {α : Type v} [DecidableEq α]
         {M : Model κ α}
         {A B : Formula α} {Γ Γ' Δ Δ' : FormulaFinset α}

open LogicGL

namespace LogicGL

abbrev trivial_GL_model {α} : Model (Fin 1) α where
  Rel' := λ _ _ => False
  Val' := λ _ _ => False

instance : trivial_GL_model (α := α) |>.IsFiniteGL where
  finite := inferInstance;
  trans  := by tauto;
  irrefl := by tauto;

end LogicGL


namespace Model.World

variable {M : Model κ α} {x : M.World}

@[grind]
def ForcesSequent (x : M.World) (S : Sequent α) : Prop := (∀ C ∈ S.ant, x ⊩ C) → (∃ D ∈ S.suc, x ⊩ D)
infix:55 " ⊩ " => ForcesSequent

omit [DecidableEq α] in lemma forces_ctx_singleton_sequent : x ⊩ (Γ ⟹ {A}) ↔ (∀ C ∈ Γ, x ⊩ C) → x ⊩ A := by grind;
omit [DecidableEq α] in lemma forces_singleton_sequent : x ⊩ (∅ ⟹ {A}) ↔ (x ⊩ A) := by grind;

variable {Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α}

omit [DecidableEq α] in lemma forces_sequent_axm : x ⊩ ({A} ⟹ {A}) := by
  intro h;
  use A;
  constructor;
  . grind;
  . exact h _ (by grind);

omit [DecidableEq α] in lemma forces_sequent_botL : x ⊩ (({⊥} : FormulaFinset α) ⟹ ∅) := by
  simp [Model.World.ForcesSequent];

omit [DecidableEq α] in lemma forces_sequent_wkL (h : x ⊩ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ' := by grind) : x ⊩ (Γ' ⟹ Δ) := by
  intro h';
  apply h;
  grind;

omit [DecidableEq α] in lemma forces_sequent_wkR (h : x ⊩ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ' := by grind) : x ⊩ (Γ ⟹ Δ') := by
  intro hΓ;
  obtain ⟨D, hD₁, hD₂⟩ := h hΓ;
  grind;

lemma forces_sequent_impL (h₁ : x ⊩ (Γ ⟹ insert A Δ)) (h₂ : x ⊩ (insert B Γ ⟹ Δ)) : x ⊩ (insert (A 🡒 B) Γ ⟹ Δ) := by
  intro h;
  simp only [Finset.mem_insert, forall_eq_or_imp] at h;
  grind;

lemma forces_sequent_impR (h : x ⊩ (insert A Γ ⟹ insert B Δ)) : x ⊩ (Γ ⟹ insert (A 🡒 B) Δ) := by
  intro hΓ;
  by_cases x ⊩ A;
  . obtain ⟨D, hD₁, hD₂⟩ := h $ by grind;
    simp at hD₁;
    rcases hD₁ with (rfl | hD₁);
    . use A 🡒 D; grind;
    . use D; grind;
  . use A 🡒 B;
    grind;

lemma forces_sequent_cut (h₁ : x ⊩ (Γ₁ ⟹ insert A Δ₁)) (h₂ : x ⊩ (insert A Γ₂ ⟹ Δ₂)) : x ⊩ (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := by
  intro h;
  obtain ⟨D, hD, hDx⟩ := h₁ (fun C hC => h C (by grind));
  rcases Finset.mem_insert.mp hD with rfl | hD;
  . obtain ⟨D', hD', hD'x⟩ := h₂ (fun C hC => by rcases Finset.mem_insert.mp hC with rfl | hC <;> grind);
    exact ⟨D', by grind, hD'x⟩;
  . exact ⟨D, by grind, hDx⟩;

end Model.World



namespace Model

omit [DecidableEq α]

@[grind]
def ValidateSequent (M : Model κ α) (S : Sequent α) : Prop := ∀ x : M.World, x ⊩ S
infix:50 " ⊧ " => ValidateSequent

variable {M : Model κ α} {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α}

omit [DecidableEq α] in
/-- Validity of the singleton sequent `∅ ⟹ {A}` is exactly validity of `A`. -/
lemma validateSequent_singleton_iff : M ⊧ (∅ ⟹ {A}) ↔ M.Validate A :=
  forall_congr' fun _ => World.forces_singleton_sequent

lemma validate_gentzen_axm : M ⊧ ({A} ⟹ {A}) := by
  intro x h;
  use A;
  constructor;
  . grind;
  . exact h _ (by grind);

lemma validate_gentzen_botL : M ⊧ ({⊥} ⟹ ∅) := by
  intro x;
  simp [World.ForcesSequent];

lemma validate_gentzen_wkL (h : M ⊧ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ' := by grind) : M ⊧ (Γ' ⟹ Δ) := by
  intro x h';
  apply h;
  grind;

lemma validate_gentzen_wkR (h : M ⊧ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ' := by grind) : M ⊧ (Γ ⟹ Δ') := by
  intro x hΓ;
  obtain ⟨D, hD₁, hD₂⟩ := h x hΓ;
  grind;

lemma validate_gentzen_impL [DecidableEq α] (hA : M ⊧ (Γ ⟹ insert A Δ)) (hB : M ⊧ (insert B Γ ⟹ Δ)) : M ⊧ ((insert (A 🡒 B) Γ) ⟹ Δ) := by
  intro x h;
  replace hA := hA x
  replace hB := hB x;
  simp only [Finset.mem_insert, forall_eq_or_imp] at h;
  grind;

lemma validate_gentzen_impR [DecidableEq α] (h : M ⊧ ((insert A Γ) ⟹ (insert B Δ))) : M ⊧ (Γ ⟹ (insert (A 🡒 B) Δ)) := by
  intro x hΓ;
  by_cases x ⊩ A;
  . obtain ⟨D, hD₁, hD₂⟩ := h x $ by grind;
    simp at hD₁;
    rcases hD₁ with (rfl | hD₁);
    . use A 🡒 D; grind;
    . use D; grind;
  . use A 🡒 B;
    grind;


open Model.World
lemma validate_gentzen_boxGL [DecidableEq α] [M.IsGL] (h : M ⊧ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : M ⊧ (Γ.box ⟹ {□A}) := by
  intro x;
  apply forces_ctx_singleton_sequent.mpr;
  intro hΓ y Rxy;
  apply forces_ctx_singleton_sequent.mp $ h y;
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, forall_eq_or_imp];
  constructor;
  . by_contra hC;
    obtain ⟨z, Ryz, hz⟩ := Model.World.not_forces_box.mp hC;
    let ⟨t, ⟨Ryt, hntA⟩, ht₂⟩ := M.terminalOf ({z | y ≺ z ∧ z ⊮ A}) ⟨z, ⟨Ryz, hz⟩⟩;
    apply hntA;
    apply forces_ctx_singleton_sequent.mp $ h t;
    simp;
    constructor;
    . rintro t' Rtt';
      by_contra;
      exact ht₂ t' ⟨_root_.trans Ryt Rtt', by assumption⟩ Rtt';
    . rintro C (hC | ⟨C, hC, rfl⟩);
      . apply hΓ (□C) (by simpa) t;
        apply _root_.trans Rxy Ryt;
      . intro t' Rtt';
        apply hΓ (□C) (by simpa) t';
        apply _root_.trans (_root_.trans Rxy Ryt) Rtt';
  . rintro C (hC | ⟨C, hC, rfl⟩);
    . exact hΓ (□C) (by simpa) y Rxy;
    . intro z Ryz;
      exact hΓ (□C) (by simpa) z (_root_.trans Rxy Ryz);

end Model


namespace LogicGL

namespace ProvableGentzen

namespace Kripke

open Model in
theorem soundness (h : ⊢ᵍ[GL] S) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGL] → M ⊧ S := by
  obtain ⟨p⟩ := h;
  intro _ M M_finiteGL;
  induction p with
  | axm A => exact validate_gentzen_axm
  | botL => exact validate_gentzen_botL
  | wkL h _ ih => exact validate_gentzen_wkL ih;
  | wkR h _ ih => exact validate_gentzen_wkR ih;
  | impL _ _ ih₁ ih₂ => exact validate_gentzen_impL ih₁ ih₂
  | impR _ ih => exact validate_gentzen_impR ih
  | boxGL _ ih => exact validate_gentzen_boxGL ih

theorem finite_soundness (h : ⊢ᵍ[GL] S) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ S := λ _ _ M [M.IsFiniteGL] => soundness h M

end Kripke

@[simp, grind .]
theorem not_provable_empty : ⊬ᵍ[GL] (∅ ⟹ ∅ : Sequent α) := by
  by_contra h;
  have : (0 : trivial_GL_model.World) ⊩ (∅ ⟹ ∅) := Kripke.finite_soundness h trivial_GL_model 0;
  grind;

end ProvableGentzen


namespace Sequent

variable {S : Sequent α}

structure Saturated (S : Sequent α) where
  impL : ∀ {A B}, A 🡒 B ∈ S.1 → A ∈ S.2 ∨ B ∈ S.1
  impR : ∀ {A B}, A 🡒 B ∈ S.2 → A ∈ S.1 ∧ B ∈ S.2

structure Expanded (BS : Sequent α) (S : Sequent α) extends S.Saturated where
  subset_subfmls : S.1 ∪ S.2 ⊆ BS.subfmls
  unprovable     : ⊬ᵍ[GL] S

end Sequent


structure ExpandedSequent (BS : Sequent α) extends Sequent α where
  saturated         : toSequent.Saturated
  subset_subfmls    : toSequent.1 ∪ toSequent.2 ⊆ BS.subfmls
  unprovable        : ⊬ᵍ[GL] toSequent

namespace ExpandedSequent

attribute [grind .] ExpandedSequent.saturated ExpandedSequent.subset_subfmls ExpandedSequent.unprovable

def widen {BS₀ BS₁ : Sequent α} (S : ExpandedSequent BS₀) (hBS : BS₀ ⊆ BS₁) : ExpandedSequent BS₁ where
  toSequent      := S.toSequent
  saturated      := S.saturated
  unprovable     := S.unprovable
  subset_subfmls := by
    trans BS₀.subfmls;
    . exact S.subset_subfmls;
    . intro A;
      simp [Sequent.subfmls, Finset.mem_union, FormulaFinset.subfmls];
      rintro (⟨B, hB₁, hB₂⟩ | ⟨B, hB₁, hB₂⟩);
      . left;
        use B;
        constructor;
        . exact hBS.1 hB₁;
        . assumption;
      . right;
        use B;
        constructor;
        . exact hBS.2 hB₁;
        . assumption;

variable {BS : Sequent α} {S : ExpandedSequent BS} {A : Formula α}

@[grind .]
lemma not_mem_both : ¬(A ∈ S.1.1 ∧ A ∈ S.1.2) := by
  push Not;
  intro h₁ h₂;
  apply S.unprovable;
  exact ProvableGentzen.union' _ h₁ h₂;
@[grind .] lemma not_mem_bot_ant : ⊥ ∉ S.1.1 := by grind;
@[grind =>] lemma of_mem_imp_ant (h : A 🡒 B ∈ S.1.1 := by grind) : A ∈ S.1.2 ∨ B ∈ S.1.1 := S.saturated.impL h
@[grind =>] lemma of_mem_imp_suc (h : A 🡒 B ∈ S.1.2 := by grind) : A ∈ S.1.1 ∧ B ∈ S.1.2 := S.saturated.impR h

section

variable {BS : Sequent α}

open Classical in
@[grind]
noncomputable def lindenbaum_indexed (BS : Sequent α) (BS_unprovable : ⊬ᵍ[GL] BS) (S₀ : Sequent α) (S₀_unprovable : ⊬ᵍ[GL] S₀) : FormulaList α → { S : Sequent α // ⊬ᵍ[GL] S }
| [] => ⟨S₀, S₀_unprovable⟩
| (A 🡒 B) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ;
  if h : (A 🡒 B) ∈ S.1 then
    if h : ⊬ᵍ[GL] ((S.1) ⟹ (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
    else ⟨((insert B S.1) ⟹ S.2), by
      push Not at h;
      contrapose! hS;
      have := ProvableGentzen.impL h hS;
      rwa [(show insert (A 🡒 B) S.1 = S.1 by grind)] at this;
    ⟩
  else if h : (A 🡒 B) ∈ S.2 then ⟨
    ((insert A S.1) ⟹ (insert B S.2)),
    by
      contrapose! hS;
      have := ProvableGentzen.impR hS;
      rwa [(show insert (A 🡒 B) S.2 = S.2 by grind)] at this;
  ⟩
  else ⟨S, hS⟩
| _ :: Γ => lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ

lemma subset_lindenbaum_indexed {BS_unprovable : ⊬ᵍ[GL] BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀} {Γ : FormulaList α} : S₀ ⊆ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1 := by
  induction Γ with
  | nil =>
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons A Γ ih =>
    match A with
    | .atom a | .box A | .bot => exact ih
    | .imp A B =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2.trans (Finset.subset_insert _ _)⟩
      · exact ⟨ih.1, ih.2⟩;

lemma subfmls_lindenbaum_indexed
  {BS_unprovable : ⊬ᵍ[GL] BS}
  {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀} (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls)
  {Γ : FormulaList α} (hΓ : ∀ C ∈ Γ, C ∈ BS.subfmls) :
  (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1 ∪ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2 ⊆ BS.subfmls := by
  induction Γ with
  | nil => exact S₀sub
  | cons A Γ ih =>
    replace ih := ih (by grind);
    match A with
    | .atom a | .box A | .bot => exact ih
    | (A 🡒 B) =>
      dsimp only [lindenbaum_indexed];
      have : (A 🡒 B) ∈ BS.subfmls := hΓ _ (by simp)
      have : A ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind;
      have : B ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind;
      split_ifs;
      all_goals
      . intro;
        grind;

lemma saturated_lindenbaum_indexed
  {BS_unprovable : ⊬ᵍ[GL] BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀}
  {Γ : FormulaList α} (hΓ : (Γ.map (·.complexity)).SortedLE)
  :
    let S := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ;
    (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.1 → A ∈ S.1.2 ∨ B ∈ S.1.1) ∧
    (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.2 → A ∈ S.1.1 ∧ B ∈ S.1.2)
  := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil => intro _; constructor <;> intro A B hmem _ <;> simp at hmem
  | cons x Γ' ih =>
    intro hΓ
    rw [List.pairwise_cons] at hΓ
    obtain ⟨hhead, htail⟩ := hΓ
    obtain ⟨ihL, ihR⟩ := ih htail
    match x with
    | .atom a | .box C | .bot =>
      constructor
      · intro A B hmem hx
        refine ihL ?_ hx
        rcases List.mem_cons.mp hmem with h | h
        · simp at h
        · exact h
      · intro A B hmem hx
        refine ihR ?_ hx
        rcases List.mem_cons.mp hmem with h | h
        · simp at h
        · exact h
    | .imp C D =>
      have hunp : ⊬ᵍ[GL] (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ').2
      dsimp only [lindenbaum_indexed]
      split_ifs with h1 h2 h3 <;>
        refine ⟨?_, ?_⟩ <;>
        intro A B hmem hx <;>
        simp only [List.mem_cons] at hmem <;>
        grind [ProvableGentzen.union']

lemma lindenbaum_indexed_saturated_impL_of_sorted_complexity
  {BS_unprovable : ⊬ᵍ[GL] BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀}
  {Γ : FormulaList α} (hΓ : (Γ.map (·.complexity)).SortedLE)
  (h₁ : A 🡒 B ∈ Γ) (h₂ : A 🡒 B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1)
  : A ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2 ∨ B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1 :=
  (saturated_lindenbaum_indexed hΓ).1 h₁ h₂

lemma lindenbaum_indexed_saturated_impL
  {BS_unprovable : ⊬ᵍ[GL] BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀}
  {Γ : FormulaList α} (h : A 🡒 B ∈ Γ)
  :
  letI S := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable (Γ.insertionSort (·.complexity ≤ ·.complexity));
  (A 🡒 B ∈ S.1.1) → A ∈ S.1.2 ∨ B ∈ S.1.1 := by
  apply lindenbaum_indexed_saturated_impL_of_sorted_complexity;
  . rw [List.map_insertionSort (f := Formula.complexity) (l := Γ) (r := λ A B => ((A.complexity) ≤ (B.complexity))) (s := (· ≤ ·)) (by grind)];
    exact List.sortedLE_insertionSort (l := Γ.map (·.complexity));
  . apply List.mem_insertionSort _ |>.mpr h;

lemma lindenbaum_indexed_saturated_impR_of_sorted_complexity
  {BS_unprovable : ⊬ᵍ[GL] BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀}
  {Γ : FormulaList α} (hΓ : (Γ.map (·.complexity)).SortedLE)
  (h₁ : A 🡒 B ∈ Γ) (h₂ : A 🡒 B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2)
  : A ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1 ∧ B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2 :=
  (saturated_lindenbaum_indexed hΓ).2 h₁ h₂

lemma lindenbaum_indexed_saturated_impR
  {BS_unprovable : ⊬ᵍ[GL] BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀}
  {Γ : FormulaList α} (h : A 🡒 B ∈ Γ)
  :
  letI S := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable (Γ.insertionSort (·.complexity ≤ ·.complexity));
  (A 🡒 B ∈ S.1.2) → A ∈ S.1.1 ∧ B ∈ S.1.2 := by
  apply lindenbaum_indexed_saturated_impR_of_sorted_complexity;
  . rw [List.map_insertionSort (f := Formula.complexity) (l := Γ) (r := λ A B => ((A.complexity) ≤ (B.complexity))) (s := (· ≤ ·)) (by grind)];
    exact List.sortedLE_insertionSort (l := Γ.map (·.complexity));
  . apply List.mem_insertionSort _ |>.mpr h;

noncomputable def lindenbaum
  {BS : Sequent α} [BS_unprovable : Fact (⊬ᵍ[GL] BS)] (S₀ : Sequent α) (S₀_unprovable : ⊬ᵍ[GL] S₀) (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls) : ExpandedSequent BS :=
  letI S := lindenbaum_indexed BS (Fact.elim inferInstance) S₀ S₀_unprovable $ BS.subfmls.toList.insertionSort (·.complexity ≤ ·.complexity);
  haveI : ∀ C ∈ BS.subfmls.toList.insertionSort (fun A B => A.complexity ≤ B.complexity), C ∈ BS.subfmls := by
    intro _ hB;
    exact Finset.mem_toList.mp $ List.mem_insertionSort _ |>.mp hB;
  {
    toSequent := S.1,
    unprovable := S.2,
    subset_subfmls := subfmls_lindenbaum_indexed ‹_› ‹_›
    saturated := {
      impL := by
        intro A B h;
        apply lindenbaum_indexed_saturated_impL ?_ h;
        exact Finset.mem_toList.mpr $ subfmls_lindenbaum_indexed ‹_› ‹_› $ Finset.mem_union.mpr $ Or.inl h;
      impR := by
        intro A B h;
        apply lindenbaum_indexed_saturated_impR ?_ h;
        exact Finset.mem_toList.mpr $ subfmls_lindenbaum_indexed ‹_› ‹_› $ Finset.mem_union.mpr $ Or.inr h;
    }
  }

lemma subset_lindenbaum {BS : Sequent α} [BS_unprovable : Fact (⊬ᵍ[GL] BS)] {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[GL] S₀} {S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls}
  : S₀ ⊆ (lindenbaum S₀ S₀_unprovable S₀sub).1 := subset_lindenbaum_indexed

end

instance {S : Sequent α} : Subsingleton S.Saturated :=
  ⟨fun a b => by cases a; cases b; rfl⟩

lemma ext {S T : ExpandedSequent BS} (ha : S.toSequent.ant = T.toSequent.ant) (hs : S.toSequent.suc = T.toSequent.suc) : S = T := by
  obtain ⟨⟨ΓS, ΔS⟩, _⟩ := S;
  obtain ⟨⟨ΓT, ΔT⟩, _⟩ := T;
  grind;

instance : Finite (ExpandedSequent BS) := by
  apply Finite.of_injective
    (β := {x : Finset (Formula α) // x ∈ BS.subfmls.powerset} × {x : Finset (Formula α) // x ∈ BS.subfmls.powerset})
    (fun S : ExpandedSequent BS => (⟨S.toSequent.ant, Finset.mem_powerset.mpr
                  (Finset.Subset.trans Finset.subset_union_left S.subset_subfmls)⟩,
               ⟨S.toSequent.suc, Finset.mem_powerset.mpr
                  (Finset.Subset.trans Finset.subset_union_right S.subset_subfmls)⟩))
  intro S T h;
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ext h.1 h.2

instance [Fact (⊬ᵍ[GL] BS)] : Nonempty (ExpandedSequent BS) := ⟨lindenbaum BS (Fact.elim inferInstance) (by grind)⟩

end ExpandedSequent



namespace ProvableGentzen.Kripke

variable {BS : Sequent α} [Fact (⊬ᵍ[GL] BS)]

@[grind]
def countermodelOf (BS : Sequent α) [Fact (⊬ᵍ[GL] BS)] : Model (ExpandedSequent BS) α where
  Val' x a := #a ∈ x.1.1
  Rel' x y :=
    x.1.1.prebox ⊂ y.1.1.prebox ∧
    x.1.1.prebox ⊆ y.1.1

instance : (countermodelOf BS).IsFiniteGL where
  finite := inferInstance
  trans := by grind;
  irrefl := by grind;

variable {x : (countermodelOf BS).World} {A : Formula α}

lemma truthlemma :
  (A ∈ x.1.1 → x ⊩ A) ∧ (A ∈ x.1.2 → ¬x ⊩ A)
  := by
  induction A generalizing x with
  | box A ih =>
    constructor;
    . intro h y Rxy;
      exact ih.1 $ Rxy.2 (by simpa [FormulaFinset.prebox]);
    . intro h;
      apply Model.World.not_forces_box.mpr;
      let y : ExpandedSequent BS := ExpandedSequent.lindenbaum (insert (□A) (x.1.1.prebox ∪ x.1.1.prebox.box) ⟹ {A})
        (by
          have := x.unprovable;
          contrapose! this;
          exact ProvableGentzen.wk (ProvableGentzen.boxGL this)
            (show x.1.1.prebox.box ⊆ x.1.1 by grind)
            (show {□A} ⊆ x.1.2 by grind);
        )
        (by
          intro B;
          simp [FormulaFinset.prebox];
          rintro (rfl | rfl | h | ⟨B, hB, rfl⟩);
          case inl | inr.inr.inr =>
            grind [x.subset_subfmls];
          case inr.inl | inr.inr.inl =>
            apply Sequent.mem_subfmls_subfmls (B := □B);
            . apply x.subset_subfmls;
              grind;
            . grind;
        );
      use y;
      constructor;
      . constructor;
        . apply Set.ssubset_iff_exists.mpr;
          constructor;
          . intro B hB;
            simp [FormulaFinset.prebox];
            apply ExpandedSequent.subset_lindenbaum.1;
            grind;
          . use A;
            constructor;
            . simp [FormulaFinset.prebox];
              apply ExpandedSequent.subset_lindenbaum.1;
              simp;
            . by_contra!;
              apply x.unprovable;
              apply ProvableGentzen.union' A;
        . intro B hB;
          apply ExpandedSequent.subset_lindenbaum.1;
          simp_all [FormulaFinset.prebox];
      . apply ih.2;
        apply ExpandedSequent.subset_lindenbaum.2;
        simp;
  | atom a =>
    constructor
    · intro h; exact h
    · intro h hf; exact ExpandedSequent.not_mem_both ⟨hf, h⟩
  | bot =>
    constructor
    · intro h; exact absurd h ExpandedSequent.not_mem_bot_ant
    · intro _ hf; exact hf
  | imp A B ihA ihB =>
    constructor
    · intro h hsA
      rcases x.saturated.impL h with hA | hB
      · exact absurd hsA (ihA.2 hA)
      · exact ihB.1 hB
    · intro h hf
      obtain ⟨hA, hB⟩ := x.saturated.impR h
      exact (ihB.2 hB) (hf (ihA.1 hA))

lemma truthlemma_ant : A ∈ x.1.1 → x ⊩ A := truthlemma.1
lemma truthlemma_suc : A ∈ x.1.2 → ¬x ⊩ A := truthlemma.2

theorem completeness {S : Sequent α} (h : ∀ {κ : Type v}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ S) : ⊢ᵍ[GL] S := by
  contrapose! h;
  have : Fact (⊬ᵍ[GL] S) := ⟨iff_unprovableGentzen_isEmpty_ProofGentzen.mpr h⟩;
  use (ExpandedSequent S), inferInstance, (countermodelOf S);
  constructor;
  . infer_instance;
  . dsimp [Model.ValidateSequent, Model.World.ForcesSequent];
    push Not;
    use (ExpandedSequent.lindenbaum S (Fact.elim inferInstance) (by grind));
    constructor;
    . intro C hC; exact truthlemma_ant $ ExpandedSequent.subset_lindenbaum.1 hC;
    . intro D hD; exact truthlemma_suc $ ExpandedSequent.subset_lindenbaum.2 hD;

end Kripke

end ProvableGentzen

end LogicGL
