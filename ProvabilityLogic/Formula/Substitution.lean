module

public import ProvabilityLogic.Formula.Basic

@[expose]
public section

open scoped Formula

variable {α β γ : Type*}

namespace Formula

/-- A substitution of atoms of `α` by formulas over `β`. The target alphabet `β` may differ
from the source alphabet `α`, so that a formula over an arbitrary alphabet `α` (e.g. `ℕ`)
can be turned into a formula over any `β` without `β` needing to carry designated atoms. -/
abbrev Substitution (α β) := α → Formula β

@[grind]
def subst (s : Substitution α β) : Formula α → Formula β
  | atom a  => (s a)
  | ⊥       => ⊥
  | □A      => □(A.subst s)
  | A 🡒 B   => A.subst s 🡒 B.subst s
scoped notation:95 A "⟦" s "⟧" => Formula.subst s A

variable {s : Substitution α β} {A B : Formula α}

lemma subst_atom : (#a)⟦s⟧ = s a := by grind;
lemma subst_bot : (⊥)⟦s⟧ = ⊥ := by grind;
lemma subst_top : (⊤)⟦s⟧ = ⊤ := by grind;
lemma subst_imp : (A 🡒 B)⟦s⟧ = A⟦s⟧ 🡒 B⟦s⟧ := by rfl
lemma subst_and : (A ⋏ B)⟦s⟧ = A⟦s⟧ ⋏ B⟦s⟧ := by grind;
lemma subst_or  : (A ⋎ B)⟦s⟧ = A⟦s⟧ ⋎ B⟦s⟧ := by grind;
lemma subst_neg : (∼A)⟦s⟧ = ∼(A⟦s⟧) := by grind;
lemma subst_iff : (A 🡘 B)⟦s⟧ = A⟦s⟧ 🡘 B⟦s⟧ := by grind;
attribute [simp, grind =]
  subst_atom
  subst_bot
  subst_top
  subst_neg
  subst_and
  subst_or
  subst_imp
  subst_iff
@[simp, grind =] lemma subst_box : (□A)⟦s⟧ = □(A⟦s⟧) := by grind;
@[simp, grind =] lemma subst_boxItr {n : ℕ} : (□^[n]A)⟦s⟧ = □^[n](A⟦s⟧) := by induction n generalizing A <;> grind;
@[simp, grind =] lemma subst_dia : (◇A)⟦s⟧ = ◇(A⟦s⟧) := by grind;
@[simp, grind =] lemma subst_diaItr {n : ℕ} : (◇^[n]A)⟦s⟧ = ◇^[n](A⟦s⟧) := by induction n generalizing A <;> grind;

/-- Renaming of propositional atoms along a function, as the specialization of `subst`
where each atom is replaced by the atom obtained via `f`. Reducible, so that the `subst_*`
simp/grind lemmas apply to `A.map f` without dedicated `map_*` lemmas. -/
@[reducible] def map (f : α → β) : Formula α → Formula β := subst (fun a => #(f a))

end Formula


namespace Formula

variable {s : Substitution α β} {A B : Formula α}

@[simp, grind =]
lemma subst_lconj {Γ : FormulaList α} : (⋀Γ)⟦s⟧ = ⋀(Γ.map (·⟦s⟧)) := by
  match Γ with
  | [] => simp;
  | [A] => simp;
  | A :: B :: Γ => simp [FormulaList.conj, subst_lconj (Γ := B :: Γ)];

variable {f : α → β}

lemma map_map {g : β → γ} : (A.map f).map g = A.map (g ∘ f) := by
  induction A <;> grind

@[simp, grind =]
lemma map_id : A.map id = A := by
  induction A <;> grind

variable [DecidableEq α] [DecidableEq β]

/-- The atoms of a (generally) substituted formula lie among the atoms introduced by
substituting each of the original atoms. -/
lemma atoms_subst_subset : (A⟦s⟧).atoms ⊆ A.atoms.biUnion (fun a => (s a).atoms) := by
  induction A with
  | atom a => simp [atoms];
  | bot => simp [atoms];
  | imp B C ihB ihC =>
    simp only [subst_imp, atoms, Finset.union_subset_iff];
    exact ⟨ihB.trans (Finset.biUnion_subset_biUnion_of_subset_left _ (by grind)),
      ihC.trans (Finset.biUnion_subset_biUnion_of_subset_left _ (by grind))⟩;
  | box B ih => simpa [atoms] using ih;

@[simp]
lemma atoms_map : (A.map f).atoms = A.atoms.image f := by
  induction A with
  | atom a => simp [atoms];
  | bot => simp [atoms];
  | imp B C ihB ihC => simp [atoms, ihB, ihC, Finset.image_union];
  | box B ih => simpa [atoms] using ih;

omit [DecidableEq β] in
/-- A substitution acting as the identity on the atoms of `A` leaves `A` unchanged. -/
lemma subst_eq_self_of_forall_atoms {s : Substitution α α} (h : ∀ a ∈ A.atoms, s a = #a) :
    A⟦s⟧ = A := by
  induction A with
  | atom a => exact h a (by simp [atoms]);
  | bot => rfl;
  | imp A B ihA ihB =>
    rw [subst_imp, ihA (fun a ha => h a (by simp [atoms, ha])),
      ihB (fun a ha => h a (by simp [atoms, ha]))];
  | box A ih =>
    rw [subst_box, ih (fun a ha => h a (by simpa [atoms] using ha))];

end Formula


namespace Formula

section Single

variable [DecidableEq α] {p q : α} {A B C : Formula α}

/-- The substitution replacing the single atom `p` by `B`. -/
def Substitution.single (p : α) (B : Formula α) : Substitution α α := fun a => if a = p then B else #a

scoped notation:95 A "⟦" p " ↦ " B "⟧" => Formula.subst (Formula.Substitution.single p B) A

@[simp, grind =] lemma Substitution.single_self : Substitution.single p B p = B := by
  simp [Substitution.single]

@[simp, grind =] lemma Substitution.single_of_ne (h : a ≠ p) : Substitution.single p B a = #a := by
  simp [Substitution.single, h]

@[simp, grind =] lemma subst_single_atom_self : (#p)⟦p ↦ B⟧ = B := by simp

@[simp, grind =] lemma subst_single_atom_of_ne (h : a ≠ p) : (#a)⟦p ↦ B⟧ = #a := by simp [h]

lemma subst_single_eq_self_of_not_mem_atoms (h : p ∉ A.atoms) : A⟦p ↦ B⟧ = A := by
  induction A <;> grind [atoms]

lemma atoms_subst_single_subset : (A⟦p ↦ B⟧).atoms ⊆ (A.atoms \ {p}) ∪ B.atoms := by
  induction A with
  | atom a =>
    by_cases h : a = p
    . subst h; simp
    . rw [subst_single_atom_of_ne h]
      simp only [atoms, Finset.singleton_subset_iff, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_singleton]
      grind
  | bot => simp [atoms]
  | imp C D ihC ihD =>
    simp only [subst_imp, atoms, Finset.union_subset_iff]
    constructor
    . exact ihC.trans (by intro w; simp; grind)
    . exact ihD.trans (by intro w; simp; grind)
  | box C ih => simpa [atoms] using ih

/-- Substituting a fresh atom `q` for `p` and then `p` for `q` recovers the formula. -/
lemma subst_single_cancel (hq : q ∉ A.atoms) : (A⟦p ↦ #q⟧)⟦q ↦ #p⟧ = A := by
  induction A with
  | atom a =>
    by_cases h : a = p
    . subst h; simp
    . have : a ≠ q := fun e => hq (by simp [atoms, e])
      rw [subst_single_atom_of_ne h, subst_single_atom_of_ne this]
  | bot => simp
  | imp C D ihC ihD =>
    simp only [atoms, Finset.mem_union, not_or] at hq
    simp [ihC hq.1, ihD hq.2]
  | box C ih =>
    simp only [atoms] at hq
    simp [ih hq]

end Single

end Formula
