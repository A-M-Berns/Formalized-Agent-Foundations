module

public import ProvabilityLogic.Kripke.Basic
public import ProvabilityLogic.Formula.Letterless

@[expose]
public section

variable [Nonempty κ₁] [Nonempty κ₂] [Nonempty κ₃] {α}

namespace Model

section Bisimulation

structure Bisimulation (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) where
  toRel : M₁.World → M₂.World → Prop
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : α} : toRel x₁ x₂ → (M₁.Val x₁ a ↔ M₂.Val x₂ a)
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

infix:80 " ⇄ " => Bisimulation

variable {M₁ : Model κ₁ α} {M₂ : Model κ₂ α}

instance : CoeFun (M₁ ⇄ M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨Bisimulation.toRel⟩

def Bisimulation.symm (bi : M₁ ⇄ M₂) : M₂ ⇄ M₁ where
  toRel x y := bi.toRel y x
  atomic h := (bi.atomic h).symm
  forth := by
    intro x₂ y₂ x₁ hxy h;
    obtain ⟨y₁, hy₁, hxy⟩ := bi.back hxy h;
    exact ⟨y₁, hy₁, hxy⟩;
  back := by
    intro x₂ x₁ y₁ hxy h;
    obtain ⟨y₂, hy₂, hxy⟩ := bi.forth hxy h;
    exact ⟨y₂, hy₂, hxy⟩;

end Bisimulation


section ModalEquivalent

def World.ModalEquivalent {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} (x₁ : M₁.World) (x₂ : M₂.World) : Prop :=
  ∀ {A : Formula α}, x₁ ⊩ A ↔ x₂ ⊩ A
infix:50 " ↭ " => World.ModalEquivalent

variable {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} {x₁ : M₁.World} {x₂ : M₂.World}

lemma World.modal_equivalent_of_bisimilar (Bi : M₁ ⇄ M₂) (bisx : Bi x₁ x₂) : x₁ ↭ x₂ := by
  intro A;
  induction A generalizing x₁ x₂ with
  | atom a => exact Bi.atomic bisx;
  | bot => simp [World.Forces];
  | imp A B ihA ihB =>
    constructor;
    . intro hAB hA;
      exact ihB bisx |>.mp $ hAB $ ihA bisx |>.mpr hA;
    . intro hAB hA;
      exact ihB bisx |>.mpr $ hAB $ ihA bisx |>.mp hA;
  | box A ih =>
    constructor;
    . intro h y₂ Rx₂y₂;
      obtain ⟨y₁, bisy, Rx₁y₁⟩ := Bi.back bisx Rx₂y₂;
      exact ih bisy |>.mp $ h _ Rx₁y₁;
    . intro h y₁ Rx₁y₁;
      obtain ⟨y₂, bisy, Rx₂y₂⟩ := Bi.forth bisx Rx₁y₁;
      exact ih bisy |>.mpr $ h _ Rx₂y₂;

def World.ModalEquivalent.symm (h : x₁ ↭ x₂) : x₂ ↭ x₁ := fun {_} => Iff.symm h

end ModalEquivalent


section PseudoEpimorphism

structure PseudoEpimorphism (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) where
  toFun : M₁.World → M₂.World
  forth {x y : M₁.World} : x ≺ y → toFun x ≺ toFun y
  back {w : M₁.World} {v : M₂.World} : toFun w ≺ v → ∃ u, toFun u = v ∧ w ≺ u
  atomic {w : M₁.World} {a : α} : M₁.Val w a ↔ M₂.Val (toFun w) a

infix:80 " →ₚ " => PseudoEpimorphism

variable [Nonempty κ] {M : Model κ α} {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} {M₃ : Model κ₃ α}

instance : CoeFun (M₁ →ₚ M₂) (λ _ => M₁.World → M₂.World) := ⟨PseudoEpimorphism.toFun⟩

namespace PseudoEpimorphism

protected def id : M →ₚ M where
  toFun := _root_.id
  forth := by simp;
  back := by simp;
  atomic := by simp;

def comp (f : M₁ →ₚ M₂) (g : M₂ →ₚ M₃) : M₁ →ₚ M₃ where
  toFun := g ∘ f
  forth hxy := g.forth $ f.forth hxy
  back := by
    intro x w hxw;
    obtain ⟨y, rfl, hxy⟩ := g.back hxw;
    obtain ⟨u, rfl, hfu⟩ := f.back hxy;
    exact ⟨u, rfl, hfu⟩;
  atomic := f.atomic.trans g.atomic

variable (f : M₁ →ₚ M₂)

lemma forth_iterate {x y : M₁.World} {n : ℕ} : x ≺^[n] y → f x ≺^[n] f y := by
  induction n generalizing x with
  | zero => rintro rfl; rfl;
  | succ n ih =>
    rintro ⟨z, Rxz, Rzy⟩;
    exact ⟨f z, f.forth Rxz, ih Rzy⟩;

lemma back_iterate {w : M₁.World} {v : M₂.World} {n : ℕ} : f w ≺^[n] v → ∃ u, f u = v ∧ w ≺^[n] u := by
  induction n generalizing w with
  | zero => rintro rfl; exact ⟨w, rfl, rfl⟩;
  | succ n ih =>
    rintro ⟨z, Rfwz, Rzv⟩;
    obtain ⟨u, rfl, Rwu⟩ := f.back Rfwz;
    obtain ⟨t, rfl, Rut⟩ := ih Rzv;
    exact ⟨t, rfl, u, Rwu, Rut⟩;

lemma toFun_rel_toFun_iff_of_inj (inj : Function.Injective f.toFun) {x y : M₁.World} :
    f x ≺ f y ↔ x ≺ y := by
  constructor;
  . intro h;
    obtain ⟨z, he, hz⟩ := f.back h;
    exact inj he ▸ hz;
  . exact f.forth;

lemma toFun_relItr_toFun_iff_of_inj (inj : Function.Injective f.toFun) {x y : M₁.World} {n : ℕ} :
    f x ≺^[n] f y ↔ x ≺^[n] y := by
  constructor;
  . intro h;
    obtain ⟨z, he, hz⟩ := f.back_iterate h;
    exact inj he ▸ hz;
  . exact f.forth_iterate;

def bisimulation : M₁ ⇄ M₂ where
  toRel x y := y = f x
  atomic := by rintro x₁ x₂ a rfl; exact f.atomic;
  forth := by
    rintro x₁ y₁ x₂ rfl Rxy;
    exact ⟨f y₁, rfl, f.forth Rxy⟩;
  back := by
    rintro x₁ x₂ y₂ rfl Rxy;
    obtain ⟨u, rfl, Rwu⟩ := f.back Rxy;
    exact ⟨u, rfl, Rwu⟩;

lemma modal_equivalence (w : M₁.World) : w ↭ f w :=
  World.modal_equivalent_of_bisimilar f.bisimulation rfl

end PseudoEpimorphism

lemma validate_of_surjective_pseudoEpimorphism {A : Formula α}
    (f : M₁ →ₚ M₂) (f_surjective : Function.Surjective f.toFun) : M₁ ⊧ A → M₂ ⊧ A := by
  intro h u;
  obtain ⟨x, rfl⟩ := f_surjective u;
  exact f.modal_equivalence x |>.mp $ h x;

end PseudoEpimorphism


section BisimulationUnder

variable [DecidableEq α]

/--
  A bisimulation-under-`P`: a bisimulation that is only required to match the
  valuation on atoms in `P`. Formalizes the notion of "cones `𝒳_a`, `𝒳_y` are
  `p̄`-isomorphic" ("Removal of a redundant cone"): rather than requiring a literal
  frame isomorphism, we ask for bisimilarity-under-`P`, the modally correct and more
  flexible notion that suffices for (and is used directly in) the forcing-preservation
  argument.

  - [Bek90, §4, item 3, Lemma 6, Lemma 8]
-/
structure BisimulationUnder (P : Finset α) (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) where
  toRel : M₁.World → M₂.World → Prop
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : α} : a ∈ P → toRel x₁ x₂ → (M₁.Val x₁ a ↔ M₂.Val x₂ a)
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

@[inherit_doc]
scoped notation:50 M₁ " ⇄[" P "] " M₂ => BisimulationUnder P M₁ M₂

variable {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} {P : Finset α}

instance : CoeFun (M₁ ⇄[P] M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨BisimulationUnder.toRel⟩

def BisimulationUnder.symm (bi : M₁ ⇄[P] M₂) : M₂ ⇄[P] M₁ where
  toRel x y := bi.toRel y x
  atomic h hr := (bi.atomic h hr).symm
  forth := by
    intro x₂ y₂ x₁ hxy h;
    obtain ⟨y₁, hy₁, hxy⟩ := bi.back hxy h;
    exact ⟨y₁, hy₁, hxy⟩;
  back := by
    intro x₂ x₁ y₁ hxy h;
    obtain ⟨y₂, hy₂, hxy⟩ := bi.forth hxy h;
    exact ⟨y₂, hy₂, hxy⟩;

variable {x₁ : M₁.World} {x₂ : M₂.World}

/--
  A bisimulation-under-`P` forces agreement on every formula whose atoms lie in `P`
  (the ω-analogue of `World.modal_equivalent_of_bisimilar`).
-/
lemma World.forces_iff_of_pbisimilar (Bi : M₁ ⇄[P] M₂) (bisx : Bi x₁ x₂) :
    ∀ {A : Formula α}, A.atoms ⊆ P → (x₁ ⊩ A ↔ x₂ ⊩ A) := by
  intro A;
  induction A generalizing x₁ x₂ with
  | atom a => intro hp; exact Bi.atomic (hp (Finset.mem_singleton_self a)) bisx;
  | bot => intro _; simp [World.Forces];
  | imp A B ihA ihB =>
    intro hp;
    simp only [Formula.atoms, Finset.union_subset_iff] at hp;
    constructor;
    . intro hAB hA;
      exact (ihB bisx hp.2).mp $ hAB $ (ihA bisx hp.1).mpr hA;
    . intro hAB hA;
      exact (ihB bisx hp.2).mpr $ hAB $ (ihA bisx hp.1).mp hA;
  | box A ih =>
    intro hp;
    replace hp : A.atoms ⊆ P := by simpa [Formula.atoms] using hp;
    constructor;
    . intro h y₂ Rx₂y₂;
      obtain ⟨y₁, bisy, Rx₁y₁⟩ := Bi.back bisx Rx₂y₂;
      exact (ih bisy hp).mp $ h _ Rx₁y₁;
    . intro h y₁ Rx₁y₁;
      obtain ⟨y₂, bisy, Rx₂y₂⟩ := Bi.forth bisx Rx₁y₁;
      exact (ih bisy hp).mpr $ h _ Rx₂y₂;

end BisimulationUnder


section Generation

structure GeneratedSub (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) extends M₁ →ₚ M₂ where
  monic : Function.Injective toFun

infix:80 " ⥹ " => GeneratedSub

namespace GeneratedSub

variable {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} (g : M₁ ⥹ M₂)

def bisimulation : M₁ ⇄ M₂ := g.toPseudoEpimorphism.bisimulation

lemma modal_equivalence (w : M₁.World) : w ↭ g.toFun w :=
  g.toPseudoEpimorphism.modal_equivalence w

end GeneratedSub

end Generation


section FrameBisimulation

variable {α₁ α₂ : Type*}

/--
  A frame bisimulation between `M₁` and `M₂`: a `Bisimulation`-like relation that only
  needs to respect the accessibility relation (`forth`/`back`) and drops the `atomic`
  condition, so it makes sense across models `M₁ : Model κ₁ α₁`, `M₂ : Model κ₂ α₂` with
  different propositional-variable types `α₁`, `α₂`. It records exactly enough structure
  to preserve forcing of letterless formulas.
-/
structure FrameBisimulation (M₁ : Model κ₁ α₁) (M₂ : Model κ₂ α₂) where
  toRel : M₁.World → M₂.World → Prop
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

infix:80 " ⇄ᶠ " => FrameBisimulation

variable {M₁ : Model κ₁ α₁} {M₂ : Model κ₂ α₂}

instance : CoeFun (M₁ ⇄ᶠ M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨FrameBisimulation.toRel⟩

def FrameBisimulation.symm (bi : M₁ ⇄ᶠ M₂) : M₂ ⇄ᶠ M₁ where
  toRel x y := bi.toRel y x
  forth := by
    intro x₂ y₂ x₁ hxy h;
    obtain ⟨y₁, hy₁, hxy⟩ := bi.back hxy h;
    exact ⟨y₁, hy₁, hxy⟩;
  back := by
    intro x₂ x₁ y₁ hxy h;
    obtain ⟨y₂, hy₂, hxy⟩ := bi.forth hxy h;
    exact ⟨y₂, hy₂, hxy⟩;

variable {x₁ : M₁.World} {x₂ : M₂.World}

lemma FrameBisimulation.forth_iterate (Bi : M₁ ⇄ᶠ M₂) (bisx : Bi x₁ x₂) {y₁ : M₁.World} {n : ℕ} :
  x₁ ≺^[n] y₁ → ∃ y₂, Bi y₁ y₂ ∧ x₂ ≺^[n] y₂ := by
  induction n generalizing x₁ x₂ with
  | zero => rintro rfl; exact ⟨x₂, bisx, rfl⟩;
  | succ n ih =>
    rintro ⟨z₁, Rx₁z₁, Rz₁y₁⟩;
    obtain ⟨z₂, bisz, Rx₂z₂⟩ := Bi.forth bisx Rx₁z₁;
    obtain ⟨y₂, bisy, Rz₂y₂⟩ := ih bisz Rz₁y₁;
    exact ⟨y₂, bisy, z₂, Rx₂z₂, Rz₂y₂⟩;

/--
  A frame bisimulation forces agreement on every letterless formula (the
  atomic-condition-free analogue of `World.modal_equivalent_of_bisimilar`).
-/
lemma World.letterless_modal_equivalent_of_frameBisimilar (Bi : M₁ ⇄ᶠ M₂) (bisx : Bi x₁ x₂) :
  ∀ {B : LetterlessFormula}, x₁ ⊩ (B.lift : Formula α₁) ↔ x₂ ⊩ (B.lift : Formula α₂) := by
  intro B;
  induction B generalizing x₁ x₂ with
  | atom a => exact a.elim;
  | bot => simp;
  | imp A B ihA ihB =>
    constructor;
    . intro hAB hA;
      exact ihB bisx |>.mp $ hAB $ ihA bisx |>.mpr hA;
    . intro hAB hA;
      exact ihB bisx |>.mpr $ hAB $ ihA bisx |>.mp hA;
  | box A ih =>
    constructor;
    . intro h y₂ Rx₂y₂;
      obtain ⟨y₁, bisy, Rx₁y₁⟩ := Bi.back bisx Rx₂y₂;
      exact ih bisy |>.mp $ h _ Rx₁y₁;
    . intro h y₁ Rx₁y₁;
      obtain ⟨y₂, bisy, Rx₂y₂⟩ := Bi.forth bisx Rx₁y₁;
      exact ih bisy |>.mpr $ h _ Rx₂y₂;

end FrameBisimulation


section FramePseudoEpimorphism

variable {α₁ α₂ : Type*}

/--
  A frame pseudo-epimorphism from `M₁` to `M₂`: a `PseudoEpimorphism`-like function that
  only needs to respect the accessibility relation (`forth`/`back`) and drops the
  `atomic` condition, so it makes sense across models `M₁ : Model κ₁ α₁`,
  `M₂ : Model κ₂ α₂` with different propositional-variable types `α₁`, `α₂`.
-/
structure FramePseudoEpimorphism (M₁ : Model κ₁ α₁) (M₂ : Model κ₂ α₂) where
  toFun : M₁.World → M₂.World
  forth {x y : M₁.World} : x ≺ y → toFun x ≺ toFun y
  back {w : M₁.World} {v : M₂.World} : toFun w ≺ v → ∃ u, toFun u = v ∧ w ≺ u

infix:80 " →ᶠ " => FramePseudoEpimorphism

variable {M₁ : Model κ₁ α₁} {M₂ : Model κ₂ α₂}

instance : CoeFun (M₁ →ᶠ M₂) (λ _ => M₁.World → M₂.World) := ⟨FramePseudoEpimorphism.toFun⟩

namespace FramePseudoEpimorphism

variable (f : M₁ →ᶠ M₂)

def bisimulation : M₁ ⇄ᶠ M₂ where
  toRel x y := y = f x
  forth := by
    rintro x₁ y₁ x₂ rfl Rxy;
    exact ⟨f y₁, rfl, f.forth Rxy⟩;
  back := by
    rintro x₁ x₂ y₂ rfl Rxy;
    obtain ⟨u, rfl, Rwu⟩ := f.back Rxy;
    exact ⟨u, rfl, Rwu⟩;

lemma letterless_modal_equivalence (w : M₁.World) {B : LetterlessFormula} :
  w ⊩ (B.lift : Formula α₁) ↔ f w ⊩ (B.lift : Formula α₂) :=
  World.letterless_modal_equivalent_of_frameBisimilar f.bisimulation rfl

end FramePseudoEpimorphism

end FramePseudoEpimorphism


end Model

end
