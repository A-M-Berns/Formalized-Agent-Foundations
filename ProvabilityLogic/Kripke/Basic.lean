module

public import ProvabilityLogic.Formula.Substitution
public import ProvabilityLogic.ToFoundation.Vorspiel.Rel.CWF

@[expose]
public section

open scoped Formula FormulaList FormulaFinset

structure Model (κ : Type u) [Nonempty κ] (α : Type v) where
  Rel' : κ → κ → Prop
  Val' : κ → α → Prop

instance [Nonempty κ] : CoeFun (Model κ α) (fun _ => κ → α → Prop) := ⟨Model.Val'⟩

namespace Model

variable [Nonempty κ] {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

abbrev worlds : Set M.World := Set.univ
@[simp] lemma worlds_nonempty : Set.Nonempty M.worlds := by simp;


abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
infixl:60 " ≺ " => Rel

@[grind]
def RelItr : ℕ → (M.World → M.World → Prop)
  |     0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, x ≺ z ∧ RelItr n z y
notation x:45 " ≺^[" n:0 "] " y:46 => RelItr n x y

section

variable {x y : M.World} {n : ℕ}

@[simp, grind .]
lemma relItr_zero : x ≺^[0] x := by rfl;

@[simp, grind =]
lemma relItr_zero_eq : x ≺^[0] y ↔ x = y := by rfl;

@[simp, grind =]
lemma relItr_one : x ≺^[1] y ↔ x ≺ y := by simp [RelItr];

@[simp, grind =>]
lemma relItr_succ : x ≺^[n + 1] y ↔ ∃ z, x ≺ z ∧ z ≺^[n] y := iff_of_eq rfl

@[simp, grind =>]
lemma relItr_succ' : x ≺^[n + 1] y ↔ ∃ z, x ≺^[n] z ∧ z ≺ y := by
  induction n generalizing x y <;> grind;

lemma relItr_comp : x ≺^[n] y → y ≺^[m] z → x ≺^[n + m] z := by
  induction n generalizing x y <;> grind;

lemma relItr_decomp : x ≺^[n + m] z → ∃ y, x ≺^[n] y ∧ y ≺^[m] z := by
  induction n generalizing x z <;> grind;

@[grind =>]
lemma relItr_unwrap_trans [IsTrans _ M.Rel] {n : ℕ+} : x ≺^[n] y → x ≺ y := by
  induction n generalizing x y with
  | one => simp;
  | succ n ih =>
    rintro ⟨z, Rxz, Rzy⟩;
    trans z;
    . exact Rxz;
    . exact ih Rzy;

@[grind! =>]
lemma relItr_unwrap_trans_pos [IsTrans _ M.Rel] (hn : 0 < n) : x ≺^[n] y → x ≺ y := relItr_unwrap_trans (n := ⟨n, hn⟩)

lemma relItr_unwrap_pred_trans [IsTrans _ M.Rel] {n : ℕ+} : x ≺^[n + 1] y → x ≺^[n] y := by
  induction n generalizing x y with
  | one =>
    rintro ⟨z, Rxz, Rzy⟩;
    apply relItr_one.mpr;
    trans z;
    . exact Rxz;
    . exact relItr_one.mp Rzy;
  | succ n ih =>
    rintro ⟨z, Rxz, Rzy⟩;
    apply relItr_succ.mpr;
    use z;
    constructor;
    . exact Rxz;
    . exact ih Rzy;

lemma relItr_unwrap_sub_trans [IsTrans _ M.Rel] {n : ℕ+} {m : ℕ} : x ≺^[n + m] y → x ≺^[n] y := by
  induction m with
  | zero => grind;
  | succ m ih =>
    intro Rxy;
    exact ih $ relItr_unwrap_pred_trans (n := ⟨n + m, by simp⟩) Rxy;

lemma relItr_reduce_trans {n m : ℕ+} [IsTrans _ M.Rel] (h : m ≤ n) : x ≺^[n] y → x ≺^[m] y := by
  wlog h : m < n;
  . grind;
  suffices n = m + (n - m) by
    rw [this];
    apply relItr_unwrap_sub_trans;
  exact PNat.add_sub_of_lt h |>.symm;

lemma relItr_reduce_trans_pos (hn : 0 < n) (hm : 0 < m) [IsTrans _ M.Rel] (h : m ≤ n) : x ≺^[n] y → x ≺^[m] y := by
  simpa using relItr_reduce_trans (n := ⟨n, hn⟩) (m := ⟨m, hm⟩) h;

end

class IsGL (M : Model κ α) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel

class IsFiniteGL (M : Model κ α) extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  [finite : Finite M.World]
instance [M.IsFiniteGL] : Finite M.World := IsFiniteGL.finite

instance [M.IsFiniteGL] : M.IsGL where
  cwf := IsConverseWellFounded.cwf (rel := M.Rel);

instance [M.IsGL] : Std.Irrefl M.Rel := ConverseWellFounded.irrefl

abbrev TerminalOf (X : Set M.World) := { t // t ∈ X ∧ ∀ x ∈ X, ¬(t ≺ x) }

noncomputable def terminalOf [IsConverseWellFounded _ M.Rel] (X : Set M.World) (hX : Set.Nonempty X) : M.TerminalOf X :=
  haveI t := (ConverseWellFounded.iff_has_max (R := M.Rel) |>.mp IsConverseWellFounded.cwf) X hX;
  ⟨t.choose, t.choose_spec⟩

abbrev Terminal := M.TerminalOf Set.univ

noncomputable def terminal [IsConverseWellFounded _ M.Rel] : M.Terminal := M.terminalOf M.worlds (by simp)


end Model




variable [Nonempty κ] {M : Model κ α} {A B : Formula α} {Γ Γ' Δ Δ' : FormulaFinset α}

namespace Model.World

variable {M : Model κ α} {x : M.World} {A B : Formula α} {n : ℕ}

@[grind]
def Forces (x : M.World) : Formula α → Prop
| .atom a    => M x a
| .bot     => False
| .imp A B => Forces x A → Forces x B
| .box A    => ∀ y, x ≺ y → Forces y A
infix:55 " ⊩ " => Forces

abbrev NotForces (x : M.World) (A : Formula α) : Prop := ¬x ⊩ A
infix:55 " ⊮ " => NotForces

@[simp, grind .] lemma forces_top : x ⊩ ⊤ := by grind;
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by grind;
@[grind =] lemma forces_or  : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by grind;
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := by grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y, x ≺ y → y ⊩ A := by grind;
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y, x ≺ y ∧ y ⊩ A := by grind;
@[grind =] lemma forces_boxItr : x ⊩ □^[n]A ↔ ∀ y, x ≺^[n] y → y ⊩ A := by induction n generalizing x <;> grind;
@[grind =] lemma forces_diaItr : x ⊩ ◇^[n]A ↔ ∃ y, x ≺^[n] y ∧ y ⊩ A := by induction n generalizing x <;> grind;
@[grind =] lemma forces_boxdot : x ⊩ ⊡A ↔ x ⊩ A ∧ ∀ y, x ≺ y → y ⊩ A := by grind;

@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := by grind;
@[grind =] lemma not_forces_and : x ⊮ A ⋏ B ↔ x ⊮ A ∨ x ⊮ B := by grind;
@[grind =] lemma not_forces_or  : x ⊮ A ⋎ B ↔ x ⊮ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_neg : x ⊮ ∼A ↔ x ⊩ A := by grind;
@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y, x ≺ y ∧ y ⊮ A := by grind;
@[grind =] lemma not_forces_dia : x ⊮ ◇A ↔ ∀ y, x ≺ y → y ⊮ A := by grind;
@[grind =] lemma not_forces_boxItr : x ⊮ □^[n]A ↔ ∃ y, x ≺^[n] y ∧ y ⊮ A := by induction n generalizing x <;> grind;
@[grind =] lemma not_forces_diaItr : x ⊮ ◇^[n]A ↔ ∀ y, x ≺^[n] y → y ⊮ A := by induction n generalizing x <;> grind;

@[grind]
def ForcesSet (x : M.World) (Γ : FormulaFinset α) : Prop := ∀ A ∈ Γ, x ⊩ A
infix:55 " ⊩ " => ForcesSet

@[grind =]
lemma forces_lconj {Γ : FormulaList α} : x ⊩ ⋀Γ ↔ ∀ A ∈ Γ, x ⊩ A := by
  match Γ with
  | [] | [A] | A :: B :: Γ => simp [FormulaList.conj, forces_and, forces_lconj];

@[grind =]
lemma forces_ldisj {Γ : FormulaList α} : x ⊩ ⋁Γ ↔ ∃ A ∈ Γ, x ⊩ A := by
  match Γ with
  | [] | [A] | A :: B :: Γ => simp [FormulaList.disj, forces_or, forces_ldisj];

@[grind =]
lemma forces_fconj {Γ : FormulaFinset α} : x ⊩ ⋀Γ ↔ ∀ A ∈ Γ, x ⊩ A := by
  simp [FormulaFinset.conj, forces_lconj];

@[grind =]
lemma forces_fdisj {Γ : FormulaFinset α} : x ⊩ ⋁Γ ↔ ∃ A ∈ Γ, x ⊩ A := by
  simp [FormulaFinset.disj, forces_ldisj];

end Model.World



namespace Model

@[grind]
def Validate (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validate

end Model


namespace Model

/-- Model obtained by composing the valuation with a substitution `s` (the frame is unchanged). -/
abbrev substModel (M : Model κ α) (s : Formula.Substitution α α) : Model κ α where
  Rel' := M.Rel'
  Val' x a := Model.World.Forces (M := M) x (s a)

lemma forces_substModel {s : Formula.Substitution α α} {A : Formula α} {x : M.World} :
    x ⊩ A⟦s⟧ ↔ Model.World.Forces (M := M.substModel s) x A := by
  induction A generalizing x with
  | atom a => rw [Formula.subst_atom]; rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [Formula.subst_imp, Model.World.Forces]; rw [ihA, ihB]
  | box A ih =>
    simp only [Formula.subst_box, Model.World.Forces];
    constructor;
    · intro h y hy; exact ih.mp (h y hy);
    · intro h y hy; exact ih.mpr (h y hy);

instance {s : Formula.Substitution α α} [Fintype M.World] : Fintype (M.substModel s).World := ‹Fintype M.World›
instance {s : Formula.Substitution α α} [h : M.IsGL] : (M.substModel s).IsGL where __ := h

end Model


namespace Model

variable {β : Type*}

/-- Forcing only depends on the model through its frame and valuation. -/
lemma forces_congr {M₁ M₂ : Model κ α} (hR : M₁.Rel' = M₂.Rel')
    (hV : ∀ x a, M₁.Val' x a ↔ M₂.Val' x a) {A : Formula α} {x : κ} :
    Model.World.Forces (M := M₁) x A ↔ Model.World.Forces (M := M₂) x A := by
  induction A generalizing x with
  | atom a => exact hV x a
  | bot => exact Iff.rfl
  | imp A B ihA ihB => simp only [Model.World.Forces]; rw [ihA, ihB]
  | box A ih =>
    simp only [Model.World.Forces];
    constructor;
    · intro h y hy;
      have hy' : M₁.Rel' x y := by rw [hR]; exact hy;
      exact ih.mp (h y hy');
    · intro h y hy;
      have hy' : M₂.Rel' x y := by rw [← hR]; exact hy;
      exact ih.mpr (h y hy');

/-- Pulling back the valuation along an atom renaming (frame unchanged). -/
abbrev mapModel (M : Model κ β) (f : α → β) : Model κ α where
  Rel' := M.Rel'
  Val' x a := M.Val' x (f a)

/-- Forcing a renamed formula is forcing in the pulled-back model. -/
lemma forces_map {M : Model κ β} {f : α → β} {A : Formula α} {x : M.World} :
    x ⊩ A.map f ↔ Model.World.Forces (M := M.mapModel f) x A := by
  induction A generalizing x <;> grind [Model.World.Forces]

/-- Extending the atom type of a model by a fresh atom which is false everywhere. -/
abbrev optionExtend (M : Model κ α) : Model κ (Option α) where
  Rel' := M.Rel'
  Val' x a := match a with | some a => M.Val' x a | none => False

instance {M : Model κ α} [h : M.IsFiniteGL] : (M.optionExtend).IsFiniteGL where
  trans := h.trans
  irrefl := h.irrefl
  finite := h.finite

end Model


end
