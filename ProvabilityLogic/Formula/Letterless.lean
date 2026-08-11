module

public import ProvabilityLogic.Formula.Substitution

@[expose]
public section

open scoped Formula FormulaList FormulaFinset

variable {α : Type*}

abbrev LetterlessFormula := Formula Empty

abbrev LetterlessFormulaList := FormulaList Empty

namespace LetterlessFormula

variable {A : LetterlessFormula}

@[grind]
def lift : LetterlessFormula → Formula α
  | .bot => ⊥
  | .imp A B => lift A 🡒 lift B
  | .box A => □(lift A)
instance : Coe LetterlessFormula (Formula α) := ⟨lift⟩

@[simp, grind =] lemma eq_subst_self : A⟦s⟧ = A := by induction A <;> grind;

/-- Substitution acts trivially on lifted letterless formulas. -/
@[simp, grind =]
lemma subst_lift {s : Formula.Substitution α α} : (lift A : Formula α)⟦s⟧ = lift A := by
  induction A <;> grind;

variable {B : LetterlessFormula}

@[simp, grind =] lemma eq_lift_bot : lift (α := α) ⊥ = ⊥ := by grind;
@[simp, grind =] lemma eq_lift_imp : lift (α := α) (A 🡒 B) = lift A 🡒 lift B := by grind;
@[simp, grind =] lemma eq_lift_box : lift (α := α) (□A) = □(lift A) := by grind;
@[simp, grind =] lemma eq_lift_box_bot : lift (α := α) (□⊥) = □⊥ := by grind;
@[simp, grind =] lemma eq_lift_boxItr_bot {n : ℕ} : lift (α := α) (□^[n]⊥) = □^[n]⊥ := by induction n <;> grind;
@[simp, grind =] lemma eq_lift_and : lift (α := α) (A ⋏ B) = (lift A) ⋏ (lift B) := by grind;

@[simp, grind =]
lemma eq_lift_lconj {Γ : LetterlessFormulaList} : lift (α := α) (⋀Γ) = ⋀(Γ.map lift) := by
  match Γ with
  | [] | [A] => grind;
  | A :: B :: Γ => simp [FormulaList.conj, eq_lift_lconj];

end LetterlessFormula


abbrev LetterlessFormulaFinset := FormulaFinset Empty

namespace LetterlessFormulaFinset

def lift [DecidableEq α] : LetterlessFormulaFinset → FormulaFinset α := λ Γ => Γ.image (LetterlessFormula.lift)
instance [DecidableEq α] : Coe LetterlessFormulaFinset (FormulaFinset α) := ⟨lift⟩

end LetterlessFormulaFinset


abbrev LetterlessFormulaSet := FormulaSet Empty

namespace LetterlessFormulaSet

def lift : LetterlessFormulaSet → FormulaSet α := λ Γ => Γ.image (LetterlessFormula.lift)
instance : Coe LetterlessFormulaSet (FormulaSet α) := ⟨lift⟩

@[simp, grind =]
lemma eq_lift_singleton {A : LetterlessFormula} {B : Formula α} : lift (α := α) {A} = {B} ↔ A.lift = B := by simp [lift];

end LetterlessFormulaSet


namespace Formula

def Letterless : Formula α → Prop
  | .atom _ => False
  | .bot => True
  | .imp A B => A.Letterless ∧ B.Letterless
  | .box A => A.Letterless

def toLetterless : (A : Formula α) → (_ : Letterless A) → LetterlessFormula
  | .bot, _ => ⊥
  | .imp A B, ⟨hA, hB⟩ => toLetterless A hA 🡒 toLetterless B hB
  | .box A, hA => □(toLetterless A hA)

@[simp, grind! .]
lemma letterless_boxItr_bot {n} : (□^[n]⊥ : Formula α).Letterless := by
  match n with
  | 0 => simp [Formula.boxItr, Letterless];
  | n + 1 => apply letterless_boxItr_bot (n := n);

@[grind =]
lemma toLetterless_boxItr_bot {n} : (□^[n]⊥ : Formula α).toLetterless (by grind) = (□^[n]⊥ : LetterlessFormula) := by
  match n with
  | 0 => simp [Formula.boxItr, Formula.toLetterless];
  | n + 1 => simp [Formula.boxItr, Formula.toLetterless, toLetterless_boxItr_bot (n := n)];

/-- Projection of `Formula α` to `LetterlessFormula` collapsing all atoms to `⊥`
(the "inverse direction" of `LetterlessFormula.lift`). -/
def projectEmpty : Formula α → LetterlessFormula
  | .atom _ => ⊥
  | .bot       => ⊥
  | .imp A B   => A.projectEmpty 🡒 B.projectEmpty
  | .box A      => □(A.projectEmpty)

@[simp] lemma projectEmpty_lift {B : LetterlessFormula} :
    (LetterlessFormula.lift B : Formula α).projectEmpty = B := by
  induction B with
  | atom a => exact a.elim
  | bot => rfl
  | imp A C ihA ihC =>
    show (LetterlessFormula.lift A : Formula α).projectEmpty 🡒 (LetterlessFormula.lift C : Formula α).projectEmpty = _;
    rw [ihA, ihC]
  | box A ih =>
    show □((LetterlessFormula.lift A : Formula α).projectEmpty) = _;
    rw [ih]

@[simp, grind =]
lemma lift_toLetterless {A : Formula α} (hA : A.Letterless) :
    (LetterlessFormula.lift (A.toLetterless hA) : Formula α) = A := by
  induction A with
  | atom a => exact absurd hA (by simp [Letterless]);
  | bot => rfl
  | imp A C ihA ihC =>
    obtain ⟨hA', hC'⟩ := hA;
    show (LetterlessFormula.lift (A.toLetterless hA') : Formula α) 🡒
      (LetterlessFormula.lift (C.toLetterless hC') : Formula α) = _;
    rw [ihA, ihC]
  | box A ih =>
    show □(LetterlessFormula.lift (A.toLetterless hA) : Formula α) = _;
    rw [ih]

end Formula



end
