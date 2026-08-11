module

public import Mathlib.Data.Finset.Preimage

@[expose]
public section

variable {α : Type*}

inductive Formula (α : Type*)
| atom : α → Formula α
| bot  : Formula α
| imp  : Formula α → Formula α → Formula α
| box  : Formula α → Formula α
deriving DecidableEq

open scoped Formula

namespace Formula

variable {A B : Formula α}

prefix:100 "#" => atom
scoped notation:max "⊥" => bot
scoped infixr:85 " 🡒 " => imp
scoped prefix:95 "□" => box

@[match_pattern]
abbrev neg (A : Formula α) : Formula α := A 🡒 ⊥
scoped prefix:90 "∼" => neg

@[match_pattern]
abbrev or (A B : Formula α) : Formula α := ∼A 🡒 B
scoped infixl:83 " ⋎ " => or

@[match_pattern]
abbrev and (A B : Formula α) : Formula α := ∼(A 🡒 ∼B)
scoped infixl:84 " ⋏ " => and

@[match_pattern]
abbrev iff (A B : Formula α) : Formula α := (A 🡒 B) ⋏ (B 🡒 A)
scoped infix:85 " 🡘 " => iff

@[match_pattern]
abbrev top : Formula α := ∼⊥
scoped notation:max "⊤" => top

@[match_pattern]
abbrev dia (A : Formula α) : Formula α := ∼□(∼A)
scoped prefix:95 "◇" => dia

@[grind]
def boxItr (A : Formula α) (n : ℕ) : Formula α := match n with
  | 0 => A
  | n + 1 => □(boxItr A n)
scoped notation:95 "□^[" n "]" A:max => boxItr A n

@[grind =_]
lemma boxItr_one : (□^[1]A) = □A := by grind;

lemma boxItr_comp {n m : ℕ} : (□^[n + m]A) = □^[n](□^[m]A) := by
  induction n generalizing A <;> grind;

@[grind]
def diaItr (A : Formula α) (n : ℕ) : Formula α := match n with
  | 0 => A
  | n + 1 => ◇(diaItr A n)
scoped notation:95 "◇^[" n "]" A:max => diaItr A n

@[grind =_]
lemma diaItr_one : (◇^[1]A) = ◇A := by grind;

lemma diaItr_comp {n m : ℕ} : (◇^[n + m]A) = ◇^[n](◇^[m]A) := by
  induction n generalizing A <;> grind;

end Formula

/-- The formula `□^[n+1]⊥ 🡒 □^[n]⊥`, asserting (informally) that the accessibility relation
has no chain of length `n + 1` from the current point. -/
@[grind]
def TBB (n : ℕ) : Formula α := (□^[(n + 1)]⊥) 🡒 (□^[n]⊥)

namespace Formula

abbrev boxdot (A : Formula α) : Formula α := A ⋏ □A
scoped prefix:95 "⊡" => boxdot

/-- The boxdot translation: replaces `□` with `⊡`. -/
@[grind]
def boxdotTranslate : Formula α → Formula α
  | .atom a => #a
  | .bot => ⊥
  | .imp A B => (boxdotTranslate A) 🡒 (boxdotTranslate B)
  | .box A => ⊡(boxdotTranslate A)
postfix:90 "ᵇ" => Formula.boxdotTranslate

@[grind]
def IsBox : Formula α → Prop
| .box _ => True
| _ => False

instance : DecidablePred (Formula.IsBox (α := α)) := λ A => by
  cases A;
  case box => exact isTrue $ by grind;
  case atom | bot | imp => exact isFalse $ by grind;

/-- Typst math-mode source for this formula, using `curryst`'s `class("unary", ·)` idiom
for the modalities. Always parenthesizes
a `→`, since as a subformula its scope would otherwise be ambiguous; used for every
subformula occurrence. `Formula.toString` (below) is the top-level entry point, which omits
these parentheses around the formula's own outermost `→`, since nothing there needs
disambiguating. -/
protected def toStringAux [ToString α] : Formula α → String
| .atom a    => s!"p_({a})"
| ◇A    => s!"class(\"unary\", diamond) {Formula.toStringAux A}"
| .box A    => s!"class(\"unary\", square) {Formula.toStringAux A}"
| .top     => "⊤"
| .bot     => "⊥"
| ∼A    => s!"not {Formula.toStringAux A}"
| .imp A B => s!"({Formula.toStringAux A} -> {Formula.toStringAux B})"

/-- Typst math-mode source for this formula. See `Formula.toStringAux` for the
parenthesization convention; this entry point omits the outermost parentheses around a
top-level `→`. -/
protected def toString [ToString α] : Formula α → String
| .imp A B => s!"{Formula.toStringAux A} -> {Formula.toStringAux B}"
| A     => Formula.toStringAux A

instance [ToString α] : ToString (Formula α) := ⟨Formula.toString⟩
instance [ToString α] : Repr (Formula α) := ⟨λ A _ => Std.Format.text $ Formula.toString A⟩

variable [DecidableEq α]

@[grind]
def atoms : Formula α → Finset α
| .bot     => ∅
| .atom a    => {a}
| .imp A B => A.atoms ∪ B.atoms
| .box A    => A.atoms

@[simp, grind =]
lemma atoms_and (A B : Formula α) : (A ⋏ B).atoms = A.atoms ∪ B.atoms := by
  simp [Formula.atoms]

@[simp, grind =]
lemma atoms_or (A B : Formula α) : (A ⋎ B).atoms = A.atoms ∪ B.atoms := by
  simp [Formula.atoms]

@[simp, grind =]
lemma atoms_neg (A : Formula α) : (∼A).atoms = A.atoms := by
  simp [Formula.atoms]

@[simp, grind =]
lemma atoms_box (A : Formula α) : (□A).atoms = A.atoms := rfl

@[simp, grind =]
lemma atoms_dia (A : Formula α) : (◇A).atoms = A.atoms := by
  simp [Formula.atoms]

end Formula


abbrev FormulaList (α) := List $ Formula α

namespace FormulaList

@[grind]
protected def conj : FormulaList α → Formula α
| [] => ⊤
| [A] => A
| A :: B :: Γ  => A ⋏ FormulaList.conj (B :: Γ)
scoped prefix:100 "⋀" => FormulaList.conj

@[simp, grind .] lemma conj_nil : FormulaList.conj (α := α) [] = ⊤ := rfl
@[simp, grind .] lemma conj_singleton : FormulaList.conj [A] = A := rfl

@[grind]
protected def disj : FormulaList α → Formula α
| [] => ⊥
| [A] => A
| A :: B :: Γ  => A ⋎ FormulaList.disj (B :: Γ)
scoped prefix:100 "⋁" => FormulaList.disj

@[simp, grind .] lemma disj_nil : FormulaList.disj (α := α) [] = ⊥ := rfl
@[simp, grind .] lemma disj_singleton : FormulaList.disj [A] = A := rfl

end FormulaList


abbrev FormulaFinset (α) := Finset (Formula α)

namespace Formula

variable {A B : Formula α}

@[grind]
def subfmls [DecidableEq α] : Formula α → FormulaFinset α
| .atom a    => {#a}
| .bot     => {⊥}
| .imp A B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)
| .box A    => insert (□A) A.subfmls

@[grind .]
lemma mem_subfmls_self [DecidableEq α] : A ∈ A.subfmls := by cases A <;> grind

@[grind .]
lemma mem_subfmls_imp_left [DecidableEq α] : A ∈ (A 🡒 B).subfmls := by grind

@[grind .]
lemma mem_subfmls_imp_right [DecidableEq α] : B ∈ (A 🡒 B).subfmls := by grind

@[grind .]
lemma mem_subfmls_box [DecidableEq α] : A ∈ (□A).subfmls := by grind

@[grind →]
lemma subfmls_trans [DecidableEq α] : A ∈ B.subfmls → A.subfmls ⊆ B.subfmls := by
  induction B with
  | imp C D ihC ihD => intro h; grind
  | box C ihC => intro h; grind
  | _ => intro h; grind

@[grind]
def complexity : Formula α → ℕ
  | .atom _    => 0
  | .bot     => 0
  | .imp A B => max A.complexity B.complexity + 1
  | .box A    => A.complexity + 1

@[simp, grind .]
lemma complexity_imp_left : A.complexity < (A 🡒 B).complexity := by grind;

@[simp, grind .]
lemma complexity_imp_right : B.complexity < (A 🡒 B).complexity := by grind;

@[simp, grind .]
lemma complexity_box : A.complexity < (□A).complexity := by grind;

@[grind =>]
lemma complexity_le_of_mem_subfmls [DecidableEq α] (h : A ∈ B.subfmls) : A.complexity ≤ B.complexity := by
  induction B <;> grind;

/-- The modal degree of a formula: the maximal nesting depth of `□` (implication does not count). -/
@[grind]
def degree : Formula α → ℕ
  | .atom _    => 0
  | .bot     => 0
  | .imp A B => max A.degree B.degree
  | .box A    => A.degree + 1

@[simp, grind .]
lemma degree_imp_left : A.degree ≤ (A 🡒 B).degree := by grind;

@[simp, grind .]
lemma degree_imp_right : B.degree ≤ (A 🡒 B).degree := by grind;

@[simp, grind .]
lemma degree_box : A.degree < (□A).degree := by grind;

@[grind =>]
lemma degree_le_of_mem_subfmls [DecidableEq α] (h : A ∈ B.subfmls) : A.degree ≤ B.degree := by
  induction B <;> grind;

/-- The atoms of a subformula `B` of `A` are contained in the atoms of `A`. -/
@[grind →]
lemma atoms_subset_of_mem_subfmls [DecidableEq α] (h : B ∈ A.subfmls) : B.atoms ⊆ A.atoms := by
  induction A <;> grind [Formula.subfmls, Formula.atoms]

end Formula


open scoped FormulaList in
private lemma atoms_lconj_subset [DecidableEq α] (L : FormulaList α) :
    (⋀L).atoms ⊆ L.toFinset.biUnion Formula.atoms := by
  match L with
  | [] => simp [FormulaList.conj, Formula.atoms, Formula.top, Formula.neg]
  | [A] => simp
  | A :: B :: L =>
    simp only [FormulaList.conj, Formula.atoms_and]
    have ih := atoms_lconj_subset (B :: L)
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [List.toFinset_cons, Finset.mem_biUnion]
      exact ⟨A, Finset.mem_insert_self _ _, hx⟩
    · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp (ih hx)
      refine Finset.mem_biUnion.mpr ⟨y, ?_, hxy⟩
      simp only [List.toFinset_cons] at hy ⊢
      exact Finset.mem_insert_of_mem hy


open scoped FormulaList in
private lemma atoms_ldisj_subset [DecidableEq α] (L : FormulaList α) :
    (⋁L).atoms ⊆ L.toFinset.biUnion Formula.atoms := by
  match L with
  | [] => simp [FormulaList.disj, Formula.atoms]
  | [A] => simp
  | A :: B :: L =>
    simp only [FormulaList.disj, Formula.atoms_or]
    have ih := atoms_ldisj_subset (B :: L)
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [List.toFinset_cons, Finset.mem_biUnion]
      exact ⟨A, Finset.mem_insert_self _ _, hx⟩
    · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp (ih hx)
      refine Finset.mem_biUnion.mpr ⟨y, ?_, hxy⟩
      simp only [List.toFinset_cons] at hy ⊢
      exact Finset.mem_insert_of_mem hy


namespace FormulaFinset

@[grind]
protected noncomputable def conj : FormulaFinset α → Formula α := FormulaList.conj ∘ Finset.toList
scoped prefix:100 "⋀" => FormulaFinset.conj

@[simp, grind .] lemma conj_empty : FormulaFinset.conj (α := α) ∅ = ⊤ := by simp [FormulaFinset.conj]
@[simp, grind .] lemma conj_singleton : FormulaFinset.conj ({A} : FormulaFinset α) = A := by simp [FormulaFinset.conj]

@[grind]
protected noncomputable def disj : FormulaFinset α → Formula α := FormulaList.disj ∘ Finset.toList
scoped prefix:100 "⋁" => FormulaFinset.disj

@[simp, grind .] lemma disj_empty : FormulaFinset.disj (α := α) ∅ = ⊥ := by simp [FormulaFinset.disj]
@[simp, grind .] lemma disj_singleton : FormulaFinset.disj ({A} : FormulaFinset α) = A := by simp [FormulaFinset.disj]


abbrev box [DecidableEq α] (Γ : FormulaFinset α) : FormulaFinset α := Γ.image (□·)
scoped prefix:95 "□" => FormulaFinset.box

variable [DecidableEq α] {Γ Δ : FormulaFinset α} {A B : Formula α}

@[grind]
def atoms (Γ : FormulaFinset α) : Finset α := Γ.biUnion Formula.atoms

@[grind →]
lemma atoms_mono (h : Γ ⊆ Δ) : Γ.atoms ⊆ Δ.atoms :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

@[grind →]
lemma atoms_subset_of_mem (h : A ∈ Γ) : A.atoms ⊆ Γ.atoms :=
  Finset.subset_biUnion_of_mem _ h

@[simp, grind =]
lemma atoms_insert (A : Formula α) (Γ : FormulaFinset α) : (insert A Γ).atoms = A.atoms ∪ Γ.atoms := by
  simp [FormulaFinset.atoms, Finset.biUnion_insert]

@[simp, grind =]
lemma atoms_empty : (∅ : FormulaFinset α).atoms = ∅ := by simp [FormulaFinset.atoms]

@[simp, grind =]
lemma atoms_singleton (A : Formula α) : ({A} : FormulaFinset α).atoms = A.atoms := by
  simp [FormulaFinset.atoms]

@[simp, grind =]
lemma atoms_union (Γ Δ : FormulaFinset α) : (Γ ∪ Δ).atoms = Γ.atoms ∪ Δ.atoms := by
  ext x
  simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨a, ha | ha, hx⟩
    · exact Or.inl ⟨a, ha, hx⟩
    · exact Or.inr ⟨a, ha, hx⟩
  · rintro (⟨a, ha, hx⟩ | ⟨a, ha, hx⟩)
    · exact ⟨a, Or.inl ha, hx⟩
    · exact ⟨a, Or.inr ha, hx⟩

/-- The atoms of `⋀Γ` are contained in the atoms of `Γ`. -/
@[grind .]
lemma atoms_conj_subset (Γ : FormulaFinset α) : (⋀Γ).atoms ⊆ Γ.atoms := by
  have := atoms_lconj_subset Γ.toList
  simpa [FormulaFinset.conj, FormulaFinset.atoms] using this

/-- The atoms of `⋁Γ` are contained in the atoms of `Γ`. -/
@[grind .]
lemma atoms_disj_subset (Γ : FormulaFinset α) : (⋁Γ).atoms ⊆ Γ.atoms := by
  have := atoms_ldisj_subset Γ.toList
  simpa [FormulaFinset.disj, FormulaFinset.atoms] using this

@[simp, grind =]
lemma box_atoms (Γ : FormulaFinset α) : Γ.box.atoms = Γ.atoms := by
  ext x
  simp only [atoms, FormulaFinset.box, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨B, hB, rfl⟩, hx⟩; exact ⟨B, hB, by simpa [Formula.atoms] using hx⟩
  · rintro ⟨B, hB, hx⟩; exact ⟨□B, ⟨B, hB, rfl⟩, by simpa [Formula.atoms] using hx⟩

lemma box_filter (hS : Γ ⊆ Δ.box) : FormulaFinset.box (Δ.filter (fun B => □B ∈ Γ)) = Γ := by
  ext x
  simp only [FormulaFinset.box, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨B, ⟨_, hBS⟩, rfl⟩; exact hBS
  · intro hx
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp (hS hx)
    exact ⟨B, ⟨hB, hx⟩, rfl⟩

@[grind]
def subfmls (Γ : FormulaFinset α) : Finset (Formula α) := Finset.biUnion Γ Formula.subfmls

@[grind .] lemma subset_self_subfmls : Γ ⊆ Γ.subfmls := by grind;

@[grind →]
lemma mem_subfmls_subfmls {Γ : FormulaFinset α} {B C : Formula α} (hB : B ∈ Γ.subfmls) (hC : C ∈ B.subfmls) : C ∈ Γ.subfmls := by
  simp only [FormulaFinset.subfmls, Finset.mem_biUnion] at hB ⊢
  grind [Formula.subfmls_trans]

lemma subset_subfmls {Γ : FormulaFinset α} : Γ.subfmls ⊆ Δ → Γ.subfmls ⊆ Δ.subfmls := by
  intro h A hA;
  simp [FormulaFinset.subfmls];
  use A;
  constructor;
  . apply h hA;
  . grind;

@[grind]
noncomputable def prebox (Γ : FormulaFinset α) : FormulaFinset α := Γ.preimage (□·) $ by grind [Set.InjOn];

omit [DecidableEq α] in
@[grind =]
lemma iff_mem_prebox_mem : A ∈ Γ.prebox ↔ □A ∈ Γ := by simp [FormulaFinset.prebox];

end FormulaFinset

/-- Instances of the T axiom `□B 🡒 B` built from the subformulas of `A`. -/
noncomputable def Formula.subfmlsS [DecidableEq α] (A : Formula α) : FormulaFinset α :=
  (A.subfmls.prebox).image (λ B => □B 🡒 B)


abbrev FormulaSet (α) := Set (Formula α)


end
