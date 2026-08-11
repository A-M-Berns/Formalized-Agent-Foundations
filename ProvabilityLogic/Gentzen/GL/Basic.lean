module

public import ProvabilityLogic.Formula.Basic

@[expose]
public section

open scoped Formula

variable {α : Type u} [DecidableEq α]

namespace LogicGL

structure Sequent (α : Type u) where
  ant : FormulaFinset α
  suc : FormulaFinset α

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

@[grind]
def subfmls (S : Sequent α) : Finset (Formula α) := S.ant.subfmls ∪ S.suc.subfmls

structure subset (S T : Sequent α) : Prop where
  ant_subset : S.ant ⊆ T.ant
  suc_subset : S.suc ⊆ T.suc

instance : HasSubset (Sequent α) := ⟨subset⟩

variable {S : Sequent α}

@[grind .] lemma subset_self_subfmls : S.ant ∪ S.suc ⊆ S.subfmls := by grind;

@[grind →]
lemma mem_subfmls_subfmls {S : Sequent α} {B C : Formula α} (hB : B ∈ S.subfmls) (hC : C ∈ B.subfmls) : C ∈ S.subfmls := by
  simp only [Sequent.subfmls, Finset.mem_union] at hB ⊢
  grind [FormulaFinset.mem_subfmls_subfmls]

end Sequent


inductive ProofGentzen : Sequent α → Type u
| axm (A) : ProofGentzen ({A} ⟹ {A})
| botL : ProofGentzen ({⊥} ⟹ (∅ : FormulaFinset α))
| wkL  {Γ Γ' Δ}  : ProofGentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : ProofGentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen (Γ ⟹ Δ')
| impL {Γ Δ A B} : ProofGentzen (Γ ⟹ (insert A Δ)) → ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹ (insert B Δ)) → ProofGentzen (Γ ⟹ (insert (A 🡒 B) Δ))
| boxGL {Γ A} : ProofGentzen ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) → ProofGentzen (Γ.box ⟹ {□A})
notation:120 "⊢ᵍ[GL]! " S:121 => ProofGentzen S


namespace ProofGentzen

variable {Γ Δ : FormulaFinset α} {A B C : Formula α}

def union (A) {Γ Δ : FormulaFinset α} (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[GL]! (Γ ⟹ Δ) := wkR $ wkL $ axm A

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[GL]! (Γ ⟹ Δ) := wkR (Δ := ∅) $ wkL botL

def mdpL_mem (A B) (h₁ : A 🡒 B ∈ Γ := by grind) (h₂ : A ∈ Γ := by grind) (h₃ : B ∈ Δ := by grind) : ⊢ᵍ[GL]! (Γ ⟹ Δ) := by
  rw [(show Γ = insert (A 🡒 B) (insert A (Γ \ {A, A 🡒 B})) by grind)];
  apply impL;
  . apply union A;
  . apply union B;


/--
  Invertibility of `impR`. Stated without a membership hypothesis `A 🡒 B ∈ Δ`:
  when `A 🡒 B ∉ Δ` the statement degenerates to weakening.
-/
-- Proved by structural recursion on the proof.
def impRInv (A B : Formula α) {S : Sequent α} : ⊢ᵍ[GL]! S → ⊢ᵍ[GL]! (insert A S.ant ⟹ insert B (S.suc.erase (A 🡒 B)))
  | .axm C =>
    if h : C = A 🡒 B then by
      subst h;
      rw [(show ({A 🡒 B} : FormulaFinset α).erase (A 🡒 B) = ∅ by grind)];
      exact mdpL_mem A B;
    else union C
  | .botL => botL_mem
  | .wkL π h => by
    have ih := impRInv A B π;
    exact wkL ih (by grind);
  | .wkR π h => by
    have ih := impRInv A B π;
    exact wkR ih (by grind);
  | .impL (Γ := Γ) (Δ := Δ) (A := C) (B := D) π₁ π₂ => by
    have ih₁ := impRInv A B π₁;
    have ih₂ := impRInv A B π₂;
    rw [(show insert A (insert (C 🡒 D) Γ) = insert (C 🡒 D) (insert A Γ) by grind)];
    exact impL (wkR ih₁ (by grind)) (wkL ih₂ (by grind));
  | .impR (Γ := Γ) (Δ := Δ) (A := C) (B := D) π => by
    have ih := impRInv A B π;
    if h : C 🡒 D = A 🡒 B then
      exact wkR (wkL ih (by grind)) (by grind)
    else
      rw [(show insert B ((insert (C 🡒 D) Δ).erase (A 🡒 B)) = insert (C 🡒 D) (insert B (Δ.erase (A 🡒 B))) by grind)];
      exact impR (wkR (wkL ih (by grind)) (by grind));
  | .boxGL π => wkR (wkL (boxGL π))

/-- One direction of the deduction theorem. -/
def deductionTheorem (π : ⊢ᵍ[GL]! (insert A Γ ⟹ {B})) : ⊢ᵍ[GL]! (Γ ⟹ {A 🡒 B}) := by
  rw [← insert_empty_eq];
  apply impR;
  rwa [insert_empty_eq];

/-- The converse direction of the deduction theorem. -/
-- Proved via `impRInv`.
def deductionTheoremInv (π : ⊢ᵍ[GL]! (Γ ⟹ {A 🡒 B})) : ⊢ᵍ[GL]! (insert A Γ ⟹ {B}) := by
  have p := impRInv A B π;
  rwa [(show ({A 🡒 B} : FormulaFinset α).erase (A 🡒 B) = ∅ by grind), insert_empty_eq] at p;


def negL : ⊢ᵍ[GL]! (Γ ⟹ (insert A Δ)) → ⊢ᵍ[GL]! ((insert (∼A) Γ) ⟹ Δ) := λ p => impL p (wkR $ wkL botL)

def negR : ⊢ᵍ[GL]! ((insert A Γ) ⟹ Δ) → ⊢ᵍ[GL]! (Γ ⟹ (insert (∼A) Δ)) := λ p => impR $ wkR $ wkL p

def andL : ⊢ᵍ[GL]! ((insert A $ insert B $ Γ) ⟹ Δ) → ⊢ᵍ[GL]! (insert (A ⋏ B) Γ ⟹ Δ) := λ p => by
  apply impL;
  . apply impR;
    apply negR;
    simpa [(show (insert A $ insert B Γ) = (insert B $ insert A Γ) by grind)] using p;
  . exact botL_mem;

def andR : ⊢ᵍ[GL]! (Γ ⟹ insert A Δ) → ⊢ᵍ[GL]! (Γ ⟹ insert B Δ) → ⊢ᵍ[GL]! (Γ ⟹ insert (A ⋏ B) Δ) := λ p q => by
  apply impR;
  apply impL;
  . exact wkR p;
  . exact negL $ wkR q;

def orL : ⊢ᵍ[GL]! (insert A Γ ⟹ Δ) → ⊢ᵍ[GL]! (insert B Γ ⟹ Δ) → ⊢ᵍ[GL]! (insert (A ⋎ B) Γ ⟹ Δ) := λ p q => by
  apply impL;
  . exact negR p;
  . exact q;

def orR : ⊢ᵍ[GL]! (Γ ⟹ (insert A $ insert B Δ)) → ⊢ᵍ[GL]! (Γ ⟹ insert (A ⋎ B) Δ) := λ p => by
  apply impR;
  apply negL;
  simpa;

def implyK : ⊢ᵍ[GL]! (∅ ⟹ {A 🡒 B 🡒 A}) := deductionTheorem $ deductionTheorem $ union A

def implyS : ⊢ᵍ[GL]! (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert A (insert (A 🡒 B) (insert (A 🡒 B 🡒 C) ∅)) = ({A 🡒 B 🡒 C, A 🡒 B, A}) by grind)];
  apply impL;
  . exact impL (union A) (union A);
  . exact impL (impL (union A) (union B)) (union C);

def elimContra : ⊢ᵍ[GL]! (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert B (insert (∼A 🡒 ∼B) ∅) = ({∼A 🡒 ∼B, B}) by grind)];
  exact impL (negR $ union A) (negL $ union B);

def modalK : ⊢ᵍ[GL]! (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert (□A) (insert (□(A 🡒 B)) ∅) = (FormulaFinset.box {A, (A 🡒 B)}) by grind)];
  apply boxGL;
  apply mdpL_mem A B;

def modal4 : ⊢ᵍ[GL]! (∅ ⟹ {(□A 🡒 □□A)}) := by
  apply deductionTheorem;
  rw [(show (insert (□A) ∅) = FormulaFinset.box {A} by grind)];
  apply boxGL;
  apply union (□A);

def modalL : ⊢ᵍ[GL]! (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := by
  apply deductionTheorem;
  rw [(show (insert (□(□A 🡒 A)) ∅) = FormulaFinset.box {□A 🡒 A} by grind)];
  apply boxGL;
  apply mdpL_mem (□A) A;

def nec : ⊢ᵍ[GL]! (∅ ⟹ {A}) → ⊢ᵍ[GL]! (∅ ⟹ {□A}) := λ p => boxGL (Γ := ∅) $ wkL p

/-- Double negation elimination (`Minimal + DNE` primitive). -/
def dne : ⊢ᵍ[GL]! (∅ ⟹ {∼∼A 🡒 A}) := by
  apply deductionTheorem;
  exact negL (negR (axm A));

/-- Left conjunction elimination. -/
def andElimL : ⊢ᵍ[GL]! (∅ ⟹ {(A ⋏ B) 🡒 A}) := by
  apply deductionTheorem;
  apply andL;
  apply union A;

/-- Right conjunction elimination. -/
def andElimR : ⊢ᵍ[GL]! (∅ ⟹ {(A ⋏ B) 🡒 B}) := by
  apply deductionTheorem;
  apply andL;
  apply union B;

/-- Conjunction introduction. -/
def andIntro : ⊢ᵍ[GL]! (∅ ⟹ {A 🡒 B 🡒 (A ⋏ B)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply andR;
  . apply union A;
  . apply union B;

/-- Left disjunction introduction. -/
def orIntroL : ⊢ᵍ[GL]! (∅ ⟹ {A 🡒 (A ⋎ B)}) := by
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply orR;
  apply union A;

/-- Right disjunction introduction. -/
def orIntroR : ⊢ᵍ[GL]! (∅ ⟹ {B 🡒 (A ⋎ B)}) := by
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply orR;
  apply union B;

/-- Disjunction elimination. -/
def orElim : ⊢ᵍ[GL]! (∅ ⟹ {(A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  apply deductionTheorem;
  apply orL;
  . apply mdpL_mem A C;
  . apply mdpL_mem B C;

/-
#eval implyK (A := #0) (B := #1)
#eval implyS (A := #0) (B := #1) (C := #2)
#eval elimContra (A := #0) (B := #1)
#eval modal4 (A := #0)
#eval modalL (A := #0)
-/

end ProofGentzen



abbrev ProvableGentzen (S : Sequent α) : Prop := Nonempty (⊢ᵍ[GL]! S)
notation:120 "⊢ᵍ[GL] " S:121 => ProvableGentzen S

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B C : Formula α}

lemma axm (A : Formula α) : ⊢ᵍ[GL] ({A} ⟹ {A}) := ⟨ProofGentzen.axm A⟩
lemma union (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[GL] (Γ ⟹ Δ) := ⟨ProofGentzen.union A hΓ hΔ⟩
lemma union' (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ[GL] S := union A hΓ hΔ
lemma botL : ⊢ᵍ[GL] ({⊥} ⟹ (∅ : FormulaFinset α)) := ⟨ProofGentzen.botL⟩
@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[GL] (Γ ⟹ Δ) := ⟨ProofGentzen.botL_mem h⟩
@[grind =>] lemma botL_mem' (S : Sequent α) (h : ⊥ ∈ S.ant := by grind) : ⊢ᵍ[GL] S := botL_mem h
lemma wkL (π : ⊢ᵍ[GL] (Γ ⟹ Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ[GL] (Γ' ⟹ Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᵍ[GL] (Γ ⟹ Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ[GL] (Γ ⟹ Δ') := ⟨ProofGentzen.wkR π.some h⟩
lemma wk (π : ⊢ᵍ[GL] (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᵍ[GL] (Γ' ⟹ Δ') := wkR (wkL π hΓ) hΔ
lemma impL (π₁ : ⊢ᵍ[GL] (Γ ⟹ insert A Δ)) (π₂ : ⊢ᵍ[GL] (insert B Γ ⟹ Δ)) : ⊢ᵍ[GL] ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᵍ[GL] ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍ[GL] (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩
lemma boxGL (π : ⊢ᵍ[GL] ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : ⊢ᵍ[GL] (Γ.box ⟹ {□A}) := ⟨ProofGentzen.boxGL π.some⟩

lemma orR (h : ⊢ᵍ[GL] (Γ ⟹ insert A (insert B Δ))) : ⊢ᵍ[GL] (Γ ⟹ insert (A ⋎ B) Δ) :=
  ⟨ProofGentzen.orR h.some⟩
lemma orL (h₁ : ⊢ᵍ[GL] (insert A Γ ⟹ Δ)) (h₂ : ⊢ᵍ[GL] (insert B Γ ⟹ Δ)) : ⊢ᵍ[GL] (insert (A ⋎ B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.orL h₁.some h₂.some⟩
lemma andR (h₁ : ⊢ᵍ[GL] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍ[GL] (Γ ⟹ insert B Δ)) : ⊢ᵍ[GL] (Γ ⟹ insert (A ⋏ B) Δ) :=
  ⟨ProofGentzen.andR h₁.some h₂.some⟩
lemma andL (h : ⊢ᵍ[GL] (insert A (insert B Γ) ⟹ Δ)) : ⊢ᵍ[GL] (insert (A ⋏ B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.andL h.some⟩
lemma negL (h : ⊢ᵍ[GL] (Γ ⟹ insert A Δ)) : ⊢ᵍ[GL] (insert (∼A) Γ ⟹ Δ) :=
  ⟨ProofGentzen.negL h.some⟩
lemma negR (h : ⊢ᵍ[GL] (insert A Γ ⟹ Δ)) : ⊢ᵍ[GL] (Γ ⟹ insert (∼A) Δ) :=
  ⟨ProofGentzen.negR h.some⟩

lemma implyK : ⊢ᵍ[GL] (∅ ⟹ {A 🡒 B 🡒 A}) := ⟨ProofGentzen.implyK⟩
lemma implyS : ⊢ᵍ[GL] (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := ⟨ProofGentzen.implyS⟩
lemma elimContra : ⊢ᵍ[GL] (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := ⟨ProofGentzen.elimContra⟩
lemma modalK  : ⊢ᵍ[GL] (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := ⟨ProofGentzen.modalK⟩
lemma modal4  : ⊢ᵍ[GL] (∅ ⟹ {(□A 🡒 □□A)}) := ⟨ProofGentzen.modal4⟩
lemma modalL  : ⊢ᵍ[GL] (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := ⟨ProofGentzen.modalL⟩
lemma nec : ⊢ᵍ[GL] (∅ ⟹ {A}) → ⊢ᵍ[GL] (∅ ⟹ {□A}) := λ ⟨p⟩ => ⟨ProofGentzen.nec p⟩
lemma dne : ⊢ᵍ[GL] (∅ ⟹ {∼∼A 🡒 A}) := ⟨ProofGentzen.dne⟩
lemma andElimL : ⊢ᵍ[GL] (∅ ⟹ {(A ⋏ B) 🡒 A}) := ⟨ProofGentzen.andElimL⟩
lemma andElimR : ⊢ᵍ[GL] (∅ ⟹ {(A ⋏ B) 🡒 B}) := ⟨ProofGentzen.andElimR⟩
lemma andIntro : ⊢ᵍ[GL] (∅ ⟹ {A 🡒 B 🡒 (A ⋏ B)}) := ⟨ProofGentzen.andIntro⟩
lemma orIntroL : ⊢ᵍ[GL] (∅ ⟹ {A 🡒 (A ⋎ B)}) := ⟨ProofGentzen.orIntroL⟩
lemma orIntroR : ⊢ᵍ[GL] (∅ ⟹ {B 🡒 (A ⋎ B)}) := ⟨ProofGentzen.orIntroR⟩
lemma orElim : ⊢ᵍ[GL] (∅ ⟹ {(A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)}) := ⟨ProofGentzen.orElim⟩

/-- Invertibility of `impR`. -/
lemma impR_inv {S : Sequent α} (h : ⊢ᵍ[GL] S) : ⊢ᵍ[GL] (insert A S.ant ⟹ insert B (S.suc.erase (A 🡒 B))) := ⟨h.some.impRInv A B⟩

/-- Deduction theorem. -/
theorem deduction_theorem : ⊢ᵍ[GL] (insert A Γ ⟹ {B}) ↔ ⊢ᵍ[GL] (Γ ⟹ {A 🡒 B}) :=
  ⟨λ ⟨π⟩ => ⟨π.deductionTheorem⟩, λ ⟨π⟩ => ⟨π.deductionTheoremInv⟩⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent α) → ⊢ᵍ[GL] S → Prop}
  (axm : ∀ A, motive ({A} ⟹ {A}) (ProvableGentzen.axm A))
  (botL : motive ({⊥} ⟹ (∅ : FormulaFinset α)) ProvableGentzen.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍ[GL] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍ[GL] (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᵍ[GL] ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxGL : ∀ {Γ A} (h : ⊢ᵍ[GL] ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) h → motive (Γ.box ⟹ {□A}) (boxGL h)
  )
  : ∀ {S : Sequent α} (h : ⊢ᵍ[GL] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

notation:120 "⊬ᵍ[GL] " S:121 => ¬ ProvableGentzen S

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : Sequent α} : (⊬ᵍ[GL] S) ↔ (IsEmpty (⊢ᵍ[GL]! S)) := by simp [ProvableGentzen];

end ProvableGentzen

end LogicGL

end
