module

public import ProvabilityLogic.Formula.Basic

@[expose]
public section

open scoped Formula

variable {α : Type u} [DecidableEq α]

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
prefix:120 "⊢ᵍ! " => ProofGentzen


namespace ProofGentzen

variable {Γ Δ : FormulaFinset α} {A B C : Formula α}

def union (A) {Γ Δ : FormulaFinset α} (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ! (Γ ⟹ Δ) := wkR $ wkL $ axm A

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ! (Γ ⟹ Δ) := wkR (Δ := ∅) $ wkL botL

def mdpL_mem (A B) (h₁ : A 🡒 B ∈ Γ := by grind) (h₂ : A ∈ Γ := by grind) (h₃ : B ∈ Δ := by grind) : ⊢ᵍ! (Γ ⟹ Δ) := by
  rw [(show Γ = insert (A 🡒 B) (insert A (Γ \ {A, A 🡒 B})) by grind)];
  apply impL;
  . apply union A;
  . apply union B;


/--
  Invertibility of `impR`. Stated without a membership hypothesis `A 🡒 B ∈ Δ`:
  when `A 🡒 B ∉ Δ` the statement degenerates to weakening.
-/
-- Proved by structural recursion on the proof.
def impRInv (A B : Formula α) {S : Sequent α} : ⊢ᵍ! S → ⊢ᵍ! (insert A S.ant ⟹ insert B (S.suc.erase (A 🡒 B)))
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
def deductionTheorem (π : ⊢ᵍ! (insert A Γ ⟹ {B})) : ⊢ᵍ! (Γ ⟹ {A 🡒 B}) := by
  rw [← insert_empty_eq];
  apply impR;
  rwa [insert_empty_eq];

/-- The converse direction of the deduction theorem. -/
-- Proved via `impRInv`.
def deductionTheoremInv (π : ⊢ᵍ! (Γ ⟹ {A 🡒 B})) : ⊢ᵍ! (insert A Γ ⟹ {B}) := by
  have p := impRInv A B π;
  rwa [(show ({A 🡒 B} : FormulaFinset α).erase (A 🡒 B) = ∅ by grind), insert_empty_eq] at p;


def negL : ⊢ᵍ! (Γ ⟹ (insert A Δ)) → ⊢ᵍ! ((insert (∼A) Γ) ⟹ Δ) := λ p => impL p (wkR $ wkL botL)

def negR : ⊢ᵍ! ((insert A Γ) ⟹ Δ) → ⊢ᵍ! (Γ ⟹ (insert (∼A) Δ)) := λ p => impR $ wkR $ wkL p

def andL : ⊢ᵍ! ((insert A $ insert B $ Γ) ⟹ Δ) → ⊢ᵍ! (insert (A ⋏ B) Γ ⟹ Δ) := λ p => by
  apply impL;
  . apply impR;
    apply negR;
    simpa [(show (insert A $ insert B Γ) = (insert B $ insert A Γ) by grind)] using p;
  . exact botL_mem;

def andR : ⊢ᵍ! (Γ ⟹ insert A Δ) → ⊢ᵍ! (Γ ⟹ insert B Δ) → ⊢ᵍ! (Γ ⟹ insert (A ⋏ B) Δ) := λ p q => by
  apply impR;
  apply impL;
  . exact wkR p;
  . exact negL $ wkR q;

def orL : ⊢ᵍ! (insert A Γ ⟹ Δ) → ⊢ᵍ! (insert B Γ ⟹ Δ) → ⊢ᵍ! (insert (A ⋎ B) Γ ⟹ Δ) := λ p q => by
  apply impL;
  . exact negR p;
  . exact q;

def orR : ⊢ᵍ! (Γ ⟹ (insert A $ insert B Δ)) → ⊢ᵍ! (Γ ⟹ insert (A ⋎ B) Δ) := λ p => by
  apply impR;
  apply negL;
  simpa;

def implyK : ⊢ᵍ! (∅ ⟹ {A 🡒 B 🡒 A}) := deductionTheorem $ deductionTheorem $ union A

def implyS : ⊢ᵍ! (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert A (insert (A 🡒 B) (insert (A 🡒 B 🡒 C) ∅)) = ({A 🡒 B 🡒 C, A 🡒 B, A}) by grind)];
  apply impL;
  . exact impL (union A) (union A);
  . exact impL (impL (union A) (union B)) (union C);

def elimContra : ⊢ᵍ! (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert B (insert (∼A 🡒 ∼B) ∅) = ({∼A 🡒 ∼B, B}) by grind)];
  exact impL (negR $ union A) (negL $ union B);

def modalK : ⊢ᵍ! (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert (□A) (insert (□(A 🡒 B)) ∅) = (FormulaFinset.box {A, (A 🡒 B)}) by grind)];
  apply boxGL;
  apply mdpL_mem A B;

def modal4 : ⊢ᵍ! (∅ ⟹ {(□A 🡒 □□A)}) := by
  apply deductionTheorem;
  rw [(show (insert (□A) ∅) = FormulaFinset.box {A} by grind)];
  apply boxGL;
  apply union (□A);

def modalL : ⊢ᵍ! (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := by
  apply deductionTheorem;
  rw [(show (insert (□(□A 🡒 A)) ∅) = FormulaFinset.box {□A 🡒 A} by grind)];
  apply boxGL;
  apply mdpL_mem (□A) A;

def nec : ⊢ᵍ! (∅ ⟹ {A}) → ⊢ᵍ! (∅ ⟹ {□A}) := λ p => boxGL (Γ := ∅) $ wkL p

/-- Double negation elimination (`Minimal + DNE` primitive). -/
def dne : ⊢ᵍ! (∅ ⟹ {∼∼A 🡒 A}) := by
  apply deductionTheorem;
  exact negL (negR (axm A));

/-- Left conjunction elimination. -/
def andElimL : ⊢ᵍ! (∅ ⟹ {(A ⋏ B) 🡒 A}) := by
  apply deductionTheorem;
  apply andL;
  apply union A;

/-- Right conjunction elimination. -/
def andElimR : ⊢ᵍ! (∅ ⟹ {(A ⋏ B) 🡒 B}) := by
  apply deductionTheorem;
  apply andL;
  apply union B;

/-- Conjunction introduction. -/
def andIntro : ⊢ᵍ! (∅ ⟹ {A 🡒 B 🡒 (A ⋏ B)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply andR;
  . apply union A;
  . apply union B;

/-- Left disjunction introduction. -/
def orIntroL : ⊢ᵍ! (∅ ⟹ {A 🡒 (A ⋎ B)}) := by
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply orR;
  apply union A;

/-- Right disjunction introduction. -/
def orIntroR : ⊢ᵍ! (∅ ⟹ {B 🡒 (A ⋎ B)}) := by
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply orR;
  apply union B;

/-- Disjunction elimination. -/
def orElim : ⊢ᵍ! (∅ ⟹ {(A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)}) := by
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



abbrev ProvableGentzen (S : Sequent α) : Prop := Nonempty (⊢ᵍ! S)
prefix:120 "⊢ᵍ " => ProvableGentzen

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B C : Formula α}

lemma axm (A : Formula α) : ⊢ᵍ ({A} ⟹ {A}) := ⟨ProofGentzen.axm A⟩
lemma union (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ (Γ ⟹ Δ) := ⟨ProofGentzen.union A hΓ hΔ⟩
lemma union' (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ S := union A hΓ hΔ
lemma botL : ⊢ᵍ ({⊥} ⟹ (∅ : FormulaFinset α)) := ⟨ProofGentzen.botL⟩
@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ (Γ ⟹ Δ) := ⟨ProofGentzen.botL_mem h⟩
@[grind =>] lemma botL_mem' (S : Sequent α) (h : ⊥ ∈ S.ant := by grind) : ⊢ᵍ S := botL_mem h
lemma wkL (π : ⊢ᵍ (Γ ⟹ Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ (Γ' ⟹ Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᵍ (Γ ⟹ Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ (Γ ⟹ Δ') := ⟨ProofGentzen.wkR π.some h⟩
lemma wk (π : ⊢ᵍ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᵍ (Γ' ⟹ Δ') := wkR (wkL π hΓ) hΔ
lemma impL (π₁ : ⊢ᵍ (Γ ⟹ insert A Δ)) (π₂ : ⊢ᵍ (insert B Γ ⟹ Δ)) : ⊢ᵍ ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᵍ ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍ (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩
lemma boxGL (π : ⊢ᵍ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : ⊢ᵍ (Γ.box ⟹ {□A}) := ⟨ProofGentzen.boxGL π.some⟩

lemma orR (h : ⊢ᵍ (Γ ⟹ insert A (insert B Δ))) : ⊢ᵍ (Γ ⟹ insert (A ⋎ B) Δ) :=
  ⟨ProofGentzen.orR h.some⟩
lemma orL (h₁ : ⊢ᵍ (insert A Γ ⟹ Δ)) (h₂ : ⊢ᵍ (insert B Γ ⟹ Δ)) : ⊢ᵍ (insert (A ⋎ B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.orL h₁.some h₂.some⟩
lemma andR (h₁ : ⊢ᵍ (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍ (Γ ⟹ insert B Δ)) : ⊢ᵍ (Γ ⟹ insert (A ⋏ B) Δ) :=
  ⟨ProofGentzen.andR h₁.some h₂.some⟩
lemma andL (h : ⊢ᵍ (insert A (insert B Γ) ⟹ Δ)) : ⊢ᵍ (insert (A ⋏ B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.andL h.some⟩
lemma negL (h : ⊢ᵍ (Γ ⟹ insert A Δ)) : ⊢ᵍ (insert (∼A) Γ ⟹ Δ) :=
  ⟨ProofGentzen.negL h.some⟩
lemma negR (h : ⊢ᵍ (insert A Γ ⟹ Δ)) : ⊢ᵍ (Γ ⟹ insert (∼A) Δ) :=
  ⟨ProofGentzen.negR h.some⟩

lemma implyK : ⊢ᵍ (∅ ⟹ {A 🡒 B 🡒 A}) := ⟨ProofGentzen.implyK⟩
lemma implyS : ⊢ᵍ (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := ⟨ProofGentzen.implyS⟩
lemma elimContra : ⊢ᵍ (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := ⟨ProofGentzen.elimContra⟩
lemma modalK  : ⊢ᵍ (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := ⟨ProofGentzen.modalK⟩
lemma modal4  : ⊢ᵍ (∅ ⟹ {(□A 🡒 □□A)}) := ⟨ProofGentzen.modal4⟩
lemma modalL  : ⊢ᵍ (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := ⟨ProofGentzen.modalL⟩
lemma nec : ⊢ᵍ (∅ ⟹ {A}) → ⊢ᵍ (∅ ⟹ {□A}) := λ ⟨p⟩ => ⟨ProofGentzen.nec p⟩
lemma dne : ⊢ᵍ (∅ ⟹ {∼∼A 🡒 A}) := ⟨ProofGentzen.dne⟩
lemma andElimL : ⊢ᵍ (∅ ⟹ {(A ⋏ B) 🡒 A}) := ⟨ProofGentzen.andElimL⟩
lemma andElimR : ⊢ᵍ (∅ ⟹ {(A ⋏ B) 🡒 B}) := ⟨ProofGentzen.andElimR⟩
lemma andIntro : ⊢ᵍ (∅ ⟹ {A 🡒 B 🡒 (A ⋏ B)}) := ⟨ProofGentzen.andIntro⟩
lemma orIntroL : ⊢ᵍ (∅ ⟹ {A 🡒 (A ⋎ B)}) := ⟨ProofGentzen.orIntroL⟩
lemma orIntroR : ⊢ᵍ (∅ ⟹ {B 🡒 (A ⋎ B)}) := ⟨ProofGentzen.orIntroR⟩
lemma orElim : ⊢ᵍ (∅ ⟹ {(A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)}) := ⟨ProofGentzen.orElim⟩

/-- Invertibility of `impR`. -/
lemma impR_inv {S : Sequent α} (h : ⊢ᵍ S) : ⊢ᵍ (insert A S.ant ⟹ insert B (S.suc.erase (A 🡒 B))) := ⟨h.some.impRInv A B⟩

/-- Deduction theorem. -/
theorem deduction_theorem : ⊢ᵍ (insert A Γ ⟹ {B}) ↔ ⊢ᵍ (Γ ⟹ {A 🡒 B}) :=
  ⟨λ ⟨π⟩ => ⟨π.deductionTheorem⟩, λ ⟨π⟩ => ⟨π.deductionTheoremInv⟩⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent α) → ⊢ᵍ S → Prop}
  (axm : ∀ A, motive ({A} ⟹ {A}) (ProvableGentzen.axm A))
  (botL : motive ({⊥} ⟹ (∅ : FormulaFinset α)) ProvableGentzen.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍ (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᵍ (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍ (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍ (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᵍ ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxGL : ∀ {Γ A} (h : ⊢ᵍ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) h → motive (Γ.box ⟹ {□A}) (boxGL h)
  )
  : ∀ {S : Sequent α} (h : ⊢ᵍ S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

prefix:120 "⊬ᵍ " => λ S => ¬⊢ᵍ S

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : Sequent α} : (⊬ᵍ S) ↔ (IsEmpty (⊢ᵍ! S)) := by simp [ProvableGentzen];

end ProvableGentzen

end
