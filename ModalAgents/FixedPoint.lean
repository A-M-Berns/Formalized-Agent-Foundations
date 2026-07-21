/-
  GL modal fixed-point theorems (Barasz, §4, Thm 4.2 / 4.3).
  These are purely logical results external to the modal agent framework.
  Barasz et al give no proofs; they cite
  Lindström, Per. 1996. “Provability Logic-a Short Introduction.”
  Barasz Thm 4.2 (the de Jongh–Sambin fixed-point theorem) is Lindström Thm 11,
  and Thm 4.3 (uniqueness of the fixed point) is Lindström Thm 12.

  Thm 4.2 (existence) is a standard GL result not yet available in FFL/Foundation;
  it is axiomatized here in single-variable form. Thm 4.3 (uniqueness) is proved
  below from a boxed-equivalence substitution lemma and Löb's rule.

  The substitution congruence below is the GL-level counterpart of §4, Lemma 4.5.
-/

import ModalAgents.ModalAgent

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-- Substitution replacing atom `p` with `ψ`, identity elsewhere. -/
abbrev diag (p : ℕ) (ψ : Formula ℕ) : Substitution ℕ :=
  fun k => if k = p then ψ else .atom k

/-! ## Substitution congruence -/

/-- Pointwise GL-iff-equivalent substitutions yield GL-iff-equivalent
formulas. This is the GL-level counterpart of Barasz §4, Lemma 4.5. -/
theorem subst_congr {σ σ' : Substitution ℕ}
    (h : ∀ a, Modal.GL ⊢ (σ a) 🡘 (σ' a)) (φ : Formula ℕ) :
    Modal.GL ⊢ φ⟦σ⟧ 🡘 φ⟦σ'⟧ := by
  induction φ with
  | hatom a => exact h a
  | hfalsum => exact E!_id
  | himp φ ψ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂
  | hbox φ ih => exact box_iff! ih

/-! ## Theorem 4.2 (Barasz, §4): GL fixed-point existence -/

/-- de Jongh–Sambin–Bernardi fixed-point theorem (Barasz, §4, Thm 4.2),
single-variable form, with the strong form of the existence claim: the
constructed fixed point uses only atoms from the input formula and not
the diagonal variable (standard for the Craig-interpolant / Bernardi
construction, Boolos Ch. 8). -/
axiom glFixedPoint_thm42 {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    ∃ ψ : Formula ℕ,
      (Modal.GL ⊢ ψ 🡘 φ⟦diag p ψ⟧) ∧
      (∀ a, a ∈ ψ.atoms → a ∈ φ.atoms ∧ a ≠ p)

/-- Skolemized fixed-point operator. For non-modalized inputs it returns the
input formula; the spec lemmas only apply when the input is modalized in `p`. -/
noncomputable def glFixedPoint (p : ℕ) (φ : Formula ℕ) : Formula ℕ :=
  haveI := Classical.propDecidable (Modalized p φ)
  if h : Modalized p φ then (glFixedPoint_thm42 h).choose else φ

private lemma glFixedPoint_eq {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    glFixedPoint p φ = (glFixedPoint_thm42 h).choose := by
  show (haveI := Classical.propDecidable (Modalized p φ);
    if h : Modalized p φ then (glFixedPoint_thm42 h).choose else φ) = _
  rw [dif_pos h]

/-- Defining equation for the fixed point (Barasz, §4, Thm 4.2). -/
theorem glFixedPoint_spec {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    Modal.GL ⊢ glFixedPoint p φ 🡘 φ⟦diag p (glFixedPoint p φ)⟧ := by
  rw [glFixedPoint_eq h]
  exact (glFixedPoint_thm42 h).choose_spec.1

/-- Atoms of the fixed point are a subset of the input's atoms minus `p`. -/
lemma glFixedPoint_atoms {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    ∀ a, a ∈ (glFixedPoint p φ).atoms → a ∈ φ.atoms ∧ a ≠ p := by
  rw [glFixedPoint_eq h]
  exact (glFixedPoint_thm42 h).choose_spec.2

/-! ## Substitution identity for absent atoms -/

/-- Substituting for an atom not in the formula leaves the formula unchanged. -/
lemma subst_diag_of_notMem_atoms {p : ℕ} {χ : Formula ℕ} :
    ∀ {ψ : Formula ℕ}, p ∉ ψ.atoms → ψ⟦diag p χ⟧ = ψ
  | .atom a, h => by
    simp only [Formula.atoms, Finset.mem_singleton] at h
    show diag p χ a = .atom a
    simp [diag, Ne.symm h]
  | .falsum, _ => rfl
  | .imp φ ψ, h => by
    simp only [Formula.atoms, Finset.mem_union, not_or] at h
    show φ⟦diag p χ⟧ 🡒 ψ⟦diag p χ⟧ = φ 🡒 ψ
    rw [subst_diag_of_notMem_atoms h.1, subst_diag_of_notMem_atoms h.2]
  | .box φ, h => by
    simp only [Formula.atoms] at h
    show □(φ⟦diag p χ⟧) = □φ
    rw [subst_diag_of_notMem_atoms h]

/-! ## Theorem 4.3 (Barasz, §4): GL fixed-point uniqueness -/

section uniqueness

variable {p : ℕ} {χ χ' : Formula ℕ}

/-- `□φ 🡒 □⊡φ`: `Four` plus box collection. -/
private def boxBoxdotOfBox {φ : Formula ℕ} : Modal.GL ⊢! □φ 🡒 □⊡φ :=
  C_trans (CK_of_C_of_C C_id axiomFour) collect_box_and

/-- Internal box-distribution over `🡘`: `□(φ 🡘 ψ) 🡒 (□φ 🡘 □ψ)`. -/
private def EBoxOfBoxE {φ ψ : Formula ℕ} :
    Modal.GL ⊢! □(φ 🡘 ψ) 🡒 (□φ 🡘 □ψ) :=
  CK_of_C_of_C
    (C_trans (implyBoxDistribute' and₁) axiomK)
    (C_trans (implyBoxDistribute' and₂) axiomK)

/-- A boxdotted equivalence premise reaches every occurrence of the
substituted atom: `⊡(χ 🡘 χ') 🡒 (φ⟦p ↦ χ⟧ 🡘 φ⟦p ↦ χ'⟧)` for arbitrary `φ`. -/
private def substCongrBoxdot : (φ : Formula ℕ) →
    Modal.GL ⊢! ⊡(χ 🡘 χ') 🡒 (φ⟦diag p χ⟧ 🡘 φ⟦diag p χ'⟧)
  | .atom a => by
    by_cases h : a = p
    · subst h
      have e₁ : (Formula.atom a)⟦diag a χ⟧ = χ := by show diag a χ a = χ; simp [diag]
      have e₂ : (Formula.atom a)⟦diag a χ'⟧ = χ' := by show diag a χ' a = χ'; simp [diag]
      rw [e₁, e₂]
      exact and₁
    · have hp : p ∉ (Formula.atom a).atoms := by
        simp only [Formula.atoms, Finset.mem_singleton]
        exact fun e => h e.symm
      rw [subst_diag_of_notMem_atoms hp, subst_diag_of_notMem_atoms hp]
      exact C_of_conseq E_Id
  | .falsum => C_of_conseq E_Id
  | .imp φ ψ =>
    FiniteContext.emptyPrf <| FiniteContext.deduct <|
      ECC_of_E_of_E
        (FiniteContext.of (substCongrBoxdot φ) ⨀ FiniteContext.byAxm₀)
        (FiniteContext.of (substCongrBoxdot ψ) ⨀ FiniteContext.byAxm₀)
  | .box φ =>
    C_trans and₂ (C_trans boxBoxdotOfBox
      (C_trans (implyBoxDistribute' (substCongrBoxdot φ)) EBoxOfBoxE))

/-- For `φ` modalized in `p` the boxed equivalence premise suffices
(Barasz §4, the substitution step of Thm 4.3). -/
private def substCongrBox : ∀ {φ : Formula ℕ}, Modalized p φ →
    Modal.GL ⊢! □(χ 🡘 χ') 🡒 (φ⟦diag p χ⟧ 🡘 φ⟦diag p χ'⟧)
  | .atom a, h => by
    have hp : p ∉ (Formula.atom a).atoms := by
      simp only [Formula.atoms, Finset.mem_singleton]
      exact fun e => h e.symm
    rw [subst_diag_of_notMem_atoms hp, subst_diag_of_notMem_atoms hp]
    exact C_of_conseq E_Id
  | .falsum, _ => C_of_conseq E_Id
  | .imp φ ψ, h =>
    FiniteContext.emptyPrf <| FiniteContext.deduct <|
      ECC_of_E_of_E
        (FiniteContext.of (substCongrBox h.1) ⨀ FiniteContext.byAxm₀)
        (FiniteContext.of (substCongrBox h.2) ⨀ FiniteContext.byAxm₀)
  | .box φ, _ =>
    C_trans boxBoxdotOfBox (C_trans (implyBoxDistribute' (substCongrBoxdot φ)) EBoxOfBoxE)

/-- Any two GL fixed points of a formula modalized in `p` are
GL-equivalent (Barasz, §4, Thm 4.3; Lindström Thm 12). Proved from the
boxed-equivalence substitution lemma and Löb's rule. -/
theorem glFixedPoint_uniqueness {p : ℕ} {φ : Formula ℕ} (hmod : Modalized p φ)
    {ψ ψ' : Formula ℕ}
    (h₁ : Modal.GL ⊢ ψ 🡘 φ⟦diag p ψ⟧)
    (h₂ : Modal.GL ⊢ ψ' 🡘 φ⟦diag p ψ'⟧) :
    Modal.GL ⊢ ψ 🡘 ψ' := by
  obtain ⟨d₁⟩ := h₁
  obtain ⟨d₂⟩ := h₂
  exact ⟨lob_rule <| FiniteContext.emptyPrf <| FiniteContext.deduct <|
    E_trans
      (E_trans (FiniteContext.of d₁)
        (FiniteContext.of (substCongrBox hmod) ⨀ FiniteContext.byAxm₀))
      (E_symm (FiniteContext.of d₂))⟩

end uniqueness
