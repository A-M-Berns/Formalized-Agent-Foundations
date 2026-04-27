/-
  GL modal fixed-point theorems (Barasz, §4, Thm 4.2 / 4.3).
  These are taken as axioms, because these are purely logical results
  that are external to the modal agent framework.

  Instead of proofs, Barasz et al give the following reference for these theorems:
  Lindström, Per. 1996. “Provability Logic-a Short Introduction.”
  Barasz Thm 4.2 (the de Jongh–Sambin fixed-point theorem) is Lindström Thm 11,
  and Thm 4.3 (uniqueness of the fixed point) is Lindström Thm 12. These are standard GL
  results not yet available in FFL/Foundation; axiomatized here in single-variable form.

  The substitution congruence below is the GL-level counterpart of §4, Lemma 4.5.
-/

import Barasz.ModalAgent

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

/-! ## Theorem 4.3 (Barasz, §4): GL fixed-point uniqueness -/

/-- Any two GL fixed points of a formula modalized in `p` are
GL-equivalent (Barasz, §4, Thm 4.3). -/
axiom glFixedPoint_uniqueness {p : ℕ} {φ : Formula ℕ} (_ : Modalized p φ)
    {ψ ψ' : Formula ℕ}
    (h₁ : Modal.GL ⊢ ψ 🡘 φ⟦diag p ψ⟧)
    (h₂ : Modal.GL ⊢ ψ' 🡘 φ⟦diag p ψ'⟧) :
    Modal.GL ⊢ ψ 🡘 ψ'

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
