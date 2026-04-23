/-
  GL modal fixed-point theorems (Barasz, §4, Thm 4.2 / 4.3 / Lemma 4.5).

  Thm 4.2 (de Jongh–Sambin) and Thm 4.3 (uniqueness) are standard GL
  results (Boolos, *Logic of Provability*, Ch. 8) not yet available in
  FFL/Foundation; axiomatized here in single-variable form. Lemma 4.5
  (substitution congruence) is proved from Foundation's K-congruence.
-/

import Barasz.Agent

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-- Substitution replacing atom `p` with `ψ`, identity elsewhere. -/
abbrev diag (p : ℕ) (ψ : Formula ℕ) : Substitution ℕ :=
  fun k => if k = p then ψ else .atom k

/-! ## Lemma 4.5 (Barasz, §4): substitution congruence -/

/-- Pointwise GL-iff-equivalent substitutions yield GL-iff-equivalent
formulas (Barasz, §4, Lemma 4.5). -/
lemma subst_congr {σ σ' : Substitution ℕ}
    (h : ∀ a, Modal.GL ⊢ (σ a) 🡘 (σ' a)) (φ : Formula ℕ) :
    Modal.GL ⊢ φ⟦σ⟧ 🡘 φ⟦σ'⟧ := by
  induction φ with
  | hatom a => exact h a
  | hfalsum => exact E!_id
  | himp φ ψ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂
  | hbox φ ih => exact box_iff! ih

/-! ## Theorem 4.2 (Barasz, §4): GL fixed-point existence -/

/-- Fixed-point operator for modalized formulas. The returned formula
satisfies `glFixedPoint_spec` when the input is modalized in `p`. -/
axiom glFixedPoint : ℕ → Formula ℕ → Formula ℕ

/-- de Jongh–Sambin–Bernardi fixed-point theorem (Barasz, §4, Thm 4.2),
single-variable form. -/
axiom glFixedPoint_spec {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    Modal.GL ⊢ glFixedPoint p φ 🡘 φ⟦diag p (glFixedPoint p φ)⟧

/-! ## Theorem 4.3 (Barasz, §4): GL fixed-point uniqueness -/

/-- Any two GL fixed points of a formula modalized in `p` are
GL-equivalent (Barasz, §4, Thm 4.3). -/
axiom glFixedPoint_uniqueness {p : ℕ} {φ : Formula ℕ} (_ : Modalized p φ)
    {ψ ψ' : Formula ℕ}
    (h₁ : Modal.GL ⊢ ψ 🡘 φ⟦diag p ψ⟧)
    (h₂ : Modal.GL ⊢ ψ' 🡘 φ⟦diag p ψ'⟧) :
    Modal.GL ⊢ ψ 🡘 ψ'
