/-
  GL modal fixed-point theorems (Barasz, §4, Thm 4.2 / 4.3).
  These are purely logical results external to the modal agent framework.
  Barasz et al give no proofs; they cite
  Lindström, Per. 1996. “Provability Logic-a Short Introduction.”
  Barasz Thm 4.2 (the de Jongh–Sambin fixed-point theorem) is Lindström Thm 11,
  and Thm 4.3 (uniqueness of the fixed point) is Lindström Thm 12.

  Thm 4.2 (existence) is `LogicGL.fixpointTheorem` of the `ProvabilityLogic`
  package — a de Jongh–Sambin construction via Maehara interpolation and Löb's
  rule — restated here in the paper's single-variable form (`glFixedPoint_thm42`).
  Thm 4.3 (uniqueness) is proved below from a boxed-equivalence substitution lemma
  and Löb's rule.

  The substitution congruence below is the GL-level counterpart of §4, Lemma 4.5.
-/

import ModalAgents.ModalAgent
import ProvabilityLogic.Logic.GL.Fixedpoint

open LogicGL Formula

/-- Substitution replacing atom `p` with `ψ`, identity elsewhere (the development's
`Formula.Substitution.single`, so `φ⟦diag p ψ⟧` is its `φ⟦p ↦ ψ⟧`). -/
abbrev diag (p : ℕ) (ψ : Formula ℕ) : Formula.Substitution ℕ ℕ :=
  Formula.Substitution.single p ψ

/-! ## Substitution congruence -/

/-- Pointwise GL-iff-equivalent substitutions yield GL-iff-equivalent
formulas. This is the GL-level counterpart of Barasz §4, Lemma 4.5, and
deliberately carries no paper-node annotation: Lemma 4.5 concludes about
*arithmetic* formulas under `PA`, which this does not state. -/
lemma subst_congr {σ σ' : Formula.Substitution ℕ ℕ}
    (h : ∀ a, ((σ a) 🡘 (σ' a)) ∈ (LogicGL : Logic ℕ)) :
    ∀ φ : Formula ℕ, ((φ⟦σ⟧) 🡘 (φ⟦σ'⟧)) ∈ (LogicGL : Logic ℕ)
  | .atom a => h a
  | .bot => GL.iff_refl
  | .imp φ ψ => GL.imp_congr (subst_congr h φ) (subst_congr h ψ)
  | .box φ => GL.box_iff (subst_congr h φ)

/-- An atom beyond the largest atom of `φ` does not occur in `φ`: the fresh-atom supply
for the fixed-point constructions. -/
lemma notMem_atoms_of_sup_lt {φ : Formula ℕ} {k : ℕ} (h : φ.atoms.sup id < k) :
    k ∉ φ.atoms := fun hk => by
  have := Finset.le_sup (f := id) hk
  simp only [id] at this
  omega

/-! ## Theorem 4.2 (Barasz, §4): GL fixed-point existence -/

/-- de Jongh–Sambin–Bernardi fixed-point theorem (Barasz, §4, Thm 4.2),
single-variable form, with the strong form of the existence claim: the
constructed fixed point uses only atoms from the input formula and not
the diagonal variable (standard for the Craig-interpolant / Bernardi
construction, Boolos Ch. 8). This is `LogicGL.fixpointTheorem` of the `ProvabilityLogic`
package, which constructs the fixed point through Maehara interpolation.

Paper node: Theorem 4.2 (§4). -/
theorem glFixedPoint_thm42 {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    ∃ ψ : Formula ℕ,
      ((ψ 🡘 φ⟦diag p ψ⟧) ∈ (LogicGL : Logic ℕ)) ∧
      (∀ a, a ∈ ψ.atoms → a ∈ φ.atoms ∧ a ≠ p) := by
  -- a fresh atom: larger than every atom of `φ` and than `p`
  set q : ℕ := (φ.atoms.sup id) + p + 1 with hqdef
  have hq : q ∉ φ.atoms := notMem_atoms_of_sup_lt (by omega)
  have hpq : p ≠ q := by omega
  obtain ⟨D, hD_atoms, hD, _⟩ :=
    LogicGL.fixpointTheorem hpq (modalized_iff_modalizedIn.mp h) hq
  refine ⟨D, GL.iff_symm hD, fun a ha => ?_⟩
  have := hD_atoms ha
  rw [Finset.mem_sdiff, Finset.mem_singleton] at this
  exact this

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

/-- Defining equation for the fixed point: the Skolemized operator `glFixedPoint`
satisfies the existence claim of the same node that `glFixedPoint_thm42` states.

Paper node: Theorem 4.2 (§4). -/
theorem glFixedPoint_spec {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    (glFixedPoint p φ 🡘 φ⟦diag p (glFixedPoint p φ)⟧) ∈ (LogicGL : Logic ℕ) := by
  rw [glFixedPoint_eq h]
  exact (glFixedPoint_thm42 h).choose_spec.1

/-- Atoms of the fixed point are a subset of the input's atoms minus `p`. -/
lemma glFixedPoint_atoms {p : ℕ} {φ : Formula ℕ} (h : Modalized p φ) :
    ∀ a, a ∈ (glFixedPoint p φ).atoms → a ∈ φ.atoms ∧ a ≠ p := by
  rw [glFixedPoint_eq h]
  exact (glFixedPoint_thm42 h).choose_spec.2

/-! ## Substitution identity for absent atoms -/

/-- Substituting for an atom not in the formula leaves the formula unchanged. -/
lemma subst_diag_of_notMem_atoms {p : ℕ} {χ : Formula ℕ} {ψ : Formula ℕ}
    (h : p ∉ ψ.atoms) : ψ⟦diag p χ⟧ = ψ :=
  Formula.subst_single_eq_self_of_not_mem_atoms h

/-! ## Theorem 4.3 (Barasz, §4): GL fixed-point uniqueness -/

section uniqueness

variable {p : ℕ} {χ χ' : Formula ℕ}

/-- `□φ 🡒 □⊡φ`: `Four` plus box collection. -/
private lemma boxBoxdotOfBox {φ : Formula ℕ} :
    (□φ 🡒 □⊡φ) ∈ (LogicGL : Logic ℕ) :=
  GL.imp_trans (GL.and_intro_imp GL.imp_id GL.axiomFour) GL.collect_box_and

/-- Internal box-distribution over `🡘`: `□(φ 🡘 ψ) 🡒 (□φ 🡘 □ψ)`. -/
private lemma EBoxOfBoxE {φ ψ : Formula ℕ} :
    (□(φ 🡘 ψ) 🡒 (□φ 🡘 □ψ)) ∈ (LogicGL : Logic ℕ) :=
  GL.and_intro_imp
    (GL.imp_trans (GL.box_imp GL.and_left) GL.axiomK)
    (GL.imp_trans (GL.box_imp GL.and_right) GL.axiomK)

/-- A boxdotted equivalence premise reaches every occurrence of the
substituted atom: `⊡(χ 🡘 χ') 🡒 (φ⟦p ↦ χ⟧ 🡘 φ⟦p ↦ χ'⟧)` for arbitrary `φ`. -/
private lemma substCongrBoxdot : (φ : Formula ℕ) →
    (⊡(χ 🡘 χ') 🡒 (φ⟦diag p χ⟧ 🡘 φ⟦diag p χ'⟧)) ∈ (LogicGL : Logic ℕ)
  | .atom a => by
    by_cases h : a = p
    · subst h
      have e₁ : (Formula.atom a)⟦diag a χ⟧ = χ := by
        show diag a χ a = χ; simp [diag, Formula.Substitution.single]
      have e₂ : (Formula.atom a)⟦diag a χ'⟧ = χ' := by
        show diag a χ' a = χ'; simp [diag, Formula.Substitution.single]
      rw [e₁, e₂]
      exact GL.and_left
    · have hp : p ∉ (Formula.atom a).atoms := by
        simp only [Formula.atoms, Finset.mem_singleton]
        exact fun e => h e.symm
      rw [subst_diag_of_notMem_atoms hp, subst_diag_of_notMem_atoms hp]
      exact GL.imp_of_mem GL.iff_refl
  | .bot => GL.imp_of_mem GL.iff_refl
  | .imp φ ψ =>
    GL.imp_congr_under (substCongrBoxdot φ) (substCongrBoxdot ψ)
  | .box φ =>
    GL.imp_trans GL.and_right (GL.imp_trans boxBoxdotOfBox
      (GL.imp_trans (GL.box_imp (substCongrBoxdot φ)) EBoxOfBoxE))

/-- For `φ` modalized in `p` the boxed equivalence premise suffices
(Barasz §4, the substitution step of Thm 4.3). -/
private lemma substCongrBox : ∀ {φ : Formula ℕ}, Modalized p φ →
    (□(χ 🡘 χ') 🡒 (φ⟦diag p χ⟧ 🡘 φ⟦diag p χ'⟧)) ∈ (LogicGL : Logic ℕ)
  | .atom a, h => by
    have hp : p ∉ (Formula.atom a).atoms := by
      simp only [Formula.atoms, Finset.mem_singleton]
      exact fun e => h e.symm
    rw [subst_diag_of_notMem_atoms hp, subst_diag_of_notMem_atoms hp]
    exact GL.imp_of_mem GL.iff_refl
  | .bot, _ => GL.imp_of_mem GL.iff_refl
  | .imp φ ψ, h =>
    GL.imp_congr_under (substCongrBox h.1) (substCongrBox h.2)
  | .box φ, _ =>
    GL.imp_trans boxBoxdotOfBox (GL.imp_trans (GL.box_imp (substCongrBoxdot φ)) EBoxOfBoxE)

/-- **Uniqueness of modal fixed points** (Lindström Thm 12), in the paper's printed
*internal* form: the two fixed-point equations are hypotheses **inside** `GL`, under
`⊡`, and the conclusion is the implication.  The paper writes its two fixed points as
propositional variables `p`, `p'`; since `GL` is closed under substitution the
statement for arbitrary `χ`, `χ'` is equivalent, and it is the form the corollaries
consume.

Proved by Löb's rule: `⊡`-premises are self-boxing (`H 🡒 □H`), which is exactly what
lets the Löb step discharge them.

Paper node: Theorem 4.3 (§4). -/
theorem glFixedPoint_uniqueness_internal {p : ℕ} {φ : Formula ℕ}
    (hmod : Modalized p φ) (χ χ' : Formula ℕ) :
    ((⊡(χ 🡘 φ⟦diag p χ⟧) ⋏ ⊡(χ' 🡘 φ⟦diag p χ'⟧)) 🡒 (χ 🡘 χ')) ∈ (LogicGL : Logic ℕ) := by
  set X := χ 🡘 φ⟦diag p χ⟧ with hX
  set X' := χ' 🡘 φ⟦diag p χ'⟧ with hX'
  set H := ⊡X ⋏ ⊡X' with hH
  set A := χ 🡘 χ' with hA
  -- `H 🡒 □H`: each `⊡`-conjunct is self-boxing through `boxBoxdotOfBox`
  have selfBox : (H 🡒 □H) ∈ (LogicGL : Logic ℕ) :=
    GL.imp_trans
      (GL.and_intro_imp (GL.imp_trans GL.and_left (GL.imp_trans GL.and_right boxBoxdotOfBox))
                        (GL.imp_trans GL.and_right (GL.imp_trans GL.and_right boxBoxdotOfBox)))
      GL.collect_box_and
  -- `□A 🡒 (H 🡒 A)`: under `H`, `χ 🡘 φ⟦χ⟧ 🡘 φ⟦χ'⟧ 🡘 χ'`, the middle step from `□A`
  have step : (□A 🡒 (H 🡒 A)) ∈ (LogicGL : Logic ℕ) := by
    -- as a two-hypothesis derivation: `{□A, H} ⊢ A`
    apply GL.of_provable
    apply DeducibleHilbert.iff_singleton_deducible_provable.mp
    apply DeducibleHilbert.deduction_theorem.mp
    have hbox : {H, □A} ⊢ʰ[GL] □A := DeducibleHilbert.ofContext (by grind)
    have hH : {H, □A} ⊢ʰ[GL] H := DeducibleHilbert.ofContext (by grind)
    have h₁ : {H, □A} ⊢ʰ[GL] X :=
      DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL)
        (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL) hH)
    have h₂ : {H, □A} ⊢ʰ[GL] X' :=
      DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL)
        (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimR) hH)
    have hmid : {H, □A} ⊢ʰ[GL] φ⟦diag p χ⟧ 🡘 φ⟦diag p χ'⟧ :=
      DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (GL.provable (substCongrBox hmod))) hbox
    -- chain the three equivalences
    have t₁ : {H, □A} ⊢ʰ[GL] χ 🡘 φ⟦diag p χ'⟧ :=
      DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (GL.provable GL.iff_trans_provable)) h₁) hmid
    exact DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (GL.provable GL.iff_trans_provable)) t₁)
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (GL.provable GL.iff_symm_provable)) h₂)
  -- Löb: `□(H 🡒 A) 🡒 (H 🡒 A)`
  apply lob_rule
  -- `{□(H 🡒 A), H} ⊢ A`: from `H` get `□H`, hence `□A` by K, hence `A` by `step`
  apply GL.of_provable
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hH : {H, □(H 🡒 A)} ⊢ʰ[GL] H := DeducibleHilbert.ofContext (by grind)
  have hbHA : {H, □(H 🡒 A)} ⊢ʰ[GL] □(H 🡒 A) := DeducibleHilbert.ofContext (by grind)
  have hbH : {H, □(H 🡒 A)} ⊢ʰ[GL] □H :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (GL.provable selfBox)) hH
  have hbA : {H, □(H 🡒 A)} ⊢ʰ[GL] □A :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.modalK) hbHA) hbH
  exact DeducibleHilbert.mdp
    (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (GL.provable step)) hbA) hH

/-- Any two GL fixed points of a formula modalized in `p` are GL-equivalent — the rule
form of `glFixedPoint_uniqueness_internal`, obtained from it by necessitation.  This is
the form the modal-agent development uses; the paper's printed Theorem 4.3 is the
internal one. -/
lemma glFixedPoint_uniqueness {p : ℕ} {φ : Formula ℕ} (hmod : Modalized p φ)
    {ψ ψ' : Formula ℕ}
    (h₁ : (ψ 🡘 φ⟦diag p ψ⟧) ∈ (LogicGL : Logic ℕ))
    (h₂ : (ψ' 🡘 φ⟦diag p ψ'⟧) ∈ (LogicGL : Logic ℕ)) :
    (ψ 🡘 ψ') ∈ (LogicGL : Logic ℕ) :=
  GL.mdp (glFixedPoint_uniqueness_internal hmod ψ ψ')
    (GL.and_intro (GL.and_intro h₁ (GL.nec h₁)) (GL.and_intro h₂ (GL.nec h₂)))

end uniqueness
