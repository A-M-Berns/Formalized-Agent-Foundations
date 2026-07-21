/-
  GL modal fixed-point theorems (Barasz, §4, Thm 4.2 / 4.3).
  These are purely logical results external to the modal agent framework.
  Barasz et al give no proofs; they cite
  Lindström, Per. 1996. “Provability Logic-a Short Introduction.”
  Barasz Thm 4.2 (the de Jongh–Sambin fixed-point theorem) is Lindström Thm 11,
  and Thm 4.3 (uniqueness of the fixed point) is Lindström Thm 12.

  Thm 4.2 (existence) is a standard GL result not available in FFL/Foundation.
  It is proved below (`glFixedPoint_thm42`) through the autoformalized
  `ProvabilityLogic/` sequent-calculus development (Harmonic Aristotle; see the
  `GlFixedPointBridge` section and the README): a de Jongh–Sambin construction via
  Maehara interpolation and Löb's rule, transported back to Foundation's `Modal.GL`
  through finite Kripke completeness. Like the Brouwer construction it is kernel-gated;
  its `ProvabilityLogic/` interior has not had a human line-by-line read-through.
  `ProvabilityLogic`'s `Formula`-level notations are `scoped`, so they do not collide
  with Foundation's modal notation here; the bridge writes that development's operations
  as explicit function calls.
  Thm 4.3 (uniqueness) is proved below from a boxed-equivalence substitution lemma
  and Löb's rule.

  The substitution congruence below is the GL-level counterpart of §4, Lemma 4.5.
-/

import ModalAgents.ModalAgent
import ProvabilityLogic.Logic.GL.Fixedpoint
import Foundation.Modal.Kripke.Logic.GL.Unnecessitation

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-- Substitution replacing atom `p` with `ψ`, identity elsewhere. -/
abbrev diag (p : ℕ) (ψ : Modal.Formula ℕ) : Modal.Substitution ℕ :=
  fun k => if k = p then ψ else .atom k

/-! ## Substitution congruence -/

/-- Pointwise GL-iff-equivalent substitutions yield GL-iff-equivalent
formulas. This is the GL-level counterpart of Barasz §4, Lemma 4.5. -/
theorem subst_congr {σ σ' : Modal.Substitution ℕ}
    (h : ∀ a, Modal.GL ⊢ (σ a) 🡘 (σ' a)) (φ : Modal.Formula ℕ) :
    Modal.GL ⊢ φ⟦σ⟧ 🡘 φ⟦σ'⟧ := by
  induction φ with
  | hatom a => exact h a
  | hfalsum => exact E!_id
  | himp φ ψ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂
  | hbox φ ih => exact box_iff! ih

/-! ## Theorem 4.2 (Barasz, §4): GL fixed-point existence

Proved via the autoformalized `ProvabilityLogic/` sequent calculus. The
`GlFixedPointBridge` namespace translates between Foundation's `Modal.Formula`
and that development's `_root_.Formula`, carries `Modalized`/`diag`/atoms across the
translation, and transports GL-provability back through finite Kripke completeness.
`Modalized` and `diag` are the repository's own (`ModalAgents.ModalAgent`, and above).
That development's `Formula` operations are written as explicit function calls
(`_root_.Formula.imp`/`.iff`/`.subst`) because its notations are `scoped` and left
unopened here to avoid colliding with Foundation's. -/

namespace GlFixedPointBridge

/-- Translation from Foundation's modal formulas to the sequent-calculus development. -/
def toSeq : Modal.Formula ℕ → _root_.Formula ℕ
  | .atom a => .atom a
  | .falsum => .bot
  | .imp A B => .imp (toSeq A) (toSeq B)
  | .box A => .box (toSeq A)

/-- Translation back to Foundation's modal formulas. -/
def ofSeq : _root_.Formula ℕ → Modal.Formula ℕ
  | .atom a => .atom a
  | .bot => .falsum
  | .imp A B => .imp (ofSeq A) (ofSeq B)
  | .box A => .box (ofSeq A)

@[simp] lemma ofSeq_toSeq (A : Modal.Formula ℕ) : ofSeq (toSeq A) = A := by
  induction A <;> simp_all [toSeq, ofSeq, LO.Modal.Formula.falsum_eq,
    LO.Modal.Formula.imp_eq, LO.Modal.Formula.box_eq]

@[simp] lemma toSeq_ofSeq (A : _root_.Formula ℕ) : toSeq (ofSeq A) = A := by
  induction A <;> simp [toSeq, ofSeq, *]

lemma modalized_iff {p : ℕ} {A : Modal.Formula ℕ} :
    Modalized p A ↔ (toSeq A).ModalizedIn p := by
  induction A <;> simp_all [Modalized, toSeq, _root_.Formula.ModalizedIn]

lemma atoms_toSeq (A : Modal.Formula ℕ) :
    (toSeq A).atoms = A.atoms := by
  induction A <;> simp_all [toSeq, _root_.Formula.atoms, LO.Modal.Formula.atoms]

lemma atoms_ofSeq (A : _root_.Formula ℕ) :
    (ofSeq A).atoms = A.atoms := by
  induction A <;> simp_all [ofSeq, _root_.Formula.atoms, LO.Modal.Formula.atoms]

lemma toSeq_diag (p : ℕ) (A B : Modal.Formula ℕ) :
    toSeq (A⟦diag p B⟧) =
      _root_.Formula.subst (_root_.Formula.Substitution.single p (toSeq B)) (toSeq A) := by
  induction A with
  | hatom a => by_cases ha : a = p <;> simp [diag, toSeq,
      _root_.Formula.Substitution.single, ha]
  | hfalsum => rfl
  | himp A C ihA ihC => simp [LO.Modal.Formula.subst, toSeq, ihA, ihC]
  | hbox A ih => simp [LO.Modal.Formula.subst, toSeq, ih]

private lemma forces_translation {M : LO.Modal.Kripke.Model} (x : M.World)
    (A : Modal.Formula ℕ) :
    let N : _root_.Model M.World ℕ := ⟨M.Rel, fun w a => M.Val a w⟩
    _root_.Model.World.Forces (M := N) x (toSeq A) ↔
      LO.Modal.Formula.Kripke.Satisfies M x A := by
  induction A generalizing x <;> simp_all [toSeq, _root_.Model.World.Forces,
    LO.Modal.Formula.Kripke.Satisfies]

lemma provable_of_mem_logicGL {A : Modal.Formula ℕ}
    (h : toSeq A ∈ (_root_.LogicGL : _root_.Logic ℕ)) : Modal.GL ⊢ A := by
  apply LO.Modal.GL.Kripke.finite_completeness_TFAE.out 3 0 |>.mp
  intro M _ _ _ _
  let N : _root_.Model M.World ℕ := ⟨M.Rel, fun w a => M.Val a w⟩
  let _instN : _root_.Model.IsFiniteGL N :=
    { trans := fun _ _ _ hxy hyz => M.trans hxy hyz,
      irrefl := fun x hxx => M.irrefl x hxx,
      finite := inferInstance }
  have hv := (_root_.LogicGL.iff_forces (A := toSeq A)).mp h
    (κ := M.World) N
  exact (forces_translation M.root.1 A).mp (hv M.root.1)

end GlFixedPointBridge

/-- de Jongh–Sambin–Bernardi fixed-point theorem (Barasz, §4, Thm 4.2),
single-variable form, with the strong form of the existence claim: the
constructed fixed point uses only atoms from the input formula and not
the diagonal variable (standard for the Craig-interpolant / Bernardi
construction, Boolos Ch. 8). Proved through `ProvabilityLogic/` (see above). -/
theorem glFixedPoint_thm42 {p : ℕ} {φ : Modal.Formula ℕ} (h : Modalized p φ) :
    ∃ ψ : Modal.Formula ℕ,
      (Modal.GL ⊢ ψ 🡘 φ⟦diag p ψ⟧) ∧
      (∀ a, a ∈ ψ.atoms → a ∈ φ.atoms ∧ a ≠ p) := by
  let q := φ.freshAtom + p + 1
  have hpq : p ≠ q := by simp [q]; omega
  have hq : q ∉ (GlFixedPointBridge.toSeq φ).atoms := by
    intro hq
    have hqφ : q ∈ φ.atoms := by
      simpa [GlFixedPointBridge.atoms_toSeq] using hq
    have hle := LO.Modal.Formula.le_max_atoms_of_mem_atoms hqφ
    have hlt := LO.Modal.Formula.le_max_atoms_freshAtom
      (φ := φ) (show φ.atoms.Nonempty from ⟨q, hqφ⟩)
    have hq_lt : q < φ.freshAtom := lt_of_le_of_lt hle hlt
    simp [q] at hq_lt
    omega
  obtain ⟨D, hD_atoms, hD⟩ := _root_.LogicGL.fixpointTheorem hpq
    (GlFixedPointBridge.modalized_iff.mp h) hq
  let ψ := GlFixedPointBridge.ofSeq D
  refine ⟨ψ, ?_, ?_⟩
  · apply GlFixedPointBridge.provable_of_mem_logicGL
    have hfix :
        _root_.Formula.iff (GlFixedPointBridge.toSeq (φ⟦diag p ψ⟧))
            (GlFixedPointBridge.toSeq ψ) ∈ (_root_.LogicGL : _root_.Logic ℕ) := by
      simpa [ψ, GlFixedPointBridge.toSeq_diag] using hD
    apply _root_.LogicGL.iff_provableHilbert.mpr
    apply _root_.ProvableHilbert.andIntroRule
    · exact _root_.ProvableHilbert.andRRule
        (_root_.LogicGL.iff_provableHilbert.mp hfix)
    · exact _root_.ProvableHilbert.andLRule
        (_root_.LogicGL.iff_provableHilbert.mp hfix)
  · intro a ha
    have haD : a ∈ D.atoms := by
      simpa [ψ, GlFixedPointBridge.atoms_ofSeq] using ha
    have had := Finset.mem_sdiff.mp (hD_atoms haD)
    exact ⟨by simpa [GlFixedPointBridge.atoms_toSeq] using had.1,
      by simpa using had.2⟩

/-- Skolemized fixed-point operator. For non-modalized inputs it returns the
input formula; the spec lemmas only apply when the input is modalized in `p`. -/
noncomputable def glFixedPoint (p : ℕ) (φ : Modal.Formula ℕ) : Modal.Formula ℕ :=
  haveI := Classical.propDecidable (Modalized p φ)
  if h : Modalized p φ then (glFixedPoint_thm42 h).choose else φ

private lemma glFixedPoint_eq {p : ℕ} {φ : Modal.Formula ℕ} (h : Modalized p φ) :
    glFixedPoint p φ = (glFixedPoint_thm42 h).choose := by
  show (haveI := Classical.propDecidable (Modalized p φ);
    if h : Modalized p φ then (glFixedPoint_thm42 h).choose else φ) = _
  rw [dif_pos h]

/-- Defining equation for the fixed point (Barasz, §4, Thm 4.2). -/
theorem glFixedPoint_spec {p : ℕ} {φ : Modal.Formula ℕ} (h : Modalized p φ) :
    Modal.GL ⊢ glFixedPoint p φ 🡘 φ⟦diag p (glFixedPoint p φ)⟧ := by
  rw [glFixedPoint_eq h]
  exact (glFixedPoint_thm42 h).choose_spec.1

/-- Atoms of the fixed point are a subset of the input's atoms minus `p`. -/
lemma glFixedPoint_atoms {p : ℕ} {φ : Modal.Formula ℕ} (h : Modalized p φ) :
    ∀ a, a ∈ (glFixedPoint p φ).atoms → a ∈ φ.atoms ∧ a ≠ p := by
  rw [glFixedPoint_eq h]
  exact (glFixedPoint_thm42 h).choose_spec.2

/-! ## Modal.Substitution identity for absent atoms -/

/-- Substituting for an atom not in the formula leaves the formula unchanged. -/
lemma subst_diag_of_notMem_atoms {p : ℕ} {χ : Modal.Formula ℕ} :
    ∀ {ψ : Modal.Formula ℕ}, p ∉ ψ.atoms → ψ⟦diag p χ⟧ = ψ
  | .atom a, h => by
    simp only [Modal.Formula.atoms, Finset.mem_singleton] at h
    show diag p χ a = .atom a
    simp [diag, Ne.symm h]
  | .falsum, _ => rfl
  | .imp φ ψ, h => by
    simp only [Modal.Formula.atoms, Finset.mem_union, not_or] at h
    show φ⟦diag p χ⟧ 🡒 ψ⟦diag p χ⟧ = φ 🡒 ψ
    rw [subst_diag_of_notMem_atoms h.1, subst_diag_of_notMem_atoms h.2]
  | .box φ, h => by
    simp only [Modal.Formula.atoms] at h
    show □(φ⟦diag p χ⟧) = □φ
    rw [subst_diag_of_notMem_atoms h]

/-! ## Theorem 4.3 (Barasz, §4): GL fixed-point uniqueness -/

section uniqueness

variable {p : ℕ} {χ χ' : Modal.Formula ℕ}

/-- `□φ 🡒 □⊡φ`: `Four` plus box collection. -/
private def boxBoxdotOfBox {φ : Modal.Formula ℕ} : Modal.GL ⊢! □φ 🡒 □⊡φ :=
  C_trans (CK_of_C_of_C C_id axiomFour) collect_box_and

/-- Internal box-distribution over `🡘`: `□(φ 🡘 ψ) 🡒 (□φ 🡘 □ψ)`. -/
private def EBoxOfBoxE {φ ψ : Modal.Formula ℕ} :
    Modal.GL ⊢! □(φ 🡘 ψ) 🡒 (□φ 🡘 □ψ) :=
  CK_of_C_of_C
    (C_trans (implyBoxDistribute' and₁) axiomK)
    (C_trans (implyBoxDistribute' and₂) axiomK)

/-- A boxdotted equivalence premise reaches every occurrence of the
substituted atom: `⊡(χ 🡘 χ') 🡒 (φ⟦p ↦ χ⟧ 🡘 φ⟦p ↦ χ'⟧)` for arbitrary `φ`. -/
private def substCongrBoxdot : (φ : Modal.Formula ℕ) →
    Modal.GL ⊢! ⊡(χ 🡘 χ') 🡒 (φ⟦diag p χ⟧ 🡘 φ⟦diag p χ'⟧)
  | .atom a => by
    by_cases h : a = p
    · subst h
      have e₁ : (Modal.Formula.atom a)⟦diag a χ⟧ = χ := by show diag a χ a = χ; simp [diag]
      have e₂ : (Modal.Formula.atom a)⟦diag a χ'⟧ = χ' := by show diag a χ' a = χ'; simp [diag]
      rw [e₁, e₂]
      exact and₁
    · have hp : p ∉ (Modal.Formula.atom a).atoms := by
        simp only [Modal.Formula.atoms, Finset.mem_singleton]
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
private def substCongrBox : ∀ {φ : Modal.Formula ℕ}, Modalized p φ →
    Modal.GL ⊢! □(χ 🡘 χ') 🡒 (φ⟦diag p χ⟧ 🡘 φ⟦diag p χ'⟧)
  | .atom a, h => by
    have hp : p ∉ (Modal.Formula.atom a).atoms := by
      simp only [Modal.Formula.atoms, Finset.mem_singleton]
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
theorem glFixedPoint_uniqueness {p : ℕ} {φ : Modal.Formula ℕ} (hmod : Modalized p φ)
    {ψ ψ' : Modal.Formula ℕ}
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
