/-
  Cooperation analysis for modal agents (Barasz, §3-4).

  `outcome X Y` is the GL formula corresponding to the paper's
  `ψ_{[X(Y)]}` (§4, Thm 4.7). `outcome_fixed_point` is the GL-level
  fixed-point equation; `Cooperates.arithmeticLift` applies the generic
  arithmetical soundness theorem for GL.
-/

import Barasz.FixedPoint
import Foundation.ProvabilityLogic.GL.Soundness

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-- Substitute atom 0 ↦ `β`, atoms 1,…,m ↦ `refs 0,…,refs (m-1)`;
atoms > m unchanged. -/
abbrev substFull (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) : Substitution ℕ :=
  fun k => match k with
    | 0 => β
    | j + 1 => if h : j < m then refs ⟨j, h⟩ else .atom (j + 1)

/-- For `k ≠ 0`, `substFull β refs k` is modalized in atom 0 whenever each
`refs j` omits atom 0. -/
lemma substFull_modalized_step {m : ℕ} (β : Formula ℕ)
    (refs : Fin m → Formula ℕ) (hrefs : ∀ j, 0 ∉ (refs j).atoms)
    {k : ℕ} (hk : k ≠ 0) : Modalized 0 (substFull β refs k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  show Modalized 0 (if h : k < m then refs ⟨k, h⟩ else .atom (k+1))
  by_cases hk' : k < m
  · rw [dif_pos hk']
    exact modalized_of_notMem_atoms (hrefs ⟨k, hk'⟩)
  · rw [dif_neg hk']
    show k+1 ≠ 0
    exact Nat.succ_ne_zero k

/-- `X.formula⟦substFull β refs⟧` is modalized in atom 0 whenever each
`refs i` omits atom 0. -/
lemma modalized_substFull (X : ModalAgent) (β : Formula ℕ)
    (refs : Fin X.arity → Formula ℕ) (hrefs : ∀ i, 0 ∉ (refs i).atoms) :
    Modalized 0 (X.formula⟦substFull β refs⟧) :=
  modalized_subst (fun _ hk => substFull_modalized_step β refs hrefs hk)
    (X.modalized 0 (Nat.zero_le _))

/-! ## Outcomes -/

/-- GL formula corresponding to the paper's `ψ_{[X(Y)]}` (Barasz, §4). -/
noncomputable def outcome (X Y : ModalAgent) : Formula ℕ :=
  glFixedPoint 0
    (X.formula⟦substFull
      (Y.formula⟦substFull (.atom 0)
        (fun j : Fin Y.arity => outcome X (Y.references j))⟧)
      (fun i : Fin X.arity => outcome Y (X.references i))⟧)
termination_by X.rank + Y.rank
decreasing_by
  all_goals first
    | (have h := ModalAgent.rank_ref_lt Y j; omega)
    | (have h := ModalAgent.rank_ref_lt X i; omega)

/-- Two-level operator. `F_of X Y (.atom 0)` is the formula whose
GL fixed point is `outcome X Y`. -/
noncomputable def F_of (X Y : ModalAgent) (p : Formula ℕ) : Formula ℕ :=
  X.formula⟦substFull
    (Y.formula⟦substFull p (fun j : Fin Y.arity => outcome X (Y.references j))⟧)
    (fun i : Fin X.arity => outcome Y (X.references i))⟧

/-- Bridge between the recursive definition of `outcome` and `F_of`. -/
lemma outcome_unfold (X Y : ModalAgent) :
    outcome X Y = glFixedPoint 0 (F_of X Y (.atom 0)) := by
  rw [outcome]; rfl

/-- Atom 0 doesn't appear in `outcome X Y`. -/
lemma outcome_atoms_notMem (X Y : ModalAgent) : 0 ∉ (outcome X Y).atoms := by
  intro hmem
  rw [outcome_unfold] at hmem
  have hMod : Modalized 0 (F_of X Y (.atom 0)) :=
    modalized_substFull X _ _ (fun i => outcome_atoms_notMem Y (X.references i))
  exact (glFixedPoint_atoms hMod 0 hmem).2 rfl
termination_by X.rank + Y.rank
decreasing_by have h := ModalAgent.rank_ref_lt X i; omega

/-- `F_of X Y p` is modalized in atom 0 for any `p`: X.formula's atom-0
occurrences are already under boxes, and the outer references omit atom 0. -/
lemma F_of_modalized (X Y : ModalAgent) (p : Formula ℕ) : Modalized 0 (F_of X Y p) :=
  modalized_substFull X _ _ (fun _ => outcome_atoms_notMem _ _)

/-! ## Substitution lemmas -/

/-- Substitution composition: `substFull β refs` post-composed with
`diag 0 χ` equals `substFull (β⟦diag 0 χ⟧) refs`, provided each `refs j`
doesn't mention atom 0. -/
lemma substFull_comp_diag_of_notMem (β χ : Formula ℕ) {m : ℕ}
    (refs : Fin m → Formula ℕ) (hrefs : ∀ j, 0 ∉ (refs j).atoms) :
    (substFull β refs) ∘ (diag 0 χ) = substFull (β⟦diag 0 χ⟧) refs := by
  funext k
  show ((substFull β refs) k)⟦diag 0 χ⟧ = (substFull (β⟦diag 0 χ⟧) refs) k
  match k with
  | 0 => rfl
  | j+1 =>
    show (if h : j < m then refs ⟨j, h⟩ else .atom (j+1))⟦diag 0 χ⟧
       = if h : j < m then refs ⟨j, h⟩ else .atom (j+1)
    by_cases h : j < m
    · rw [dif_pos h]
      exact subst_diag_of_notMem_atoms (hrefs ⟨j, h⟩)
    · rw [dif_neg h]
      show diag 0 χ (j+1) = .atom (j+1)
      simp [diag]

/-- Substitution identity: `F_of X Y (.atom 0)` with atom 0 instantiated
to `ψ` equals `F_of X Y ψ`. -/
lemma F_of_subst (X Y : ModalAgent) (ψ : Formula ℕ) :
    (F_of X Y (.atom 0))⟦diag 0 ψ⟧ = F_of X Y ψ := by
  unfold F_of
  rw [← Formula.subst.def_comp,
      substFull_comp_diag_of_notMem _ _ _ (fun _ => outcome_atoms_notMem _ _),
      ← Formula.subst.def_comp,
      substFull_comp_diag_of_notMem _ _ _ (fun _ => outcome_atoms_notMem _ _)]
  rfl

/-- For zero-reference substitutions, changing the atom-0 replacement is the
only nontrivial substitution case. -/
lemma substFull_zero_congr (φ β γ : Formula ℕ) (refs : Fin 0 → Formula ℕ)
    (h : Modal.GL ⊢ β 🡘 γ) :
    Modal.GL ⊢ φ⟦substFull β refs⟧ 🡘 φ⟦substFull γ refs⟧ := by
  apply subst_congr
  intro a
  cases a with
  | zero => exact h
  | succ k =>
    show Modal.GL ⊢
      (if hk : k < 0 then refs ⟨k, hk⟩ else .atom (k + 1)) 🡘
      (if hk : k < 0 then refs ⟨k, hk⟩ else .atom (k + 1))
    simp

/-! ## Fixed-point equations -/

/-- Two-level fixed-point equation for `outcome`. -/
lemma outcome_twoLevel (X Y : ModalAgent) :
    Modal.GL ⊢ outcome X Y 🡘 F_of X Y (outcome X Y) := by
  have h := glFixedPoint_spec (F_of_modalized X Y (.atom 0))
  rw [← outcome_unfold, F_of_subst] at h
  exact h

/-- GL-level form of the modal-agent fixed-point equation
(Barasz, §4, Thm 4.7). -/
theorem outcome_fixed_point (X Y : ModalAgent) :
    Modal.GL ⊢ outcome X Y 🡘
      X.formula⟦substFull (outcome Y X)
        (fun j : Fin X.arity => outcome Y (X.references j))⟧ := by
  set K := X.formula⟦substFull (outcome Y X)
    (fun i : Fin X.arity => outcome Y (X.references i))⟧
  have hYX' : Modal.GL ⊢ outcome Y X 🡘
      Y.formula⟦substFull K (fun j : Fin Y.arity => outcome X (Y.references j))⟧ :=
    outcome_twoLevel Y X
  have hKfp : Modal.GL ⊢ K 🡘 F_of X Y K := by
    unfold F_of
    apply subst_congr
    intro a
    match a with
    | 0 => exact hYX'
    | _+1 => exact E!_id
  have hMod := F_of_modalized X Y (.atom 0)
  have hα' : Modal.GL ⊢ outcome X Y 🡘 (F_of X Y (.atom 0))⟦diag 0 (outcome X Y)⟧ := by
    rw [F_of_subst]; exact outcome_twoLevel X Y
  have hKfp' : Modal.GL ⊢ K 🡘 (F_of X Y (.atom 0))⟦diag 0 K⟧ := by
    rw [F_of_subst]; exact hKfp
  exact glFixedPoint_uniqueness hMod hα' hKfp'

/-! ## Concrete-agent formula reductions -/

@[simp] lemma cooperateBot_formula_substFull
    (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) :
    cooperateBot.formula⟦substFull β refs⟧ = (⊤ : Formula ℕ) := rfl

@[simp] lemma defectBot_formula_substFull
    (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) :
    defectBot.formula⟦substFull β refs⟧ = (⊥ : Formula ℕ) := rfl

@[simp] lemma fairBot_formula_substFull
    (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) :
    fairBot.formula⟦substFull β refs⟧ = □β := rfl

@[simp] lemma prudentBot_formula_substFull
    (β : Formula ℕ) (refs : Fin 1 → Formula ℕ) :
    prudentBot.formula⟦substFull β refs⟧ = □β ⋏ □(∼□⊥ 🡒 ∼(refs 0)) := rfl

/-! ## Cooperation predicates -/

/-- X cooperates with Y: GL proves the outcome formula. -/
def Cooperates (X Y : ModalAgent) : Prop := Modal.GL ⊢ outcome X Y

/-- X defects against Y: GL does not prove the outcome formula. This is a
modal-level proxy, not a PA unprovability statement. -/
def Defects (X Y : ModalAgent) : Prop := Modal.GL ⊬ outcome X Y

/-! ## Cooperation theorems -/

/-- `outcome defectBot Y ↔ ⊥` for every Y. -/
lemma outcome_defectBot (Y : ModalAgent) : Modal.GL ⊢ outcome defectBot Y 🡘 ⊥ := by
  have h := outcome_fixed_point defectBot Y
  simpa [defectBot_formula_substFull] using h

/-- `outcome cooperateBot Y ↔ ⊤` for every Y. -/
lemma outcome_cooperateBot (Y : ModalAgent) : Modal.GL ⊢ outcome cooperateBot Y 🡘 ⊤ := by
  have h := outcome_fixed_point cooperateBot Y
  simpa [cooperateBot_formula_substFull] using h

/-- `outcome fairBot Y ↔ □(outcome Y fairBot)` for every Y. -/
lemma outcome_fairBot (Y : ModalAgent) :
    Modal.GL ⊢ outcome fairBot Y 🡘 □(outcome Y fairBot) := by
  have h := outcome_fixed_point fairBot Y
  simpa [fairBot_formula_substFull] using h

/-- `outcome prudentBot Y ↔ □(outcome Y prudentBot) ⋏ □(∼□⊥ 🡒 ∼(outcome Y defectBot))`
for every Y. -/
lemma outcome_prudentBot (Y : ModalAgent) :
    Modal.GL ⊢ outcome prudentBot Y 🡘
      □(outcome Y prudentBot) ⋏ □(∼□⊥ 🡒 ∼(outcome Y defectBot)) := by
  have h := outcome_fixed_point prudentBot Y
  simpa [prudentBot_formula_substFull] using h

/-- DefectBot defects against every opponent (Barasz, §2). -/
theorem defectBot_defects (Y : ModalAgent) : Defects defectBot Y := by
  intro ⟨hb⟩
  have ⟨hβ⟩ := outcome_defectBot Y
  exact (inferInstance : Consistent Modal.GL).not_inconsistent
    (fun _ => ⟨efq ⨀ (and₁ ⨀ hβ ⨀ hb)⟩)

/-- CooperateBot cooperates with every opponent (Barasz, §2). -/
theorem cooperateBot_cooperates (Y : ModalAgent) : Cooperates cooperateBot Y := by
  have ⟨h⟩ := outcome_cooperateBot Y
  exact ⟨and₂ ⨀ h ⨀ verum⟩

/-! ## Concrete cooperation: rank 0 -/

/-- FairBot cooperates with itself (Barasz, §3, Thm 3.1). -/
theorem fairBot_vs_fairBot : Cooperates fairBot fairBot := by
  have ⟨hα⟩ := outcome_fairBot fairBot
  have h : Modal.GL ⊢! outcome fairBot fairBot ⋏ outcome fairBot fairBot :=
    lobian_circle (and₂ ⨀ hα) (and₂ ⨀ hα)
  exact ⟨and₁ ⨀ h⟩

/-- FairBot and CooperateBot mutually cooperate (Barasz, §3). -/
theorem fairBot_vs_cooperateBot :
    Cooperates fairBot cooperateBot ∧ Cooperates cooperateBot fairBot := by
  have ⟨hα⟩ := outcome_fairBot cooperateBot
  have ⟨h_cb⟩ := cooperateBot_cooperates fairBot
  exact ⟨⟨and₂ ⨀ hα ⨀ nec h_cb⟩, cooperateBot_cooperates fairBot⟩

/-- GL-level form of Barasz §4, Thm 4.10: a rank-0 modal agent that
cooperates with FairBot also cooperates with CooperateBot. -/
theorem rank0_fairBot_implies_cooperateBot (X : ModalAgent) (h_rank : X.rank = 0) :
    Cooperates X fairBot → Cooperates X cooperateBot := by
  intro hXF
  have h_arity := ModalAgent.arity_eq_zero_of_rank_eq_zero h_rank
  cases X with
  | mk φ n refs mod =>
    simp [ModalAgent.arity] at h_arity
    subst n
    let X : ModalAgent := ModalAgent.mk φ 0 refs mod
    change Cooperates X cooperateBot
    change Cooperates X fairBot at hXF
    have hXF_proof := hXF.some
    have hXFB_fp := outcome_fixed_point X fairBot
    have hFBX := outcome_fairBot X
    have h_to_box : Modal.GL ⊢
        φ⟦substFull (outcome fairBot X)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ 🡘
        φ⟦substFull (□(outcome X fairBot))
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ :=
      substFull_zero_congr φ (outcome fairBot X) (□(outcome X fairBot))
        (fun j : Fin 0 => outcome fairBot (X.references j)) hFBX
    have h_phi_box : Modal.GL ⊢!
        φ⟦substFull (□(outcome X fairBot))
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ := by
      exact and₁ ⨀ h_to_box.some ⨀ (and₁ ⨀ hXFB_fp.some ⨀ hXF_proof)
    have h_box_top : Modal.GL ⊢ □(outcome X fairBot) 🡘 (⊤ : Formula ℕ) := by
      exact ⟨E_intro (C_of_conseq verum) (C_of_conseq (nec hXF_proof))⟩
    have h_to_top : Modal.GL ⊢
        φ⟦substFull (□(outcome X fairBot))
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ 🡘
        φ⟦substFull (⊤ : Formula ℕ)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ :=
      substFull_zero_congr φ (□(outcome X fairBot)) (⊤ : Formula ℕ)
        (fun j : Fin 0 => outcome fairBot (X.references j)) h_box_top
    have h_phi_top : Modal.GL ⊢!
        φ⟦substFull (⊤ : Formula ℕ)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ := by
      exact and₁ ⨀ h_to_top.some ⨀ h_phi_box
    have hCBX := outcome_cooperateBot X
    have h_to_cb : Modal.GL ⊢
        φ⟦substFull (outcome cooperateBot X)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ 🡘
        φ⟦substFull (⊤ : Formula ℕ)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ :=
      substFull_zero_congr φ (outcome cooperateBot X) (⊤ : Formula ℕ)
        (fun j : Fin 0 => outcome cooperateBot (X.references j)) hCBX
    have hXCB_fp := outcome_fixed_point X cooperateBot
    have h_rhs_cb : Modal.GL ⊢!
        φ⟦substFull (outcome cooperateBot X)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ := by
      simpa using (and₂ ⨀ h_to_cb.some ⨀ h_phi_top)
    exact ⟨and₂ ⨀ hXCB_fp.some ⨀ h_rhs_cb⟩

/-- FairBot and DefectBot mutually defect (Barasz, §3). -/
theorem fairBot_vs_defectBot :
    Defects fairBot defectBot ∧ Defects defectBot fairBot := by
  have ⟨hα⟩ := outcome_fairBot defectBot
  have ⟨hβ⟩ := outcome_defectBot fairBot
  refine ⟨?_, defectBot_defects fairBot⟩
  intro ⟨ha⟩
  have h_box : Modal.GL ⊢! □(outcome defectBot fairBot) := and₁ ⨀ hα ⨀ ha
  have h_imp : Modal.GL ⊢! outcome defectBot fairBot 🡒 ⊥ := and₁ ⨀ hβ
  have : Modal.GL ⊢! □(⊥ : Formula ℕ) := axiomK' (nec h_imp) ⨀ h_box
  exact unprovable_box_bot ⟨this⟩

/-- PrudentBot and FairBot mutually cooperate (Barasz, §3, Thm 3.2). -/
theorem prudentBot_vs_fairBot :
    Cooperates prudentBot fairBot ∧ Cooperates fairBot prudentBot := by
  have ⟨hα⟩ := outcome_prudentBot fairBot
  have ⟨hFBvsPB⟩ := outcome_fairBot prudentBot
  have ⟨hFBvsDB⟩ := outcome_fairBot defectBot
  have ⟨hDBvsFB⟩ := outcome_defectBot fairBot
  have h_FBvsDB_to_boxbot : Modal.GL ⊢! outcome fairBot defectBot 🡒 □(⊥ : Formula ℕ) :=
    C_trans (and₁ ⨀ hFBvsDB) (axiomK' (nec (and₁ ⨀ hDBvsFB)))
  have h_consist : Modal.GL ⊢! □(∼□(⊥ : Formula ℕ) 🡒 ∼(outcome fairBot defectBot)) :=
    nec (contra h_FBvsDB_to_boxbot)
  have h : Modal.GL ⊢! outcome prudentBot fairBot ⋏ outcome fairBot prudentBot :=
    lobian_circle (and₂ ⨀ hFBvsPB)
      (C_trans (CK_of_C_of_C C_id (C_of_conseq h_consist)) (and₂ ⨀ hα))
  exact ⟨⟨and₁ ⨀ h⟩, ⟨and₂ ⨀ h⟩⟩

/-- PrudentBot and DefectBot mutually defect (Barasz, §3, Thm 3.2). -/
theorem prudentBot_vs_defectBot :
    Defects prudentBot defectBot ∧ Defects defectBot prudentBot := by
  have ⟨hα⟩ := outcome_prudentBot defectBot
  have ⟨hβ⟩ := outcome_defectBot prudentBot
  refine ⟨?_, defectBot_defects prudentBot⟩
  intro ⟨ha⟩
  have h_box : Modal.GL ⊢! □(outcome defectBot prudentBot) := and₁ ⨀ (and₁ ⨀ hα ⨀ ha)
  have h_imp : Modal.GL ⊢! outcome defectBot prudentBot 🡒 ⊥ := and₁ ⨀ hβ
  exact unprovable_box_bot ⟨axiomK' (nec h_imp) ⨀ h_box⟩

/-- PrudentBot defects against CooperateBot; CooperateBot cooperates
with PrudentBot (Barasz, §3, Thm 3.2). -/
theorem prudentBot_vs_cooperateBot :
    Defects prudentBot cooperateBot ∧ Cooperates cooperateBot prudentBot := by
  have ⟨hα⟩ := outcome_prudentBot cooperateBot
  refine ⟨?_, cooperateBot_cooperates prudentBot⟩
  intro ⟨ha⟩
  have h_right : Modal.GL ⊢! □(∼□(⊥:Formula ℕ) 🡒 ∼(outcome cooperateBot defectBot)) :=
    and₂ ⨀ (and₁ ⨀ hα ⨀ ha)
  have ⟨h_cbdb⟩ := cooperateBot_cooperates defectBot
  have h_flip : Modal.GL ⊢! □(outcome cooperateBot defectBot 🡒 □(⊥ : Formula ℕ)) :=
    axiomK' (nec CCNNC) ⨀ h_right
  have h_boxbox : Modal.GL ⊢! □(□(⊥ : Formula ℕ)) :=
    axiomK' h_flip ⨀ (nec h_cbdb)
  exact unprovable_box_box_bot ⟨h_boxbox⟩

/-- PrudentBot cooperates with itself (Barasz, §3, Thm 3.2). -/
theorem prudentBot_vs_prudentBot : Cooperates prudentBot prudentBot := by
  have ⟨hα⟩ := outcome_prudentBot prudentBot
  have ⟨hg⟩ := outcome_prudentBot defectBot
  have ⟨hβ⟩ := outcome_defectBot prudentBot
  have h_g_to_boxbot : Modal.GL ⊢! outcome prudentBot defectBot 🡒 □(⊥ : Formula ℕ) :=
    C_trans (C_trans (and₁ ⨀ hg) and₁) (axiomK' (nec (and₁ ⨀ hβ)))
  have h_consist : Modal.GL ⊢! □(∼□(⊥:Formula ℕ) 🡒 ∼(outcome prudentBot defectBot)) :=
    nec (contra h_g_to_boxbot)
  have h₁ : Modal.GL ⊢! □(outcome prudentBot prudentBot) 🡒
      □(outcome prudentBot prudentBot) ⋏
      □(∼□(⊥:Formula ℕ) 🡒 ∼(outcome prudentBot defectBot)) :=
    CK_of_C_of_C C_id (C_of_conseq h_consist)
  exact ⟨lob_rule (C_trans h₁ (and₂ ⨀ hα))⟩

/-! ## Arithmetical lift (Barasz, §4, Thm 4.1) -/

/-- Lift GL-provable cooperation through an arithmetical realization
(Barasz, §4, Thm 4.1). -/
theorem Cooperates.arithmeticLift {X Y : ModalAgent} (h : Cooperates X Y)
    {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
    {T U : FirstOrder.Theory L} [FirstOrder.ProvabilityAbstraction.Diagonalization T]
    [T ⪯ U] {𝔅 : FirstOrder.ProvabilityAbstraction.Provability T U} [𝔅.HBL]
    {f : ProvabilityLogic.Realization 𝔅} : U ⊢ f (outcome X Y) :=
  ProvabilityLogic.GL.arithmetical_soundness h
