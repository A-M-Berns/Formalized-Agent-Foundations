/-
  Cooperation analysis for modal agents (Barasz, §3-4).

  `outcome X Y` is the GL formula corresponding to the paper's
  `ψ_{[X(Y)]}` (§4, Thm 4.7). `outcome_fixed_point` is the GL-level
  fixed-point equation; `Cooperates.arithmeticLift` applies the generic
  arithmetical soundness theorem for GL.
-/

import ModalAgents.FixedPoint
import ProvabilityLogic.ProvabilityLogic.GL.Basic

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-- Substitute atom 0 ↦ `β`, atoms 1,…,m ↦ `refs 0,…,refs (m-1)`;
atoms > m unchanged. -/
abbrev substFull (β : Modal.Formula ℕ) {m : ℕ} (refs : Fin m → Modal.Formula ℕ) : Modal.Substitution ℕ :=
  fun k => match k with
    | 0 => β
    | j + 1 => if h : j < m then refs ⟨j, h⟩ else .atom (j + 1)

/-- For `k ≠ 0`, `substFull β refs k` is modalized in atom 0 whenever each
`refs j` omits atom 0. -/
lemma substFull_modalized_step {m : ℕ} (β : Modal.Formula ℕ)
    (refs : Fin m → Modal.Formula ℕ) (hrefs : ∀ j, 0 ∉ (refs j).atoms)
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
lemma modalized_substFull (X : ModalAgent) (β : Modal.Formula ℕ)
    (refs : Fin X.arity → Modal.Formula ℕ) (hrefs : ∀ i, 0 ∉ (refs i).atoms) :
    Modalized 0 (X.formula⟦substFull β refs⟧) :=
  modalized_subst (fun _ hk => substFull_modalized_step β refs hrefs hk)
    (X.modalized 0 (Nat.zero_le _))

/-! ## Outcomes -/

/-- GL formula corresponding to the paper's `ψ_{[X(Y)]}` (Barasz, §4). -/
noncomputable def outcome (X Y : ModalAgent) : Modal.Formula ℕ :=
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
noncomputable def F_of (X Y : ModalAgent) (p : Modal.Formula ℕ) : Modal.Formula ℕ :=
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
lemma F_of_modalized (X Y : ModalAgent) (p : Modal.Formula ℕ) : Modalized 0 (F_of X Y p) :=
  modalized_substFull X _ _ (fun _ => outcome_atoms_notMem _ _)

/-! ## Modal.Substitution lemmas -/

/-- Modal.Substitution composition: `substFull β refs` post-composed with
`diag 0 χ` equals `substFull (β⟦diag 0 χ⟧) refs`, provided each `refs j`
doesn't mention atom 0. -/
lemma substFull_comp_diag_of_notMem (β χ : Modal.Formula ℕ) {m : ℕ}
    (refs : Fin m → Modal.Formula ℕ) (hrefs : ∀ j, 0 ∉ (refs j).atoms) :
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

/-- Modal.Substitution identity: `F_of X Y (.atom 0)` with atom 0 instantiated
to `ψ` equals `F_of X Y ψ`. -/
lemma F_of_subst (X Y : ModalAgent) (ψ : Modal.Formula ℕ) :
    (F_of X Y (.atom 0))⟦diag 0 ψ⟧ = F_of X Y ψ := by
  unfold F_of
  rw [← Modal.Formula.subst.def_comp,
      substFull_comp_diag_of_notMem _ _ _ (fun _ => outcome_atoms_notMem _ _),
      ← Modal.Formula.subst.def_comp,
      substFull_comp_diag_of_notMem _ _ _ (fun _ => outcome_atoms_notMem _ _)]
  rfl

/-- For zero-reference substitutions, changing the atom-0 replacement is the
only nontrivial substitution case. -/
lemma substFull_zero_congr (φ β γ : Modal.Formula ℕ) (refs : Fin 0 → Modal.Formula ℕ)
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

/-- GL-level form of the modal-agent fixed-point equation: `outcome X Y` is
the fixed point `ψ_{[X(Y)]}` of `X`'s modal formula applied to `Y`'s outcomes.

Paper node: Theorem 4.7 (§4). -/
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
    (β : Modal.Formula ℕ) {m : ℕ} (refs : Fin m → Modal.Formula ℕ) :
    cooperateBot.formula⟦substFull β refs⟧ = (⊤ : Modal.Formula ℕ) := rfl

@[simp] lemma defectBot_formula_substFull
    (β : Modal.Formula ℕ) {m : ℕ} (refs : Fin m → Modal.Formula ℕ) :
    defectBot.formula⟦substFull β refs⟧ = (⊥ : Modal.Formula ℕ) := rfl

@[simp] lemma fairBot_formula_substFull
    (β : Modal.Formula ℕ) {m : ℕ} (refs : Fin m → Modal.Formula ℕ) :
    fairBot.formula⟦substFull β refs⟧ = □β := rfl

@[simp] lemma prudentBot_formula_substFull
    (β : Modal.Formula ℕ) (refs : Fin 1 → Modal.Formula ℕ) :
    prudentBot.formula⟦substFull β refs⟧ = □β ⋏ □(∼□⊥ 🡒 ∼(refs 0)) := rfl

/-! ## Cooperation predicates -/

/-- X cooperates with Y: GL proves the outcome formula. -/
def Cooperates (X Y : ModalAgent) : Prop := Modal.GL ⊢ outcome X Y

/-- X defects against Y, rendered as: GL does not prove the outcome formula.

**This is weaker than the paper's notion of defection, and the gap is
one-directional.** Barász et al. assert *provable defection* — e.g.
`PA+2 ⊢ [PB(CB)=D]` for Theorem 3.2's last conjunct — whereas this predicate says
only that cooperation is *unprovable* in `GL`. Unprovability of cooperation does not
yield provability of defection, so no `Defects` result lifts to an arithmetical
claim: `Cooperates` has `Cooperates.arithmeticLift` (Theorem 4.1) and `Defects` has
no counterpart. Every use of this predicate inherits the weakening; see the modeling
boundary in `ModalAgents/README.md`. -/
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
  exact outcome_fixed_point prudentBot Y

/-- DefectBot defects against every opponent. Barasz states this as §2 prose
(`PA ⊢ [DB(X)=D]`, in an unnumbered remark), so it carries no paper-node
annotation. -/
theorem defectBot_defects (Y : ModalAgent) : Defects defectBot Y := by
  intro ⟨hb⟩
  have ⟨hβ⟩ := outcome_defectBot Y
  exact (inferInstance : Consistent Modal.GL).not_inconsistent
    (fun _ => ⟨efq ⨀ (and₁ ⨀ hβ ⨀ hb)⟩)

/-- CooperateBot cooperates with every opponent. Barasz states this as §2 prose
(`PA ⊢ [CB(X)=C]`, in an unnumbered remark), so it carries no paper-node
annotation. -/
theorem cooperateBot_cooperates (Y : ModalAgent) : Cooperates cooperateBot Y := by
  have ⟨h⟩ := outcome_cooperateBot Y
  exact ⟨and₂ ⨀ h ⨀ verum⟩

/-! ## Concrete cooperation: rank 0 -/

/-- FairBot cooperates with itself, by the Löbian circle.

Paper node: Theorem 3.1 (§3). -/
theorem fairBot_vs_fairBot : Cooperates fairBot fairBot := by
  have ⟨hα⟩ := outcome_fairBot fairBot
  have h : Modal.GL ⊢! outcome fairBot fairBot ⋏ outcome fairBot fairBot :=
    lobian_circle (and₂ ⨀ hα) (and₂ ⨀ hα)
  exact ⟨and₁ ⨀ h⟩

/-- FairBot and CooperateBot mutually cooperate. Barasz notes this only as §3
prose ("FairBot wastes utility by cooperating even with CooperateBot"), so it
carries no paper-node annotation. -/
theorem fairBot_vs_cooperateBot :
    Cooperates fairBot cooperateBot ∧ Cooperates cooperateBot fairBot := by
  have ⟨hα⟩ := outcome_fairBot cooperateBot
  have ⟨h_cb⟩ := cooperateBot_cooperates fairBot
  exact ⟨⟨and₂ ⨀ hα ⨀ nec h_cb⟩, cooperateBot_cooperates fairBot⟩

/-- GL-level form: a rank-0 modal agent that cooperates with FairBot also
cooperates with CooperateBot.

Paper node: Theorem 4.10 (§4). -/
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
    have h_box_top : Modal.GL ⊢ □(outcome X fairBot) 🡘 (⊤ : Modal.Formula ℕ) := by
      exact ⟨E_intro (C_of_conseq verum) (C_of_conseq (nec hXF_proof))⟩
    have h_to_top : Modal.GL ⊢
        φ⟦substFull (□(outcome X fairBot))
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ 🡘
        φ⟦substFull (⊤ : Modal.Formula ℕ)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ :=
      substFull_zero_congr φ (□(outcome X fairBot)) (⊤ : Modal.Formula ℕ)
        (fun j : Fin 0 => outcome fairBot (X.references j)) h_box_top
    have h_phi_top : Modal.GL ⊢!
        φ⟦substFull (⊤ : Modal.Formula ℕ)
          (fun j : Fin 0 => outcome fairBot (X.references j))⟧ := by
      exact and₁ ⨀ h_to_top.some ⨀ h_phi_box
    have hCBX := outcome_cooperateBot X
    have h_to_cb : Modal.GL ⊢
        φ⟦substFull (outcome cooperateBot X)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ 🡘
        φ⟦substFull (⊤ : Modal.Formula ℕ)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ :=
      substFull_zero_congr φ (outcome cooperateBot X) (⊤ : Modal.Formula ℕ)
        (fun j : Fin 0 => outcome cooperateBot (X.references j)) hCBX
    have hXCB_fp := outcome_fixed_point X cooperateBot
    have h_rhs_cb : Modal.GL ⊢!
        φ⟦substFull (outcome cooperateBot X)
          (fun j : Fin 0 => outcome cooperateBot (X.references j))⟧ := by
      simpa using (and₂ ⨀ h_to_cb.some ⨀ h_phi_top)
    exact ⟨and₂ ⨀ hXCB_fp.some ⨀ h_rhs_cb⟩

/-- FairBot and DefectBot mutually defect. Barasz states FairBot's
unexploitability as §3 prose ("by inspection"), so this carries no paper-node
annotation. -/
theorem fairBot_vs_defectBot :
    Defects fairBot defectBot ∧ Defects defectBot fairBot := by
  have ⟨hα⟩ := outcome_fairBot defectBot
  have ⟨hβ⟩ := outcome_defectBot fairBot
  refine ⟨?_, defectBot_defects fairBot⟩
  intro ⟨ha⟩
  have h_box : Modal.GL ⊢! □(outcome defectBot fairBot) := and₁ ⨀ hα ⨀ ha
  have h_imp : Modal.GL ⊢! outcome defectBot fairBot 🡒 ⊥ := and₁ ⨀ hβ
  have : Modal.GL ⊢! □(⊥ : Modal.Formula ℕ) := axiomK' (nec h_imp) ⨀ h_box
  exact unprovable_box_bot ⟨this⟩

/-- PrudentBot and FairBot mutually cooperate — the "mutually cooperates …
with FairBot" conjunct of the node below.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_vs_fairBot :
    Cooperates prudentBot fairBot ∧ Cooperates fairBot prudentBot := by
  have ⟨hα⟩ := outcome_prudentBot fairBot
  have ⟨hFBvsPB⟩ := outcome_fairBot prudentBot
  have ⟨hFBvsDB⟩ := outcome_fairBot defectBot
  have ⟨hDBvsFB⟩ := outcome_defectBot fairBot
  have h_FBvsDB_to_boxbot : Modal.GL ⊢! outcome fairBot defectBot 🡒 □(⊥ : Modal.Formula ℕ) :=
    C_trans (and₁ ⨀ hFBvsDB) (axiomK' (nec (and₁ ⨀ hDBvsFB)))
  have h_consist : Modal.GL ⊢! □(∼□(⊥ : Modal.Formula ℕ) 🡒 ∼(outcome fairBot defectBot)) :=
    nec (contra h_FBvsDB_to_boxbot)
  have h : Modal.GL ⊢! outcome prudentBot fairBot ⋏ outcome fairBot prudentBot :=
    lobian_circle (and₂ ⨀ hFBvsPB)
      (C_trans (CK_of_C_of_C C_id (C_of_conseq h_consist)) (and₂ ⨀ hα))
  exact ⟨⟨and₁ ⨀ h⟩, ⟨and₂ ⨀ h⟩⟩

/-- PrudentBot and DefectBot mutually defect. This is the "in particular,
`PA+1 ⊢ [PB(DB)=D]`" step *inside* the proof of Barasz §3, Thm 3.2, not one of
that theorem's four conjuncts, so it carries no paper-node annotation; Thm 3.2's
unexploitability conjunct (which quantifies over all opponents) is not
formalized here. -/
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
with PrudentBot. The first component is the "defects against CooperateBot"
conjunct of the node below.

**Disclosed weakening.** That conjunct is `PA+2 ⊢ [PB(CB)=D]` in the paper —
provable defection. Here it is `Defects`, i.e. `GL ⊬ outcome`, the unprovability of
cooperation; see that definition. The cooperation component is at full strength and
lifts through `Cooperates.arithmeticLift`. The node's remaining conjuncts are carried
by `prudentBot_vs_prudentBot` and `prudentBot_vs_fairBot`; its unexploitability
conjunct, which quantifies over all opponents, is not formalized.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_vs_cooperateBot :
    Defects prudentBot cooperateBot ∧ Cooperates cooperateBot prudentBot := by
  have ⟨hα⟩ := outcome_prudentBot cooperateBot
  refine ⟨?_, cooperateBot_cooperates prudentBot⟩
  intro ⟨ha⟩
  have h_right : Modal.GL ⊢! □(∼□(⊥:Modal.Formula ℕ) 🡒 ∼(outcome cooperateBot defectBot)) :=
    and₂ ⨀ (and₁ ⨀ hα ⨀ ha)
  have ⟨h_cbdb⟩ := cooperateBot_cooperates defectBot
  have h_flip : Modal.GL ⊢! □(outcome cooperateBot defectBot 🡒 □(⊥ : Modal.Formula ℕ)) :=
    axiomK' (nec CCNNC) ⨀ h_right
  have h_boxbox : Modal.GL ⊢! □(□(⊥ : Modal.Formula ℕ)) :=
    axiomK' h_flip ⨀ (nec h_cbdb)
  exact unprovable_box_box_bot ⟨h_boxbox⟩

/-- PrudentBot cooperates with itself — the "mutually cooperates with itself"
conjunct of the node below.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_vs_prudentBot : Cooperates prudentBot prudentBot := by
  have ⟨hα⟩ := outcome_prudentBot prudentBot
  have ⟨hg⟩ := outcome_prudentBot defectBot
  have ⟨hβ⟩ := outcome_defectBot prudentBot
  have h_g_to_boxbot : Modal.GL ⊢! outcome prudentBot defectBot 🡒 □(⊥ : Modal.Formula ℕ) :=
    C_trans (C_trans (and₁ ⨀ hg) and₁) (axiomK' (nec (and₁ ⨀ hβ)))
  have h_consist : Modal.GL ⊢! □(∼□(⊥:Modal.Formula ℕ) 🡒 ∼(outcome prudentBot defectBot)) :=
    nec (contra h_g_to_boxbot)
  have h₁ : Modal.GL ⊢! □(outcome prudentBot prudentBot) 🡒
      □(outcome prudentBot prudentBot) ⋏
      □(∼□(⊥:Modal.Formula ℕ) 🡒 ∼(outcome prudentBot defectBot)) :=
    CK_of_C_of_C C_id (C_of_conseq h_consist)
  exact ⟨lob_rule (C_trans h₁ (and₂ ⨀ hα))⟩

/-! ## Arithmetical lift (Barasz, §4, Thm 4.1) -/

/-- Lift GL-provable cooperation through an arithmetical realization
The realization comes from the upstream
`ProvabilityLogic` package and consumes that development's formulas, so the
conclusion interprets the translated outcome formula
(`GlFixedPointBridge.toSeq`); the translation is the identity on the modal
structure (see `GlFixedPointBridge.ofSeq_toSeq`/`toSeq_ofSeq`).

Paper node: Theorem 4.1 (§4). -/
theorem Cooperates.arithmeticLift {X Y : ModalAgent} (h : Cooperates X Y)
    {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
    {T U : FirstOrder.Theory L} [FirstOrder.ProvabilityAbstraction.Diagonalization T]
    [T ⪯ U] {𝔅 : FirstOrder.ProvabilityAbstraction.Provability T U} [𝔅.HBL]
    {f : _root_.Realization ℕ 𝔅} :
    U ⊢ f (GlFixedPointBridge.toSeq (outcome X Y)) :=
  _root_.LogicGL.arithmetical_soundness'
    (GlFixedPointBridge.mem_logicGL_of_provable h)

/-- Example: the GL proof that FairBot cooperates with itself lifts to PA
under any standard arithmetical realization. -/
example (f : _root_.StandardRealization ℕ 𝗣𝗔) :
    𝗣𝗔 ⊢ f (GlFixedPointBridge.toSeq (outcome fairBot fairBot)) :=
  Cooperates.arithmeticLift fairBot_vs_fairBot
