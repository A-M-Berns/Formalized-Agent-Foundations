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

This is strictly weaker than `ProvablyDefects` below, which is the paper's notion —
`ProvablyDefects.defects` is the one-way implication, and there is no converse.
Where the strong form is available it is stated and used instead
(`defectBot_provably_defects`); this predicate remains the endpoint form in exactly
the three places where the strong form is *not available in `GL` at all*, for a
reason that is itself proved here:

* `fairBot_vs_defectBot` — `outcome fairBot defectBot` is GL-equivalent to `□⊥`
  (`outcome_fairBot_defectBot`), so the strong form is `GL ⊢ ∼□⊥`, i.e. `GL`
  proving its own consistency;
* `prudentBot_vs_defectBot` — likewise GL-equivalent to `□⊥`
  (`outcome_prudentBot_defectBot`);
* `prudentBot_vs_cooperateBot` — GL-equivalent to `□□⊥`
  (`outcome_prudentBot_cooperateBot`), so the strong form is `GL ⊢ ∼□□⊥`,
  i.e. `GL` proving `Con(PA+1)`.

`unprovable_neg_box_bot` and `unprovable_neg_box_box_bot` show `GL` proves neither,
and `fairBot_not_provably_defects_defectBot`,
`prudentBot_not_provably_defects_defectBot` and
`prudentBot_not_provably_defects_cooperateBot` land the consequence: on those three
endpoints the weak form is forced, not a shortcut. This tracks the paper exactly,
which states them as `PA+1 ⊢ [FB(DB)=D]`, `PA+1 ⊢ [PB(DB)=D]` and
`PA+2 ⊢ [PB(CB)=D]` — one and two reflection steps above the `PA` that `GL` models.
See the modeling boundary in `ModalAgents/README.md`. -/
def Defects (X Y : ModalAgent) : Prop := Modal.GL ⊬ outcome X Y

/-- X provably defects against Y: GL proves the outcome formula *false*. This is the
paper's notion of defection (`PA ⊢ [X(Y)=D]`), and unlike `Defects` it is a positive
`GL` claim, so it lifts to arithmetic through `ProvablyDefects.arithmeticLift`. -/
def ProvablyDefects (X Y : ModalAgent) : Prop := Modal.GL ⊢ ∼(outcome X Y)

/-- Provable defection implies defection, by consistency of `GL`. The converse fails,
and for the three endpoints listed at `Defects` it fails unavoidably. -/
lemma ProvablyDefects.defects {X Y : ModalAgent} (h : ProvablyDefects X Y) :
    Defects X Y := fun hc =>
  (inferInstance : Consistent Modal.GL).not_inconsistent
    (fun _ => ⟨efq ⨀ (h.some ⨀ hc.some)⟩)

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

/-- DefectBot *provably* defects against every opponent — the paper's own
`PA ⊢ [DB(X)=D]`, at full strength, since `outcome defectBot Y` is GL-equivalent to
`⊥`. Barasz states this as §2 prose in an unnumbered remark, so it carries no
paper-node annotation. -/
lemma defectBot_provably_defects (Y : ModalAgent) : ProvablyDefects defectBot Y := by
  have ⟨hβ⟩ := outcome_defectBot Y
  exact ⟨and₁ ⨀ hβ⟩

/-- DefectBot defects against every opponent — the weak form, for uniformity with the
other defection endpoints. `defectBot_provably_defects` is the strong form. -/
lemma defectBot_defects (Y : ModalAgent) : Defects defectBot Y :=
  (defectBot_provably_defects Y).defects

/-- CooperateBot cooperates with every opponent. Barasz states this as §2 prose
(`PA ⊢ [CB(X)=C]`, in an unnumbered remark), so it carries no paper-node
annotation. -/
lemma cooperateBot_cooperates (Y : ModalAgent) : Cooperates cooperateBot Y := by
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
lemma fairBot_vs_cooperateBot :
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
annotation.

DefectBot's half is at the paper's strength (`defectBot_provably_defects`). FairBot's
half is `Defects`, and it cannot be strengthened: `outcome fairBot defectBot` is
GL-equivalent to `□⊥` (`outcome_fairBot_defectBot`), so provable defection would be
`GL ⊢ ∼□⊥` — see `fairBot_not_provably_defects_defectBot`. The paper accordingly
states this one in `PA+1`. -/
lemma fairBot_vs_defectBot :
    Defects fairBot defectBot ∧ Defects defectBot fairBot := by
  have ⟨hα⟩ := outcome_fairBot defectBot
  have ⟨hβ⟩ := outcome_defectBot fairBot
  refine ⟨?_, defectBot_defects fairBot⟩
  intro ⟨ha⟩
  have h_box : Modal.GL ⊢! □(outcome defectBot fairBot) := and₁ ⨀ hα ⨀ ha
  have h_imp : Modal.GL ⊢! outcome defectBot fairBot 🡒 ⊥ := and₁ ⨀ hβ
  have : Modal.GL ⊢! □(⊥ : Modal.Formula ℕ) := axiomK' (nec h_imp) ⨀ h_box
  exact unprovable_box_bot ⟨this⟩

/-- **PrudentBot is unexploitable** — the first conjunct of the node below, and the
only one that quantifies over all opponents.

"`Y` exploits PrudentBot" is `Cooperates prudentBot Y ∧ Defects Y prudentBot`: the
sucker's payoff, PrudentBot cooperating into a defection. Its negation, for every `Y`,
is the implication stated here, since `Defects Y prudentBot` is
`Modal.GL ⊬ outcome Y prudentBot` and its classical negation is
`Cooperates Y prudentBot`.

The argument is the paper's, in modal form: PrudentBot cooperates only given a *proof*
that its opponent cooperates back, and the paper cashes that proof out by soundness of
`PA`. Here the corresponding step is `GL`'s unnecessitation rule `□φ / φ`, which is
admissible in `GL` (Foundation's `unnecessitation!`). So the conclusion needs no
soundness side-assumption and lands at full strength — `Cooperates`, hence liftable by
`Cooperates.arithmeticLift` — rather than at the weakened `¬ Defects`.

Paper node: Theorem 3.2 (§3). -/
theorem prudentBot_unexploitable (Y : ModalAgent) :
    Cooperates prudentBot Y → Cooperates Y prudentBot := by
  intro h
  have ⟨hα⟩ := outcome_prudentBot Y
  exact unnecessitation! ⟨and₁ ⨀ (and₁ ⨀ hα ⨀ h.some)⟩

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
that theorem's four conjuncts, so it carries no paper-node annotation.

DefectBot's half is at the paper's strength (`defectBot_provably_defects`).
PrudentBot's half is `Defects` and cannot be strengthened: `outcome prudentBot
defectBot` is GL-equivalent to `□⊥` (`outcome_prudentBot_defectBot`), so provable
defection would be `GL ⊢ ∼□⊥` — see `prudentBot_not_provably_defects_defectBot`.
That is why the paper's own statement of this step is in `PA+1`. -/
lemma prudentBot_vs_defectBot :
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

**Disclosed weakening, and its cause.** That conjunct is `PA+2 ⊢ [PB(CB)=D]` in the
paper — provable defection. Here it is `Defects`, i.e. `GL ⊬ outcome`. The gap is not
a shortcut: `outcome prudentBot cooperateBot` is GL-equivalent to `□□⊥`
(`outcome_prudentBot_cooperateBot`), so provable defection would be `GL ⊢ ∼□□⊥`, i.e.
`GL` proving `Con(PA+1)`, which it does not
(`prudentBot_not_provably_defects_cooperateBot`). `PA+2` is exactly the strength the
paper needs and `GL` lacks. The cooperation component is at full strength and lifts
through `Cooperates.arithmeticLift`. The node's remaining conjuncts are carried by
`prudentBot_unexploitable`, `prudentBot_vs_prudentBot` and `prudentBot_vs_fairBot`.

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

/-! ## The defection boundary

`defectBot_provably_defects` gives defection at the paper's strength. The three
remaining defection endpoints cannot: each of their outcome formulas is GL-equivalent
to an iterated `□⊥`, so the strong form asks `GL` for a consistency statement, and by
Gödel's second incompleteness theorem it has none. The equivalences below make that
exact, and the three `¬ ProvablyDefects` results are the consequence.

The reflection depth matches the paper step for step: `□⊥` here is `PA+1` there
(`PA+1 ⊢ [FB(DB)=D]`, `PA+1 ⊢ [PB(DB)=D]`) and `□□⊥` is `PA+2`
(`PA+2 ⊢ [PB(CB)=D]`). PrudentBot's own definition already reads its opponent's
behaviour against DefectBot under `∼□⊥ 🡒 ·` for precisely this reason — the paper's
remark after Theorem 3.2 is that the extra reflection step is load-bearing. -/

/-- Against DefectBot, FairBot's outcome is GL-equivalent to `□⊥`: FairBot cooperates
exactly when it can prove DefectBot's (refutable) cooperation. -/
lemma outcome_fairBot_defectBot :
    Modal.GL ⊢ outcome fairBot defectBot 🡘 □(⊥ : Modal.Formula ℕ) := by
  have ⟨hα⟩ := outcome_fairBot defectBot
  have ⟨hβ⟩ := outcome_defectBot fairBot
  exact ⟨E_trans hα (box_congruence hβ)⟩

/-- Against DefectBot, PrudentBot's outcome is GL-equivalent to `□⊥` as well: `□⊥`
already gives both of PrudentBot's conjuncts. -/
lemma outcome_prudentBot_defectBot :
    Modal.GL ⊢ outcome prudentBot defectBot 🡘 □(⊥ : Modal.Formula ℕ) := by
  have ⟨hα⟩ := outcome_prudentBot defectBot
  have ⟨hβ⟩ := outcome_defectBot prudentBot
  exact ⟨E_intro
    (C_trans (C_trans (and₁ ⨀ hα) and₁) (axiomK' (nec (and₁ ⨀ hβ))))
    (C_trans (CK_of_C_of_C C_box_of_boxBot C_box_of_boxBot) (and₂ ⨀ hα))⟩

/-- Against CooperateBot, PrudentBot's outcome is GL-equivalent to `□□⊥`: the first
conjunct is outright provable, and the second — PrudentBot's `PA+1` check that
CooperateBot defects against DefectBot — is what costs the second box. -/
lemma outcome_prudentBot_cooperateBot :
    Modal.GL ⊢ outcome prudentBot cooperateBot 🡘 □(□(⊥ : Modal.Formula ℕ)) := by
  have ⟨hα⟩ := outcome_prudentBot cooperateBot
  have ⟨hcbdb⟩ := cooperateBot_cooperates defectBot
  have ⟨hcbpb⟩ := cooperateBot_cooperates prudentBot
  refine ⟨E_intro (C_trans (C_trans (C_trans (and₁ ⨀ hα) and₂) (axiomK' (nec CCNNC)))
      (C_swap axiomK ⨀ nec hcbdb)) ?_⟩
  exact C_trans
    (CK_of_C_of_C (C_of_conseq (nec hcbpb)) (axiomK' (nec (C_swap CNC))))
    (and₂ ⨀ hα)

/-- FairBot's defection against DefectBot is **not** available at the paper's
strength: `GL ⊢ ∼(outcome fairBot defectBot)` is `GL ⊢ ∼□⊥`, which is `GL` proving
its own consistency. Hence `fairBot_vs_defectBot` states the weak `Defects` by
necessity, not by convenience. -/
lemma fairBot_not_provably_defects_defectBot : ¬ ProvablyDefects fairBot defectBot :=
  fun h => unprovable_neg_box_bot
    ⟨C_trans (and₂ ⨀ outcome_fairBot_defectBot.some) h.some⟩

/-- PrudentBot's defection against DefectBot is not available at the paper's strength,
for the same reason as `fairBot_not_provably_defects_defectBot`: it too reduces to
`GL ⊢ ∼□⊥`. The paper states this conjunct in `PA+1`. -/
lemma prudentBot_not_provably_defects_defectBot :
    ¬ ProvablyDefects prudentBot defectBot :=
  fun h => unprovable_neg_box_bot
    ⟨C_trans (and₂ ⨀ outcome_prudentBot_defectBot.some) h.some⟩

/-- PrudentBot's defection against CooperateBot — Theorem 3.2's last conjunct — is not
available at the paper's strength either: it reduces to `GL ⊢ ∼□□⊥`, i.e. `GL` proving
`Con(PA+1)`. The paper states this conjunct in `PA+2`. -/
lemma prudentBot_not_provably_defects_cooperateBot :
    ¬ ProvablyDefects prudentBot cooperateBot :=
  fun h => unprovable_neg_box_box_bot
    ⟨C_trans (and₂ ⨀ outcome_prudentBot_cooperateBot.some) h.some⟩

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

/-- Lift GL-provable *defection* through an arithmetical realization, by the same
soundness theorem. This is the payoff of stating defection as `ProvablyDefects` rather
than `Defects`: a negative claim that `GL` actually proves is still a `GL` theorem, so
it lifts, whereas `Defects` — a metatheoretic non-provability — has no counterpart
here and could not have one.

Paper node: Theorem 4.1 (§4). -/
theorem ProvablyDefects.arithmeticLift {X Y : ModalAgent} (h : ProvablyDefects X Y)
    {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
    {T U : FirstOrder.Theory L} [FirstOrder.ProvabilityAbstraction.Diagonalization T]
    [T ⪯ U] {𝔅 : FirstOrder.ProvabilityAbstraction.Provability T U} [𝔅.HBL]
    {f : _root_.Realization ℕ 𝔅} :
    U ⊢ f (GlFixedPointBridge.toSeq (∼(outcome X Y))) :=
  _root_.LogicGL.arithmetical_soundness'
    (GlFixedPointBridge.mem_logicGL_of_provable h)

/-- Example: the GL proof that FairBot cooperates with itself lifts to PA
under any standard arithmetical realization. -/
example (f : _root_.StandardRealization ℕ 𝗣𝗔) :
    𝗣𝗔 ⊢ f (GlFixedPointBridge.toSeq (outcome fairBot fairBot)) :=
  Cooperates.arithmeticLift fairBot_vs_fairBot

/-- Example: DefectBot's defection lifts to PA at the paper's strength — `PA` proves
the outcome formula false, not merely that it is unprovable. -/
example (Y : ModalAgent) (f : _root_.StandardRealization ℕ 𝗣𝗔) :
    𝗣𝗔 ⊢ f (GlFixedPointBridge.toSeq (∼(outcome defectBot Y))) :=
  ProvablyDefects.arithmeticLift (defectBot_provably_defects Y)
