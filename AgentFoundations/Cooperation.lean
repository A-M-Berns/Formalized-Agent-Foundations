/-
  Cooperation analysis for modal agents (Barasz, §3).

  `outcome X Y` is the paper's `ψ_{[X(Y)]}` (§4, Thm 4.7), the
  GL-sentence naming X's output against Y, constructed by the modal
  fixed-point theorem (§4, Thm 4.2 existence; Thm 4.3 uniqueness). We
  axiomatize the equation in one-step form; Thm 4.7's fully-unfolded
  form is equivalent by uniqueness. §3 only uses the equation as a
  black box.

  So far we work purely in GL. Thm 4.1 (arithmetic soundness of GL)
  lifts GL-level results to PA-level corollaries.

  Paper map:
  - `defectBot_defects`          §2 remark: `PA ⊢ [DB(X) = D]`
  - `cooperateBot_cooperates`    §2 remark: `PA ⊢ [CB(X) = C]`
  - `fairBot_vs_fairBot`         §3, Thm 3.1
  - `fairBot_vs_cooperateBot`    §3 (FB's flaw vs CB)
  - `fairBot_vs_defectBot`       §3 (FB unexploitability)
  - `prudentBot_vs_fairBot`      §3, Thm 3.2
  - `prudentBot_vs_defectBot`    §3, Thm 3.2
  - `prudentBot_vs_cooperateBot` §3, Thm 3.2
  - `prudentBot_vs_prudentBot`   §3, Thm 3.2
-/

import AgentFoundations.Agent
import Foundation.ProvabilityLogic.GL.Soundness

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

/-- Substitute atom 0 ↦ `β`, atoms 1,…,m ↦ `refs 0,…,refs (m-1)`;
atoms > m unchanged. -/
abbrev substFull (β : Formula ℕ) {m : ℕ} (refs : Fin m → Formula ℕ) : Substitution ℕ :=
  fun k => match k with
    | 0 => β
    | j + 1 => if h : j < m then refs ⟨j, h⟩ else .atom (j + 1)

/-! ## Modal agent outcome (Barasz, §4, Thm 4.7) -/

/-- `outcome X Y`: the paper's `ψ_{[X(Y)]}`. -/
axiom outcome : Agent → Agent → Formula ℕ

/-- Modal agent fixed-point equation, one-step form (Barasz, §4,
Thm 4.7; existence Thm 4.2, uniqueness Thm 4.3). -/
axiom outcome_fixed_point (X Y : Agent) :
    Modal.GL ⊢ outcome X Y 🡘
      X.formula⟦substFull (outcome Y X) (fun j => outcome Y (X.references j))⟧


def Cooperates (X Y : Agent) : Prop := Modal.GL ⊢ outcome X Y

def Defects (X Y : Agent) : Prop := Modal.GL ⊬ outcome X Y

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

/-- `outcome defectBot Y ↔ ⊥` for every Y. -/
lemma outcome_defectBot (Y : Agent) : Modal.GL ⊢ outcome defectBot Y 🡘 ⊥ := by
  have h := outcome_fixed_point defectBot Y
  simpa [defectBot_formula_substFull] using h

/-- `outcome cooperateBot Y ↔ ⊤` for every Y. -/
lemma outcome_cooperateBot (Y : Agent) : Modal.GL ⊢ outcome cooperateBot Y 🡘 ⊤ := by
  have h := outcome_fixed_point cooperateBot Y
  simpa [cooperateBot_formula_substFull] using h

/-- DefectBot defects against every opponent (Barasz, §2). -/
theorem defectBot_defects (Y : Agent) : Defects defectBot Y := by
  intro ⟨hb⟩
  have ⟨hβ⟩ := outcome_defectBot Y
  exact (inferInstance : Consistent Modal.GL).not_inconsistent
    (fun _ => ⟨efq ⨀ (and₁ ⨀ hβ ⨀ hb)⟩)

/-- CooperateBot cooperates with every opponent (Barasz, §2). -/
theorem cooperateBot_cooperates (Y : Agent) : Cooperates cooperateBot Y := by
  have ⟨h⟩ := outcome_cooperateBot Y
  exact ⟨and₂ ⨀ h ⨀ verum⟩

/-! ## Concrete cooperation: rank 0 -/

/-- FairBot cooperates with itself (Barasz, §3, Thm 3.1). -/
theorem fairBot_vs_fairBot : Cooperates fairBot fairBot := by
  have hα := outcome_fixed_point fairBot fairBot
  simp only [fairBot_formula_substFull] at hα
  have ⟨hα⟩ := hα
  have h : Modal.GL ⊢! outcome fairBot fairBot ⋏ outcome fairBot fairBot :=
    lobian_circle (and₂ ⨀ hα) (and₂ ⨀ hα)
  exact ⟨and₁ ⨀ h⟩

/-- FairBot vs CooperateBot: both cooperate (Barasz, §3). -/
theorem fairBot_vs_cooperateBot :
    Cooperates fairBot cooperateBot ∧ Cooperates cooperateBot fairBot := by
  have hα := outcome_fixed_point fairBot cooperateBot
  simp only [fairBot_formula_substFull] at hα
  have ⟨hα⟩ := hα
  have ⟨h_cb⟩ := cooperateBot_cooperates fairBot
  exact ⟨⟨and₂ ⨀ hα ⨀ nec h_cb⟩, cooperateBot_cooperates fairBot⟩

/-- FairBot vs DefectBot: both defect (Barasz, §3). -/
theorem fairBot_vs_defectBot :
    Defects fairBot defectBot ∧ Defects defectBot fairBot := by
  have hα := outcome_fixed_point fairBot defectBot
  simp only [fairBot_formula_substFull] at hα
  have ⟨hβ⟩ := outcome_defectBot fairBot
  refine ⟨?_, defectBot_defects fairBot⟩
  intro ⟨ha⟩
  have ⟨hα⟩ := hα
  have h_box : Modal.GL ⊢! □(outcome defectBot fairBot) := and₁ ⨀ hα ⨀ ha
  have h_imp : Modal.GL ⊢! outcome defectBot fairBot 🡒 ⊥ := and₁ ⨀ hβ
  have : Modal.GL ⊢! □(⊥ : Formula ℕ) := axiomK' (nec h_imp) ⨀ h_box
  exact unprovable_box_bot ⟨this⟩

/-! ## Concrete cooperation: rank 1 -/

/-- PrudentBot vs FairBot: both cooperate (Barasz, §3, Thm 3.2). -/
theorem prudentBot_vs_fairBot :
    Cooperates prudentBot fairBot ∧ Cooperates fairBot prudentBot := by
  have hα := outcome_fixed_point prudentBot fairBot
  simp only [prudentBot_formula_substFull] at hα
  have hFBvsPB := outcome_fixed_point fairBot prudentBot
  simp only [fairBot_formula_substFull] at hFBvsPB
  have hFBvsDB := outcome_fixed_point fairBot defectBot
  simp only [fairBot_formula_substFull] at hFBvsDB
  have hDBvsFB := outcome_defectBot fairBot
  have ⟨hα⟩ := hα
  have ⟨hFBvsPB⟩ := hFBvsPB
  have ⟨hFBvsDB⟩ := hFBvsDB
  have ⟨hDBvsFB⟩ := hDBvsFB
  have h_FBvsDB_to_boxbot : Modal.GL ⊢! outcome fairBot defectBot 🡒 □(⊥ : Formula ℕ) :=
    C_trans (and₁ ⨀ hFBvsDB) (axiomK' (nec (and₁ ⨀ hDBvsFB)))
  have h_consist : Modal.GL ⊢! □(∼□(⊥ : Formula ℕ) 🡒 ∼(outcome fairBot defectBot)) :=
    nec (contra h_FBvsDB_to_boxbot)
  have h : Modal.GL ⊢! outcome prudentBot fairBot ⋏ outcome fairBot prudentBot :=
    lobian_circle (and₂ ⨀ hFBvsPB)
      (C_trans (CK_of_C_of_C C_id (C_of_conseq h_consist)) (and₂ ⨀ hα))
  exact ⟨⟨and₁ ⨀ h⟩, ⟨and₂ ⨀ h⟩⟩

/-- PrudentBot vs DefectBot: both defect (Barasz, §3, Thm 3.2). -/
theorem prudentBot_vs_defectBot :
    Defects prudentBot defectBot ∧ Defects defectBot prudentBot := by
  have hα := outcome_fixed_point prudentBot defectBot
  simp only [prudentBot_formula_substFull] at hα
  have ⟨hβ⟩ := outcome_defectBot prudentBot
  refine ⟨?_, defectBot_defects prudentBot⟩
  intro ⟨ha⟩
  have ⟨hα⟩ := hα
  have h_box : Modal.GL ⊢! □(outcome defectBot prudentBot) := and₁ ⨀ (and₁ ⨀ hα ⨀ ha)
  have h_imp : Modal.GL ⊢! outcome defectBot prudentBot 🡒 ⊥ := and₁ ⨀ hβ
  exact unprovable_box_bot ⟨axiomK' (nec h_imp) ⨀ h_box⟩

/-- PrudentBot vs CooperateBot: PB defects, CB cooperates (Barasz, §3, Thm 3.2). -/
theorem prudentBot_vs_cooperateBot :
    Defects prudentBot cooperateBot ∧ Cooperates cooperateBot prudentBot := by
  have hα := outcome_fixed_point prudentBot cooperateBot
  simp only [prudentBot_formula_substFull] at hα
  refine ⟨?_, cooperateBot_cooperates prudentBot⟩
  intro ⟨ha⟩
  have ⟨hα⟩ := hα
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
  have hα := outcome_fixed_point prudentBot prudentBot
  simp only [prudentBot_formula_substFull] at hα
  have hg := outcome_fixed_point prudentBot defectBot
  simp only [prudentBot_formula_substFull] at hg
  have hβ := outcome_defectBot prudentBot
  have ⟨hα⟩ := hα
  have ⟨hg⟩ := hg
  have ⟨hβ⟩ := hβ
  have h_g_to_boxbot : Modal.GL ⊢! outcome prudentBot defectBot 🡒 □(⊥ : Formula ℕ) :=
    C_trans (C_trans (and₁ ⨀ hg) and₁) (axiomK' (nec (and₁ ⨀ hβ)))
  have h_consist : Modal.GL ⊢! □(∼□(⊥:Formula ℕ) 🡒 ∼(outcome prudentBot defectBot)) :=
    nec (contra h_g_to_boxbot)
  have h₁ : Modal.GL ⊢! □(outcome prudentBot prudentBot) 🡒
      □(outcome prudentBot prudentBot) ⋏
      □(∼□(⊥:Formula ℕ) 🡒 ∼(outcome prudentBot defectBot)) :=
    CK_of_C_of_C C_id (C_of_conseq h_consist)
  exact ⟨lob_rule (C_trans h₁ (and₂ ⨀ hα))⟩

/-! ## Arithmetical lift to PA (Barasz, §4, Thm 4.1) -/

/-- Lift cooperation to PA-provability (Barasz, §4, Thm 4.1). Wraps
`LO.ProvabilityLogic.GL.arithmetical_soundness`; specialized to PA's
standard provability predicate, yields `PA ⊢ [X(Y) = C]`.

`Defects` does not lift symmetrically: `GL ⊬ A` only yields *some*
realization with `U ⊬ f A`, not unprovability under every realization. -/
theorem Cooperates.arithmeticLift {X Y : Agent} (h : Cooperates X Y)
    {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
    {T U : FirstOrder.Theory L} [FirstOrder.ProvabilityAbstraction.Diagonalization T]
    [T ⪯ U] {𝔅 : FirstOrder.ProvabilityAbstraction.Provability T U} [𝔅.HBL]
    {f : ProvabilityLogic.Realization 𝔅} : U ⊢ f (outcome X Y) :=
  ProvabilityLogic.GL.arithmetical_soundness h
