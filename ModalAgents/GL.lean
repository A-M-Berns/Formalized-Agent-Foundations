/-
  GL toolkit: key lemmas in Gödel-Löb provability logic for the
  modal agent framework.

  The logic is `LogicGL` from the `ProvabilityLogic` package
  (`A ∈ LogicGL`, Hilbert-provability `⊢ʰ[GL] A`, with finite Kripke completeness
  and the fixed-point theorem). Provability is a `Prop` throughout this file.

  Main results:
  - `lob_rule`                  : if GL ⊢ □φ 🡒 φ then GL ⊢ φ
  - `lobian_circle`             : if GL ⊢ □A 🡒 B and GL ⊢ □B 🡒 A then GL ⊢ A ⋏ B
  - `unnecessitation`           : if GL ⊢ □φ then GL ⊢ φ   (via a root extension)
  - `unprovable_box_bot`        : GL ⊬ □⊥
  - `unprovable_box_box_bot`    : GL ⊬ □□⊥
  - `unprovable_neg_box_bot`    : GL ⊬ ∼□⊥      (Gödel's second incompleteness theorem)
  - `unprovable_neg_box_box_bot`: GL ⊬ ∼□□⊥
-/

import ProvabilityLogic.Logic.GL.Basic
import ProvabilityLogic.Logic.GL.Theorems
import ProvabilityLogic.Kripke.RootExtension

open LogicGL Formula

variable {φ ψ A A' B B' C : Formula ℕ}

/-! ## Membership and Hilbert provability -/

/-- `LogicGL` membership from a Hilbert proof. -/
lemma GL.of_provable (h : ⊢ʰ[GL] A) : A ∈ (LogicGL : Logic ℕ) := iff_provableHilbert.mpr h

/-- A Hilbert proof from `LogicGL` membership. -/
lemma GL.provable (h : A ∈ (LogicGL : Logic ℕ)) : ⊢ʰ[GL] A := iff_provableHilbert.mp h

lemma GL.mdp (h₁ : (A 🡒 B) ∈ (LogicGL : Logic ℕ)) (h₂ : A ∈ (LogicGL : Logic ℕ)) :
    B ∈ (LogicGL : Logic ℕ) :=
  GL.of_provable (ProvableHilbert.mdp (GL.provable h₁) (GL.provable h₂))

lemma GL.nec (h : A ∈ (LogicGL : Logic ℕ)) : (□A) ∈ (LogicGL : Logic ℕ) :=
  GL.of_provable (ProvableHilbert.nec (GL.provable h))

lemma GL.axiomK : (□(A 🡒 B) 🡒 (□A 🡒 □B)) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.modalK
lemma GL.axiomFour : (□A 🡒 □□A) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.modal4
lemma GL.axiomL : (□(□A 🡒 A) 🡒 □A) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.modalL
lemma GL.efq : (⊥ 🡒 A) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.efq
lemma GL.imp_id : (A 🡒 A) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.impId
lemma GL.and_left : ((A ⋏ B) 🡒 A) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.andElimL
lemma GL.and_right : ((A ⋏ B) 🡒 B) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.andElimR

lemma GL.imp_trans (h₁ : (A 🡒 B) ∈ (LogicGL : Logic ℕ)) (h₂ : (B 🡒 C) ∈ (LogicGL : Logic ℕ)) :
    (A 🡒 C) ∈ (LogicGL : Logic ℕ) :=
  GL.of_provable (ProvableHilbert.impTrans (GL.provable h₁) (GL.provable h₂))

/-- `A ⊢ B 🡒 A`: a theorem is a consequence of anything. -/
lemma GL.imp_of_mem (h : A ∈ (LogicGL : Logic ℕ)) : (B 🡒 A) ∈ (LogicGL : Logic ℕ) :=
  GL.of_provable (ProvableHilbert.af (GL.provable h))

lemma GL.and_intro (h₁ : A ∈ (LogicGL : Logic ℕ)) (h₂ : B ∈ (LogicGL : Logic ℕ)) :
    (A ⋏ B) ∈ (LogicGL : Logic ℕ) :=
  GL.of_provable (ProvableHilbert.andIntroRule (GL.provable h₁) (GL.provable h₂))

lemma GL.and_intro_imp (h₁ : (A 🡒 B) ∈ (LogicGL : Logic ℕ)) (h₂ : (A 🡒 C) ∈ (LogicGL : Logic ℕ)) :
    (A 🡒 (B ⋏ C)) ∈ (LogicGL : Logic ℕ) :=
  GL.of_provable (ProvableHilbert.ctxAndIntroRule (GL.provable h₁) (GL.provable h₂))

lemma GL.and_elim_left (h : (A ⋏ B) ∈ (LogicGL : Logic ℕ)) : A ∈ (LogicGL : Logic ℕ) :=
  GL.mdp GL.and_left h

lemma GL.and_elim_right (h : (A ⋏ B) ∈ (LogicGL : Logic ℕ)) : B ∈ (LogicGL : Logic ℕ) :=
  GL.mdp GL.and_right h

/-- Box is monotone: from `A 🡒 B` derive `□A 🡒 □B`. -/
lemma GL.box_imp (h : (A 🡒 B) ∈ (LogicGL : Logic ℕ)) : (□A 🡒 □B) ∈ (LogicGL : Logic ℕ) :=
  GL.mdp GL.axiomK (GL.nec h)

lemma GL.top : (⊤ : Formula ℕ) ∈ (LogicGL : Logic ℕ) := GL.of_provable ProvableHilbert.top

/-- Contraposition, as a GL theorem. -/
lemma GL.elimContra : ((∼A 🡒 ∼B) 🡒 (B 🡒 A)) ∈ (LogicGL : Logic ℕ) :=
  GL.of_provable ProvableHilbert.elimContra

/-- Contraposition, as a rule. -/
lemma GL.contra (h : (A 🡒 B) ∈ (LogicGL : Logic ℕ)) : (∼B 🡒 ∼A) ∈ (LogicGL : Logic ℕ) :=
  LogicGL.contra h

/-! ## Equivalences -/

lemma GL.iff_refl : (A 🡘 A) ∈ (LogicGL : Logic ℕ) := GL.and_intro GL.imp_id GL.imp_id

lemma GL.iff_symm (h : (A 🡘 B) ∈ (LogicGL : Logic ℕ)) : (B 🡘 A) ∈ (LogicGL : Logic ℕ) :=
  GL.and_intro (GL.and_elim_right h) (GL.and_elim_left h)

lemma GL.iff_trans (h₁ : (A 🡘 B) ∈ (LogicGL : Logic ℕ)) (h₂ : (B 🡘 C) ∈ (LogicGL : Logic ℕ)) :
    (A 🡘 C) ∈ (LogicGL : Logic ℕ) :=
  GL.and_intro (GL.imp_trans (GL.and_elim_left h₁) (GL.and_elim_left h₂))
    (GL.imp_trans (GL.and_elim_right h₂) (GL.and_elim_right h₁))

lemma GL.iff_mp (h : (A 🡘 B) ∈ (LogicGL : Logic ℕ)) (hA : A ∈ (LogicGL : Logic ℕ)) :
    B ∈ (LogicGL : Logic ℕ) :=
  GL.mdp (GL.and_elim_left h) hA

lemma GL.iff_mpr (h : (A 🡘 B) ∈ (LogicGL : Logic ℕ)) (hB : B ∈ (LogicGL : Logic ℕ)) :
    A ∈ (LogicGL : Logic ℕ) :=
  GL.mdp (GL.and_elim_right h) hB

/-- Negation is a congruence for `🡘`. -/
lemma GL.neg_congr (h : (A 🡘 B) ∈ (LogicGL : Logic ℕ)) : (∼A 🡘 ∼B) ∈ (LogicGL : Logic ℕ) :=
  GL.and_intro (GL.contra (GL.and_elim_right h)) (GL.contra (GL.and_elim_left h))

/-- Box is a congruence for `🡘`. -/
lemma GL.box_iff (h : (A 🡘 B) ∈ (LogicGL : Logic ℕ)) : (□A 🡘 □B) ∈ (LogicGL : Logic ℕ) :=
  GL.and_intro (GL.box_imp (GL.and_elim_left h)) (GL.box_imp (GL.and_elim_right h))

/-- The Hilbert-provable implication `(A' 🡒 A) 🡒 (B 🡒 B') 🡒 ((A 🡒 B) 🡒 (A' 🡒 B'))`:
contravariance in the antecedent, covariance in the consequent. -/
private lemma imp_mono_provable :
    ⊢ʰ[GL] (A' 🡒 A) 🡒 (B 🡒 B') 🡒 ((A 🡒 B) 🡒 (A' 🡒 B')) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have h₁ : {A', A 🡒 B, B 🡒 B', A' 🡒 A} ⊢ʰ[GL] A' 🡒 A := DeducibleHilbert.ofContext (by grind)
  have h₂ : {A', A 🡒 B, B 🡒 B', A' 🡒 A} ⊢ʰ[GL] A 🡒 B := DeducibleHilbert.ofContext (by grind)
  have h₃ : {A', A 🡒 B, B 🡒 B', A' 🡒 A} ⊢ʰ[GL] B 🡒 B' := DeducibleHilbert.ofContext (by grind)
  have h₄ : {A', A 🡒 B, B 🡒 B', A' 🡒 A} ⊢ʰ[GL] A' := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp h₃ (DeducibleHilbert.mdp h₂ (DeducibleHilbert.mdp h₁ h₄))

/-- Implication is a congruence for `🡘`. -/
lemma GL.imp_congr (h₁ : (A 🡘 A') ∈ (LogicGL : Logic ℕ)) (h₂ : (B 🡘 B') ∈ (LogicGL : Logic ℕ)) :
    ((A 🡒 B) 🡘 (A' 🡒 B')) ∈ (LogicGL : Logic ℕ) := by
  refine GL.and_intro ?_ ?_
  · exact GL.mdp (GL.mdp (GL.of_provable imp_mono_provable) (GL.and_elim_right h₁)) (GL.and_elim_left h₂)
  · exact GL.mdp (GL.mdp (GL.of_provable imp_mono_provable) (GL.and_elim_left h₁)) (GL.and_elim_right h₂)

/-- Modus ponens under a hypothesis: the `S` combinator. -/
lemma GL.under_mdp {H : Formula ℕ} (h₁ : (H 🡒 (A 🡒 B)) ∈ (LogicGL : Logic ℕ))
    (h₂ : (H 🡒 A) ∈ (LogicGL : Logic ℕ)) : (H 🡒 B) ∈ (LogicGL : Logic ℕ) :=
  GL.mdp (GL.mdp (GL.of_provable ProvableHilbert.implyS) h₁) h₂

/-- `🡘` is transitive, as a GL theorem. -/
lemma GL.iff_trans_provable :
    ((A 🡘 B) 🡒 (B 🡘 C) 🡒 (A 🡘 C)) ∈ (LogicGL : Logic ℕ) := by
  apply GL.of_provable
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have h₁ : {B 🡘 C, A 🡘 B} ⊢ʰ[GL] A 🡘 B := DeducibleHilbert.ofContext (by grind)
  have h₂ : {B 🡘 C, A 🡘 B} ⊢ʰ[GL] B 🡘 C := DeducibleHilbert.ofContext (by grind)
  have d₁ : {B 🡘 C, A 🡘 B} ⊢ʰ[GL] A 🡒 C :=
    DeducibleHilbert.impTrans (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL) h₁)
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL) h₂)
  have d₂ : {B 🡘 C, A 🡘 B} ⊢ʰ[GL] C 🡒 A :=
    DeducibleHilbert.impTrans (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimR) h₂)
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimR) h₁)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) d₁) d₂

/-- `🡘` is symmetric, as a GL theorem. -/
lemma GL.iff_symm_provable : ((A 🡘 B) 🡒 (B 🡘 A)) ∈ (LogicGL : Logic ℕ) := by
  apply GL.of_provable
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  have h : {A 🡘 B} ⊢ʰ[GL] A 🡘 B := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp
    (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro)
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimR) h))
    (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL) h)

/-- Implication congruence for `🡘`, as a GL theorem. -/
lemma GL.imp_congr_provable :
    ((A 🡘 A') 🡒 (B 🡘 B') 🡒 ((A 🡒 B) 🡘 (A' 🡒 B'))) ∈ (LogicGL : Logic ℕ) := by
  apply GL.of_provable
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have h₁ : {B 🡘 B', A 🡘 A'} ⊢ʰ[GL] A 🡘 A' := DeducibleHilbert.ofContext (by grind)
  have h₂ : {B 🡘 B', A 🡘 A'} ⊢ʰ[GL] B 🡘 B' := DeducibleHilbert.ofContext (by grind)
  have d₁ : {B 🡘 B', A 🡘 A'} ⊢ʰ[GL] (A 🡒 B) 🡒 (A' 🡒 B') :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable imp_mono_provable)
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimR) h₁))
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL) h₂)
  have d₂ : {B 🡘 B', A 🡘 A'} ⊢ʰ[GL] (A' 🡒 B') 🡒 (A 🡒 B) :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable imp_mono_provable)
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL) h₁))
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimR) h₂)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) d₁) d₂

/-- Implication congruence under a common hypothesis `H`. -/
lemma GL.imp_congr_under {H : Formula ℕ} (h₁ : (H 🡒 (A 🡘 A')) ∈ (LogicGL : Logic ℕ))
    (h₂ : (H 🡒 (B 🡘 B')) ∈ (LogicGL : Logic ℕ)) :
    (H 🡒 ((A 🡒 B) 🡘 (A' 🡒 B'))) ∈ (LogicGL : Logic ℕ) :=
  GL.under_mdp (GL.under_mdp (GL.imp_of_mem GL.imp_congr_provable) h₁) h₂

/-- Box collects conjunctions: `(□A ⋏ □B) 🡒 □(A ⋏ B)`. -/
lemma GL.collect_box_and : ((□A ⋏ □B) 🡒 □(A ⋏ B)) ∈ (LogicGL : Logic ℕ) := by
  have h : (□A 🡒 (□B 🡒 □(A ⋏ B))) ∈ (LogicGL : Logic ℕ) :=
    GL.imp_trans (GL.box_imp (GL.of_provable ProvableHilbert.andIntro)) GL.axiomK
  apply GL.of_provable
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  have hH : {□A ⋏ □B} ⊢ʰ[GL] □A ⋏ □B := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp
    (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (GL.provable h))
      (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimL) hH))
    (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andElimR) hH)

/-! ## Löb's rule and the Löbian circle -/

/-- Löb's rule: `GL ⊢ □φ 🡒 φ` gives `GL ⊢ φ`. -/
lemma lob_rule (h : (□φ 🡒 φ) ∈ (LogicGL : Logic ℕ)) : φ ∈ (LogicGL : Logic ℕ) :=
  GL.mdp h (GL.mdp GL.axiomL (GL.nec h))

/-- The Löbian circle: `GL ⊢ □A 🡒 B` and `GL ⊢ □B 🡒 A` give `GL ⊢ A ⋏ B`. -/
lemma lobian_circle
    (h₁ : (□A 🡒 B) ∈ (LogicGL : Logic ℕ)) (h₂ : (□B 🡒 A) ∈ (LogicGL : Logic ℕ)) :
    (A ⋏ B) ∈ (LogicGL : Logic ℕ) :=
  lob_rule <| GL.and_intro_imp
    (GL.imp_trans (GL.box_imp GL.and_right) h₂)
    (GL.imp_trans (GL.box_imp GL.and_left) h₁)

/-! ## Consistency and unnecessitation -/

/-- `GL` is consistent: `⊥` is refuted at the one-point model. -/
lemma GL.bot_not_mem : (⊥ : Formula ℕ) ∉ (LogicGL : Logic ℕ) :=
  not_mem_of_concrete_not_forces (Model.pointModel fun _ => False) (x := 0) fun h => h

/-- **Unnecessitation**: `GL ⊢ □φ` gives `GL ⊢ φ`. If `φ` fails at the root of some finite
`GL` model, extending that model by a fresh root below it refutes `□φ` at the new root. -/
lemma unnecessitation (h : (□φ) ∈ (LogicGL : Logic ℕ)) : φ ∈ (LogicGL : Logic ℕ) := by
  by_contra hφ
  obtain ⟨n, hn, M, hM, hroot⟩ : ∃ (n : ℕ) (_ : NeZero n) (M : RootedModel (Fin n) ℕ)
      (_ : M.IsFiniteGL), ¬ M.root.1 ⊩[M.toModel] φ := by
    by_contra hc
    push Not at hc
    exact hφ (iff_forces_root_concrete.mpr fun n _ M _ => hc n ‹_› M ‹_›)
  have hbox := iff_forces_root.mp h (M.extendRoot 1)
  have hrel : (M.extendRoot 1).toModel.Rel (M.extendRoot 1).root.1 (RootedModel.extendRoot.embed M.root.1) := by
    show (M.extendRoot 1).Rel' (.inr _) (.inl _)
    trivial
  exact hroot (RootedModel.extendRoot.same_forces_embed.mp (hbox _ hrel))

lemma unprovable_box_bot : (□(⊥ : Formula ℕ)) ∉ (LogicGL : Logic ℕ) :=
  fun h => GL.bot_not_mem (unnecessitation h)

lemma unprovable_box_box_bot : (□(□(⊥ : Formula ℕ))) ∉ (LogicGL : Logic ℕ) :=
  fun h => unprovable_box_bot (unnecessitation h)

/-- From `□⊥`, everything is provable-in-the-box. -/
lemma GL.box_of_boxBot : (□(⊥ : Formula ℕ) 🡒 □φ) ∈ (LogicGL : Logic ℕ) := GL.box_imp GL.efq

/-- **GL does not prove its own consistency.** `∼□⊥` is the modal reading of
`Con(PA)`, and this is Gödel's second incompleteness theorem in modal form: if
`GL ⊢ □⊥ 🡒 ⊥` then Löb's rule collapses `GL` to inconsistency. Everything the
paper proves in `PA+1` rather than `PA` runs into this. -/
lemma unprovable_neg_box_bot : (∼□(⊥ : Formula ℕ)) ∉ (LogicGL : Logic ℕ) :=
  fun h => GL.bot_not_mem (lob_rule h)

/-- `GL` does not prove `Con(PA+1)` either: `∼□□⊥` would give back `∼□⊥`, since
`□⊥ 🡒 □□⊥`. Everything the paper proves in `PA+2` runs into this. -/
lemma unprovable_neg_box_box_bot : (∼□(□(⊥ : Formula ℕ))) ∉ (LogicGL : Logic ℕ) :=
  fun h => unprovable_neg_box_bot (GL.imp_trans GL.box_of_boxBot h)
