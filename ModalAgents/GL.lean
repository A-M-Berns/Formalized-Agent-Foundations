/-
  GL toolkit: key lemmas in Gödel-Löb provability logic for the
  modal agent framework.

  Main results:
  - `lob_rule`                  : if GL ⊢ □φ 🡒 φ then GL ⊢ φ
  - `lobian_circle`             : if GL ⊢ □A 🡒 B and GL ⊢ □B 🡒 A then GL ⊢ A ⋏ B
  - `unprovable_box_bot`        : GL ⊬ □⊥
  - `unprovable_box_box_bot`    : GL ⊬ □□⊥
  - `unprovable_neg_box_bot`    : GL ⊬ ∼□⊥      (Gödel's second incompleteness theorem)
  - `unprovable_neg_box_box_bot`: GL ⊬ ∼□□⊥
-/

import Foundation.Modal.Kripke.Logic.GL.Unnecessitation

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

variable {φ A B : Formula ℕ}

def lob_rule (h : Modal.GL ⊢! □φ 🡒 φ) : Modal.GL ⊢! φ :=
  h ⨀ (axiomL ⨀ (nec h))

def lobian_circle
    (h₁ : Modal.GL ⊢! □A 🡒 B) (h₂ : Modal.GL ⊢! □B 🡒 A) : Modal.GL ⊢! A ⋏ B :=
  let key : Modal.GL ⊢! □(A ⋏ B) 🡒 A ⋏ B :=
    C_trans axiomM (CK_of_C_of_C (C_trans and₂ h₂) (C_trans and₁ h₁))
  lob_rule key

lemma unprovable_box_bot : Modal.GL ⊬ □(⊥ : Formula ℕ) :=
  fun h => (unnecessitation! h).elim fun hbot =>
    (inferInstance : Consistent Modal.GL).not_inconsistent (fun _ => ⟨efq ⨀ hbot⟩)

lemma unprovable_box_box_bot : Modal.GL ⊬ □(□(⊥ : Formula ℕ)) :=
  fun h => unprovable_box_bot (unnecessitation! h)

/-- From `□⊥`, everything is provable-in-the-box. -/
def C_box_of_boxBot : Modal.GL ⊢! □(⊥ : Formula ℕ) 🡒 □φ := axiomK' (nec efq)

/-- **GL does not prove its own consistency.** `∼□⊥` is the modal reading of
`Con(PA)`, and this is Gödel's second incompleteness theorem in modal form: if
`GL ⊢ □⊥ 🡒 ⊥` then Löb's rule collapses `GL` to inconsistency. Everything the
paper proves in `PA+1` rather than `PA` runs into this. -/
lemma unprovable_neg_box_bot : Modal.GL ⊬ ∼□(⊥ : Formula ℕ) :=
  fun h => (inferInstance : Consistent Modal.GL).not_inconsistent
    (fun _ => ⟨efq ⨀ lob_rule h.some⟩)

/-- `GL` does not prove `Con(PA+1)` either: `∼□□⊥` would give back `∼□⊥`, since
`□⊥ 🡒 □□⊥`. Everything the paper proves in `PA+2` runs into this. -/
lemma unprovable_neg_box_box_bot : Modal.GL ⊬ ∼□(□(⊥ : Formula ℕ)) :=
  fun h => unprovable_neg_box_bot ⟨C_trans C_box_of_boxBot h.some⟩
