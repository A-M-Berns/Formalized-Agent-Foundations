/-
  GL toolkit: key lemmas in Gödel-Löb provability logic for the
  modal agent framework.

  Main results:
  - `lob_rule`              : if GL ⊢ □φ 🡒 φ then GL ⊢ φ
  - `lobian_circle`         : if GL ⊢ □A 🡒 B and GL ⊢ □B 🡒 A then GL ⊢ A ⋏ B
  - `unprovable_box_bot`    : GL ⊬ □⊥
  - `unprovable_box_box_bot`: GL ⊬ □□⊥
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
