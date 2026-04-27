/-
  Modal agents over GL (Barasz, §4).

  The paper defines modal agents arithmetically. This file formalizes the
  corresponding GL-level structure: a fully modalized formula together with
  lower-rank reference agents.

  Atom 0 means "the opponent cooperates with this agent"; atom i + 1 means
  "the opponent cooperates with reference i".

  The concrete agents are CooperateBot, DefectBot, FairBot, and PrudentBot.
-/

import Barasz.GL

open LO LO.Modal

/-! ## Fully modalized formulas -/

/-- *Modalized in atom n* (Barasz, §4): every occurrence of atom n
appears inside a □. -/
def Modalized (n : ℕ) : Formula ℕ → Prop
  | .atom i   => i ≠ n
  | .falsum   => True
  | .imp φ ψ  => Modalized n φ ∧ Modalized n ψ
  | .box _    => True

lemma rank0_modalized {φ : Formula ℕ} (h : Modalized 0 φ) :
    ∀ i, i ≤ 0 → Modalized i φ := by
  intro i hi; rwa [Nat.le_zero.mp hi]

/-- If atom n doesn't appear in φ at all, then φ is trivially modalized in n. -/
lemma modalized_of_notMem_atoms {n : ℕ} :
    ∀ {φ : Formula ℕ}, n ∉ φ.atoms → Modalized n φ
  | .atom a, h => by
    simp only [Formula.atoms, Finset.mem_singleton] at h
    exact fun heq => h heq.symm
  | .falsum, _ => trivial
  | .imp _ _, h => by
    simp only [Formula.atoms, Finset.mem_union, not_or] at h
    exact ⟨modalized_of_notMem_atoms h.1, modalized_of_notMem_atoms h.2⟩
  | .box _, _ => trivial

/-- If φ is modalized in n and every σ(k) with k ≠ n is modalized in n, then
φ⟦σ⟧ is modalized in n. No condition on σ(n) — its content always lands under
a □ because φ had all atom-n occurrences boxed. -/
lemma modalized_subst {n : ℕ} {σ : Substitution ℕ}
    (hσ : ∀ k, k ≠ n → Modalized n (σ k)) :
    ∀ {φ : Formula ℕ}, Modalized n φ → Modalized n (φ⟦σ⟧)
  | .atom a, h => hσ a h
  | .falsum, _ => trivial
  | .imp _ _, h => ⟨modalized_subst hσ h.1, modalized_subst hσ h.2⟩
  | .box _, _ => trivial

/-! ## Modal agents -/

/-- A modal agent (Barasz, §4, Definition p. 11): a GL formula together
with a finite family of reference agents. Atom 0 of `formula` is
"opponent cooperates with me." Atom `i + 1` is "opponent cooperates
with reference `i`". All relevant atoms must occur under a □. -/
inductive ModalAgent : Type where
  | mk (formula : Formula ℕ) (arity : ℕ)
      (references : Fin arity → ModalAgent)
      (modalized : ∀ i, i ≤ arity → Modalized i formula) : ModalAgent

namespace ModalAgent

def formula : ModalAgent → Formula ℕ
  | .mk f _ _ _ => f

def arity : ModalAgent → ℕ
  | .mk _ n _ _ => n

def references : (X : ModalAgent) → Fin X.arity → ModalAgent
  | .mk _ _ r _ => r

def modalized : (X : ModalAgent) → ∀ i, i ≤ X.arity → Modalized i X.formula
  | .mk _ _ _ m => m

/-- Rank of a modal agent (Barasz, §4): 0 if there are no references, otherwise
1 + max rank of references. -/
def rank : ModalAgent → ℕ
  | .mk _ 0     _ _ => 0
  | .mk _ (_+1) r _ => (Finset.univ.sup fun i => rank (r i)) + 1

/-- A reference has strictly smaller rank than its parent agent. -/
lemma rank_ref_lt : ∀ (X : ModalAgent) (i : Fin X.arity), (X.references i).rank < X.rank
  | .mk _ (_+1) r _, i => by
    show (r i).rank < (Finset.univ.sup fun j => (r j).rank) + 1
    exact Nat.lt_succ_of_le
      (Finset.le_sup (f := fun j => (r j).rank) (Finset.mem_univ i))

/-- Rank-0 modal agents have no reference agents. -/
lemma arity_eq_zero_of_rank_eq_zero {X : ModalAgent} (h : X.rank = 0) : X.arity = 0 := by
  cases X with
  | mk _ n _ _ =>
    cases n with
    | zero => rfl
    | succ _ =>
      simp [rank] at h

/-- Build a rank-0 agent. -/
def mkRank0 (φ : Formula ℕ)
    (h : Modalized 0 φ := by simp [Modalized]) : ModalAgent :=
  .mk φ 0 Fin.elim0 (rank0_modalized h)

end ModalAgent

/-! ## Concrete agents -/

/-- CooperateBot: always cooperates, φ = ⊤ (Barasz, §2, Alg 1). -/
def cooperateBot : ModalAgent := .mkRank0 ⊤

/-- DefectBot: always defects, φ = ⊥ (Barasz, §2, Alg 2). -/
def defectBot : ModalAgent := .mkRank0 ⊥

/-- FairBot: cooperates iff it can prove the opponent cooperates, φ = □(atom 0) (Barasz, §3, Alg 4). -/
def fairBot : ModalAgent := .mkRank0 (□(.atom 0 : Formula ℕ))

/-- PrudentBot cooperates with `Y` iff PA proves that `Y` cooperates with
PrudentBot and PA+1 proves that `Y` does not cooperate with DefectBot
(Barasz, §3, Alg 5). In GL, the PA+1 condition is represented as
`□(∼□⊥ 🡒 ψ)`. -/
def prudentBot : ModalAgent :=
  .mk (□(.atom 0 : Formula ℕ) ⋏ □(∼□⊥ 🡒 ∼(.atom 1 : Formula ℕ)))
    1 (fun _ => defectBot)
    (fun i hi => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl <;> simp [Modalized])
