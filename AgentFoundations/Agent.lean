/-
  Modal agents over GL (Barasz, §4).

  A *modal agent of rank k* is determined by modal agents Y₁, …, Yₙ of
  rank < k and a fully modalized formula φ(p, q₁, …, qₙ) such that for
  every opponent Z,

      PA ⊢ [X(Z)] ↔ φ([Z(X)], [Z(Y₁)], …, [Z(Yₙ)]).

  (§4, Eq 4.1 and the unnumbered Definition on page 11.)

  "Fully modalized" = every propositional variable occurs inside a □;
  this syntactic condition is what makes the modal fixed-point theorem
  (§4, Thm 4.2 existence; Thm 4.3 uniqueness) applicable.

  Atoms of `formula`:
    atom 0       — "opponent cooperates with me"
    atom 1, …, n — "opponent cooperates with reference agent i"

  Concrete agents:
  - `cooperateBot` (§2, Algorithm 1)
  - `defectBot`    (§2, Algorithm 2)
  - `fairBot`      (§3, Algorithm 4)
  - `prudentBot`   (§3, Algorithm 5)
-/

import AgentFoundations.GL

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

/-! ## Agents -/

/-- A modal agent (Barasz, §4, Definition p. 11): a GL formula together
with a finite family of *reference agents*. Atom 0 of `formula` is
"opponent cooperates with me"; atoms 1, …, `arity` are "opponent
cooperates with reference i". `modalized` requires every such atom
under a □.

References use `Fin arity → Agent` to avoid Lean's nested-inductive
restriction on `List Agent`. -/
inductive Agent : Type where
  | mk (formula : Formula ℕ) (arity : ℕ)
      (references : Fin arity → Agent)
      (modalized : ∀ i, i ≤ arity → Modalized i formula) : Agent

namespace Agent

def formula : Agent → Formula ℕ
  | .mk f _ _ _ => f

def arity : Agent → ℕ
  | .mk _ n _ _ => n

def references : (X : Agent) → Fin X.arity → Agent
  | .mk _ _ r _ => r

/-- Rank of a modal agent (Barasz, §4): 0 if no references, else
1 + max rank of references. Distinct from `arity`. -/
def rank : Agent → ℕ
  | .mk _ 0     _ _ => 0
  | .mk _ (_+1) r _ => (Finset.univ.sup fun i => rank (r i)) + 1

/-- Build a rank-0 agent; default tactic discharges `Modalized 0` for
the standard bot formulas. -/
def mkRank0 (φ : Formula ℕ)
    (h : Modalized 0 φ := by simp [Modalized]) : Agent :=
  .mk φ 0 Fin.elim0 (rank0_modalized h)

end Agent

/-! ## Concrete agents -/

/-- CooperateBot: always cooperates, φ = ⊤ (Barasz, §2, Alg 1). -/
def cooperateBot : Agent := .mkRank0 ⊤

/-- DefectBot: always defects, φ = ⊥ (Barasz, §2, Alg 2). -/
def defectBot : Agent := .mkRank0 ⊥

/-- FairBot: cooperates iff it can *prove* the opponent cooperates,
φ = □(atom 0) (Barasz, §3, Alg 4). -/
def fairBot : Agent := .mkRank0 (□(.atom 0 : Formula ℕ))

/-- PrudentBot: φ = □(atom 0) ⋏ □(∼□⊥ 🡒 ∼(atom 1)), atom 1 referencing
DefectBot (Barasz, §3, Alg 5). In GL, `□(∼□⊥ 🡒 ψ)` encodes `PA+1 ⊢ ψ`. -/
def prudentBot : Agent :=
  .mk (□(.atom 0 : Formula ℕ) ⋏ □(∼□⊥ 🡒 ∼(.atom 1 : Formula ℕ)))
    1 (fun _ => defectBot)
    (fun i hi => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl <;> simp [Modalized])
