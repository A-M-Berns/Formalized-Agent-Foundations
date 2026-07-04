/-
# Efficient-computability infrastructure (`dd:fuel`) — prec-free fuel combinators

Certifying that a *responsive* trader is efficiently computable (`def:ec`) means exhibiting a
`Nat.Partrec.Code` and a polynomial `evaln` fuel budget that reproduces the encoded day-`n`
strategy. The obstacle was fuel accounting through `Nat.pair` — but with the `Nat.pair`-tagged
`EF` encoding (`Criterion.lean`), the strategy-encoding function is a tree of the interpreter's
**prec-free** primitives (`const`/`left`/`right`/`pair`/`comp`), and for those `evaln` does not
decrement fuel: a single budget exceeding every intermediate value evaluates the whole tree.

This file packages that as a `Fueled c f b` predicate — "`c` computes `f` within `b n` fuel" —
closed under the primitives, so a trader's code is assembled compositionally and its fuel bound
falls out. Composing const/pair over a fixed template gives a bound polynomial in `n`, which is
exactly `EfficientlyComputable`. Faithfulness is untouched: this is the paper's poly-time
`def:ec`, only now with a tractable membership proof.
-/
import LogicalInduction.Criterion

namespace LogicalInduction

open Nat.Partrec.Code

/-- `c` computes `f` on every input `n` within `b n` fuel of the clocked interpreter. -/
def Fueled (c : Nat.Partrec.Code) (f : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  ∀ n, evaln (b n) c n = some (f n)

theorem Fueled.mono {c : Nat.Partrec.Code} {f b b' : ℕ → ℕ}
    (h : Fueled c f b) (hb : ∀ n, b n ≤ b' n) : Fueled c f b' :=
  fun n => evaln_mono (hb n) (h n)

/-- Constant: `Code.const K` outputs `K` within `n + K + 1` fuel. -/
theorem fueled_const (K : ℕ) :
    Fueled (Nat.Partrec.Code.const K) (fun _ => K) (fun n => n + K + 1) :=
  fun n => evaln_const_self K n

/-- Left projection `n ↦ (unpair n).1`. -/
theorem fueled_left :
    Fueled Nat.Partrec.Code.left (fun n => n.unpair.1) (fun n => n + 1) := by
  intro n; show evaln (n + 1) Nat.Partrec.Code.left n = some n.unpair.1
  simp [evaln]

/-- Right projection `n ↦ (unpair n).2`. -/
theorem fueled_right :
    Fueled Nat.Partrec.Code.right (fun n => n.unpair.2) (fun n => n + 1) := by
  intro n; show evaln (n + 1) Nat.Partrec.Code.right n = some n.unpair.2
  simp [evaln]

/-- Successor `n ↦ n + 1`. -/
theorem fueled_succ :
    Fueled Nat.Partrec.Code.succ (fun n => n + 1) (fun n => n + 1) := by
  intro n; show evaln (n + 1) Nat.Partrec.Code.succ n = some (n + 1)
  simp [evaln]

/-- Pairing: `Code.pair` computes `Nat.pair (f n) (g n)` (a primitive — no `prec`, no fuel
decrement), so a shared budget `max (bf n) (bg n)` suffices. -/
theorem fueled_pair {cf cg : Nat.Partrec.Code} {f g bf bg : ℕ → ℕ}
    (hf : Fueled cf f bf) (hg : Fueled cg g bg) :
    Fueled (cf.pair cg) (fun n => Nat.pair (f n) (g n)) (fun n => max (bf n) (bg n)) := by
  intro n
  show evaln (max (bf n) (bg n)) (cf.pair cg) n = some (Nat.pair (f n) (g n))
  have hn : n < max (bf n) (bg n) := by
    have := evaln_bound (hf n); have := evaln_bound (hg n); omega
  obtain ⟨k, hk⟩ : ∃ k, max (bf n) (bg n) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hk]
  have hfn : evaln (k + 1) cf n = some (f n) := by
    rw [← hk]; exact evaln_mono (le_max_left _ _) (hf n)
  have hgn : evaln (k + 1) cg n = some (g n) := by
    rw [← hk]; exact evaln_mono (le_max_right _ _) (hg n)
  simp [evaln, Option.guard_eq_some', hfn, hgn, Seq.seq, Option.bind_eq_some_iff]
  omega

/-- Composition: `Code.comp cf cg` computes `f ∘ g`. The intermediate value `g n` is fed to
`cf`, so the budget is `max (bg n) (bf (g n))`. -/
theorem fueled_comp {cf cg : Nat.Partrec.Code} {f g bf bg : ℕ → ℕ}
    (hf : Fueled cf f bf) (hg : Fueled cg g bg) :
    Fueled (cf.comp cg) (fun n => f (g n)) (fun n => max (bg n) (bf (g n))) := by
  intro n
  show evaln (max (bg n) (bf (g n))) (cf.comp cg) n = some (f (g n))
  have hn : n < max (bg n) (bf (g n)) := by have := evaln_bound (hg n); omega
  obtain ⟨k, hk⟩ : ∃ k, max (bg n) (bf (g n)) = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  rw [hk]
  have hgn : evaln (k + 1) cg n = some (g n) := by
    rw [← hk]; exact evaln_mono (le_max_left _ _) (hg n)
  have hfn : evaln (k + 1) cf (g n) = some (f (g n)) := by
    rw [← hk]; exact evaln_mono (le_max_right _ _) (hf (g n))
  have hb2 := evaln_bound (hf (g n))
  have hm2 := le_max_right (bg n) (bf (g n))
  simp [evaln, Option.guard_eq_some', hgn, hfn, Option.bind_eq_some_iff]
  omega

/-- Identity `n ↦ n`, built from `pair left right` (`Nat.pair (unpair n).1 (unpair n).2 = n`). -/
theorem fueled_id :
    Fueled (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right) (fun n => n) (fun n => n + 1) := by
  have h := fueled_pair fueled_left fueled_right
  simpa [Nat.pair_unpair] using h.mono (fun n => by simp)

end LogicalInduction
