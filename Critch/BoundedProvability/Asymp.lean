/-
  Asymptotic comparison for Critch 2019, §§2.5 and 4.

  This file intentionally contains only the `≺` relation and the small
  collection of facts needed for the bounded Löb proof.
-/

import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Log

namespace LO.FirstOrder.Critch

namespace Asymp

/-- Critch §2.5 asymptotic domination relation on meta-level proof bounds. -/
def LtAsymp (f g : Nat → Nat) : Prop :=
  ∀ M : Nat, ∃ N : Nat, ∀ n, N < n → M * f n < g n

/-- Eventual positivity, used for the zero sanity check. -/
def EventuallyPositive (g : Nat → Nat) : Prop :=
  ∃ N, ∀ n, N < n → 0 < g n

end Asymp

scoped infix:50 " ≺ " => Asymp.LtAsymp

/--
Integer logarithm base 2, used as the meta-level analogue of Critch's `lg(k)`
from §2.2.
-/
def lg (k : Nat) : Nat :=
  Nat.log 2 k

namespace Asymp

variable {f g h : Nat → Nat}

/-- Sanity check for Critch §2.5: zero is dominated by any eventually positive function. -/
lemma zero_ltAsymp (hg : EventuallyPositive g) : (fun _ => 0) ≺ g := by
  intro M
  rcases hg with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦ by simpa using hN n hn⟩

/-- Transitivity of `≺`, used repeatedly in Critch §4. -/
lemma trans (hfg : f ≺ g) (hgh : g ≺ h) : f ≺ h := by
  intro M
  rcases hfg M with ⟨N₁, hN₁⟩
  rcases hgh 1 with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  exact lt_trans
    (hN₁ n (lt_of_le_of_lt (Nat.le_max_left _ _) hn))
    (by simpa using hN₂ n (lt_of_le_of_lt (Nat.le_max_right _ _) hn))

private lemma mul_lt_two_pow_of_two_mul_le (M l : Nat) (hMl : 2 * M ≤ l) :
    M * l < 2 ^ l := by
  refine Nat.le_induction ?base ?step l hMl
  · have hbase := Nat.two_mul_sq_add_one_le_two_pow_two_mul M
    apply Nat.lt_of_succ_le
    change M * (2 * M) + 1 ≤ 2 ^ (2 * M)
    rw [show M * (2 * M) + 1 = 2 * M ^ 2 + 1 by
      rw [pow_two]
      ac_rfl]
    exact hbase
  · intro i hle ih
    have hi : i < 2 ^ i := Nat.lt_two_pow_self
    have hMle : M ≤ 2 ^ i :=
      le_trans (Nat.le_trans (Nat.le_mul_of_pos_left M (by decide : 0 < 2)) hle) hi.le
    calc
      M * (i + 1) = M * i + M := by rw [Nat.mul_succ]
      _ < 2 ^ i + 2 ^ i := Nat.add_lt_add_of_lt_of_le ih hMle
      _ = 2 ^ i * 2 := by rw [← two_mul, Nat.mul_comm]
      _ = 2 ^ (i + 1) := by rw [pow_succ]

private lemma add_lt_of_two_mul_lt {a b c : Nat} (ha : 2 * a < c) (hb : 2 * b < c) :
    a + b < c := by
  have hsum : 2 * a + 2 * b < c + c := Nat.add_lt_add ha hb
  have htwice : 2 * (a + b) < 2 * c := by
    rw [Nat.mul_add, two_mul c]
    exact hsum
  exact (Nat.mul_lt_mul_left (by decide : 0 < 2)).mp htwice

/-- Basic growth fact for Critch §4, step 1: `lg k ≺ k`. -/
lemma lg_ltAsymp_id : lg ≺ id := by
  intro M
  refine ⟨2 ^ (2 * M), fun n hn ↦ ?_⟩
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_trans (pow_pos (by decide : 0 < 2) _) hn)
  have hlog : 2 * M ≤ lg n := by
    exact Nat.le_log_of_pow_le Nat.one_lt_two hn.le
  exact lt_of_lt_of_le (mul_lt_two_pow_of_two_mul_le M (lg n) hlog)
    (Nat.pow_log_le_self 2 hn0)

/--
Closure under addition of dominated terms, used in Critch §4, steps 12 and 15
to combine proof-overhead terms.
-/
lemma add (hfh : f ≺ h) (hgh : g ≺ h) : (fun k => f k + g k) ≺ h := by
  intro M
  rcases hfh (2 * M) with ⟨N₁, hN₁⟩
  rcases hgh (2 * M) with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hf := hN₁ n (lt_of_le_of_lt (Nat.le_max_left _ _) hn)
  have hg := hN₂ n (lt_of_le_of_lt (Nat.le_max_right _ _) hn)
  have hf' : 2 * (M * f n) < h n := by
    rwa [Nat.mul_assoc] at hf
  have hg' : 2 * (M * g n) < h n := by
    rwa [Nat.mul_assoc] at hg
  have hadd := add_lt_of_two_mul_lt hf' hg'
  rwa [← Nat.mul_add] at hadd

/--
Fallback witness condition for Critch §4, step 1.

The concrete inverse/square-root construction is intentionally not formalized
here. Phase 4 can assume this condition and extract the required `g`.
-/
def HasIntermediateWitness (e f : Nat → Nat) : Prop :=
  ∃ g, lg ≺ g ∧ (fun k => e (g k)) ≺ f

/-- Extract the intermediate `g` required in Critch §4, step 1. -/
lemma exists_intermediate_witness {e f : Nat → Nat} (h : HasIntermediateWitness e f) :
    ∃ g, lg ≺ g ∧ (fun k => e (g k)) ≺ f :=
  h

/--
Unpack a concrete threshold from `f ≺ g`; used throughout Critch §4 when fixing
specific constants.
-/
lemma threshold (hfg : f ≺ g) (M : Nat) : ∃ N, ∀ n, N < n → M * f n < g n :=
  hfg M

end Asymp

end LO.FirstOrder.Critch
