/-
  Asymptotic comparison for Critch 2019.

  This file will contain the `≺` relation and the small collection of
  inequalities used to track bounded proof overheads.
-/

namespace LO.FirstOrder.Critch

def AsympLT (f g : Nat → Nat) : Prop :=
  ∀ M, 0 < M → ∃ N, ∀ n, N ≤ n → M * f n < g n

scoped infix:50 " ≺ " => AsympLT

end LO.FirstOrder.Critch
