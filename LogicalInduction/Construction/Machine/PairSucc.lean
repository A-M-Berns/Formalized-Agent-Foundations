/-
# `Nat.unpair` as an iterated successor, with no square root

Stage 2A of the efficiency-model program (`LogicalInduction/notes/complexitylib-adoption.md`
Part VIII). Pure arithmetic — no machine, no tape, no complexity class.

**Why this file exists.** Mathlib defines

```
Nat.unpair n = let s := sqrt n
               if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)
```

and a register machine that follows that definition operationally needs an integer square
root, which the substrate audit priced at 300–500 lines of Hoare-specified machine on its
own. But the machine only has to be **extensionally** equal to `Nat.unpair`; it is under no
obligation to compute it the way Mathlib defines it.

`Nat.pair` enumerates pairs in shells indexed by `s = max a b`:

```
shell s :  (0,s) (1,s) … (s-1,s) (s,0) (s,1) … (s,s)
indices : s²   s²+1  …  s²+s-1  s²+s  …           s²+2s = (s+1)²-1
```

so the *successor* of a pair in this enumeration is a four-case comparison on `a` and `b`
with no arithmetic beyond `+1`. Iterating it `n` times from `(0,0)` therefore lands on
`Nat.unpair n` — and the machine needs only comparison and increment, both of which the
register library already supports.

This file proves that, so the machine layer can be built against `pairNext` instead of
against `sqrt`.

## Main results

- `pair_pairNext` — one successor step advances the pairing index by exactly one
- `pair_pairIter` — `n` steps from `(0,0)` reach a pair whose index is `n`
- `pairIter_eq_unpair` — hence the iteration *is* `Nat.unpair`, extensionally
- `pairIter_le` — both coordinates stay bounded by `n`, which is what bounds register sizes
  in the eventual machine

**Not a paper node**, and not FAF-specific: this is a fact about `Nat.pair` alone and is a
candidate for upstreaming to `complexitylib` or Mathlib.
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Ring

namespace LogicalInduction

/-- The successor of a pair in `Nat.pair`'s enumeration order.

Reading the shell picture above: inside the ascending leg `(·, s)` step the first coordinate;
at the corner turn to `(s, 0)`; inside the descending leg `(s, ·)` step the second; and at
the diagonal `(s, s)` open the next shell at `(0, s+1)`. -/
def pairNext : ℕ × ℕ → ℕ × ℕ
  | (a, b) =>
      if a < b then
        (if a + 1 < b then (a + 1, b) else (b, 0))
      else if b < a then (a, b + 1)
      else (0, a + 1)

/-- **One successor step advances the pairing index by exactly one.** -/
lemma pair_pairNext (a b : ℕ) :
    Nat.pair (pairNext (a, b)).1 (pairNext (a, b)).2 = Nat.pair a b + 1 := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · -- ascending leg: `a < b`
    by_cases hsucc : a + 1 < b
    · simp only [pairNext, if_pos hab, if_pos hsucc]
      simp only [Nat.pair, if_pos hab, if_pos hsucc]
      omega
    · -- corner: `a + 1 = b`, so the next pair is `(b, 0)`
      obtain rfl : b = a + 1 := by omega
      simp only [pairNext, if_pos hab, if_neg hsucc]
      simp only [Nat.pair, if_pos hab, if_neg (show ¬ a + 1 < 0 by omega)]
      ring
  · -- diagonal: `a = b`, open the next shell at `(0, a + 1)`
    subst hab
    simp only [pairNext, if_neg (lt_irrefl a)]
    simp only [Nat.pair, if_neg (lt_irrefl a), if_pos (show 0 < a + 1 by omega)]
    ring
  · -- descending leg: `b < a`
    simp only [pairNext, if_neg (Nat.not_lt.mpr hab.le), if_pos hab]
    simp only [Nat.pair, if_neg (Nat.not_lt.mpr hab.le),
      if_neg (show ¬ a < b + 1 by omega)]
    omega

/-- `n` successor steps from `(0, 0)`. -/
def pairIter : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => pairNext (pairIter n)

/-- **The iteration's index is the iteration count.** -/
lemma pair_pairIter : ∀ n : ℕ, Nat.pair (pairIter n).1 (pairIter n).2 = n
  | 0 => rfl
  | n + 1 => by
      show Nat.pair (pairNext (pairIter n)).1 (pairNext (pairIter n)).2 = n + 1
      have h := pair_pairNext (pairIter n).1 (pairIter n).2
      rw [pair_pairIter n] at h
      exact h

/-- **The iteration is `Nat.unpair`, extensionally.** Hence a machine that iterates the
successor transition computes `Nat.unpair` without ever computing a square root. -/
lemma pairIter_eq_unpair (n : ℕ) : pairIter n = Nat.unpair n := by
  conv_rhs => rw [← pair_pairIter n]
  rw [Nat.unpair_pair]

/-- Both coordinates stay bounded by the iteration count. This is what will bound the
register sizes in the machine implementation: after `n` steps neither coordinate exceeds
`n`, so every intermediate value is at most the input. -/
lemma pairIter_le (n : ℕ) : (pairIter n).1 ≤ n ∧ (pairIter n).2 ≤ n := by
  constructor
  · conv_rhs => rw [← pair_pairIter n]
    exact Nat.left_le_pair _ _
  · conv_rhs => rw [← pair_pairIter n]
    exact Nat.right_le_pair _ _

end LogicalInduction
