/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is **FAF-authored**, mathematics included.  It is the one place in
`ShannonInformation/` where that is true: `API.lean` re-exports PFR's development, whereas
the lemmas below are proved here because the vendored tree has no countable-index
analogues of them.  See `ShannonInformation/README.md` and
`Condensation/notes/finite-range-generalization-plan.md` §3.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The nonnegative-family core of countable Shannon entropy

Every lemma here is a statement about an abstract family `p : ι → ℝ` of nonnegative reals.
No measure theory appears; the measure-side instantiation is
`ShannonInformation/FiniteEntropy/Defs.lean`.

## Why this layer exists, and why it is short

For a probability measure every term `negMulLog (p s)` of the entropy series is
**nonnegative** (`p s ∈ [0, 1]`, `Real.negMulLog_nonneg`).  So there is no sign-splitting
problem: summability is boundedness of the partial sums, `Summable.of_nonneg_of_le` is the
workhorse, and every `tsum` rearrangement in sight is a monotone one.  Consequently none of
these proofs needs Jensen's inequality, convexity, or an exhaustion argument over finite
subsets — `Real.negMulLog_le_one_sub_self` and `Real.log_le_sub_one_of_pos` do all the work
termwise.

## Main statements

* `negMulLog_tsum_le` — the **grouping bound**: `negMulLog (∑' t, p t) ≤ ∑' t, negMulLog (p t)`.
  This is `H[X] ≤ H[⟨X, Y⟩]` and `H[f ∘ X] ≤ H[X]` in atomic form, and it is what makes
  finite entropy *compose*.
* `tsum_negMulLog_eq_add` — the **local chain rule**: the entropy of a row splits into the
  row's mass term plus its mass times the entropy of the normalised row.
* `tsum_mul_log_div_nonneg` — **Gibbs' inequality, countable form**.  A termwise bound, not
  a Jensen argument; it is the source of subadditivity and of `0 ≤ I[X : Y]`.
* `negMulLog_le_add_of_le` — the termwise pair bound.  Summed over a product index it is
  simultaneously the closure of finite entropy under pairing *and* subadditivity.
* `summable_negMulLog_tsum_fiber` / `tsum_negMulLog_tsum_fiber_le` — grouping along an
  arbitrary map `g : ι → κ`, in summability and in value.

## Mathlib lemmas this layer deliberately does *not* restate

`Summable.of_nonneg_of_le`, `summable_prod_of_nonneg`, `summable_of_sum_le`,
`Summable.prod_factor`, `Summable.prod`, `Summable.tsum_prod'`, `HasSum.tsum_fiberwise` and
`Summable.tsum_subtype_le` all exist upstream and are used directly.
-/

@[expose] public section

namespace ShannonInformation

open Real

/-! ### C1 — the grouping bound -/

/-- **Grouping bound.**  `negMulLog` of a sum is at most the sum of the `negMulLog`s.

This is the atomic form of `H[X] ≤ H[⟨X, Y⟩]` and of `H[f ∘ X] ≤ H[X]`: reading `p t` as
the mass of the `t`-th cell of a group, the entropy contributed by the group as a whole is
no more than the entropy contributed by its cells. -/
lemma negMulLog_tsum_le {T : Type*} (p : T → ℝ) (h0 : ∀ t, 0 ≤ p t) (hsum : Summable p)
    (hent : Summable fun t ↦ negMulLog (p t)) :
    negMulLog (∑' t, p t) ≤ ∑' t, negMulLog (p t) := by
  set P := ∑' t, p t with hP
  have hP0 : 0 ≤ P := tsum_nonneg h0
  rcases eq_or_lt_of_le hP0 with h | hpos
  · have hall : ∀ t, p t = 0 := fun t ↦ by
      simpa using le_antisymm (h ▸ hsum.le_tsum t fun j _ ↦ h0 j) (h0 t)
    simp [negMulLog, ← h, hall]
  · have key : ∀ t, p t * (-Real.log P) ≤ negMulLog (p t) := by
      intro t
      rcases eq_or_lt_of_le (h0 t) with ht | ht
      · simp [negMulLog, ← ht]
      · have hpt : p t ≤ P := hsum.le_tsum t fun j _ ↦ h0 j
        have : Real.log (p t) ≤ Real.log P := Real.log_le_log ht hpt
        simp only [negMulLog, neg_mul]
        nlinarith [ht.le]
    calc negMulLog P = (∑' t, p t) * (-Real.log P) := by simp [negMulLog, hP]
      _ = ∑' t, p t * (-Real.log P) := (hsum.tsum_mul_right _).symm
      _ ≤ ∑' t, negMulLog (p t) := Summable.tsum_le_tsum key (hsum.mul_right _) hent

/-! ### C2 — the local chain rule -/

/-- Splitting `negMulLog` of a normalised mass into the unnormalised term and the
normalisation. -/
lemma negMulLog_div (p P : ℝ) (h0 : 0 ≤ p) (hP : 0 < P) :
    negMulLog (p / P) = P⁻¹ * negMulLog p + p * (Real.log P * P⁻¹) := by
  rcases eq_or_lt_of_le h0 with h | h
  · simp [negMulLog, ← h]
  · rw [negMulLog, negMulLog, Real.log_div (ne_of_gt h) (ne_of_gt hP)]
    field_simp
    ring

/-- **Local chain rule.**  The entropy of a single row `p` of a joint distribution equals
the entropy of its total mass plus that mass times the entropy of the normalised row.

Summed over the first coordinate this is the measure-level chain rule
`H[⟨X, Y⟩] = H[X] + H[Y | X]`, with no kernel detour. -/
lemma tsum_negMulLog_eq_add {T : Type*} (p : T → ℝ) (h0 : ∀ t, 0 ≤ p t) (hsum : Summable p)
    (hent : Summable fun t ↦ negMulLog (p t)) (hP : 0 < ∑' t, p t) :
    (∑' t, negMulLog (p t))
      = negMulLog (∑' t, p t) + (∑' t, p t) * ∑' t, negMulLog (p t / ∑' t, p t) := by
  set P := ∑' t, p t with hPdef
  have hPne : P ≠ 0 := ne_of_gt hP
  have hid : ∀ t, negMulLog (p t / P) = P⁻¹ * negMulLog (p t) + p t * (Real.log P * P⁻¹) :=
    fun t ↦ negMulLog_div _ _ (h0 t) hP
  have hs1 : Summable fun t ↦ P⁻¹ * negMulLog (p t) := hent.mul_left _
  have hs2 : Summable fun t ↦ p t * (Real.log P * P⁻¹) := hsum.mul_right _
  have key : (∑' t, negMulLog (p t / P))
      = P⁻¹ * (∑' t, negMulLog (p t)) + P * (Real.log P * P⁻¹) := by
    rw [tsum_congr hid, hs1.tsum_add hs2, hent.tsum_mul_left, hsum.tsum_mul_right]
  rw [key, negMulLog]
  field_simp
  ring

/-! ### C3 — Gibbs' inequality -/

/-- **Gibbs' inequality, countable form.**  The termwise bound `p - q ≤ p * log (p / q)`
carries the whole of subadditivity and of `0 ≤ I[X : Y]`, with no Jensen argument and no
convexity. -/
lemma tsum_mul_log_div_nonneg {ι : Type*} (p q : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 ≤ q i) (hac : ∀ i, q i = 0 → p i = 0) (hpsum : Summable p)
    (hqsum : Summable q) (hsum : Summable fun i ↦ p i * Real.log (p i / q i))
    (hmass : ∑' i, q i ≤ ∑' i, p i) :
    0 ≤ ∑' i, p i * Real.log (p i / q i) := by
  have term : ∀ i, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with hpi | hpi
    · simp [← hpi]
      exact hq0 i
    · have hqi : 0 < q i :=
        lt_of_le_of_ne (hq0 i) fun h ↦ absurd (hac i h.symm) (ne_of_gt hpi)
      have h1 : Real.log (q i / p i) ≤ q i / p i - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h2 : Real.log (q i / p i) = -Real.log (p i / q i) := by
        rw [← Real.log_inv]; congr 1; field_simp
      rw [h2] at h1
      have := mul_le_mul_of_nonneg_left h1 hpi.le
      field_simp at this
      nlinarith
  calc (0 : ℝ) ≤ ∑' i, p i - ∑' i, q i := by linarith
    _ = ∑' i, (p i - q i) := (hpsum.tsum_sub hqsum).symm
    _ ≤ ∑' i, p i * Real.log (p i / q i) :=
        Summable.tsum_le_tsum term (hpsum.sub hqsum) hsum

/-! ### The termwise pair bound

One inequality does two jobs: summed over `S × T` its left side is the joint entropy series
(so the bound closes finite entropy under pairing) and its right side sums to
`H[X] + H[Y]` (so the same bound *is* subadditivity).  Note it is not a bound by
nonnegative terms only: `a * b - r` is negative exactly when the pair is positively
correlated at `(x, y)`, which is why the summability argument splits it as a difference of
two summable nonnegative families rather than dominating it. -/

/-- The termwise pair bound.  With `r` the joint mass of a cell and `a`, `b` its two
marginal masses (so `r ≤ a` and `r ≤ b`),
`negMulLog r ≤ -(r * log a) + -(r * log b) + (a * b - r)`. -/
lemma negMulLog_le_add_of_le {r a b : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) (hrb : r ≤ b) :
    negMulLog r ≤ -(r * Real.log a) + -(r * Real.log b) + (a * b - r) := by
  rcases eq_or_lt_of_le hr with h | hrpos
  · have ha : 0 ≤ a := h ▸ hra
    have hb : 0 ≤ b := h ▸ hrb
    simp [negMulLog, ← h]
    positivity
  · have ha : 0 < a := lt_of_lt_of_le hrpos hra
    have hb : 0 < b := lt_of_lt_of_le hrpos hrb
    have h1 : Real.log (a * b / r) ≤ a * b / r - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (a * b / r) = Real.log a + Real.log b - Real.log r := by
      rw [Real.log_div (by positivity) (ne_of_gt hrpos), Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hrpos.le
    have h4 : r * (a * b / r - 1) = a * b - r := by field_simp
    rw [h4] at h3
    simp only [negMulLog]
    nlinarith

/-! ### Grouping along an arbitrary map -/

section Fiber

variable {ι κ : Type*} {p : ι → ℝ} {g : ι → κ}

/-- Regrouping a summable family along `g` and summing the fibre sums recovers the whole
sum.  A thin specialisation of `HasSum.tsum_fiberwise`, recorded because the fibre-sum
family is what the entropy statements below are stated over. -/
lemma summable_tsum_fiber (hp : Summable p) (g : ι → κ) :
    Summable fun k ↦ ∑' i : (g ⁻¹' {k} : Set ι), p i :=
  (hp.hasSum.tsum_fiberwise g).summable

lemma tsum_tsum_fiber (hp : Summable p) (g : ι → κ) :
    (∑' k, ∑' i : (g ⁻¹' {k} : Set ι), p i) = ∑' i, p i :=
  (hp.hasSum.tsum_fiberwise g).tsum_eq

/-- **Grouping preserves finite entropy.**  If the entropy series of a subprobability family
`p` converges, so does the entropy series of the pushforward family
`k ↦ ∑' i ∈ g ⁻¹' {k}, p i`. -/
lemma summable_negMulLog_tsum_fiber (h0 : ∀ i, 0 ≤ p i) (hp : Summable p)
    (hp1 : ∑' i, p i ≤ 1) (hent : Summable fun i ↦ negMulLog (p i)) (g : ι → κ) :
    Summable fun k ↦ negMulLog (∑' i : (g ⁻¹' {k} : Set ι), p i) := by
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) (summable_tsum_fiber hent g)
  · refine negMulLog_nonneg (tsum_nonneg fun i ↦ h0 i) ?_
    exact le_trans (Summable.tsum_subtype_le p _ h0 hp) hp1
  · exact negMulLog_tsum_le _ (fun i ↦ h0 i) (hp.subtype _) (hent.subtype _)

/-- **`H[g ∘ X] ≤ H[X]` in atomic form.** -/
lemma tsum_negMulLog_tsum_fiber_le (h0 : ∀ i, 0 ≤ p i) (hp : Summable p) (hp1 : ∑' i, p i ≤ 1)
    (hent : Summable fun i ↦ negMulLog (p i)) (g : ι → κ) :
    (∑' k, negMulLog (∑' i : (g ⁻¹' {k} : Set ι), p i)) ≤ ∑' i, negMulLog (p i) := by
  have hle : ∀ k, negMulLog (∑' i : (g ⁻¹' {k} : Set ι), p i)
      ≤ ∑' i : (g ⁻¹' {k} : Set ι), negMulLog (p i) :=
    fun k ↦ negMulLog_tsum_le _ (fun i ↦ h0 i) (hp.subtype _) (hent.subtype _)
  calc (∑' k, negMulLog (∑' i : (g ⁻¹' {k} : Set ι), p i))
      ≤ ∑' k, ∑' i : (g ⁻¹' {k} : Set ι), negMulLog (p i) :=
        Summable.tsum_le_tsum hle (summable_negMulLog_tsum_fiber h0 hp hp1 hent g)
          (summable_tsum_fiber hent g)
    _ = ∑' i, negMulLog (p i) := tsum_tsum_fiber hent g

end Fiber

end ShannonInformation
