/-
# `thm:ec` — Expectations Converge (the bundle-hysteresis trader, Phase D2)

Paper (`main.tex` 1688): the day-`n` expectation `𝔼ₙ(X)` of any `[0,1]`-LUV converges.

The proof is `thm:con`'s again, with bundle bookkeeping. If `𝔼ₙ(X)` oscillates across a
rational gap `[a, b]`, the exploiter runs the **hysteresis** state of `thm:con` — but
driven by the *expectation feature* `𝔼ₙ(X)` (an `EF`: a rational multiple of a sum of
`price` nodes on `X`'s day-`n` thresholds) instead of a single price, and trading the
**day-`n` threshold bundle** `{(1/n)·⌜X > i/n⌝}_{i<n}` instead of a single sentence.

Two wrinkles versus `thm:con`, both visible in the statement:

1. **Bundles bought on day `n` pay off as day-`n` bundles.** In a plausible world `v`
   valuing `X` at `x` (`hval` — the D1 linkage hypothesis, disclosed type-`(c)`), the
   day-`n` bundle pays `X.expectApprox v.payout n ∈ [x, x + 1/n]` (`lem:conluvapprox`),
   so the `thm:con` accounting picks up an error `Σ |Δₙ|/n ≤ (2B₋ + 1)/n₀` — hence
2. **the trader is gated to start at a day `n₀` with `2/n₀ ≤ γ/2`** (γ the hysteresis
   margin), via the `δ = 0` degenerate-`ctsind` padding of the B2 ladder, so the gain
   `γ·B₋` keeps a positive coefficient `γ/2` after absorbing the error.

The feature-generic signal/state layer (`buyIndF`/`sellIndF`/`hystChain`) mirrors
`Hysteresis.lean` with `.price φ n` abstracted to an arbitrary feature `EF`; `thm:con`'s
concrete lemmas are untouched.
-/
import LogicalInduction.Properties.Coherence
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.Expectations

namespace LogicalInduction

open Filter Topology

/-! ### Feature-generic continuous threshold indicators

`Hysteresis.lean`'s signals with the priced object abstracted: `buyIndF e a δ` ramps
from `1` (when `e ≤ a`) to `0` (when `e ≥ a + δ`); `sellIndF e b δ` from `0` (at
`b − δ`) to `1` (at `b`). At `δ = 0` both are identically `0` (`1/0 = 0` in `ℚ`) — the
gate padding. -/

/-- Buy signal on the feature `e`: `1` when `e ≤ a`, ramps to `0` at `a + δ`. -/
def buyIndF (e : EF) (a δ : ℚ) : EF :=
  clip01 (.mul (.add (.const (a + δ)) (.mul (.const (-1)) e)) (.const (1/δ)))

/-- Sell signal on the feature `e`: `1` when `e ≥ b`, ramps to `0` at `b − δ`. -/
def sellIndF (e : EF) (b δ : ℚ) : EF :=
  clip01 (.mul (.add e (.const (δ - b))) (.const (1/δ)))

lemma buyIndF_denote (e : EF) (a δ : ℚ) (V : History) :
    (buyIndF e a δ).denote V
      = max 0 (min 1 (((a : ℝ) + δ - e.denote V) * (1/(δ : ℝ)))) := by
  simp only [buyIndF, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    Pi.mul_apply, Pi.add_apply]
  push_cast; ring_nf

lemma sellIndF_denote (e : EF) (b δ : ℚ) (V : History) :
    (sellIndF e b δ).denote V
      = max 0 (min 1 ((e.denote V - ((b : ℝ) - δ)) * (1/(δ : ℝ)))) := by
  simp only [sellIndF, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    Pi.mul_apply, Pi.add_apply]
  push_cast; ring_nf

@[simp] theorem buyIndF_rank (e : EF) (a δ : ℚ) : (buyIndF e a δ).rank = e.rank := by
  simp [buyIndF, EF.rank]

@[simp] theorem sellIndF_rank (e : EF) (b δ : ℚ) : (sellIndF e b δ).rank = e.rank := by
  simp [sellIndF, EF.rank]

section SignalFacts

variable {e : EF} {a b δ : ℚ} {V : History}

lemma buyIndF_mem (e : EF) (a δ : ℚ) (V : History) :
    0 ≤ (buyIndF e a δ).denote V ∧ (buyIndF e a δ).denote V ≤ 1 := by
  rw [buyIndF_denote]; exact ⟨clipVal_nonneg _, clipVal_le_one _⟩

lemma sellIndF_mem (e : EF) (b δ : ℚ) (V : History) :
    0 ≤ (sellIndF e b δ).denote V ∧ (sellIndF e b δ).denote V ≤ 1 := by
  rw [sellIndF_denote]; exact ⟨clipVal_nonneg _, clipVal_le_one _⟩

lemma buyIndF_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (buyIndF e a δ).denote V) :
    e.denote V < (a : ℝ) + δ := by
  rw [buyIndF_denote] at h
  have := clipVal_pos_imp h
  nlinarith [mul_pos (show (0:ℝ) < 1/(δ:ℝ) by positivity) hδ]

lemma buyIndF_eq_one (hδ : 0 < (δ : ℝ)) (h : e.denote V < (a : ℝ)) :
    (buyIndF e a δ).denote V = 1 := by
  rw [buyIndF_denote]
  refine clipVal_eq_one ?_
  have h1 : (δ:ℝ) ≤ (a:ℝ) + δ - e.denote V := by linarith
  calc (1:ℝ) = (δ:ℝ) * (1/(δ:ℝ)) := by field_simp
    _ ≤ ((a:ℝ) + δ - e.denote V) * (1/(δ:ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1; positivity

lemma buyIndF_eq_zero (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ)
    (h : (b : ℝ) < e.denote V) : (buyIndF e a δ).denote V = 0 := by
  rw [buyIndF_denote]
  refine clipVal_eq_zero ?_
  have hδ' : (0:ℝ) < δ := hδ
  have : (a:ℝ) + δ - e.denote V ≤ 0 := by nlinarith
  have h1δ : (0:ℝ) ≤ 1/(δ:ℝ) := by positivity
  nlinarith

lemma sellIndF_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (sellIndF e b δ).denote V) :
    (b : ℝ) - δ < e.denote V := by
  rw [sellIndF_denote] at h
  have := clipVal_pos_imp h
  nlinarith [mul_pos (show (0:ℝ) < 1/(δ:ℝ) by positivity) hδ]

lemma sellIndF_eq_one (hδ : 0 < (δ : ℝ)) (h : (b : ℝ) < e.denote V) :
    (sellIndF e b δ).denote V = 1 := by
  rw [sellIndF_denote]
  refine clipVal_eq_one ?_
  have h1 : (δ:ℝ) ≤ e.denote V - ((b:ℝ) - δ) := by linarith
  calc (1:ℝ) = (δ:ℝ) * (1/(δ:ℝ)) := by field_simp
    _ ≤ (e.denote V - ((b:ℝ) - δ)) * (1/(δ:ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1; positivity

/-- The `δ = 0` degenerate buy signal is identically `0` — the gate padding. -/
lemma buyIndF_denote_zero_delta (e : EF) (a : ℚ) (V : History) :
    (buyIndF e a 0).denote V = 0 := by
  rw [buyIndF_denote]
  norm_num

/-- The `δ = 0` degenerate sell signal is identically `0` — the gate padding. -/
lemma sellIndF_denote_zero_delta (e : EF) (b : ℚ) (V : History) :
    (sellIndF e b 0).denote V = 0 := by
  rw [sellIndF_denote]
  norm_num

end SignalFacts

/-! ### The hysteresis chain over abstract signal families

`hystN`'s recursion with the signals abstracted: `H 0 = 0`,
`H (k+1) = max (H k · (1 − sell k)) (buy k)`. All state facts assume only signal
membership in `[0,1]` where needed. -/

/-- The hysteresis holdings chain over signal families `buy`, `sell`. -/
def hystChain (buy sell : ℕ → EF) : ℕ → EF
  | 0 => .const 0
  | (k + 1) => .max (.mul (hystChain buy sell k) (oneMinus (sell k))) (buy k)

lemma hystChain_denote_zero (buy sell : ℕ → EF) (V : History) :
    (hystChain buy sell 0).denote V = 0 := by simp [hystChain]

lemma hystChain_denote_succ (buy sell : ℕ → EF) (V : History) (k : ℕ) :
    (hystChain buy sell (k + 1)).denote V
      = max ((hystChain buy sell k).denote V * (1 - (sell k).denote V))
          ((buy k).denote V) := by
  simp [hystChain, EF.denote_max, EF.denote_mul, Pi.mul_apply, oneMinus_denote]

lemma hystChain_rank (buy sell : ℕ → EF)
    (hb : ∀ i, (buy i).rank ≤ i) (hs : ∀ i, (sell i).rank ≤ i) :
    ∀ k, (hystChain buy sell k).rank ≤ k - 1
  | 0 => by simp [hystChain]
  | (k + 1) => by
      have ih := hystChain_rank buy sell hb hs k
      have h1 := hb k
      have h2 := hs k
      simp only [hystChain, EF.rank, oneMinus_rank, max_le_iff]
      omega

section ChainFacts

variable {buy sell : ℕ → EF} {V : History}

lemma hystChain_mem (hb : ∀ i, 0 ≤ (buy i).denote V ∧ (buy i).denote V ≤ 1)
    (hs : ∀ i, 0 ≤ (sell i).denote V ∧ (sell i).denote V ≤ 1) :
    ∀ k, 0 ≤ (hystChain buy sell k).denote V ∧ (hystChain buy sell k).denote V ≤ 1
  | 0 => by rw [hystChain_denote_zero]; norm_num
  | (k + 1) => by
      obtain ⟨ih0, ih1⟩ := hystChain_mem hb hs k
      obtain ⟨hs0, hs1⟩ := hs k
      obtain ⟨hb0, hb1⟩ := hb k
      rw [hystChain_denote_succ]
      exact ⟨le_max_of_le_right hb0, max_le (by nlinarith) hb1⟩

/-- Fact 1, generic: a net buy at day `k` means the buy signal fired. -/
lemma hystChain_incr_imp (hb : ∀ i, 0 ≤ (buy i).denote V ∧ (buy i).denote V ≤ 1)
    (hs : ∀ i, 0 ≤ (sell i).denote V ∧ (sell i).denote V ≤ 1) {k : ℕ}
    (h : (hystChain buy sell k).denote V < (hystChain buy sell (k + 1)).denote V) :
    0 < (buy k).denote V := by
  by_contra hbz'
  push_neg at hbz'
  have hbz : (buy k).denote V = 0 := le_antisymm hbz' (hb k).1
  obtain ⟨ih0, ih1⟩ := hystChain_mem hb hs k
  obtain ⟨hs0, hs1⟩ := hs k
  rw [hystChain_denote_succ, hbz] at h
  have hprod : (hystChain buy sell k).denote V * (1 - (sell k).denote V)
      ≤ (hystChain buy sell k).denote V := by nlinarith
  have hprod0 : 0 ≤ (hystChain buy sell k).denote V * (1 - (sell k).denote V) := by
    nlinarith
  rw [max_eq_left hprod0] at h
  linarith

/-- Fact 2, generic: a net sell at day `k` means the sell signal fired. -/
lemma hystChain_decr_imp (hs : ∀ i, 0 ≤ (sell i).denote V ∧ (sell i).denote V ≤ 1)
    {k : ℕ}
    (h : (hystChain buy sell (k + 1)).denote V < (hystChain buy sell k).denote V) :
    0 < (sell k).denote V := by
  by_contra hsz'
  push_neg at hsz'
  have hsz : (sell k).denote V = 0 := le_antisymm hsz' (hs k).1
  have hle : (hystChain buy sell k).denote V
      ≤ (hystChain buy sell (k + 1)).denote V := by
    rw [hystChain_denote_succ, hsz]
    simp only [sub_zero, mul_one]
    exact le_max_left _ _
  linarith

/-- Fact 3 (buy side), generic: a fully-fired buy signal forces full holdings. -/
lemma hystChain_eq_one (hb : ∀ i, 0 ≤ (buy i).denote V ∧ (buy i).denote V ≤ 1)
    (hs : ∀ i, 0 ≤ (sell i).denote V ∧ (sell i).denote V ≤ 1) {k : ℕ}
    (h : (buy k).denote V = 1) : (hystChain buy sell (k + 1)).denote V = 1 := by
  obtain ⟨ih0, ih1⟩ := hystChain_mem hb hs k
  obtain ⟨hs0, hs1⟩ := hs k
  rw [hystChain_denote_succ, h]
  exact max_eq_right (by nlinarith)

/-- Fact 3 (sell side), generic: a dead buy and a fully-fired sell force empty
holdings. -/
lemma hystChain_eq_zero {k : ℕ} (hbz : (buy k).denote V = 0)
    (hsz : (sell k).denote V = 1) : (hystChain buy sell (k + 1)).denote V = 0 := by
  rw [hystChain_denote_succ, hbz, hsz]
  simp

end ChainFacts

/-! ### Variation bookkeeping over the generic chain (C2/C3 substrate) -/

/-- The day-`i` position change. -/
noncomputable def hcDelta (buy sell : ℕ → EF) (V : History) (i : ℕ) : ℝ :=
  (hystChain buy sell (i + 1)).denote V - (hystChain buy sell i).denote V

/-- Positive variation `B₊ n = Σ_{i ≤ n} max Δᵢ 0`. -/
noncomputable def hcBpos (buy sell : ℕ → EF) (V : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), max (hcDelta buy sell V i) 0

/-- Negative variation `B₋ n = Σ_{i ≤ n} max (−Δᵢ) 0`. -/
noncomputable def hcBneg (buy sell : ℕ → EF) (V : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), max (-(hcDelta buy sell V i)) 0

-- `max_sub_max_neg` lives in `Properties/Hysteresis.lean` (imported transitively via
-- `Coherence`); the duplicate definition here was removed in the consolidation pass.

private lemma abs_eq_max_add_max_neg (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  rcases le_total x 0 with h | h
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -x)]; ring
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -x ≤ (0:ℝ))]; ring

lemma hcDelta_sum (buy sell : ℕ → EF) (V : History) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), hcDelta buy sell V i
      = (hystChain buy sell (n + 1)).denote V := by
  rw [show (∑ i ∈ Finset.range (n + 1), hcDelta buy sell V i)
      = ∑ i ∈ Finset.range (n + 1), ((hystChain buy sell (i + 1)).denote V
          - (hystChain buy sell i).denote V) from rfl,
    Finset.sum_range_sub (fun i => (hystChain buy sell i).denote V),
    hystChain_denote_zero, sub_zero]

lemma hcBpos_eq (buy sell : ℕ → EF) (V : History) (n : ℕ) :
    hcBpos buy sell V n
      = hcBneg buy sell V n + (hystChain buy sell (n + 1)).denote V := by
  have h : hcBpos buy sell V n - hcBneg buy sell V n
      = ∑ i ∈ Finset.range (n + 1), hcDelta buy sell V i := by
    rw [hcBpos, hcBneg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => max_sub_max_neg _)
  rw [hcDelta_sum] at h
  linarith

lemma hcBneg_nonneg (buy sell : ℕ → EF) (V : History) (n : ℕ) :
    0 ≤ hcBneg buy sell V n :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

lemma hcBneg_mono (buy sell : ℕ → EF) (V : History) {n m : ℕ} (h : n ≤ m) :
    hcBneg buy sell V n ≤ hcBneg buy sell V m :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right h 1))
    (fun _ _ _ => le_max_right _ _)

/-- The negative variation accumulated on `(n, m]` covers any drop in holdings. -/
lemma hcBneg_swing (buy sell : ℕ → EF) (V : History) {n m : ℕ} (h : n ≤ m) :
    (hystChain buy sell (n + 1)).denote V - (hystChain buy sell (m + 1)).denote V
      ≤ hcBneg buy sell V m - hcBneg buy sell V n := by
  have hsub : hcBneg buy sell V m - hcBneg buy sell V n
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), max (-(hcDelta buy sell V i)) 0 := by
    rw [hcBneg, hcBneg, eq_comm, Finset.sum_Ico_eq_sub _ (by omega)]
  have hdel : (hystChain buy sell (m + 1)).denote V
        - (hystChain buy sell (n + 1)).denote V
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), hcDelta buy sell V i := by
    rw [Finset.sum_Ico_eq_sub _ (by omega), hcDelta_sum, hcDelta_sum]
  have hge : ∑ i ∈ Finset.Ico (n + 1) (m + 1), (-(hcDelta buy sell V i))
      ≤ ∑ i ∈ Finset.Ico (n + 1) (m + 1), max (-(hcDelta buy sell V i)) 0 :=
    Finset.sum_le_sum (fun i _ => le_max_left _ _)
  rw [hsub]
  calc (hystChain buy sell (n + 1)).denote V - (hystChain buy sell (m + 1)).denote V
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), (-(hcDelta buy sell V i)) := by
        rw [Finset.sum_neg_distrib, ← hdel]; ring
    _ ≤ _ := hge

/-- **C3, generic**: if the chain frequently reaches `1` and frequently reaches `0`, the
negative variation is unbounded — each full swing adds at least `1`. -/
lemma hcBneg_unbounded {buy sell : ℕ → EF} {V : History}
    (h1 : ∃ᶠ n in atTop, (hystChain buy sell (n + 1)).denote V = 1)
    (h0 : ∃ᶠ n in atTop, (hystChain buy sell (n + 1)).denote V = 0) :
    ∀ K : ℕ, ∃ n, (K : ℝ) ≤ hcBneg buy sell V n := by
  intro K
  induction K with
  | zero => exact ⟨0, by simpa using hcBneg_nonneg buy sell V 0⟩
  | succ K ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n₁, hn₁, hone⟩ := (Filter.frequently_atTop.mp h1) (n + 1)
      obtain ⟨m₁, hm₁, hzero⟩ := (Filter.frequently_atTop.mp h0) (n₁ + 1)
      refine ⟨m₁, ?_⟩
      have hswing := hcBneg_swing buy sell V (show n₁ ≤ m₁ by omega)
      have hmono := hcBneg_mono buy sell V (show n ≤ n₁ by omega)
      rw [hone, hzero] at hswing
      push_cast
      linarith

/-! ### The expectation feature as an `EF`

`𝔼ₙ(X)` is a rational multiple of a finite sum of prices (`def:e`), so the hysteresis
signals can watch it: `expectEF X n` denotes exactly `X.expect P n`. -/

/-- Partial threshold sum: `Σ_{i<m} ⌜X > i/n⌝*ⁿ`. -/
def LUV.thresholdSumEF (X : LUV) (n : ℕ) : ℕ → EF
  | 0 => .const 0
  | (m + 1) => .add (X.thresholdSumEF n m) (.price (X.gt ((m : ℚ) / (n : ℚ))) n)

/-- The day-`n` expectation feature: `(1/n) · Σ_{i<n} ⌜X > i/n⌝*ⁿ`. -/
def LUV.expectEF (X : LUV) (n : ℕ) : EF :=
  .mul (.const (1/(n : ℚ))) (X.thresholdSumEF n n)

lemma LUV.thresholdSumEF_denote (X : LUV) (n : ℕ) (P : History) : ∀ m,
    (X.thresholdSumEF n m).denote P
      = ∑ i ∈ Finset.range m, P n (X.gt ((i : ℚ) / (n : ℚ)))
  | 0 => by simp [thresholdSumEF]
  | (m + 1) => by
      rw [thresholdSumEF]
      simp only [EF.denote_add, Pi.add_apply, EF.denote_price]
      rw [thresholdSumEF_denote X n P m, Finset.sum_range_succ]

lemma LUV.expectEF_denote (X : LUV) (n : ℕ) (P : History) :
    (X.expectEF n).denote P = X.expect P n := by
  rw [expectEF]
  simp only [EF.denote_mul, Pi.mul_apply, EF.denote_const, thresholdSumEF_denote]
  rw [LUV.expect, LUV.expectApprox]
  push_cast
  rw [one_div]

lemma LUV.thresholdSumEF_rank (X : LUV) (n : ℕ) : ∀ m, (X.thresholdSumEF n m).rank ≤ n
  | 0 => by simp [thresholdSumEF]
  | (m + 1) => by
      have ih := thresholdSumEF_rank X n m
      simp only [thresholdSumEF, EF.rank, max_le_iff]
      omega

lemma LUV.expectEF_rank (X : LUV) (n : ℕ) : (X.expectEF n).rank ≤ n := by
  have := X.thresholdSumEF_rank n n
  simp only [expectEF, EF.rank, max_le_iff]
  omega

/-! ### The gated signals -/

/-- Gate-padded ramp width: `0` before the start day `n₀` (killing the signal — the B2
padding trick), `δ` from `n₀` on. -/
def excPad (n₀ : ℕ) (δ : ℚ) (n : ℕ) : ℚ := if n < n₀ then 0 else δ

/-- Day-`n` buy signal: fires when `𝔼ₙ(X)` dips below `a + δ`, only from day `n₀`. -/
def excBuy (X : LUV) (a δ : ℚ) (n₀ n : ℕ) : EF :=
  buyIndF (X.expectEF n) a (excPad n₀ δ n)

/-- Day-`n` sell signal: fires when `𝔼ₙ(X)` spikes above `b − δ`, only from day `n₀`. -/
def excSell (X : LUV) (b δ : ℚ) (n₀ n : ℕ) : EF :=
  sellIndF (X.expectEF n) b (excPad n₀ δ n)

section GatedSignals

variable {X : LUV} {a b δ : ℚ} {n₀ n : ℕ} {P : History}

lemma excBuy_mem (X : LUV) (a δ : ℚ) (n₀ n : ℕ) (P : History) :
    0 ≤ (excBuy X a δ n₀ n).denote P ∧ (excBuy X a δ n₀ n).denote P ≤ 1 :=
  buyIndF_mem _ _ _ P

lemma excSell_mem (X : LUV) (b δ : ℚ) (n₀ n : ℕ) (P : History) :
    0 ≤ (excSell X b δ n₀ n).denote P ∧ (excSell X b δ n₀ n).denote P ≤ 1 :=
  sellIndF_mem _ _ _ P

lemma excBuy_live (h : n₀ ≤ n) :
    excBuy X a δ n₀ n = buyIndF (X.expectEF n) a δ := by
  rw [excBuy, excPad, if_neg (by omega)]

lemma excSell_live (h : n₀ ≤ n) :
    excSell X b δ n₀ n = sellIndF (X.expectEF n) b δ := by
  rw [excSell, excPad, if_neg (by omega)]

lemma excBuy_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (excBuy X a δ n₀ n).denote P) :
    n₀ ≤ n ∧ X.expect P n < (a : ℝ) + δ := by
  rcases lt_or_ge n n₀ with hn | hn
  · rw [excBuy, excPad, if_pos hn, buyIndF_denote_zero_delta] at h
    exact absurd h (lt_irrefl 0)
  · rw [excBuy_live hn] at h
    exact ⟨hn, X.expectEF_denote n P ▸ buyIndF_pos_imp hδ h⟩

lemma excSell_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (excSell X b δ n₀ n).denote P) :
    n₀ ≤ n ∧ (b : ℝ) - δ < X.expect P n := by
  rcases lt_or_ge n n₀ with hn | hn
  · rw [excSell, excPad, if_pos hn, sellIndF_denote_zero_delta] at h
    exact absurd h (lt_irrefl 0)
  · rw [excSell_live hn] at h
    exact ⟨hn, X.expectEF_denote n P ▸ sellIndF_pos_imp hδ h⟩

lemma excBuy_eq_one (hδ : 0 < (δ : ℝ)) (hn : n₀ ≤ n)
    (h : X.expect P n < (a : ℝ)) : (excBuy X a δ n₀ n).denote P = 1 := by
  rw [excBuy_live hn]
  exact buyIndF_eq_one hδ (by rw [X.expectEF_denote n P]; exact h)

lemma excBuy_eq_zero (hδ : 0 < (δ : ℝ)) (hn : n₀ ≤ n)
    (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ) (h : (b : ℝ) < X.expect P n) :
    (excBuy X a δ n₀ n).denote P = 0 := by
  rw [excBuy_live hn]
  exact buyIndF_eq_zero hδ hab (by rw [X.expectEF_denote n P]; exact h)

lemma excSell_eq_one (hδ : 0 < (δ : ℝ)) (hn : n₀ ≤ n)
    (h : (b : ℝ) < X.expect P n) : (excSell X b δ n₀ n).denote P = 1 := by
  rw [excSell_live hn]
  exact sellIndF_eq_one hδ (by rw [X.expectEF_denote n P]; exact h)

lemma excBuy_rank (X : LUV) (a δ : ℚ) (n₀ n : ℕ) : (excBuy X a δ n₀ n).rank ≤ n := by
  rw [excBuy, buyIndF_rank]; exact X.expectEF_rank n

lemma excSell_rank (X : LUV) (b δ : ℚ) (n₀ n : ℕ) : (excSell X b δ n₀ n).rank ≤ n := by
  rw [excSell, sellIndF_rank]; exact X.expectEF_rank n

end GatedSignals

/-! ### The bundle trader -/

/-- Day-`n` position change of the gated hysteresis state on `𝔼(X)`. -/
def excDeltaEF (X : LUV) (a b δ : ℚ) (n₀ n : ℕ) : EF :=
  .add (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (n + 1))
    (.mul (.const (-1)) (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) n))

/-- Day-`n` per-threshold coefficient: `(1/n) · Δₙ` — the trade buys `Δₙ` units of the
day-`n` bundle `{(1/n)·⌜X > i/n⌝}_{i<n}`. -/
def excCoef (X : LUV) (a b δ : ℚ) (n₀ n : ℕ) : EF :=
  .mul (.const (1/(n : ℚ))) (excDeltaEF X a b δ n₀ n)

lemma excDeltaEF_rank (X : LUV) (a b δ : ℚ) (n₀ n : ℕ) :
    (excDeltaEF X a b δ n₀ n).rank ≤ n := by
  have h1 := hystChain_rank _ _ (excBuy_rank X a δ n₀) (excSell_rank X b δ n₀) (n + 1)
  have h2 := hystChain_rank _ _ (excBuy_rank X a δ n₀) (excSell_rank X b δ n₀) n
  simp only [excDeltaEF, EF.rank, max_le_iff]
  omega

@[simp] theorem excDeltaEF_denote (X : LUV) (a b δ : ℚ) (n₀ n : ℕ) (P : History) :
    (excDeltaEF X a b δ n₀ n).denote P
      = hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n := by
  simp only [excDeltaEF, EF.denote_add, EF.denote_mul, EF.denote_const, Pi.add_apply,
    Pi.mul_apply, hcDelta]
  push_cast; ring

/-- **The `thm:ec` bundle trader**: on day `n`, trade `Δₙ` units of the day-`n`
threshold bundle of `X`, where `Δ` is the gated hysteresis on `𝔼(X)`. -/
def excTrader (X : LUV) (a b δ : ℚ) (n₀ : ℕ) : Trader where
  strat n :=
    { trades := (List.range n).map
        (fun i : ℕ => (excCoef X a b δ n₀ n, X.gt ((i : ℚ) / (n : ℚ))))
      rank_le := by
        intro p hp
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨i, -, rfl⟩ := hp
        have := excDeltaEF_rank X a b δ n₀ n
        simp only [excCoef, EF.rank, max_le_iff]
        omega }

private lemma list_range_map_sum (f : ℕ → ℝ) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | (n + 1) => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
        list_range_map_sum f n]
      simp

/-- The day-`n` strategy value: `Δₙ · (bundle payout − bundle cost)`, i.e.
`Δₙ · (𝔼ⁿ_w(X) − 𝔼ₙ(X))`. -/
lemma excTrader_value (X : LUV) (a b δ : ℚ) (n₀ : ℕ) (V : History)
    (w : Sentence → ℝ) (n : ℕ) :
    ((excTrader X a b δ n₀).strat n).value V w
      = hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) V n
          * (X.expectApprox w n - X.expectApprox (V n) n) := by
  have hc : (excCoef X a b δ n₀ n).denote V
      = (n : ℝ)⁻¹ * hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) V n := by
    simp only [excCoef, EF.denote_mul, EF.denote_const, Pi.mul_apply, excDeltaEF_denote]
    push_cast
    rw [one_div]
  have hval : ((excTrader X a b δ n₀).strat n).value V w
      = ((List.range n).map (fun i : ℕ => (excCoef X a b δ n₀ n).denote V
          * (w (X.gt ((i : ℚ) / (n : ℚ))) - V n (X.gt ((i : ℚ) / (n : ℚ)))))).sum := by
    simp only [excTrader, Strategy.value, List.map_map, Function.comp_def]
  rw [hval, list_range_map_sum, LUV.expectApprox, LUV.expectApprox]
  simp only [hc]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- Net worth: `Σ_{n ≤ N} Δₙ · (𝔼ⁿ_{v}(X) − 𝔼ₙ(X))`. -/
lemma excTrader_netWorth (X : LUV) (a b δ : ℚ) (n₀ : ℕ) (P : History) (v : PCWorld)
    (N : ℕ) : (excTrader X a b δ n₀).netWorth P v N
      = ∑ n ∈ Finset.range (N + 1),
          hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n
            * (X.expectApprox v.payout n - X.expect P n) := by
  simp only [Trader.netWorth]
  exact Finset.sum_congr rfl (fun n _ => excTrader_value X a b δ n₀ P v.payout n)

/-! ### The accounting (C2 with the bundle error term) -/

section Accounting

variable {X : LUV} {a b δ : ℚ} {n₀ : ℕ} {P : History}

/-- **The C2 master bound with the bundle error**: in any world valuing `X` at some `x`,
the net worth is at least `γ·B₋ − (a+δ) − (2B₋ + 1)/n₀`, where `γ = (b−δ)−(a+δ)`.
The `(2B₋+1)/n₀` term is the bundle-payout mismatch (`lem:conluvapprox` at each traded
day, all of which are `≥ n₀` by the gate). -/
theorem excTrader_netWorth_ge (hδ : 0 < (δ : ℝ)) (ha : 0 ≤ (a : ℝ) + δ)
    (hn₀ : 1 ≤ n₀) (v : PCWorld) {x : ℝ} (N : ℕ) (hx : v.ApproxValuesUpTo X x N) :
    ((b : ℝ) - δ - ((a : ℝ) + δ)) * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N
        - ((a : ℝ) + δ)
        - (2 * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1) / n₀
      ≤ (excTrader X a b δ n₀).netWorth P v N := by
  have hbmem := fun i => excBuy_mem X a δ n₀ i P
  have hsmem := fun i => excSell_mem X b δ n₀ i P
  rw [excTrader_netWorth]
  have hsplit : ∀ n : ℕ,
      hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n
          * (X.expectApprox v.payout n - X.expect P n)
        = hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n * (x - X.expect P n)
          + hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n
              * (X.expectApprox v.payout n - x) := fun n => by ring
  rw [Finset.sum_congr rfl (fun n _ => hsplit n), Finset.sum_add_distrib]
  -- Term A: the thm:con accounting against the fixed world value x.
  have htermA : ((b : ℝ) - δ - ((a : ℝ) + δ))
        * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N - ((a : ℝ) + δ)
      ≤ ∑ n ∈ Finset.range (N + 1),
          hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n * (x - X.expect P n) := by
    have hsplitA : ∑ n ∈ Finset.range (N + 1),
        hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n * (x - X.expect P n)
        = x * (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (N + 1)).denote P
          - ∑ n ∈ Finset.range (N + 1),
              hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n * X.expect P n := by
      rw [← hcDelta_sum (excBuy X a δ n₀) (excSell X b δ n₀) P N, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplitA]
    have hterm : ∀ i, hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i * X.expect P i
        ≤ ((a : ℝ) + δ) * max (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i) 0
          - ((b : ℝ) - δ)
              * max (-(hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i)) 0 := by
      intro i
      rcases lt_trichotomy (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i) 0
        with h | h | h
      · have hlt : (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (i + 1)).denote P
            < (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) i).denote P := by
          have h' : (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (i + 1)).denote P
              - (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) i).denote P < 0 := h
          linarith
        have hp := (excSell_pos_imp hδ (hystChain_decr_imp hsmem hlt)).2
        rw [max_eq_right h.le, max_eq_left (by linarith :
          (0:ℝ) ≤ -(hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i))]
        nlinarith
      · rw [h]; simp
      · have hlt : (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) i).denote P
            < (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (i + 1)).denote P := by
          have h' : 0 < (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (i + 1)).denote P
              - (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) i).denote P := h
          linarith
        have hp := (excBuy_pos_imp hδ (hystChain_incr_imp hbmem hsmem hlt)).2
        rw [max_eq_left h.le, max_eq_right (by linarith :
          -(hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i) ≤ (0:ℝ))]
        nlinarith
    have hsum : ∑ i ∈ Finset.range (N + 1),
        hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i * X.expect P i
        ≤ ((a : ℝ) + δ) * hcBpos (excBuy X a δ n₀) (excSell X b δ n₀) P N
          - ((b : ℝ) - δ) * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N := by
      calc ∑ i ∈ Finset.range (N + 1),
            hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i * X.expect P i
          ≤ ∑ i ∈ Finset.range (N + 1),
              (((a : ℝ) + δ) * max (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i) 0
                - ((b : ℝ) - δ)
                    * max (-(hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P i)) 0) :=
            Finset.sum_le_sum (fun i _ => hterm i)
        _ = _ := by
            rw [hcBpos, hcBneg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hpay0 : 0 ≤ x := hx.1
    obtain ⟨hh0, hh1⟩ := hystChain_mem hbmem hsmem (N + 1)
    have hBp := hcBpos_eq (excBuy X a δ n₀) (excSell X b δ n₀) P N
    nlinarith [mul_nonneg hpay0 hh0]
  -- Term B: the bundle-payout error.
  have htermB : -((2 * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1) / n₀)
      ≤ ∑ n ∈ Finset.range (N + 1),
          hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n
            * (X.expectApprox v.payout n - x) := by
    have hn₀R : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have hpt : ∀ n : ℕ, n ≤ N →
        -((max (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n) 0
            + max (-(hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n)) 0)
              * (1 / (n₀ : ℝ)))
          ≤ hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n
              * (X.expectApprox v.payout n - x) := by
      intro n hnN
      rcases eq_or_ne (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n) 0 with h | h
      · rw [h]; simp
      · have hn : n₀ ≤ n := by
          rcases lt_or_gt_of_ne h with h' | h'
          · have hlt : (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (n + 1)).denote P
                < (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) n).denote P := by
              have h'' : (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (n + 1)).denote P
                  - (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) n).denote P < 0 := h'
              linarith
            exact (excSell_pos_imp hδ (hystChain_decr_imp hsmem hlt)).1
          · have hlt : (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) n).denote P
                < (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (n + 1)).denote P := by
              have h'' : 0 < (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (n + 1)).denote P
                  - (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) n).denote P := h'
              linarith
            exact (excBuy_pos_imp hδ (hystChain_incr_imp hbmem hsmem hlt)).1
        have hnear := hx.2 n (by omega) hnN
        have hle : |X.expectApprox v.payout n - x| ≤ 1 / (n₀ : ℝ) := by
          refine hnear.trans ?_
          have h1 : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          exact one_div_le_one_div_of_le (by linarith) h1
        calc -((max (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n) 0
              + max (-(hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n)) 0)
                * (1 / (n₀ : ℝ)))
            = -(|hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n| * (1 / (n₀ : ℝ))) := by
              rw [abs_eq_max_add_max_neg]
          _ ≤ -(|hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n|
                * |X.expectApprox v.payout n - x|) := by
              have hmul := mul_le_mul_of_nonneg_left hle
                (abs_nonneg (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n))
              linarith
          _ = -|hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n
                * (X.expectApprox v.payout n - x)| := by rw [abs_mul]
          _ ≤ _ := neg_abs_le _
    calc -((2 * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1) / n₀)
        ≤ -((hcBpos (excBuy X a δ n₀) (excSell X b δ n₀) P N
              + hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N) * (1 / (n₀ : ℝ))) := by
          have hBp := hcBpos_eq (excBuy X a δ n₀) (excSell X b δ n₀) P N
          obtain ⟨hh0, hh1⟩ := hystChain_mem hbmem hsmem (N + 1)
          have hpos : (0 : ℝ) < (n₀ : ℝ) := by linarith
          have key : hcBpos (excBuy X a δ n₀) (excSell X b δ n₀) P N
                + hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N
              ≤ 2 * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1 := by
            rw [hBp]; linarith
          have hmul := mul_le_mul_of_nonneg_right key
            (by positivity : (0:ℝ) ≤ 1 / (n₀ : ℝ))
          have hdiv : (2 * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1) / (n₀ : ℝ)
              = (2 * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1)
                  * (1 / (n₀ : ℝ)) := div_eq_mul_one_div _ _
          rw [hdiv]
          linarith
      _ = ∑ n ∈ Finset.range (N + 1),
            -((max (hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n) 0
              + max (-(hcDelta (excBuy X a δ n₀) (excSell X b δ n₀) P n)) 0)
                * (1 / (n₀ : ℝ))) := by
          rw [hcBpos, hcBneg, ← Finset.sum_add_distrib, Finset.sum_mul,
            ← Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum (fun n hn => hpt n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))
  linarith

/-- **C3 for the expectation feature**: oscillation of `𝔼(X)` across `[a, b]` drives the
gated chain through full swings, so `B₋ → ∞`. -/
lemma excBneg_unbounded (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ)
    (hA : ∃ᶠ n in atTop, X.expect P n < (a : ℝ))
    (hB : ∃ᶠ n in atTop, (b : ℝ) < X.expect P n) :
    ∀ K : ℕ, ∃ n, (K : ℝ) ≤ hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P n := by
  have hbmem := fun i => excBuy_mem X a δ n₀ i P
  have hsmem := fun i => excSell_mem X b δ n₀ i P
  refine hcBneg_unbounded ?_ ?_
  · refine ((hA.and_eventually (Filter.eventually_ge_atTop n₀)).mono ?_)
    rintro n ⟨hdip, hn⟩
    exact hystChain_eq_one hbmem hsmem (excBuy_eq_one hδ hn hdip)
  · refine ((hB.and_eventually (Filter.eventually_ge_atTop n₀)).mono ?_)
    rintro n ⟨hspike, hn⟩
    exact hystChain_eq_zero (excBuy_eq_zero hδ hn hab hspike) (excSell_eq_one hδ hn hspike)

end Accounting

/-! ### Exploitation and the criterion application -/

/-- **The bundle trader exploits an oscillating expectation.** Gate condition
`2/n₀ ≤ γ/2` (γ the hysteresis margin) absorbs the bundle-payout error. -/
lemma excTrader_exploits (P : History) (DP : DeductiveProcess) (X : LUV)
    {a b δ : ℚ} {n₀ : ℕ}
    (hδ : 0 < (δ : ℝ)) (ha : 0 ≤ (a : ℝ) + δ) (hab : (a : ℝ) + δ < (b : ℝ) - δ)
    (hn₀ : 1 ≤ n₀)
    (hgap : 2 / (n₀ : ℝ) ≤ ((b : ℝ) - δ - ((a : ℝ) + δ)) / 2)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld),
      v.ConsistentWith (DP.D n) → ∃ x, v.ApproxValuesUpTo X x n)
    (hA : ∃ᶠ n in atTop, X.expect P n < (a : ℝ))
    (hB : ∃ᶠ n in atTop, (b : ℝ) < X.expect P n) :
    (excTrader X a b δ n₀).Exploits P DP := by
  have hγ0 : 0 < (b : ℝ) - δ - ((a : ℝ) + δ) := by linarith
  have hn₀R : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
  have hn₀pos : (0 : ℝ) < (n₀ : ℝ) := by linarith
  have hg : (2 : ℝ) ≤ ((b : ℝ) - δ - ((a : ℝ) + δ)) / 2 * n₀ := by
    rw [div_le_iff₀ hn₀pos] at hgap
    linarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hval
  -- the simplified master bound (for stages `≥ N₀`, where `hval` holds):
  -- netWorth ≥ (γ/2)·B₋ − (a+δ) − 1
  have hmaster : ∀ (N : ℕ), N₀ ≤ N → ∀ (v : PCWorld), v.ConsistentWith (DP.D N) →
      ((b : ℝ) - δ - ((a : ℝ) + δ)) / 2
            * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N
          - ((a : ℝ) + δ) - 1
        ≤ (excTrader X a b δ n₀).netWorth P v N := by
    intro N hN v hv
    obtain ⟨x, hx⟩ := hN₀ N hN v hv
    have h := excTrader_netWorth_ge (b := b) (P := P) hδ ha hn₀ v N hx
    have hB0 : 0 ≤ hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N :=
      hcBneg_nonneg _ _ _ _
    have herr : (2 * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1) / n₀
        ≤ ((b : ℝ) - δ - ((a : ℝ) + δ)) / 2
            * hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N + 1 := by
      rw [div_le_iff₀ hn₀pos]
      nlinarith [mul_le_mul_of_nonneg_left hg hB0]
    nlinarith
  set Cearly : ℝ :=
    ∑ i ∈ Finset.range N₀, ((excTrader X a b δ n₀).strat i).magnitude P with hCe
  have hCe0 : 0 ≤ Cearly :=
    Finset.sum_nonneg (fun i _ => Strategy.magnitude_nonneg _ _)
  refine ⟨⟨-(max ((a : ℝ) + δ + 1) Cearly), ?_⟩, ?_⟩
  · -- BddBelow: eventual master bound past `N₀`; finitely many early stages by partial magnitude
    rintro y ⟨N, v, hv, rfl⟩
    by_cases hN : N₀ ≤ N
    · have h := hmaster N hN v hv
      have hB0 : 0 ≤ hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P N :=
        hcBneg_nonneg _ _ _ _
      have : -((a : ℝ) + δ + 1) ≤ (excTrader X a b δ n₀).netWorth P v N := by nlinarith
      linarith [le_max_left ((a : ℝ) + δ + 1) Cearly]
    · push_neg at hN
      have h := (excTrader X a b δ n₀).abs_netWorth_le_partialMagnitude P v hP N
      have hle : N + 1 ≤ N₀ := hN
      have hmono : ∑ i ∈ Finset.range (N + 1),
            ((excTrader X a b δ n₀).strat i).magnitude P ≤ Cearly := by
        rw [hCe]
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hle)
          (fun i _ _ => Strategy.magnitude_nonneg _ _)
      have hlow : -Cearly ≤ (excTrader X a b δ n₀).netWorth P v N := by
        have := neg_le_of_abs_le h; linarith
      linarith [le_max_right ((a : ℝ) + δ + 1) Cearly]
  · -- ¬BddAbove: push each `excBneg_unbounded` witness past `N₀` via monotonicity of `B₋`
    rw [not_bddAbove_iff]
    intro y
    obtain ⟨K, hK⟩ := exists_nat_gt ((y + ((a : ℝ) + δ) + 1)
      / (((b : ℝ) - δ - ((a : ℝ) + δ)) / 2))
    obtain ⟨n', hn'⟩ := excBneg_unbounded (n₀ := n₀) hδ hab.le hA hB K
    have hnN₀ : N₀ ≤ max n' N₀ := le_max_right _ _
    have hn : (K : ℝ) ≤ hcBneg (excBuy X a δ n₀) (excSell X b δ n₀) P (max n' N₀) :=
      hn'.trans (hcBneg_mono _ _ _ (le_max_left _ _))
    obtain ⟨v, hv⟩ := hcons (max n' N₀)
    refine ⟨(excTrader X a b δ n₀).netWorth P v (max n' N₀), ⟨max n' N₀, v, hv, rfl⟩, ?_⟩
    have h := hmaster (max n' N₀) hnN₀ v hv
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < ((b : ℝ) - δ - ((a : ℝ) + δ)) / 2)] at hK
    have hKB := mul_le_mul_of_nonneg_left hn
      (by linarith : (0:ℝ) ≤ ((b : ℝ) - δ - ((a : ℝ) + δ)) / 2)
    nlinarith

#print axioms excTrader_exploits

/-! ### Efficient emission of the expectation feature and variable-width chain -/

lemma encode_inv_nat_polyFueled :
    ∃ c, PolyFueled c (fun n => Encodable.encode (1 / (n : ℚ))) := by
  have livePF := (PolyFueled.const 2).pair PolyFueled.id
  have pickPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Encodable.encode (0 : ℚ))).pair livePF).pair PolyFueled.id)
  refine ⟨_, pickPF.of_eq (fun n => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rcases n with _ | n
  · simp
  · simp only [Nat.succ_ne_zero, if_false, one_div]
    simpa using (encode_rat_inv_natCast (Nat.succ_pos n)).symm

lemma encode_if_lt_const_polyFueled (n₀ : ℕ) (q₀ q₁ : ℚ) :
    ∃ c, PolyFueled c (fun n => Encodable.encode (if n < n₀ then q₀ else q₁)) := by
  have testPF := subc_polyFueled.comp
    ((PolyFueled.const n₀).pair PolyFueled.id)
  have pickPF := ifzSel_polyFueled.comp
    (((PolyFueled.const (Encodable.encode q₁)).pair
      (PolyFueled.const (Encodable.encode q₀))).pair testPF)
  refine ⟨_, pickPF.of_eq (fun n => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases h : n < n₀
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

/-- A threshold-price term followed by the enclosing sum's `add` tag. -/
def excThresholdBlk (X : LUV) (n i : ℕ) : List ℕ :=
  (EF.price (X.gt ((i : ℚ) / (n : ℚ))) n).serialize ++ [2]

lemma excThresholdBlk_tokenStream (X : LUV) (hcode : X.PolyThresholdCodes) :
    PolyTokenStream (fun m => excThresholdBlk X m.unpair.1 m.unpair.2) := by
  obtain ⟨cX, hX⟩ := hcode
  show PolyTokenStream (fun m =>
    [0, Encodable.encode (X.gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ))),
      m.unpair.1, 2])
  exact (((PolyTokenStream.const 0).append (PolyTokenStream.polyTok hX)).append
    (PolyTokenStream.polyTok PolyFueled.left)).append (PolyTokenStream.const 2)

lemma excThresholdBlk_length (X : LUV) (n i : ℕ) :
    (excThresholdBlk X n i).length = 4 := by
  simp [excThresholdBlk, EF.serialize]

lemma serialize_thresholdSumEF (X : LUV) (n : ℕ) : ∀ m,
    (X.thresholdSumEF n m).serialize =
      [1, Encodable.encode (0 : ℚ)] ++
        (List.range m).flatMap (fun i => excThresholdBlk X n i)
  | 0 => by simp [LUV.thresholdSumEF, EF.serialize]
  | m + 1 => by
      rw [LUV.thresholdSumEF, EF.serialize, serialize_thresholdSumEF X n m,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp [excThresholdBlk, EF.serialize, List.append_assoc]

lemma expectEF_polySegStream (X : LUV) (hcode : X.PolyThresholdCodes) :
    PolySegStream (fun n => (X.expectEF n).serialize) := by
  have head : PolySegStream (fun n => (EF.const (1 / (n : ℚ))).serialize) :=
    PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp encode_inv_nat_polyFueled)
  have zero : PolySegStream (fun _ : ℕ => [1, Encodable.encode (0 : ℚ)]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have blocks := PolySegStream.blocks (excThresholdBlk_tokenStream X hcode) 4
    (fun m => excThresholdBlk_length X _ _) (by omega) PolyFueled.id
  have sums := zero.append blocks
  refine PolySegStream.of_eq ((head.append sums).append
    (PolySegStream.ofTokenStream (PolyTokenStream.const 3))) ?_
  intro n
  rw [LUV.expectEF]
  simp only [EF.serialize]
  rw [serialize_thresholdSumEF]
  simp

lemma PolySegStream.serialize_oneMinus {e : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize)) :
    PolySegStream (fun n => (oneMinus (e n)).serialize) :=
  PolySegStream.serialize_add
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1))
    (PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) he)

lemma PolySegStream.serialize_efMin {e f : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize))
    (hf : PolySegStream (fun n => (f n).serialize)) :
    PolySegStream (fun n => (efMin (e n) (f n)).serialize) :=
  PolySegStream.serialize_mul
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1)))
    (PolySegStream.serialize_max
      (PolySegStream.serialize_mul
        (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) he)
      (PolySegStream.serialize_mul
        (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) hf))

lemma PolySegStream.serialize_clip01 {e : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize)) :
    PolySegStream (fun n => (clip01 (e n)).serialize) :=
  PolySegStream.serialize_max
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0))
    (PolySegStream.serialize_efMin
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)) he)

lemma excBuy_polySegStream (X : LUV) (hcode : X.PolyThresholdCodes)
    (a δ : ℚ) (n₀ : ℕ) :
    PolySegStream (fun n => (excBuy X a δ n₀ n).serialize) := by
  have he := expectEF_polySegStream X hcode
  have hca : ∃ c, PolyFueled c (fun n =>
      Encodable.encode (a + excPad n₀ δ n)) := by
    simpa [excPad, apply_ite] using encode_if_lt_const_polyFueled n₀ a (a + δ)
  have hcs : ∃ c, PolyFueled c (fun n =>
      Encodable.encode (1 / excPad n₀ δ n)) := by
    simpa [excPad, apply_ite] using encode_if_lt_const_polyFueled n₀ 0 (1 / δ)
  have hc : PolySegStream (fun n => (EF.const (a + excPad n₀ δ n)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp hca)
  have hs : PolySegStream (fun n => (EF.const (1 / excPad n₀ δ n)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp hcs)
  show PolySegStream (fun n =>
    (clip01 (.mul (.add (.const (a + excPad n₀ δ n))
      (.mul (.const (-1)) (X.expectEF n))) (.const (1 / excPad n₀ δ n)))).serialize)
  exact PolySegStream.serialize_clip01 (PolySegStream.serialize_mul
    (PolySegStream.serialize_add hc (PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) he)) hs)

lemma excSell_polySegStream (X : LUV) (hcode : X.PolyThresholdCodes)
    (b δ : ℚ) (n₀ : ℕ) :
    PolySegStream (fun n => (excSell X b δ n₀ n).serialize) := by
  have he := expectEF_polySegStream X hcode
  have hcb : ∃ c, PolyFueled c (fun n =>
      Encodable.encode (excPad n₀ δ n - b)) := by
    obtain ⟨c, hc⟩ := encode_if_lt_const_polyFueled n₀ (-b) (δ - b)
    refine ⟨c, hc.of_eq (fun n => ?_)⟩
    by_cases h : n < n₀ <;> simp [excPad, h]
  have hcs : ∃ c, PolyFueled c (fun n =>
      Encodable.encode (1 / excPad n₀ δ n)) := by
    simpa [excPad, apply_ite] using encode_if_lt_const_polyFueled n₀ 0 (1 / δ)
  have hc : PolySegStream (fun n => (EF.const (excPad n₀ δ n - b)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp hcb)
  have hs : PolySegStream (fun n => (EF.const (1 / excPad n₀ δ n)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp hcs)
  show PolySegStream (fun n =>
    (clip01 (.mul (.add (X.expectEF n) (.const (excPad n₀ δ n - b)))
      (.const (1 / excPad n₀ δ n)))).serialize)
  exact PolySegStream.serialize_clip01
    (PolySegStream.serialize_mul (PolySegStream.serialize_add he hc) hs)

/-- One historical block in the feature-generic hysteresis chain. -/
def excHystBlk (X : LUV) (a b δ : ℚ) (n₀ k : ℕ) : List ℕ :=
  (oneMinus (excSell X b δ n₀ k)).serialize ++ [3] ++
    (excBuy X a δ n₀ k).serialize ++ [4]

lemma excHystBlk_polySegStream (X : LUV) (hcode : X.PolyThresholdCodes)
    (a b δ : ℚ) (n₀ : ℕ) :
    PolySegStream (fun k => excHystBlk X a b δ n₀ k) := by
  exact (((PolySegStream.serialize_oneMinus (excSell_polySegStream X hcode b δ n₀)).append
    (PolySegStream.ofTokenStream (PolyTokenStream.const 3))).append
    (excBuy_polySegStream X hcode a δ n₀)).append
    (PolySegStream.ofTokenStream (PolyTokenStream.const 4))

lemma serialize_excHystChain (X : LUV) (a b δ : ℚ) (n₀ : ℕ) : ∀ k,
    (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) k).serialize =
      [1, Encodable.encode (0 : ℚ)] ++
        (List.range k).flatMap (fun j => excHystBlk X a b δ n₀ j)
  | 0 => by simp [hystChain, EF.serialize]
  | k + 1 => by
      rw [hystChain]
      simp only [EF.serialize]
      rw [serialize_excHystChain X a b δ n₀ k,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
      simp [excHystBlk, List.append_assoc]

lemma excCoef_polySegStream (X : LUV) (hcode : X.PolyThresholdCodes)
    (a b δ : ℚ) (n₀ : ℕ) :
    PolySegStream (fun n => (excCoef X a b δ n₀ n).serialize) := by
  have blk := excHystBlk_polySegStream X hcode a b δ n₀
  have z : PolySegStream (fun _ : ℕ => [1, Encodable.encode (0 : ℚ)]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have blk' := blk.comp PolyFueled.right
  have chain1 : PolySegStream (fun n =>
      (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) (n + 1)).serialize) :=
    PolySegStream.of_eq (z.append (PolySegStream.concatVar blk' PolyFueled.id.succ_comp))
      (fun n => by rw [serialize_excHystChain]; simp [Nat.unpair_pair])
  have chain0 : PolySegStream (fun n =>
      (hystChain (excBuy X a δ n₀) (excSell X b δ n₀) n).serialize) :=
    PolySegStream.of_eq (z.append (PolySegStream.concatVar blk' PolyFueled.id))
      (fun n => by rw [serialize_excHystChain]; simp [Nat.unpair_pair])
  have delta := PolySegStream.serialize_add chain1
    (PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) chain0)
  have scale : PolySegStream (fun n => (EF.const (1 / (n : ℚ))).serialize) :=
    PolySegStream.ofTokenStream
      (PolyTokenStream.serialize_const_comp encode_inv_nat_polyFueled)
  refine PolySegStream.of_eq (PolySegStream.serialize_mul scale delta) ?_
  intro n
  rw [excCoef, excDeltaEF]

private lemma serializeTrades_map_same (e : EF) (f : ℕ → Sentence) : ∀ l : List ℕ,
    serializeTrades (l.map (fun i => (e, f i))) =
      l.flatMap (fun i => e.serialize ++ [6, Encodable.encode (f i)])
  | [] => by simp [serializeTrades]
  | i :: l => by
      rw [List.map_cons, List.flatMap_cons, serializeTrades, serializeTrades_map_same]
      simp [List.append_assoc]

private lemma serializeTrades_excTrader (X : LUV) (a b δ : ℚ) (n₀ n : ℕ) :
    serializeTrades ((excTrader X a b δ n₀).strat n).trades =
      (List.range n).flatMap (fun i : ℕ =>
        (excCoef X a b δ n₀ n).serialize ++
          [6, Encodable.encode (X.gt ((i : ℚ) / (n : ℚ)))]) := by
  show serializeTrades ((List.range n).map
    (fun i : ℕ => (excCoef X a b δ n₀ n, X.gt ((i : ℚ) / (n : ℚ))))) = _
  exact serializeTrades_map_same (excCoef X a b δ n₀ n)
    (fun i : ℕ => X.gt ((i : ℚ) / (n : ℚ))) (List.range n)

/-- Efficient computability of the bundle trader. The day-`n` stream is `n` identical
coefficient serializations (each `Θ(n²)`: the two hysteresis chains contain historical
day-`k` blocks carrying the `Θ(k)` expectation feature) with distinct threshold sentences.
`PolySegStream.concatVar` emits the variable-width chains; the outer bundle is uniform-width.
`hcode` supplies the compact sentence-code interface for `⌜X > i/n⌝`. -/
lemma excTrader_ecTok (X : LUV) (hcode : X.PolyThresholdCodes)
    (a b δ : ℚ) (n₀ : ℕ) :
    EfficientlyComputableTok (excTrader X a b δ n₀) := by
  have hcode' := hcode
  obtain ⟨cX, hX⟩ := hcode
  have coef := (excCoef_polySegStream X hcode' a b δ n₀).comp PolyFueled.left
  have frame : PolySegStream (fun m =>
      [6, Encodable.encode (X.gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ)))]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 6).append (PolyTokenStream.polyTok hX))
  have chunk := coef.append frame
  have chunks := PolySegStream.concat chunk PolyFueled.id (fun n j => by
    simp only [List.length_append, Nat.unpair_pair]
    rfl)
  exact ecTok_of_segStream _ (PolySegStream.of_eq chunks (fun n => by
    rw [serializeTrades_excTrader]
    simp only [Nat.unpair_pair]))

/-- **Expectations Converge** (`thm:ec`): under a logical inductor, the day-`n`
expectation of any `[0,1]`-LUV converges, provided plausible worlds keep existing
(`hcons`) and assign `X` values (`hval` — the `lem:conluvapprox` linkage, disclosed
type-`(c)`: it imports "Θ represents computations" as a hypothesis).

The compact threshold-code hypothesis is the `def:ec` interface for the paper's
Θ-definable LUV syntax. The bundle trader, its exploitation proof, and its variable-width
emission certificate are all discharged.
Paper node: `thm:ec` -/
theorem LUV.expect_converges (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (X : LUV)
    (hcode : X.PolyThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld),
      v.ConsistentWith (DP.D n) → ∃ x, v.ApproxValuesUpTo X x n) :
    ∃ L : ℝ, ConvergesTo (X.expectSeq P) L := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  by_contra hnc
  obtain ⟨a, b, hab, hA, hB⟩ := exists_rat_oscillation_of_not_exists_convergesTo
    (X.expectSeq P) (fun n => X.expect_mem_Icc P n (fun s => hP n s)) hnc
  -- band width δ = (b−a)/4, margin γ = (b−a)/2
  set δ : ℚ := (b - a) / 4 with hδdef
  have hδR : ((δ : ℚ) : ℝ) = ((b : ℝ) - a) / 4 := by rw [hδdef]; push_cast; ring
  have hδ : 0 < (δ : ℝ) := by rw [hδR]; linarith
  have hgapab : (a : ℝ) + δ < (b : ℝ) - δ := by rw [hδR]; linarith
  set γ : ℝ := (b : ℝ) - δ - ((a : ℝ) + δ) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have ha : 0 ≤ (a : ℝ) + δ := by
    -- a dip day exists and expectations are ≥ 0, so 0 ≤ a.
    obtain ⟨n, -, hn⟩ := (Filter.frequently_atTop.mp hA) 0
    have := (X.expect_mem_Icc P n (fun s => hP n s)).1
    have hEn : X.expect P n < (a : ℝ) := hn
    linarith
  -- gate day: n₀ ≥ 4/γ, n₀ ≥ 1
  obtain ⟨n₀', hn₀'⟩ := exists_nat_ge ((4 : ℝ) / γ)
  set n₀ : ℕ := n₀' + 1 with hn₀def
  have hn₀ : 1 ≤ n₀ := by omega
  have hn₀R : ((4 : ℝ) / γ) ≤ (n₀ : ℝ) := by
    calc ((4 : ℝ) / γ) ≤ (n₀' : ℝ) := hn₀'
      _ ≤ (n₀ : ℝ) := by rw [hn₀def]; push_cast; linarith
  have hgap : 2 / (n₀ : ℝ) ≤ γ / 2 := by
    have hn₀pos : (0 : ℝ) < (n₀ : ℝ) := by
      have : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
      linarith
    rw [div_le_div_iff₀ hn₀pos (by norm_num : (0:ℝ) < 2)]
    rw [div_le_iff₀ hγ0] at hn₀R
    nlinarith
  exact hLI.noExploit (excTrader X a b δ n₀) (excTrader_ecTok X hcode a b δ n₀)
    (excTrader_exploits P DP X hδ ha hgapab hn₀ hgap hcons hP hval hA hB)

#print axioms LUV.expect_converges

/-- `𝔼_∞(X)` — the limiting expectation (`thm:ec`). -/
noncomputable def LUV.expectInf (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV)
    (hcode : X.PolyThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∃ x, v.ApproxValuesUpTo X x n) : ℝ :=
  (X.expect_converges P DP hcode hcons (Filter.Eventually.of_forall hval)).choose

end LogicalInduction
