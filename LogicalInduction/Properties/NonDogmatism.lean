/-
# `thm:nd` — Non-Dogmatism (weak fragment)

Paper (`main.tex` 1528): if `Θ ⊬ ¬φ` then `P∞(φ) > 0`. Our semantic substrate renders the
unrefutability hypothesis per-day — "`φ`-satisfying plausible worlds keep existing"
(`∀ n, ∃ v, v.ConsistentWith (DP.D n) ∧ v.Holds φ`, the `def:lang`-level reading of `⊬`,
disclosed in the ledger) — and this file proves the **weak fragment**: the price cannot
frequently fall below the decaying bound `2^{-(n+2)}`. It is honestly *weaker* than
`thm:nd` (the bound decays; the full liminf form is Phase B2's budget-halving trader).

The exploiting trader is memoryless: on day `n` it buys
`β n = max 0 (1 − 2^{n+1}·φ*ⁿ)` shares of `φ`. Its day-`n` spend is `β n · Pₙφ ≤ 2^{-(n+1)}`
(the signal only fires below `2^{-(n+1)}`), so the total spend is ≤ 1 in every world —
bounded downside. If the price frequently dips below `2^{-(n+2)}`, the signal fires with
`β ≥ 1/2` while a plausible `φ`-world pays `1 − Pₙφ ≥ 1/2` per share — each dip banks
`≥ 1/4` of `φ`-world value, and the dips accumulate without bound.

The power `2^{n+1}` is a **left-nested** `mul`-chain of `const 2` — size `Θ(n)` with
homogeneous width-3 serialization blocks, so `ecTok_of_blockStream` (Phase A2) certifies
the trader e.c. directly.
-/
import LogicalInduction.Properties.Basic

namespace LogicalInduction

open Filter Topology

/-! ### The sharpening power `2^(k+1)`, as a block-serializable feature -/

/-- The left-nested product `2 · 2 ⋯ 2` (`k+1` factors): denotes `2^(k+1)`, serializes as
`[1,⌜2⌝]` followed by `k` homogeneous width-3 blocks `[1,⌜2⌝,3]`. -/
def twoPowChain : ℕ → EF
  | 0 => EF.const 2
  | (k + 1) => EF.mul (twoPowChain k) (EF.const 2)

@[simp] theorem twoPowChain_denote (P : History) : ∀ k,
    (twoPowChain k).denote P = 2 ^ (k + 1)
  | 0 => by norm_num [twoPowChain]
  | (k + 1) => by
      have ih := twoPowChain_denote P k
      simp only [twoPowChain, EF.denote_mul, Pi.mul_apply, ih, EF.denote_const]
      norm_num [pow_succ]

@[simp] theorem twoPowChain_rank : ∀ k, (twoPowChain k).rank = 0
  | 0 => rfl
  | (k + 1) => by rw [twoPowChain, EF.rank, twoPowChain_rank k]; rfl

theorem serialize_twoPowChain : ∀ k,
    (twoPowChain k).serialize
      = [1, Encodable.encode (2 : ℚ)]
        ++ (List.range k).flatMap (fun _ => [1, Encodable.encode (2 : ℚ), 3])
  | 0 => by simp [twoPowChain, EF.serialize]
  | (k + 1) => by
      rw [twoPowChain, EF.serialize, serialize_twoPowChain k, List.range_succ]
      simp [EF.serialize]

/-! ### The trader (`def:trader`, constructed — not stubbed) -/

/-- Day-`n` buy signal: `max 0 (1 − 2^{n+1}·φ*ⁿ)` — fires only when the price is below
`2^{-(n+1)}`, at slope `2^{n+1}`. -/
def ndBeta (φ : Sentence) (n : ℕ) : EF :=
  .max (.const 0)
    (.add (.const 1) (.mul (.const (-1)) (.mul (twoPowChain n) (.price φ n))))

theorem ndBeta_denote (φ : Sentence) (P : History) (n : ℕ) :
    (ndBeta φ n).denote P = max 0 (1 - 2 ^ (n + 1) * P n φ) := by
  simp only [ndBeta, EF.denote_max, EF.denote_add, EF.denote_mul, EF.denote_const,
    EF.denote_price, twoPowChain_denote, Pi.add_apply, Pi.mul_apply]
  norm_num [sub_eq_add_neg, neg_mul]

theorem ndBeta_rank (φ : Sentence) (n : ℕ) : (ndBeta φ n).rank ≤ n := by
  simp [ndBeta, EF.rank]

/-- The non-dogmatism trader: `β n` shares of `φ` daily. -/
def ndTrader (φ : Sentence) : Trader where
  strat n := { trades := [(ndBeta φ n, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact ndBeta_rank φ n }

@[simp] theorem ndTrader_value (φ : Sentence) (V : History) (w : Sentence → ℝ) (n : ℕ) :
    ((ndTrader φ).strat n).value V w = (ndBeta φ n).denote V * (w φ - V n φ) := by
  simp [ndTrader, Strategy.value]

theorem ndTrader_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (ndTrader φ).netWorth V v m
      = ∑ i ∈ Finset.range (m + 1), (ndBeta φ i).denote V * (v.payout φ - V i φ) := by
  simp [Trader.netWorth]

/-! ### The economics -/

theorem ndBeta_nonneg (φ : Sentence) (P : History) (n : ℕ) :
    0 ≤ (ndBeta φ n).denote P := by
  rw [ndBeta_denote]; exact le_max_left _ _

/-- Day-`n` spend bound: `β n · Pₙφ ≤ 2^{-(n+1)}` (support of the signal is
`Pₙφ < 2^{-(n+1)}` and `β ≤ 1` there). -/
theorem ndBeta_mul_price_le (φ : Sentence) (P : History) (n : ℕ) (hP0 : 0 ≤ P n φ) :
    (ndBeta φ n).denote P * P n φ ≤ 1 / 2 ^ (n + 1) := by
  rw [ndBeta_denote]
  have h2 : (0:ℝ) < 2 ^ (n + 1) := by positivity
  rcases le_total (1 - 2 ^ (n + 1) * P n φ) 0 with h | h
  · rw [max_eq_left h, zero_mul]; positivity
  · rw [max_eq_right h]
    have hP : P n φ ≤ 1 / 2 ^ (n + 1) := by
      rw [le_div_iff₀ h2]; nlinarith
    calc (1 - 2 ^ (n + 1) * P n φ) * P n φ
        ≤ 1 * P n φ := mul_le_mul_of_nonneg_right (by nlinarith) hP0
      _ = P n φ := one_mul _
      _ ≤ 1 / 2 ^ (n + 1) := hP

/-- `∑_{i<m} 2^{-(i+1)} ≤ 1` — the total spend bound. -/
theorem sum_inv_twoPow_le_one (m : ℕ) :
    ∑ i ∈ Finset.range m, (1:ℝ) / 2 ^ (i + 1) ≤ 1 := by
  have key : ∀ k, ∑ i ∈ Finset.range k, (1:ℝ) / 2 ^ (i + 1) = 1 - 1 / 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have h2 : (2:ℝ) ^ k ≠ 0 := by positivity
        field_simp
        ring
  rw [key m]
  have : (0:ℝ) < 1 / 2 ^ m := by positivity
  linarith

/-- On a dip day (`Pₙφ < 2^{-(n+2)}`), the `φ`-world term banks at least `1/4`:
the signal is ≥ `1/2` and the share pays `1 − Pₙφ ≥ 1/2`. -/
theorem ndBeta_trigger (φ : Sentence) (P : History) (n : ℕ)
    (hP0 : 0 ≤ P n φ) (htrig : P n φ < 1 / 2 ^ (n + 2)) :
    (1:ℝ)/4 ≤ (ndBeta φ n).denote P * (1 - P n φ) := by
  rw [ndBeta_denote]
  have h2 : (0:ℝ) < 2 ^ (n + 2) := by positivity
  have hsplit : (2:ℝ) ^ (n + 2) = 2 ^ (n + 1) * 2 := by rw [pow_succ]
  rw [lt_div_iff₀ h2] at htrig
  have hy : 2 ^ (n + 1) * P n φ < 1/2 := by nlinarith
  have hβ : (1:ℝ)/2 ≤ max 0 (1 - 2 ^ (n + 1) * P n φ) :=
    le_max_of_le_right (by linarith)
  have h1P : (1:ℝ)/2 ≤ 1 - P n φ := by
    have h1le : (1:ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg hP0 (by linarith : (0:ℝ) ≤ 2 ^ (n + 2) - 2)]
  calc (1:ℝ)/4 = (1/2) * (1/2) := by norm_num
    _ ≤ max 0 (1 - 2 ^ (n + 1) * P n φ) * (1 - P n φ) :=
        mul_le_mul hβ h1P (by norm_num) (le_trans (by norm_num) hβ)

/-- **The exploitation** (`thm:nd`, weak fragment): with prices in `[0,1]`, plausible
`φ`-worlds daily, and frequent dips below `2^{-(n+2)}`, `ndTrader φ` exploits. -/
theorem ndTrader_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (hP0 : ∀ n, 0 ≤ P n φ) (hP1 : ∀ n, P n φ ≤ 1)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ)
    (hfreq : ∃ᶠ n in atTop, P n φ < 1 / 2 ^ (n + 2)) :
    (ndTrader φ).Exploits P DP := by
  refine exploits_of_bddBelow_of_unbounded _ _ _ 1 ?_ ?_
  · -- Bounded below by −1: the spend bound, in every plausible world.
    rintro x ⟨m, v, hv, rfl⟩
    rw [ndTrader_netWorth]
    have hterm : ∀ i, -((1:ℝ) / 2 ^ (i + 1)) ≤ (ndBeta φ i).denote P * (v.payout φ - P i φ) := by
      intro i
      have hβ0 := ndBeta_nonneg φ P i
      have hpay : 0 ≤ v.payout φ := by rw [PCWorld.payout]; split <;> norm_num
      have hspend := ndBeta_mul_price_le φ P i (hP0 i)
      nlinarith [mul_nonneg hβ0 hpay]
    calc (-1:ℝ)
        ≤ -∑ i ∈ Finset.range (m + 1), (1:ℝ) / 2 ^ (i + 1) := by
          have := sum_inv_twoPow_le_one (m + 1); linarith
      _ = ∑ i ∈ Finset.range (m + 1), -((1:ℝ) / 2 ^ (i + 1)) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ Finset.range (m + 1), (ndBeta φ i).denote P * (v.payout φ - P i φ) :=
          Finset.sum_le_sum (fun i _ => hterm i)
  · -- Unbounded: accumulate `1/4` per dip along the frequent subsequence, in `φ`-worlds.
    intro B
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (4 * B)
    obtain ⟨v, hv, hvφ⟩ := hφ (g M)
    have hpay : v.payout φ = 1 := by rw [PCWorld.payout, if_pos hvφ]
    refine ⟨(ndTrader φ).netWorth P v (g M), ⟨g M, v, hv, rfl⟩, ?_⟩
    rw [ndTrader_netWorth]
    set F : ℕ → ℝ := fun i => (ndBeta φ i).denote P * (v.payout φ - P i φ) with hF
    have hterm0 : ∀ i, 0 ≤ F i := by
      intro i; rw [hF]
      simp only [hpay]
      exact mul_nonneg (ndBeta_nonneg φ P i) (by have := hP1 i; linarith)
    have hsub : (Finset.range (M + 1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : ((M:ℝ) + 1) * (1/4) ≤ ∑ i ∈ Finset.range (g M + 1), F i := by
      calc ((M:ℝ) + 1) * (1/4)
          = ∑ _k ∈ Finset.range (M + 1), (1/4 : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M + 1), F (g k) :=
            Finset.sum_le_sum (fun k _ => by
              rw [hF]; simp only [hpay]
              exact ndBeta_trigger φ P (g k) (hP0 _) (hg k))
        _ = ∑ i ∈ (Finset.range (M + 1)).image g, F i :=
            (Finset.sum_image (hg_mono.injective.injOn)).symm
        _ ≤ ∑ i ∈ Finset.range (g M + 1), F i :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hterm0 i)
    nlinarith

/-! ### Efficient computability, via `ecTok_of_blockStream` (Phase A2) -/

theorem serialize_ndBeta (φ : Sentence) (n : ℕ) :
    (ndBeta φ n).serialize
      = [1, Encodable.encode (0:ℚ), 1, Encodable.encode (1:ℚ), 1, Encodable.encode (-1:ℚ),
         1, Encodable.encode (2:ℚ)]
        ++ (List.range n).flatMap (fun _ => [1, Encodable.encode (2:ℚ), 3])
        ++ [0, Encodable.encode φ, n, 3, 3, 2, 4] := by
  simp [ndBeta, EF.serialize, serialize_twoPowChain]

/-- `ndTrader φ` is efficiently computable: its stream is 8 head tokens, `n` homogeneous
width-3 blocks (the pow-chain), and a 9-token tail carrying the day index. -/
theorem ndTrader_ecTok (φ : Sentence) : EfficientlyComputableTok (ndTrader φ) := by
  refine ecTok_of_blockStream _
    [fun _ => 1, fun _ => Encodable.encode (0:ℚ), fun _ => 1, fun _ => Encodable.encode (1:ℚ),
     fun _ => 1, fun _ => Encodable.encode (-1:ℚ), fun _ => 1, fun _ => Encodable.encode (2:ℚ)]
    [fun _ => 1, fun _ => Encodable.encode (2:ℚ), fun _ => 3]
    [fun _ => 0, fun _ => Encodable.encode φ, fun n => n, fun _ => 3, fun _ => 3,
     fun _ => 2, fun _ => 4, fun _ => 6, fun _ => Encodable.encode φ]
    PolyFueled.id ?_ ?_ ?_ (by simp) ?_
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨_, PolyFueled.const 1⟩, ⟨_, PolyFueled.const (Encodable.encode (0:ℚ))⟩,
      ⟨_, PolyFueled.const 1⟩, ⟨_, PolyFueled.const (Encodable.encode (1:ℚ))⟩,
      ⟨_, PolyFueled.const 1⟩, ⟨_, PolyFueled.const (Encodable.encode (-1:ℚ))⟩,
      ⟨_, PolyFueled.const 1⟩, ⟨_, PolyFueled.const (Encodable.encode (2:ℚ))⟩]
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    exacts [⟨_, PolyFueled.const 1⟩, ⟨_, PolyFueled.const (Encodable.encode (2:ℚ))⟩,
      ⟨_, PolyFueled.const 3⟩]
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨_, PolyFueled.const 0⟩, ⟨_, PolyFueled.const (Encodable.encode φ)⟩,
      ⟨_, PolyFueled.id⟩, ⟨_, PolyFueled.const 3⟩, ⟨_, PolyFueled.const 3⟩,
      ⟨_, PolyFueled.const 2⟩, ⟨_, PolyFueled.const 4⟩, ⟨_, PolyFueled.const 6⟩,
      ⟨_, PolyFueled.const (Encodable.encode φ)⟩]
  · intro n
    show serializeTrades [(ndBeta φ n, φ)] = _
    rw [serializeTrades, serializeTrades, serialize_ndBeta]
    simp

/-! ### The criterion application -/

/-- **Non-Dogmatism, weak fragment** (`thm:nd`): under a logical inductor with `φ`-prices
in `[0,1]`, if `φ`-satisfying plausible worlds keep existing (the per-day semantic
rendering of `Θ ⊬ ¬φ`), the price is eventually at least `2^{-(n+2)}`. Weaker than the
paper's `thm:nd` (the bound decays with `n`); the liminf form is the budget-halving
trader's job (Phase B2). -/
theorem lic_nonDogmatism_weak (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence)
    (hP0 : ∀ n, 0 ≤ P n φ) (hP1 : ∀ n, P n φ ≤ 1)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) :
    ∀ᶠ n in atTop, 1 / 2 ^ (n + 2) ≤ P n φ := by
  by_contra h
  rw [not_eventually] at h
  have hfreq : ∃ᶠ n in atTop, P n φ < 1 / 2 ^ (n + 2) :=
    h.mono (fun n hn => not_le.mp hn)
  exact hLI.noExploit (ndTrader φ) (ndTrader_ecTok φ)
    (ndTrader_exploits P DP φ hP0 hP1 hφ hfreq)

#print axioms lic_nonDogmatism_weak

end LogicalInduction
