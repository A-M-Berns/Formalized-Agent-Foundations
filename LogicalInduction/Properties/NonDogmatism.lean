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
import LogicalInduction.Properties.Hysteresis

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

/-! ## Full `thm:nd` — the scale-ladder trader

Paper (`main.tex` 1533, sketch; `app:obu`/`lem:type2`, 5556 ff., the formal construction):
the trader "spend[s] their first 50 cents when `Pₙ(φ) < 1/2` … their next 25 cents when
`Pₙ(φ) < 1/4`", one rung per scale, so that under `liminf Pₙφ = 0` every rung eventually
fires and plausible profits diverge while total spend stays bounded.

**Two modeling findings, disclosed here rather than discovered later:**

1. *The recursive budget trader is not poly-size expressible as an `EF` tree.* The natural
   state `r(n+1) = r n − Pₙ·ctsind(Pₙ < r n/2)` uses `r n` twice (once bare, once inside
   the clip), so its tree doubles per day. No single-occurrence recursion can repair this:
   a chain that consumes its state once is a composition of unary affine/`max`/`min` steps,
   hence *monotone or antitone* in the state, while the budget update is genuinely
   non-monotone. The paper's own `app:obu` trader dodges this — its state update
   `α(n+1) = α n + (k+1−α n)·Lₙ` is affine in `α`, i.e. `α n·(1−Lₙ) + (k+1)·Lₙ`, single
   occurrence — and in product form (`remaining shares = target·Π(1−Lᵢ)`) it is exactly the
   `hystN` chain shape from `thm:con`. (The paper certifies its version by dynamic
   programming, `app:dynamicprogramming` — sharing our tree `dd:dsl` does not have.)

2. *The paper's constants are rescaled polynomially for `dd:fuel`.* The fuel-clocked
   interpreter prices tokens by **value**, and the encodings of `2^{-j}`-style rationals
   are exponentially large values. Rung `j` here buys up to `j³` shares below the price
   `1/j³` at weight `1/j²` (trade coefficient constant `j = j³/j²`): total spend
   `≤ Σ 1/j² ≤ 2`, and a fired rung `j` banks `j·(1 − 1/j³) ≥ j − 1` — same economics,
   poly-value constants.

Rungs are padded with degenerate (`δ = 0`, identically-zero) `ctsind` factors on days
before their start day `j`, so every rung's arming chain has the same, uniform-width
serialization — the shape the (pending) doubly-indexed emission needs. -/

/-! ### The generic arming chain -/

/-- Arming chain over a per-day disarm signal: `armChain sig n = Π_{i<n} (1 − sig i)`.
With `sig i ∈ [0,1]` it decays from `1` toward `0`, and the *shares telescope*: the total
of `armChain · sig` over any window is the drop in the chain's value. Shared by the buy
and sell ladders. -/
def armChain (sig : ℕ → EF) : ℕ → EF
  | 0 => .const 1
  | (n + 1) => .mul (armChain sig n) (oneMinus (sig n))

theorem armChain_denote_zero (sig : ℕ → EF) (P : History) :
    (armChain sig 0).denote P = 1 := by simp [armChain]

theorem armChain_denote_succ (sig : ℕ → EF) (P : History) (n : ℕ) :
    (armChain sig (n + 1)).denote P
      = (armChain sig n).denote P * (1 - (sig n).denote P) := by
  simp [armChain, EF.denote_mul, Pi.mul_apply, oneMinus_denote]

theorem armChain_mem (sig : ℕ → EF) (P : History)
    (hs : ∀ i, 0 ≤ (sig i).denote P ∧ (sig i).denote P ≤ 1) :
    ∀ n, 0 ≤ (armChain sig n).denote P ∧ (armChain sig n).denote P ≤ 1
  | 0 => by rw [armChain_denote_zero]; norm_num
  | (n + 1) => by
      obtain ⟨ih0, ih1⟩ := armChain_mem sig P hs n
      obtain ⟨hs0, hs1⟩ := hs n
      rw [armChain_denote_succ]
      constructor
      · nlinarith
      · nlinarith

/-- Padded-start rungs stay fully armed until their start day. -/
theorem armChain_denote_of_le (sig : ℕ → EF) (P : History) {j : ℕ}
    (hpad : ∀ i < j, (sig i).denote P = 0) :
    ∀ n, n ≤ j → (armChain sig n).denote P = 1 := by
  intro n
  induction n with
  | zero => intro _; exact armChain_denote_zero sig P
  | succ n ih =>
      intro h
      rw [armChain_denote_succ, ih (by omega), hpad n (by omega)]
      ring

/-- The shares telescope: `Σ_{n ∈ [j, N)} armChain·sig = armChain j − armChain N`. -/
theorem armChain_shares_sum (sig : ℕ → EF) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, (armChain sig n).denote P * (sig n).denote P
      = (armChain sig j).denote P - (armChain sig N).denote P := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ih, armChain_denote_succ]
      ring

theorem armChain_rank (sig : ℕ → EF) (hs : ∀ i, (sig i).rank ≤ i) :
    ∀ n, (armChain sig n).rank ≤ n - 1
  | 0 => by simp [armChain, EF.rank]
  | (n + 1) => by
      have ih := armChain_rank sig hs n
      have hn := hs n
      simp only [armChain, EF.rank, oneMinus_rank, max_le_iff]
      omega

/-! ### Rung constants -/

/-- Rung-`j` threshold: `1/(2j³)`. The rung's `ctsind` is `1` below `ndThr j` and `0` above
`2·ndThr j = 1/j³`; both the threshold and the rung weight `1/j²` have poly-**value**
rational encodings (`dd:fuel`), unlike the paper's `2^{-j}` ladder. -/
def ndThr (j : ℕ) : ℚ := 1 / (2 * (j : ℚ) ^ 3)

/-- Ramp-width schedule with padding: `0` before the rung's start day `j` (a degenerate
`ctsind` that is identically `0`, since `1/0 = 0` in `ℚ`), `ndThr j` from day `j` on. -/
def ndPadThr (j n : ℕ) : ℚ := if n < j then 0 else ndThr j

theorem ndThr_cast (j : ℕ) : ((ndThr j : ℚ) : ℝ) = 1 / (2 * (j : ℝ) ^ 3) := by
  rw [ndThr]; push_cast; ring

theorem ndThr_pos {j : ℕ} (hj : 1 ≤ j) : 0 < ((ndThr j : ℚ) : ℝ) := by
  rw [ndThr_cast]
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le one_pos h1
  exact div_pos one_pos (by nlinarith [pow_pos h0 3])

theorem ndThr_double {j : ℕ} (hj : 1 ≤ j) :
    ((ndThr j : ℚ) : ℝ) + ((ndThr j : ℚ) : ℝ) = 1 / (j : ℝ) ^ 3 := by
  rw [ndThr_cast]
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le one_pos h1
  have h3 : ((j : ℝ)) ^ 3 ≠ 0 := ne_of_gt (pow_pos h0 3)
  field_simp
  ring

theorem ndCube_le_one {j : ℕ} (hj : 1 ≤ j) : 1 / (j : ℝ) ^ 3 ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le one_pos h1
  rw [div_le_one (pow_pos h0 3)]
  exact one_le_pow₀ h1

theorem ndWeight_mul {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) * (1 / (j : ℝ) ^ 3) = 1 / (j : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (j : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos h1)
  field_simp

/-! ### The buy rungs -/

/-- Rung-`j` day-`i` buy trigger: `ctsind(Pᵢφ < 1/j³)` once live (`i ≥ j`), identically
`0` before (the `δ = 0` padding). -/
def ndBuySig (φ : Sentence) (j i : ℕ) : EF := buyIndEF φ (ndThr j) (ndPadThr j i) i

theorem ndBuySig_live (φ : Sentence) {j i : ℕ} (h : j ≤ i) :
    ndBuySig φ j i = buyIndEF φ (ndThr j) (ndThr j) i := by
  rw [ndBuySig, ndPadThr, if_neg (by omega)]

theorem ndBuySig_denote_pad (φ : Sentence) (P : History) {j i : ℕ} (h : i < j) :
    (ndBuySig φ j i).denote P = 0 := by
  rw [ndBuySig, ndPadThr, if_pos h, buyIndEF_denote]
  norm_num

theorem ndBuySig_mem (φ : Sentence) (P : History) (j i : ℕ) :
    0 ≤ (ndBuySig φ j i).denote P ∧ (ndBuySig φ j i).denote P ≤ 1 :=
  buyInd_mem φ _ _ i P

theorem ndBuySig_pos_imp (φ : Sentence) (P : History) {j i : ℕ} (hj : 1 ≤ j)
    (h : 0 < (ndBuySig φ j i).denote P) : P i φ < 1 / (j : ℝ) ^ 3 := by
  rcases lt_or_ge i j with hij | hij
  · rw [ndBuySig_denote_pad φ P hij] at h
    exact absurd h (lt_irrefl 0)
  · rw [ndBuySig_live φ hij] at h
    have hlt := buyInd_pos_imp (ndThr_pos hj) h
    rwa [ndThr_double hj] at hlt

theorem ndBuySig_eq_one (φ : Sentence) (P : History) {j i : ℕ} (hj : 1 ≤ j) (hlive : j ≤ i)
    (h : P i φ < ((ndThr j : ℚ) : ℝ)) : (ndBuySig φ j i).denote P = 1 := by
  rw [ndBuySig_live φ hlive]
  exact buyInd_eq_one (ndThr_pos hj) h

theorem ndBuySig_rank (φ : Sentence) (j i : ℕ) : (ndBuySig φ j i).rank = i :=
  buyIndEF_rank φ _ _ i

/-- Day-`n` shares bought by rung `j` (per unit of the coefficient constant `j`):
`armChain · trigger ∈ [0, 1]`. -/
noncomputable def ndShares (φ : Sentence) (P : History) (j n : ℕ) : ℝ :=
  (armChain (ndBuySig φ j) n).denote P * (ndBuySig φ j n).denote P

theorem ndShares_nonneg (φ : Sentence) (P : History) (j n : ℕ) : 0 ≤ ndShares φ P j n :=
  mul_nonneg (armChain_mem _ P (fun i => ndBuySig_mem φ P j i) n).1
    (ndBuySig_mem φ P j n).1

theorem ndShares_pos_sig {φ : Sentence} {P : History} {j n : ℕ}
    (h : 0 < ndShares φ P j n) : 0 < (ndBuySig φ j n).denote P := by
  rcases (ndBuySig_mem φ P j n).1.lt_or_eq with hs | hs
  · exact hs
  · rw [ndShares, ← hs, mul_zero] at h
    exact absurd h (lt_irrefl 0)

/-- Rung-`j` lifetime shares by day `N`: exactly the arming drop, hence `≤ 1`. -/
theorem ndShares_sum (φ : Sentence) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, ndShares φ P j n
      = 1 - (armChain (ndBuySig φ j) N).denote P := by
  simp only [ndShares]
  rw [armChain_shares_sum (ndBuySig φ j) P h,
    armChain_denote_of_le (ndBuySig φ j) P
      (fun i hi => ndBuySig_denote_pad φ P hi) j le_rfl]

theorem ndShares_sum_le_one (φ : Sentence) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, ndShares φ P j n ≤ 1 := by
  rw [ndShares_sum φ P h]
  have := (armChain_mem (ndBuySig φ j) P (fun i => ndBuySig_mem φ P j i) N).1
  linarith

/-- Rung-`j` day-`n` trade coefficient: `j · armChain · trigger` — up to `j³` shares at
weight `1/j²` each, i.e. coefficient constant `j³/j² = j`. -/
def ndCoef (φ : Sentence) (j n : ℕ) : EF :=
  .mul (.const (j : ℚ)) (.mul (armChain (ndBuySig φ j) n) (ndBuySig φ j n))

theorem ndCoef_denote (φ : Sentence) (P : History) (j n : ℕ) :
    (ndCoef φ j n).denote P = (j : ℝ) * ndShares φ P j n := by
  simp only [ndCoef, EF.denote_mul, EF.denote_const, Pi.mul_apply, ndShares]
  push_cast
  ring

theorem ndCoef_rank (φ : Sentence) (j n : ℕ) : (ndCoef φ j n).rank ≤ n := by
  have h1 := armChain_rank (ndBuySig φ j) (fun i => (ndBuySig_rank φ j i).le) n
  have h2 := (ndBuySig_rank φ j n).le
  simp only [ndCoef, EF.rank, max_le_iff]
  omega

/-! ### The ladder and the trader -/

/-- The day-`n` ladder: `Σ_{j=1}^{m} ndCoef j n` (left-nested adds). -/
def ndLadderEF (φ : Sentence) (n : ℕ) : ℕ → EF
  | 0 => .const 0
  | (m + 1) => .add (ndLadderEF φ n m) (ndCoef φ (m + 1) n)

theorem ndLadderEF_denote (φ : Sentence) (P : History) (n : ℕ) : ∀ m,
    (ndLadderEF φ n m).denote P
      = ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * ndShares φ P (k + 1) n
  | 0 => by simp [ndLadderEF]
  | (m + 1) => by
      rw [ndLadderEF]
      simp only [EF.denote_add, Pi.add_apply]
      rw [ndLadderEF_denote φ P n m, Finset.sum_range_succ, ndCoef_denote]

theorem ndLadderEF_rank (φ : Sentence) (n : ℕ) : ∀ m, (ndLadderEF φ n m).rank ≤ n
  | 0 => by simp [ndLadderEF, EF.rank]
  | (m + 1) => by
      have h1 := ndLadderEF_rank φ n m
      have h2 := ndCoef_rank φ (m + 1) n
      simp only [ndLadderEF, EF.rank, max_le_iff]
      omega

/-- The **scale-ladder non-dogmatism trader** (`thm:nd`, `app:obu` shape): on day `n`,
rung `j ≤ n` buys `j · armChainⱼ · ctsind(Pₙφ < 1/j³)` shares of `φ`. -/
def ndLadderTrader (φ : Sentence) : Trader where
  strat n := { trades := [(ndLadderEF φ n n, φ)]
               rank_le := by
                 intro p hp
                 simp only [List.mem_singleton] at hp
                 subst hp
                 exact ndLadderEF_rank φ n n }

@[simp] theorem ndLadderTrader_value (φ : Sentence) (V : History) (w : Sentence → ℝ)
    (n : ℕ) : ((ndLadderTrader φ).strat n).value V w
      = (ndLadderEF φ n n).denote V * (w φ - V n φ) := by
  simp [ndLadderTrader, Strategy.value]

theorem ndLadderTrader_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (ndLadderTrader φ).netWorth V v m
      = ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range n,
          ((k + 1 : ℕ) : ℝ) * ndShares φ V (k + 1) n * (v.payout φ - V n φ) := by
  simp only [Trader.netWorth, ndLadderTrader_value, ndLadderEF_denote, Finset.sum_mul]

/-! ### The economics -/

/-- Triangle swap for the ladder's double sums. -/
private theorem sum_range_triangle_comm (f : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range n, f k n
      = ∑ k ∈ Finset.range N, ∑ n ∈ Finset.Ico (k + 1) N, f k n := by
  simp only [Finset.range_eq_Ico]
  exact (Finset.sum_Ico_Ico_comm' 0 N (fun k n => f k n)).symm

/-- `Σ_{k<M} 1/(k+1)² ≤ 2` — the ladder's total-spend bound. -/
theorem sum_inv_sq_le_two (M : ℕ) :
    ∑ k ∈ Finset.range M, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  have key : ∀ N : ℕ, 1 ≤ N →
      ∑ k ∈ Finset.range N, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 - 1 / (N : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N hN ih =>
        rw [Finset.sum_range_succ]
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have hstep : (1 : ℝ) / ((N : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
          rw [div_sub_div _ _ (by nlinarith) (by nlinarith),
            div_le_div_iff₀ (by nlinarith) (by nlinarith)]
          ring_nf
          nlinarith
        push_cast at ih ⊢
        linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have h := key M hM
    have h1 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) < 1 / (M : ℝ) := by positivity
    linarith

/-- In **any** world, the rung-`j` day-`n` value term loses at most `shares/j²`
(spend happens only below the price `1/j³`, and `j·(1/j³) = 1/j²`). -/
theorem ndTerm_ge (φ : Sentence) (P : History) (v : PCWorld) {j : ℕ} (hj : 1 ≤ j)
    (n : ℕ) : -(ndShares φ P j n * (1 / (j : ℝ) ^ 2))
      ≤ (j : ℝ) * ndShares φ P j n * (v.payout φ - P n φ) := by
  have hb := ndShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hP := ndBuySig_pos_imp φ P hj (ndShares_pos_sig hb')
    have hpay : 0 ≤ v.payout φ := by rw [PCWorld.payout]; split <;> norm_num
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hjb : 0 < (j : ℝ) * ndShares φ P j n := mul_pos (by linarith) hb'
    have hge : -(1 / (j : ℝ) ^ 3) ≤ v.payout φ - P n φ := by linarith
    calc -(ndShares φ P j n * (1 / (j : ℝ) ^ 2))
        = (j : ℝ) * ndShares φ P j n * (-(1 / (j : ℝ) ^ 3)) := by
          rw [← ndWeight_mul hj]; ring
      _ ≤ (j : ℝ) * ndShares φ P j n * (v.payout φ - P n φ) :=
          mul_le_mul_of_nonneg_left hge hjb.le
  · rw [← hb']
    norm_num

/-- In a `φ`-world every rung's term is a gain: shares are bought below `1/j³ ≤ 1`. -/
theorem ndTerm_nonneg (φ : Sentence) (P : History) (v : PCWorld) (hv : v.Holds φ)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    0 ≤ (j : ℝ) * ndShares φ P j n * (v.payout φ - P n φ) := by
  have hb := ndShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hP := ndBuySig_pos_imp φ P hj (ndShares_pos_sig hb')
    have hpay : v.payout φ = 1 := by rw [PCWorld.payout, if_pos hv]
    have hle := ndCube_le_one hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [hpay]
    exact mul_nonneg (mul_nonneg (by linarith) hb'.le) (by linarith)
  · rw [← hb']
    norm_num

/-- In a `φ`-world the rung-`j` term banks at least `j·shares·(1 − 1/j³)`. -/
theorem ndTerm_profit (φ : Sentence) (P : History) (v : PCWorld) (hv : v.Holds φ)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    (j : ℝ) * ndShares φ P j n * (1 - 1 / (j : ℝ) ^ 3)
      ≤ (j : ℝ) * ndShares φ P j n * (v.payout φ - P n φ) := by
  have hpay : v.payout φ = 1 := by rw [PCWorld.payout, if_pos hv]
  rw [hpay]
  have hb := ndShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hP := ndBuySig_pos_imp φ P hj (ndShares_pos_sig hb')
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (by linarith) hb'.le)
  · rw [← hb']
    norm_num

/-- **The exploitation** (`thm:nd`): if the price frequently dips below every positive
threshold, the scale-ladder trader exploits — every rung eventually fires, banking
`≥ j − 1` in the plausible `φ`-worlds, while total spend stays `≤ 2` in every world. -/
theorem ndLadderTrader_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ)
    (hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, P n φ < ε) :
    (ndLadderTrader φ).Exploits P DP := by
  refine exploits_of_bddBelow_of_unbounded _ _ _ 2 ?_ ?_
  · -- Bounded below by −2: rung `j` spends at most `1/j²` in every world.
    rintro x ⟨m, v, hv, rfl⟩
    rw [ndLadderTrader_netWorth, sum_range_triangle_comm]
    have hk : ∀ k ∈ Finset.range (m + 1),
        -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)
          ≤ ∑ n ∈ Finset.Ico (k + 1) (m + 1),
              ((k + 1 : ℕ) : ℝ) * ndShares φ P (k + 1) n * (v.payout φ - P n φ) := by
      intro k hkm
      have hj : 1 ≤ k + 1 := by omega
      have hsum := ndShares_sum_le_one φ P
        (j := k + 1) (N := m + 1) (by simp only [Finset.mem_range] at hkm; omega)
      have hw2 : (0 : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
      calc -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)
          ≤ -((∑ n ∈ Finset.Ico (k + 1) (m + 1), ndShares φ P (k + 1) n)
              * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
            have h1 := mul_le_mul_of_nonneg_right hsum hw2
            rw [one_mul] at h1
            linarith
        _ = ∑ n ∈ Finset.Ico (k + 1) (m + 1),
              -(ndShares φ P (k + 1) n * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
            rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
        _ ≤ _ := Finset.sum_le_sum (fun n _ => ndTerm_ge φ P v hj n)
    calc (-2 : ℝ)
        ≤ -∑ k ∈ Finset.range (m + 1), (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
          have := sum_inv_sq_le_two (m + 1)
          linarith
      _ = ∑ k ∈ Finset.range (m + 1), -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum hk
  · -- Unbounded: rung `j > B + 1` fires at its first dip below `ndThr j` past day `j`.
    intro B
    obtain ⟨j', hj'⟩ := exists_nat_gt B
    have hj : 1 ≤ j' + 1 := by omega
    have hθ := ndThr_pos (j := j' + 1) hj
    obtain ⟨n₀, hn₀, hdip⟩ := (Filter.frequently_atTop.mp (hfreq _ hθ)) (j' + 1)
    obtain ⟨v, hv, hvφ⟩ := hφ n₀
    refine ⟨(ndLadderTrader φ).netWorth P v n₀, ⟨n₀, v, hv, rfl⟩, ?_⟩
    rw [ndLadderTrader_netWorth, sum_range_triangle_comm]
    have hterm : ∀ k ∈ Finset.range (n₀ + 1),
        0 ≤ ∑ n ∈ Finset.Ico (k + 1) (n₀ + 1),
            ((k + 1 : ℕ) : ℝ) * ndShares φ P (k + 1) n * (v.payout φ - P n φ) :=
      fun k _ => Finset.sum_nonneg (fun n _ => ndTerm_nonneg φ P v hvφ (by omega) n)
    have hjmem : j' ∈ Finset.range (n₀ + 1) := Finset.mem_range.mpr (by omega)
    -- the rung-(j'+1) slice alone exceeds B
    have harm0 : (armChain (ndBuySig φ (j' + 1)) (n₀ + 1)).denote P = 0 := by
      rw [armChain_denote_succ, ndBuySig_eq_one φ P hj hn₀ hdip]
      ring
    have hsum1 : ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1), ndShares φ P (j' + 1) n = 1 := by
      rw [ndShares_sum φ P (by omega), harm0, sub_zero]
    have hj1 : (1 : ℝ) ≤ ((j' + 1 : ℕ) : ℝ) := by exact_mod_cast hj
    have hslice : ((j' + 1 : ℕ) : ℝ) - 1
        ≤ ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
            ((j' + 1 : ℕ) : ℝ) * ndShares φ P (j' + 1) n * (v.payout φ - P n φ) := by
      have hw := ndWeight_mul (j := j' + 1) hj
      have hsq : 1 / ((j' + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by nlinarith)]
        nlinarith
      calc ((j' + 1 : ℕ) : ℝ) - 1
          ≤ ((j' + 1 : ℕ) : ℝ) * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3) := by nlinarith
        _ = ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
              ((j' + 1 : ℕ) : ℝ) * ndShares φ P (j' + 1) n
                * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3) := by
            have hfac : ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
                  ((j' + 1 : ℕ) : ℝ) * ndShares φ P (j' + 1) n
                    * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3)
                = (((j' + 1 : ℕ) : ℝ) * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3))
                    * ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1), ndShares φ P (j' + 1) n := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n _ => by ring)
            rw [hfac, hsum1, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun n _ => ndTerm_profit φ P v hvφ hj n)
    have hB : B < ((j' + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
    have hsingle := Finset.single_le_sum hterm hjmem
    linarith

#print axioms ndLadderTrader_exploits

/-- Efficient computability of the scale-ladder trader. The trader is genuinely
poly-size — day `n` carries `n` rungs, each a uniform-width padded chain of `n` blocks,
`Θ(n²)` tokens with poly-value constants — but certifying it through `dd:fuel` needs
three pieces the emission toolkit does not yet have:

1. **runtime-divisor `divmod`** (`divmodc` bakes the divisor into the code; here the
   block width is `Θ(n)`, known only at runtime);
2. **`PolySegStream.concat`** — `n`-fold segment concatenation (`.append` is binary;
   the day-`n` stream is `n` rung chunks);
3. **poly-fueled emission of rung-varying rational constants** — the tokens
   `⌜ndThr j⌝`, `⌜(j : ℚ)⌝` vary with the rung, so the emitter must compute
   `Encodable.encode` of these rationals from `j` inside the fuel budget (poly-value by
   the `1/j³` rescaling, but the encoding functions still need `PolyFueled` codes).

This is the plan's known B2 decision point (growing-width blocks), plus the new
finding that parametric-family traders (the paper's "efficiently emulatable sequences",
`app:preliminaries`.3) need constant-token emission our kit hasn't exercised. -/
theorem ndLadderTrader_ecTok (φ : Sentence) :
    EfficientlyComputableTok (ndLadderTrader φ) := by
  sorry -- TODO(blueprint:def:ec): runtime-divisor divmod + PolySegStream.concat + poly-fueled ℚ-constant tokens

/-- **Non-Dogmatism, positive direction** (`thm:nd`): under a logical inductor, if
`φ`-satisfying plausible worlds keep existing (the per-day semantic rendering of
`Θ ⊬ ¬φ`), the price is eventually bounded away from `0`. No price-range hypotheses:
the ladder's economics localize to its trigger bands.

Depends on the `ndLadderTrader_ecTok` `sorry` (emission cert pending); the trader and
its exploitation are fully proved. -/
theorem lic_nonDogmatism (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ε ≤ P n φ := by
  by_contra h
  have hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, P n φ < ε := by
    intro ε hε
    by_contra h'
    rw [Filter.not_frequently] at h'
    exact h ⟨ε, hε, h'.mono (fun n hn => le_of_not_gt hn)⟩
  exact hLI.noExploit (ndLadderTrader φ) (ndLadderTrader_ecTok φ)
    (ndLadderTrader_exploits P DP φ hφ hfreq)

#print axioms lic_nonDogmatism

end LogicalInduction
