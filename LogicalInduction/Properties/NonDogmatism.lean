/-
# `thm:nd` — Non-Dogmatism (paper §4.6; appendix `app:nondog`)

Paper statement: if `Θ ⊬ ¬φ` then `P∞(φ) > 0`, and if `Θ ⊬ φ` then `P∞(φ) < 1`.

**Modeling substitution, disclosed.** The syntactic hypothesis `Θ ⊬ ¬φ` is rendered
semantically and per-day — "`φ`-satisfying plausible worlds keep existing", i.e.
`∀ n, ∃ v, v.ConsistentWith (DP.D n) ∧ v.Holds φ` — the `def:lang`-level reading of `⊬`.
The dual direction uses the mirrored condition with `¬ v.Holds φ`.

Contents:
* `lic_nonDogmatism_weak` — a decaying-bound fragment (eventually `Pₙφ ≥ 2^{-(n+2)}`),
  proved by a memoryless one-day-at-a-time trader; retained beside the full theorem.
* `lic_nonDogmatism`, `lic_nonDogmatism_dual` — the two directions of `thm:nd`, via the
  buy and sell scale ladders (the trader shape the paper uses in `app:obu`).
* `lic_limit_pos`, `lic_limit_lt_one` — the limit forms `P∞(φ) > 0` and `P∞(φ) < 1`,
  taking price convergence as a hypothesis.
-/
import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.Hysteresis

namespace LogicalInduction

open Filter Topology

/-! ## The weak fragment: a decaying lower bound

The trader is memoryless: on day `n` it buys `β n = max 0 (1 − 2^{n+1}·Pₙφ)` shares of
`φ`. Its day-`n` spend is `β n · Pₙφ ≤ 2^{-(n+1)}`, so total spend is `≤ 1` in every
world. If the price frequently dips below `2^{-(n+2)}`, the signal fires with `β ≥ 1/2`
while a plausible `φ`-world pays `1 − Pₙφ ≥ 1/2` per share, so each dip banks `≥ 1/4` of
`φ`-world value and the dips accumulate without bound. -/

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

lemma serialize_twoPowChain : ∀ k,
    (twoPowChain k).serialize
      = [1, Encodable.encode (2 : ℚ)]
        ++ (List.range k).flatMap (fun _ => [1, Encodable.encode (2 : ℚ), 3])
  | 0 => by simp [twoPowChain, EF.serialize]
  | (k + 1) => by
      rw [twoPowChain, EF.serialize, serialize_twoPowChain k, List.range_succ]
      simp [EF.serialize]

/-! ### The trader (`def:trader`) -/

/-- Day-`n` buy signal: `max 0 (1 − 2^{n+1}·φ*ⁿ)` — fires only when the price is below
`2^{-(n+1)}`, at slope `2^{n+1}`. -/
def ndBeta (φ : Sentence) (n : ℕ) : EF :=
  .max (.const 0)
    (.add (.const 1) (.mul (.const (-1)) (.mul (twoPowChain n) (.price φ n))))

lemma ndBeta_denote (φ : Sentence) (P : History) (n : ℕ) :
    (ndBeta φ n).denote P = max 0 (1 - 2 ^ (n + 1) * P n φ) := by
  simp only [ndBeta, EF.denote_max, EF.denote_add, EF.denote_mul, EF.denote_const,
    EF.denote_price, twoPowChain_denote, Pi.add_apply, Pi.mul_apply]
  norm_num [sub_eq_add_neg, neg_mul]

lemma ndBeta_rank (φ : Sentence) (n : ℕ) : (ndBeta φ n).rank ≤ n := by
  simp [ndBeta, EF.rank]

/-- The non-dogmatism trader: `β n` shares of `φ` daily. -/
def ndTrader (φ : Sentence) : Trader where
  strat n := { trades := [(ndBeta φ n, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact ndBeta_rank φ n }

@[simp] theorem ndTrader_value (φ : Sentence) (V : History) (w : Sentence → ℝ) (n : ℕ) :
    ((ndTrader φ).strat n).value V w = (ndBeta φ n).denote V * (w φ - V n φ) := by
  simp [ndTrader, Strategy.value]

lemma ndTrader_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (ndTrader φ).netWorth V v m
      = ∑ i ∈ Finset.range (m + 1), (ndBeta φ i).denote V * (v.payout φ - V i φ) := by
  simp [Trader.netWorth]

/-! ### The economics -/

lemma ndBeta_nonneg (φ : Sentence) (P : History) (n : ℕ) :
    0 ≤ (ndBeta φ n).denote P := by
  rw [ndBeta_denote]; exact le_max_left _ _

/-- Day-`n` spend bound: `β n · Pₙφ ≤ 2^{-(n+1)}` (support of the signal is
`Pₙφ < 2^{-(n+1)}` and `β ≤ 1` there). -/
lemma ndBeta_mul_price_le (φ : Sentence) (P : History) (n : ℕ) (hP0 : 0 ≤ P n φ) :
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
lemma sum_inv_twoPow_le_one (m : ℕ) :
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
lemma ndBeta_trigger (φ : Sentence) (P : History) (n : ℕ)
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

/-! ### Efficient computability, via `ecTok_of_blockStream` -/

theorem serialize_ndBeta (φ : Sentence) (n : ℕ) :
    (ndBeta φ n).serialize
      = [1, Encodable.encode (0:ℚ), 1, Encodable.encode (1:ℚ), 1, Encodable.encode (-1:ℚ),
         1, Encodable.encode (2:ℚ)]
        ++ (List.range n).flatMap (fun _ => [1, Encodable.encode (2:ℚ), 3])
        ++ [0, Encodable.encode φ, n, 3, 3, 2, 4] := by
  simp [ndBeta, EF.serialize, serialize_twoPowChain]

/-- `ndTrader φ` is efficiently computable: its stream is 8 head tokens, `n` homogeneous
width-3 blocks (the pow-chain), and a 9-token tail carrying the day index. -/
lemma ndTrader_ecTok (φ : Sentence) : EfficientlyComputableTok (ndTrader φ) := by
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

/-- **Non-Dogmatism, weak fragment** (`thm:nd`): under a logical inductor, if
`φ`-satisfying plausible worlds keep existing (the per-day semantic rendering of
`Θ ⊬ ¬φ`), the price is eventually at least `2^{-(n+2)}`.

RETAINED FRAGMENT — strictly weaker than the paper's `thm:nd`, because the bound decays
with `n` rather than being bounded away from `0`. It is kept beside the faithful form
`lic_nonDogmatism` below, which supersedes it. The price range is carried by
`IsLogicalInductor`.
Paper node: `thm:nd` -/
theorem lic_nonDogmatism_weak (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) :
    ∀ᶠ n in atTop, 1 / 2 ^ (n + 2) ≤ P n φ := by
  have hP0 : ∀ n, 0 ≤ P n φ := fun n => (hLI.price_mem_Icc n φ).1
  have hP1 : ∀ n, P n φ ≤ 1 := fun n => (hLI.price_mem_Icc n φ).2
  by_contra h
  rw [not_eventually] at h
  have hfreq : ∃ᶠ n in atTop, P n φ < 1 / 2 ^ (n + 2) :=
    h.mono (fun n hn => not_le.mp hn)
  exact hLI.noExploitTok (ndTrader φ) (ndTrader_ecTok φ)
    (ndTrader_exploits P DP φ hP0 hP1 hφ hfreq)

#print axioms lic_nonDogmatism_weak

/-! ## Full `thm:nd` — the scale-ladder trader

Paper: the §4.6 proof sketch, with the formal construction in `app:obu` via `lem:type2`.
The trader "spend[s] their first 50 cents when `Pₙ(φ) < 1/2` … their next 25 cents when
`Pₙ(φ) < 1/4`", one rung per scale, so that under `liminf Pₙφ = 0` every rung eventually
fires and plausible profits diverge while total spend stays bounded.

**Two modeling deviations from the paper's trader, disclosed:**

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
serialization — the shape the doubly-indexed token emission needs. -/

/-! ### The generic arming chain -/

/-- Arming chain over a per-day disarm signal: `armChain sig n = Π_{i<n} (1 − sig i)`.
With `sig i ∈ [0,1]` it decays from `1` toward `0`, and the *shares telescope*: the total
of `armChain · sig` over any window is the drop in the chain's value. Shared by the buy
and sell ladders. -/
def armChain (sig : ℕ → EF) : ℕ → EF
  | 0 => .const 1
  | (n + 1) => .mul (armChain sig n) (oneMinus (sig n))

lemma armChain_denote_zero (sig : ℕ → EF) (P : History) :
    (armChain sig 0).denote P = 1 := by simp [armChain]

lemma armChain_denote_succ (sig : ℕ → EF) (P : History) (n : ℕ) :
    (armChain sig (n + 1)).denote P
      = (armChain sig n).denote P * (1 - (sig n).denote P) := by
  simp [armChain, EF.denote_mul, Pi.mul_apply, oneMinus_denote]

lemma armChain_mem (sig : ℕ → EF) (P : History)
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
lemma armChain_denote_of_le (sig : ℕ → EF) (P : History) {j : ℕ}
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
lemma armChain_shares_sum (sig : ℕ → EF) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, (armChain sig n).denote P * (sig n).denote P
      = (armChain sig j).denote P - (armChain sig N).denote P := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ih, armChain_denote_succ]
      ring

lemma armChain_rank (sig : ℕ → EF) (hs : ∀ i, (sig i).rank ≤ i) :
    ∀ n, (armChain sig n).rank ≤ n - 1
  | 0 => by simp [armChain]
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

lemma ndThr_cast (j : ℕ) : ((ndThr j : ℚ) : ℝ) = 1 / (2 * (j : ℝ) ^ 3) := by
  rw [ndThr]; push_cast; ring

lemma ndThr_pos {j : ℕ} (hj : 1 ≤ j) : 0 < ((ndThr j : ℚ) : ℝ) := by
  rw [ndThr_cast]
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le one_pos h1
  exact div_pos one_pos (by nlinarith [pow_pos h0 3])

lemma ndThr_double {j : ℕ} (hj : 1 ≤ j) :
    ((ndThr j : ℚ) : ℝ) + ((ndThr j : ℚ) : ℝ) = 1 / (j : ℝ) ^ 3 := by
  rw [ndThr_cast]
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le one_pos h1
  have h3 : ((j : ℝ)) ^ 3 ≠ 0 := ne_of_gt (pow_pos h0 3)
  field_simp
  ring

lemma ndCube_le_one {j : ℕ} (hj : 1 ≤ j) : 1 / (j : ℝ) ^ 3 ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le one_pos h1
  rw [div_le_one (pow_pos h0 3)]
  exact one_le_pow₀ h1

lemma ndWeight_mul {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) * (1 / (j : ℝ) ^ 3) = 1 / (j : ℝ) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h0 : (j : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos h1)
  field_simp

/-! ### The buy rungs -/

/-- Rung-`j` day-`i` buy trigger: `ctsind(Pᵢφ < 1/j³)` once live (`i ≥ j`), identically
`0` before (the `δ = 0` padding). -/
def ndBuySig (φ : Sentence) (j i : ℕ) : EF := buyIndEF φ (ndThr j) (ndPadThr j i) i

lemma ndBuySig_live (φ : Sentence) {j i : ℕ} (h : j ≤ i) :
    ndBuySig φ j i = buyIndEF φ (ndThr j) (ndThr j) i := by
  rw [ndBuySig, ndPadThr, if_neg (by omega)]

lemma ndBuySig_denote_pad (φ : Sentence) (P : History) {j i : ℕ} (h : i < j) :
    (ndBuySig φ j i).denote P = 0 := by
  rw [ndBuySig, ndPadThr, if_pos h, buyIndEF_denote]
  norm_num

lemma ndBuySig_mem (φ : Sentence) (P : History) (j i : ℕ) :
    0 ≤ (ndBuySig φ j i).denote P ∧ (ndBuySig φ j i).denote P ≤ 1 :=
  buyInd_mem φ _ _ i P

lemma ndBuySig_pos_imp (φ : Sentence) (P : History) {j i : ℕ} (hj : 1 ≤ j)
    (h : 0 < (ndBuySig φ j i).denote P) : P i φ < 1 / (j : ℝ) ^ 3 := by
  rcases lt_or_ge i j with hij | hij
  · rw [ndBuySig_denote_pad φ P hij] at h
    exact absurd h (lt_irrefl 0)
  · rw [ndBuySig_live φ hij] at h
    have hlt := buyInd_pos_imp (ndThr_pos hj) h
    rwa [ndThr_double hj] at hlt

lemma ndBuySig_eq_one (φ : Sentence) (P : History) {j i : ℕ} (hj : 1 ≤ j) (hlive : j ≤ i)
    (h : P i φ < ((ndThr j : ℚ) : ℝ)) : (ndBuySig φ j i).denote P = 1 := by
  rw [ndBuySig_live φ hlive]
  exact buyInd_eq_one (ndThr_pos hj) h

lemma ndBuySig_rank (φ : Sentence) (j i : ℕ) : (ndBuySig φ j i).rank = i :=
  buyIndEF_rank φ _ _ i

/-- Day-`n` shares bought by rung `j` (per unit of the coefficient constant `j`):
`armChain · trigger ∈ [0, 1]`. -/
noncomputable def ndShares (φ : Sentence) (P : History) (j n : ℕ) : ℝ :=
  (armChain (ndBuySig φ j) n).denote P * (ndBuySig φ j n).denote P

lemma ndShares_nonneg (φ : Sentence) (P : History) (j n : ℕ) : 0 ≤ ndShares φ P j n :=
  mul_nonneg (armChain_mem _ P (fun i => ndBuySig_mem φ P j i) n).1
    (ndBuySig_mem φ P j n).1

lemma ndShares_pos_sig {φ : Sentence} {P : History} {j n : ℕ}
    (h : 0 < ndShares φ P j n) : 0 < (ndBuySig φ j n).denote P := by
  rcases (ndBuySig_mem φ P j n).1.lt_or_eq with hs | hs
  · exact hs
  · rw [ndShares, ← hs, mul_zero] at h
    exact absurd h (lt_irrefl 0)

/-- Rung-`j` lifetime shares by day `N`: exactly the arming drop, hence `≤ 1`. -/
lemma ndShares_sum (φ : Sentence) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, ndShares φ P j n
      = 1 - (armChain (ndBuySig φ j) N).denote P := by
  simp only [ndShares]
  rw [armChain_shares_sum (ndBuySig φ j) P h,
    armChain_denote_of_le (ndBuySig φ j) P
      (fun i hi => ndBuySig_denote_pad φ P hi) j le_rfl]

lemma ndShares_sum_le_one (φ : Sentence) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, ndShares φ P j n ≤ 1 := by
  rw [ndShares_sum φ P h]
  have := (armChain_mem (ndBuySig φ j) P (fun i => ndBuySig_mem φ P j i) N).1
  linarith

/-- Rung-`j` day-`n` trade coefficient: `j · armChain · trigger` — up to `j³` shares at
weight `1/j²` each, i.e. coefficient constant `j³/j² = j`. -/
def ndCoef (φ : Sentence) (j n : ℕ) : EF :=
  .mul (.const (j : ℚ)) (.mul (armChain (ndBuySig φ j) n) (ndBuySig φ j n))

lemma ndCoef_denote (φ : Sentence) (P : History) (j n : ℕ) :
    (ndCoef φ j n).denote P = (j : ℝ) * ndShares φ P j n := by
  simp only [ndCoef, EF.denote_mul, EF.denote_const, Pi.mul_apply, ndShares]
  push_cast
  ring

lemma ndCoef_rank (φ : Sentence) (j n : ℕ) : (ndCoef φ j n).rank ≤ n := by
  have h1 := armChain_rank (ndBuySig φ j) (fun i => (ndBuySig_rank φ j i).le) n
  have h2 := (ndBuySig_rank φ j n).le
  simp only [ndCoef, EF.rank, max_le_iff]
  omega

/-! ### The ladder and the trader -/

/-- The day-`n` ladder: `Σ_{j=1}^{m} ndCoef j n` (left-nested adds). -/
def ndLadderEF (φ : Sentence) (n : ℕ) : ℕ → EF
  | 0 => .const 0
  | (m + 1) => .add (ndLadderEF φ n m) (ndCoef φ (m + 1) n)

lemma ndLadderEF_denote (φ : Sentence) (P : History) (n : ℕ) : ∀ m,
    (ndLadderEF φ n m).denote P
      = ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * ndShares φ P (k + 1) n
  | 0 => by simp [ndLadderEF]
  | (m + 1) => by
      rw [ndLadderEF]
      simp only [EF.denote_add, Pi.add_apply]
      rw [ndLadderEF_denote φ P n m, Finset.sum_range_succ, ndCoef_denote]

lemma ndLadderEF_rank (φ : Sentence) (n : ℕ) : ∀ m, (ndLadderEF φ n m).rank ≤ n
  | 0 => by simp [ndLadderEF]
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

lemma ndLadderTrader_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (ndLadderTrader φ).netWorth V v m
      = ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range n,
          ((k + 1 : ℕ) : ℝ) * ndShares φ V (k + 1) n * (v.payout φ - V n φ) := by
  simp only [Trader.netWorth, ndLadderTrader_value, ndLadderEF_denote, Finset.sum_mul]

/-! ### The economics -/

/-- Triangle swap for the ladder's double sums. -/
private lemma sum_range_triangle_comm (f : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range n, f k n
      = ∑ k ∈ Finset.range N, ∑ n ∈ Finset.Ico (k + 1) N, f k n := by
  simp only [Finset.range_eq_Ico]
  exact (Finset.sum_Ico_Ico_comm' 0 N (fun k n => f k n)).symm

/-- `Σ_{k<M} 1/(k+1)² ≤ 2` — the ladder's total-spend bound. -/
lemma sum_inv_sq_le_two (M : ℕ) :
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
lemma ndTerm_ge (φ : Sentence) (P : History) (v : PCWorld) {j : ℕ} (hj : 1 ≤ j)
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
lemma ndTerm_nonneg (φ : Sentence) (P : History) (v : PCWorld) (hv : v.Holds φ)
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
lemma ndTerm_profit (φ : Sentence) (P : History) (v : PCWorld) (hv : v.Holds φ)
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

/-! ### Efficient computability (the parametric-ladder emission)

The day-`n` stream is `n` rung chunks of uniform width `Θ(n)`, each: a rung-constant
head, `n` fixed-width arm blocks (only the day-index and the rung's `ℚ`-constant tokens
vary), the day-`n` trade signal, and closers. Emission: `PolySegStream.concat` over the
rungs (runtime-divisor division), `PolySegStream.blocks` within each chunk, and
poly-fueled arithmetic for the rung-varying encoded constants
(`⌜ndThr j⌝ = Nat.pair 2 (2j³)` etc. — the closed forms of `encode_rat_eq`). -/

theorem encode_rat_zero : Encodable.encode ((0 : ℚ)) = 1 := rfl

lemma ndThr_eq_inv (j : ℕ) : ndThr j = ((2 * j ^ 3 : ℕ) : ℚ)⁻¹ := by
  rw [ndThr, one_div]
  norm_cast

lemma encode_ndThr {j : ℕ} (hj : 1 ≤ j) :
    Encodable.encode (ndThr j) = Nat.pair 2 (2 * j ^ 3) := by
  have h3 : 0 < 2 * j ^ 3 := by
    have := pow_pos (show 0 < j by omega) 3
    omega
  rw [ndThr_eq_inv, encode_rat_inv_natCast h3]

lemma encode_ndThr_double {j : ℕ} (hj : 1 ≤ j) :
    Encodable.encode (ndThr j + ndThr j) = Nat.pair 2 (j ^ 3) := by
  have h3 : 0 < j ^ 3 := pow_pos (show 0 < j by omega) 3
  have heq : ndThr j + ndThr j = ((j ^ 3 : ℕ) : ℚ)⁻¹ := by
    have hx : ((j : ℚ)) ^ 3 ≠ 0 := by
      have : ((j : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      exact pow_ne_zero 3 this
    rw [ndThr]
    push_cast
    field_simp
    ring
  rw [heq, encode_rat_inv_natCast h3]

lemma encode_ndThr_recip {j : ℕ} (_hj : 1 ≤ j) :
    Encodable.encode (1 / ndThr j) = Nat.pair (4 * j ^ 3) 1 := by
  have heq : (1 : ℚ) / ndThr j = ((2 * j ^ 3 : ℕ) : ℚ) := by
    rw [ndThr, one_div_one_div]
    push_cast
    ring
  rw [heq, encode_rat_natCast, show 2 * (2 * j ^ 3) = 4 * j ^ 3 from by ring]

/-- Poly-fueled cube `(j' + 1)³` from a poly-fueled extractor. -/
lemma cube_succ_polyFueled {cj : Nat.Partrec.Code} {j'f : ℕ → ℕ}
    (hj : PolyFueled cj j'f) : ∃ c, PolyFueled c (fun m => (j'f m + 1) ^ 3) := by
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  have hj1 := hj.succ_comp
  have hsq := (hmul.comp (hj1.pair hj1)).of_eq
    (f' := fun m => (j'f m + 1) * (j'f m + 1))
    (fun m => by simp only [Nat.unpair_pair])
  exact ⟨_, (hmul.comp (hsq.pair hj1)).of_eq (fun m => by
    simp only [Nat.unpair_pair]
    ring)⟩

/-- Poly-fueled emission of the padded threshold-sum token
`⌜ndThr (j'+1) + ndPadThr (j'+1) i⌝` (pad below the rung's start day, live after). -/
lemma encode_thrSum_polyFueled {cj ci : Nat.Partrec.Code} {j'f if_ : ℕ → ℕ}
    (hj : PolyFueled cj j'f) (hi : PolyFueled ci if_) :
    ∃ c, PolyFueled c (fun m =>
      Encodable.encode (ndThr (j'f m + 1) + ndPadThr (j'f m + 1) (if_ m))) := by
  obtain ⟨c3, h3⟩ := cube_succ_polyFueled hj
  obtain ⟨cad, had⟩ := addc_polyFueled
  have h2cube := (had.comp (h3.pair h3)).of_eq
    (f' := fun m => 2 * (j'f m + 1) ^ 3)
    (fun m => by simp only [Nat.unpair_pair]; ring)
  have padv := (PolyFueled.const 2).pair h2cube
  have livev := (PolyFueled.const 2).pair h3
  have test := subc_polyFueled.comp (hi.pair hj)
  refine ⟨_, (ifzSel_polyFueled.comp ((padv.pair livev).pair test)).of_eq (fun m => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rcases Nat.lt_or_ge (if_ m) (j'f m + 1) with hcase | hcase
  · rw [if_pos (by omega), ndPadThr, if_pos hcase, add_zero,
      encode_ndThr (by omega : 1 ≤ j'f m + 1)]
  · rw [if_neg (by omega), ndPadThr, if_neg (by omega),
      encode_ndThr_double (by omega : 1 ≤ j'f m + 1)]

/-- Poly-fueled emission of the padded slope token `⌜1 / ndPadThr (j'+1) i⌝`
(`⌜0⌝ = 1` in the pad region, `⌜2(j'+1)³⌝` live). -/
lemma encode_thrRecip_polyFueled {cj ci : Nat.Partrec.Code} {j'f if_ : ℕ → ℕ}
    (hj : PolyFueled cj j'f) (hi : PolyFueled ci if_) :
    ∃ c, PolyFueled c (fun m =>
      Encodable.encode (1 / ndPadThr (j'f m + 1) (if_ m))) := by
  obtain ⟨c3, h3⟩ := cube_succ_polyFueled hj
  obtain ⟨cad, had⟩ := addc_polyFueled
  have h2cube := (had.comp (h3.pair h3)).of_eq
    (f' := fun m => 2 * (j'f m + 1) ^ 3)
    (fun m => by simp only [Nat.unpair_pair]; ring)
  have h4cube := (had.comp (h2cube.pair h2cube)).of_eq
    (f' := fun m => 4 * (j'f m + 1) ^ 3)
    (fun m => by simp only [Nat.unpair_pair]; ring)
  have padv := PolyFueled.const 1
  have livev := h4cube.pair (PolyFueled.const 1)
  have test := subc_polyFueled.comp (hi.pair hj)
  refine ⟨_, (ifzSel_polyFueled.comp ((padv.pair livev).pair test)).of_eq (fun m => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rcases Nat.lt_or_ge (if_ m) (j'f m + 1) with hcase | hcase
  · rw [if_pos (by omega), ndPadThr, if_pos hcase, div_zero, encode_rat_zero]
  · rw [if_neg (by omega), ndPadThr, if_neg (by omega),
      encode_ndThr_recip (by omega : 1 ≤ j'f m + 1)]

/-- Poly-fueled emission of the rung-weight token `⌜((j'+1 : ℕ) : ℚ)⌝`. -/
lemma encode_ratCast_polyFueled {cj : Nat.Partrec.Code} {j'f : ℕ → ℕ}
    (hj : PolyFueled cj j'f) :
    ∃ c, PolyFueled c (fun m => Encodable.encode (((j'f m + 1 : ℕ) : ℚ))) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hj1 := hj.succ_comp
  have h2j := (had.comp (hj1.pair hj1)).of_eq
    (f' := fun m => 2 * (j'f m + 1))
    (fun m => by simp only [Nat.unpair_pair]; ring)
  exact ⟨_, (h2j.pair (PolyFueled.const 1)).of_eq
    (fun m => (encode_rat_natCast _).symm)⟩

/-- The rung-`j` day-`i` arm-chain serialization block. -/
def ndArmBlock (φ : Sentence) (j i : ℕ) : List ℕ :=
  (oneMinus (ndBuySig φ j i)).serialize ++ [3]

lemma ndArmBlock_tokenStream (φ : Sentence) :
    PolyTokenStream (fun x => ndArmBlock φ (x.unpair.1.unpair.2 + 1) x.unpair.2) := by
  have hbuy : PolyTokenStream (fun x =>
      (ndBuySig φ (x.unpair.1.unpair.2 + 1) x.unpair.2).serialize) :=
    buyIndEF_tokenStream_comp (jf := fun x => x.unpair.2)
      (af := fun x => ndThr (x.unpair.1.unpair.2 + 1))
      (δf := fun x => ndPadThr (x.unpair.1.unpair.2 + 1) x.unpair.2)
      PolyFueled.right φ
      (encode_thrSum_polyFueled (PolyFueled.right.comp PolyFueled.left) PolyFueled.right)
      (encode_thrRecip_polyFueled (PolyFueled.right.comp PolyFueled.left) PolyFueled.right)
  exact (PolyTokenStream.serialize_oneMinus hbuy).append (PolyTokenStream.const 3)

/-- Arm blocks have rung- and day-independent width (only token values vary). -/
lemma ndArmBlock_length (φ : Sentence) (j i : ℕ) :
    (ndArmBlock φ j i).length = (ndArmBlock φ 1 0).length := by
  simp [ndArmBlock, ndBuySig, buyIndEF, oneMinus, clip01, efMin, EF.serialize]

lemma serialize_ndBuySig_length (φ : Sentence) (j i : ℕ) :
    (ndBuySig φ j i).serialize.length = (ndBuySig φ 1 0).serialize.length := by
  simp [ndBuySig, buyIndEF, clip01, efMin, EF.serialize]

lemma serialize_armChain_ndBuy (φ : Sentence) (j : ℕ) : ∀ n,
    (armChain (ndBuySig φ j) n).serialize
      = [1, Encodable.encode ((1 : ℚ))]
        ++ (List.range n).flatMap (fun i => ndArmBlock φ j i)
  | 0 => by simp [armChain, EF.serialize]
  | (n + 1) => by
      rw [armChain]
      simp only [EF.serialize]
      rw [serialize_armChain_ndBuy φ j n, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, ndArmBlock]
      simp [List.append_assoc]

lemma serialize_ndCoef (φ : Sentence) (j n : ℕ) :
    (ndCoef φ j n).serialize
      = [1, Encodable.encode ((j : ℚ))]
        ++ (armChain (ndBuySig φ j) n).serialize
        ++ (ndBuySig φ j n).serialize ++ [3, 3] := by
  simp [ndCoef, EF.serialize, List.append_assoc]

lemma serialize_ndLadderEF (φ : Sentence) (n : ℕ) : ∀ m,
    (ndLadderEF φ n m).serialize
      = [1, Encodable.encode ((0 : ℚ))]
        ++ (List.range m).flatMap (fun j' => (ndCoef φ (j' + 1) n).serialize ++ [2])
  | 0 => by simp [ndLadderEF, EF.serialize]
  | (m + 1) => by
      rw [ndLadderEF]
      simp only [EF.serialize]
      rw [serialize_ndLadderEF φ n m, List.range_succ, List.flatMap_append,
        List.flatMap_singleton]
      simp [List.append_assoc]

/-- The rung chunk (coefficient serialization plus the ladder's `add` tag), as a
`PolySegStream` over the paired input `⟨n, j'⟩`. -/
lemma ndChunkSeg_polySegStream (φ : Sentence) :
    PolySegStream (fun m =>
      (ndCoef φ (m.unpair.2 + 1) m.unpair.1).serialize ++ [2]) := by
  have hW0 : 0 < (ndArmBlock φ 1 0).length := by
    norm_num [ndArmBlock, ndBuySig, buyIndEF, oneMinus, clip01, efMin, EF.serialize]
  have segA : PolySegStream (fun m =>
      (EF.const (((m.unpair.2 + 1 : ℕ) : ℚ))).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp
      (encode_ratCast_polyFueled PolyFueled.right))
  have segB : PolySegStream (fun _ : ℕ => [1, Encodable.encode ((1 : ℚ))]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have segC := PolySegStream.blocks (ndArmBlock_tokenStream φ)
    ((ndArmBlock φ 1 0).length) (fun x => ndArmBlock_length φ _ _) hW0 PolyFueled.left
  have segD : PolySegStream (fun m =>
      (ndBuySig φ (m.unpair.2 + 1) m.unpair.1).serialize) :=
    PolySegStream.ofTokenStream (buyIndEF_tokenStream_comp (jf := fun m => m.unpair.1)
      (af := fun m => ndThr (m.unpair.2 + 1))
      (δf := fun m => ndPadThr (m.unpair.2 + 1) m.unpair.1)
      PolyFueled.left φ
      (encode_thrSum_polyFueled PolyFueled.right PolyFueled.left)
      (encode_thrRecip_polyFueled PolyFueled.right PolyFueled.left))
  have segE : PolySegStream (fun _ : ℕ => [3, 3, 2]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 3).append
      ((PolyTokenStream.const 3).append (PolyTokenStream.const 2)))
  refine PolySegStream.of_eq
    ((((segA.append segB).append segC).append segD).append segE) (fun m => ?_)
  rw [serialize_ndCoef, serialize_armChain_ndBuy]
  simp [EF.serialize, Nat.unpair_pair, List.append_assoc]

/-- The scale-ladder trader is efficiently computable. The day-`n` stream is a head
`[1, ⌜0⌝]`, then `n` rung chunks of uniform runtime width via `PolySegStream.concat`
(each chunk: rung-constant head, `n` fixed-width arm blocks via `PolySegStream.blocks`,
the day-`n` signal, closers), then the trade tail. The rung-varying `ℚ`-constant tokens
are emitted as poly-fueled arithmetic through the closed encoding forms
(`encode_ndThr` etc.). -/
lemma ndLadderTrader_ecTok (φ : Sentence) :
    EfficientlyComputableTok (ndLadderTrader φ) := by
  have hunif : ∀ n j,
      ((ndCoef φ ((Nat.pair n j).unpair.2 + 1) (Nat.pair n j).unpair.1).serialize
          ++ [2]).length
        = ((ndCoef φ ((Nat.pair n 0).unpair.2 + 1) (Nat.pair n 0).unpair.1).serialize
          ++ [2]).length := by
    intro n j
    simp only [Nat.unpair_pair]
    rw [serialize_ndCoef, serialize_ndCoef, serialize_armChain_ndBuy,
      serialize_armChain_ndBuy]
    have hfm : ∀ j' : ℕ, ((List.range n).flatMap (fun i => ndArmBlock φ j' i)).length
        = n * (ndArmBlock φ 1 0).length := fun j' =>
      length_flatMap_const_width _ _ n (fun i _ => ndArmBlock_length φ _ _)
    have hsig := serialize_ndBuySig_length φ (j + 1) n
    have hsig0 := serialize_ndBuySig_length φ (0 + 1) n
    simp only [List.length_append, List.length_cons, List.length_nil, hfm]
    omega
  have segChunks := PolySegStream.concat (ndChunkSeg_polySegStream φ) PolyFueled.id hunif
  have seg1 : PolySegStream (fun _ : ℕ => [1, Encodable.encode ((0 : ℚ))]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have seg3 : PolySegStream (fun _ : ℕ => [6, Encodable.encode φ]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 6).append (PolyTokenStream.const _))
  refine ecTok_of_segStream _ (PolySegStream.of_eq ((seg1.append segChunks).append seg3) ?_)
  intro n
  show _ = serializeTrades ((ndLadderTrader φ).strat n).trades
  rw [show ((ndLadderTrader φ).strat n).trades = [(ndLadderEF φ n n, φ)] from rfl,
    serializeTrades, serializeTrades, serialize_ndLadderEF]
  simp [Nat.unpair_pair]

#print axioms ndLadderTrader_ecTok

/-- **Non-Dogmatism, positive direction** (`thm:nd`): under a logical inductor, if
`φ`-satisfying plausible worlds keep existing (the per-day semantic rendering of
`Θ ⊬ ¬φ`), the price is eventually bounded away from `0`. No price-range hypotheses are
needed: the ladder's economics localize to its trigger bands.
Paper node: `thm:nd` -/
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
  exact hLI.noExploitTok (ndLadderTrader φ) (ndLadderTrader_ecTok φ)
    (ndLadderTrader_exploits P DP φ hφ hfreq)

#print axioms lic_nonDogmatism

/-! ### The dual direction: `Θ ⊬ φ` ⇒ price bounded away from `1`

The mirrored **sell** ladder. This does *not* reduce to the positive direction applied to
`∼φ` — the prices of `φ` and `∼φ` are unlinked without coherence — so
rung `j` here *sells* up to `j³` shares when the price spikes above `1 − 1/j³`, with the
same arming chain over `sellIndEF` signals. Selling banks the price now against a payout
`≤ 1` later: in every world the rung's downside is `≤ 1/j²` (the spike band), and in the
plausible `¬φ`-worlds that `Θ ⊬ φ` keeps supplying (payout `0`) a fired rung banks
`j·(1 − 1/j³) ≥ j − 1`. -/

/-- Rung-`j` day-`i` sell trigger: `ctsind(Pᵢφ > 1 − 1/j³)` once live (`i ≥ j`),
identically `0` before (the same `δ = 0` padding). -/
def ndSellSig (φ : Sentence) (j i : ℕ) : EF :=
  sellIndEF φ (1 - ndThr j) (ndPadThr j i) i

lemma ndSellSig_live (φ : Sentence) {j i : ℕ} (h : j ≤ i) :
    ndSellSig φ j i = sellIndEF φ (1 - ndThr j) (ndThr j) i := by
  rw [ndSellSig, ndPadThr, if_neg (by omega)]

lemma ndSellSig_denote_pad (φ : Sentence) (P : History) {j i : ℕ} (h : i < j) :
    (ndSellSig φ j i).denote P = 0 := by
  rw [ndSellSig, ndPadThr, if_pos h, sellIndEF_denote]
  norm_num

lemma ndSellSig_mem (φ : Sentence) (P : History) (j i : ℕ) :
    0 ≤ (ndSellSig φ j i).denote P ∧ (ndSellSig φ j i).denote P ≤ 1 :=
  sellInd_mem φ _ _ i P

lemma ndSellSig_pos_imp (φ : Sentence) (P : History) {j i : ℕ} (hj : 1 ≤ j)
    (h : 0 < (ndSellSig φ j i).denote P) : 1 - 1 / (j : ℝ) ^ 3 < P i φ := by
  rcases lt_or_ge i j with hij | hij
  · rw [ndSellSig_denote_pad φ P hij] at h
    exact absurd h (lt_irrefl 0)
  · rw [ndSellSig_live φ hij] at h
    have hlt := sellInd_pos_imp (ndThr_pos hj) h
    have hd := ndThr_double hj
    push_cast at hlt
    linarith

lemma ndSellSig_eq_one (φ : Sentence) (P : History) {j i : ℕ} (hj : 1 ≤ j)
    (hlive : j ≤ i) (h : 1 - ((ndThr j : ℚ) : ℝ) < P i φ) :
    (ndSellSig φ j i).denote P = 1 := by
  rw [ndSellSig_live φ hlive]
  apply sellInd_eq_one (ndThr_pos hj)
  push_cast
  linarith

lemma ndSellSig_rank (φ : Sentence) (j i : ℕ) : (ndSellSig φ j i).rank = i :=
  sellIndEF_rank φ _ _ i

/-- Day-`n` shares sold by rung `j` (per unit of the coefficient constant `j`). -/
noncomputable def ndSellShares (φ : Sentence) (P : History) (j n : ℕ) : ℝ :=
  (armChain (ndSellSig φ j) n).denote P * (ndSellSig φ j n).denote P

lemma ndSellShares_nonneg (φ : Sentence) (P : History) (j n : ℕ) :
    0 ≤ ndSellShares φ P j n :=
  mul_nonneg (armChain_mem _ P (fun i => ndSellSig_mem φ P j i) n).1
    (ndSellSig_mem φ P j n).1

lemma ndSellShares_pos_sig {φ : Sentence} {P : History} {j n : ℕ}
    (h : 0 < ndSellShares φ P j n) : 0 < (ndSellSig φ j n).denote P := by
  rcases (ndSellSig_mem φ P j n).1.lt_or_eq with hs | hs
  · exact hs
  · rw [ndSellShares, ← hs, mul_zero] at h
    exact absurd h (lt_irrefl 0)

lemma ndSellShares_sum (φ : Sentence) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, ndSellShares φ P j n
      = 1 - (armChain (ndSellSig φ j) N).denote P := by
  simp only [ndSellShares]
  rw [armChain_shares_sum (ndSellSig φ j) P h,
    armChain_denote_of_le (ndSellSig φ j) P
      (fun i hi => ndSellSig_denote_pad φ P hi) j le_rfl]

lemma ndSellShares_sum_le_one (φ : Sentence) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, ndSellShares φ P j n ≤ 1 := by
  rw [ndSellShares_sum φ P h]
  have := (armChain_mem (ndSellSig φ j) P (fun i => ndSellSig_mem φ P j i) N).1
  linarith

/-- Rung-`j` day-`n` sell coefficient: `−j · armChain · trigger`. -/
def ndSellCoef (φ : Sentence) (j n : ℕ) : EF :=
  .mul (.const (-(j : ℚ))) (.mul (armChain (ndSellSig φ j) n) (ndSellSig φ j n))

lemma ndSellCoef_denote (φ : Sentence) (P : History) (j n : ℕ) :
    (ndSellCoef φ j n).denote P = -((j : ℝ) * ndSellShares φ P j n) := by
  simp only [ndSellCoef, EF.denote_mul, EF.denote_const, Pi.mul_apply, ndSellShares]
  push_cast
  ring

lemma ndSellCoef_rank (φ : Sentence) (j n : ℕ) : (ndSellCoef φ j n).rank ≤ n := by
  have h1 := armChain_rank (ndSellSig φ j) (fun i => (ndSellSig_rank φ j i).le) n
  have h2 := (ndSellSig_rank φ j n).le
  simp only [ndSellCoef, EF.rank, max_le_iff]
  omega

/-- The day-`n` sell ladder: `Σ_{j=1}^{m} ndSellCoef j n`. -/
def ndSellLadderEF (φ : Sentence) (n : ℕ) : ℕ → EF
  | 0 => .const 0
  | (m + 1) => .add (ndSellLadderEF φ n m) (ndSellCoef φ (m + 1) n)

lemma ndSellLadderEF_denote (φ : Sentence) (P : History) (n : ℕ) : ∀ m,
    (ndSellLadderEF φ n m).denote P
      = ∑ k ∈ Finset.range m, -(((k + 1 : ℕ) : ℝ) * ndSellShares φ P (k + 1) n)
  | 0 => by simp [ndSellLadderEF]
  | (m + 1) => by
      rw [ndSellLadderEF]
      simp only [EF.denote_add, Pi.add_apply]
      rw [ndSellLadderEF_denote φ P n m, Finset.sum_range_succ, ndSellCoef_denote]

lemma ndSellLadderEF_rank (φ : Sentence) (n : ℕ) : ∀ m,
    (ndSellLadderEF φ n m).rank ≤ n
  | 0 => by simp [ndSellLadderEF]
  | (m + 1) => by
      have h1 := ndSellLadderEF_rank φ n m
      have h2 := ndSellCoef_rank φ (m + 1) n
      simp only [ndSellLadderEF, EF.rank, max_le_iff]
      omega

/-- The **sell-ladder non-dogmatism trader** (`thm:nd`, dual direction): on day `n`,
rung `j ≤ n` sells `j · armChainⱼ · ctsind(Pₙφ > 1 − 1/j³)` shares of `φ`. -/
def ndSellLadderTrader (φ : Sentence) : Trader where
  strat n := { trades := [(ndSellLadderEF φ n n, φ)]
               rank_le := by
                 intro p hp
                 simp only [List.mem_singleton] at hp
                 subst hp
                 exact ndSellLadderEF_rank φ n n }

@[simp] theorem ndSellLadderTrader_value (φ : Sentence) (V : History) (w : Sentence → ℝ)
    (n : ℕ) : ((ndSellLadderTrader φ).strat n).value V w
      = (ndSellLadderEF φ n n).denote V * (w φ - V n φ) := by
  simp [ndSellLadderTrader, Strategy.value]

/-- Net worth with the sign folded in: each term is `j · shares · (price − payout)`. -/
lemma ndSellLadderTrader_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (ndSellLadderTrader φ).netWorth V v m
      = ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range n,
          ((k + 1 : ℕ) : ℝ) * ndSellShares φ V (k + 1) n * (V n φ - v.payout φ) := by
  simp only [Trader.netWorth, ndSellLadderTrader_value, ndSellLadderEF_denote,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun k _ => by ring))

/-- In **any** world, the rung-`j` day-`n` sell term loses at most `shares/j²`
(sales happen only above the price `1 − 1/j³`, and the payout is at most `1`). -/
lemma ndSellTerm_ge (φ : Sentence) (P : History) (v : PCWorld) {j : ℕ} (hj : 1 ≤ j)
    (n : ℕ) : -(ndSellShares φ P j n * (1 / (j : ℝ) ^ 2))
      ≤ (j : ℝ) * ndSellShares φ P j n * (P n φ - v.payout φ) := by
  have hb := ndSellShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hP := ndSellSig_pos_imp φ P hj (ndSellShares_pos_sig hb')
    have hpay : v.payout φ ≤ 1 := by rw [PCWorld.payout]; split <;> norm_num
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hjb : 0 < (j : ℝ) * ndSellShares φ P j n := mul_pos (by linarith) hb'
    have hge : -(1 / (j : ℝ) ^ 3) ≤ P n φ - v.payout φ := by linarith
    calc -(ndSellShares φ P j n * (1 / (j : ℝ) ^ 2))
        = (j : ℝ) * ndSellShares φ P j n * (-(1 / (j : ℝ) ^ 3)) := by
          rw [← ndWeight_mul hj]; ring
      _ ≤ (j : ℝ) * ndSellShares φ P j n * (P n φ - v.payout φ) :=
          mul_le_mul_of_nonneg_left hge hjb.le
  · rw [← hb']
    norm_num

/-- In a `¬φ`-world every rung's sell term is a gain: sales happen above
`1 − 1/j³ ≥ 0` and the payout is `0`. -/
lemma ndSellTerm_nonneg (φ : Sentence) (P : History) (v : PCWorld) (hv : ¬ v.Holds φ)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    0 ≤ (j : ℝ) * ndSellShares φ P j n * (P n φ - v.payout φ) := by
  have hb := ndSellShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hP := ndSellSig_pos_imp φ P hj (ndSellShares_pos_sig hb')
    have hpay : v.payout φ = 0 := by rw [PCWorld.payout, if_neg hv]
    have hle := ndCube_le_one hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [hpay]
    exact mul_nonneg (mul_nonneg (by linarith) hb'.le) (by linarith)
  · rw [← hb']
    norm_num

/-- In a `¬φ`-world the rung-`j` sell term banks at least `j·shares·(1 − 1/j³)`. -/
lemma ndSellTerm_profit (φ : Sentence) (P : History) (v : PCWorld) (hv : ¬ v.Holds φ)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    (j : ℝ) * ndSellShares φ P j n * (1 - 1 / (j : ℝ) ^ 3)
      ≤ (j : ℝ) * ndSellShares φ P j n * (P n φ - v.payout φ) := by
  have hpay : v.payout φ = 0 := by rw [PCWorld.payout, if_neg hv]
  rw [hpay]
  have hb := ndSellShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hP := ndSellSig_pos_imp φ P hj (ndSellShares_pos_sig hb')
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (by linarith) hb'.le)
  · rw [← hb']
    norm_num

/-- **The dual exploitation** (`thm:nd`): if the price frequently spikes above every
`1 − ε`, the sell ladder exploits — every rung eventually fires, banking `≥ j − 1` in
the plausible `¬φ`-worlds, while the downside stays `≤ 2` in every world. -/
theorem ndSellLadderTrader_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ)
    (hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, 1 - ε < P n φ) :
    (ndSellLadderTrader φ).Exploits P DP := by
  refine exploits_of_bddBelow_of_unbounded _ _ _ 2 ?_ ?_
  · rintro x ⟨m, v, hv, rfl⟩
    rw [ndSellLadderTrader_netWorth, sum_range_triangle_comm]
    have hk : ∀ k ∈ Finset.range (m + 1),
        -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)
          ≤ ∑ n ∈ Finset.Ico (k + 1) (m + 1),
              ((k + 1 : ℕ) : ℝ) * ndSellShares φ P (k + 1) n * (P n φ - v.payout φ) := by
      intro k hkm
      have hj : 1 ≤ k + 1 := by omega
      have hsum := ndSellShares_sum_le_one φ P
        (j := k + 1) (N := m + 1) (by simp only [Finset.mem_range] at hkm; omega)
      have hw2 : (0 : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
      calc -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2)
          ≤ -((∑ n ∈ Finset.Ico (k + 1) (m + 1), ndSellShares φ P (k + 1) n)
              * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
            have h1 := mul_le_mul_of_nonneg_right hsum hw2
            rw [one_mul] at h1
            linarith
        _ = ∑ n ∈ Finset.Ico (k + 1) (m + 1),
              -(ndSellShares φ P (k + 1) n * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
            rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
        _ ≤ _ := Finset.sum_le_sum (fun n _ => ndSellTerm_ge φ P v hj n)
    calc (-2 : ℝ)
        ≤ -∑ k ∈ Finset.range (m + 1), (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
          have := sum_inv_sq_le_two (m + 1)
          linarith
      _ = ∑ k ∈ Finset.range (m + 1), -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
          rw [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum hk
  · intro B
    obtain ⟨j', hj'⟩ := exists_nat_gt B
    have hj : 1 ≤ j' + 1 := by omega
    have hθ := ndThr_pos (j := j' + 1) hj
    obtain ⟨n₀, hn₀, hspike⟩ := (Filter.frequently_atTop.mp (hfreq _ hθ)) (j' + 1)
    obtain ⟨v, hv, hvφ⟩ := hφ n₀
    refine ⟨(ndSellLadderTrader φ).netWorth P v n₀, ⟨n₀, v, hv, rfl⟩, ?_⟩
    rw [ndSellLadderTrader_netWorth, sum_range_triangle_comm]
    have hterm : ∀ k ∈ Finset.range (n₀ + 1),
        0 ≤ ∑ n ∈ Finset.Ico (k + 1) (n₀ + 1),
            ((k + 1 : ℕ) : ℝ) * ndSellShares φ P (k + 1) n * (P n φ - v.payout φ) :=
      fun k _ => Finset.sum_nonneg (fun n _ => ndSellTerm_nonneg φ P v hvφ (by omega) n)
    have hjmem : j' ∈ Finset.range (n₀ + 1) := Finset.mem_range.mpr (by omega)
    have harm0 : (armChain (ndSellSig φ (j' + 1)) (n₀ + 1)).denote P = 0 := by
      rw [armChain_denote_succ, ndSellSig_eq_one φ P hj hn₀ hspike]
      ring
    have hsum1 : ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1), ndSellShares φ P (j' + 1) n = 1 := by
      rw [ndSellShares_sum φ P (by omega), harm0, sub_zero]
    have hj1 : (1 : ℝ) ≤ ((j' + 1 : ℕ) : ℝ) := by exact_mod_cast hj
    have hslice : ((j' + 1 : ℕ) : ℝ) - 1
        ≤ ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
            ((j' + 1 : ℕ) : ℝ) * ndSellShares φ P (j' + 1) n * (P n φ - v.payout φ) := by
      have hw := ndWeight_mul (j := j' + 1) hj
      have hsq : 1 / ((j' + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (by nlinarith)]
        nlinarith
      calc ((j' + 1 : ℕ) : ℝ) - 1
          ≤ ((j' + 1 : ℕ) : ℝ) * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3) := by nlinarith
        _ = ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
              ((j' + 1 : ℕ) : ℝ) * ndSellShares φ P (j' + 1) n
                * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3) := by
            have hfac : ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
                  ((j' + 1 : ℕ) : ℝ) * ndSellShares φ P (j' + 1) n
                    * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3)
                = (((j' + 1 : ℕ) : ℝ) * (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3))
                    * ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1), ndSellShares φ P (j' + 1) n := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n _ => by ring)
            rw [hfac, hsum1, mul_one]
        _ ≤ _ := Finset.sum_le_sum (fun n _ => ndSellTerm_profit φ P v hvφ hj n)
    have hB : B < ((j' + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
    have hsingle := Finset.single_le_sum hterm hjmem
    linarith

#print axioms ndSellLadderTrader_exploits

/-! ### Sell-ladder emission — negative-numerator constant tokens

The sell chunks mirror the buy chunks, but the band constants `δ − b` (with
`b = 1 − ndThr j` near `1`) have **negative numerators**: their encodes route through
`Int.negSucc` (`⌜−(a/b)⌝ = pair (2(a−1)+1) b` for a normalized positive fraction
`a/b`), with an extra rung-1 branch where the live constant collapses to `0`. -/

theorem encode_int_neg_natCast {n : ℕ} (hn : 0 < n) :
    Encodable.encode ((-(n : ℤ))) = 2 * n - 1 := by
  have h : -((n : ℤ)) = Int.negSucc (n - 1) := by omega
  rw [h, show Encodable.encode (Int.negSucc (n - 1)) = 2 * (n - 1) + 1 from rfl]
  omega

lemma encode_rat_neg_natCast {n : ℕ} (hn : 0 < n) :
    Encodable.encode (-((n : ℚ))) = Nat.pair (2 * n - 1) 1 := by
  rw [encode_rat_eq, Rat.neg_num, Rat.neg_den, Rat.num_natCast, Rat.den_natCast,
    encode_int_neg_natCast hn]

/-- Encoding a normalized negative fraction: `⌜−(a/b)⌝ = pair (2(a−1)+1) b`. -/
lemma encode_rat_neg_div {a b : ℕ} (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b) :
    Encodable.encode (-((a : ℚ) / (b : ℚ))) = Nat.pair (2 * (a - 1) + 1) b := by
  have hb : b ≠ 0 := by omega
  have hnat : (Int.negSucc (a - 1)).natAbs = a := by
    rw [Int.natAbs_negSucc]
    omega
  have hcop' : (Int.negSucc (a - 1)).natAbs.Coprime b := by rwa [hnat]
  have heq : -((a : ℚ) / (b : ℚ)) = Rat.mk' (Int.negSucc (a - 1)) b hb hcop' := by
    rw [Rat.mk_eq_divInt, Rat.divInt_eq_div]
    have hcast : ((Int.negSucc (a - 1) : ℤ) : ℚ) = -(a : ℚ) := by
      have h1 : Int.negSucc (a - 1) = -(a : ℤ) := by omega
      rw [h1]
      push_cast
      ring
    rw [hcast]
    push_cast
    ring
  rw [heq, encode_rat_eq]
  rfl

lemma encode_sellB_pad {j : ℕ} (hj : 1 ≤ j) :
    Encodable.encode ((0 : ℚ) - (1 - ndThr j))
      = Nat.pair (2 * (2 * j ^ 3 - 1 - 1) + 1) (2 * j ^ 3) := by
  have h3 : 0 < j ^ 3 := pow_pos (by omega) 3
  have heq : (0 : ℚ) - (1 - ndThr j)
      = -(((2 * j ^ 3 - 1 : ℕ) : ℚ) / ((2 * j ^ 3 : ℕ) : ℚ)) := by
    rw [ndThr]
    have hcast : ((2 * j ^ 3 - 1 : ℕ) : ℚ) = 2 * (j : ℚ) ^ 3 - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * j ^ 3)]
      ring
    rw [hcast]
    push_cast
    have hx : (2 : ℚ) * (j : ℚ) ^ 3 ≠ 0 :=
      mul_ne_zero two_ne_zero (pow_ne_zero 3 (Nat.cast_ne_zero.mpr (by omega)))
    field_simp
    ring
  have hcop : (2 * j ^ 3 - 1).Coprime (2 * j ^ 3) := by
    have h : 2 * j ^ 3 = (2 * j ^ 3 - 1) + 1 := by omega
    rw [h]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rw [heq, encode_rat_neg_div (by omega) (by omega) hcop]

lemma encode_sellB_live {j : ℕ} (hj : 2 ≤ j) :
    Encodable.encode (ndThr j - (1 - ndThr j))
      = Nat.pair (2 * (j ^ 3 - 1 - 1) + 1) (j ^ 3) := by
  have h8 : 8 ≤ j ^ 3 := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ j ^ 3 := Nat.pow_le_pow_left hj 3
  have heq : ndThr j - (1 - ndThr j)
      = -(((j ^ 3 - 1 : ℕ) : ℚ) / ((j ^ 3 : ℕ) : ℚ)) := by
    rw [ndThr]
    have hcast : ((j ^ 3 - 1 : ℕ) : ℚ) = (j : ℚ) ^ 3 - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ j ^ 3)]
      ring
    rw [hcast]
    push_cast
    have hx : ((j : ℚ)) ^ 3 ≠ 0 := pow_ne_zero 3 (Nat.cast_ne_zero.mpr (by omega))
    field_simp
    ring
  have hcop : (j ^ 3 - 1).Coprime (j ^ 3) := by
    have h : j ^ 3 = (j ^ 3 - 1) + 1 := by omega
    rw [h]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rw [heq, encode_rat_neg_div (by omega) (by omega) hcop]

lemma encode_sellB_live_one : Encodable.encode (ndThr 1 - (1 - ndThr 1)) = 1 := by
  have h : ndThr 1 - (1 - ndThr 1) = 0 := by norm_num [ndThr]
  rw [h, encode_rat_zero]

/-- Poly-fueled emission of the padded sell-band token
`⌜ndPadThr (j'+1) i − (1 − ndThr (j'+1))⌝` (pad / rung-1 live / general live). -/
lemma encode_sellB_polyFueled {cj ci : Nat.Partrec.Code} {j'f if_ : ℕ → ℕ}
    (hj : PolyFueled cj j'f) (hi : PolyFueled ci if_) :
    ∃ c, PolyFueled c (fun m =>
      Encodable.encode (ndPadThr (j'f m + 1) (if_ m) - (1 - ndThr (j'f m + 1)))) := by
  obtain ⟨c3, h3⟩ := cube_succ_polyFueled hj
  obtain ⟨cad, had⟩ := addc_polyFueled
  have h2cube := (had.comp (h3.pair h3)).of_eq
    (f' := fun m => 2 * (j'f m + 1) ^ 3)
    (fun m => by simp only [Nat.unpair_pair]; ring)
  have h4cube := (had.comp (h2cube.pair h2cube)).of_eq
    (f' := fun m => 4 * (j'f m + 1) ^ 3)
    (fun m => by simp only [Nat.unpair_pair]; ring)
  have hpadnum := (subc_polyFueled.comp (h4cube.pair (PolyFueled.const 3))).of_eq
    (f' := fun m => 2 * (2 * (j'f m + 1) ^ 3 - 1 - 1) + 1)
    (fun m => by
      simp only [Nat.unpair_pair]
      have := pow_pos (show 0 < j'f m + 1 by omega) 3
      omega)
  have hpadv := hpadnum.pair h2cube
  have hsub2 := (subc_polyFueled.comp (h3.pair (PolyFueled.const 2))).of_eq
    (f' := fun m => (j'f m + 1) ^ 3 - 2)
    (fun m => by simp only [Nat.unpair_pair])
  have hlivenum := ((had.comp (hsub2.pair hsub2)).succ_comp).of_eq
    (f' := fun m => 2 * ((j'f m + 1) ^ 3 - 1 - 1) + 1)
    (fun m => by simp only [Nat.unpair_pair]; omega)
  have hlivev := hlivenum.pair h3
  have hinner := ifzSel_polyFueled.comp (((PolyFueled.const 1).pair hlivev).pair hj)
  have houter := ifzSel_polyFueled.comp
    ((hpadv.pair hinner).pair (subc_polyFueled.comp (hi.pair hj)))
  refine ⟨_, houter.of_eq (fun m => ?_)⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  rcases Nat.lt_or_ge (if_ m) (j'f m + 1) with hcase | hcase
  · rw [if_pos (by omega), ndPadThr, if_pos hcase,
      encode_sellB_pad (by omega : 1 ≤ j'f m + 1)]
  · rcases Nat.eq_zero_or_pos (j'f m) with h0 | h0
    · rw [if_neg (by omega), if_pos h0, ndPadThr, if_neg (by omega), h0]
      exact (encode_sellB_live_one).symm
    · rw [if_neg (by omega), if_neg (by omega), ndPadThr, if_neg (by omega),
        encode_sellB_live (by omega : 2 ≤ j'f m + 1)]

/-- Poly-fueled emission of the sell rung-weight token `⌜−((j'+1 : ℕ) : ℚ)⌝`. -/
lemma encode_neg_ratCast_polyFueled {cj : Nat.Partrec.Code} {j'f : ℕ → ℕ}
    (hj : PolyFueled cj j'f) :
    ∃ c, PolyFueled c (fun m => Encodable.encode (-((j'f m + 1 : ℕ) : ℚ))) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have h2j1 := ((had.comp (hj.pair hj)).succ_comp).of_eq
    (f' := fun m => 2 * (j'f m + 1) - 1)
    (fun m => by simp only [Nat.unpair_pair]; omega)
  exact ⟨_, (h2j1.pair (PolyFueled.const 1)).of_eq
    (fun m => (encode_rat_neg_natCast (Nat.succ_pos _)).symm)⟩

/-- The sell-rung day-`i` arm-chain serialization block. -/
def ndSellArmBlock (φ : Sentence) (j i : ℕ) : List ℕ :=
  (oneMinus (ndSellSig φ j i)).serialize ++ [3]

lemma ndSellArmBlock_tokenStream (φ : Sentence) :
    PolyTokenStream (fun x => ndSellArmBlock φ (x.unpair.1.unpair.2 + 1) x.unpair.2) := by
  have hsell : PolyTokenStream (fun x =>
      (ndSellSig φ (x.unpair.1.unpair.2 + 1) x.unpair.2).serialize) :=
    sellIndEF_tokenStream_comp (jf := fun x => x.unpair.2)
      (bf := fun x => 1 - ndThr (x.unpair.1.unpair.2 + 1))
      (δf := fun x => ndPadThr (x.unpair.1.unpair.2 + 1) x.unpair.2)
      PolyFueled.right φ
      (encode_sellB_polyFueled (PolyFueled.right.comp PolyFueled.left) PolyFueled.right)
      (encode_thrRecip_polyFueled (PolyFueled.right.comp PolyFueled.left) PolyFueled.right)
  exact (PolyTokenStream.serialize_oneMinus hsell).append (PolyTokenStream.const 3)

lemma ndSellArmBlock_length (φ : Sentence) (j i : ℕ) :
    (ndSellArmBlock φ j i).length = (ndSellArmBlock φ 1 0).length := by
  simp [ndSellArmBlock, ndSellSig, sellIndEF, oneMinus, clip01, efMin, EF.serialize]

lemma serialize_ndSellSig_length (φ : Sentence) (j i : ℕ) :
    (ndSellSig φ j i).serialize.length = (ndSellSig φ 1 0).serialize.length := by
  simp [ndSellSig, sellIndEF, clip01, efMin, EF.serialize]

lemma serialize_armChain_ndSell (φ : Sentence) (j : ℕ) : ∀ n,
    (armChain (ndSellSig φ j) n).serialize
      = [1, Encodable.encode ((1 : ℚ))]
        ++ (List.range n).flatMap (fun i => ndSellArmBlock φ j i)
  | 0 => by simp [armChain, EF.serialize]
  | (n + 1) => by
      rw [armChain]
      simp only [EF.serialize]
      rw [serialize_armChain_ndSell φ j n, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, ndSellArmBlock]
      simp [List.append_assoc]

lemma serialize_ndSellCoef (φ : Sentence) (j n : ℕ) :
    (ndSellCoef φ j n).serialize
      = [1, Encodable.encode (-((j : ℚ)))]
        ++ (armChain (ndSellSig φ j) n).serialize
        ++ (ndSellSig φ j n).serialize ++ [3, 3] := by
  simp [ndSellCoef, EF.serialize, List.append_assoc]

lemma serialize_ndSellLadderEF (φ : Sentence) (n : ℕ) : ∀ m,
    (ndSellLadderEF φ n m).serialize
      = [1, Encodable.encode ((0 : ℚ))]
        ++ (List.range m).flatMap (fun j' => (ndSellCoef φ (j' + 1) n).serialize ++ [2])
  | 0 => by simp [ndSellLadderEF, EF.serialize]
  | (m + 1) => by
      rw [ndSellLadderEF]
      simp only [EF.serialize]
      rw [serialize_ndSellLadderEF φ n m, List.range_succ, List.flatMap_append,
        List.flatMap_singleton]
      simp [List.append_assoc]

/-- The sell-rung chunk as a `PolySegStream` over the paired input `⟨n, j'⟩`. -/
lemma ndSellChunkSeg_polySegStream (φ : Sentence) :
    PolySegStream (fun m =>
      (ndSellCoef φ (m.unpair.2 + 1) m.unpair.1).serialize ++ [2]) := by
  have hW0 : 0 < (ndSellArmBlock φ 1 0).length := by
    norm_num [ndSellArmBlock, ndSellSig, sellIndEF, oneMinus, clip01, efMin, EF.serialize]
  have segA : PolySegStream (fun m =>
      (EF.const (-((m.unpair.2 + 1 : ℕ) : ℚ))).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp
      (encode_neg_ratCast_polyFueled PolyFueled.right))
  have segB : PolySegStream (fun _ : ℕ => [1, Encodable.encode ((1 : ℚ))]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have segC := PolySegStream.blocks (ndSellArmBlock_tokenStream φ)
    ((ndSellArmBlock φ 1 0).length) (fun x => ndSellArmBlock_length φ _ _) hW0
    PolyFueled.left
  have segD : PolySegStream (fun m =>
      (ndSellSig φ (m.unpair.2 + 1) m.unpair.1).serialize) :=
    PolySegStream.ofTokenStream (sellIndEF_tokenStream_comp (jf := fun m => m.unpair.1)
      (bf := fun m => 1 - ndThr (m.unpair.2 + 1))
      (δf := fun m => ndPadThr (m.unpair.2 + 1) m.unpair.1)
      PolyFueled.left φ
      (encode_sellB_polyFueled PolyFueled.right PolyFueled.left)
      (encode_thrRecip_polyFueled PolyFueled.right PolyFueled.left))
  have segE : PolySegStream (fun _ : ℕ => [3, 3, 2]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 3).append
      ((PolyTokenStream.const 3).append (PolyTokenStream.const 2)))
  refine PolySegStream.of_eq
    ((((segA.append segB).append segC).append segD).append segE) (fun m => ?_)
  rw [serialize_ndSellCoef, serialize_armChain_ndSell]
  simp [EF.serialize, Nat.unpair_pair, List.append_assoc]

/-- The sell ladder is efficiently computable: the mirror of `ndLadderTrader_ecTok`, with
the negative-numerator band constants emitted through `encode_sellB_polyFueled`. -/
lemma ndSellLadderTrader_ecTok (φ : Sentence) :
    EfficientlyComputableTok (ndSellLadderTrader φ) := by
  have hunif : ∀ n j,
      ((ndSellCoef φ ((Nat.pair n j).unpair.2 + 1) (Nat.pair n j).unpair.1).serialize
          ++ [2]).length
        = ((ndSellCoef φ ((Nat.pair n 0).unpair.2 + 1) (Nat.pair n 0).unpair.1).serialize
          ++ [2]).length := by
    intro n j
    simp only [Nat.unpair_pair]
    rw [serialize_ndSellCoef, serialize_ndSellCoef, serialize_armChain_ndSell,
      serialize_armChain_ndSell]
    have hfm : ∀ j' : ℕ, ((List.range n).flatMap (fun i => ndSellArmBlock φ j' i)).length
        = n * (ndSellArmBlock φ 1 0).length := fun j' =>
      length_flatMap_const_width _ _ n (fun i _ => ndSellArmBlock_length φ _ _)
    have hsig := serialize_ndSellSig_length φ (j + 1) n
    have hsig0 := serialize_ndSellSig_length φ (0 + 1) n
    simp only [List.length_append, List.length_cons, List.length_nil, hfm]
    omega
  have segChunks := PolySegStream.concat (ndSellChunkSeg_polySegStream φ)
    PolyFueled.id hunif
  have seg1 : PolySegStream (fun _ : ℕ => [1, Encodable.encode ((0 : ℚ))]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have seg3 : PolySegStream (fun _ : ℕ => [6, Encodable.encode φ]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 6).append (PolyTokenStream.const _))
  refine ecTok_of_segStream _ (PolySegStream.of_eq ((seg1.append segChunks).append seg3) ?_)
  intro n
  show _ = serializeTrades ((ndSellLadderTrader φ).strat n).trades
  rw [show ((ndSellLadderTrader φ).strat n).trades = [(ndSellLadderEF φ n n, φ)] from rfl,
    serializeTrades, serializeTrades, serialize_ndSellLadderEF]
  simp [Nat.unpair_pair]

#print axioms ndSellLadderTrader_ecTok

/-- **Non-Dogmatism, dual direction** (`thm:nd`): under a logical inductor, if
`φ`-falsifying plausible worlds keep existing (the per-day semantic rendering of
`Θ ⊬ φ`), the price is eventually bounded away from `1`.
Paper node: `thm:nd` -/
theorem lic_nonDogmatism_dual (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, P n φ ≤ 1 - ε := by
  by_contra h
  have hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, 1 - ε < P n φ := by
    intro ε hε
    by_contra h'
    rw [Filter.not_frequently] at h'
    exact h ⟨ε, hε, h'.mono (fun n hn => le_of_not_gt hn)⟩
  exact hLI.noExploitTok (ndSellLadderTrader φ) (ndSellLadderTrader_ecTok φ)
    (ndSellLadderTrader_exploits P DP φ hφ hfreq)

#print axioms lic_nonDogmatism_dual

/-! ### Limit-form corollaries (`P∞`) -/

/-- `thm:nd`, limit form, positive direction: `P∞(φ) > 0`. Convergence of the price is an
explicit hypothesis rather than an appeal to `thm:con`, so the statement is usable at any
convergent limit the caller already has (`lic_price_convergesTo` supplies one).
Paper node: `thm:nd` -/
theorem lic_limit_pos (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) {L : ℝ}
    (hL : ConvergesTo (fun n => P n φ) L)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) :
    0 < L := by
  obtain ⟨ε, hε, hev⟩ := lic_nonDogmatism P DP φ hφ
  have := ge_of_tendsto hL hev
  linarith

/-- `thm:nd`, limit form, dual direction: with the price convergent, `P∞(φ) < 1`.
Paper node: `thm:nd` -/
theorem lic_limit_lt_one (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) {L : ℝ}
    (hL : ConvergesTo (fun n => P n φ) L)
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) :
    L < 1 := by
  obtain ⟨ε, hε, hev⟩ := lic_nonDogmatism_dual P DP φ hφ
  have hle : L ≤ 1 - ε := le_of_tendsto hL hev
  linarith

#print axioms lic_limit_pos
#print axioms lic_limit_lt_one

end LogicalInduction
