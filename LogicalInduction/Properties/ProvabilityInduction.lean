import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Framework.Emission.WriteOut
import LogicalInduction.Framework.Efficiency

/-!
# Provability Induction — §4.2

The fixed-sentence fragment of `thm:provind` (`app:provind`, `sec:provind`).

The carrier of `thm:provind` is `lic_provind` (`AffineCoherence.lean`), which assumes what
the paper assumes — that each sentence is a *theorem*, i.e. holds in every world consistent
with the completed deductive process. This module holds forms with a strictly stronger
membership hypothesis, whose trader is constant and whose proofs are correspondingly
short; **none of them carries the node**, and none is a `theorem`.

## Objects

`buyDaily φ` buys one share of `φ` every day: its day-`n` strategy is the constant list
`[(1, φ)]`, of rank `0`, and it comes with its value, net-worth and efficient-computability
certificates. `buyDaily_ec` runs `Code.const` on the one fixed strategy code, which halts
within affine fuel and so fits the polynomial clock (`dd:fuel`).

## Endpoints

* `lic_deducible_price_near_one` — for a single `ε`, the price of an always-deducible `φ`
  rises above `1 − ε` at some day.
* `lic_deducible_eventually_ge` — the same bound, eventually rather than once.
* `lic_deducible_tendsto_one` — for a fixed always-deducible `φ`, `Pₙ(φ) → 1`.

The paper's second half — an efficiently computable sequence of *disprovable* sentences with
`Pₙ(ψₙ) → 0` — is carried by `lic_provind_false` (`AffineCoherence.lean`).

All exploitation routes through the engines of `Properties/Support/Exploitation.lean`; nothing here
re-derives the accumulation argument.
-/

namespace LogicalInduction

open Filter Topology

/-! ## The daily buy traders -/

/-- The trader that buys exactly one share of `φ` on every day. Each day-`n` strategy is
the single pair `(1, φ)`: a constant (hence continuous, hence legal) trade of rank 0. This
is the exploiting trader for the base case of Provability Induction. -/
def buyDaily (φ : Sentence) : Trader where
  strat _ := { trades := [(EF.const 1, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact Nat.zero_le _ }

@[simp] lemma buyDaily_value (φ : Sentence) (V : History) (w : Sentence → ℝ) (n : ℕ) :
    ((buyDaily φ).strat n).value V w = w φ - V n φ := by
  simp [buyDaily, Strategy.value]

lemma buyDaily_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (buyDaily φ).netWorth V v m = ∑ i ∈ Finset.range (m + 1), (v.payout φ - V i φ) := by
  simp [Trader.netWorth]

/-! ## Efficient computability -/

lemma buyDaily_ec (φ : Sentence) : EfficientlyComputableTok (buyDaily φ) := by
  refine ecTok_of_stream _ ?_
  have h : ∀ n, ((buyDaily φ).strat n).trades = [(EF.const 1, φ)] := fun _ => rfl
  simp only [h]
  exact PolyTokenStream.trades_cons (PolyTokenStream.serialize_const 1)
    (PolyFueled.const (Encodable.encode φ)) PolyTokenStream.trades_nil

/-! ## Provability induction for a fixed sentence -/

/-- If `φ` is always deducible and the market holds it uniformly `ε` below 1, the
do-buy-daily trader exploits: bounded below (net worth `≥ 0` in every plausible world,
since every world consistent with `Dₘ ∋ φ` values `φ` at 1) yet unbounded above (net worth
`≥ (m+1)·ε → ∞`). -/
lemma buyDaily_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hded : ∀ n, φ ∈ DP.D n) (hunder : ∀ n, P n φ ≤ 1 - ε)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyDaily φ).Exploits P DP := by
  refine exploits_of_nonneg_partialSums (buyDaily φ) P DP (fun i => 1 - P i φ) ε hε
    (fun i => by have := hunder i; linarith) (fun n v hv => ?_)
    (Filter.Frequently.of_forall (fun n => by have := hunder n; linarith)) hcons
  have hpay : v.payout φ = 1 := by rw [PCWorld.payout, if_pos (hv φ (hded n))]
  rw [buyDaily_netWorth, hpay]

/-- **Fixed-sentence fragment of Provability Induction**, stated against `def:lic`: a
logical inductor cannot hold an always-deducible sentence uniformly below price 1. For
every `ε > 0` the price rises above `1 − ε` at some day.

Carries **no** node: `hded : ∀ n, φ ∈ DP.D n` asks the sentence to lie in every finite
stage, which is strictly stronger than `thm:provind`'s "is a theorem" (holds in every world
consistent with the completed process), and the paper's statement is about a *sequence*.
The carrier is `lic_provind` (`AffineCoherence.lean`); this is the constant-trader fragment
whose short proof the module header describes. -/
lemma lic_deducible_price_near_one (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (ε : ℝ) (hε : 0 < ε)
    (hded : ∀ n, φ ∈ DP.D n) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ n, 1 - ε < P n φ := by
  by_contra h
  push Not at h
  exact hLI.noExploitTok (buyDaily φ) (buyDaily_ec φ) (buyDaily_exploits P DP φ ε hε hded h hcons)

/-- Exploitation under *infinitely-often* underpricing (the accumulation argument). With
prices bounded by `1`, every plausible assessment is `≥ 0` (bounded below); and along the
subsequence of underpriced days the net worth grows without bound. -/
lemma buyDaily_exploits_freq (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hded : ∀ n, φ ∈ DP.D n) (hP1 : ∀ n, P n φ ≤ 1)
    (hfreq : ∃ᶠ n in atTop, P n φ ≤ 1 - ε)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyDaily φ).Exploits P DP := by
  refine exploits_of_nonneg_partialSums (buyDaily φ) P DP (fun i => 1 - P i φ) ε hε
    (fun i => by have := hP1 i; linarith) (fun n v hv => ?_)
    (hfreq.mono (fun n hn => by linarith)) hcons
  have hpay : v.payout φ = 1 := by rw [PCWorld.payout, if_pos (hv φ (hded n))]
  rw [buyDaily_netWorth, hpay]

/-- **Limiting form of the fixed-sentence fragment**: under a logical inductor, an
always-deducible `φ` has `Pₙ(φ)` eventually within any `ε` of `1`. This is the criterion
output — `¬(underpriced infinitely often)`. The price range is carried by
`IsLogicalInductor`.

Carries no node, for the reason recorded at `lic_deducible_price_near_one`. -/
lemma lic_deducible_eventually_ge (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (hded : ∀ n, φ ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, 1 - ε < P n φ := by
  have hP1 : ∀ n, P n φ ≤ 1 := fun n => (hLI.price_mem_Icc n φ).2
  by_contra h
  rw [not_eventually] at h
  simp only [not_lt] at h
  exact hLI.noExploitTok (buyDaily φ) (buyDaily_ec φ)
    (buyDaily_exploits_freq P DP φ ε hε hded hP1 h hcons)

/-- **Convergence form of the fixed-sentence fragment**: the price of an always-deducible
sentence converges to `1`. Packages `lic_deducible_eventually_ge` with the upper bound
`Pₙ(φ) ≤ 1` (from the inductor's market certificate) into `ConvergesTo` (`dd:asymp`).

Carries no node, for the reason recorded at `lic_deducible_price_near_one`. -/
lemma lic_deducible_tendsto_one (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (hded : ∀ n, φ ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ) 1 := by
  have hP1 : ∀ n, P n φ ≤ 1 := fun n => (hLI.price_mem_Icc n φ).2
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (lic_deducible_eventually_ge P DP φ hded hcons ε hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := hN n hn
  have h2 := hP1 n
  constructor <;> linarith


end LogicalInduction
