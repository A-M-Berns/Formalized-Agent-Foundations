import LogicalInduction.Properties.Basic
import LogicalInduction.Framework.WriteOut

/-!
# Provability Induction — §4.2

The fixed-sentence and always-deduced-sequence fragments of `thm:provind` (`app:provind`,
`sec:provind`).

The canonical carrier of `thm:provind` is `lic_provind` (`AffineCoherence.lean`), which
assumes only what the paper assumes — that each sentence is deduced at *some* stage,
`∀ n, ∃ k, φ n ∈ D k`. This module holds the strictly weaker forms, whose traders are
constant and whose proofs are correspondingly short.

## Objects

`buyDaily φ` buys one share of `φ` every day: its day-`n` strategy is the constant list
`[(1, φ)]`, of rank `0`. `buySeq φ` buys one share of `φ n` on day `n`. Both come with their
value, net-worth and efficient-computability certificates.

`buyDaily_ec` runs `Code.const` on the one fixed strategy code, which halts within affine
fuel and so fits the polynomial clock (`dd:fuel`). `buySeq_ec_big` takes the paper's `𝓔𝓒`
sentence sequence in the write-out class `BigSentenceCodes` (`Framework/WriteOut.lean`),
which admits arbitrarily deep sentence families.

## Endpoints

* `lic_deducible_price_near_one` — for a single `ε`, the price of an always-deducible `φ`
  rises above `1 − ε` at some day.
* `lic_deducible_eventually_ge` — the same bound, eventually rather than once.
* `lic_deducible_tendsto_one` — for a fixed always-deducible `φ`, `Pₙ(φ) → 1`.
* `lic_provind_seq` — for an `𝓔𝓒` sequence with `φ n ∈ D n`, `Pₙ(φₙ) → 1`.

`lic_provind_seq` is not the paper's statement: `thm:provind` quantifies over an efficiently
computable sequence of *theorems*, whose proofs may arrive arbitrarily later than the index,
so the hypothesis `φ n ∈ D n` is strictly stronger than the paper's. The paper's second half
— an efficiently computable sequence of *disprovable* sentences with `Pₙ(ψₙ) → 0` — is
carried by `lic_provind_false` (`AffineCoherence.lean`).

All exploitation routes through the engines of `Properties/Basic.lean`; nothing here
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

/-- **Base case of Provability Induction** (`thm:provind`), stated against `def:lic`: a
logical inductor cannot hold an always-deducible sentence uniformly below price 1. For
every `ε > 0` the price rises above `1 − ε` at some day.
Paper node: `thm:provind` -/
theorem lic_deducible_price_near_one (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (ε : ℝ) (hε : 0 < ε)
    (hded : ∀ n, φ ∈ DP.D n) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ n, 1 - ε < P n φ := by
  by_contra h
  push_neg at h
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

/-- **Provability Induction, limiting form, for a fixed sentence** (`thm:provind`): under a
logical inductor, an always-deducible `φ` has `Pₙ(φ)` eventually within any `ε` of `1`.
This is the criterion output — `¬(underpriced infinitely often)`. The price range is
carried by `IsLogicalInductor`.
Paper node: `thm:provind` -/
theorem lic_deducible_eventually_ge (P : History) (DP : DeductiveProcess)
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

/-- **Provability Induction, convergence form** (`thm:provind`): the price of an
always-deducible sentence converges to `1`. Packages `lic_deducible_eventually_ge` with the
upper bound `Pₙ(φ) ≤ 1` (from the inductor's market certificate) into `ConvergesTo`
(`dd:asymp`).
Paper node: `thm:provind` -/
theorem lic_deducible_tendsto_one (P : History) (DP : DeductiveProcess)
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

/-! ## Provability induction along a deduced sequence -/

/-- The trader that buys one share of `φ n` on day `n` — the constant-coefficient trader for
the **sequence** form of Provability Induction. -/
noncomputable def buySeq (φ : ℕ → Sentence) : Trader where
  strat n := { trades := [(.const 1, φ n)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp; subst hp
                             simp [EF.rank] }

lemma buySeq_value (φ : ℕ → Sentence) (V : History) (v : PCWorld) (n : ℕ)
    (hpay : v.payout (φ n) = 1) :
    ((buySeq φ).strat n).value V v.payout = 1 - V n (φ n) := by
  simp only [buySeq, Strategy.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    EF.denote_const]
  rw [hpay]; push_cast; ring

/-- Write-out-class certificate for the sequence buy trader: the coefficient is a
price-free constant, so the write-out metered (`BigSentenceCodes`) 𝓔𝓒 sentence stream
is the only varying slot.
Paper node: `def:ec` -/
lemma buySeq_ec_big (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    EfficientlyComputable (buySeq φ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig _ (fun _ => .const 1) φ
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1))
    (fun _ => trivial) hφ (fun _ => rfl)

/-- **Timely-membership form of the sequence statement**: for an efficiently computable
sequence of sentences `φₙ`, *each already deduced by its own day* (`hded : φ n ∈ D n`),
the price `Pₙ(φₙ) → 1`. Efficient computability is discharged directly in the **write-out**
class from the `𝓔𝓒`-sequence hypothesis (`BigSentenceCodes`, `Framework/WriteOut.lean`),
which admits arbitrarily deep and skewed sentence sequences.

**This is not the paper's `thm:provind`**, whose content is precisely that `φ n` need
*not* be in `D n` — theorems may be proved arbitrarily later than their indices. The
faithful sequence form is `lic_provind` (`AffineCoherence.lean`), which assumes only
`∀ n, ∃ k, φ n ∈ D k`. The trader here is the constant buy trader of the fixed case, indexed
by the sequence, and the hypotheses are correspondingly simpler.
Paper node: `thm:provind` -/
theorem lic_provind_seq (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hded : ∀ n, φ n ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n (φ n)) 1 := by
  have hP1 : ∀ n, P n (φ n) ≤ 1 := fun n => (hLI.price_mem_Icc n (φ n)).2
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hev : ∀ᶠ n in atTop, 1 - ε < P n (φ n) := by
    by_contra h
    rw [not_eventually] at h; simp only [not_lt] at h
    refine hLI.noExploit (buySeq φ) (buySeq_ec_big φ hφ) ?_
    refine exploits_of_nonneg_partialSums (buySeq φ) P DP (fun i => 1 - P i (φ i)) ε hε
      (fun i => by have := hP1 i; linarith) ?_ ?_ hcons
    · intro n v hv
      simp only [Trader.netWorth]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsub : DP.D i ⊆ DP.D n := Finset.le_iff_subset.mp
        (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hi')
      have hmem : φ i ∈ DP.D n := hsub (hded i)
      exact buySeq_value φ P v i (by rw [PCWorld.payout, if_pos (hv _ hmem)])
    · exact h.mono (fun n hn => by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have := hP1 n; have := hN n hn; constructor <;> linarith

end LogicalInduction
