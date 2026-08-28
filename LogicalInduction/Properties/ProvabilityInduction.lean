/-
# Provability Induction — §4.2, `thm:provind` (`app:provind`, `sec:provind`)

Fixed-sentence and `𝓔𝓒`-sequence forms.
-/
import LogicalInduction.Properties.Basic
import LogicalInduction.Framework.WriteOut

namespace LogicalInduction

open Filter Topology


/-! ### The exploiting trader (`def:trader`) -/

/-- The trader that buys exactly one share of `φ` on every day. Each day-`n` strategy is
the single pair `(1, φ)`: a constant (hence continuous, hence legal) trade of rank 0. This
is the exploiting trader for the base case of Provability Induction. -/
def buyDaily (φ : Sentence) : Trader where
  strat _ := { trades := [(EF.const 1, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact Nat.zero_le _ }


@[simp] theorem buyDaily_value (φ : Sentence) (V : History) (w : Sentence → ℝ) (n : ℕ) :
    ((buyDaily φ).strat n).value V w = w φ - V n φ := by
  simp [buyDaily, Strategy.value]


lemma buyDaily_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (buyDaily φ).netWorth V v m = ∑ i ∈ Finset.range (m + 1), (v.payout φ - V i φ) := by
  simp [Trader.netWorth]


/-! ### Efficient computability, via the clocked interpreter

The day-`n` strategy is the same constant list `[(const 1, φ)]` for every `n`, so the
program that computes it is `Code.const K`, where `K` is that list's code. It halts within
`n + K + 1` fuel (`evaln_const_self`), which is affine in `n`, hence within the polynomial
budget `EfficientlyComputable` requires — a single program producing the strategies under
a polynomial clock, in the `dd:fuel` model. -/
lemma buyDaily_ec (φ : Sentence) : EfficientlyComputableTok (buyDaily φ) := by
  refine ecTok_of_stream _ ?_
  have h : ∀ n, ((buyDaily φ).strat n).trades = [(EF.const 1, φ)] := fun _ => rfl
  simp only [h]
  exact PolyTokenStream.trades_cons (PolyTokenStream.serialize_const 1)
    (PolyFueled.const (Encodable.encode φ)) PolyTokenStream.trades_nil


/-! ### The exploitation (`def:exploitation`) -/

/-- If `φ` is always deducible and the market holds it uniformly `ε` below 1, the
do-buy-daily trader exploits: bounded below (net worth `≥ 0` in every plausible world,
since every world consistent with `Dₘ ∋ φ` values `φ` at 1) yet unbounded above (net worth
`≥ (m+1)·ε → ∞`). -/
lemma buyDaily_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hded : ∀ n, φ ∈ DP.D n) (hunder : ∀ n, P n φ ≤ 1 - ε)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyDaily φ).Exploits P DP := by
  -- In any world plausible on day `m`, `φ ∈ D m` is affirmed, so its payout is 1.
  have hpay : ∀ (m : ℕ) (v : PCWorld), v.ConsistentWith (DP.D m) → v.payout φ = 1 := by
    intro m v hv
    rw [PCWorld.payout, if_pos (hv φ (hded m))]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · -- Bounded below by 0: every assessment is a sum of nonnegative `(1 − Pᵢ φ)` terms.
    rintro x ⟨m, v, hv, rfl⟩
    rw [buyDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [hpay m v hv]; have := hunder i; linarith
  · -- Unbounded above: assessment on day `m` is `≥ (m+1)·ε`, which diverges.
    rintro ⟨B, hB⟩
    have key : ∀ m : ℕ, (m + 1 : ℝ) * ε ≤ B := by
      intro m
      obtain ⟨v, hv⟩ := hcons m
      have hmem : (buyDaily φ).netWorth P v m ∈ (buyDaily φ).plausibleAssessments P DP :=
        ⟨m, v, hv, rfl⟩
      have hge : (m + 1 : ℝ) * ε ≤ (buyDaily φ).netWorth P v m := by
        rw [buyDaily_netWorth, hpay m v hv]
        calc (m + 1 : ℝ) * ε
            = ∑ _i ∈ Finset.range (m + 1), ε := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
          _ ≤ ∑ i ∈ Finset.range (m + 1), (1 - P i φ) :=
              Finset.sum_le_sum (fun i _ => by have := hunder i; linarith)
      exact hge.trans (hB hmem)
    obtain ⟨m, hm⟩ := exists_nat_gt (B / ε)
    have hBm : B < (m : ℝ) * ε := by rw [div_lt_iff₀ hε] at hm; linarith
    have := key m
    push_cast at this
    nlinarith [this, hBm, hε]


/-! ### The criterion consequence (`def:lic`) -/

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


/-! ## Provability Induction in the limit, for a fixed sentence

The statement above assumed *uniform* underpricing and concluded only that the price rises
above `1 − ε` once. The `thm:provind` conclusion is the limit statement `Pₙ(φ) → 1`. For a
fixed always-deducible `φ` the same constant `buyDaily` trader delivers it under a stronger
analysis: if the price dips below `1 − ε` infinitely often, buying one share a day
accumulates profit `≥ ε` on each of infinitely many days, so net worth is unbounded. -/

/-- Exploitation under *infinitely-often* underpricing (the accumulation argument). With
prices bounded by `1`, every plausible assessment is `≥ 0` (bounded below); and along the
subsequence of underpriced days the net worth grows without bound. -/
lemma buyDaily_exploits_freq (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hded : ∀ n, φ ∈ DP.D n) (hP1 : ∀ n, P n φ ≤ 1)
    (hfreq : ∃ᶠ n in atTop, P n φ ≤ 1 - ε)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (buyDaily φ).Exploits P DP := by
  have hpay : ∀ (m : ℕ) (v : PCWorld), v.ConsistentWith (DP.D m) → v.payout φ = 1 :=
    fun m v hv => by rw [PCWorld.payout, if_pos (hv φ (hded m))]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · -- bounded below by 0: each term `1 − Pᵢ φ ≥ 0` since `Pᵢ φ ≤ 1`.
    rintro x ⟨m, v, hv, rfl⟩
    rw [buyDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [hpay m v hv]; have := hP1 i; linarith
  · -- unbounded above: extract the underpriced subsequence and accumulate.
    rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hcons (g M)
    -- the day-`g M` assessment is `≥ (M+1)·ε`.
    have hsub : (Finset.range (M + 1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M + 1 : ℝ) * ε ≤ (buyDaily φ).netWorth P v (g M) := by
      rw [buyDaily_netWorth, hpay (g M) v hv]
      calc (M + 1 : ℝ) * ε
          = ∑ _k ∈ Finset.range (M + 1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M + 1), (1 - P (g k) φ) :=
            Finset.sum_le_sum (fun k _ => by have := hg k; linarith)
        _ = ∑ i ∈ (Finset.range (M + 1)).image g, (1 - P i φ) := by
            rw [Finset.sum_image (hg_mono.injective.injOn)]
        _ ≤ ∑ i ∈ Finset.range (g M + 1), (1 - P i φ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => by have := hP1 i; linarith)
    have hmem : (buyDaily φ).netWorth P v (g M) ∈ (buyDaily φ).plausibleAssessments P DP :=
      ⟨g M, v, hv, rfl⟩
    have hBm : B < (M + 1 : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)


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


/-! ## `thm:provind` — sequence form (efficiently computable sentence sequence)

The fixed-`φ` limiting form (`lic_deducible_tendsto_one`) generalizes to a *sequence* `φₙ`: the
same constant buy trader, now indexed, works — the only new ingredient is certifying the
trader efficiently computable when the *sentence* varies, which needs the sequence to be an
efficiently computable sequence of sentences (`hφ`, the paper's `𝓔𝓒`-sequence), discharged via
`ec_of_polyEF_seq`. -/

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


/-- Symbol-class certificate for the sequence buy trader: the coefficient is a
price-free constant, so the 𝓔𝓒 sentence stream is the only varying slot.
Paper node: `def:ec` -/
lemma buySeq_ec_rpn (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    EfficientlyComputable (buySeq φ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig _ (fun _ => .const 1) φ
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1))
    (fun _ => trivial) hφ (fun _ => rfl)

lemma buySeq_ec (φ : ℕ → Sentence) {cφ : Nat.Partrec.Code}
    (hφ : PolyFueled cφ (fun n => Encodable.encode (φ n))) :
    EfficientlyComputableTok (buySeq φ) := by
  refine ecTok_of_stream _ ?_
  have h : ∀ n, ((buySeq φ).strat n).trades = [(EF.const 1, φ n)] := fun _ => rfl
  simp only [h]
  exact PolyTokenStream.trades_cons (PolyTokenStream.serialize_const 1) hφ
    PolyTokenStream.trades_nil


/-- **Timely-membership form of the sequence statement**: for an efficiently computable
sequence of sentences `φₙ`, *each already deduced by its own day* (`hded : φ n ∈ D n`),
the price `Pₙ(φₙ) → 1`. Same constant buy trader as the fixed case, now indexed by the
sequence; e.c. directly in the symbol-metered class from the `𝓔𝓒`-sequence
hypothesis (`BigSentenceCodes`), which admits arbitrarily deep and skewed sentence
sequences.

**This is not the paper's `thm:provind`**, whose content is precisely that `φ n` need
*not* be in `D n` — theorems may be proved arbitrarily later than their indices. The
faithful sequence form is `lic_provind` (`AffineCoherence.lean`), which assumes only
`∀ n, ∃ k, φ n ∈ D k`. This fragment is retained for its simpler trader and hypotheses.
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
    refine hLI.noExploit (buySeq φ) (buySeq_ec_rpn φ hφ) ?_
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
