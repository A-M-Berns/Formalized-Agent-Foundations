/-
# §4.1 Convergence and Coherence

* `thm:lc`  — Limit Coherence (bullets 2 & 3: disprovable→0, finite additivity).
* `thm:con` — Convergence (the oscillation reduction and its arbitrage trader).
-/
import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.Hysteresis

namespace LogicalInduction

open Filter Topology


/-! ## Limit Coherence, bullet (2): disprovable ⇒ price → 0 (`thm:lc`)

The mirror image of the provability bullet, via the **sell** trader. If `φ` is disprovable
— `∼φ` always deducible — then every plausible world values `φ` at `0`, so selling one share
of `φ` a day yields net worth `∑ᵢ Pᵢ(φ) ≥ 0`; if the price stays above `ε` infinitely often
that is unbounded, so a logical inductor forces `Pₙ(φ) → 0`. -/

/-- In a world consistent with a set containing `∼φ`, `φ` is false (Foundation Boolean
semantics: `∼φ = φ 🡒 ⊥`, so `Holds (∼φ) ↔ ¬ Holds φ`). -/
lemma PCWorld.payout_of_disprovable (v : PCWorld) (φ : Sentence) (h : v.Holds (∼φ)) :
    v.payout φ = 0 := by
  have : ¬ v.Holds φ := by
    simpa [PCWorld.Holds, LO.Propositional.Formula.Boolean.val,
      LO.Propositional.Formula.neg_def] using h
  rw [PCWorld.payout, if_neg this]


/-- The trader that sells one share of `φ` every day (buys `-1`). -/
def sellDaily (φ : Sentence) : Trader where
  strat _ := { trades := [(EF.const (-1), φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact Nat.zero_le _ }


lemma sellDaily_netWorth (φ : Sentence) (V : History) (v : PCWorld) (m : ℕ) :
    (sellDaily φ).netWorth V v m = ∑ i ∈ Finset.range (m + 1), (V i φ - v.payout φ) := by
  simp only [Trader.netWorth, sellDaily, Strategy.value]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [EF.denote]


lemma sellDaily_ec (φ : Sentence) : EfficientlyComputableTok (sellDaily φ) := by
  refine ecTok_of_stream _ ?_
  have h : ∀ n, ((sellDaily φ).strat n).trades = [(EF.const (-1), φ)] := fun _ => rfl
  simp only [h]
  exact PolyTokenStream.trades_cons (PolyTokenStream.serialize_const (-1))
    (PolyFueled.const (Encodable.encode φ)) PolyTokenStream.trades_nil


/-- Exploitation of the sell trader under infinitely-often *overpricing* of a disprovable
`φ`: net worth `∑ Pᵢ(φ) ≥ 0` (prices `≥ 0`), unbounded along the overpriced subsequence. -/
lemma sellDaily_exploits_freq (P : History) (DP : DeductiveProcess) (φ : Sentence) (ε : ℝ)
    (hε : 0 < ε) (hdis : ∀ n, (∼φ) ∈ DP.D n) (hP0 : ∀ n, 0 ≤ P n φ)
    (hfreq : ∃ᶠ n in atTop, ε ≤ P n φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sellDaily φ).Exploits P DP := by
  have hpay : ∀ (m : ℕ) (v : PCWorld), v.ConsistentWith (DP.D m) → v.payout φ = 0 :=
    fun m v hv => PCWorld.payout_of_disprovable v φ (hv (∼φ) (hdis m))
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨m, v, hv, rfl⟩
    rw [sellDaily_netWorth]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [hpay m v hv]; have := hP0 i; linarith
  · rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hcons (g M)
    have hsub : (Finset.range (M + 1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi
      simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M + 1 : ℝ) * ε ≤ (sellDaily φ).netWorth P v (g M) := by
      rw [sellDaily_netWorth, hpay (g M) v hv]
      calc (M + 1 : ℝ) * ε
          = ∑ _k ∈ Finset.range (M + 1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M + 1), (P (g k) φ - 0) :=
            Finset.sum_le_sum (fun k _ => by have := hg k; linarith)
        _ = ∑ i ∈ (Finset.range (M + 1)).image g, (P i φ - 0) := by
            rw [Finset.sum_image (hg_mono.injective.injOn)]
        _ ≤ ∑ i ∈ Finset.range (g M + 1), (P i φ - 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun i _ _ => by have := hP0 i; linarith)
    have hmem : (sellDaily φ).netWorth P v (g M) ∈ (sellDaily φ).plausibleAssessments P DP :=
      ⟨g M, v, hv, rfl⟩
    have hBm : B < (M + 1 : ℝ) * ε := by rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)


/-- **Finite additivity of payout under exclusion.** If `∼(φ∧ψ)` holds (the disjuncts are
mutually exclusive), the payout of `φ∨ψ` is the sum of the payouts — the world-level identity
behind coherent finite additivity. -/
lemma PCWorld.payout_or_of_excl (v : PCWorld) (φ ψ : Sentence)
    (h : v.Holds (∼(φ ⋏ ψ))) : v.payout (φ ⋎ ψ) = v.payout φ + v.payout ψ := by
  rw [PCWorld.holds_neg, PCWorld.holds_and] at h
  simp only [PCWorld.payout]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ
  · exact absurd ⟨hφ, hψ⟩ h
  · rw [if_pos (show v.Holds (φ ⋎ ψ) from Or.inl hφ), if_pos hφ, if_neg hψ]; norm_num
  · rw [if_pos (show v.Holds (φ ⋎ ψ) from Or.inr hψ), if_neg hφ, if_pos hψ]; norm_num
  · rw [if_neg (show ¬ v.Holds (φ ⋎ ψ) from not_or.mpr ⟨hφ, hψ⟩), if_neg hφ, if_neg hψ]; norm_num


/-- **Limit Coherence, bullet (2)** (`thm:lc`): the price of a disprovable sentence
converges to `0` under a logical inductor.
Paper node: `thm:lc` -/
theorem lic_disprovable_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (hdis : ∀ n, (∼φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ) 0 := by
  have hP0 : ∀ n, 0 ≤ P n φ := fun n => (hLI.price_mem_Icc n φ).1
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hev : ∀ᶠ n in atTop, P n φ < ε := by
    by_contra h
    rw [not_eventually] at h
    simp only [not_lt] at h
    exact hLI.noExploitTok (sellDaily φ) (sellDaily_ec φ)
      (sellDaily_exploits_freq P DP φ ε hε hdis hP0 h hcons)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have := hP0 n
  have h1 := hN n hn
  constructor <;> linarith

/-! ## `thm:con` — Convergence.

> The limit `P_∞(φ) := limₙ Pₙ(φ)` exists for all `φ`.  *(Garrabrant et al., `thm:con`.)*

The paper's argument (`sec:convergence` / `app:con`): if the market never makes up its mind
about `φ`, its price oscillates, and a trader can **arbitrage** the oscillation — buy `φ`
cheap, sell it back dear — pocketing a fixed profit on each swing at no risk, hence
exploiting. A logical inductor forbids this, so the price must converge.

This splits into two halves:

1. **The reduction (`exists_rat_oscillation_of_not_convergesTo`).** Non-convergence of a
   `[0,1]`-bounded price forces a *rational* oscillation: `a < b` in `ℚ` with `Pₙφ < a`
   infinitely often and `Pₙφ > b` infinitely often. This is the contrapositive of Mathlib's
   `tendsto_of_no_upcrossings` over the dense set `↑ℚ ⊆ ℝ`.

2. **The exploiting trader (`oscillation_exploitable`).** Given the oscillation, the
   hysteresis trader (`Properties/Hysteresis.lean`) arbitrages it: buy below `a`, hold, sell
   above `b`.

`lic_price_convergesTo` chains them against `def:lic`. -/

open Filter Topology in



/-- Price gap of an exclusive pair: `P(φ∨ψ) − P(φ) − P(ψ)`, as an `EF`. -/
noncomputable def gapEF (φ ψ : Sentence) (n : ℕ) : EF :=
  .add (.price (φ ⋎ ψ) n) (.add (.mul (.const (-1)) (.price φ n)) (.mul (.const (-1)) (.price ψ n)))


/-- Continuous buy-signal for direction `σ ∈ {1,-1}`: `max(0, σ·gap − ε/2)`. -/
noncomputable def sigEF (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : EF :=
  buySignal (.mul (.const σ) (gapEF φ ψ n)) ε


lemma gapEF_rank (φ ψ : Sentence) (n : ℕ) : (gapEF φ ψ n).rank ≤ n := by
  simp [gapEF, EF.rank]

lemma sigEF_rank (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : (sigEF φ ψ σ ε n).rank ≤ n := by
  simp [sigEF, EF.rank, gapEF]


/-- The exclusion-arbitrage trader for direction `σ`: each day plays `sig` copies of the
world-neutral portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]`. -/
noncomputable def exclTr (φ ψ : Sentence) (σ ε : ℚ) : Trader where
  strat n := { trades := [(.mul (sigEF φ ψ σ ε n) (.const (-σ)), φ ⋎ ψ),
                          (.mul (sigEF φ ψ σ ε n) (.const σ), φ),
                          (.mul (sigEF φ ψ σ ε n) (.const σ), ψ)]
               rank_le := by
                 intro p hp
                 have hs := sigEF_rank φ ψ σ ε n
                 simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                 rcases hp with h|h|h <;> subst h <;>
                   exact (by simpa [EF.rank] using sigEF_rank φ ψ σ ε n) }


/-- The day-`n` payoff sequence: `sig · σ · gap`, a nonnegative world-independent real. -/
noncomputable def exclW (P : History) (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : ℝ :=
  (sigEF φ ψ σ ε n).denote P * ((σ : ℝ) * (gapEF φ ψ n).denote P)


lemma exclTr_value (φ ψ : Sentence) (σ ε : ℚ) (P : History) (v : PCWorld) (n : ℕ)
    (hv : v.Holds (∼(φ ⋏ ψ))) :
    ((exclTr φ ψ σ ε).strat n).value P v.payout = exclW P φ ψ σ ε n := by
  have hpay : v.payout (φ ⋎ ψ) = v.payout φ + v.payout ψ := PCWorld.payout_or_of_excl v φ ψ hv
  simp only [exclTr, exclW, gapEF, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, EF.denote_mul, EF.denote_const, EF.denote_add, EF.denote_price,
    Pi.mul_apply, Pi.add_apply]
  rw [hpay]; push_cast; ring


/-- Denotation of the buy-signal: `max(0, σ·gap − ε/2)`. -/
lemma sigEF_denote (φ ψ : Sentence) (σ ε : ℚ) (P : History) (n : ℕ) :
    (sigEF φ ψ σ ε n).denote P = max 0 ((σ:ℝ) * (gapEF φ ψ n).denote P + (-(ε:ℝ)/2)) := by
  simp only [sigEF, buySignal_denote, EF.denote_mul, EF.denote_const, Pi.mul_apply]


/-- `exclW` is nonnegative (needs `ε > 0`): when the signal fires, `σ·gap ≥ ε/2 > 0`. -/
lemma exclW_nonneg (P : History) (φ ψ : Sentence) (σ ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    0 ≤ exclW P φ ψ σ ε n := by
  rw [exclW, sigEF_denote]
  set G := (σ:ℝ) * (gapEF φ ψ n).denote P with hG
  by_cases h : G + (-(ε:ℝ)/2) ≤ 0
  · rw [max_eq_left h]; simp
  · push_neg at h
    have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    exact mul_nonneg (le_max_left _ _) (by nlinarith [h, hεr])


lemma exclTr_netWorth (φ ψ : Sentence) (σ ε : ℚ) (P : History) (DP : DeductiveProcess)
    (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n) (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (exclTr φ ψ σ ε).netWorth P v n = ∑ i ∈ Finset.range (n+1), exclW P φ ψ σ ε i := by
  simp only [Trader.netWorth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact exclTr_value φ ψ σ ε P v i (hv _ (hexcl n))



/-- The real price-gap equals the `gapEF` denotation. -/
lemma gapEF_denote (φ ψ : Sentence) (P : History) (n : ℕ) :
    (gapEF φ ψ n).denote P = P n (φ ⋎ ψ) - P n φ - P n ψ := by
  simp only [gapEF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring


/-- The signal template is efficiently computable. -/
lemma sigEF_polyEF (φ ψ : Sentence) (σ ε : ℚ) : PolyEF (sigEF φ ψ σ ε) := by
  have hgap : PolyEF (gapEF φ ψ) :=
    (PolyEF.price (φ ⋎ ψ)).add
      (((PolyEF.const (-1)).mul (PolyEF.price φ)).add ((PolyEF.const (-1)).mul (PolyEF.price ψ)))
  exact buySignal_polyEF ((PolyEF.const σ).mul hgap) ε


/-- The token stream of `gapEF` is compositional (an `add`/`mul`/`price`/`const` tree). -/
lemma gapEF_stream (φ ψ : Sentence) : PolyTokenStream (fun n => (gapEF φ ψ n).serialize) := by
  simp only [gapEF]
  exact PolyTokenStream.serialize_add (PolyTokenStream.serialize_price (φ ⋎ ψ))
    (PolyTokenStream.serialize_add
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const _)
        (PolyTokenStream.serialize_price φ))
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const _)
        (PolyTokenStream.serialize_price ψ)))

/-- The token stream of the buy-signal `sigEF = max(0, σ·gap − ε/2)`. -/
lemma sigEF_stream (φ ψ : Sentence) (σ ε : ℚ) :
    PolyTokenStream (fun n => (sigEF φ ψ σ ε n).serialize) := by
  simp only [sigEF, buySignal]
  exact PolyTokenStream.serialize_max (PolyTokenStream.serialize_const _)
    (PolyTokenStream.serialize_add
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const _) (gapEF_stream φ ψ))
      (PolyTokenStream.serialize_const _))

lemma exclTr_ec (φ ψ : Sentence) (σ ε : ℚ) : EfficientlyComputableTok (exclTr φ ψ σ ε) := by
  refine ecTok_of_stream _ ?_
  have h : ∀ n, ((exclTr φ ψ σ ε).strat n).trades =
      [(.mul (sigEF φ ψ σ ε n) (.const (-σ)), φ ⋎ ψ),
       (.mul (sigEF φ ψ σ ε n) (.const σ), φ),
       (.mul (sigEF φ ψ σ ε n) (.const σ), ψ)] := fun _ => rfl
  simp only [h]
  exact PolyTokenStream.trades_cons
      (PolyTokenStream.serialize_mul (sigEF_stream φ ψ σ ε) (PolyTokenStream.serialize_const _))
      (PolyFueled.const (Encodable.encode (φ ⋎ ψ)))
    (PolyTokenStream.trades_cons
      (PolyTokenStream.serialize_mul (sigEF_stream φ ψ σ ε) (PolyTokenStream.serialize_const _))
      (PolyFueled.const (Encodable.encode φ))
    (PolyTokenStream.trades_cons
      (PolyTokenStream.serialize_mul (sigEF_stream φ ψ σ ε) (PolyTokenStream.serialize_const _))
      (PolyFueled.const (Encodable.encode ψ))
    PolyTokenStream.trades_nil))


/-- Under a logical inductor with `∼(φ∧ψ)` revealed, if `σ·gap ≥ ε` frequently then the
exclusion-arbitrage trader (direction `σ`, rational threshold `ε > 0`) exploits — contradicting
`def:lic`. Its net worth is `Σ exclW`, each term nonnegative (world-neutral by exclusivity), and
`≥ ε²/2` on the frequently-underpriced days. -/
lemma exclTr_exploits (P : History) (DP : DeductiveProcess) (φ ψ : Sentence) (σ ε : ℚ)
    (hε : 0 < ε) (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfreq : ∃ᶠ n in atTop, (ε:ℝ) ≤ (σ:ℝ) * (gapEF φ ψ n).denote P) :
    (exclTr φ ψ σ ε).Exploits P DP := by
  have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  refine exploits_of_nonneg_partialSums (exclTr φ ψ σ ε) P DP (exclW P φ ψ σ ε) ((ε:ℝ)^2/2)
    (by positivity) (fun i => exclW_nonneg P φ ψ σ ε hε i)
    (exclTr_netWorth φ ψ σ ε P DP hexcl) ?_ hcons
  refine hfreq.mono (fun n hn => ?_)
  rw [exclW, sigEF_denote]
  set g := (σ:ℝ) * (gapEF φ ψ n).denote P with hgdef
  rw [max_eq_right (by linarith)]
  nlinarith [hn, hεr]


/-- **Finite additivity of the limiting belief** (`thm:lc`, bullet 3, finite-stage form): if
`∼(φ∧ψ)` is a theorem (the disjuncts are exclusive), the price gap
`Pₙ(φ∨ψ) − Pₙ(φ) − Pₙ(ψ)` converges to `0` under a logical inductor. Hence
`P∞(φ∨ψ) = P∞(φ) + P∞(ψ)` wherever the limits exist (`thm:con`). Both over- and under-pricing
are killed by the world-neutral portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]` (`σ = ±1`), whose value is
world-independent by exclusivity.
Paper node: `thm:lc` -/
theorem lic_excl_gap_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n (φ ⋎ ψ) - P n φ - P n ψ) 0 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  -- upper: gap eventually < q
  have h1 : ∀ᶠ n in atTop, (gapEF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    exact hLI.noExploitTok _ (exclTr_ec φ ψ 1 q)
      (exclTr_exploits P DP φ ψ 1 q hq0' hexcl hcons (by simpa using hc))
  -- lower: gap eventually > -q
  have h2 : ∀ᶠ n in atTop, -(q:ℝ) < (gapEF φ ψ n).denote P := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploitTok _ (exclTr_ec φ ψ (-1) q)
      (exclTr_exploits P DP φ ψ (-1) q hq0' hexcl hcons ?_)
    refine hc.mono (fun n hn => ?_)
    push_cast; nlinarith [hn]
  have hfin : ∀ᶠ n in atTop, dist (P n (φ ⋎ ψ) - P n φ - P n ψ) 0 < ε := by
    filter_upwards [h1, h2] with n hn1 hn2
    rw [Real.dist_eq, ← gapEF_denote φ ψ P n, abs_lt]
    constructor <;> linarith
  exact eventually_atTop.mp hfin


/-- **Finite additivity of the limit** (`thm:lc`, bullet 3, limit form): wherever the three
prices converge (guaranteed by `thm:con`), an exclusive disjunction's limiting price is the sum
`P∞(φ∨ψ) = P∞(φ) + P∞(ψ)`. Immediate from `lic_excl_gap_tendsto_zero` and uniqueness of limits.
Stated with the convergences as explicit hypotheses so it is self-contained (and `thm:con`,
now proved, discharges them).
Paper node: `thm:lc` -/
theorem lic_limit_additive (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ ψ : Sentence) (hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Lφψ Lφ Lψ : ℝ) (hφψ : ConvergesTo (fun n => P n (φ ⋎ ψ)) Lφψ)
    (hφ : ConvergesTo (fun n => P n φ) Lφ) (hψ : ConvergesTo (fun n => P n ψ) Lψ) :
    Lφψ = Lφ + Lψ := by
  have hgap := lic_excl_gap_tendsto_zero P DP φ ψ hexcl hcons
  have hto : ConvergesTo (fun n => P n (φ ⋎ ψ) - P n φ - P n ψ) (Lφψ - Lφ - Lψ) :=
    (hφψ.sub hφ).sub hψ
  have := tendsto_nhds_unique hto hgap
  linarith

open Filter Topology

/-- **The oscillation reduction, general form.** A `[0,1]`-bounded real sequence that does
*not* converge must **oscillate across a rational gap**: there are rationals `a < b` with the
sequence below `a` infinitely often and above `b` infinitely often. Instantiated at prices
(`exists_rat_oscillation_of_not_convergesTo`) and at expectation sequences (`thm:ec`).

This is the contrapositive of `tendsto_of_no_upcrossings` instantiated at the dense range
of `(↑) : ℚ → ℝ`; the rationality of `a, b` is what lets the arbitrage traders use them as
`EF` constants. -/
theorem exists_rat_oscillation_of_not_exists_convergesTo (u : ℕ → ℝ)
    (hb : ∀ n, 0 ≤ u n ∧ u n ≤ 1)
    (hnc : ¬ ∃ L, ConvergesTo u L) :
    ∃ a b : ℚ, (a : ℝ) < b ∧ (∃ᶠ n in atTop, u n < (a : ℝ)) ∧
      (∃ᶠ n in atTop, (b : ℝ) < u n) := by
  by_contra hcon
  refine hnc (tendsto_of_no_upcrossings (u := u) Rat.denseRange_cast ?_
    (isBoundedUnder_of ⟨1, fun n => (hb n).2⟩) (isBoundedUnder_of ⟨0, fun n => (hb n).1⟩))
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab ⟨hA, hB⟩
  exact hcon ⟨a, b, hab, hA, hB⟩

/-- **Reduction step for `thm:con`**: the price specialization of
`exists_rat_oscillation_of_not_exists_convergesTo`. -/
theorem exists_rat_oscillation_of_not_convergesTo (P : History) (φ : Sentence)
    (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hnc : ¬ ∃ L, ConvergesTo (fun n => P n φ) L) :
    ∃ a b : ℚ, (a : ℝ) < b ∧ (∃ᶠ n in atTop, P n φ < (a : ℝ)) ∧
      (∃ᶠ n in atTop, (b : ℝ) < P n φ) :=
  exists_rat_oscillation_of_not_exists_convergesTo (fun n => P n φ) hb hnc


/-- **The oscillation-arbitrage trader exists and exploits** (`app:con`).

Given a rational oscillation of `Pₙφ` across `[a, b]` (price `< a` i.o. and `> b` i.o.), with
plausible worlds available every day, there is an *efficiently computable* trader that
exploits `P`.

The witness is the **hysteresis trader** (`Properties/Hysteresis.lean`, band `δ = (b−a)/4`):
a size-`Θ(n)` running holdings state — buy on dips below `a`, hold through the ramp, sell on
spikes above `b`. Its net worth is `≥ ((b−a)/2)·B₋ − (a+δ)` in *every* world (buys happen
only below `a+δ`, sells only above `b−δ`), and each completed swing adds `1` to the negative
variation `B₋`, so the oscillation drives it to unbounded upside off bounded downside.
Efficient computability is discharged through the clocked interpreter
(`hystTrader_ecTok`). -/
lemma oscillation_exploitable (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (a b : ℚ) (hab : (a : ℝ) < b) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∃ Tr : Trader, EfficientlyComputableTok Tr ∧ Tr.Exploits P DP :=
  oscillation_exploitable_hyst P DP φ a b hab hb hcons hA hB


/-- **Convergence** (`thm:con`): under a logical inductor, the price of every sentence `φ`
converges. Proof: if not, the price oscillates across a rational gap
(`exists_rat_oscillation_of_not_convergesTo`), and that oscillation is exploitable
(`oscillation_exploitable`) by an e.c. trader — contradicting `def:lic`.

The market range is part of `IsLogicalInductor`; the remaining hypothesis says that each day
admits a plausible world (`hcons`; without it the market is vacuously unexploitable and nothing
constrains the price).
Paper node: `thm:con` -/
theorem lic_price_convergesTo (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ L, ConvergesTo (fun n => P n φ) L := by
  have hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n => hLI.price_mem_Icc n φ
  by_contra hnc
  obtain ⟨a, b, hab, hA, hB⟩ := exists_rat_oscillation_of_not_convergesTo P φ hb hnc
  obtain ⟨Tr, hec, hexp⟩ := oscillation_exploitable P DP φ a b hab hb hcons hA hB
  exact hLI.noExploitTok Tr hec hexp

end LogicalInduction
