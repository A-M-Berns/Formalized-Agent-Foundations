import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Framework.Emission.WriteOut

/-!
# §4.1 Convergence and Coherence

The two exploitation arguments behind `thm:con` and behind two of the three bullets of
`thm:lc`, together with the hysteresis arbitrage trader `thm:con` turns on. Every
exploitation here routes through the engines of `Properties/Support/Exploitation.lean`: the
`thm:lc` traders are world-neutral, so their day-`i` value is one fixed real and their net
worth is that sequence's partial sum.

## Convergence

`lic_price_convergesTo` renders `thm:con`: under a logical inductor the price of every
sentence converges. The proof reduces non-convergence to a rational oscillation and
arbitrages it. The canonical carrier of `thm:con` in the `ℙ∞` naming is
`lic_limitingBelief_tendsto` (`AffinePersistence.lean`), which names the limit; this module
supplies its existence.

`exists_rat_oscillation_of_not_exists_convergesTo` is the reduction: a `[0,1]`-bounded
sequence that fails to converge oscillates across a rational gap — below `a` infinitely often
and above `b` infinitely often, for some rationals `a < b`. It is the contrapositive of
Mathlib's `tendsto_of_no_upcrossings` taken over the dense range of `(↑) : ℚ → ℝ`, and the
rationality of `a` and `b` is what lets an arbitrage trader use the two thresholds as `EF`
constants. It is stated at an arbitrary bounded sequence rather than at prices;
`exists_rat_oscillation_of_not_convergesTo` is the price instance.

`oscillation_exploitable` names the arbitrage trader: the hysteresis trader `hystTrader`,
which buys below `a`, holds through the ramp and sells above `b`, packaged with its
efficient-computability certificate. Its continuous threshold indicators and the `[0,1]` clip
its holdings state is built from are `Properties/Support/Exploitation.lean`'s.

## Limit coherence

`lic_disprovable_tendsto_zero` is bullet 2 of `thm:lc`: the price of a sentence disproved at
some stage converges to `0`. Its trader is `sellDaily`, which sells one share of `φ` a
day; every plausible world values a disprovable `φ` at `0`, so the day-`i` value is `Pᵢ(φ)`.

`lic_excl_gap_tendsto_zero` and `lic_limit_additive` are bullet 3: the price gap
`Pₙ(φ∨ψ) − Pₙ(φ) − Pₙ(ψ)` of an exclusive disjunction converges to `0`, and hence the
limiting prices are additive. The trader is `exclTr`, which plays the world-neutral portfolio
`σ·[(-1, φ∨ψ), (1, φ), (1, ψ)]` gated by the continuous buy-signal `sigEF` on the price gap
`gapEF`, in both directions `σ = ±1`. `PCWorld.payout_or_of_excl` is the world-level finite
additivity identity that portfolio rests on, shared with `LimitCoherence.lean`.

The canonical carrier of `thm:lc` as a whole — the Gaifman conditions on the limiting belief
and the countably additive measure on completed worlds — is `lic_limitCoherence`
(`LimitCoherence.lean`); the two theorems here are contributing bullets.

Those two bullets take their derivability hypothesis in the paper's own `Θ ⊢ χ` form
(tex:1022-1024), rendered `∃ k, χ ∈ DP.D k`: the sentence is disproved at *some* stage.
The finitely many days before that stage cannot break bounded downside, which is what
`exploits_of_ge_partialSums_from` (`Support/Exploitation.lean`) packages.
`lic_limitCoherence` carries the
node as a whole — it takes no derivability hypothesis at all, and the measure it produces is
supported on the completed-theory worlds, so the paper's `Θ ⊢ ¬φ` bullets read off it
directly.
-/

namespace LogicalInduction

open Filter Topology

/-! ## Limit coherence: disprovable sentences -/

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
    (hε : 0 < ε) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    {k : ℕ} (hdis : (∼φ) ∈ DP.D k) (hP0 : ∀ n, 0 ≤ P n φ)
    (hfreq : ∃ᶠ n in atTop, ε ≤ P n φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sellDaily φ).Exploits P DP := by
  refine exploits_of_ge_partialSums_from (sellDaily φ) P DP hP (fun i => P i φ) ε hε hP0 k
    (fun n hkn v hv => ?_) hfreq hcons
  rw [sellDaily_netWorth,
    PCWorld.payout_of_disprovable v φ (hv (∼φ) (DP.mono_le hkn hdis))]
  simp

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

The hypothesis `hdis : ∃ k, (∼φ) ∈ DP.D k` is the paper's `Θ ⊢ ¬φ` (tex:1022-1024): the
sentence is disproved at *some* stage.  `lic_limitCoherence` (`LimitCoherence.lean`) carries
`thm:lc` as a whole, with no derivability hypothesis at all.
Paper node: `thm:lc` -/
theorem lic_disprovable_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence) (hdis : ∃ k, (∼φ) ∈ DP.D k)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ) 0 := by
  obtain ⟨k, hk⟩ := hdis
  have hP0 : ∀ n, 0 ≤ P n φ := fun n => (hLI.price_mem_Icc n φ).1
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have hev : ∀ᶠ n in atTop, P n φ < ε := by
    by_contra h
    rw [not_eventually] at h
    simp only [not_lt] at h
    exact hLI.noExploitTok (sellDaily φ) (sellDaily_ec φ)
      (sellDaily_exploits_freq P DP φ ε hε
        (fun n ψ => hLI.price_mem_Icc n ψ) hk hP0 h hcons)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have := hP0 n
  have h1 := hN n hn
  constructor <;> linarith

/-! ## Limit coherence: finite additivity -/

/-- Price gap of an exclusive pair: `P(φ∨ψ) − P(φ) − P(ψ)`, as an `EF`. -/
noncomputable def gapEF (φ ψ : Sentence) (n : ℕ) : EF :=
  .add (.price (φ ⋎ ψ) n) (.add (.mul (.const (-1)) (.price φ n)) (.mul (.const (-1)) (.price ψ n)))

/-- Continuous buy-signal for direction `σ ∈ {1,-1}`: `max(0, σ·gap − ε/2)`. -/
noncomputable def sigEF (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : EF :=
  buySignal (.mul (.const σ) (gapEF φ ψ n)) ε

/-- The price gap reads only day-`n` prices, so it has rank at most `n`: the legality fact a
client gating a trader on `gapEF` needs. -/
lemma gapEF_rank (φ ψ : Sentence) (n : ℕ) : (gapEF φ ψ n).rank ≤ n := by
  simp [gapEF, EF.rank]

/-- The buy-signal inherits the rank of the gap it reads. -/
lemma sigEF_rank (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : (sigEF φ ψ σ ε n).rank ≤ n := by
  simpa [sigEF] using gapEF_rank φ ψ n

/-- The exclusion-arbitrage trader for direction `σ`: each day plays `sig` copies of the
world-neutral portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]`. -/
noncomputable def exclTr (φ ψ : Sentence) (σ ε : ℚ) : Trader where
  strat n := { trades := [(.mul (sigEF φ ψ σ ε n) (.const (-σ)), φ ⋎ ψ),
                          (.mul (sigEF φ ψ σ ε n) (.const σ), φ),
                          (.mul (sigEF φ ψ σ ε n) (.const σ), ψ)]
               rank_le := by
                 intro p hp
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
    {k : ℕ} (hexcl : (∼(φ ⋏ ψ)) ∈ DP.D k) (n : ℕ) (hkn : k ≤ n)
    (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (exclTr φ ψ σ ε).netWorth P v n = ∑ i ∈ Finset.range (n+1), exclW P φ ψ σ ε i := by
  simp only [Trader.netWorth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact exclTr_value φ ψ σ ε P v i (hv _ (DP.mono_le hkn hexcl))

/-- The real price-gap equals the `gapEF` denotation. -/
lemma gapEF_denote (φ ψ : Sentence) (P : History) (n : ℕ) :
    (gapEF φ ψ n).denote P = P n (φ ⋎ ψ) - P n φ - P n ψ := by
  simp only [gapEF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring

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
    (hε : 0 < ε) (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    {k : ℕ} (hexcl : (∼(φ ⋏ ψ)) ∈ DP.D k)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfreq : ∃ᶠ n in atTop, (ε:ℝ) ≤ (σ:ℝ) * (gapEF φ ψ n).denote P) :
    (exclTr φ ψ σ ε).Exploits P DP := by
  have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  refine exploits_of_ge_partialSums_from (exclTr φ ψ σ ε) P DP hP (exclW P φ ψ σ ε)
    ((ε:ℝ)^2/2) (by positivity) (fun i => exclW_nonneg P φ ψ σ ε hε i) k
    (fun n hkn v hv => (exclTr_netWorth φ ψ σ ε P DP hexcl n hkn v hv).ge) ?_ hcons
  refine hfreq.mono (fun n hn => ?_)
  rw [exclW, sigEF_denote]
  set g := (σ:ℝ) * (gapEF φ ψ n).denote P with hgdef
  rw [max_eq_right (by linarith)]
  nlinarith [hn, hεr]

/-- **Finite additivity of the limiting belief** (`thm:lc`, bullet 3, finite-stage form): if
`∼(φ∧ψ)` is disproved at some stage (the disjuncts are exclusive), the price gap
`Pₙ(φ∨ψ) − Pₙ(φ) − Pₙ(ψ)` converges to `0` under a logical inductor. Hence
`P∞(φ∨ψ) = P∞(φ) + P∞(ψ)` wherever the limits exist (`thm:con`). Both over- and under-pricing
are killed by the world-neutral portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]` (`σ = ±1`), whose value is
world-independent by exclusivity.

The hypothesis `hexcl : ∃ k, (∼(φ ⋏ ψ)) ∈ DP.D k` is the paper's `Θ ⊢ ¬(φ∧ψ)`;
`lic_limitCoherence` (`LimitCoherence.lean`) carries `thm:lc` as a whole.
Paper node: `thm:lc` -/
theorem lic_excl_gap_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (hexcl : ∃ k, (∼(φ ⋏ ψ)) ∈ DP.D k)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n (φ ⋎ ψ) - P n φ - P n ψ) 0 := by
  obtain ⟨k, hk⟩ := hexcl
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ => hLI.price_mem_Icc n φ
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  -- upper: gap eventually < q
  have h1 : ∀ᶠ n in atTop, (gapEF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    exact hLI.noExploitTok _ (exclTr_ec φ ψ 1 q)
      (exclTr_exploits P DP φ ψ 1 q hq0' hP hk hcons (by simpa using hc))
  -- lower: gap eventually > -q
  have h2 : ∀ᶠ n in atTop, -(q:ℝ) < (gapEF φ ψ n).denote P := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploitTok _ (exclTr_ec φ ψ (-1) q)
      (exclTr_exploits P DP φ ψ (-1) q hq0' hP hk hcons ?_)
    refine hc.mono (fun n hn => ?_)
    push_cast; nlinarith [hn]
  have hfin : ∀ᶠ n in atTop, dist (P n (φ ⋎ ψ) - P n φ - P n ψ) 0 < ε := by
    filter_upwards [h1, h2] with n hn1 hn2
    rw [Real.dist_eq, ← gapEF_denote φ ψ P n, abs_lt]
    constructor <;> linarith
  exact eventually_atTop.mp hfin

/-- **Finite additivity of the limit** (`thm:lc`, bullet 3, limit form): wherever the three
prices converge (guaranteed by `thm:con`), the limiting price of a disjunction whose
exclusivity is disproved at some stage is the sum `P∞(φ∨ψ) = P∞(φ) + P∞(ψ)`. Immediate from
`lic_excl_gap_tendsto_zero` and uniqueness of limits. Stated with the convergences as explicit
hypotheses so it is self-contained; `lic_price_convergesTo` (below) discharges all three.

The hypothesis `hexcl` is inherited from `lic_excl_gap_tendsto_zero` in the paper's
`Θ ⊢ ¬(φ∧ψ)` form; `lic_limitCoherence` (`LimitCoherence.lean`) carries `thm:lc` as a whole.
Paper node: `thm:lc` -/
theorem lic_limit_additive (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ ψ : Sentence) (hexcl : ∃ k, (∼(φ ⋏ ψ)) ∈ DP.D k)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (Lφψ Lφ Lψ : ℝ) (hφψ : ConvergesTo (fun n => P n (φ ⋎ ψ)) Lφψ)
    (hφ : ConvergesTo (fun n => P n φ) Lφ) (hψ : ConvergesTo (fun n => P n ψ) Lψ) :
    Lφψ = Lφ + Lψ := by
  have hgap := lic_excl_gap_tendsto_zero P DP φ ψ hexcl hcons
  have hto : ConvergesTo (fun n => P n (φ ⋎ ψ) - P n φ - P n ψ) (Lφψ - Lφ - Lψ) :=
    (hφψ.sub hφ).sub hψ
  have := tendsto_nhds_unique hto hgap
  linarith

/-! ## The oscillation reduction -/

/-- **The oscillation reduction, general form.** A `[0,1]`-bounded real sequence that does
*not* converge must **oscillate across a rational gap**: there are rationals `a < b` with the
sequence below `a` infinitely often and above `b` infinitely often. Stated at an arbitrary
bounded sequence; `exists_rat_oscillation_of_not_convergesTo` is the price instance.

This is the contrapositive of `tendsto_of_no_upcrossings` instantiated at the dense range
of `(↑) : ℚ → ℝ`; the rationality of `a, b` is what lets the arbitrage traders use them as
`EF` constants. -/
lemma exists_rat_oscillation_of_not_exists_convergesTo (u : ℕ → ℝ)
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
lemma exists_rat_oscillation_of_not_convergesTo (P : History) (φ : Sentence)
    (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hnc : ¬ ∃ L, ConvergesTo (fun n => P n φ) L) :
    ∃ a b : ℚ, (a : ℝ) < b ∧ (∃ᶠ n in atTop, P n φ < (a : ℝ)) ∧
      (∃ᶠ n in atTop, (b : ℝ) < P n φ) :=
  exists_rat_oscillation_of_not_exists_convergesTo (fun n => P n φ) hb hnc

/-! ## The hysteresis arbitrage trader

The trader `oscillation_exploitable` turns on.  It carries a size-`Θ(n)` running holdings
state `hystN`: `H 0 = 0`, `H (k+1) = max (H k · (1 − sellInd k)) (buyInd k)`, with the
recursive branch written first so the serialization accretes fixed-width blocks in ascending
day order on one side; the day-`n` trade is `H (n+1) − H n`.

The accounting needs no per-swing induction: buys happen only below `a + δ` and sells only
above `b − δ`, so `netWorth ≥ (b−a−2δ)·B₋ − (a+δ)` in every world
(`hystTrader_netWorth_ge`), and each completed swing adds `1` to the downward variation `B₋`
(`hystBneg_unbounded`).  Efficient computability (`hystTrader_ecTok`) is a five-segment
emission: fixed head, `n+1` fixed-width blocks, fixed mid, `n` blocks, fixed tail.

The indicators and the `[0,1]` clip the state is built from are
`Properties/Support/Exploitation.lean`'s. -/

/-! ### The holdings state -/

/-- The `k`-block holdings state: `H 0 = 0`,
`H (k+1) = max (H k · (1 − sellInd k)) (buyInd k)`. Day-`n` holdings are `H (n+1)`.
The recursive branch is written first so the serialization accretes blocks in ascending
day order on one side. -/
def hystN (φ : Sentence) (a b δ : ℚ) : ℕ → EF
  | 0 => .const 0
  | (k + 1) => .max (.mul (hystN φ a b δ k) (oneMinus (sellIndEF φ b δ k)))
      (buyIndEF φ a δ k)

/-- The real holdings value `h k`. -/
noncomputable def hystH (φ : Sentence) (a b δ : ℚ) (P : History) (k : ℕ) : ℝ :=
  (hystN φ a b δ k).denote P

lemma hystH_zero (φ a b δ) (P : History) : hystH φ a b δ P 0 = 0 := by
  simp [hystH, hystN]

lemma hystH_succ (φ a b δ) (P : History) (k : ℕ) :
    hystH φ a b δ P (k + 1)
      = max (hystH φ a b δ P k * (1 - (sellIndEF φ b δ k).denote P))
          ((buyIndEF φ a δ k).denote P) := by
  simp only [hystH, hystN, EF.denote_max, EF.denote_mul, Pi.mul_apply,
    oneMinus_denote]

/-- `hystN k` references only days `< k`: rank ≤ `k − 1`. -/
lemma hystN_rank (φ a b δ) : ∀ k, (hystN φ a b δ k).rank ≤ k - 1
  | 0 => by simp [hystN]
  | (k + 1) => by
      have ih := hystN_rank φ a b δ k
      simp only [hystN, EF.rank, oneMinus_rank, sellIndEF_rank, buyIndEF_rank, max_le_iff]
      omega

section State

variable (φ : Sentence) (a b δ : ℚ) (P : History)

lemma hystH_mem : ∀ k, 0 ≤ hystH φ a b δ P k ∧ hystH φ a b δ P k ≤ 1
  | 0 => by rw [hystH_zero]; norm_num
  | (k + 1) => by
      obtain ⟨ih0, ih1⟩ := hystH_mem k
      obtain ⟨hs0, hs1⟩ := sellInd_mem φ b δ k P
      obtain ⟨hb0, hb1⟩ := buyInd_mem φ a δ k P
      rw [hystH_succ]
      constructor
      · exact le_max_of_le_right hb0
      · exact max_le (by nlinarith) hb1

variable {φ a b δ P}

/-- Fact 1: a net buy at day `k` means the buy signal fired, so `Pₖφ < a + δ`. -/
lemma hystH_incr_imp (hδ : 0 < (δ : ℝ)) {k : ℕ}
    (h : hystH φ a b δ P k < hystH φ a b δ P (k + 1)) : P k φ < (a : ℝ) + δ := by
  refine buyInd_pos_imp hδ ?_
  by_contra hb
  push_neg at hb
  have hb0 := (buyInd_mem φ a δ k P).1
  have hbz : (buyIndEF φ a δ k).denote P = 0 := le_antisymm hb hb0
  obtain ⟨ih0, ih1⟩ := hystH_mem φ a b δ P k
  obtain ⟨hs0, hs1⟩ := sellInd_mem φ b δ k P
  rw [hystH_succ, hbz] at h
  have hprod : hystH φ a b δ P k * (1 - (sellIndEF φ b δ k).denote P)
      ≤ hystH φ a b δ P k := by nlinarith
  have hprod0 : 0 ≤ hystH φ a b δ P k * (1 - (sellIndEF φ b δ k).denote P) := by nlinarith
  rw [max_eq_left hprod0] at h
  linarith

/-- Fact 2: a net sell at day `k` means the sell signal fired, so `b − δ < Pₖφ`. -/
lemma hystH_decr_imp (hδ : 0 < (δ : ℝ)) {k : ℕ}
    (h : hystH φ a b δ P (k + 1) < hystH φ a b δ P k) : (b : ℝ) - δ < P k φ := by
  refine sellInd_pos_imp hδ ?_
  by_contra hs
  push_neg at hs
  have hs0 := (sellInd_mem φ b δ k P).1
  have hsz : (sellIndEF φ b δ k).denote P = 0 := le_antisymm hs hs0
  have hle : hystH φ a b δ P k ≤ hystH φ a b δ P (k + 1) := by
    rw [hystH_succ, hsz]
    simp only [sub_zero, mul_one] at *
    exact le_max_left _ _
  linarith

/-- Fact 3 (buy side): a dip below `a` forces full holdings, `h (k+1) = 1`. -/
lemma hystH_eq_one (hδ : 0 < (δ : ℝ)) {k : ℕ} (h : P k φ < (a : ℝ)) :
    hystH φ a b δ P (k + 1) = 1 := by
  obtain ⟨ih0, ih1⟩ := hystH_mem φ a b δ P k
  obtain ⟨hs0, hs1⟩ := sellInd_mem φ b δ k P
  rw [hystH_succ, buyInd_eq_one hδ h]
  exact max_eq_right (by nlinarith)

/-- Fact 3 (sell side): a spike above `b` forces empty holdings, `h (k+1) = 0`. -/
lemma hystH_eq_zero (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ) {k : ℕ}
    (h : (b : ℝ) < P k φ) : hystH φ a b δ P (k + 1) = 0 := by
  rw [hystH_succ, buyInd_eq_zero hδ hab h, sellInd_eq_one hδ h]
  simp

end State

/-! ### The trader -/

/-- Day-`n` trade coefficient: the position change `H (n+1) − H n`. -/
def hystTradeEF (φ : Sentence) (a b δ : ℚ) (n : ℕ) : EF :=
  .add (hystN φ a b δ (n + 1)) (.mul (.const (-1)) (hystN φ a b δ n))

lemma hystTradeEF_rank (φ a b δ) (n : ℕ) : (hystTradeEF φ a b δ n).rank ≤ n := by
  have h1 := hystN_rank φ a b δ (n + 1)
  have h2 := hystN_rank φ a b δ n
  simp only [hystTradeEF, EF.rank, max_le_iff]
  omega

/-- The hysteresis trader: trades the position change on `φ` each day. -/
def hystTrader (φ : Sentence) (a b δ : ℚ) : Trader where
  strat n := { trades := [(hystTradeEF φ a b δ n, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact hystTradeEF_rank φ a b δ n }

/-- The day-`i` position change, as a real. -/
noncomputable def hystDelta (φ : Sentence) (a b δ : ℚ) (P : History) (i : ℕ) : ℝ :=
  hystH φ a b δ P (i + 1) - hystH φ a b δ P i

@[simp] lemma hystTradeEF_denote (φ a b δ) (P : History) (n : ℕ) :
    (hystTradeEF φ a b δ n).denote P = hystDelta φ a b δ P n := by
  simp only [hystTradeEF, EF.denote_add, EF.denote_mul, EF.denote_const, Pi.add_apply,
    Pi.mul_apply, hystDelta, hystH]
  push_cast; ring

lemma hystTrader_netWorth (φ a b δ) (P : History) (v : PCWorld) (n : ℕ) :
    (hystTrader φ a b δ).netWorth P v n
      = ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * (v.payout φ - P i φ) := by
  simp [Trader.netWorth, hystTrader, Strategy.value]

/-! ## The variation bookkeeping -/

/-- Positive variation `B₊ n = ∑_{i ≤ n} max Δᵢ 0`. -/
noncomputable def hystBpos (φ : Sentence) (a b δ : ℚ) (P : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), max (hystDelta φ a b δ P i) 0

/-- Negative variation `B₋ n = ∑_{i ≤ n} max (−Δᵢ) 0`. -/
noncomputable def hystBneg (φ : Sentence) (a b δ : ℚ) (P : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), max (-(hystDelta φ a b δ P i)) 0

/-- `x⁺ - x⁻ = x` in the `max`-form used by the affine serialization proofs.
(Mathlib's `posPart_sub_negPart` is the same fact in `⁺`/`⁻` notation.) -/
lemma max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -x)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ (0:ℝ))]; ring

lemma hystDelta_sum (φ a b δ) (P : History) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i = hystH φ a b δ P (n + 1) := by
  rw [show (∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i)
      = ∑ i ∈ Finset.range (n + 1), (hystH φ a b δ P (i + 1) - hystH φ a b δ P i) from rfl,
    Finset.sum_range_sub (fun i => hystH φ a b δ P i), hystH_zero, sub_zero]

lemma hystBpos_eq (φ a b δ) (P : History) (n : ℕ) :
    hystBpos φ a b δ P n = hystBneg φ a b δ P n + hystH φ a b δ P (n + 1) := by
  have : hystBpos φ a b δ P n - hystBneg φ a b δ P n
      = ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i := by
    rw [hystBpos, hystBneg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => max_sub_max_neg _)
  rw [hystDelta_sum] at this
  linarith

lemma hystBneg_nonneg (φ a b δ) (P : History) (n : ℕ) : 0 ≤ hystBneg φ a b δ P n :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- **The master bound**: in *every* world, the net worth is at least
`(b−δ−(a+δ))·B₋ − (a+δ)`. Bounded below outright; unbounded once `B₋ → ∞`. -/
lemma hystTrader_netWorth_ge (φ : Sentence) (a b δ : ℚ) (P : History)
    (hδ : 0 < (δ : ℝ)) (ha : 0 ≤ (a : ℝ) + δ) (v : PCWorld) (n : ℕ) :
    ((b : ℝ) - δ - ((a : ℝ) + δ)) * hystBneg φ a b δ P n - ((a : ℝ) + δ)
      ≤ (hystTrader φ a b δ).netWorth P v n := by
  rw [hystTrader_netWorth]
  -- Split each term: Δᵢ(w − Pᵢ) = Δᵢw − ΔᵢPᵢ.
  have hsplit : ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * (v.payout φ - P i φ)
      = v.payout φ * hystH φ a b δ P (n + 1)
        - ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * P i φ := by
    rw [← hystDelta_sum φ a b δ P n, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit]
  -- Termwise: ΔᵢPᵢ ≤ (a+δ)·max Δᵢ 0 − (b−δ)·max (−Δᵢ) 0.
  have hterm : ∀ i, hystDelta φ a b δ P i * P i φ
      ≤ ((a : ℝ) + δ) * max (hystDelta φ a b δ P i) 0
        - ((b : ℝ) - δ) * max (-(hystDelta φ a b δ P i)) 0 := by
    intro i
    rcases lt_trichotomy (hystDelta φ a b δ P i) 0 with h | h | h
    · -- net sell: Pᵢ > b − δ (fact 2)
      have hp := hystH_decr_imp hδ (show hystH φ a b δ P (i+1) < hystH φ a b δ P i by
        have := h; rw [hystDelta] at this; linarith)
      rw [max_eq_right h.le, max_eq_left (by linarith : (0:ℝ) ≤ -(hystDelta φ a b δ P i))]
      nlinarith
    · rw [h]; simp
    · -- net buy: Pᵢ < a + δ (fact 1)
      have hp := hystH_incr_imp hδ (show hystH φ a b δ P i < hystH φ a b δ P (i+1) by
        have := h; rw [hystDelta] at this; linarith)
      rw [max_eq_left h.le, max_eq_right (by linarith : -(hystDelta φ a b δ P i) ≤ (0:ℝ))]
      nlinarith
  have hsum : ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * P i φ
      ≤ ((a : ℝ) + δ) * hystBpos φ a b δ P n - ((b : ℝ) - δ) * hystBneg φ a b δ P n := by
    calc ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * P i φ
        ≤ ∑ i ∈ Finset.range (n + 1), (((a : ℝ) + δ) * max (hystDelta φ a b δ P i) 0
            - ((b : ℝ) - δ) * max (-(hystDelta φ a b δ P i)) 0) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = ((a : ℝ) + δ) * hystBpos φ a b δ P n - ((b : ℝ) - δ) * hystBneg φ a b δ P n := by
          rw [hystBpos, hystBneg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Assemble, using B₊ = B₋ + h(n+1), h ∈ [0,1], payout ≥ 0, a+δ ≥ 0.
  have hpay : 0 ≤ v.payout φ := by rw [PCWorld.payout]; split <;> norm_num
  obtain ⟨hh0, hh1⟩ := hystH_mem φ a b δ P (n + 1)
  have hBp := hystBpos_eq φ a b δ P n
  nlinarith [mul_nonneg hpay hh0]

/-! ### Unbounded downward variation under oscillation -/

section Unbounded

variable {φ : Sentence} {a b δ : ℚ} {P : History}

lemma hystBneg_mono (φ a b δ) (P : History) {n m : ℕ} (h : n ≤ m) :
    hystBneg φ a b δ P n ≤ hystBneg φ a b δ P m :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right h 1)) (fun _ _ _ => le_max_right _ _)

/-- The negative variation accumulated on `(n, m]` covers any drop in holdings. -/
lemma hystBneg_swing (φ a b δ) (P : History) {n m : ℕ} (h : n ≤ m) :
    hystH φ a b δ P (n + 1) - hystH φ a b δ P (m + 1)
      ≤ hystBneg φ a b δ P m - hystBneg φ a b δ P n := by
  have hsub : hystBneg φ a b δ P m - hystBneg φ a b δ P n
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), max (-(hystDelta φ a b δ P i)) 0 := by
    rw [hystBneg, hystBneg, eq_comm, Finset.sum_Ico_eq_sub _ (by omega)]
  have hdel : hystH φ a b δ P (m + 1) - hystH φ a b δ P (n + 1)
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), hystDelta φ a b δ P i := by
    rw [Finset.sum_Ico_eq_sub _ (by omega), hystDelta_sum, hystDelta_sum]
  have hge : ∑ i ∈ Finset.Ico (n + 1) (m + 1), (-(hystDelta φ a b δ P i))
      ≤ ∑ i ∈ Finset.Ico (n + 1) (m + 1), max (-(hystDelta φ a b δ P i)) 0 :=
    Finset.sum_le_sum (fun i _ => le_max_left _ _)
  rw [hsub]
  calc hystH φ a b δ P (n + 1) - hystH φ a b δ P (m + 1)
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), (-(hystDelta φ a b δ P i)) := by
        rw [Finset.sum_neg_distrib, ← hdel]; ring
    _ ≤ _ := hge

/-- Under two-sided oscillation the negative variation is unbounded — each full
swing (dip below `a`, then spike above `b`) adds at least `1`. -/
lemma hystBneg_unbounded (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ)
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∀ K : ℕ, ∃ n, (K : ℝ) ≤ hystBneg φ a b δ P n := by
  intro K
  induction K with
  | zero => exact ⟨0, by simpa using hystBneg_nonneg φ a b δ P 0⟩
  | succ K ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n₁, hn₁, hPn₁⟩ := (Filter.frequently_atTop.mp hA) (n + 1)
      obtain ⟨m₁, hm₁, hPm₁⟩ := (Filter.frequently_atTop.mp hB) (n₁ + 1)
      refine ⟨m₁, ?_⟩
      have h1 : hystH φ a b δ P (n₁ + 1) = 1 := hystH_eq_one hδ hPn₁
      have h0 : hystH φ a b δ P (m₁ + 1) = 0 := hystH_eq_zero hδ hab hPm₁
      have hswing := hystBneg_swing φ a b δ P (show n₁ ≤ m₁ by omega)
      have hmono := hystBneg_mono φ a b δ P (show n ≤ n₁ by omega)
      rw [h1, h0] at hswing
      push_cast
      linarith

end Unbounded

/-! ## Exploitation -/

/-- **The hysteresis trader exploits an oscillating market.** -/
lemma hystTrader_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence)
    {a b δ : ℚ} (hδ : 0 < (δ : ℝ)) (ha : 0 ≤ (a : ℝ) + δ)
    (hab : (a : ℝ) + δ < (b : ℝ) - δ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    (hystTrader φ a b δ).Exploits P DP := by
  set γ : ℝ := (b : ℝ) - δ - ((a : ℝ) + δ) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  refine exploits_of_bddBelow_of_unbounded _ _ _ ((a : ℝ) + δ) ?_ ?_
  · rintro x ⟨m, v, hv, rfl⟩
    have h := hystTrader_netWorth_ge φ a b δ P hδ ha v m
    have hB0 := hystBneg_nonneg φ a b δ P m
    nlinarith
  · intro B
    obtain ⟨K, hK⟩ := exists_nat_gt ((B + ((a : ℝ) + δ)) / γ)
    obtain ⟨n, hn⟩ := hystBneg_unbounded hδ hab.le hA hB K
    obtain ⟨v, hv⟩ := hcons n
    refine ⟨(hystTrader φ a b δ).netWorth P v n, ⟨n, v, hv, rfl⟩, ?_⟩
    have h := hystTrader_netWorth_ge φ a b δ P hδ ha v n
    rw [div_lt_iff₀ hγ0] at hK
    nlinarith

/-! ### The hysteresis trader's stream

The day-`n` stream decomposes into five segments — fixed head `[1,⌜0⌝]`, `n+1` fixed-width
blocks (the `H (n+1)` chain), fixed mid `[1,⌜−1⌝,1,⌜0⌝]`, `n` more blocks (the `H n`
chain), fixed tail `[3,2,6,⌜φ⌝]` — emitted by the segment-composition layer
(`PolySegStream`, `Framework/Emission/Computable.lean`). -/

/-- The day-`j` block of the holdings chain's serialization. -/
def hystBlk (φ : Sentence) (a b δ : ℚ) (j : ℕ) : List ℕ :=
  (oneMinus (sellIndEF φ b δ j)).serialize ++ [3] ++ (buyIndEF φ a δ j).serialize ++ [4]

lemma hystBlk_tokenStream (φ : Sentence) (a b δ : ℚ) :
    PolyTokenStream (fun m => hystBlk φ a b δ m.unpair.2) := by
  show PolyTokenStream (fun m =>
    (oneMinus (sellIndEF φ b δ m.unpair.2)).serialize ++ [3]
      ++ (buyIndEF φ a δ m.unpair.2).serialize ++ [4])
  exact (((PolyTokenStream.serialize_oneMinus
      (sellIndEF_tokenStream PolyFueled.right φ b δ)).append
    (PolyTokenStream.const 3)).append
    (buyIndEF_tokenStream PolyFueled.right φ a δ)).append (PolyTokenStream.const 4)

/-- Block width is day-independent (only the leaf day-index token varies). -/
lemma hystBlk_length (φ : Sentence) (a b δ : ℚ) (j : ℕ) :
    (hystBlk φ a b δ j).length = (hystBlk φ a b δ 0).length := by
  simp [hystBlk, buyIndEF, sellIndEF, oneMinus, clip01, efMin, EF.serialize]

lemma serialize_hystN (φ : Sentence) (a b δ : ℚ) : ∀ k,
    (hystN φ a b δ k).serialize
      = [1, Encodable.encode (0:ℚ)] ++ (List.range k).flatMap (hystBlk φ a b δ)
  | 0 => by simp [hystN, EF.serialize]
  | (k + 1) => by
      rw [hystN]
      simp only [EF.serialize]
      rw [serialize_hystN φ a b δ k, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, hystBlk]
      simp [List.append_assoc]

/-- **The hysteresis trader is efficiently computable** — five-segment emission. -/
lemma hystTrader_ecTok (φ : Sentence) (a b δ : ℚ) :
    EfficientlyComputableTok (hystTrader φ a b δ) := by
  have hW : ∀ m : ℕ, (hystBlk φ a b δ m.unpair.2).length = (hystBlk φ a b δ 0).length :=
    fun m => hystBlk_length φ a b δ _
  have hW0 : 0 < (hystBlk φ a b δ 0).length := by
    norm_num [hystBlk, buyIndEF, sellIndEF, oneMinus, clip01, efMin, EF.serialize]
  have seg1 : PolySegStream (fun _ : ℕ => [1, Encodable.encode (0:ℚ)]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have blocks1 := PolySegStream.blocks (hystBlk_tokenStream φ a b δ) _ hW hW0
    PolyFueled.id.succ_comp
  have seg3 : PolySegStream (fun _ : ℕ =>
      [1, Encodable.encode (-1:ℚ), 1, Encodable.encode (0:ℚ)]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 1).append
      ((PolyTokenStream.const _).append
        ((PolyTokenStream.const 1).append (PolyTokenStream.const _))))
  have blocks2 := PolySegStream.blocks (hystBlk_tokenStream φ a b δ) _ hW hW0
    PolyFueled.id
  have seg5 : PolySegStream (fun _ : ℕ => [3, 2, 6, Encodable.encode φ]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 3).append
      ((PolyTokenStream.const 2).append
        ((PolyTokenStream.const 6).append (PolyTokenStream.const _))))
  refine ecTok_of_segStream _ (PolySegStream.of_eq
    ((((seg1.append blocks1).append seg3).append blocks2).append seg5) ?_)
  intro n
  show _ = serializeTrades ((hystTrader φ a b δ).strat n).trades
  rw [show ((hystTrader φ a b δ).strat n).trades = [(hystTradeEF φ a b δ n, φ)] from rfl,
    serializeTrades, serializeTrades, hystTradeEF]
  simp only [EF.serialize]
  rw [serialize_hystN φ a b δ (n + 1), serialize_hystN φ a b δ n]
  simp [Nat.unpair_pair, List.append_assoc]

/-! ## Convergence -/

/-- **The oscillation-arbitrage trader exists and exploits** (`app:con`).

Given a rational oscillation of `Pₙφ` across `[a, b]` (price `< a` i.o. and `> b` i.o.), with
plausible worlds available every day, there is an *efficiently computable* trader that
exploits `P`.

The witness is the **hysteresis trader** above, at band `δ = (b−a)/4`: a size-`Θ(n)` running
holdings state — buy on dips below `a`, hold through the ramp, sell on spikes above `b`. Its
net worth is `≥ ((b−a)/2)·B₋ − (a+δ)` in *every* world (buys happen only below `a+δ`, sells
only above `b−δ`), and each completed swing adds `1` to the negative variation `B₋`, so the
oscillation drives it to unbounded upside off bounded downside.  Efficient computability is
discharged through the clocked interpreter (`hystTrader_ecTok`). -/
lemma oscillation_exploitable (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (a b : ℚ) (hab : (a : ℝ) < b) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∃ Tr : Trader, EfficientlyComputableTok Tr ∧ Tr.Exploits P DP := by
  set δ : ℚ := (b - a) / 4 with hδdef
  have hδR : ((δ : ℚ) : ℝ) = ((b : ℝ) - a) / 4 := by rw [hδdef]; push_cast; ring
  have hδ : 0 < (δ : ℝ) := by rw [hδR]; linarith
  have hgap : (a : ℝ) + δ < (b : ℝ) - δ := by rw [hδR]; linarith
  have ha : 0 ≤ (a : ℝ) + δ := by
    -- a dip day exists and prices are ≥ 0, so 0 ≤ a.
    obtain ⟨n, -, hn⟩ := (Filter.frequently_atTop.mp hA) 0
    have := (hb n).1
    linarith
  exact ⟨hystTrader φ a b δ, hystTrader_ecTok φ a b δ,
    hystTrader_exploits P DP φ hδ ha hgap hcons hA hB⟩

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
