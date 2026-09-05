import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.Hysteresis

/-!
# §4.1 Convergence and Coherence

The two exploitation arguments behind `thm:con` and behind two of the three bullets of
`thm:lc`. Every exploitation here routes through `exploits_of_nonneg_partialSums`
(`Properties/Basic.lean`): each trader in this module is world-neutral, so its day-`i` value
is one fixed real and its net worth is that sequence's partial sum.

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

`oscillation_exploitable` names the arbitrage trader: the hysteresis trader of
`Properties/Hysteresis.lean`, which buys below `a`, holds through the ramp and sells above
`b`, packaged with its efficient-computability certificate.

## Limit coherence

`lic_disprovable_tendsto_zero` is bullet 2 of `thm:lc`: the price of a sentence disprovable
from day 0 on converges to `0`. Its trader is `sellDaily`, which sells one share of `φ` a
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

Those two bullets take their derivability hypothesis in the *day-0* form `∀ n, χ ∈ DP.D n`
rather than the paper's `Θ ⊢ χ` (tex:1022-1024). Since a `DeductiveProcess` is monotone, that
is membership in the very first stage, and it is strictly stronger than the paper's
`∃ k, χ ∈ DP.D k`: it says the sentence is derivable from day 0 on, not merely eventually.
`lic_limitCoherence` carries the node at the paper's own form — it takes no derivability
hypothesis at all, and the measure it produces is supported on the completed-theory worlds,
so the paper's `Θ ⊢ ¬φ` bullets read off it directly.
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
    (hε : 0 < ε) (hdis : ∀ n, (∼φ) ∈ DP.D n) (hP0 : ∀ n, 0 ≤ P n φ)
    (hfreq : ∃ᶠ n in atTop, ε ≤ P n φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (sellDaily φ).Exploits P DP := by
  refine exploits_of_nonneg_partialSums (sellDaily φ) P DP (fun i => P i φ) ε hε hP0
    (fun n v hv => ?_) hfreq hcons
  rw [sellDaily_netWorth, PCWorld.payout_of_disprovable v φ (hv (∼φ) (hdis n))]
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

/-- **Limit Coherence, bullet (2)** (`thm:lc`): the price of a sentence disprovable from day
0 on converges to `0` under a logical inductor.

The hypothesis `hdis : ∀ n, (∼φ) ∈ DP.D n` is the day-0 form: monotonicity of `DP` makes it
membership in the first stage, strictly stronger than the paper's `Θ ⊢ ¬φ`, which is
`∃ k, (∼φ) ∈ DP.D k`. `lic_limitCoherence` (`LimitCoherence.lean`) carries `thm:lc` at the
paper's own form, with no derivability hypothesis at all.
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
`∼(φ∧ψ)` is disprovable from day 0 on (the disjuncts are exclusive), the price gap
`Pₙ(φ∨ψ) − Pₙ(φ) − Pₙ(ψ)` converges to `0` under a logical inductor. Hence
`P∞(φ∨ψ) = P∞(φ) + P∞(ψ)` wherever the limits exist (`thm:con`). Both over- and under-pricing
are killed by the world-neutral portfolio `σ·[(-1,φ∨ψ),(1,φ),(1,ψ)]` (`σ = ±1`), whose value is
world-independent by exclusivity.

The hypothesis `hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n` is the day-0 form, strictly stronger than
the paper's `Θ ⊢ ¬(φ∧ψ)`, which is `∃ k, (∼(φ ⋏ ψ)) ∈ DP.D k`; `lic_limitCoherence`
(`LimitCoherence.lean`) carries `thm:lc` at the paper's own form.
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
prices converge (guaranteed by `thm:con`), the limiting price of a disjunction whose
exclusivity is disprovable from day 0 on is the sum `P∞(φ∨ψ) = P∞(φ) + P∞(ψ)`. Immediate from
`lic_excl_gap_tendsto_zero` and uniqueness of limits. Stated with the convergences as explicit
hypotheses so it is self-contained; `lic_price_convergesTo` (below) discharges all three.

The hypothesis `hexcl` is inherited from `lic_excl_gap_tendsto_zero` in the same day-0 form,
strictly stronger than the paper's `Θ ⊢ ¬(φ∧ψ)`; `lic_limitCoherence` (`LimitCoherence.lean`)
carries `thm:lc` at the paper's own form.
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

/-! ## Convergence -/

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
