import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.WriteOut

/-!
# Learning Logical Relationships

Renders §4.5 *Learning Logical Relationships*, `thm:lex` (appendix `app:lex`), in three
renderings of increasing generality: equivalence (`⊢ φ ↔ ψ` forces the prices together),
implication (`⊢ φ → ψ` eventually stops `φ` being overpriced against `ψ`), and the
exclusive–exhaustive families that are the paper's statement proper.

The equivalence and implication lanes share one shape: an `EF` price gap (`gap2EF`), a
continuous buy signal on it (`sig2EF` / `impSig`), a two-sentence portfolio (`eqTr` /
`impTr`), a world-independent day value (`eqW` / `impW`), an emission certificate (`eqTr_ec`
/ `impTr_ec`) and an exploitation lemma. The equivalence portfolio `σ·[(1,φ),(−1,ψ)]` is
world-neutral because equivalence equates the payouts (`PCWorld.payout_eq_of_iff`), so its
day value is the deterministic difference `σ·(Pφ − Pψ)`. The implication portfolio is only
risk-free, bounded below by `impW` because `φ → ψ` gives `payout φ ≤ payout ψ`
(`PCWorld.payout_le_of_imp`).

`lic_lex_tendsto_zero` and `lic_imp_eventually_le` are `thm:lex`-family consequences rather
than the paper's statement; `scripts/coverage-classification.md` credits `thm:lex` to
`lic_learning_exclusive_exhaustive` alone.

`exclusiveExhaustiveAffine` normalizes `(Σ_{j<k} φʲₙ − 1)/k` so the share magnitude is
exactly one, and `exclusiveExhaustive_polySequence` is its uniform emission certificate for a
fixed positive `k` of efficiently codeable sequences.
`lic_learning_exclusive_exhaustive` is `thm:lex`; its semantic premise is the
completed-theory rendering of the paper's "Θ proves exactly one member of each fixed finite
tuple". It is consumed by `Properties/{LimitCoherence,OccamBounds}.lean`.

`PCWorld.payout_eq_of_iff` and `payout_le_of_imp` are the payout facts the equivalence and
implication consequences rest on; they are stated and consumed here.
-/

namespace LogicalInduction

open Filter Topology

/-! ## Learning logical equivalence -/

/-- If both `∼φ⋎ψ` and `∼ψ⋎φ` hold (i.e. `φ ↔ ψ`), the payouts coincide. -/
lemma PCWorld.payout_eq_of_iff (v : PCWorld) (φ ψ : Sentence)
    (h1 : v.Holds (∼φ ⋎ ψ)) (h2 : v.Holds (∼ψ ⋎ φ)) : v.payout φ = v.payout ψ := by
  rw [PCWorld.holds_or, PCWorld.holds_neg] at h1 h2
  simp only [PCWorld.payout]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;>
    simp_all

/-- Price difference `Pₙφ − Pₙψ` as an `EF`. -/
noncomputable def gap2EF (φ ψ : Sentence) (n : ℕ) : EF :=
  .add (.price φ n) (.mul (.const (-1)) (.price ψ n))

/-- Buy-signal for the equivalence trader in direction `σ`: `max(0, σ·(Pφ − Pψ) − ε/2)`. -/
noncomputable def sig2EF (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : EF :=
  buySignal (.mul (.const σ) (gap2EF φ ψ n)) ε

lemma gap2EF_denote (φ ψ : Sentence) (P : History) (n : ℕ) :
    (gap2EF φ ψ n).denote P = P n φ - P n ψ := by
  simp only [gap2EF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring

lemma sig2EF_denote (φ ψ : Sentence) (σ ε : ℚ) (P : History) (n : ℕ) :
    (sig2EF φ ψ σ ε n).denote P = max 0 ((σ:ℝ) * (gap2EF φ ψ n).denote P + (-(ε:ℝ)/2)) := by
  simp only [sig2EF, buySignal_denote, EF.denote_mul, EF.denote_const, Pi.mul_apply]

/-- The equivalence-arbitrage trader for direction `σ`: plays `sig` copies of
`σ·[(1,φ),(-1,ψ)]` — world-neutral when `φ ↔ ψ`. -/
noncomputable def eqTr (φ ψ : Sentence) (σ ε : ℚ) : Trader where
  strat n := { trades := [(.mul (sig2EF φ ψ σ ε n) (.const (-σ)), φ),
                          (.mul (sig2EF φ ψ σ ε n) (.const σ), ψ)]
               rank_le := by
                 intro p hp
                 have hs : (sig2EF φ ψ σ ε n).rank ≤ n := by simp [sig2EF, EF.rank, gap2EF]
                 simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                 rcases hp with h|h <;> subst h <;>
                   exact (by simpa [EF.rank] using hs) }

/-- World-independent day-`n` value of the equivalence portfolio: `sig2EF · σ·(Pφ − Pψ)`. -/
noncomputable def eqW (P : History) (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : ℝ :=
  (sig2EF φ ψ σ ε n).denote P * ((σ : ℝ) * (gap2EF φ ψ n).denote P)

lemma eqTr_value (φ ψ : Sentence) (σ ε : ℚ) (P : History) (v : PCWorld) (n : ℕ)
    (h1 : v.Holds (∼φ ⋎ ψ)) (h2 : v.Holds (∼ψ ⋎ φ)) :
    ((eqTr φ ψ σ ε).strat n).value P v.payout = eqW P φ ψ σ ε n := by
  have hpay : v.payout φ = v.payout ψ := PCWorld.payout_eq_of_iff v φ ψ h1 h2
  simp only [eqTr, eqW, gap2EF, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, EF.denote_mul, EF.denote_const, EF.denote_add, EF.denote_price,
    Pi.mul_apply, Pi.add_apply]
  rw [hpay]; push_cast; ring

/-- A continuous buy-signal on a gap, times that gap, is never negative: the signal is zero
until the gap exceeds `ε/2`, and positive only where the gap already is. -/
lemma buySignal_mul_nonneg (G : ℝ) {ε : ℚ} (hε : 0 < ε) :
    0 ≤ max 0 (G + (-(ε:ℝ)/2)) * G := by
  by_cases h : G + (-(ε:ℝ)/2) ≤ 0
  · rw [max_eq_left h]; simp
  · push_neg at h
    have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    exact mul_nonneg (le_max_left _ _) (by nlinarith [h, hεr])

/-- The equivalence portfolio's day value is never negative. -/
lemma eqW_nonneg (P : History) (φ ψ : Sentence) (σ ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    0 ≤ eqW P φ ψ σ ε n := by
  rw [eqW, sig2EF_denote]
  exact buySignal_mul_nonneg _ hε

/-- The token stream of `gap2EF = φ*ⁿ − ψ*ⁿ` (an `add`/`mul`/`price`/`const` tree). -/
lemma gap2EF_stream (φ ψ : Sentence) : PolyTokenStream (fun n => (gap2EF φ ψ n).serialize) := by
  simp only [gap2EF]
  exact PolyTokenStream.serialize_add (PolyTokenStream.serialize_price φ)
    (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const _)
      (PolyTokenStream.serialize_price ψ))

/-- The token stream of `sig2EF = max(0, σ·(φ*−ψ*) − ε/2)`. -/
lemma sig2EF_stream (φ ψ : Sentence) (σ ε : ℚ) :
    PolyTokenStream (fun n => (sig2EF φ ψ σ ε n).serialize) := by
  simp only [sig2EF, buySignal]
  exact PolyTokenStream.serialize_max (PolyTokenStream.serialize_const _)
    (PolyTokenStream.serialize_add
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const _) (gap2EF_stream φ ψ))
      (PolyTokenStream.serialize_const _))

/-- The equivalence trader is in the token-metered efficient class, from constant sentence
codes for `φ` and `ψ`. -/
lemma eqTr_ec (φ ψ : Sentence) (σ ε : ℚ) : EfficientlyComputableTok (eqTr φ ψ σ ε) := by
  refine ecTok_of_stream _ ?_
  have h : ∀ n, ((eqTr φ ψ σ ε).strat n).trades =
      [(.mul (sig2EF φ ψ σ ε n) (.const (-σ)), φ), (.mul (sig2EF φ ψ σ ε n) (.const σ), ψ)] :=
    fun _ => rfl
  simp only [h]
  exact PolyTokenStream.trades_cons
      (PolyTokenStream.serialize_mul (sig2EF_stream φ ψ σ ε) (PolyTokenStream.serialize_const _))
      (PolyFueled.const (Encodable.encode φ))
    (PolyTokenStream.trades_cons
      (PolyTokenStream.serialize_mul (sig2EF_stream φ ψ σ ε) (PolyTokenStream.serialize_const _))
      (PolyFueled.const (Encodable.encode ψ))
    PolyTokenStream.trades_nil)

/-- A price gap violated infinitely often in direction `σ` lets the equivalence trader
exploit the market: its day values are nonnegative and infinitely often at least `ε²/2`. -/
lemma eqTr_exploits (P : History) (DP : DeductiveProcess) (φ ψ : Sentence) (σ ε : ℚ)
    (hε : 0 < ε) (himp1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n) (himp2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hfreq : ∃ᶠ n in atTop, (ε:ℝ) ≤ (σ:ℝ) * (gap2EF φ ψ n).denote P) :
    (eqTr φ ψ σ ε).Exploits P DP := by
  have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  refine exploits_of_nonneg_partialSums (eqTr φ ψ σ ε) P DP (eqW P φ ψ σ ε) ((ε:ℝ)^2/2)
    (by positivity) (fun i => eqW_nonneg P φ ψ σ ε hε i) ?_ ?_ hcons
  · intro n v hv
    simp only [Trader.netWorth]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact eqTr_value φ ψ σ ε P v i (hv _ (himp1 n)) (hv _ (himp2 n))
  · refine hfreq.mono (fun n hn => ?_)
    rw [eqW, sig2EF_denote]
    set g := (σ:ℝ) * (gap2EF φ ψ n).denote P with hgdef
    rw [max_eq_right (by linarith)]
    nlinarith [hn, hεr]

/-- **Learning of logical equivalence**: if `⊢ φ ↔ ψ` (both implications revealed by the
deductive process), the price difference `Pₙφ − Pₙψ → 0` under a logical inductor. The
portfolio is the world-neutral two-sentence one, payouts being equal by equivalence.

A consequence of the `thm:lex` family; the paper's statement itself is
`lic_learning_exclusive_exhaustive`.
Paper node: `thm:lex` -/
theorem lic_lex_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (himp1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n)
    (himp2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ - P n ψ) 0 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  have h1 : ∀ᶠ n in atTop, (gap2EF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    exact hLI.noExploitTok _ (eqTr_ec φ ψ 1 q)
      (eqTr_exploits P DP φ ψ 1 q hq0' himp1 himp2 hcons (by simpa using hc))
  have h2 : ∀ᶠ n in atTop, -(q:ℝ) < (gap2EF φ ψ n).denote P := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploitTok _ (eqTr_ec φ ψ (-1) q)
      (eqTr_exploits P DP φ ψ (-1) q hq0' himp1 himp2 hcons ?_)
    refine hc.mono (fun n hn => ?_); push_cast; nlinarith [hn]
  have hfin : ∀ᶠ n in atTop, dist (P n φ - P n ψ) 0 < ε := by
    filter_upwards [h1, h2] with n hn1 hn2
    rw [Real.dist_eq, ← gap2EF_denote φ ψ P n, abs_lt]; constructor <;> linarith
  exact eventually_atTop.mp hfin

/-! ## Learning logical implication -/

/-- `∼φ⋎ψ` (i.e. `φ→ψ`) makes `φ`'s payout `≤ ψ`'s. -/
lemma PCWorld.payout_le_of_imp (v : PCWorld) (φ ψ : Sentence)
    (h : v.Holds (∼φ ⋎ ψ)) : v.payout φ ≤ v.payout ψ := by
  rw [PCWorld.holds_or, PCWorld.holds_neg] at h
  simp only [PCWorld.payout]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;> simp_all

/-- Buy-signal for the implication trader: `max(0, (Pφ−Pψ) − ε/2)`. -/
noncomputable def impSig (φ ψ : Sentence) (ε : ℚ) (n : ℕ) : EF :=
  buySignal (gap2EF φ ψ n) ε

lemma impSig_denote (φ ψ : Sentence) (ε : ℚ) (P : History) (n : ℕ) :
    (impSig φ ψ ε n).denote P = max 0 ((gap2EF φ ψ n).denote P + (-(ε:ℝ)/2)) := by
  simp only [impSig, buySignal_denote]

/-- Implication trader: `impSig` copies of `[(-1,φ),(1,ψ)]` (sell `φ`, buy `ψ`) — profits when
`φ` is overpriced relative to `ψ`; risk-free because `φ→ψ` ⇒ `payout φ ≤ payout ψ`. -/
noncomputable def impTr (φ ψ : Sentence) (ε : ℚ) : Trader where
  strat n := { trades := [(.mul (impSig φ ψ ε n) (.const (-1)), φ),
                          (impSig φ ψ ε n, ψ)]
               rank_le := by
                 intro p hp
                 have hs : (impSig φ ψ ε n).rank ≤ n := by simp [impSig, EF.rank, gap2EF]
                 simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
                 rcases hp with h|h
                 · subst h; simpa [EF.rank] using hs
                 · subst h; exact hs }

/-- World-independent lower bound for the day-`n` value: `impSig · (Pφ − Pψ)`. -/
noncomputable def impW (P : History) (φ ψ : Sentence) (ε : ℚ) (n : ℕ) : ℝ :=
  (impSig φ ψ ε n).denote P * ((gap2EF φ ψ n).denote P)

/-- The world-independent floor `impW` on the implication portfolio's day value: `φ → ψ`
gives `payout φ ≤ payout ψ`, so the portfolio is risk-free. -/
lemma impTr_value_ge (φ ψ : Sentence) (ε : ℚ) (P : History) (v : PCWorld) (n : ℕ)
    (himp : v.Holds (∼φ ⋎ ψ)) :
    impW P φ ψ ε n ≤ ((impTr φ ψ ε).strat n).value P v.payout := by
  have hpay : v.payout φ ≤ v.payout ψ := PCWorld.payout_le_of_imp v φ ψ himp
  have hs0 : 0 ≤ (impSig φ ψ ε n).denote P := by rw [impSig_denote]; exact le_max_left _ _
  simp only [impTr, impW, gap2EF, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, EF.denote_mul, EF.denote_const, EF.denote_add, EF.denote_price,
    Pi.mul_apply, Pi.add_apply]
  have hgap : (impSig φ ψ ε n).denote P * (P n φ + (-1) * P n ψ)
      ≤ (impSig φ ψ ε n).denote P * (-1) * (v.payout φ - P n φ)
        + (impSig φ ψ ε n).denote P * (v.payout ψ - P n ψ) := by
    have : (impSig φ ψ ε n).denote P * (-1) * (v.payout φ - P n φ)
        + (impSig φ ψ ε n).denote P * (v.payout ψ - P n ψ)
        = (impSig φ ψ ε n).denote P * (P n φ + (-1)*P n ψ)
          + (impSig φ ψ ε n).denote P * (v.payout ψ - v.payout φ) := by ring
    rw [this]; nlinarith [hs0, hpay]
  simpa [gap2EF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price] using hgap

/-- The implication portfolio's world-independent floor is never negative. -/
lemma impW_nonneg (P : History) (φ ψ : Sentence) (ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    0 ≤ impW P φ ψ ε n := by
  rw [impW, impSig_denote]
  exact buySignal_mul_nonneg _ hε

/-- The token stream of `impSig = max(0, (φ*−ψ*) − ε/2)`. -/
lemma impSig_stream (φ ψ : Sentence) (ε : ℚ) :
    PolyTokenStream (fun n => (impSig φ ψ ε n).serialize) := by
  simp only [impSig, buySignal]
  exact PolyTokenStream.serialize_max (PolyTokenStream.serialize_const _)
    (PolyTokenStream.serialize_add (gap2EF_stream φ ψ) (PolyTokenStream.serialize_const _))

/-- The implication trader is in the token-metered efficient class, from constant sentence
codes for `φ` and `ψ`. -/
lemma impTr_ec (φ ψ : Sentence) (ε : ℚ) : EfficientlyComputableTok (impTr φ ψ ε) := by
  refine ecTok_of_stream _ ?_
  have h : ∀ n, ((impTr φ ψ ε).strat n).trades =
      [(.mul (impSig φ ψ ε n) (.const (-1)), φ), (impSig φ ψ ε n, ψ)] := fun _ => rfl
  simp only [h]
  exact PolyTokenStream.trades_cons
      (PolyTokenStream.serialize_mul (impSig_stream φ ψ ε) (PolyTokenStream.serialize_const _))
      (PolyFueled.const (Encodable.encode φ))
    (PolyTokenStream.trades_cons (impSig_stream φ ψ ε) (PolyFueled.const (Encodable.encode ψ))
    PolyTokenStream.trades_nil)

/-- **Learning logical implication**: if `⊢ φ → ψ` (revealed as `∼φ⋎ψ`), then a logical
inductor eventually stops overpricing `φ` relative to `ψ`: for every `ε > 0`, eventually
`Pₙφ ≤ Pₙψ + ε`.

A consequence of the `thm:lex` family; the paper's statement itself is
`lic_learning_exclusive_exhaustive`.
Paper node: `thm:lex` -/
theorem lic_imp_eventually_le (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (himp : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, P n φ ≤ P n ψ + ε := by
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  have hmain : ∀ᶠ n in atTop, (gap2EF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploitTok _ (impTr_ec φ ψ q) ?_
    refine exploits_of_ge_partialSums (impTr φ ψ q) P DP (impW P φ ψ q) ((q:ℝ)^2/2)
      (by positivity) (fun i => impW_nonneg P φ ψ q hq0' i) ?_ ?_ hcons
    · intro n v hv
      simp only [Trader.netWorth]
      refine Finset.sum_le_sum (fun i _ => impTr_value_ge φ ψ q P v i (hv _ (himp n)))
    · refine hc.mono (fun n hn => ?_)
      rw [impW, impSig_denote]
      set g := (gap2EF φ ψ n).denote P with hgdef
      have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0'
      rw [max_eq_right (by linarith)]
      nlinarith [hn, hqr]
  filter_upwards [hmain] with n hn
  rw [gap2EF_denote] at hn; linarith

/-! ## Exclusive–exhaustive families (`thm:lex`) -/

/-- The normalized affine constraint `(Σ_{j<k} φʲₙ - 1) / k`.  Normalization is internal
and leaves its share magnitude exactly one. -/
def exclusiveExhaustiveAffine (k : ℕ) (φ : ℕ → ℕ → Sentence) (n : ℕ) :
    AffineCombination where
  const := .const (-(1 / (k : ℚ)))
  terms := (List.range k).map (fun j => (.const (1 / (k : ℚ)), φ j n))

/-- Uniform polynomial affine syntax for a fixed positive number of efficiently codeable
sentence sequences. -/
noncomputable def exclusiveExhaustive_polySequence
    (k : ℕ) (hk : 0 < k) (φ : ℕ → ℕ → Sentence)
    (hφ : ∀ j < k, BigSentenceCodes (φ j)) :
    AffineCombination.PolySequence (exclusiveExhaustiveAffine k φ) := by
  exact {
    termCount := fun _ => k
    coefficient := fun _ => .const (1 / (k : ℚ))
    sentence := fun z => φ (z.unpair.2 % k) z.unpair.1
    termCount_poly := ⟨Nat.Partrec.Code.const k, PolyFueled.const k⟩
    const_poly := BigSpliceStream.serialize_const (-(1 / (k : ℚ)))
    coefficient_poly := BigSpliceStream.serialize_const (1 / (k : ℚ))
    sentence_poly := BigSentenceCodes.modDispatch hk hφ
    terms_eq := by
      intro n
      rw [exclusiveExhaustiveAffine]
      apply List.map_congr_left
      intro a ha
      simp only [Nat.unpair_pair]
      rw [Nat.mod_eq_of_lt (List.mem_range.mp ha)]
    const_rank := by intro n; simp [exclusiveExhaustiveAffine]
    coefficient_rank := by intro n j hj; simp [EF.rank]
    const_closed := by intro n ρ V; simp [exclusiveExhaustiveAffine]
    coefficient_closed := by intro z ρ V; simp [EF.denoteWith]
  }

lemma exclusiveExhaustiveAffine_price
    (k : ℕ) (_hk : 0 < k) (φ : ℕ → ℕ → Sentence)
    (P : History) (n m : ℕ) :
    (exclusiveExhaustiveAffine k φ n).price P m =
      ((List.range k).map (fun j => P m (φ j n))).sum / k - 1 / k := by
  simp only [exclusiveExhaustiveAffine, AffineCombination.price,
    AffineCombination.value, List.map_map]
  simp only [Function.comp_def, EF.denote_const]
  rw [List.sum_map_mul_left]
  push_cast
  ring

lemma exclusiveExhaustiveAffine_magnitude
    (k : ℕ) (hk : 0 < k) (φ : ℕ → ℕ → Sentence)
    (P : History) (n : ℕ) :
    (exclusiveExhaustiveAffine k φ n).magnitude P = 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [exclusiveExhaustiveAffine, AffineCombination.magnitude, List.map_map,
    Function.comp_def, EF.denote_const]
  let q : ℚ := 1 / (k : ℚ)
  change (List.map (Function.const ℕ |(q : ℝ)|) (List.range k)).sum = 1
  rw [List.map_const, List.length_range, List.sum_replicate, nsmul_eq_mul]
  dsimp only [q]
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [abs_of_pos (one_div_pos.mpr hkR)]
  field_simp

/-- **Learning Exclusive–Exhaustive Relationships** (`thm:lex`).  The semantic premise is
the completed-theory rendering of the paper's statement that `Theory` proves exactly one
member of each fixed finite tuple.
Paper node: `thm:lex` -/
theorem lic_learning_exclusive_exhaustive
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (k : ℕ) (hk : 0 < k) (φ : ℕ → ℕ → Sentence)
    (hφ : ∀ j < k, BigSentenceCodes (φ j))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hexclusiveExhaustive : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      ((List.range k).map (fun j => v.payout (φ j n))).sum = 1) :
    (fun n => ((List.range k).map (fun j => P n (φ j n))).sum) ≈ₙ fun _ => 1 := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  let As := exclusiveExhaustiveAffine k φ
  have hpoly := exclusiveExhaustive_polySequence k hk φ hφ
  have hmag : ∀ n, (As n).magnitude P ≤ 1 := fun n => by
    simp only [As]
    rw [exclusiveExhaustiveAffine_magnitude k hk φ P n]
  have hbcs : AffineCombination.BoundedCombinationSequence As P := {
    poly := hpoly
    bounded := ⟨1 + 1 / (k : ℝ), fun n => by
      rw [AffineCombination.l1Norm]
      rw [show (As n).magnitude P = 1 by
        exact exclusiveExhaustiveAffine_magnitude k hk φ P n]
      dsimp only [As, exclusiveExhaustiveAffine]
      simp only [EF.denote_const]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      push_cast
      rw [abs_neg, abs_of_pos (one_div_pos.mpr hkR)]
      exact le_of_eq (add_comm _ _)⟩
  }
  have hzero := hpoly.affine_provind_theory_eq P DP
    (hbcs.boundedPrices hP) ⟨1, hmag⟩ hworld 0 (fun n v hv => by
      rw [show (As n).value P v.payout =
          (((List.range k).map (fun j => v.payout (φ j n))).sum - 1) / k by
        change (exclusiveExhaustiveAffine k φ n).value P v.payout = _
        simp only [exclusiveExhaustiveAffine, AffineCombination.value, EF.denote_const,
          List.map_map]
        simp only [Function.comp_def, EF.denote_const]
        rw [List.sum_map_mul_left]
        push_cast
        ring]
      rw [hexclusiveExhaustive n v hv]
      simp)
  unfold As at hzero
  simp only [exclusiveExhaustiveAffine_price k hk φ P] at hzero
  unfold AsympEq at hzero ⊢
  convert hzero.const_mul (k : ℝ) using 1
  · funext n
    simp only []
    field_simp
    ring
  · simp

end LogicalInduction
