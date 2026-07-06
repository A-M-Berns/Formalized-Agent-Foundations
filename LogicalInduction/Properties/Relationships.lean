/-
# `thm:lex` — learning logical relationships (equivalence, implication)
-/
import LogicalInduction.Properties.Basic

namespace LogicalInduction

open Filter Topology


/-! ## `thm:lex` — learning logical equivalence

If `⊢ φ ↔ ψ` then the prices track each other: `Pₙφ − Pₙψ → 0`. Structurally this is the
additivity result with a *two*-sentence world-neutral portfolio `σ·[(1,φ),(-1,ψ)]` — by
equivalence the payouts are equal (`payout_eq_of_iff`), so the day value is the deterministic
difference `σ·(Pφ−Pψ)`, and the same buy-signal + reusable exploitation engine apply. -/

/-- If both `∼φ⋎ψ` and `∼ψ⋎φ` hold (i.e. `φ ↔ ψ`), the payouts coincide. -/
theorem PCWorld.payout_eq_of_iff (v : PCWorld) (φ ψ : Sentence)
    (h1 : v.Holds (∼φ ⋎ ψ)) (h2 : v.Holds (∼ψ ⋎ φ)) : v.payout φ = v.payout ψ := by
  rw [PCWorld.holds_or, PCWorld.holds_neg] at h1 h2
  simp only [PCWorld.payout]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;>
    simp_all [hφ, hψ]


/-- Price difference `Pₙφ − Pₙψ` as an `EF`. -/
noncomputable def gap2EF (φ ψ : Sentence) (n : ℕ) : EF :=
  .add (.price φ n) (.mul (.const (-1)) (.price ψ n))


noncomputable def sig2EF (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : EF :=
  .max (.const 0) (.add (.mul (.const σ) (gap2EF φ ψ n)) (.const (-ε/2)))


theorem gap2EF_denote (φ ψ : Sentence) (P : History) (n : ℕ) :
    (gap2EF φ ψ n).denote P = P n φ - P n ψ := by
  simp only [gap2EF, EF.denote_add, EF.denote_mul, EF.denote_const, EF.denote_price,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring


theorem sig2EF_denote (φ ψ : Sentence) (σ ε : ℚ) (P : History) (n : ℕ) :
    (sig2EF φ ψ σ ε n).denote P = max 0 ((σ:ℝ) * (gap2EF φ ψ n).denote P + (-(ε:ℝ)/2)) := by
  simp only [sig2EF, EF.denote_max, EF.denote_add, EF.denote_mul, EF.denote_const,
    Pi.add_apply, Pi.mul_apply]; push_cast; ring_nf


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


noncomputable def eqW (P : History) (φ ψ : Sentence) (σ ε : ℚ) (n : ℕ) : ℝ :=
  (sig2EF φ ψ σ ε n).denote P * ((σ : ℝ) * (gap2EF φ ψ n).denote P)


theorem eqTr_value (φ ψ : Sentence) (σ ε : ℚ) (P : History) (v : PCWorld) (n : ℕ)
    (h1 : v.Holds (∼φ ⋎ ψ)) (h2 : v.Holds (∼ψ ⋎ φ)) :
    ((eqTr φ ψ σ ε).strat n).value P v.payout = eqW P φ ψ σ ε n := by
  have hpay : v.payout φ = v.payout ψ := PCWorld.payout_eq_of_iff v φ ψ h1 h2
  simp only [eqTr, eqW, gap2EF, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, EF.denote_mul, EF.denote_const, EF.denote_add, EF.denote_price,
    Pi.mul_apply, Pi.add_apply]
  rw [hpay]; push_cast; ring


theorem eqW_nonneg (P : History) (φ ψ : Sentence) (σ ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    0 ≤ eqW P φ ψ σ ε n := by
  rw [eqW, sig2EF_denote]
  set G := (σ:ℝ) * (gap2EF φ ψ n).denote P with hG
  by_cases h : G + (-(ε:ℝ)/2) ≤ 0
  · rw [max_eq_left h]; simp
  · push_neg at h
    have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    exact mul_nonneg (le_max_left _ _) (by nlinarith [h, hεr])


theorem sig2EF_polyEF (φ ψ : Sentence) (σ ε : ℚ) : PolyEF (sig2EF φ ψ σ ε) := by
  have hgap : PolyEF (gap2EF φ ψ) :=
    (PolyEF.price φ).add ((PolyEF.const (-1)).mul (PolyEF.price ψ))
  exact (PolyEF.const 0).max (((PolyEF.const σ).mul hgap).add (PolyEF.const (-ε/2)))


theorem eqTr_ec (φ ψ : Sentence) (σ ε : ℚ) : EfficientlyComputable (eqTr φ ψ σ ε) := by
  obtain ⟨_, h1⟩ := (sig2EF_polyEF φ ψ σ ε).mul (PolyEF.const (-σ))
  obtain ⟨_, h2⟩ := (sig2EF_polyEF φ ψ σ ε).mul (PolyEF.const σ)
  have e1 := h1.pair (PolyFueled.const (Encodable.encode φ))
  have e2 := h2.pair (PolyFueled.const (Encodable.encode ψ))
  have l1 := ((e1.pair ((e2.pair (PolyFueled.const 0)).succ_comp)).succ_comp)
  have heq : (fun n => Nat.pair (Nat.pair (EF.mul (sig2EF φ ψ σ ε n) (EF.const (-σ))).toNat
      (Encodable.encode φ))
      (Nat.pair (Nat.pair (EF.mul (sig2EF φ ψ σ ε n) (EF.const σ)).toNat (Encodable.encode ψ))
        0 + 1) + 1)
      = (fun n => Encodable.encode ((eqTr φ ψ σ ε).strat n).trades) := by funext n; rfl
  rw [heq] at l1
  exact EfficientlyComputable.of_polyFueled l1


theorem eqTr_exploits (P : History) (DP : DeductiveProcess) (φ ψ : Sentence) (σ ε : ℚ)
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


/-- **Learning of logical equivalence** (`thm:lex`, finite-stage form): if `⊢ φ ↔ ψ` (both
implications revealed by the deductive process), the price difference `Pₙφ − Pₙψ → 0` under a
logical inductor. World-neutral 2-sentence portfolio (payouts equal by equivalence). -/
theorem lic_lex_tendsto_zero (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (himp1 : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n)
    (himp2 : ∀ n, (∼ψ ⋎ φ) ∈ DP.D n) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n φ - P n ψ) 0 := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  have h1 : ∀ᶠ n in atTop, (gap2EF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    exact hLI.noExploit _ (eqTr_ec φ ψ 1 q)
      (eqTr_exploits P DP φ ψ 1 q hq0' himp1 himp2 hcons (by simpa using hc))
  have h2 : ∀ᶠ n in atTop, -(q:ℝ) < (gap2EF φ ψ n).denote P := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploit _ (eqTr_ec φ ψ (-1) q)
      (eqTr_exploits P DP φ ψ (-1) q hq0' himp1 himp2 hcons ?_)
    refine hc.mono (fun n hn => ?_); push_cast; nlinarith [hn]
  have hfin : ∀ᶠ n in atTop, dist (P n φ - P n ψ) 0 < ε := by
    filter_upwards [h1, h2] with n hn1 hn2
    rw [Real.dist_eq, ← gap2EF_denote φ ψ P n, abs_lt]; constructor <;> linarith
  exact eventually_atTop.mp hfin


/-- `∼φ⋎ψ` (i.e. `φ→ψ`) makes `φ`'s payout `≤ ψ`'s. -/
theorem PCWorld.payout_le_of_imp (v : PCWorld) (φ ψ : Sentence)
    (h : v.Holds (∼φ ⋎ ψ)) : v.payout φ ≤ v.payout ψ := by
  rw [PCWorld.holds_or, PCWorld.holds_neg] at h
  simp only [PCWorld.payout]
  by_cases hφ : v.Holds φ <;> by_cases hψ : v.Holds ψ <;> simp_all


/-- Buy-signal for the implication trader: `max(0, (Pφ−Pψ) − ε/2)`. -/
noncomputable def impSig (φ ψ : Sentence) (ε : ℚ) (n : ℕ) : EF :=
  .max (.const 0) (.add (gap2EF φ ψ n) (.const (-ε/2)))


theorem impSig_denote (φ ψ : Sentence) (ε : ℚ) (P : History) (n : ℕ) :
    (impSig φ ψ ε n).denote P = max 0 ((gap2EF φ ψ n).denote P + (-(ε:ℝ)/2)) := by
  simp only [impSig, EF.denote_max, EF.denote_add, EF.denote_const, Pi.add_apply]; push_cast; ring_nf


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


theorem impTr_value_ge (φ ψ : Sentence) (ε : ℚ) (P : History) (v : PCWorld) (n : ℕ)
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


theorem impW_nonneg (P : History) (φ ψ : Sentence) (ε : ℚ) (hε : 0 < ε) (n : ℕ) :
    0 ≤ impW P φ ψ ε n := by
  rw [impW, impSig_denote]
  set G := (gap2EF φ ψ n).denote P
  by_cases h : G + (-(ε:ℝ)/2) ≤ 0
  · rw [max_eq_left h]; simp
  · push_neg at h
    have hεr : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    exact mul_nonneg (le_max_left _ _) (by nlinarith [h, hεr])


theorem impSig_polyEF (φ ψ : Sentence) (ε : ℚ) : PolyEF (impSig φ ψ ε) := by
  have hgap : PolyEF (gap2EF φ ψ) :=
    (PolyEF.price φ).add ((PolyEF.const (-1)).mul (PolyEF.price ψ))
  exact (PolyEF.const 0).max (hgap.add (PolyEF.const (-ε/2)))


theorem impTr_ec (φ ψ : Sentence) (ε : ℚ) : EfficientlyComputable (impTr φ ψ ε) := by
  obtain ⟨_, h1⟩ := (impSig_polyEF φ ψ ε).mul (PolyEF.const (-1))
  obtain ⟨_, h2⟩ := impSig_polyEF φ ψ ε
  have e1 := h1.pair (PolyFueled.const (Encodable.encode φ))
  have e2 := h2.pair (PolyFueled.const (Encodable.encode ψ))
  have l1 := ((e1.pair ((e2.pair (PolyFueled.const 0)).succ_comp)).succ_comp)
  have heq : (fun n => Nat.pair (Nat.pair (EF.mul (impSig φ ψ ε n) (EF.const (-1))).toNat
      (Encodable.encode φ))
      (Nat.pair (Nat.pair (impSig φ ψ ε n).toNat (Encodable.encode ψ)) 0 + 1) + 1)
      = (fun n => Encodable.encode ((impTr φ ψ ε).strat n).trades) := by funext n; rfl
  rw [heq] at l1
  exact EfficientlyComputable.of_polyFueled l1


/-- **Learning logical implication** (`thm:lex` family): if `⊢ φ → ψ` (revealed as `∼φ⋎ψ`),
then a logical inductor eventually stops overpricing `φ` relative to `ψ`: for every `ε > 0`,
eventually `Pₙφ ≤ Pₙψ + ε`. -/
theorem lic_imp_eventually_le (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ ψ : Sentence) (himp : ∀ n, (∼φ ⋎ ψ) ∈ DP.D n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, P n φ ≤ P n ψ + ε := by
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hq0' : 0 < q := by exact_mod_cast hq0
  have hmain : ∀ᶠ n in atTop, (gap2EF φ ψ n).denote P < (q:ℝ) := by
    by_contra hc; rw [not_eventually] at hc; simp only [not_lt] at hc
    refine hLI.noExploit _ (impTr_ec φ ψ q) ?_
    refine exploits_of_ge_partialSums (impTr φ ψ q) P DP (impW P φ ψ q) ((q:ℝ)^2/2)
      (by positivity) (fun i => impW_nonneg P φ ψ q hq0' i) ?_ ?_ hcons
    · intro n v hv
      simp only [Trader.netWorth]
      refine Finset.sum_le_sum (fun i _ => impTr_value_ge φ ψ q P v i (hv _ (himp n)))
    · refine hc.mono (fun n hn => ?_)
      rw [impW, impSig_denote]
      set g := (gap2EF φ ψ n).denote P with hgdef
      have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq0'
      rw [max_eq_right (by push_cast; linarith)]
      push_cast; nlinarith [hn, hqr]
  filter_upwards [hmain] with n hn
  rw [gap2EF_denote] at hn; linarith

end LogicalInduction
