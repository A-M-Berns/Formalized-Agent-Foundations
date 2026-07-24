import LogicalInduction.Construction.TradingFirm

/-!
# The logical-induction algorithm

This file closes the semantic fixed-point loop in the paper's construction.  On day `n`,
the recursively generated market presents its finite rational prefix to `TradingFirm` and
asks `MarketMaker` for the next rational belief state.  The prefix-invariance theorem for
the firm then identifies this adaptive realization with the static firm used by the
dominance theorem.
-/

namespace LogicalInduction

/-- The recursive rational states of the logical-induction algorithm. -/
noncomputable def liaStates (DP : DeductiveProcess) : ℕ → RationalBeliefState
  | n =>
      let past := List.ofFn fun i : Fin n => liaStates DP i
      MarketMaker ((TradingFirm DP).action n past) past
        (marketMakerError n) (marketMakerError_pos n)
termination_by n => n
decreasing_by exact i.isLt

/-- The exact rational quote table produced by `liaStates`. -/
noncomputable def liaQuote (DP : DeductiveProcess) : ℕ → Sentence → ℚ :=
  fun n => (liaStates DP n).quote

/-- The real-valued history obtained by casting the exact rational quotes. -/
noncomputable def liaHistory (DP : DeductiveProcess) : History :=
  fun n => (liaStates DP n).toValuation

/-- The ordinary trader obtained by running the adaptive firm against the actual LIA
prefix.  This is the trader faced by the recursive MarketMaker construction. -/
noncomputable def liaTrader (DP : DeductiveProcess) : Trader where
  strat n := (TradingFirm DP).action n
    (List.ofFn fun i : Fin n => liaStates DP i)

lemma rationalHistory_liaPast (DP : DeductiveProcess) {n day : ℕ}
    (hday : day < n) (phi : Sentence) :
    rationalHistory (List.ofFn fun i : Fin n => liaStates DP i) day phi =
      liaQuote DP day phi := by
  simp [rationalHistory, liaQuote, hday]

/-- The recursively defined LIA states are exactly the generic MarketMaker recursion for
the realized firm. -/
lemma liaStates_eq_marketMakerStates (DP : DeductiveProcess) (n : ℕ) :
    liaStates DP n = marketMakerStates (liaTrader DP) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpast :
          (List.ofFn fun i : Fin n => liaStates DP i) =
            List.ofFn fun i : Fin n => marketMakerStates (liaTrader DP) i := by
        apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [List.getElem_ofFn]
          exact ih i (by simpa using hi₁)
      rw [liaStates, marketMakerStates]
      change MarketMaker
          ((TradingFirm DP).action n
            (List.ofFn fun i : Fin n => liaStates DP i))
          (List.ofFn fun i : Fin n => liaStates DP i)
          (marketMakerError n) (marketMakerError_pos n) =
        MarketMaker
          ((TradingFirm DP).action n
            (List.ofFn fun i : Fin n => liaStates DP i))
          (List.ofFn fun i : Fin n => marketMakerStates (liaTrader DP) i)
          (marketMakerError n) (marketMakerError_pos n)
      rw [hpast]

lemma liaHistory_eq_marketMakerHistory (DP : DeductiveProcess) :
    liaHistory DP = marketMakerHistory (liaTrader DP) := by
  funext n phi
  rw [liaHistory, marketMakerHistory, liaStates_eq_marketMakerStates]

/-- Prefix invariance identifies the adaptive realized firm with the static complete-table
firm used by `trading_firm_dominance`. -/
lemma tradingFirmTrader_liaQuote_eq_liaTrader (DP : DeductiveProcess) :
    tradingFirmTrader DP (liaQuote DP) = liaTrader DP := by
  unfold tradingFirmTrader liaTrader
  congr 1
  funext n
  apply TradingFirmAt_eq_of_eq_prefix
  intro day hday phi
  exact (rationalHistory_liaPast DP hday phi).symm

lemma liaHistory_range (DP : DeductiveProcess) (day : ℕ) (phi : Sentence) :
    0 ≤ liaHistory DP day phi ∧ liaHistory DP day phi ≤ 1 := by
  exact (liaStates DP day).toValuation_mem_Icc phi

lemma liaHistory_eq_quote_cast (DP : DeductiveProcess) (day : ℕ)
    (phi : Sentence) :
    liaHistory DP day phi = (liaQuote DP day phi : ℝ) := rfl

/-- The realized TradingFirm cannot exploit the LIA market, by the MarketMaker lemma. -/
lemma liaTrader_not_exploited (DP : DeductiveProcess) :
    ¬ (liaTrader DP).Exploits (liaHistory DP) DP := by
  rw [liaHistory_eq_marketMakerHistory]
  exact marketMaker_not_exploited (liaTrader DP) DP

/-- Semantic logical-induction capstone: no efficiently computable trader exploits the
recursive rational market. -/
lemma lia_no_efficient_trader_exploits (DP : DeductiveProcess)
    (Tr : Trader) (hTr : EfficientlyComputableTok Tr) :
    ¬ Tr.Exploits (liaHistory DP) DP := by
  intro hEx
  have hfirm := trading_firm_dominance DP (liaHistory DP)
    (liaHistory_range DP) (liaQuote DP) (liaHistory_eq_quote_cast DP)
    Tr hTr hEx
  rw [tradingFirmTrader_liaQuote_eq_liaTrader] at hfirm
  exact liaTrader_not_exploited DP hfirm

/-- Digit-model semantic capstone: no digit-metered (`EfficientlyComputableTok₂`)
trader exploits the recursive rational market either — the firm's odd indices cover the
wider class (`trading_firm_dominance₂`), and the MarketMaker bound is class-agnostic. -/
lemma lia_no_efficient_trader_exploits₂ (DP : DeductiveProcess)
    (Tr : Trader) (hTr : EfficientlyComputableTok₂ Tr) :
    ¬ Tr.Exploits (liaHistory DP) DP := by
  intro hEx
  have hfirm := trading_firm_dominance₂ DP (liaHistory DP)
    (liaHistory_range DP) (liaQuote DP) (liaHistory_eq_quote_cast DP)
    Tr hTr hEx
  rw [tradingFirmTrader_liaQuote_eq_liaTrader] at hfirm
  exact liaTrader_not_exploited DP hfirm

/-- Assembly lemma isolating the one remaining construction obligation: once the exact
partial-recursive presentation of `liaHistory` is supplied, all semantic fields of the
logical-inductor criterion are already discharged.  This is deliberately not named the
paper-facing `LIA_is_logical_inductor`; M7 does not count the computability premise as a
solution. -/
lemma lia_isLogicalInductor_of_computableMarket (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP)
    (hmarket : ComputableMarket (liaHistory DP)) :
    IsLogicalInductor (liaHistory DP) DP where
  marketComputable := hmarket
  processComputable := hDP
  noExploit := lia_no_efficient_trader_exploits DP

/-- Digit-model assembly: the same, for the paper-faithful `IsLogicalInductor₂`. -/
lemma lia_isLogicalInductor₂_of_computableMarket (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP)
    (hmarket : ComputableMarket (liaHistory DP)) :
    IsLogicalInductor₂ (liaHistory DP) DP where
  toIsLogicalInductor := lia_isLogicalInductor_of_computableMarket DP hDP hmarket
  noExploit₂ := lia_no_efficient_trader_exploits₂ DP

#print axioms liaStates_eq_marketMakerStates
#print axioms tradingFirmTrader_liaQuote_eq_liaTrader
#print axioms liaTrader_not_exploited
#print axioms lia_no_efficient_trader_exploits
#print axioms lia_no_efficient_trader_exploits₂
#print axioms lia_isLogicalInductor_of_computableMarket
#print axioms lia_isLogicalInductor₂_of_computableMarket

end LogicalInduction
