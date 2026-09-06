import LogicalInduction.Construction.TradingFirm
import LogicalInduction.Framework.MachineEfficiency

/-!
# `def:lia` — the logical induction algorithm

This module renders the paper's algorithm `LIA` (`alg:li` / `def:lia`, tex:2649) and closes
the semantic half of the logical induction criterion (`def:lic`, tex:657) over the market
that algorithm constructs.

The recursion is the paper's own: on day `n` the already-generated rational prefix is
presented to `TradingFirm`, and `MarketMaker` returns the next rational belief state as its
fixed point against the firm's day-`n` strategy. `liaStates` is that recursion, `liaQuote`
its exact rational quote table, `liaHistory` the real-valued market it induces — the market
every `_unconditional` and `_closed` endpoint is stated over — and `liaTrader` the ordinary
trader
obtained by running the adaptive firm against the realized prefix. `liaStates` and
`liaHistory` are in `AxiomAudit.lean`'s LI-CANONICAL inventory.

The main results are `lia_no_machine_trader_exploits` — no machine-efficient trader
(`def:ec`, `MachineEfficientTrader`) exploits `liaHistory` — its corollary
`lia_no_efficient_trader_exploits` over the fuel certificates (`dd:fuel`), and the two
assembly lemmas `lia_isMachineLogicalInductor_of_computableMarket` and
`lia_isLogicalInductor_of_computableMarket`.

Two identifications carry the argument. Prefix invariance
(`tradingFirmTrader_liaQuote_eq_liaTrader`) identifies the adaptive realized firm with the
static complete-table firm that `trading_firm_dominance` quantifies over, and
`liaStates_eq_marketMakerStates` identifies this recursion with the generic MarketMaker
recursion, so `marketMaker_not_exploited` applies to it.

The assembly lemmas take a computable-market presentation as a hypothesis, which is why
they are not the paper-facing statement: assuming the market is computable is not
exhibiting the program. `Construction/LIAComputation.lean` and
`Construction/LIACompiler.lean` supply that presentation, yielding
`LIA_is_logical_inductor`.
-/

namespace LogicalInduction

/-! ## The `LIA` recursion -/

/-- The recursive rational states of the logical-induction algorithm: day `n` is the
market maker's fixed point against the trading firm run on the history of days `< n`.
This is the paper's `LIA` recursion itself.
Paper node: `def:lia` -/
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

/-- The real-valued history obtained by casting the exact rational quotes — the market
`LIA` induces, and the market every `_unconditional` and `_closed` endpoint is stated over.
Paper node: `def:lia` -/
noncomputable def liaHistory (DP : DeductiveProcess) : History :=
  fun n => (liaStates DP n).toValuation

/-- The `def:market` range clause for the constructed market: every LIA price lies in
`[0, 1]`. -/
lemma liaHistory_range (DP : DeductiveProcess) (day : ℕ) (phi : Sentence) :
    0 ≤ liaHistory DP day phi ∧ liaHistory DP day phi ≤ 1 := by
  exact (liaStates DP day).toValuation_mem_Icc phi

/-- The real market is definitionally the cast of the exact rational quote table, so
reasoning carried out in `ℚ` transfers to `liaHistory` without loss. -/
lemma liaHistory_eq_quote_cast (DP : DeductiveProcess) (day : ℕ)
    (phi : Sentence) :
    liaHistory DP day phi = (liaQuote DP day phi : ℝ) := rfl

/-- The ordinary trader obtained by running the adaptive firm against the actual LIA
prefix.  This is the trader faced by the recursive MarketMaker construction. -/
noncomputable def liaTrader (DP : DeductiveProcess) : Trader where
  strat n := (TradingFirm DP).action n
    (List.ofFn fun i : Fin n => liaStates DP i)

/-! ## Identification with the generic MarketMaker recursion -/

/-- On a day strictly inside the prefix, the rational history of the LIA prefix is the LIA
quote table itself. -/
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

/-- The market form of `liaStates_eq_marketMakerStates`. -/
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

/-! ## `def:lic` over the constructed market -/

/-- The realized TradingFirm cannot exploit the LIA market, by the MarketMaker lemma. -/
lemma liaTrader_not_exploited (DP : DeductiveProcess) :
    ¬ (liaTrader DP).Exploits (liaHistory DP) DP := by
  rw [liaHistory_eq_marketMakerHistory]
  exact marketMaker_not_exploited (liaTrader DP) DP

/-- Semantic logical-induction capstone: no **machine-efficient** trader exploits the
recursive rational market. The class is ordinary machine polynomial time, through
`Complexity.FP`.
Paper node: `def:lic` -/
lemma lia_no_machine_trader_exploits (DP : DeductiveProcess)
    (Tr : Trader) (hTr : MachineEfficientTrader Tr) :
    ¬ Tr.Exploits (liaHistory DP) DP := by
  intro hEx
  have hfirm := trading_firm_dominance DP (liaHistory DP)
    (liaHistory_range DP) (liaQuote DP) (liaHistory_eq_quote_cast DP)
    Tr hTr hEx
  rw [tradingFirmTrader_liaQuote_eq_liaTrader] at hfirm
  exact liaTrader_not_exploited DP hfirm

/-- The fuel-certified corollary: everything the fuel calculus certifies is
machine-efficient, so it cannot exploit the market either. -/
lemma lia_no_efficient_trader_exploits (DP : DeductiveProcess)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (liaHistory DP) DP :=
  lia_no_machine_trader_exploits DP Tr hTr.toMachine

/-- Assembly lemma: it separates the semantic content of the criterion from the
computable-market presentation.  Every semantic field is discharged here; the presentation
is supplied as a hypothesis, which is why this is not the paper-facing statement —
assuming the market is computable is not exhibiting the program.
`Construction/LIACompiler.lean` supplies it, giving `LIA_is_logical_inductor`. -/
lemma lia_isMachineLogicalInductor_of_computableMarket (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP)
    (hmarket : ComputableMarket (liaHistory DP)) :
    IsMachineLogicalInductor (liaHistory DP) DP where
  marketComputable := hmarket
  processComputable := hDP
  noExploit := lia_no_machine_trader_exploits DP

/-- The same assembly at the fuel-class compatibility predicate, by the bridge. -/
lemma lia_isLogicalInductor_of_computableMarket (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP)
    (hmarket : ComputableMarket (liaHistory DP)) :
    IsLogicalInductor (liaHistory DP) DP :=
  @IsMachineLogicalInductor.toIsLogicalInductor _ _
    (lia_isMachineLogicalInductor_of_computableMarket DP hDP hmarket)

end LogicalInduction
