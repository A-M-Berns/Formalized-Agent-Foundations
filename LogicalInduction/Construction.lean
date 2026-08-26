/-
# Construction and existence (`LogicalInduction.Construction`)

The paper's §5: an explicit algorithm `LIA` together with the proof that its market
satisfies the logical-induction criterion. Paper nodes hosted here:

* `lem:fpl` → `fixed_point_lemma` — the price-adjustment map on the compact convex
  space of valuations has a fixed point; it is continuous because trading strategies
  are (what continuity of `EF.denote` buys). Mathlib has no Brouwer fixed-point
  theorem, so `Construction.Brouwer` proves the instance needed here from Sperner's
  lemma; see that file's header for its trust-surface disclosure.
* `def:markemaker` → `MarketMaker` — rational approximation to the fixed point.
* `lem:budgeter` → `Budgeter`, `budgeter_props` — caps each enumerated trader.
* `def:tradingfirm` → `TradingFirm` — combines enumerated traders with budgets.
* `def:lia` / `alg:li` → `LIA` — the concrete algorithm.
* `thm:lia` → `LIA_is_logical_inductor` — discharges `def:lic` for `LIA`.
* `thm:li`  → `exists_logical_inductor` — main existence result.

-/
import LogicalInduction.Construction.MarketMaker
import LogicalInduction.Construction.MachineTraderEnumeration
import LogicalInduction.Construction.Budgeter
import LogicalInduction.Construction.TradingFirm
import LogicalInduction.Construction.LIA
import LogicalInduction.Construction.LIAComputation
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Witnesses

namespace LogicalInduction

end LogicalInduction
