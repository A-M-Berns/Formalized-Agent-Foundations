/-
# Part IV — Construction / existence (`LogicalInduction.Construction`)

The hard core. Expect this Part to be where real time goes. Nodes hosted here (see
roadmap §3, Part IV):

* `lem:fpl` → `fixed_point_lemma` — **Brouwer.** The price-adjustment map `adj` on the
  compact convex `Valuations'` is continuous *because trading strategies are continuous*
  (what `EF.denote` continuity buys).
  ⚠ FINDING (M0): Mathlib has **no Brouwer fixed-point theorem** (only Brouwerian/Heyting
  *algebras* and Riesz–Markov–*Kakutani*, both unrelated). The missing theorem has since
  been proved in-project via Sperner's lemma; `Construction.Brouwer` is the completed M6
  gate. See `PROGRESS.md` for its trust-surface disclosure.
* `def:markemaker` → `MarketMaker` — rational approximation to the fixed point.
* `lem:budgeter` → `Budgeter`, `budgeter_props` — caps each enumerated trader.
* `def:tradingfirm` → `TradingFirm` — combines enumerated traders with budgets.
* `def:lia` / `alg:li` → `LIA` — the concrete algorithm.
* `thm:lia` → `LIA_is_logical_inductor` — discharges `def:lic` for `LIA`.
* `thm:li`  → `exists_logical_inductor` — main existence result.

-/
import LogicalInduction.Construction.Brouwer

namespace LogicalInduction

end LogicalInduction
