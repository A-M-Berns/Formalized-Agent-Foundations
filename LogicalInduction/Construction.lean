/-
# Part IV — Construction / existence (`LogicalInduction.Construction`)

The hard core. Expect this Part to be where real time goes. Nodes hosted here (see
roadmap §3, Part IV):

* `lem:fpl` → `fixed_point_lemma` — **Brouwer.** The price-adjustment map `adj` on the
  compact convex `Valuations'` is continuous *because trading strategies are continuous*
  (what `EF.denote` continuity buys).
  ⚠ FINDING (M0): Mathlib has **no Brouwer fixed-point theorem** (only Brouwerian/Heyting
  *algebras* and Riesz–Markov–*Kakutani*, both unrelated). The roadmap's "use Mathlib's
  Brouwer" assumption is false. This Part is gated on either contributing Brouwer/Kakutani
  upstream or finding an alternate route. See `Scratchpad.lean` and `PROGRESS.md`.
* `def:markemaker` → `MarketMaker` — rational approximation to the fixed point.
* `lem:budgeter` → `Budgeter`, `budgeter_props` — caps each enumerated trader.
* `def:tradingfirm` → `TradingFirm` — combines enumerated traders with budgets.
* `def:lia` / `alg:li` → `LIA` — the concrete algorithm.
* `thm:lia` → `LIA_is_logical_inductor` — discharges `def:lic` for `LIA`.
* `thm:li`  → `exists_logical_inductor` — main existence result.

TODO(blueprint:lem:fpl): resolve the Brouwer gap before starting this Part.
-/
import LogicalInduction.Construction.Brouwer

namespace LogicalInduction

end LogicalInduction
