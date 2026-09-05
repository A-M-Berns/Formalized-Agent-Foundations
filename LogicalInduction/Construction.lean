import LogicalInduction.Construction.MarketMaker
import LogicalInduction.Construction.MachineTraderEnumeration
import LogicalInduction.Construction.Budgeter
import LogicalInduction.Construction.TradingFirm
import LogicalInduction.Construction.LIA
import LogicalInduction.Construction.LIAComputation
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Witnesses

/-!
# Construction and existence (`LogicalInduction.Construction`)

The paper's §5: an explicit algorithm together with the proof that its market satisfies the
logical induction criterion at the paper's own quantifier.

## The fixed point and the market maker

* `lem:fpl` → `fixed_point_lemma` (`MarketMaker.lean`) — the price-adjustment map on the
  compact convex space of valuations has a fixed point; it is continuous because trading
  strategies are (what continuity of `EF.denote` buys). Mathlib has no Brouwer fixed-point
  theorem, so `Construction.Brouwer` proves the instance needed here from Sperner's lemma;
  see that file's header for its trust-surface disclosure.
* `def:markemaker` → `MarketMaker` — rational approximation to the fixed point.

## Enumeration, budgeting and the trading firm

* `def:ec` → `MachineTraderEnumeration` — `enumeratedTrader`, sound
  (`enumeratedTrader_machineEfficient`) and covering (`exists_enumeratedTrader_eq`) for
  `MachineEfficientTrader`. This is what makes the firm dominate the paper's own class, and
  hence what makes the criterion hold at the paper's own quantifier.
* `lem:budgeter` → `Budgeter` and its three parts (`Budgeter.lean`) — caps each enumerated
  trader.
* `eq:tradingfirm` / `lem:tfdom` → `TradingFirm` — combines enumerated traders with budgets,
  and carries the dominance lemma (`trading_firm_dominance`, `trading_firm_dominance_of_ec`)
  over the enumeration above.

## The algorithm and the existence theorems

* `def:lia` / `alg:li` → `liaStates`, `liaHistory` (`LIA.lean`, with `liaQuote` and
  `liaTrader` beside them) — the concrete algorithm and the market it induces.
  `LIAComputation` and `LIACompiler` carry its bounded-evaluation and compilation layers.
* `thm:lia` → `LIA_isMachineLogicalInductor` — discharges `def:lic` at the paper's own
  quantifier; `LIA_is_logical_inductor` is its fuel-class form, which is what the §4
  property tail consumes.
* `thm:li` → `exists_machine_logical_inductor`, with
  `exists_computable_beliefSequence_logical_inductor` the full belief-sequence form the
  paper states (`def:belseq`); `exists_logical_inductor` is the fuel-class projection.

`Construction/Witnesses/` holds the representation machinery that discharges the property
tail's interfaces over the constructed inductor. Nothing in the §5 existence proof imports
it.
-/
