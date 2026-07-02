/-
# Part II — Shared engines (`LogicalInduction.Engine`)

The workhorses every property proof routes through. Build the ROI bound before any
property. Nodes hosted here (see roadmap §3, Part II):

* `def:roi` / `app:roi` → `ReturnOnInvestment`, `roi_bound` — bounds a trader's return;
  nearly every property proof routes through it.
* `def:tradermag` → `Trader.magnitude` — used by ROI and budgeting.
* `def:emulatabletraders` → `EmulatableTraders` — the concrete clocked enumeration shape
  (`dd:abstract`).
* `thm:affpolymax` / `app:affpolymax` → `affine_preemptive_learning` — the **affine
  master theorem**; one of the two "lift" hubs.
* `lem:conluvapprox`, `lem:mesh`, `lem:limexpapprox` → `LUV.*_approx` — the **expectation
  bridge** that lifts probability results to expectation results; the second "lift" hub.

TODO(blueprint:def:roi): `ReturnOnInvestment` and `roi_bound`.
-/

namespace LogicalInduction

end LogicalInduction
