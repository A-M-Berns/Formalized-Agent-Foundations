/-
# Framework (`LogicalInduction.Framework`)

Everything upstream of both `Properties/` and `Construction/`: the paper's §2–3
substrate and the shared proof machinery.

* `Asymptotics`  — the single limit vocabulary (`dd:asymp`).
* `Foundations`  — language, worlds, markets, deductive processes (`def:lang`–`def:worlds`).
* `Computable`   — the fuel-clocked computability model (`def:ec`, `dd:fuel`).
* `Criterion`    — expressible features (`def:tf`), traders, the LI criterion (`def:lic`).
* `Affine`       — trade magnitude/net-worth bounds and affine combinations (buy orders).
* `ROI`          — the return-on-investment lemma (App. `roi`) and the affine master theorem.
* `Expectations` — logically uncertain variables (`def:luv`).
-/
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Foundations
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.ROI
import LogicalInduction.Framework.Expectations
