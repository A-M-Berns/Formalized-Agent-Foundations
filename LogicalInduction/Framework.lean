/-
# Framework (`LogicalInduction.Framework`)

Everything upstream of both `Properties/` and `Construction/`: the paper's §2–3
substrate and the shared proof machinery.

* `Asymptotics`    — the single limit vocabulary (`dd:asymp`).
* `Foundations`    — language, worlds, markets, deductive processes (`def:lang`–`def:worlds`).
* `Computable`     — the fuel-clocked computability model (`def:ec`, `dd:fuel`).
* `Emission`       — bounded-simulation compilers over `Nat.Partrec.Code` and the clocked
                     token-emission layer they feed.
* `DigitArith`     — bignum arithmetic on digit streams, so emission is metered in token
                     *bits* rather than in code values (`dd:fuel`).
* `RpnSentence`    — sentences as Polish-notation symbol runs (one token per formula
                     symbol), so stream length tracks symbol count rather than code size.
* `RpnSplice`      — the symbol-metered sentence-sequence class and its combinators.
* `RpnEmission`    — realizes those sequences as emitted digit streams.
* `RpnComputation` — primitive recursion for the Polish-notation contraction, which the
                     trading firm's compiler runs to decode candidate traders.
* `Criterion`      — expressible features (`def:tf`), traders, the LI criterion (`def:lic`).
* `Compactness`    — propositional compactness over Cantor space: per-stage satisfiability
                     of a deductive process yields one world consistent with every stage.
* `Affine`         — trade magnitude/net-worth bounds and affine combinations (buy orders).
* `ROI`            — the repeatable return-on-investment lemma (`lem:type3`) and the
                     budgeted-trader machinery its proof needs.
* `Expectations`   — logically uncertain variables (`def:luv`).
* `RationalCut`    — generic bounded-cut semantics yielding completed-world LUV values.

The four `Rpn*` modules together discharge `def:ec`'s symbol-metered sentence slots.
-/
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Foundations
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.Emission
import LogicalInduction.Framework.DigitArith
import LogicalInduction.Framework.RpnSentence
import LogicalInduction.Framework.RpnSplice
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnComputation
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Compactness
import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.ROI
import LogicalInduction.Framework.Expectations
import LogicalInduction.Framework.RationalCut
import LogicalInduction.Framework.WriteOut
import LogicalInduction.Framework.Machine.WriteOutMachine
