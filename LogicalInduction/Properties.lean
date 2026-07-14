/-
# Part III — Property tail (`LogicalInduction.Properties`) — roll-up

Every property here is conditioned on `[IsLogicalInductor P DP]` and proved via the
assume-fail → build-trader → certify-e.c. → invoke-criterion pattern, with the exploiting
trader *genuinely constructed* and its efficient computability *discharged through the clocked
interpreter* (`dd:fuel`). No arithmetic stub ever stands in for an exploit.

File layout (promoted from a single file once it grew past ~1000 lines):

* `Properties.Basic` — shared substrate: `PCWorld` boolean/payout lemmas and the two
  exploitation engines (`exploits_of_nonneg_partialSums` world-neutral;
  `exploits_of_ge_partialSums` world-dependent).
* `Properties.ProvabilityInduction` — `thm:provind`: `buyDaily` (fixed φ, base + limiting form)
  and `buySeq` (`𝓔𝓒`-sequence form).
* `Properties.Coherence` — `thm:lc`: bullet 2 (disprovable → 0, `sellDaily`) and bullet 3
  (finite additivity + the limit identity, world-neutral portfolio `exclTr`).
* `Properties.Convergence` — `thm:con`: the non-convergence ⇒ rational-oscillation reduction,
  and `oscillation_exploitable`, discharged by the hysteresis trader.
* `Properties.Hysteresis` — the `thm:con` arbitrage core: the size-`Θ(n)` hysteresis
  holdings state, the sign-decomposition accounting, and its five-segment e.c. emission.
* `Properties.NonDogmatism` — `thm:nd`: the weak fragment (`ndTrader`, the first Phase-A
  block-emission trader) and the full theorem, both directions (the `app:obu` scale
  ladders `ndLadderTrader`/`ndSellLadderTrader`) plus the `P∞` limit forms.
* `Properties.ExpectationConvergence` — `thm:ec`: the feature-generic hysteresis layer
  (`buyIndF`/`sellIndF`/`hystChain`) and the bundle trader `excTrader` on the
  expectation feature `𝔼(X)`, gated to absorb the `lem:conluvapprox` payout error.
* `Properties.Relationships` — `thm:lex`: learning logical equivalence (`eqTr`) and implication
  / price monotonicity (`impTr`).
* `Properties.AffinePreemptiveLearning` — `thm:affpolymax`'s exact liminf/limsup analytic
  hub, factored over the two operational no-preemptive-gap conditions supplied by ROI.
* `Properties.AffineProvability` / `Properties.ExpectationAffine` — the semantic affine
  lower-bound theorem and the proved `thm:ei`/`loe`/`expprovind` LUV lift.
* `Properties.SelfTrust` — `thm:cee`/`ceu`/`ccee`/`st` statement surface:
  reflection as revelation-schedule linkage hypotheses over relational quoted families
  (under audit after the M4 lift exposed a missing cross-grid quote interface);
  `DeferralFunction` (`def:deferralfunc`).

See `PROGRESS.md` for the per-node ledger (label → decl → status → kind → provenance).
-/
import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.ProvabilityInduction
import LogicalInduction.Properties.Coherence
import LogicalInduction.Properties.Convergence
import LogicalInduction.Properties.Hysteresis
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Properties.Relationships
import LogicalInduction.Properties.AffineProvability
import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.AffinePreemptiveLearning
