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
  and the arbitrage-trader interface (`oscillation_exploitable`, the deferred hysteresis core).
* `Properties.NonDogmatism` — `thm:nd` (weak fragment): the price of a never-refuted `φ`
  eventually clears `2^{-(n+2)}` (`ndTrader`, the first Phase-A block-emission trader).
* `Properties.Relationships` — `thm:lex`: learning logical equivalence (`eqTr`) and implication
  / price monotonicity (`impTr`).

See `PROGRESS.md` for the per-node ledger (label → decl → status → kind → provenance).
-/
import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.ProvabilityInduction
import LogicalInduction.Properties.Coherence
import LogicalInduction.Properties.Convergence
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.Relationships
