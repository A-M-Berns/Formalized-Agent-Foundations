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
* `Properties.Coherence` (§4.1, includes former `Convergence`) — `thm:con`: the non-convergence ⇒ rational-oscillation reduction,
  and `oscillation_exploitable`, discharged by the hysteresis trader.
* `Properties.Hysteresis` — the `thm:con` arbitrage core: the size-`Θ(n)` hysteresis
  holdings state, the sign-decomposition accounting, and its five-segment e.c. emission.
* `Properties.NonDogmatism` — `thm:nd`: the weak fragment (`ndTrader`, the first Phase-A
  block-emission trader) and the full theorem, both directions (the `app:obu` scale
  ladders `ndLadderTrader`/`ndSellLadderTrader`) plus the `P∞` limit forms.
* `Properties.UniformNonDogmatism` — `thm:obu`: the varying-sentence scale ladder,
  non-vacuous joint-consistency exploitation proof, polynomial token emitter, and exact
  common positive `P∞` bound over an explicit efficient-repetition preprocessing witness.
* `Properties.OccamBounds` — `thm:ob`: the Kraft-weighted sentence/rung ladder, literal
  triangular token emitter, global summable-risk floor, unbounded possible-world upside,
  and the exact common lower/upper `P∞` bounds through a fixed negation compiler overhead.
* `Properties.UniversalSemimeasure` — faithful continuous/lower-semicomputable/universal
  semimeasure and independent bit-prefix syntax for `thm:dus`, plus the finite-tree
  `MeanPayout ≤ MaxPayout` analytic core and the direct unit-budget scale trader with
  maximizing-world extraction, the summable scale diagonal and its literal token emitter,
  global downside/unbounded-upside proof, and the exact fixed-constant capstone.
* `Properties.UniversalSemimeasure` (includes former `StrictSemimeasure`) — `thm:strict` from Uniform Non-Dogmatism and the
  explicit recursively-inseparable null-prefix-class representation boundary.
* `Properties.Conditioning` — exact capped conditional markets, a direct finite-zero
  prefix repair on the original market, and stagewise combined deductive-process semantics
  for the fixed and growing-prefix forms of `thm:scon`.
* `Properties.ExpectationConvergence` — `thm:ec`: the day-`n` expectation is the price of
  the precision-`n` threshold bundle, so `thm:affcoh` traps it between the limiting
  belief's liminf/limsup, `thm:lc` averages that belief over completed-theory worlds, and
  `lem:conluvapprox` makes the precision sequence Cauchy.
* `Properties.Relationships` — `thm:lex`: the paper's finite exclusive/exhaustive family
  theorem, plus fixed-equivalence (`eqTr`) and implication/price-monotonicity (`impTr`)
  consequences.
* `Properties.LimitCoherence` — `thm:lc`: the Gaifman conditions for limiting beliefs,
  completed-theory theorem/refutation limits, and the countably additive probability measure
  on `PCWorld` concentrated on worlds consistent with the completed deductive process.
* `Properties.FinitePerturbations` — `thm:ifp`: the literal old-price syntax freeze,
  finite net-worth error accounting, exploitation transport, and exact conditional
  logical-inductor biconditional over the disclosed efficient-prefix compiler boundary.
* `Properties.AffinePreemptiveLearning` — `thm:affpolymax`'s exact liminf/limsup analytic
  hub, factored over the two operational no-preemptive-gap conditions supplied by ROI.
* `Properties.AffineProvability` / `Properties.ExpectationAffine` — the semantic affine
  lower-bound theorem and the proved `thm:ei`/`loe`/`expprovind` LUV lift.
* `Properties.ExpectationProperties` — concrete LUV-combination threshold meshes,
  completed-world approximation, and the collected expectation-property lifts.
* `Properties.Calibration` — generated divergent weightings, normalized bias/limit-point
  analysis, and the capped affine run family for recurring unbiasedness.
* `Properties.Pseudorandomness` — exact deferral-patient weighting vocabulary, the
  explicit Kelly feedback trader/economic kernel and conditional `thm:wubaff`/`thm:wub`
  capstones, the polynomial patient-capacity selector, and all three conditional `thm:prandaff` comparison
  directions, plus the exact varied-frequency `thm:prand` specialization and arbitrary-
  real-frequency rational squeeze for `thm:benford`.
* `Properties.MetaLearning` — the `pac`/`pazfc`/`incons` and
  `halts`/`loops`/`dontwait` consequences over explicit computation-representation
  interfaces, all reduced to completed-theory Provability Induction.
* `Properties.Introspection` — exact interval introspection (`ref`), paradox resistance
  (`lp`), and same-day quoted-price/quoted-expectation identities (`epr`/`er`) through
  concrete completed-theory affine quote portfolios.
* `Properties.SelfTrust` — proved `thm:cee`/`ceu`/`ccee`/`st`, over theorem-specific
  quote certificates bundling delayed revelation semantics with the fixed-portfolio
  cross-grid law; `DeferralFunction` (`def:deferralfunc`).

See `notes/logical-induction-roadmap.md` for the paper-node map and
`notes/next-session.md` for the construction record.
-/
import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.ProvabilityInduction
import LogicalInduction.Properties.Coherence
import LogicalInduction.Properties.Hysteresis
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.UniformNonDogmatism
import LogicalInduction.Properties.OccamBounds
import LogicalInduction.Properties.UniversalSemimeasure
import LogicalInduction.Properties.Conditioning
import LogicalInduction.Properties.Relationships
import LogicalInduction.Properties.LimitCoherence
import LogicalInduction.Properties.FinitePerturbations
import LogicalInduction.Properties.AffineProvability
import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Properties.ExpectationProperties
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.AffinePreemptiveLearning
import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.Calibration
import LogicalInduction.Properties.Pseudorandomness
import LogicalInduction.Properties.MetaLearning
import LogicalInduction.Properties.Introspection
