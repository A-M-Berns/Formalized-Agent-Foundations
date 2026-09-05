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
import LogicalInduction.Properties.FinitePerturbationCounterexample
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

/-!
# §4 — Properties of logical inductors

The paper's §4 property tail, one module per theorem family, in the paper's own subsection
order.

## The proof pattern and the criterion hypothesis

The dominant pattern is the paper's: assume the property fails, construct a trader that
exploits `P` under that assumption, certify the trader efficiently computable through the
clocked interpreter (`dd:fuel`), and invoke the criterion. The `lic_*` consequences take
`[IsLogicalInductor P DP]`, so `IsMachineLogicalInductor.toIsLogicalInductor` makes every
one of them available at the machine class.

Three groups of results are stated differently, for one reason each:

* A theorem whose *conclusion* is the criterion cannot use that instance and is stated at
  `[IsMachineLogicalInductor P DP]` directly — `Properties.Conditioning`'s `*_machine`
  forms, and `Properties.FinitePerturbations`' `machine_lic_iff_of_finiteSupportPerturbation`.
* `Properties.FinitePerturbationCounterexample` refutes a printed statement rather than
  rendering one, so it carries no provenance annotation of its own.
* `Properties.LimitCoherence`'s Gaifman-measure results and the conditioning transduction
  are analytic rather than trader constructions.

`Properties.Basic` is shared substrate rather than a paper node: the `PCWorld` boolean and
payout lemmas, the ε-gated buy indicator, and the three exploitation engines
(`exploits_of_ge_partialSums`, world-dependent; `exploits_of_nonneg_partialSums`, its
world-neutral specialization; `exploits_of_bddBelow_of_unbounded`, the definitional route).

## §4.1–4.2 Convergence, coherence, timely learning

* `Properties.Coherence` — `thm:con` (non-convergence ⇒ rational oscillation ⇒ exploit) and
  `thm:lc` bullets 2 and 3 (disprovable ⇒ price → 0; finite additivity).
* `Properties.Hysteresis` — the `thm:con` arbitrage trader: buy-low/sell-high holdings
  state, the latched `armChain`, its net-worth accounting, and its efficient-computability
  certificate.
* `Properties.LimitCoherence` — `thm:lc`: the Gaifman conditions on the limiting belief and
  the countably additive probability measure on `PCWorld` it induces.
* `Properties.ProvabilityInduction` — `thm:provind`, for a fixed sentence and for an
  efficiently computable sentence sequence.
* `Properties.TimelyLearning` — `thm:perkno` (persistence of knowledge) and `thm:tbo`
  (preemptive learning).

## §4.3–4.5 Calibration, statistical patterns, logical relationships

* `Properties.Calibration` — `thm:simcal` (recurring calibration) and
  `thm:recurringunbiasedness`, over divergent weightings (`def:fuz`), in the forms
  conditional on a historical maturity verifier; the unconditional endpoints are proved in
  `Construction/Witnesses/HistoricalMaturity.lean`.
* `Properties.Pseudorandomness` — `thm:wubaff`/`thm:wub` (unbiasedness from feedback),
  `thm:prandaff`, and the pseudorandom-frequency theorems `thm:prand`/`thm:benford`.
* `Properties.Relationships` — `thm:lex` (exclusive-exhaustive families), plus the
  equivalence and implication consequences.
* `Properties.AffineProvability` — the semantic affine lower bound `affine_provind` that
  `thm:affprovind` runs on; the node's endpoints are in `Properties.AffineCoherence`.
* `Properties.AffineCoherence` — `thm:affcoh`, and the `thm:provind` forms that factor
  through it, including `lic_provind` itself.
* `Properties.AffinePersistence` — `thm:peraffkno`.
* `Properties.AffinePreemptiveLearning` — `thm:affpolymax`, factored over the two
  no-preemptive-gap conditions supplied by the return-on-investment machinery.

## §4.6–4.8 Non-dogmatism, conditionals, expectations

* `Properties.FinitePerturbations` — `thm:ifp` (closure under finite perturbations).
* `Properties.FinitePerturbationCounterexample` — the refutation of the *unrestricted*
  `thm:ifp`, modulo its advice construction.
* `Properties.NonDogmatism` — `thm:nd`, both directions, in finite-stage and limit form.
* `Properties.UniformNonDogmatism` — `thm:obu`.
* `Properties.OccamBounds` — `thm:ob`, over a Kraft-weighted sentence ladder.
* `Properties.UniversalSemimeasure` — `thm:dus` (domination of the universal semimeasure)
  and `thm:strict` (strict domination).
* `Properties.Conditioning` — `thm:scon`, in the fixed-prefix, gated and growing-prefix
  forms, at both classes; the `*_machine` forms are canonical, and neither set follows from
  the other.
* `Properties.ExpectationConvergence` — `thm:ec`: the day-`n` expectation is the price of
  the precision-`n` threshold bundle, trapped by `thm:affcoh` and made Cauchy by
  `lem:conluvapprox`.
* `Properties.ExpectationAffine` — `thm:ei`, `thm:loe`, `thm:expprovind`.
* `Properties.ExpectationProperties` — LUV-combination threshold meshes,
  completed-world approximation, and the collected expectation-property lifts.

## §4.9–4.12 Trust, introspection, self-trust

* `Properties.MetaLearning` — `thm:pac`, `thm:incons`, `thm:halts`, `thm:loops`,
  `thm:dontwait`, all reduced to completed-theory Provability Induction, together with the
  representation interfaces the `thm:pazfc` lane consumes; that node's endpoint is
  `lic_belief_stronger_theory_consistency_unconditional` in
  `Construction/Witnesses/ComputationRepresented.lean`.
* `Properties.Introspection` — `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`.
* `Properties.SelfTrust` — `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`, and the deferral
  functions (`def:deferralfunc`) they quantify over.
-/
