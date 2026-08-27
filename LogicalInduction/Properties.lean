/-
# §4 — Properties of logical inductors

Every theorem in this directory is conditioned on `[IsLogicalInductor P DP]` and proved by
the paper's pattern: assume the property fails, construct a trader that exploits `P` under
that assumption, certify the trader efficiently computable, and invoke the criterion. The
exploiting trader is always constructed, and its efficient computability always discharged
through the clocked interpreter (`dd:fuel`).

Modules, by the paper subsection they render:

* `Properties.Basic` — shared substrate, not a paper node: `PCWorld` boolean/payout lemmas
  and the two exploitation engines (`exploits_of_nonneg_partialSums`, world-neutral;
  `exploits_of_ge_partialSums`, world-dependent).

§4.1 Convergence and Coherence
* `Properties.Coherence` — `thm:con` (non-convergence ⇒ rational oscillation ⇒ exploit) and
  `thm:lc` bullets 2 and 3 (disprovable ⇒ price → 0; finite additivity).
* `Properties.Hysteresis` — the `thm:con` arbitrage trader: buy-low/sell-high holdings
  state, its net-worth accounting, and its efficient-computability certificate.
* `Properties.LimitCoherence` — `thm:lc`: the Gaifman conditions on the limiting belief and
  the countably additive probability measure on `PCWorld` it induces.

§4.2 Timely Learning
* `Properties.ProvabilityInduction` — `thm:provind`, for a fixed sentence and for an
  efficiently computable sentence sequence.
* `Properties.TimelyLearning` — `thm:perkno` (persistence of knowledge) and `thm:tbo`
  (preemptive learning).

§4.3 Calibration and Unbiasedness
* `Properties.Calibration` — `thm:simcal` (recurring calibration) and
  `thm:recurringunbiasedness`, over divergent weightings (`def:fuz`).

§4.4 Learning Statistical Patterns
* `Properties.Pseudorandomness` — `thm:wubaff`/`thm:wub` (unbiasedness from feedback),
  `thm:prandaff`, and the pseudorandom-frequency theorems `thm:prand`/`thm:benford`.

§4.5 Learning Logical Relationships
* `Properties.Relationships` — `thm:lex` (exclusive-exhaustive families), plus the
  equivalence and implication consequences.
* `Properties.AffineProvability` — `thm:affprovind`, from a semantic affine lower bound.
* `Properties.AffineCoherence` — `thm:affcoh`.
* `Properties.AffinePersistence` — `thm:peraffkno`.
* `Properties.AffinePreemptiveLearning` — `thm:affpolymax`, factored over the two
  no-preemptive-gap conditions supplied by the return-on-investment machinery.

§4.6 Non-Dogmatism
* `Properties.FinitePerturbations` — `thm:ifp` (closure under finite perturbations).
* `Properties.FinitePerturbationCounterexample` — the refutation of the *unrestricted*
  `thm:ifp`, modulo its advice construction.  Refutes a paper statement rather than
  rendering one, so it carries no `Paper node:` annotation.
* `Properties.NonDogmatism` — `thm:nd`, both directions, in finite-stage and limit form.
* `Properties.UniformNonDogmatism` — `thm:obu`.
* `Properties.OccamBounds` — `thm:ob`, over a Kraft-weighted sentence ladder.
* `Properties.UniversalSemimeasure` — `thm:dus` (domination of the universal semimeasure)
  and `thm:strict` (strict domination).

§4.7 Conditionals
* `Properties.Conditioning` — `thm:scon`, in the fixed-prefix and growing-prefix forms.

§4.8 Expectations
* `Properties.ExpectationConvergence` — `thm:ec`: the day-`n` expectation is the price of
  the precision-`n` threshold bundle, trapped by `thm:affcoh` and made Cauchy by
  `lem:conluvapprox`.
* `Properties.ExpectationAffine` — `thm:ei`, `thm:loe`, `thm:expprovind`.
* `Properties.ExpectationProperties` — LUV-combination threshold meshes,
  completed-world approximation, and the collected expectation-property lifts.

§4.9–4.10 Trust in Consistency, Reasoning about Halting
* `Properties.MetaLearning` — `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`,
  `thm:loops`, `thm:dontwait`, all reduced to completed-theory Provability Induction.

§4.11 Introspection
* `Properties.Introspection` — `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`.

§4.12 Self-Trust
* `Properties.SelfTrust` — `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`, and the deferral
  functions (`def:deferralfunc`) they quantify over.
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
