import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Properties.Support.WeightedAverages
import LogicalInduction.Properties.Support.SettlementDecision
import LogicalInduction.Properties.Coherence
import LogicalInduction.Properties.LimitCoherence
import LogicalInduction.Properties.ProvabilityInduction
import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Properties.Calibration
import LogicalInduction.Properties.Pseudorandomness
import LogicalInduction.Properties.Relationships
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Properties.AffinePreemptiveLearning
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.UniformNonDogmatism
import LogicalInduction.Properties.OccamBounds
import LogicalInduction.Properties.UniversalSemimeasure
import LogicalInduction.Properties.FinitePerturbations
import LogicalInduction.Properties.FinitePerturbationCounterexample
import LogicalInduction.Properties.Conditioning
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.ExpectationProperties
import LogicalInduction.Properties.MetaLearning
import LogicalInduction.Properties.Introspection
import LogicalInduction.Properties.SelfTrust

/-!
# §4 — Properties of logical inductors (`LogicalInduction.Properties`)

The paper's §4 property tail, one module per theorem family, in the paper's own subsection
order.  Everything here is proved over an *arbitrary* logical inductor: no module in this
directory imports `LogicalInduction.Construction.*`, so `lake build
LogicalInduction.Properties` is the gate for §4 and a downstream development may assume a
logical inductor without pulling in the §5 construction.

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

## `Support/` — shared §4 proof technology, no paper node

* `Properties.Support.Exploitation` — the four routes from a net-worth bound to
  `Trader.Exploits` (`exploits_of_ge_partialSums` with its `_from` and
  `exploits_of_nonneg_partialSums` variants, and `exploits_of_bddBelow_of_unbounded`),
  together with the continuous signal
  toolkit every §4 trader is gated by: `buySignal`, the `oneMinus`/`efMin`/`clip01` blocks,
  the threshold indicators of `def:ctsind` at a price leaf and at a feature, the latched
  `armChain`, and the emission closures of all four stream classes.
* `Properties.Support.WeightedAverages` — `prefixSum`, `DivergentWeighting`,
  `weightedAverage` and `weightedBias`: the averaging vocabulary §4.3–4.4 is stated in.
* `Properties.Support.SettlementDecision` — `AffineCombination.DeterminedViaTheory` and its
  tolerance form, the decidable settlement tests `SettlementTest` / `SettlementTestBool`
  over finite Boolean worlds, and the finite exact maturity certificates
  `UnitMaturitySemanticCertificate` / `unitMaturityCheckAtFuel`.

## §4.1–4.2 Convergence, coherence, provability induction, timely learning

* `Properties.Coherence` — `thm:con` (non-convergence ⇒ rational oscillation ⇒ exploit),
  carrying the hysteresis arbitrage trader that discharges it, and `thm:lc` bullets 2 and 3
  (disprovable ⇒ price → 0; finite additivity).
* `Properties.LimitCoherence` — `thm:lc` as a whole: the Gaifman conditions on the limiting
  belief and the countably additive probability measure on `PCWorld` it induces.
* `Properties.ProvabilityInduction` — `thm:provind`, for a fixed sentence and for a
  `def:ec` sentence sequence.
* `Properties.TimelyLearning` — `thm:perkno` (Persistence of Knowledge) and `thm:tbo`
  (Preemptive Learning); its `thm:simcal` annotation sits on the emission certificate
  `sentenceAffine_polySequence`, which discharges that node's "`⟨φ⟩` is an e.c. sequence"
  premise, not on the §4.3 endpoint.

## §4.3–4.5 Calibration, statistical patterns, logical relationships, affine

* `Properties.Calibration` — `def:fuz`, `def:ece` and `thm:simcal`, in the forms conditional
  on a historical maturity verifier (`BiasRunHistoricallyVerifiable`); the *unconditional*
  `thm:simcal`, `thm:recurringunbiasedness` and `thm:recunbiasedaff` endpoints are proved in
  `Construction/Statistics/HistoricalMaturity.lean`, which discharges that premise — still
  over an arbitrary `[IsLogicalInductor P DP]`, not over the constructed market — from the
  market and deductive-process computations that instance already carries.
* `Properties.Pseudorandomness` — `thm:wubaff`/`thm:wub` (unbiasedness from feedback),
  `app:prandaff`, and the pseudorandom-frequency theorems `thm:prand`/`thm:benford`. Its two
  affine unbiasedness engines are annotated `thm:wubaff`, `thm:wubexp` jointly, because the
  expectation form in `Properties.ExpectationProperties` is the same engine read on a LUV.
* `Properties.Relationships` — `thm:lex` (exclusive–exhaustive families), the equivalence
  and implication consequences, and the sentence-and-negation instance
  `lic_limitingBelief_add_neg` that `thm:lc` and `thm:ob` both read off it.
* `Properties.AffineCoherence` — `thm:affcoh`; all three comparison forms of
  `thm:affprovind` (`AffineCombination.PolySequence.affine_provind_theory_ge` / `_le` /
  `_eq`, which are that node's endpoints — *not* `lic_provind_true`/`_false`), over the
  semantic engine `PolySequence.affine_provind`; and the `thm:provind` forms that factor
  through it, including `lic_provind` itself.
* `Properties.AffinePersistence` — `thm:peraffkno`, and the named limit
  `lic_limitingBelief_tendsto` carrying `thm:con`.
* `Properties.AffinePreemptiveLearning` — `thm:affpolymax`, factored over the two
  no-preemptive-gap conditions supplied by the return-on-investment machinery.

## §4.6–4.8 Non-dogmatism, conditionals, expectations

* `Properties.NonDogmatism` — `thm:nd`, both directions, in finite-stage and limit form.
* `Properties.UniformNonDogmatism` — `thm:obu`.
* `Properties.OccamBounds` — `thm:ob`, over a Kraft-weighted sentence ladder.
* `Properties.UniversalSemimeasure` — `thm:dus` (domination of the universal semimeasure)
  and `thm:strict` (strict domination).
* `Properties.FinitePerturbations` — `thm:ifp` (closure under finite perturbations) and its
  appendix `app:ifp`; the freeze transducer it transports a trader with is
  `Framework/Emission/FreezeTransducer.lean`.
* `Properties.FinitePerturbationCounterexample` — the refutation of the *unrestricted*
  `thm:ifp`, modulo its advice construction.
* `Properties.Conditioning` — `thm:scon`, in the fixed-prefix, gated and growing-prefix
  forms, at both classes; the `*_machine` forms are canonical, and neither set follows from
  the other.
* `Properties.ExpectationConvergence` — `thm:ec`: the day-`n` expectation is the price of
  the precision-`n` threshold bundle, trapped by `thm:affcoh` and made Cauchy by
  `lem:conluvapprox`.
* `Properties.ExpectationAffine` — `thm:ei`, `thm:loe`, `thm:expprovind`.
* `Properties.ExpectationProperties` — `def:luv`, `def:blcp`, `lem:mesh`, and the collected
  expectation-property lifts `thm:expcoh`, `thm:exppolymax`, `thm:perexpkno`, `thm:wubexp`
  (the last shared with the affine engines in `Properties.Pseudorandomness`).

## §4.9–4.12 Trust, introspection, self-trust

* `Properties.MetaLearning` — `thm:pac`, `thm:incons`, `thm:halts`, `thm:loops`,
  `thm:dontwait`, all reduced to completed-theory Provability Induction, together with the
  representation interfaces the `thm:pazfc` lane consumes; that node's endpoint is
  `lic_belief_stronger_theory_consistency_unconditional` in
  `Construction/Knowledge/Endpoints.lean`.
* `Properties.Introspection` — `thm:ref`, `thm:lp`, `thm:epr`, `thm:er`, and the quotation
  interface `CompletedAffineQuoteApprox`, annotated `thm:cee`, `thm:ceu`, `thm:ccee`,
  `thm:st` because it is the approximation datum `Properties.SelfTrust` states those four
  nodes over.
* `Properties.SelfTrust` — `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`, and the deferral
  functions (`def:deferralfunc`) they quantify over, together with the bounded schedule
  (`deadlineRun`, `scheduledMatch`) by which a machine tests the undecidable deferral
  deadline; both `Construction/` lanes that read a deferral schedule read it from here.
-/
