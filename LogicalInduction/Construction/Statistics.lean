import LogicalInduction.Construction.Statistics.SettlementClock
import LogicalInduction.Construction.Statistics.SettlementCompiler
import LogicalInduction.Construction.Statistics.FeedbackEmission
import LogicalInduction.Construction.Statistics.FeedbackTruth
import LogicalInduction.Construction.Statistics.HistoricalMaturity
import LogicalInduction.Construction.Statistics.Endpoints

/-!
# Statistical properties (`LogicalInduction.Construction.Statistics`)

The §4.3–4.4 lane, together with the §4.5 affine and §4.8 expectation analogues of the same
three families, which run on the same four constructed interfaces: recurring calibration and
unbiasedness — `thm:simcal` (tex:1193), `thm:recurringunbiasedness` (tex:1225),
`thm:recunbiasedaff` (tex:1469, §4.5), `thm:recurringunbiasednessexp` (tex:1812, §4.8) —
unbiasedness from feedback — `thm:wub` (tex:1249), `thm:wubaff` (tex:1480, §4.5),
`thm:wubexp` (tex:1822, §4.8) — and the pseudorandomness family `thm:benford` (tex:1283),
`thm:prand` (tex:1314), `thm:prandaff` (tex:1492, §4.5) and `thm:prandexp` (tex:1834, §4.8).

`Properties/Calibration.lean`, `Properties/Pseudorandomness.lean`,
`Properties/ExpectationProperties.lean` and `Properties/TimelyLearning.lean` state those nodes
over an arbitrary inductor, each behind an interface the trader needs and the paper argues
informally:
a clock that says when an affine combination has settled, an emitter turning a feedback
schedule into an efficiently computable trade stream, a delayed-truth sequence, and a uniform
verifier for "this pattern has recurred often enough".  This directory constructs all four and
instantiates the endpoints over the single paper-facing market.  Two of the eleven nodes —
`thm:prandexp` and `thm:recurringunbiasednessexp` — are carried by no declaration under
`Properties/`: this lane's own `HistoricalMaturity.lean` capstones are their only carriers, and
they are stated there over an arbitrary inductor.

## The settlement clock

* `SettlementClock` — `PatientSettlementClock` from a semi-decider or a purely computational
  checker, over the sound under-approximation `deadlinePassed` of the undecidable deferral
  deadline (`def:deferralfunc`).
* `SettlementCompiler` — the checker itself, compiled from a market program and a
  deductive-process program: course-of-values `Primrec` recursions on Gödel codes, the fuel
  layer over the market's quote table, and `def:ece` into `Computable`.  Its
  `PatientSettlementClock.ofComputations` leaves no computability *bridge* and no checker as a
  hypothesis; the one computability obligation it still charges the caller is
  `htolPrim : Primrec tol` on the caller-supplied tolerance stream.

## Feedback and maturity

* `FeedbackEmission` — the `def:ec` write-out certificate for the feedback trader indexed by a
  deferral function, which is what makes `thm:wubaff` and `thm:wubexp` quantify over the
  paper's own trader class.
* `FeedbackTruth` — the delayed-feedback truth sequence: `FeedbackTruthComputation` and the
  generic `_ofComputation` carriers, with the mixed-truth witnesses that keep the premise from
  being satisfiable only by a constant.  This is the one module of the lane that depends on the
  `Quotation/` lane: it imports `Construction/Quotation/Packages.lean` for
  `DeferralFunction.exists_clock` and, through it, `Construction/Quotation/DeferralFibre.lean`
  for the deferral fibre `deferralPreimage`.  The dependency runs both ways at the lane level —
  `Packages.lean` imports this lane's `FeedbackEmission.lean` — and both headers say so.
* `HistoricalMaturity` — the uniform maturity search behind the Return on Investment lemma
  (`lem:type3`, tex:3567): compiled from programs for the member traders, the market and the
  deductive stages, it closes `BiasRunHistoricallyVerifiable` and
  `HistoricalVerifiedMaturitySchedule`.  Its capstones then state `thm:simcal`,
  `thm:recurringunbiasedness`, `thm:recunbiasedaff`, `thm:recurringunbiasednessexp`,
  `thm:benford`, `thm:prand`, `thm:prandaff` and `thm:prandexp` over an arbitrary inductor with
  no verifier and no clock hypothesis, building both from the inductor's own computability data.

## The endpoints over the constructed market

* `Endpoints` — `thm:wub`, `thm:wubaff` and `thm:wubexp` over `liaHistory (paperDP T)`, the
  same provability process the computational-knowledge and quotation endpoints price against.
-/
