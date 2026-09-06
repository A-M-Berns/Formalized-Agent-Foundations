import LogicalInduction.Construction.MarketMaker
import LogicalInduction.Construction.MachineTraderEnumeration
import LogicalInduction.Construction.Budgeter
import LogicalInduction.Construction.TradingFirm
import LogicalInduction.Construction.LIA
import LogicalInduction.Construction.LIAComputation
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Paper
import LogicalInduction.Construction.Knowledge
import LogicalInduction.Construction.Quotation
import LogicalInduction.Construction.Statistics
import LogicalInduction.Construction.NonDogmatism
import LogicalInduction.Construction.Freeze
import LogicalInduction.Construction.Conditioning
import LogicalInduction.Construction.LUV
import LogicalInduction.Construction.SemanticExtension

/-!
# Construction and existence (`LogicalInduction.Construction`)

The paper's §5: an explicit algorithm together with the proof that its market satisfies the
logical induction criterion at the paper's own quantifier.

## The fixed point and the market maker

* `lem:fpl` → `fixed_point_lemma` (`MarketMaker.lean`) — the price-adjustment map on the
  compact convex space of valuations has a fixed point; it is continuous because trading
  strategies are (what continuity of `EF.denote` buys). Mathlib has no Brouwer fixed-point
  theorem, so `Construction.Brouwer` proves the instance needed here from Sperner's lemma;
  see that file's header for its trust-surface disclosure.
* `def:markemaker` → `MarketMaker` — rational approximation to the fixed point.

## Enumeration, budgeting and the trading firm

* `def:ec` → `MachineTraderEnumeration` — `enumeratedTrader`, sound
  (`enumeratedTrader_machineEfficient`) and covering (`exists_enumeratedTrader_eq`) for
  `MachineEfficientTrader`. This is what makes the firm dominate the paper's own class, and
  hence what makes the criterion hold at the paper's own quantifier.
* `lem:budgeter` → `Budgeter` and its three parts (`Budgeter.lean`) — caps each enumerated
  trader.
* `eq:tradingfirm` / `lem:tfdom` → `TradingFirm` — combines enumerated traders with budgets,
  and carries the dominance lemma (`trading_firm_dominance`, `trading_firm_dominance_of_ec`)
  over the enumeration above.

## The algorithm and the existence theorems

* `def:lia` / `alg:li` → `liaStates`, `liaHistory` (`LIA.lean`, with `liaQuote` and
  `liaTrader` beside them) — the concrete algorithm and the market it induces.
  `LIAComputation` and `LIACompiler` carry its bounded-evaluation and compilation layers.
* `thm:lia` → `LIA_isMachineLogicalInductor` — discharges `def:lic` at the paper's own
  quantifier; `LIA_is_logical_inductor` is its fuel-class form, which is what the §4
  property tail consumes.
* `thm:li` → `exists_machine_logical_inductor`, with
  `exists_computable_beliefSequence_logical_inductor` the full belief-sequence form the
  paper states (`def:belseq`); `exists_logical_inductor` is the fuel-class projection.

## The lanes that discharge the §4 interfaces

The §5 existence proof above imports none of what follows: these are the constructions that
turn each property theorem's assumed boundary interface into a built one, grouped by the
paper family they serve.  Each lane directory has its own roll-up module with the same kind
of map as this one.

### `Paper/` — the literal first-order layer (`Construction/Paper.lean`)

* `FirstOrder` — the tag-`5` prime reading of Foundation's arithmetic sentences inside the
  propositional `Sentence` type, and its primitive-recursive compiler on Gödel codes
  (`dd:nnf`).
* `ComputationDP` — `theoremDP`, the computation/quotation literal stream, with
  `quotationPresentation` (`thm:ref`) and `liaMarketComputation` (`thm:lia`).
* `TheoremDP` — `paperTheoryDP`, the `Θ`-complete first-order theorem stream, and `paperDP`,
  the single market's process, with `paperQuotationPresentation` (`thm:ref`) and
  `paperMarketComputation` (`thm:lia`).
* `Market` — the self-reference family over `liaHistory (paperDP T)`: `thm:ref`, `thm:lp`,
  `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`.
* `FiniteEntailment` — `stageEntails`, the executable finite-stage entailment test.

### `Quotation/` — §4.11–4.12 (`Construction/Quotation.lean`)

* `Packages` — the code-indexed quotation layer (`dd:quote-code`), the affine quote
  portfolios and package constructors, and the eight `_ofCode` / `_ofRepresentation` /
  `_ofDiagonal` theorems `Paper/Market` instantiates.
* `DeferralFibre` — the quotation-free deferred affine layer (`def:ece`).
* `MarketQuoteCodes` — market-generic quote codes derived from the certified market program.
* `ProductDefinition` — the fresh-atom definitional extension diagnosing `thm:ccee`'s mesh
  slack (`dd:mesh`).
* `ExactProduct`, `RepresentedWeight`, `ExactCCEE` — the literal route to `thm:ccee` at zero
  slack on the same market.

### `Knowledge/` — §4.9–4.10 (`Construction/Knowledge.lean`)

* `Syntax`, `SubstEmission` — the claim syntax whose sentences name their machine, and its
  `def:ec` write-out certificate.
* `DayMachine`, `SourceNumbering`, `SourceRecognizer`, `SourceWindow` — the write-and-read-back
  kit that reads a machine as the theory it presents (`dd:machinetheory`).
* `Endpoints` — `thm:pac`, `thm:pazfc`, `thm:incons`, `thm:halts`, `thm:loops`,
  `thm:dontwait` over `liaHistory (paperDP T)`.

### `Statistics/` — §4.3–4.4 with the §4.5/§4.8 analogues (`Construction/Statistics.lean`)

* `SettlementClock` — `PatientSettlementClock` from a semi-decider or a computational checker,
  over a sound under-approximation of the undecidable deferral deadline.
* `SettlementCompiler` — that checker compiled from a market program and a deductive-process
  program (`PatientSettlementClock.ofComputations`), with the `def:ece` bridge into
  `Computable`.
* `FeedbackEmission`, `FeedbackTruth` — the `def:ec` emitter for the feedback trader and the
  delayed-truth sequence `thm:wub` is stated over.
* `HistoricalMaturity` — the uniform maturity search of `lem:type3`, and with it the
  recurring-unbiasedness, calibration and pseudorandomness capstones (`thm:simcal`,
  `thm:recurringunbiasedness`, `thm:recunbiasedaff`, `thm:recurringunbiasednessexp`,
  `thm:benford`, `thm:prand`, `thm:prandaff`, `thm:prandexp`) over an arbitrary inductor.
* `Endpoints` — `thm:wub`, `thm:wubaff`, `thm:wubexp` over `liaHistory (paperDP T)`.

### `NonDogmatism/` — §4.6 (`Construction/NonDogmatism.lean`)

* `RepeatedEnumeration` — `thm:obu`'s padding-and-repeating step, for a write-out-metered
  source and for an arbitrary c.e. one (`CEEnumeration`).
* `Kraft`, `PrefixMachine`, `UniversalPrefix` — Kraft's inequality, a concrete self-delimiting
  sentence code, and a self-delimiting *universal* machine, all discharging `thm:ob`'s
  `PrefixMachinePresentation`.
* `UniversalDovetailer`, `BitPrefix`, `StrictSeparators` — the constructed universal continuous
  semimeasure, the bit-prefix sentence presentation `thm:dus` is stated over, and the
  separator data for `thm:strict`.
* `Endpoints` — `thm:dus` and `thm:strict` unconditional over the constructed `LIA`: `thm:dus`
  over both `emptyBitDeductiveProcess` and `paperDP T`, `thm:strict` over
  `emptyBitDeductiveProcess` only.

### `Freeze/` — `thm:ifp` (`Construction/Freeze.lean`)

* `Prefix`, `CanonicalCodes`, `Compiler` — the `def:lia` freeze of the inductor's early quote
  table in the `dd:fuel` calculus, when the escape-leaf decode test is a canonical-code
  comparison, and the symbol-level freeze of the flat RPN stream.
* `RunAutomaton`, `PatternAutomaton`, `StructuredPatterns`, `CounterAutomaton`,
  `PayloadAutomaton`, `SegmentAutomaton`, `SegmentCounter`, `FiberTest`, `SegmentRecognizer` —
  the `Complexity.FP` recognizer kit deciding, for an arbitrary target and with no side
  condition, that a word's token run denotes it.
* `Step`, `Oracle` — the freeze as a polynomial-time transduction and the run-level lookup for
  a finite quote table, carrying `machine_lic_iff_of_finiteSupport`, the corrected `thm:ifp`.
* `Counterexample`, `LIAPerturbation` — the witness refuting the printed `thm:ifp`, and the
  instance in which the corrected one does visible work.

### `Conditioning/` — §4.7 (`Construction/Conditioning.lean`)

* `Presentation` — the `ConditioningPresentation` data `thm:scon` takes, in three forms: the
  paper's fixed `Θ ∪ {ψ}` case, the compact growing form, and the prefix conjunctions of an
  arbitrary e.c. sequence.
* `Compiler` — the conditioned market `P(φ | ψ)` as an exact rational program, the finite
  denominator patch and its price floor, the flat token transducer, and the digit-metered
  residual.
* `PricePass`, `FramePass` — the translation in the RPN symbol model (`dd:fuel`): the
  run-aware automaton and price rewrite, then the frame legs, the two-leg join and
  `conditionedTranslation_preserves_ecRpn`.
* `Transduction`, `TransductionFrame` — the same transducer as a `Complexity.FP` machine
  function, ending in `conditionedTranslation_preserves_machine`.
* `Endpoints` — the criterion-level `lic_conditioned*` family in both trader classes, and
  `thm:scon` unconditional over the constructed `LIA`.

### `LUV/` — §4.8 (`Construction/LUV.lean`)

* `PaperLUV`, `SourceCodec`, `ArithmeticSource` — the literal first-order frontend: `def:luv`
  with an arbitrary defining formula, the RPN leaf codec and compact ℒₒᵣ numeral it is
  emitted through, and the paper's own formula source language `ArithSource` with the class
  `PolyArithmeticSourceSeq` that meters a family as the paper writes it (`dd:nnf`).
  `PaperLUVCombination` is `def:blcp` over it.
* `Arithmetic`, `Presentation` — `dd:luv-arith`: the paper's worked computable LUV class, and
  the derivation of the world-value interfaces from it together with the deductive process
  `luvThresholdDP` that satisfies the one premise retained.
* `Syntax` — `LUVCombinationSyntax` and the four `_ofSyntax` carriers of `lem:mesh`,
  `thm:exppolymax`, `thm:expcoh` and `thm:perexpkno`.
* `Endpoints` — `thm:expprovind`, `thm:loe`, and the `_arith` / `_arith_unconditional`
  expectation tail.

### `SemanticExtension/` — the generalized `thm:ccee` (`Construction/SemanticExtension.lean`)

This lane exists for one endpoint,
`lic_no_expected_net_update_conditional_exact_canonical`: `thm:ccee` at zero slack over an
*arbitrary* threshold-only source carrying only `LUV.RpnThresholdCodeSeq`, priced on a fixed
enlarged language rather than on `liaHistory (paperDP T)`.

* `Prime` — the semantic-prime handle allocation, and the diagonalization showing no
  non-vacuous fixed process reflects every efficiently emitted source.
* `Quote` — the definitional bridge from a quote leaf to the universal quotation atom.
* `Product` — the exact product closure, the joint obstruction, and the two factor-ownership
  gates that answer it.
* `Source` — the proof-carrying source certificate, its executable checker, and the fixed
  universal interpreter.
* `LanguageCopy` — the fixed old-language renaming, the entailment-gated admission over it,
  and the compiler that admits an existing RPN threshold certificate.
* `Registry` — the registry-guarded exact product process.
* `Endpoints` — `canonicalCCEEDP` and the endpoint itself.
-/
