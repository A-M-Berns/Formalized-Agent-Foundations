import LogicalInduction.Properties
import LogicalInduction.Framework.Machine.WriteOutMachine
import LogicalInduction.Construction.Machine.CondEndpoints
import LogicalInduction.Construction.Witnesses.FreezeOracle
import LogicalInduction.Construction.Witnesses.FinitePerturbationWitness
import LogicalInduction.Construction.Witnesses.HistoricalMaturity
import LogicalInduction.Construction.Witnesses.LIAPerturbation
import LogicalInduction.Construction.Witnesses.LUVPresentation
import LogicalInduction.Construction.Witnesses.StrictSeparators

/-!
# Logical Induction — the supported interface

```lean
import LogicalInduction.API
```

One import, and it is the interface for theoretical work over logical inductors: the
semantic objects of the paper's §2–3, the criterion at the paper's own quantifier, the §4
property library, the certificate kit that builds an exploiting trader, the two theorems
that move the criterion from one market to another, and the constructed inhabitants that
discharge the property tail's interfaces.

Its import closure is 111 modules, of the 152 that `import LogicalInduction` reaches — the
§2–3 substrate, all of §4, the whole §5 spine, and the witness modules named below — so a
name discussed here resolves from this import alone.  What stays outside is the first-order
instantiation layer and the semantic-extension lane, listed under *Deeper imports*.

## The objects

A **`Sentence`** is a propositional formula over Foundation's `Formula`; a **`History`** is
the market, a function from day and sentence to a price in `[0,1]`; a
**`DeductiveProcess`** is the day-indexed stream of what has been deduced, and a
**`PCWorld`** a propositionally consistent world completing it.  An **`EF`** is an
expressible feature (`dd:dsl`), a reified expression in prices and rationals with a
denotation; a **`Strategy`** is a day's finite list of (feature, sentence) trades; a
**`Trader`** is a day-indexed family of strategies, and `Trader.Exploits P DP` says its
holdings are bounded below and unbounded above across the plausible worlds — the paper's
notion of making unbounded money at no risk.  An **`AffineCombination`** is the affine
portfolio the §4 proofs price.  A **`LUV`** is a logically uncertain variable, presented by
its family of threshold sentences, with `LUV.expect` its market expectation and
`PCWorld.ValuesAt X x` the market-observable content of "`X` has value `x` in `v`".  The
limit vocabulary — `≈ₙ`, `≳ₙ`, `≲ₙ`, `ConvergesTo` — is owned by `Framework.Asymptotics`
(`dd:asymp`), together with its algebra: `AsympEq.add`, `.sub`, `.const_mul`, `AsympLE.add`,
`AsympLE.trans` and `asympGE_iff`.  `EF.EFn n` is the rank-`n` feature ring, graded
monotonically by `EF.EFn_mono`.

## Efficiency: one class, one certification route

The paper's `def:ec` is **ordinary machine polynomial time**, and so is the Lean rendering:

* `MachineEfficientTrader Tr` — some function in `Complexity.FP` maps the *unary* day `n` to
  a word decoding to `Tr`'s day-`n` strategy.  No fuel, no interpreter, no repository-local
  notion of cost.

To use that class you must exhibit a `Complexity.FP` witness, which is unpleasant by hand.
So there is a compositional certificate calculus, and exactly one bridge out of it:

* `EfficientlyComputable Tr` / `PolyFueled` (`dd:fuel`) ask for a `Nat.Partrec.Code` pair
  emitting the trade stream inside a polynomial fuel bound on Mathlib's `evaln`.  These are
  **certificates**, not a definition of efficiency.
* `EfficientlyComputable.toMachine : EfficientlyComputable Tr → MachineEfficientTrader Tr`
  is the bridge, proved through a real `evaln` → Turing-machine compiler.

So a fuel certificate is a *sufficient* route into the paper's class.  The converse is
neither proved nor claimed, and nothing paper-facing depends on it.

## Building an exploiting trader

A §4-style argument ends by handing the criterion a trader together with a certificate, so
the certificate kit is part of the interface.

* **Scalars.** `PolyFueled c f` certifies a `ℕ → ℕ` function against the code `c`; it is
  closed under `PolyFueled.const`, `.id`, `.left`, `.right`, `.pair`, `.comp`, `.prec`,
  `.succ_comp`, `.addConst` and `.of_eq`, and `PolyFueled.primrec` extracts the primitive
  recursion a downstream `Primrec` obligation wants.
* **Token and segment streams.** `PolySegStream s` certifies a day-indexed list of tokens.
  Its closure suite is `PolySegStream.ofTokenStream`, `.append`, `.comp`, `.ifZero`,
  `.of_eq`, `.blocks`, `.block`, `.repeatTag`, `.concat`, `.concatVar` and
  `.digitizeStream`, and its `serialize_*` mirror of the `EF` datatype is complete —
  `serialize_const`, `serialize_var`, `serialize_price`, `serialize_add`, `serialize_mul`,
  `serialize_max`, `serialize_safeRecip`, `serialize_letE` — so an emission assembly can be
  written against the whole feature grammar.  `PolySegStream.exists_FP_word`
  (`Framework/Machine/WriteOutMachine.lean`) is the recipe that turns such a stream into the
  `Complexity.FP` word the machine class asks for, and `ecTok_of_segStream` is the
  trader-level capstone: a trader whose day-`n` stream is a `PolySegStream` is
  `EfficientlyComputableTok`.
* **Sentence families.** `RpnSentenceCodes` is closed under the propositional connectives —
  `RpnSentenceCodes.or` and `.imp` beside `.and`, `.const`, `.ifZero`, `.comp`, `.bigAnd`
  and `.bigOr` — and `BigSentenceCodes` is the write-out class the property tail actually
  binds.  Both have machine readings in `Framework/Machine/WriteOutMachine.lean`:
  `MachineTokenStream` and `MachineSentenceCodes` are the `Complexity.FP` shapes, reached by
  `BigTokenStream.toMachine`, `BigSentenceCodes.toMachine` and `RpnSentenceCodes.toMachine`,
  the sentence-side analogues of `EfficientlyComputable.toMachine`.
* **Assembling the trader.** `EfficientlyComputable.ofSingleTradeBlocksBig`,
  `.ofTradeBlocksBig` (variable trade count, write-out coefficients and sentences),
  `.ofSingleTradeBlocks` and `.ofTradeBlocks` (their token-metered counterparts), fed by the
  write-out classes `BigSentenceCodes`, `BigDigits`, `DigitRatCodes`, `DigitMachineCodes`
  and the emission classes `BigTokenStream` / `BigSpliceStream`.
* **Exploitation engines.**  `Properties.Basic` supplies the three ways a constructed
  trader is shown to exploit: `exploits_of_ge_partialSums` (world-dependent partial-sum
  bound), `exploits_of_nonneg_partialSums` (its world-neutral specialization) and
  `exploits_of_bddBelow_of_unbounded` (the definitional route from a floor plus
  unboundedness).  `Trader.bddBelow_plausible_of_finiteMagnitude` discharges the
  bounded-downside half from summable total magnitude, and
  `Trader.Exploits.of_boundedDifference` transports exploitation across two markets whose
  net-worth streams differ boundedly.
* **Indicator toolkit.**  The buy/sell hysteresis machinery the §4.1 and §4.5 traders run
  on is public: `buySignal_nonneg` and `buySignal_eq_of_pos` for the ε-gated indicator,
  `armChain` for the latched arming state with `serialize_armChain` its emission
  certificate, and `exists_rat_oscillation_of_not_convergesTo` /
  `exists_rat_oscillation_of_not_exists_convergesTo` for the rational oscillation window a
  non-convergence hypothesis hands the trader.
* **Return on investment.**  `ROIBudget.noRepeatableROI` is `lem:type3`, with
  `ROIBudget.noRepeatableROI_of_verifiedMaturity` the form to apply — it takes one
  polynomial maturity checker (`ROIBudget.VerifiedMaturitySchedule`) and builds the closing
  days, the semantic schedule and the openness table.  `ROIBudget.exists_maturitySchedule`
  records which half of that input is a real obligation: the semantic schedule is free, only
  the polynomial verifier is asked for.  `HasROI` (`def:roi`), `PolyTradeEmulatable` and
  `EfficientlyEmulatable` (`def:emulatabletraders`) are the trader-family interfaces those
  statements quantify over.

## The criterion, and which of its two forms to state against

* `IsMachineLogicalInductor P DP` — `def:lic` over `MachineEfficientTrader`: a computable
  market and deductive process such that no polynomial-time trader exploits the market.
  **This is the paper-facing criterion**, and the one the §5 construction discharges.
* `IsLogicalInductor P DP` — the same criterion over the fuel-certified class.  It is the
  compatibility interface: the §4 property theorems are stated against it, and the instance
  `IsMachineLogicalInductor.toIsLogicalInductor` carries every one of them to a machine
  logical inductor unchanged.

The asymmetry is worth internalizing, because it determines how to state new results.  A
theorem *consuming* the criterion should take `[IsLogicalInductor P DP]`: such a statement is
automatically available at the machine class, while the reverse is not.  A theorem whose
*conclusion* is the criterion cannot use the instance at all — it must be stated at the
machine class directly, since the class has to be closed under the trader translation the
proof performs.  Both such theorems are below, at both classes.

## The §4 property library

Every `lic_*` family takes `[IsLogicalInductor P DP]` and holds of *every* logical inductor:
convergence and coherence, provability induction, timely learning (persistence of knowledge,
preemptive learning), calibration and unbiasedness, pseudorandomness, logical relationships,
non-dogmatism with its uniform and Occam forms, universal-semimeasure domination,
expectations, introspection, paradox resistance, and self-trust.  Names mirror the paper's
labels (`lic_provind` ↔ `thm:provind`).

Two conveniences on that surface are worth naming, because they save a client the standing
convergence side condition: `lic_price_convergesTo` is `thm:con` in the form that hands back
the limit, and `lic_exists_limit_pos` / `lic_exists_limit_lt_one` are the closed
non-dogmatism forms — an independent sentence's price has a limit strictly inside `(0,1)`,
with the convergence hypothesis discharged internally rather than assumed.  On the affine
side, `affineFutureHigh` / `affineFutureLow` are the paper's `supₘ≥ₙ` / `infₘ≥ₙ` benchmarks
and `BoundedAffinePrices` the uniform cross-time price bound their `sSup`/`sInf` forms need,
which `AffineCombination.BoundedCombinationSequence.boundedPrices` reads off a bounded
combination sequence over a market with prices in `[0,1]`.

Three more supported tools sit beside the §4.8 and §4.12 statements.  `LUV.expectInf` is
`𝔼_∞(X)`, the limiting expectation of `thm:ec`; a client never unfolds its choice, because
`LUV.expectSeq_convergesTo_expectInf` is its defining property and
`LUV.expectInf_eq_of_convergesTo` identifies it with any limit found independently.
`DeferralFunction` (`def:deferralfunc`) is what the self-trust endpoints quantify over, and
`succDeferral` inhabits it, so none of those binders is vacuous.
`AffineQuotePortfolio.gap_asympEq_zero_of_diagonal` divides a quote portfolio's positive
normalization out of a vanishing diagonal price, which is the last step of every two-sided
quotation endpoint.

## Moving the criterion between markets

**Conditioning (`thm:scon`).**  `lic_conditioned_machine`, `lic_conditioned_gated_machine`
and `lic_conditioned_eventual_machine` are the canonical forms; `lic_conditioned`,
`lic_conditioned_gated` and `lic_conditioned_eventual` are their fuel-class counterparts.
Neither set follows from the other, so both stand.

The conditioning data is a `ConditioningPresentation DP extra`, and three constructors build
one so a client never fills the fields by hand
(`Construction/Witnesses/ConditioningPresentation.lean`):
`fixedConditioningPresentation` for a single sentence, `prefixConditioningPresentation` for
the growing prefix conjunctions of a `BigSentenceCodes` family, and
`conditioningPresentationOfComputations` from a `CompactConditioningProcessComputation`.
Above them sit the two hypothesis-free machine endpoints in
`LogicalInduction.ConditioningCompile` (`Construction/Machine/CondEndpoints.lean`):
`lic_conditioned_fixed_machine` conditions on one sentence and
`lic_conditioned_growing_machine_ofSequence` on an arbitrary efficiently computable
sequence, both with **no** consistency premise — the stage and market programs are read off
the inductor instance itself.

**Finite perturbation (`thm:ifp`).**  Read this one carefully, because the *printed* theorem
is false: a single changed pricing day is an infinite computable function, so it can carry
unbounded computational advice to an efficient trader.
`FinitePerturbationCounterexample.not_overgeneral_ifp` refutes the paper's unrestricted
statement (`notes/paper-errata.md`, PE1); it is re-exported below so the bare name resolves
from this import.  `LIAPerturbation.machineLogicalInductor_liaPerturbed` is the corrected
theorem doing visible work in the other direction: the constructed market with one price
moved is still a machine logical inductor, and its inductor-hood comes from `thm:ifp` and
nowhere else.

What holds — and what a client should use — is the finite-*support* correction, exported
here as `lic_iff_of_finiteSupportPerturbation_machine`: two `ComputableMarket`s differing at
only finitely many `(day, sentence)` price coordinates satisfy the criterion together, with
no certificate hypothesis (the freeze certificate is compiled from each market's own
computability certificate) and **no condition on the moved sentences**.
`FiniteSupportPerturbation` is its whole hypothesis, and
`FiniteSupportPerturbation.tail_agree` relates it to the paper's tail agreement (finite
support is strictly stronger — `tailAgree_not_finiteSupport` proves the converse fails, so
this theorem cannot re-derive the refuted printed one).
`lic_iff_of_noReservedSupportPerturbation` and `lic_iff_of_recognizableSupportPerturbation`
are the same theorem under strictly stronger hypotheses:
`RecognizableSupportPerturbation` implies `NoReservedSupportPerturbation` implies
`FiniteSupportPerturbation`, by `FreezeOracle.RecognizableSupportPerturbation.toNoReserved`
and `.toFiniteSupport`.  Prefer the finite-support form.

No syntactic condition travels with the theorem.  `DigitFP.sqrtRemW_mem_FP` and
`DigitFP.unpairW_spec` put integer square root and `Nat.unpair` inside `Complexity.FP`,
`FiberTest.fiberW_mem_FP` builds the escape-leaf decode test on them, `PayAuto` decides the
structured payload language of a fixed formula code, and `CtrAuto.ctrMachine` decides the
structured block's `aⁿbⁿ` unary length field.  `FreezeOracle.machine_lic_iff_hardPoint` and
`FreezeOracle.machine_lic_iff_reservedPoint` freeze coordinates at `atom 0 ⋏ ⊥` and at a
reserved atom.  What is disclosed is a property of the construction, not of the statement:
the recognizer is compiled per frozen sentence, so its polynomial-time constants depend on
that sentence, which is sound exactly because the support is finite.  The fuel-class forms
`lic_iff_of_finitePerturbation` and `lic_iff_of_finiteSupportPerturbation` take patch
certificates (`EfficientPrefixPatch`, `FiniteSupportPatch`) that have **no inhabitant
anywhere in this repository**, because the fuel calculus does not close over the escape-leaf
decode the frozen lookup needs.  Use the machine form.

## Constructed inhabitants that arrive with this import

The §5 existence construction arrives transitively, so `liaStates`, `liaHistory`,
`LIA_isMachineLogicalInductor` and `exists_machine_logical_inductor` are usable from this
import, together with `exists_computable_beliefSequence_logical_inductor` — the full
belief-sequence form the paper states (`def:belseq`), handing back a computable sequence of
explicit finite-support rational belief states — and `liaBoundedEvaluatorCompiler`, the
compiled bounded evaluator the existence proof runs on.  The construction's internals are
not interface.

Four further families of constructed data come with it, each removing a hypothesis a §4
statement would otherwise leave to the caller:

* **Non-dogmatism and semimeasures.**  `CEEnumeration source` is `thm:obu`'s "computably
  enumerable sequence" premise as the paper states it (unclocked), and
  `lic_uniform_nonDogmatism_ofCE` consumes it directly, building the padded efficient
  repetition internally.  `bitPrefixSentencesOfIndependentAtoms` constructs the independent
  bit-prefix sentence family `thm:dus` quantifies over, with
  `lic_domination_universalSemimeasure_ofIndependentAtoms` the endpoint over it, and
  `lic_strict_domination_universalSemimeasure_ofAtomCodes` is `thm:strict` at a family given
  by its atom codes.
* **Statistics without a verifier.**  `Construction/Witnesses/HistoricalMaturity.lean`
  closes the two maturity interfaces the §4.3–4.5 proofs leave open and restates their
  capstones with no verifier hypothesis: `AffineCombination.recurringunbiasedness` and
  `AffineCombination.simcal`, `AffineCombination.BoundedCombinationSequence.recunbiasedaff`
  and `.prandaff` (with its `_above`/`_below` halves),
  `LUVCombination.BoundedSequence.recurringunbiasednessexp` and `.prandexp`, and the
  pseudorandom-frequency family `lic_learning_varied_pseudorandom` and
  `lic_learning_pseudorandom_frequency`.  The settlement clocks are constructed too, so no
  endpoint there takes a clock as data.
* **Feedback.**  `FeedbackEmission.feedbackTraderEmissionSigns` is the emission certificate
  for the sign-switching feedback trader, and `FeedbackEmission.lic_wubaff_ofFeedbackTruth`,
  `FeedbackEmission.boundedCombination_wubaff_ofFeedbackTruth` and
  `FeedbackEmission.luv_wubexp_ofFeedbackTruth` are the `thm:wubaff` / `thm:wubexp`
  endpoints over a supplied delayed-truth computation.
* **LUVs and horizons.**  `ComputableLUV` is the `dd:luv-arith` certified class: its
  `ComputableLUV.toLUV_polyThresholdCodes` is the repository's one proved
  `PolyThresholdCodes` certificate, and `ComputableLUV.valuesAt_ofArithmetic` discharges the
  world-value obligation from an `ArithmeticLUVPresentation`.  The four
  `LUVCombination.BoundedSequence` endpoints stated
  against a `LUVCombinationSyntax` presentation rather than a bare metering hypothesis are
  `mesh_independence_ofSyntax`, `expcoh_ofSyntax`, `perexpkno_ofSyntax` and
  `exppolymax_ofSyntax`.  `PresentedLUVSeq` is the threshold-only source interface the
  semantic lane quantifies over, built by `semanticHandleLUVSeq` with
  `semanticHandleLUVSeq_rpnThresholdCodeSeq` its emission certificate and
  `PresentedLUVSeq.gt_eq` its threshold-unfolding equation; what a *presented* source cannot
  do is recorded by `no_nonvacuous_worldValued_presented_of_rpn`, which is why `dd:mesh`
  exists.  `ComputableHorizon` is the §4.10 horizon interface, inhabited by
  `ComputableHorizon.of` from any computable step bound and by `ComputableHorizon.ackermann`
  at a bound no primitive recursive function dominates.  `PGenerableRat` is `def:ece` for
  rational sequences, with `PGenerableRat.ofDigitRatCodes` the write-out route in and
  `PGenerableRat.computable` the computability it yields against a market computation.

## Deeper imports, and when you need them

What this import does *not* bring is the first-order instantiation layer beyond
`paperDP T`'s own construction, and the semantic-extension lane.  Thirteen further imports
are the interface to those, each answering one question:

Every path below is under `LogicalInduction.Construction.Witnesses` unless written out.

* `R0Representability` — discharging `RepresentsComputations` at `𝗣𝗔⁻`, `𝗜𝚺₁` or `𝗣𝗔`.
* `ComputationRepresented` — the §4.10 endpoints over `liaHistory (paperDP T)`, together
  with the hypothesis-discharge kit below.
* `ArithmeticSource` — writing a new literal first-order formula family (`dd:nnf`).
* `PaperLUV` — the paper's literal first-order LUV objects, and the concrete families
  inhabiting them across the range the paper writes.
* `PaperExactCCEE` — `PaperLUVSeq`, and `thm:ccee` at zero mesh slack.
* `UnconditionalOverLIA` — `thm:dus` and `thm:scon` unconditionally over the constructed
  inductor.
* `FeedbackUnconditional` — `thm:wub` / `thm:wubaff` / `thm:wubexp` unconditionally over it.
* `LUVExpectationCertified` — the `_arith` LUV-expectation tail on the `dd:luv-arith` class.
* `UniversalPrefix` — the constructed self-delimiting universal machine and its prefix
  complexity, which `thm:ob` is instantiated at.
* `UniversalDovetailer` — the constructed universal continuous semimeasure `thm:dus`
  quantifies over.
* `SemanticLiftedCCEE` — the lifted-language substrate of the generalized `thm:ccee` over
  an arbitrary threshold-only source.
* `LogicalInduction.Framework.BoundedConsistency` — bounded provability and the paper's
  finite-consistency predicate `Con(Θ)(ν)` (`dd:symbolcount`).
* `LogicalInduction` — the whole development.

`RepresentsComputations T` — the paper's standing §2 assumption that Θ represents
computations, with `represents_proves`, `represents_refutes`, `represents_refutes_all` and
`RepresentsComputations.consistent` — is already in this import's closure
(`Framework/RepresentsComputations.lean`); only the instances discharging it need the first
import above.  Two further binders appear beside the paper's own premise in the §4.9–4.10
endpoints, and both are disclosed in `LogicalInduction/README.md`: `[T.Δ₁]` (a
`Δ₁`-definable axiom set — representation infrastructure) and `[𝗣𝗔⁻ ⪯ T]` (a genuine, small
strengthening).  `[𝗜𝚺₁ ⪯ T]` is asked for by three endpoints only.  No endpoint asks for
Σ₁-soundness.

**The §4.10 hypothesis-discharge kit.**  The endpoints in `ComputationRepresented` take two
side conditions that look like obligations and are not.  `theoryOf_const_ofNNF` discharges
the `thm:incons` presentation condition for a one-axiom theory — `ArithSource.ofNNF` writes
every sentence, so `theoryOf` of the constant machine is exactly that theory
(`dd:machinetheory`) — and `conGamma_mentions_zero_of_horizon_unbounded` discharges the
`Con(Θ′)(ν)` non-degeneracy condition from an unbounded horizon (`dd:symbolcount`), with
`ComputableHorizon.ackermann` supplying one.  Import that module to reach them.

## Not interface

Lean makes transitively imported declarations visible; visibility is not a stability
promise.  Raw `Nat.Partrec.Code` manipulation, the register-machine simulator and its
compilers (`Framework/Machine/`), token and bit folds, RPN parsing internals, the freeze and
conditioning stream compilers, the written-source recognizer and its budgeted day-window
splice (`SourceRecognizer`, `SourceWindow`, `DayMachine`), and the trader implementations
inside the property proofs are implementation, and may be renamed or restructured.

## Two representation interfaces you will meet

* **LUVs are threshold families.**  The `LUV` objects a client meets are rational threshold
  families over the propositional language, not first-order terms.  The paper's literal
  first-order object exists as `PaperLUV` — an actual one-variable arithmetic formula
  carrying object-level proofs — and compiles into the carrier, so results stated against the
  carrier apply to more families than the paper's.
* **`dd:mesh` and `thm:ccee`.**  `ConditionalExpectationQuote` carries a per-day reflection
  slack in its `slack` field.  That slack is the price of a *threshold-only* source: nothing
  in the abstract `LUV` interface names a value, so the quoted product can only be
  reconstructed from thresholds.  For the paper's **literal** first-order sources
  (`PaperLUVSeq`) the product is exact —
  `lic_no_expected_net_update_conditional_paperLUV_closed` states `thm:ccee` at `slack = 0`
  over the single market `liaHistory (paperDP T)`, like every other canonical endpoint.
  `lic_no_expected_net_update_conditional_exact_canonical` remains as the generalized
  semantic-extension form: exact for an *arbitrary* threshold-only source, but priced over a
  renamed deductive process.  `PaperLUVSeq` itself is a construction interface and is not
  re-exported here; import
  `LogicalInduction.Construction.Witnesses.PaperExactCCEE` to use the exact route.

`LogicalInduction/README.md` explains the modeling; `scripts/coverage-classification.md` and
`AxiomAudit.lean` carry the exact paper correspondence and the axiom accounting.
-/

namespace LogicalInduction

/-! ## Re-exports

The corrected finite-perturbation hypothesis and its atom witnesses, together with the
refutation of the printed `thm:ifp`, so clients need not name the construction namespaces
they are defined in. -/

export FreezeOracle (NoReservedSupportPerturbation RecognizableSupportPerturbation
  recognizable_atom atom_zero_noReserved)

export FinitePerturbationCounterexample (not_overgeneral_ifp)

/-! ## Finite perturbation, corrected (`thm:ifp`) -/

/-- **Closure under finite perturbations, corrected (`thm:ifp`).**

Two computable markets that differ at only finitely many `(day, sentence)` price
coordinates satisfy the logical induction criterion together, at the paper's own
quantifier.  This is the supported name for the result; it is definitionally
`FreezeOracle.machine_lic_iff_of_finiteSupport`, which is where it is proved.  The name
carries the `_machine` suffix because `lic_iff_of_finiteSupportPerturbation` is taken by the
*fuel-class* statement, which takes a patch certificate that has no inhabitant.

The paper's own statement — finitely many changed *days* — is **false**, and is refuted by
`FinitePerturbationCounterexample.not_overgeneral_ifp`; see `notes/paper-errata.md`, PE1.
Finite support is the natural repair, and is strictly stronger than the printed tail
agreement: `FiniteSupportPerturbation.tail_agree` gives one direction and
`tailAgree_not_finiteSupport` refutes the converse, so this theorem cannot re-derive the
refuted one.

`hpert` is the whole hypothesis on the perturbation, and there is no hypothesis at all on
the finitely many moved sentences: no `Recognizable`, no `BotFree`, no `NoReserved`, and no
freeze certificate.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem lic_iff_of_finiteSupportPerturbation_machine (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : FiniteSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  FreezeOracle.machine_lic_iff_of_finiteSupport P P' DP hPcomp hP'comp hpert

/-- **Closure under finite perturbations under a no-reserved-support hypothesis
(`thm:ifp`).**

`NoReservedSupportPerturbation` implies `FiniteSupportPerturbation`
(`FreezeOracle.NoReservedSupportPerturbation.toFiniteSupport`), so this is
`lic_iff_of_finiteSupportPerturbation_machine` under a strictly stronger hypothesis.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem lic_iff_of_noReservedSupportPerturbation (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : NoReservedSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  FreezeOracle.machine_lic_iff_of_noReservedSupport P P' DP hPcomp hP'comp hpert

/-- **Closure under finite perturbations under a recognizability hypothesis (`thm:ifp`).**

`RecognizableSupportPerturbation` implies `NoReservedSupportPerturbation`
(`FreezeOracle.RecognizableSupportPerturbation.toNoReserved`), so this is
`lic_iff_of_noReservedSupportPerturbation` under a strictly stronger hypothesis again.

Kind `C`; hypotheses `(a)`.
Paper node: `thm:ifp` -/
theorem lic_iff_of_recognizableSupportPerturbation (P P' : History) (DP : DeductiveProcess)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hpert : RecognizableSupportPerturbation P P') :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP :=
  FreezeOracle.machine_lic_iff_of_recognizableSupport P P' DP hPcomp hP'comp hpert

end LogicalInduction
