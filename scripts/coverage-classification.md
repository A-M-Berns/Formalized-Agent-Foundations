# Logical Induction — canonical endpoints and per-label strength

This file is the **single curated source** for two of the three trust-surface artifacts.
Keeping them in one file is deliberate: they used to be maintained separately (the shown
endpoint lived in `scripts/gen-trust-surface.py`, the strength claim lived here), and every
disagreement they developed was invisible, because nothing checked that the declaration a
strength row talked about was the declaration the page displayed.

The three artifacts, and which one is which:

1. **Paper-node association / provenance** — the `Paper node:` line in a declaration's
   docstring, checked by `scripts/check-paper-nodes.sh`. Association is *not* publication:
   a declaration may legitimately carry a label and never be shown. Most do — `thm:scon`
   has 54 axiom-checked carriers and 4 canonical endpoints.
2. **Canonical public trust-surface endpoints** — the *endpoints* table below. This is the
   small curated set a skeptical reader is asked to read, and it is what
   `docs/trust-surface.html` renders with full signatures. Everything else carrying the
   label is summarised on the card by name only.
3. **Per-label strength** — the *strength* table below.

`scripts/check_endpoint_coverage.py` enforces, fail-closed:

* every non-excluded annotated label has a row in **both** tables, and no row outlives its
  label;
* every canonical endpoint name **resolves** to a declaration in `LogicalInduction/`
  (the old generator silently dropped a name that did not resolve and substituted an
  arbitrary fallback — this is the defect that hid the `thm:ifp` mis-selection);
* every canonical endpoint **carries the label it is listed under** in its `Paper node:`
  line, so a curated entry cannot drift onto an unrelated declaration;
* every canonical endpoint is **axiom-checked** — the `AxiomAudit.lean` block delimited by
  `LI-CANONICAL-BEGIN` / `LI-CANONICAL-END` must name exactly this table's endpoints, same
  spelling, no more and no less.

So a curated node can no longer fall back, and a strength claim can no longer be about a
declaration the reader never sees.

## Inventory split

`AxiomAudit.lean`'s `LogicalInduction` section now has two kinds of block:

* the **public canonical endpoint inventory** (`LI-CANONICAL-BEGIN` … `LI-CANONICAL-END`) —
  exactly the endpoints table below;
* **internal axiom regression assertions** — every other `#assert_axioms_clean` block.
  These stay under the build gate, so build coverage is unchanged and nothing lost its
  regression guard; they are simply not public trust surface. Being useful to freeze is
  not a reason to put a declaration in front of a reader.

Tier-2 (`#assert_fields`) is orthogonal to both and unchanged: it freezes the field-name
set of every structure appearing in a Tier-1 endpoint's type.

## Status vocabulary — the primary axis

The question a status answers is: **is the paper's own statement, as printed, right, and do
we prove it?** It is re-derived from the paper text, the canonical endpoint's *elaborated*
signature, and any erratum — never from a docstring.

- **exact** — the printed statement, proved. Hypotheses are the paper's own.
- **strengthened** — the printed statement and more: a weaker hypothesis, a stronger
  conclusion, or a datum the paper assumes that is constructed here instead. The row says
  which, and why the strengthening is strict where that has been proved.
- **corrected** — the printed statement is defective (an erratum), and the repaired
  statement is proved. The row names the erratum.
- **refuted** — the printed statement is **false**, and its negation is proved here. One
  node: `thm:ifp`.
- **qualified** — the one status that falls short: full strength only for a restricted
  class, or with a retained representation/operational interface, or with the paper's
  intended subject matter abstracted to a placeholder. The row says which.

## Axis — the secondary column

`universal` / `instantiated` / `n/a`. Both non-`n/a` values are at the paper's own
statement; neither is stronger than the other, and neither overrides the status.

- **universal** — proved for *every* logical inductor (`[IsLogicalInductor P DP]` or
  `[IsMachineLogicalInductor P DP]`), which is the paper's own framing for its §4 tail.
- **instantiated** — additionally instantiated over the constructed `LIA`, with the
  representation obligations discharged. Remaining premises are ones the paper itself takes
  (joint consistency, a Σ₁-sound `Θ ⊇ 𝗜𝚺₁`).
- **n/a** — definition nodes, and `thm:ifp`.

## Global model disclosure (applies to every row)

The root `README.md` keeps five things apart that all get called "a boundary" — modeling
substitution, representation interface, paper erratum, strengthening, certification
technology — and only the first is a debt against faithfulness. Sorted that way:

* The **propositional substrate** (`Formula ℕ`) is *not* a substitution: it is the paper's
  own outer language by its Notation section, with the first-order Θ entering through
  explicit interfaces.
* **`dd:fuel` on the trader class** is *not* a substitution either: the class is ordinary
  machine polynomial time (`MachineEfficientTrader`, through `Complexity.FP`), and the
  fuel-clocked calculus is certification technology proved to land inside it
  (`EfficientlyComputable.toMachine`).
* **`dd:fuel` on the property tail's own data sequences** (`RpnSentenceCodes φ`,
  `PolyRatCodes p`, `PGenerableWeighting W`, …) is a **representation interface**: it
  restricts who can supply the input, not what is proved. It is the paper's own e.c.
  requirement, is charged once at `def:ec`, and does **not** lower a row downstream. Stage
  joint consistency (`∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)`) is likewise the
  paper's own.

**The once-globally rule covers the symbol-metered class only.** `def:ec`'s faithful
rendering is `RpnSentenceCodes` (and its `LUV`/affine analogues), which meters a sentence by
its symbol count, as the paper does. The whole-value classes — `PolySentenceCodes`,
`PolyThresholdCodeSeq`, `PolyNatCodes` — meter the single pair-code token instead, and the
repo **proves** the inclusion strict (`ordinaryBitPrefixCodes` with
`not_polySentenceCodes_bitPrefixSentence` exhibit a paper-admissible e.c. sentence family no
whole-value hypothesis can be instantiated at). So a whole-value hypothesis is a genuine
class restriction and **does** lower a row. This is easy to miss: the two classes are one
coercion apart (`RpnSentenceCodes.ofPolySentenceCodes`), and the narrowed endpoints open by
applying it. Check whether the hypothesis is also passed as **data** to a quote-code
constructor, which is what forces whole-value metering and blocks the generalization.

---

<!-- table: endpoints -->

## Canonical public endpoints

Names are as `AxiomAudit.lean`'s canonical block spells them, qualified within the
`LogicalInduction` namespace. Order is the order the page shows: **the paper's own printed
form first.** A parenthetical after a name is a role note, rendered beside it on the card.

| label | canonical endpoints |
|---|---|
| def:affcomsen | `AffineCombination` |
| def:bap | `AffineCombination.BoundedCombinationSequence` |
| def:blcp | `LUVCombination.BoundedSequence`; `PaperLUVCombination.boundedSequence` (literal paper LUVs); `unitFracPaperLUVBoundedSequence` (non-vacuity witness) |
| def:dedproc | `DeductiveProcess`; `DeductiveProcessComputation` (the paper's "computably enumerable") |
| def:deferralfunc | `DeferralFunction` |
| def:ec | `MachineEfficientTrader` (the paper's own class); `EfficientlyComputable` (`dd:fuel` certification device); `EfficientlyComputable.toMachine` (the inclusion) |
| def:ece | `GeneratedRatFeature` |
| def:fuz | `PGenerableWeighting` |
| def:lia | `liaStates`; `liaHistory` |
| def:lic | `IsMachineLogicalInductor` (the paper's own quantifier); `IsLogicalInductor` (fuel-class compatibility reading) |
| def:luv | `PaperLUV` (the literal object); `LUV` (the abstract threshold carrier); `unitFracPaperLUVSeq` (non-vacuity witness) |
| def:trader | `Trader` |
| def:tradestrat | `Strategy` |
| lem:mesh | `LUVCombination.BoundedSequence.mesh_independence_ofSyntax` |
| lem:tfdom | `trading_firm_dominance` |
| thm:affcoh | `AffineCombination.PolySequence.affcoh` |
| thm:affpolymax | `AffineCombination.BoundedCombinationSequence.affpolymax` |
| thm:affprovind | `AffineCombination.PolySequence.affine_provind_theory_ge` (the printed display); `AffineCombination.PolySequence.affine_provind_theory_le`; `AffineCombination.PolySequence.affine_provind_theory_eq` |
| thm:benford | `lic_learning_pseudorandom_frequency` (the printed `≈ₙ`); `lic_learning_pseudorandom_frequency_above`; `lic_learning_pseudorandom_frequency_below` |
| thm:ccee | `lic_no_expected_net_update_conditional_closed_exact` |
| thm:cee | `lic_expected_future_expectations_closed` |
| thm:ceu | `lic_no_expected_net_update_closed` |
| thm:con | `lic_limitingBelief_tendsto` (names the limit `ℙ∞`); `lic_price_convergesTo` |
| thm:dontwait | `lic_does_not_anticipate_halting_unconditional` |
| thm:dus | `lic_domination_universalSemimeasure_ofIndependentAtoms`; `lic_domination_universalSemimeasure` |
| thm:ec | `LUV.expect_converges` |
| thm:ei | `lic_expectation_indicator` |
| thm:epr | `lic_expectations_of_probabilities_closed` |
| thm:er | `lic_iterated_expectations_closed` |
| thm:expcoh | `LUVCombination.BoundedSequence.expcoh_ofSyntax` |
| thm:exppolymax | `LUVCombination.BoundedSequence.exppolymax_ofSyntax` |
| thm:expprovind | `lic_expect_combination_provind_ge` (the printed display); `lic_expect_combination_provind_le`; `lic_expect_combination_provind_eq` |
| thm:halts | `lia_learns_halting_patterns_unconditional` |
| thm:ifp | `FinitePerturbationCounterexample.not_overgeneral_ifp` (**refutes the printed theorem**); `FreezeOracle.machine_lic_iff_of_recognizableSupport` (**the corrected theorem**); `LIAPerturbation.machineLogicalInductor_liaPerturbed` (the corrected theorem doing work) |
| thm:incons | `lic_disbelief_inconsistent_theories_unconditional` |
| thm:lc | `lic_limitCoherence` |
| thm:lex | `lic_learning_exclusive_exhaustive` |
| thm:li | `exists_computable_beliefSequence_logical_inductor`; `exists_machine_logical_inductor` |
| thm:lia | `LIA_isMachineLogicalInductor` (the paper's own quantifier); `LIA_is_logical_inductor` (its fuel-class projection) |
| thm:loe | `lic_linearity_of_expectation_seq` |
| thm:loops | `lic_learns_provable_nonhalting_patterns_unconditional` |
| thm:lp | `lic_paradox_resistance_ofDiagonal_unconditional` |
| thm:nd | `lic_nonDogmatism`; `lic_nonDogmatism_dual` |
| thm:ob | `UPrefix.lic_occamBounds_ofUniversalPrefix` |
| thm:obu | `lic_uniform_nonDogmatism_ofCE`; `lic_uniform_nonDogmatism` |
| thm:pac | `lic_belief_finitistic_consistency_unconditional` |
| thm:pazfc | `lic_belief_stronger_theory_consistency_unconditional` |
| thm:peraffkno | `AffineCombination.PolySequence.peraffkno` |
| thm:perexpkno | `LUVCombination.BoundedSequence.perexpkno_ofSyntax` |
| thm:perkno | `lic_persistence_of_knowledge` |
| thm:prand | `lic_learning_varied_pseudorandom` (the printed `≈ₙ`); `lic_learning_varied_pseudorandom_above` (erratum PE5: centering inverted); `lic_learning_varied_pseudorandom_below` (erratum PE5) |
| thm:prandaff | `AffineCombination.BoundedCombinationSequence.prandaff_above` (the printed display); `AffineCombination.BoundedCombinationSequence.prandaff_below`; `AffineCombination.BoundedCombinationSequence.prandaff` |
| thm:prandexp | `LUVCombination.BoundedSequence.prandexp` (the printed display); `LUVCombination.BoundedSequence.prandexp_below`; `LUVCombination.BoundedSequence.prandexp_eq` |
| thm:provind | `lic_provind` |
| thm:recunbiasedaff | `AffineCombination.BoundedCombinationSequence.recunbiasedaff` |
| thm:recurringunbiasedness | `AffineCombination.recurringunbiasedness` |
| thm:recurringunbiasednessexp | `LUVCombination.BoundedSequence.recurringunbiasednessexp` (repairs erratum PE2) |
| thm:ref | `lic_introspection_closed` (quote constructed from the market program); `lic_introspection` (quote as caller interface) |
| thm:scon | `ConditioningCompile.lic_conditioned_fixed_machine_ofComputationAndMarket` (printed form, half 1); `ConditioningCompile.lic_conditioned_growing_machine_ofComputationsAndMarket` (printed form, half 2); `lic_conditioned_fixed_machine_unconditional`; `lic_conditioned_growing_machine_unconditional` |
| thm:simcal | `AffineCombination.simcal`; `AffineCombination.sentenceAffine_polySequence` (discharges `hpoly` from the paper's e.c. hypothesis); `calibrationIndicator_pgenerable` (discharges `hWgen`; proves tex:1188) |
| thm:st | `lic_self_trust_closed` |
| thm:strict | `lic_strict_domination_universalSemimeasure_ofAtomCodes`; `lic_strict_domination_universalSemimeasure` |
| thm:tbo | `lic_preemptive_learning` |
| thm:wub | `FeedbackTruth.lic_wub_ofComputation` (universal); `FeedbackTruth.lic_wub_ofComputation_unconditional` (over `LIA`) |
| thm:wubaff | `FeedbackTruth.boundedCombination_wubaff_ofComputation` (universal, any `BCS`); `FeedbackTruth.boundedCombination_wubaff_ofComputation_unconditional` (over `LIA`) |
| thm:wubexp | `FeedbackTruth.luv_wubexp_ofComputation` (universal); `FeedbackTruth.luv_wubexp_ofComputation_unconditional` (over `LIA`) |

---

<!-- table: strength -->

## Per-label strength

| label | status | axis | justification |
|---|---|---|---|
| def:affcomsen | exact | n/a | direct rendering: a constant feature plus a list of feature/sentence terms, with features as `EF` expression trees so that generability is syntactic |
| def:bap | exact | n/a | direct rendering of the paper's two clauses: `poly` is the e.c. certificate on the combination sequence, `bounded` the single uniform `ℓ¹` bound |
| def:blcp | exact | n/a | direct rendering of the paper's two clauses — an efficiency certificate on the compiled threshold mesh plus one uniform `L¹` bound — and stated over the paper's own LUVs as well as the abstract carrier: `PaperLUVCombination` carries its shares as literal `PaperLUV`s and reaches `LUV` only through `toLUV`, `boundedSequence` discharges the bounded-sequence interface from that data with the family's own structural threshold certificate, and `unitFracPaperLUVBoundedSequence` inhabits it with the genuinely varying `1/(n+1)` family. The carrier-level charge that used to sit here is gone, on the same footing as `def:luv`'s |
| def:dedproc | exact | n/a | `D` and `mono` are the paper's nondecreasing finite sets; "computably enumerable" lives in the separate certificate `DeductiveProcessComputation`, taken as a hypothesis exactly where the paper says "computable deductive process" |
| def:deferralfunc | exact | n/a | `n < f n` with the emitter clocked polynomially in the *output* `f n`, as the paper asks, so `f` may grow fast |
| def:ec | qualified | n/a | **The trader half is closed.** `MachineEfficientTrader` is an honest complexity class — some `Complexity.FP` function of the *unary* day emits the day's strategy — and it is the class the construction dominates: the trader enumeration is sound and complete for exactly it (`enumeratedTrader_machineEfficient`, `exists_enumeratedTrader_eq`), and `IsMachineLogicalInductor` is what `LIA_isMachineLogicalInductor` proves. `dd:fuel` is a certification device for that class (`EfficientlyComputable.toMachine`), not a substitution for it. What qualifies the row is the other half: the efficiently computable *sequence* classes the property tail takes as its own data (`RpnSentenceCodes`, `RpnThresholdCodes`, `PolySequence`, …) are still the symbol-metered fuel rendering, so those statements quantify over a possibly smaller set of admissible data than the paper's. The machine reading exists (`MachineSentenceCodes`, with the inclusion `RpnSentenceCodes.toMachine`) but is consumed only at `thm:scon`; the converse inclusion is open. This is the global fuel charge, levied here and nowhere else |
| def:ece | exact | n/a | direct rendering of market-generability: rank bound, emitter, closure, denotation — nothing retained beyond the global fuel model |
| def:fuz | exact | n/a | direct rendering of a generable weighting: the same data as `def:ece` minus the denotation clause, so a trader can trade on the weighting without knowing its values |
| def:lia | exact | n/a | the recursion itself: `liaStates DP n` is the market maker's fixed point against the trading firm run on the history of days `< n`, and `liaHistory` is the market it induces. The three components are separate audited constructions; `thm:lia` certifies the assembly |
| def:lic | exact | n/a | `IsMachineLogicalInductor` states the criterion at the paper's own quantifier — no `Complexity.FP` trader exploits the market — and is the criterion the construction proves. Its field set is frozen at Tier 2 alongside `IsLogicalInductor`, the fuel-class compatibility reading reached from it by `IsMachineLogicalInductor.toIsLogicalInductor`; the fuel class is what the whole §4 tail is *conditioned* on, which makes those theorems stronger, not weaker. Both bundle two facts the paper leaves ambient — the market and the process are computable |
| def:luv | exact | n/a | `PaperLUV` is the paper's object literally: an `ArithmeticSemisentence 1` carrying object-level `T`-proofs of unique existence and `[0,1]` membership. `toLUV` compiles it into the abstract threshold carrier `LUV` (field `gt`) that downstream results consume; `PCWorld.ValuesAt` is *derived* through `paperTheoryDP` and the rational cut rather than assumed, and `PaperLUVSeq` compiles the literal threshold syntax to `RpnThresholdCodeSeq`. Inhabited by a varying `1/(n+1)` family. The abstract `LUV` is shown second precisely because it is the over-general one |
| def:trader | exact | n/a | a trader is its day-indexed strategy function; all economic content (holdings, exploitation) is derived, matching the paper's reading of a trader as a strategy sequence |
| def:tradestrat | exact | n/a | direct rendering: `trades` is the paper's `ξ₁φ₁ + …`, `rank_le` the paper's rank condition that an `n`-strategy mentions only prices of days `≤ n` |
| lem:mesh | exact | universal | `mesh_independence_ofSyntax` retains `[IsLogicalInductor]`, the `def:blcp` bounded sequence, and `S : LUVCombinationSyntax` — the paper's own ℙ-generable presentation, inhabited by `ordinaryLUVCombinationSyntax`. It is cleaner than the sibling `mesh_independence`, which additionally demands a `MeshSoftmaxOperationalWitness` and an explicit rational bound |
| lem:tfdom | strengthened | universal | no inductor hypothesis, as in the paper: any rational `[0,1]` market exploited by *some* efficient trader is exploited by the firm. Strengthened because the exploiter hypothesis is `MachineEfficientTrader`, the *larger* class, hence the weaker premise; the fuel-class corollary `trading_firm_dominance_of_ec` is correctly internal. The enumeration covering the whole class is `exists_enumeratedTrader_eq` |
| thm:affcoh | exact | universal | analytic capstone over `[IsLogicalInductor]` with the paper's bounded-combination data. `BoundedCombinationSequence` is *defined* as `PolySequence` + `L¹` bound, so stating the endpoint over `PolySequence` + `BoundedAffinePrices` + a magnitude bound is a decomposition of the paper's class, not a narrowing |
| thm:affpolymax | strengthened | universal | same conclusion shape as the paper, but over the bare `BoundedCombinationSequence`: the price and magnitude bounds are derived from the sequence rather than assumed |
| thm:affprovind | exact | universal | the printed display is `≳ₙ`, "and similarly for `=`/`≈ₙ` and `≤`/`≲ₙ`", so all three directions are the node. `_ge` is shown first because it is the printed one; `_eq`'s hypothesis (`value = b`) implies both one-sided ones and its body is `asympEq_iff_asympLE_asympGE` over them, so it is the weakest of the three and sits last |
| thm:benford | strengthened | universal | `PseudorandomFrequency` quantifies only over additionally `DeferralPatient` weightings — a *weaker* premise than `def:pseudorandom`, hence a stronger theorem; `f = n+1` recovers the paper's case. Clock-free: maturity and settlement are constructed internally. The paper's headline is `≈ₙ`, so the two-sided form leads |
| thm:ccee | exact | instantiated | `lic_no_expected_net_update_conditional_closed_exact` takes exactly the paper-facing source interface (`X : ℕ → LUV`, `RpnThresholdCodeSeq X`, completed-world `source_valued`), a bare `DeferralFunction`, and a ℙ-generable `[0,1]` weight. Zero slack — the generic `_ofRepresentation_unconditional` carries a vanishing `slack` and an approximation premise; this signature has neither — and no caller-visible freshness or proof-carrying certificate, unlike the sibling `lic_no_expected_net_update_conditional_exact_closed`, which demands `ProductAtomFresh X` and a caller-supplied extension. The sole market is `liaHistory (canonicalCCEEDP T)`, whose computable, explicitly non-vacuous process is fixed from `T` before `X`, `f`, or `w`; one canonical enlarged language from the outset, not a source-dependent extension. **Disclosed gap:** the process side of non-vacuity is witnessed (`canonicalCCEEDP_computable`, `canonicalCCEEDP_hworld`), but there is no witness that this endpoint's `weight_generable` hypothesis is inhabited by a non-constant weight — the only such N+, `lic_no_expected_net_update_conditional_exact_closed_nonvacuous`, lives over `exactProductDP`, not over `canonicalCCEEDP` |
| thm:cee | exact | instantiated | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq`, with the deferred-expectation quote constructed and a bare `DeferralFunction` (`f n > n`, as `def:deferralfunc` asks). The only remaining premise is the paper's own "the source is an LUV of the theory" (`source_valued`) |
| thm:ceu | exact | instantiated | the cleanest endpoint in the paper: exactly a deferral function, the sentence sequence, and its `RpnSentenceCodes`. The quote code is constructed; no reflection data and no deferral narrowing |
| thm:con | exact | universal | genuine trader proof over `[IsLogicalInductor]`; the oscillation trader is constructed inside the proof, and the statement carries only the criterion instance and stage consistency. `lic_limitingBelief_tendsto` leads because the paper's statement *defines* `ℙ∞(φ) := lim ℙₙ(φ)`, and `limitingBelief` is the `ℙ∞` that `thm:lc`, `thm:perkno`, `thm:nd` and `thm:ob` consume downstream; `lic_price_convergesTo` proves the same fact in bare `∃ L` form |
| thm:dontwait | strengthened | instantiated | unconditional over `LIA` on the provability process (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`), at the paper's own horizon class. The horizon hypothesis is `hh : ComputableHorizon horizons` and nothing else — program plus specification, no growth bound — so **any** computable `f` (tex:1946-1952) is admissible, where the former `PolyNatCodes horizons` restricted it to polynomial time. The strengthening is *proved strict*: `ComputableHorizon.ackermann` is admissible and `not_polyNatCodes_ack` shows the old class excluded it. The claim's Gödel name pairs the constant `⌜f⌝` with `n` unevaluated and the arithmetic schema does the evaluation, exactly as the paper writes `⌜f⌝(⌜n⌝)`. Genuine subject matter: `machines : ℕ → Nat.Partrec.Code` with a real non-halting hypothesis |
| thm:dus | exact | universal | quantifies over **any** `DP` and any `[IsLogicalInductor P DP]`, the paper's own generality. Inputs are the paper's semantic premise `IndependentBitAtoms`, the naming certificate, and the semimeasure's from-below presentation; prefix codes are symbol-metered and inhabited. Not `instantiated`: the three `_unconditional` forms all fix `DP = emptyBitDeductiveProcess`, and the paper frames the node as fresh symbols added *to* `Θ`, so `Θ = ∅` is the degenerate case |
| thm:ec | exact | universal | retains `[IsLogicalInductor]`, the paper's own `def:ec` threshold codes, stage joint consistency, and `def:luv`'s world-value fact at the paper's `cworlds(Θ)` quantifier (`∀ v, v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x`). The limit is constructed, not assumed. The former stage-quantified per-grid premise is gone and needed no compactness entailment to remove: the proof reads a world value only inside `filter_upwards [hae]`, where `hae` is `lic_limitCoherence`'s a.e. support on completed-theory worlds |
| thm:ei | exact | universal | the paper's varying-sequence statement, genuine trader proof over `[IsLogicalInductor]`. `LUV.IsIndicator` quantifies over `v.ConsistentWithTheory DP` — completed worlds — which is exactly `app:ei`'s own quantifier (tex:5229) and not the stronger every-stage reading, which `indicatorWitness_not_stagewise` shows would exclude the paper's own indicator; `indicatorWitness_isIndicator` exhibits a non-degenerate inhabitant |
| thm:epr | exact | instantiated | unconditional over `LIA` at `def:ec`'s own symbol-metered class; the quote code is constructed from the market program (`theoremPriceQuoteCode`), leaving exactly `φ` and `RpnSentenceCodes φ` |
| thm:er | exact | instantiated | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq`; the expectation quote code is constructed via `expectQuote_computable`, leaving exactly `X` and its threshold codes |
| thm:expcoh | exact | universal | retains `[IsLogicalInductor]`, the `def:blcp` bounded sequence, `S : LUVCombinationSyntax`, and `WorldValued` — the paper's own `def:luv` fact at `cworlds(Θ)`. `S` is the paper's own ℙ-generable presentation and is inhabited by `ordinaryLUVCombinationSyntax`, so it is not a retained interface. Nothing stage-quantified survives anywhere in the transitive premise set: `ConvergencePresentation.daily_value` became `world_value`, the upstream `TheorySemantics.stage_values` field was deleted, and the `ConvergencePresentation` argument is gone from the signature. Dominates the sibling `expcoh`, which additionally demands a `MeshSoftmaxOperationalWitness`, per-term threshold codes and an explicit bound |
| thm:exppolymax | exact | universal | same premise set as `thm:expcoh` — the bounded sequence, `S : LUVCombinationSyntax`, and `WorldValued` — with the operational witness discharged; `exppolymax_arith` additionally discharges `WorldValued` for the certified class |
| thm:expprovind | exact | universal | the printed display is `≳ₙ`, "and similarly for `=`/`≈ₙ` and `≤`/`≲ₙ`", so all three directions are the node and all three are shown, `_ge` first. Each takes precisely tex:1753-1757's one-sided bound at `cworlds(Θ)`, with each completed world free to pick its own valuation; `DeterminedViaTheory` is gone from them. The `_ofDetermined` variants take the *stronger* determinacy hypothesis, hence are weaker theorems and are internal; the fixed-LUV `lic_expectation_provind*` quantify over stage-plausible worlds and are a separate, weaker rendering |
| thm:halts | exact | instantiated | unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`), with real subject matter: `machines : ℕ → Nat.Partrec.Code` and a genuine `CodeHalts` hypothesis. The two e.c. class hypotheses are the paper's, and nothing bounds an individual machine's runtime, matching tex:1931 |
| thm:ifp | refuted | n/a | **The printed theorem is false, and the corrected theorem is proved.** `not_overgeneral_ifp` negates exactly the printed quantifier — `∀ P P' DP N, IsMachineLogicalInductor P DP → ComputableMarket P' → tail agreement → IsMachineLogicalInductor P' DP` — with no theory parameter, `sorry`-free and axiom-clean, using the constructed `LIA` as the inductor and a day-`0` advice tape as the perturbation. The published proof's invalid step is the "only finitely many constants" claim at tex:6047-6062; the ledger is `notes/paper-errata.md` PE1. The **corrected** theorem is `FreezeOracle.machine_lic_iff_of_recognizableSupport`: two computable markets differing on only finitely many `(day, sentence)` coordinates satisfy the criterion together — strictly stronger than the paper's tail agreement in the direction that survives, and exactly the case where the appendix's constant table really is finite. It takes **no** patch argument, discharging the two `MachineFiniteSupportPatch` inputs of `machine_lic_iff_of_finiteSupportPerturbation` internally. Its one residual hypothesis, `Recognizable`, is a condition on the *syntax* of the finitely many moved sentences, not on any market: representation residue standing for two `Complexity.FP` primitives this toolkit lacks (integer square root, a structured-payload parser), both proved necessary rather than convenient. `machine_lic_iff_twoPoint` makes it non-vacuous and `machineLogicalInductor_liaPerturbed` makes it informative — applied to `LIA` with one price moved, it derives a machine logical inductor no construction here produces. Deliberately **not** canonical: the fuel-class carriers `lic_iff_of_finitePerturbation` and `lic_iff_of_finiteSupportPerturbation`, whose `EfficientPrefixPatch`/`FiniteSupportPatch` hypotheses are *uninhabited* at the `dd:fuel` inverse-operation ceiling, and `machine_lic_iff_of_finiteSupportPerturbation`, which the corrected theorem supersedes. They remain axiom-checked internals |
| thm:incons | qualified | instantiated | unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`), and both conjuncts of the paper's display are delivered. Qualified for the same reason as `thm:pac`: `SemidecidableComputation` presents an *arbitrary* semidecidable predicate `inconsistent : ℕ → Prop`, not a proof-search-for-`⊥`; the only N+, `ordinarySemidecidableComputation`, is "`0 < n`", so the paper's intended sequence of inconsistency claims is never exhibited. Additionally, `inconsistencySentence` and `consistencySentence` are independent families rather than syntactic negations — a documented, honest weakening |
| thm:lc | exact | universal | the measure `μ` plays the paper's `Pr`: a genuine probability measure on completed worlds, constructed rather than assumed, agreeing with `limitingBelief` on every sentence event and (a.e.) supported on worlds consistent with `Γ`. All three paper clauses in one theorem, over `[IsLogicalInductor]` plus `hworld` |
| thm:lex | exact | universal | propositional rendering over `[IsLogicalInductor]`; the exclusive-exhaustive premise is the completed-world payout-sum rendering, disclosed at the site |
| thm:li | strengthened | instantiated | sole hypothesis is a computable deductive process. The conclusion mirrors `def:belseq` — one `Nat.Partrec.Code` emits each day's finite association list, supports are finite, quotes are rational in `[0,1]` — *and* concludes `IsMachineLogicalInductor`, the paper's own quantifier. Strengthened in the `def:belseq` emission conjunct relative to the bare existence forms |
| thm:lia | exact | instantiated | the central construction, kernel-clean; the sole premise is a computable deductive process. `LIA_isMachineLogicalInductor` leads because it concludes the paper's own quantifier — `LIA_is_logical_inductor` is literally its `toIsLogicalInductor` projection, and showing only the projection contradicted the sibling node `thm:li`, which already shows the machine class |
| thm:loe | exact | universal | the paper's varying-sequence form: `a b : ℕ → ℚ` and `X Y Z : ℕ → LUV`. `Θ ⊢ Zₙ = aₙXₙ + bₙYₙ` is `DeterminedViaTheory` on the linearity combination (= paper `def:affthmval`), and `WorldValued` is `def:luv`'s own fact. The fixed sibling `lic_linearity_of_expectation` quantifies its hypothesis over *stage*-plausible worlds — a strictly stronger premise, correctly internal |
| thm:loops | exact | instantiated | unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`); the hypothesis is literal object-level `T`-provability of non-halting, not a deductive-process emission surrogate |
| thm:lp | strengthened | instantiated | the paradoxical sequence is **constructed** (`theoremDiagonalQuoteCode`, by Gödel fixed point from the market computation) where the paper merely posits one, and the whole result is closed over `LIA`. The extra width premises are universally quantified and the class is inhabited (`harmonicWeight_polyRatCodes`) |
| thm:nd | strengthened | universal | the conclusion `∃ ε > 0, ∀ᶠ n, ε ≤ ℙₙ(φ)` is stronger than the paper's limit claim; the literal `ℙ∞` forms `lic_limit_pos`/`lic_limit_lt_one` are corollaries needing a `ConvergesTo` input and are internal. The plausibility premise is the paper's own, made stagewise |
| thm:ob | exact | universal | paper-strength bounds at genuine universal prefix complexity `κ_U`, with `prefixWeight κ φ = 1/2^(κ φ)` literally the paper's `2^(−κ)`. Invariance is proved (Kraft, the negation compiler, the invariance theorem); presentation and threshold emission are constructed, so only `[IsLogicalInductor]` and stagewise plausibility survive. Both halves in one statement. No `_unconditional` Occam endpoint exists anywhere, so nothing stronger is available |
| thm:obu | exact | universal | `_ofCE` takes the paper's own premises (tex:1540-1546): a c.e. source — `CEEnumeration`, a program whose dovetailed run returns `⌜source i⌝` at every index, with no clock — plus stagewise joint consistency of `Γ ∪ φ̄`, and concludes the paper's `ε` and `ℙ∞`. The padded efficient repetition the paper builds *inside* its proof (tex:5651-5656) is constructed by `EfficientRepeatedEnumeration.ofCE`, so `lic_uniform_nonDogmatism`, which assumes that structure directly, is the strictly stronger premise and sits second |
| thm:pac | qualified | instantiated | unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`), and the **horizon class is the paper's**: `BoundedComputation` carries `horizon : ComputableHorizon steps` — the program `⌜f⌝` and its specification, no growth bound — in place of the former `steps_poly : PolyNatCodes steps`, and `not_polyNatCodes_ack` proves that generalization strict. The deferred-horizon schema is what makes it possible: the claim name pairs the constant `⌜f⌝` with `n` unevaluated. `PolyNatCodes input` remains, on the paper's own e.c. input sequence. **What qualifies the row:** nothing in the statement is about the consistency of a theory. `consistentWithin` is an *arbitrary* decidable predicate and the sentence family is built by `representedDecidableClaimsOfComputation` from an arbitrary bounded machine; no `BoundedComputation` instance for a proof-search-for-`⊥` machine exists anywhere in the repo, and the sole N+, `ordinaryBoundedComputation`, is "`Code.zero` halts within `n` steps". The endpoint *implies* the paper's theorem for a reader who supplies the `Con`-machine; that instance is not constructed here |
| thm:pazfc | qualified | instantiated | **This node and `thm:pac` are discharged by one and the same proposition.** The elaborated signature of `lic_belief_stronger_theory_consistency_unconditional` is identical to `thm:pac`'s up to renaming the binder `consistentWithin` to `strongerConsistentWithin`, and the underlying `_ofComputation` pair is the same shape — the source's own docstring says so. There is no second theory `Θ′` anywhere in the statement, and nothing prevents `Θ′ = Θ`. Everything in the `thm:pac` row about the arbitrary decidable predicate applies verbatim; the `ComputableHorizon` half of the strength claim is verified the same way |
| thm:peraffkno | exact | universal | analytic capstone over `[IsLogicalInductor]`; sole carrier, hypotheses are the paper's |
| thm:perexpkno | exact | universal | same premise set as `thm:expcoh` — the `def:blcp` bounded sequence, `S : LUVCombinationSyntax`, `WorldValued` — and the same repair: the `ConvergencePresentation` argument is gone from the signature rather than merely derivable |
| thm:perkno | exact | universal | over `[IsLogicalInductor]` with the paper's own e.c. probability sequence. The conclusion is a **three**-way conjunction matching the paper's three displayed clauses (`≈`, `≲` and `≳` against the future sup/inf) clause for clause; `limitingBelief P (φ n)` is `ℙ∞(φₙ)` |
| thm:prand | corrected | universal | clock-free varied-frequency form; the target rationals enter as a market-generable feature (`def:ece`), as the paper requires, and the two-sided `≈ₙ` headline is exact. **Erratum PE5:** the centering of the one-sided notions is *inverted* relative to the printed `def:seqprand`, which displays the weighted average of `(pᵢ − ThmInd(φᵢ))` and calls its `≳ₙ` form "varied pseudorandom *above*". With the paper's centering, `def:seqprand`'s `≳ₙ` and `thm:prand`'s `ℙₙ(φₙ) ≳ₙ pₙ` point in opposite directions; the repo centers the other way (`VariedPseudorandomAbove truth p := PseudorandomAbove (truth − p)`), which is what the exploiting-trader argument needs and what makes the paper's advertised conclusion come out right. The `≈ₙ` form is unaffected, being sign-symmetric |
| thm:prandaff | exact | universal | clock-free: the patient settlement clock is constructed from the inductor, leaving exactly the paper's bounded-combination, determination and pseudorandomness premises. The printed display is `≳ₙ`, "and similarly for `≈ₙ` and `≲ₙ`", so `prandaff_above` leads; the two-sided `prandaff` sits last because its hypothesis is the conjunction of the two one-sided ones and its body is `asympEq_iff_asympLE_asympGE` over them |
| thm:prandexp | exact | universal | retains `WorldValued` (paper `def:luv`) and `DeterminedViaTheory` (paper `def:affthmval`, tex:1807); the clock is constructed. The paper prints only the `≳` direction, so `prandexp` leads and the `_below`/`_eq` forms follow |
| thm:provind | exact | universal | both halves of the paper's statement in one theorem, with `RpnSentenceCodes` on both sequences. "Sequence of theorems" becomes `∀ n, ∃ k, φ n ∈ DP.D k` — each `φₙ` eventually appears in the process — and dually for the disprovable `ψₙ`, which is the paper's eventual-deducibility premise |
| thm:recunbiasedaff | exact | universal | maturity constructed internally; clock-free, and no verifier premise remains |
| thm:recurringunbiasedness | exact | universal | same, over the sentence-affine family. Despite the namespace this is genuinely sentence-level — `φ` is lifted by `sentenceAffine` — not an affine substitution |
| thm:recurringunbiasednessexp | corrected | universal | same premises as `thm:prandexp`, both the paper's own. **Erratum PE2:** the printed statement (tex:1812-1820) is garbled — it carries a spurious "support of `⟨w⟩ ⊆ image of f`" clause referring to an `f` the statement never introduces, a clause that belongs to `thm:wubexp` and is missing there. The Lean statement is the repair: no deferral function, no support clause, concluding `HasLimitPoint 0` |
| thm:ref | exact | instantiated | unconditional over `LIA` at `RpnSentenceCodes`, with the interval quote constructed from the market's exact rational quote. Its hypotheses are exactly the paper's (tex:1969-1981): ℙ-generable interval bounds via their market-generated feature presentations, an e.c. sentence sequence, the vanishing width, and the range side conditions. Two `PolyRatCodes` hypotheses formerly stood on `ā` and `b̄`; they were **redundant** — consumed only as `.computable`, which `PGenerableRat.computable` supplies from the `MarketComputation` already in scope, the route `thm:st` already took — and have been removed. **PE6** records the separate fact that the paper's *own proof* needs more than the paper states: `app:ref` applies `thm:affprovind` to a combination over sentences containing `⌜aₙ⌝`, `⌜bₙ⌝`, which requires those numerals efficiently writable, whereas ℙ-generability gives a feature whose value at the market is the bound. This formalization escapes that gap rather than inheriting it: the quoted sentence is a code-indexed atom (`dd:quote-code`), so its emission cost does not depend on the bounds |
| thm:scon | strengthened | instantiated | both halves at the paper's own quantifier. The two printed forms `lic_conditioned_fixed_machine_ofComputationAndMarket` / `lic_conditioned_growing_machine_ofComputationsAndMarket` are universal over `[IsMachineLogicalInductor P DP]` with **no** consistency hypothesis — the degenerate branch is `isMachineLogicalInductor_of_stage_unsatisfiable` — and the growing-form `hjoint` is gone, derived by propositional compactness (`Framework/Compactness.lean`). Their premise-free instances over the constructed `LIA` take exactly the hypotheses of the fuel-class pair `lic_conditioned_{fixed,growing}_unconditional` — `(T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]` and the condition, no inductor hypothesis — and conclude the strictly stronger `IsMachineLogicalInductor`, discharging the base by `LIA_isMachineLogicalInductor` where the fuel forms use `LIA_is_logical_inductor`. The machine transports are `conditionedTranslation_preserves_machine` and `eventualConditionedTranslation_preserves_machine`, under the same `RpnSentenceCodes` hypothesis on the condition as the fuel counterparts; the fuel endpoints and their inhabited witnesses are unchanged beside them, so this is a strengthening, not a replacement. (For the *general* forms the machine/fuel swap is on both sides of a closure implication, so those pairs are incomparable; the closed pair is where domination is strict) |
| thm:simcal | exact | universal | maturity is constructed internally, and the endpoint's hypotheses are reachable from exactly the paper's: `AffineCombination.simcal` takes `hpoly : PolySequence (sentenceAffine φ)` and `hWgen : PGenerableWeighting (calibrationIndicator φ a b δ)` as arguments, and both are *proved* here from the paper's own "`⟨φ⟩` is an e.c. sequence of decidable sentences" and "`⟨δ⟩` is an e.c. sequence of positive rationals" — by `AffineCombination.sentenceAffine_polySequence` and `calibrationIndicator_pgenerable` respectively, both shown on this card. (`calibrationIndicator_pgenerable` is exactly the fact tex:1188 asserts without proof.) They are arguments rather than a collapsed single endpoint, which is an ergonomic wart, not a strength loss: no collapsed endpoint exists |
| thm:st | exact | instantiated | unconditional over `LIA` with every representation obligation discharged: the `SelfTrustQuote` reflection data is constructed (`theoremConfidenceQuoteCode`), the quoted product LUV is symbol-metered (`indicatorProductLUV_rpnThresholdCodeSeq` emits the `⋏`-shell as tokens rather than as a `Nat.pair` on Gödel values), and the reciprocal code is *derived* (`PolyRatCodes.inv_of_pos`). The remaining hypotheses are exactly tex:2093's four: a deferral function, an e.c. sentence sequence, an e.c. sequence of positive rationals, and a ℙ-generable rational probability sequence. Note `p` carries only generability, no `PolyRatCodes`, so the `thm:ref` narrowing does **not** recur here |
| thm:strict | exact | universal | paper strength for **any** `DP` and any inductor. `_ofAtomCodes` needs only computability of the atoms' Gödel codes, `[IsLogicalInductor]` and `0 < C`, building the separator presentation internally via `strictSeparatorPresentationOfKleene`; the separator argument is fully constructed (Kleene's recursively inseparable pair, the constraint enumerator from the atom codes, and the stage classes proved null by the Kučera–Demuth argument rather than assumed). The bare form takes `S : StrictSeparatorPresentation M B` as an explicit caller input and is therefore weaker as a usable statement, so it sits second. Not `instantiated`, for the same reason as `thm:dus`: the `_unconditional` form is over the constantly-empty deductive process |
| thm:tbo | exact | universal | over `[IsLogicalInductor]`; the `sSup`/`sInf` over `fun j => P (n + j) (φ n)` are the paper's sup/inf over `m ≥ n` of `ℙₘ(φₙ)`, and the conclusion is the paper's two liminf/limsup identities verbatim |
| thm:wub | exact | universal | `lic_wub_ofComputation` is universal over `[IsLogicalInductor]` with exactly tex:1249-1258's premises plus `hworld`: a ℙ-generable divergent weighting, a strictly increasing deferral function whose image contains the weighting's support, and timed feedback (`FeedbackTruthComputation`, rendered with a *polynomial* clock at `f(k+1)`, i.e. a weaker hypothesis than the paper's `O(f(n+1))`). It leads for that reason. The `_unconditional` form buys the discharge of `hworld` at the price of three arithmetic-theory class hypotheses the paper does not impose, and of no longer being about all inductors; it is shown second rather than alone |
| thm:wubaff | exact | universal | `boundedCombination_wubaff_ofComputation` takes a plain `BoundedCombinationSequence` — the paper's `⟨A⟩ ∈ 𝓑𝓒𝓢` at any bound — and rescales internally through `h.unitNormalization.scale`; emitter and truth bridge are constructed, leaving the paper's own timed-feedback premise `FeedbackTruthComputation`. It leads because the unit-magnitude siblings `lic_wubaff_ofComputation(_unconditional)` carry `∀ i, (As i).magnitude P ≤ 1` plus a separate `BoundedAffinePrices`, a normalization the paper's `𝓑𝓒𝓢` does not impose; the repo's own docstring calls the bounded-combination form "paper-facing", and it is now the one shown |
| thm:wubexp | exact | instantiated | the normalized threshold mesh, its feedback traders, and its sparse delayed-truth affine family (the one the paper builds *inside* `app:wub`) are all constructed. The remaining premises are exactly tex:1822-1832's — a bounded LUV-combination sequence determined via `Θ` at the *combination* level (`def:affthmval`), the `def:luv` premise `WorldValued`, a ℙ-generable divergent weighting supported on the image of a strictly increasing deferral function, and timed feedback (polynomial clock at `f(k+1)`, as for `thm:wub`). Determination is at the combination level only, so `[(1, X), (-1, X)]` for a wholly undetermined `X` is covered, which it would not be under `LUVCombination.ExactTheoryPresentation`; meshing is nonlinear, so the bridge is built at `ApproxDeterminedViaTheory` with the vanishing `meshErrorBound` (`lem:conluvapprox`). The universal form over any inductor leads; the `LIA`-closed form follows. Note the paper's printed statement is missing the support-⊆-image clause that belongs here (erratum PE2); the Lean carries it, correctly |
