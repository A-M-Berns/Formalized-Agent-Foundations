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
* **`dd:fuel` on the property tail's own *symbol-metered* data sequences**
  (`RpnSentenceCodes φ`, `RpnThresholdCodeSeq X`, `AffineCombination.PolySequence As`,
  `PGenerableWeighting W`, `GeneratedRatFeature P q ξ`, …) is a **representation
  interface**: it restricts who can supply the input, not what is proved. It is the paper's
  own e.c. requirement, is charged once at `def:ec`, and does **not** lower a row
  downstream. Stage joint consistency (`∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)`) is
  likewise the paper's own.

**The once-globally rule covers the symbol-metered classes only.** The distinction is at
the *definition*, not the name, and it is one conjunct of `PolyFueled`:

```
PolyFueled c f  :=  ∃ b, Fueled c f b ∧ IsPolyBounded f ∧ IsPolyBounded b
```

`IsPolyBounded f` bounds the **output value** `f n ≤ a·(n+1)^k + a`, over and above the fuel
bound `IsPolyBounded b`. So there are two different things a hypothesis built from
`PolyFueled` can be doing, and only reading the definition tells them apart:

* **symbol-metered** — `RpnSentenceCodes`, `RpnThresholdCodes(Seq)`, `RpnSpliceStream`,
  `PolySegStream` and the structures built from them. Here `PolyFueled` is applied to a
  *token emitter* and a *stream length*, so what is polynomial is the number of symbols and
  the size of each one, and a large value reaches the stream by being spliced out of many
  small tokens. That is the paper's own metering: `def:ec` is "runtime polynomial in `n`
  (i.e. in the length of `n` written in unary)" (tex:753-755), and `thm:halts`'s own gloss
  spells out that what must be polynomial is the time to **write out** the object —
  "it must be possible to write out the source code specifying `m_n` in time polynomial in
  `n`" (tex:1931-1933), with `⟨y⟩` an e.c. sequence of *bitstrings* at `thm:dontwait`
  (tex:1946-1952). A poly-time writer emits poly-many symbols, so the objects it can name
  run up to *exponential* magnitude.
* **whole-value** — `PolySentenceCodes`, `PolyThresholdCodes`, `PolyThresholdCodeSeq`,
  `PolyRatCodes`, `PolyNatCodes`, `PolyMachineCodes`, and anything whose fields are those
  (`PolyPositiveWidths`, `BoundedComputation.input_poly`,
  `SemidecidableComputation.input_poly`, `IntrospectionIntervalQuote.width_codes`,
  `DUSApproximationPresentation.approximation_codes`, `DUSThresholdEmission`,
  `PrefixMachinePresentation`, `SelfTrustQuote`, `ParadoxResistanceQuote`,
  `PatientSettlementClock`). Here `PolyFueled` is applied directly to
  `Encodable.encode`-of-the-object, so the *Gödel value* — not its length — must be
  polynomial in `n`. That is a strictly smaller class than the paper's, and the repo proves
  it smaller in both flavours: `ordinaryBitPrefixCodes` with
  `not_polySentenceCodes_bitPrefixSentence` exhibit a paper-admissible e.c. sentence family
  no whole-value sentence hypothesis can be instantiated at, and `not_polyFueled_two_pow`
  rules out `2^n`, hence rules out an e.c. bitstring sequence of length `n`, an e.c.
  rational sequence `δₙ = 2^(−n)`, and a machine sequence whose source grows faster than
  `O(log n)` characters. A whole-value hypothesis is therefore a **genuine class
  restriction**, and the `def:ec` charge does not cover it.

**When a whole-value hypothesis lowers a row.** Exactly when all three hold; check them in
order, because two of the three are what keep honest rows from being demoted:

1. it is a **hypothesis the caller must supply**, not a fact the repo *proves* about an
   object it constructs (`UPrefix.uSel_polyRatCodes`, `prefixApprox_polyRatCodes`,
   `dusThresholdEmission`, the constructed settlement clocks — these restrict nothing);
2. it constrains a datum the **paper itself quantifies over** as e.c. — `⟨m⟩`, `⟨x⟩`,
   `⟨φ⟩`, `⟨δ⟩`, `⟨p⟩` — rather than a repo-side presentation object the paper never
   mentions (that object's own disclosure is what the row carries);
3. the datum it constrains **appears in the conclusion**. A whole-value premise on a datum
   absent from the conclusion and provably inhabited is eliminable by instantiation and
   costs nothing — this is why `thm:lp`'s `width` does not lower that row.

This is easy to miss twice over. The symbol-metered and whole-value sentence classes are one
coercion apart (`RpnSentenceCodes.ofPolySentenceCodes`), so a narrowed endpoint opens by
applying it; and several whole-value hypotheses are **not visible in the elaborated
signature at all**, because they are fields of a structure the signature names
(`BoundedComputation`, `SemidecidableComputation`, `IntrospectionIntervalQuote`). Read the
structure, not the binder list.

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
| thm:ccee | `lic_no_expected_net_update_conditional_exact_canonical` |
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
| thm:scon | `ConditioningCompile.lic_conditioned_fixed_machine` (printed form, half 1); `ConditioningCompile.lic_conditioned_growing_machine_ofProcessComputation` (printed form, half 2); `lic_conditioned_fixed_machine_unconditional`; `lic_conditioned_growing_machine_unconditional` |
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
| def:ec | qualified | n/a | **The trader half is closed.** `MachineEfficientTrader` is an honest complexity class — some `Complexity.FP` function of the *unary* day emits the day's strategy — and it is the class the construction dominates: the trader enumeration is sound and complete for exactly it (`enumeratedTrader_machineEfficient`, `exists_enumeratedTrader_eq`), and `IsMachineLogicalInductor` is what `LIA_isMachineLogicalInductor` proves. `dd:fuel` is a certification device for that class (`EfficientlyComputable.toMachine`), not a substitution for it. What qualifies the row is the other half: the efficiently computable *sequence* classes the property tail takes as its own data (`RpnSentenceCodes`, `RpnThresholdCodes`, `PolySequence`, …) are still the symbol-metered fuel rendering, so those statements quantify over a possibly smaller set of admissible data than the paper's. The machine reading exists (`MachineSentenceCodes`, with the inclusion `RpnSentenceCodes.toMachine`) but is consumed only at `thm:scon`; the converse inclusion is open. This is the global fuel charge, levied here and nowhere else. It covers the **symbol-metered** classes only: the whole-value classes (`PolyRatCodes`, `PolyNatCodes`, `PolyMachineCodes`, `PolySentenceCodes`, `PolyThresholdCode(Seq)`) bound the Gödel *value* rather than the symbol count, are strictly smaller, and are charged at each row that takes one — see the disclosure section above |
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
| thm:ccee | exact | instantiated | `lic_no_expected_net_update_conditional_exact_canonical` takes exactly the paper-facing source interface (`X : ℕ → LUV`, `RpnThresholdCodeSeq X`, completed-world `source_valued`), a bare `DeferralFunction`, and a ℙ-generable `[0,1]` weight. Zero slack — the generic `_ofRepresentation_unconditional` carries a vanishing `slack` and an approximation premise; this signature has neither — and no caller-visible freshness or proof-carrying certificate, unlike the sibling `lic_no_expected_net_update_conditional_exact_productExtension`, which demands `ProductAtomFresh X` and a caller-supplied extension. The sole market is `liaHistory (canonicalCCEEDP T)`, whose computable, explicitly non-vacuous process is fixed from `T` before `X`, `f`, or `w`; one canonical enlarged language from the outset, not a source-dependent extension. **Disclosed gap:** the process side of non-vacuity is witnessed (`canonicalCCEEDP_computable`, `canonicalCCEEDP_hworld`), but there is no witness that this endpoint's `weight_generable` hypothesis is inhabited by a non-constant weight — the only such N+, `lic_no_expected_net_update_conditional_exact_productExtension_nonvacuous`, lives over `exactProductDP`, not over `canonicalCCEEDP` |
| thm:cee | exact | instantiated | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq`, with the deferred-expectation quote constructed and a bare `DeferralFunction` (`f n > n`, as `def:deferralfunc` asks). The only remaining premise is the paper's own "the source is an LUV of the theory" (`source_valued`) |
| thm:ceu | exact | instantiated | the cleanest endpoint in the paper: exactly a deferral function, the sentence sequence, and its `RpnSentenceCodes`. The quote code is constructed; no reflection data and no deferral narrowing |
| thm:con | exact | universal | genuine trader proof over `[IsLogicalInductor]`; the oscillation trader is constructed inside the proof, and the statement carries only the criterion instance and stage consistency. `lic_limitingBelief_tendsto` leads because the paper's statement *defines* `ℙ∞(φ) := lim ℙₙ(φ)`, and `limitingBelief` is the `ℙ∞` that `thm:lc`, `thm:perkno`, `thm:nd` and `thm:ob` consume downstream; `lic_price_convergesTo` proves the same fact in bare `∃ L` form |
| thm:dontwait | qualified | instantiated | unconditional over `LIA` on the provability process (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`), at the paper's own horizon class. **The horizon half is a proved strengthening; the machine/input half is what qualifies the row, and the two are independent hypotheses of one signature.** The horizon hypothesis is `hh : ComputableHorizon horizons` and nothing else — program plus specification, no growth bound — so **any** computable `f` (tex:1946-1952) is admissible, where the former `PolyNatCodes horizons` restricted it to polynomial time. The strengthening is *proved strict*: `ComputableHorizon.ackermann` is admissible and `not_polyNatCodes_ack` shows the old class excluded it. The claim's Gödel name pairs the constant `⌜f⌝` with `n` unevaluated and the arithmetic schema does the evaluation, exactly as the paper writes `⌜f⌝(⌜n⌝)`. Genuine subject matter: `machines : ℕ → Nat.Partrec.Code` with a real non-halting hypothesis. **What qualifies the row:** `hm : PolyMachineCodes machines` and `hi : PolyNatCodes inputs` are the same whole-value pair as `thm:halts`, and here the mismatch is sharpest — tex:1946-1952 asks for an e.c. sequence of *bitstrings* `⟨y⟩`, and a length-`n` bitstring has value `2^n`, which `not_polyFueled_two_pow` excludes. The paper's own worked example (a constant `q` against an enumeration of all bitstrings) does survive, since both data then have polynomial magnitude, but a varying machine sequence with growing source generally does not. The `ComputableHorizon` strengthening on `f` is unaffected by this and is proved strict independently |
| thm:dus | exact | universal | quantifies over **any** `DP` and any `[IsLogicalInductor P DP]`, the paper's own generality. Inputs are the paper's semantic premise `IndependentBitAtoms`, the naming certificate, and the semimeasure's from-below presentation; prefix codes are symbol-metered and inhabited. **Metering note, checked and deliberately not charged here:** `DUSApproximationPresentation.approximation_codes` and both fields of `DUSThresholdEmission` are whole-value `PolyRatCodes`. They do not lower the row under the disclosure section's test, on clauses (1) and (2): the datum they constrain is the repo-side rational approximation *table*, which the paper never quantifies over (it constructs one, "slowing an arbitrary lower approximation down to a polynomial-time table"), and the repo constructs and *proves* both certificates for its own universal semimeasure (`dusApproximationPresentation`, `dusThresholdEmission`). The presentation being a caller input at all is the retained representation interface this row already declares. Not `instantiated`: the three `_unconditional` forms all fix `DP = emptyBitDeductiveProcess`, and the paper frames the node as fresh symbols added *to* `Θ`, so `Θ = ∅` is the degenerate case |
| thm:ec | exact | universal | retains `[IsLogicalInductor]`, the paper's own `def:ec` threshold codes, stage joint consistency, and `def:luv`'s world-value fact at the paper's `cworlds(Θ)` quantifier (`∀ v, v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x`). The limit is constructed, not assumed. The former stage-quantified per-grid premise is gone and needed no compactness entailment to remove: the proof reads a world value only inside `filter_upwards [hae]`, where `hae` is `lic_limitCoherence`'s a.e. support on completed-theory worlds |
| thm:ei | exact | universal | the paper's varying-sequence statement, genuine trader proof over `[IsLogicalInductor]`. `LUV.IsIndicator` quantifies over `v.ConsistentWithTheory DP` — completed worlds — which is exactly `app:ei`'s own quantifier (tex:5229) and not the stronger every-stage reading, which `indicatorWitness_not_stagewise` shows would exclude the paper's own indicator; `indicatorWitness_isIndicator` exhibits a non-degenerate inhabitant |
| thm:epr | exact | instantiated | unconditional over `LIA` at `def:ec`'s own symbol-metered class; the quote code is constructed from the market program (`theoremPriceQuoteCode`), leaving exactly `φ` and `RpnSentenceCodes φ` |
| thm:er | exact | instantiated | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq`; the expectation quote code is constructed via `expectQuote_computable`, leaving exactly `X` and its threshold codes |
| thm:expcoh | exact | universal | retains `[IsLogicalInductor]`, the `def:blcp` bounded sequence, `S : LUVCombinationSyntax`, and `WorldValued` — the paper's own `def:luv` fact at `cworlds(Θ)`. `S` is the paper's own ℙ-generable presentation and is inhabited by `ordinaryLUVCombinationSyntax`, so it is not a retained interface. Nothing stage-quantified survives anywhere in the transitive premise set: `ConvergencePresentation.daily_value` became `world_value`, the upstream `TheorySemantics.stage_values` field was deleted, and the `ConvergencePresentation` argument is gone from the signature. Dominates the sibling `expcoh`, which additionally demands a `MeshSoftmaxOperationalWitness`, per-term threshold codes and an explicit bound |
| thm:exppolymax | exact | universal | same premise set as `thm:expcoh` — the bounded sequence, `S : LUVCombinationSyntax`, and `WorldValued` — with the operational witness discharged; `exppolymax_arith` additionally discharges `WorldValued` for the certified class |
| thm:expprovind | exact | universal | the printed display is `≳ₙ`, "and similarly for `=`/`≈ₙ` and `≤`/`≲ₙ`", so all three directions are the node and all three are shown, `_ge` first. Each takes precisely tex:1753-1757's one-sided bound at `cworlds(Θ)`, with each completed world free to pick its own valuation; `DeterminedViaTheory` is gone from them. The `_ofDetermined` variants take the *stronger* determinacy hypothesis, hence are weaker theorems and are internal; the fixed-LUV `lic_expectation_provind*` quantify over stage-plausible worlds and are a separate, weaker rendering |
| thm:halts | qualified | instantiated | unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`), with real subject matter: `machines : ℕ → Nat.Partrec.Code` and a genuine `CodeHalts` hypothesis. Nothing bounds an individual machine's runtime, matching tex:1931. **What qualifies the row:** the two e.c. class hypotheses are *not* the paper's. `hm : PolyMachineCodes machines` and `hi : PolyNatCodes inputs` are whole-value (`PolyFueled` on `Encodable.encode (machines n)` / on `inputs n`, so `IsPolyBounded` binds the Gödel value), whereas tex:1931-1933 says in as many words that what must be polynomial is the time to *write out* `⟨m⟩` — a poly-time writer emits poly-many *symbols*, so the paper admits source code of length `poly n`, i.e. codes of magnitude up to `2^poly(n)`, and `⟨x⟩` is a sequence of *bitstrings*. `not_polyFueled_two_pow` refutes both classes at `2^n`, so this endpoint covers only machine sequences whose descriptions grow logarithmically and inputs of polynomial magnitude. Both data appear in the conclusion (through `representedHaltingClaims … hm hi`), so the restriction is not eliminable. A symbol-metered rendering would need a statement change; there is no `RpnNatCodes`/`RpnMachineCodes` in the repo |
| thm:ifp | refuted | n/a | **The printed theorem is false, and the corrected theorem is proved.** `not_overgeneral_ifp` negates exactly the printed quantifier — `∀ P P' DP N, IsMachineLogicalInductor P DP → ComputableMarket P' → tail agreement → IsMachineLogicalInductor P' DP` — with no theory parameter, `sorry`-free and axiom-clean, using the constructed `LIA` as the inductor and a day-`0` advice tape as the perturbation. The published proof's invalid step is the "only finitely many constants" claim at tex:6047-6062; the ledger is `notes/paper-errata.md` PE1. The **corrected** theorem is `FreezeOracle.machine_lic_iff_of_recognizableSupport`: two computable markets differing on only finitely many `(day, sentence)` coordinates satisfy the criterion together — strictly stronger than the paper's tail agreement in the direction that survives, and exactly the case where the appendix's constant table really is finite. It takes **no** patch argument, discharging the two `MachineFiniteSupportPatch` inputs of `machine_lic_iff_of_finiteSupportPerturbation` internally. Its one residual hypothesis, `Recognizable`, is a condition on the *syntax* of the finitely many moved sentences, not on any market: representation residue standing for two `Complexity.FP` primitives this toolkit lacks (integer square root, a structured-payload parser), both proved necessary rather than convenient. `machine_lic_iff_twoPoint` makes it non-vacuous and `machineLogicalInductor_liaPerturbed` makes it informative — applied to `LIA` with one price moved, it derives a machine logical inductor no construction here produces. Deliberately **not** canonical: the fuel-class carriers `lic_iff_of_finitePerturbation` and `lic_iff_of_finiteSupportPerturbation`, whose `EfficientPrefixPatch`/`FiniteSupportPatch` hypotheses are *uninhabited* at the `dd:fuel` inverse-operation ceiling, and `machine_lic_iff_of_finiteSupportPerturbation`, which the corrected theorem supersedes. They remain axiom-checked internals |
| thm:incons | qualified | instantiated | **What the paper asserts** (tex:1893-1903): for an **e.c. sequence of recursively axiomatizable inconsistent theories** `⟨Θ′⟩`, `ℙₙ(⌜⌜Θ′ₙ⌝ is inconsistent⌝) ≈ₙ 1` and hence `ℙₙ(⌜⌜Θ′ₙ⌝ is consistent⌝) ≈ₙ 0`, those two sentences being the universal generalization of `Con(Θ′)(ν)` and *its negation* (tex:1855-1866). **What the Lean theorem proves:** `lic_disbelief_inconsistent_theories_unconditional` is unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`) and delivers both conjuncts of the display — but over a schematic carrier: `inconsistent : ℕ → Prop` an *arbitrary* semidecidable predicate presented by `SemidecidableComputation`, one fixed machine on a named input sequence, not a proof-search for `⊥`. **What is missing:** the `Con(Θ′)` family again, and beyond it a real sequence of inconsistent theories — the sole `N+` is `ordinarySemidecidableComputation`, “`0 < n`”, so the paper's intended subject matter is never exhibited. **What is proved:** the induction argument is generic in the same way as at `thm:pac`; the emitted families are symbol-metered `RpnSentenceCodes` and the trader half consumes only the represented-claims interface. **Two design notes.** `inconsistencySentence` and `consistencySentence` are independent families rather than syntactic negations. The stated reason — avoiding a syntactic-negation law the abstract `Sentence` representation does not provide — **no longer holds**: `Sentence` is `LO.Propositional.Formula ℕ` and `∼` is used on it freely elsewhere in this development, `InconsistentTheoryClaims.consistency_disprovable` included. That refactor is small; the theory-sequence witness is the hard part and is what actually qualifies the row. And a third, smaller restriction, invisible in the signature: `SemidecidableComputation.input_poly` is `PolyNatCodes input` — whole-value, where the paper's `⟨Θ′⟩` is e.c. in the write-out sense. **Removing the qualification** needs the same `Con`-schema work as `thm:pac` (~400–800 lines) plus a genuine inconsistent-theory sequence, and would still leave the symbol-versus-code metering gap. Frozen with the qualification deliberately |
| thm:lc | exact | universal | the measure `μ` plays the paper's `Pr`: a genuine probability measure on completed worlds, constructed rather than assumed, agreeing with `limitingBelief` on every sentence event and (a.e.) supported on worlds consistent with `Γ`. All three paper clauses in one theorem, over `[IsLogicalInductor]` plus `hworld` |
| thm:lex | exact | universal | propositional rendering over `[IsLogicalInductor]`; the exclusive-exhaustive premise is the completed-world payout-sum rendering, disclosed at the site |
| thm:li | strengthened | instantiated | sole hypothesis is a computable deductive process. The conclusion mirrors `def:belseq` — one `Nat.Partrec.Code` emits each day's finite association list, supports are finite, quotes are rational in `[0,1]` — *and* concludes `IsMachineLogicalInductor`, the paper's own quantifier. Strengthened in the `def:belseq` emission conjunct relative to the bare existence forms |
| thm:lia | exact | instantiated | the central construction, kernel-clean; the sole premise is a computable deductive process. `LIA_isMachineLogicalInductor` leads because it concludes the paper's own quantifier — `LIA_is_logical_inductor` is literally its `toIsLogicalInductor` projection, and showing only the projection contradicted the sibling node `thm:li`, which already shows the machine class |
| thm:loe | exact | universal | the paper's varying-sequence form: `a b : ℕ → ℚ` and `X Y Z : ℕ → LUV`. `Θ ⊢ Zₙ = aₙXₙ + bₙYₙ` is `DeterminedViaTheory` on the linearity combination (= paper `def:affthmval`), and `WorldValued` is `def:luv`'s own fact. The fixed sibling `lic_linearity_of_expectation` quantifies its hypothesis over *stage*-plausible worlds — a strictly stronger premise, correctly internal |
| thm:loops | qualified | instantiated | unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`); the hypothesis is literal object-level `T`-provability of non-halting, not a deductive-process emission surrogate. **Qualified for exactly `thm:halts`'s reason and no other:** the same `PolyMachineCodes machines` / `PolyNatCodes inputs` pair, whole-value rather than the paper's write-out metering, and the same two data in the conclusion |
| thm:lp | strengthened | instantiated | the paradoxical sequence is **constructed** (`theoremDiagonalQuoteCode`, by Gödel fixed point from the market computation) where the paper merely posits one, and the whole result is closed over `LIA`. The extra width premises are universally quantified and the class is inhabited (`harmonicWeight_polyRatCodes`). **Metering note, checked and deliberately not charged here:** `PolyRatCodes width` is whole-value, but it fails clause (3) of the disclosure section's test — `width` appears nowhere in the conclusion (`(fun n => ℙₙ(χᵖₙ)) ≈ₙ fun _ => p`), and the class is provably inhabited, so the premise is eliminable by instantiation and the statement is equivalent to the width-free one. The paper states no `δ` here at all; this is the one place a `PolyRatCodes` hypothesis costs nothing |
| thm:nd | strengthened | universal | the conclusion `∃ ε > 0, ∀ᶠ n, ε ≤ ℙₙ(φ)` is stronger than the paper's limit claim; the literal `ℙ∞` forms `lic_limit_pos`/`lic_limit_lt_one` are corollaries needing a `ConvergesTo` input and are internal. The plausibility premise is the paper's own, made stagewise |
| thm:ob | exact | universal | paper-strength bounds at genuine universal prefix complexity `κ_U`, with `prefixWeight κ φ = 1/2^(κ φ)` literally the paper's `2^(−κ)`. Invariance is proved (Kraft, the negation compiler, the invariance theorem); presentation and threshold emission are constructed, so only `[IsLogicalInductor]` and stagewise plausibility survive. Both halves in one statement. No `_unconditional` Occam endpoint exists anywhere, so nothing stronger is available |
| thm:obu | exact | universal | `_ofCE` takes the paper's own premises (tex:1540-1546): a c.e. source — `CEEnumeration`, a program whose dovetailed run returns `⌜source i⌝` at every index, with no clock — plus stagewise joint consistency of `Γ ∪ φ̄`, and concludes the paper's `ε` and `ℙ∞`. The padded efficient repetition the paper builds *inside* its proof (tex:5651-5656) is constructed by `EfficientRepeatedEnumeration.ofCE`, so `lic_uniform_nonDogmatism`, which assumes that structure directly, is the strictly stronger premise and sits second |
| thm:pac | qualified | instantiated | **What the paper asserts** (tex:1869-1875): for *any* computable `f`, `ℙₙ(Con(Θ)(⌜⌜f⌝(⌜n⌝)⌝)) ≈ₙ 1`, where `Con(Θ′)(ν)` is defined at tex:1855-1866 as the one-free-variable formula “there is no proof of `⊥` from `⌜Θ′⌝` with `ν` or fewer **symbols**”. **What the Lean theorem proves:** `lic_belief_finitistic_consistency_unconditional` is unconditional over `LIA` (Σ₁-sound `Θ ⊇ 𝗜𝚺₁`) and takes a schematic carrier — `consistentWithin : ℕ → Prop` an *arbitrary* decidable predicate, presented by `C : BoundedComputation consistentWithin`, i.e. one fixed machine run under a step budget — and the sentence it prices is a `boundedHaltingClaimSentence`: “this machine halts on this input within `⌜f⌝(n)` steps”. Nothing in the statement is about the consistency of a theory. **What is missing** is the representation object: the `Con(Θ′)(ν)` family, and with it any `BoundedComputation` instance for a proof-search-for-`⊥` machine — none exists anywhere in the repo, and the sole `N+`, `ordinaryBoundedComputation`, is “`Code.zero` halts within `n` steps”. The endpoint *implies* the paper's theorem for a reader who supplies the `Con`-machine; that instance is not constructed here. **What is proved, and is the honest half of this row:** the logical-induction argument itself is formalized and generic. `lic_provind_true` consumes only a `RepresentedDecidableClaims DP truth` — a symbol-metered (`RpnSentenceCodes`) emitted family with positive and negative process representation — so the trader half is reusable at any such family, including the `Con` one once it exists. Only sentence *generation* is absent. **Two things do land at the paper's own strength.** The horizon class is the paper's: `BoundedComputation` carries `horizon : ComputableHorizon steps` — the program `⌜f⌝` and its specification, no growth bound — in place of the former `steps_poly : PolyNatCodes steps`, and `not_polyNatCodes_ack` proves that generalization strict; the deferred-horizon schema is what makes it possible, since the claim name pairs the constant `⌜f⌝` with `n` unevaluated. And the process side is the constructed, computable `theoremDP`. **A second, smaller restriction, invisible in the elaborated signature:** `BoundedComputation.input_poly` is `PolyNatCodes input` — whole-value, bounding the *value* of the day-`n` input rather than the poly-time cost of writing it (see the disclosure section). This row previously claimed it was “the paper's own e.c. input sequence”; it is not. **Removing the qualification** needs the `Con` schema and its event tag, positive `Con` emission with a schema mutual-exclusivity lemma — roughly 400–800 lines, a new world-consistency proof and two `#assert_fields` unfreezes. It would also not fully close the gap: the paper meters proofs in **symbols**, Foundation has no symbol-length measure at all (`complexity` is connective depth, `height` proof-tree height, `bv` bound variables), and every candidate predicate meters by the Gödel number of the derivation, so the substitution would narrow rather than disappear. Frozen with the qualification deliberately |
| thm:pazfc | qualified | instantiated | **What the paper asserts** (tex:1881-1886): for *any* recursively axiomatizable consistent `Θ′` — including theories strictly stronger than `Θ` — `ℙₙ(Con(Θ′)(⌜⌜f⌝(⌜n⌝)⌝)) ≈ₙ 1`, with `Con(Θ′)(ν)` as defined at tex:1855-1866. The second theory is the entire content of the node. **What the Lean theorem proves:** exactly what `thm:pac` proves, and not a distinct proposition. `lic_belief_stronger_theory_consistency_unconditional`'s elaborated signature is `thm:pac`'s up to renaming the binder `consistentWithin` to `strongerConsistentWithin`, and at the universal layer the two are *definitionally* the same theorem: `lic_belief_finitistic_consistency` and `lic_belief_stronger_theory_consistency` are byte-identical apart from that binder name, and `example : @lic_belief_finitistic_consistency = @lic_belief_stronger_theory_consistency := rfl` is accepted by the kernel. **What is missing:** a `Θ′` at all. No second theory parameter appears anywhere in the statement, and nothing prevents `Θ′ = Θ`; the distinctive datum of the paper's node is *absent*, which is a stronger charge than “representation machinery is retained”. Everything in the `thm:pac` row applies verbatim: the schematic `BoundedComputation` carrier over an arbitrary decidable predicate, the `boundedHaltingClaimSentence` actually priced, the missing `Con(Θ′)(ν)` family and the missing proof-search witness, the whole-value `input_poly`, and the `ComputableHorizon` half that *is* at the paper's strength (verified the same way, `not_polyNatCodes_ack`). **What is proved:** as at `thm:pac`, the induction argument is generic — `lic_provind_true` needs only a `RepresentedDecidableClaims`, so a `Con(Θ′)` family would drop straight in. Only sentence generation is missing. **Removing the qualification** is the same 400–800-line `Con`-schema work as `thm:pac` plus a second fixed theory parameter (which the §4.10 probe found is free), and would still leave the symbol-versus-Gödel-code metering gap, Foundation having no symbol-length measure. Frozen with the qualification deliberately |
| thm:peraffkno | exact | universal | analytic capstone over `[IsLogicalInductor]`; sole carrier, hypotheses are the paper's |
| thm:perexpkno | exact | universal | same premise set as `thm:expcoh` — the `def:blcp` bounded sequence, `S : LUVCombinationSyntax`, `WorldValued` — and the same repair: the `ConvergencePresentation` argument is gone from the signature rather than merely derivable |
| thm:perkno | qualified | universal | over `[IsLogicalInductor]`, sole carrier, and the conclusion is a **three**-way conjunction matching the paper's three displayed clauses (`≈`, `≲` and `≳` against the future sup/inf) clause for clause; `limitingBelief P (φ n)` is `ℙ∞(φₙ)`. `φ` carries the symbol-metered `RpnSentenceCodes`, which is `def:ec`'s own charge and costs nothing here. **What qualifies the row** is the second data hypothesis: `PolyRatCodes p`, on the paper's "e.c. sequence of rational-number probabilities" (tex:1105-1107). That class is whole-value — `PolyFueled` on `Encodable.encode (p n)`, so numerator and denominator must be of polynomial *magnitude* — and it therefore admits only probability sequences approaching their limits at a polynomial rate, excluding e.g. `pₙ = 1 − 2^(−n)`, which the paper's write-out metering admits. `p` is in both hypothesis and conclusion, so the narrowing is not eliminable |
| thm:prand | corrected | universal | clock-free varied-frequency form; the target rationals enter as a market-generable feature (`def:ece`), as the paper requires, and the two-sided `≈ₙ` headline is exact. **Erratum PE5:** the centering of the one-sided notions is *inverted* relative to the printed `def:seqprand`, which displays the weighted average of `(pᵢ − ThmInd(φᵢ))` and calls its `≳ₙ` form "varied pseudorandom *above*". With the paper's centering, `def:seqprand`'s `≳ₙ` and `thm:prand`'s `ℙₙ(φₙ) ≳ₙ pₙ` point in opposite directions; the repo centers the other way (`VariedPseudorandomAbove truth p := PseudorandomAbove (truth − p)`), which is what the exploiting-trader argument needs and what makes the paper's advertised conclusion come out right. The `≈ₙ` form is unaffected, being sign-symmetric |
| thm:prandaff | exact | universal | clock-free: the patient settlement clock is constructed from the inductor, leaving exactly the paper's bounded-combination, determination and pseudorandomness premises. The printed display is `≳ₙ`, "and similarly for `≈ₙ` and `≲ₙ`", so `prandaff_above` leads; the two-sided `prandaff` sits last because its hypothesis is the conjunction of the two one-sided ones and its body is `asympEq_iff_asympLE_asympGE` over them |
| thm:prandexp | exact | universal | retains `WorldValued` (paper `def:luv`) and `DeterminedViaTheory` (paper `def:affthmval`, tex:1807); the clock is constructed. The paper prints only the `≳` direction, so `prandexp` leads and the `_below`/`_eq` forms follow |
| thm:provind | exact | universal | both halves of the paper's statement in one theorem, with `RpnSentenceCodes` on both sequences. "Sequence of theorems" becomes `∀ n, ∃ k, φ n ∈ DP.D k` — each `φₙ` eventually appears in the process — and dually for the disprovable `ψₙ`, which is the paper's eventual-deducibility premise |
| thm:recunbiasedaff | exact | universal | maturity constructed internally; clock-free, and no verifier premise remains |
| thm:recurringunbiasedness | exact | universal | same, over the sentence-affine family. Despite the namespace this is genuinely sentence-level — `φ` is lifted by `sentenceAffine` — not an affine substitution |
| thm:recurringunbiasednessexp | corrected | universal | same premises as `thm:prandexp`, both the paper's own. **Erratum PE2:** the printed statement (tex:1812-1820) is garbled — it carries a spurious "support of `⟨w⟩ ⊆ image of f`" clause referring to an `f` the statement never introduces, a clause that belongs to `thm:wubexp` and is missing there. The Lean statement is the repair: no deferral function, no support clause, concluding `HasLimitPoint 0` |
| thm:ref | qualified | instantiated | unconditional over `LIA` at `RpnSentenceCodes`, with the interval quote constructed from the market's exact rational quote. Its hypotheses are the paper's (tex:1969-1981) up to one metering gap: ℙ-generable interval bounds via their market-generated feature presentations, an e.c. sentence sequence, the vanishing width, and the range side conditions. Two `PolyRatCodes` hypotheses formerly stood on `ā` and `b̄`; they were **redundant** — consumed only as `.computable`, which `PGenerableRat.computable` supplies from the `MarketComputation` already in scope, the route `thm:st` already took — and have been removed. **What qualifies the row** is the third one, which remains: `PolyRatCodes δ` on the paper's "any e.c. sequence of positive rationals `⟨δ⟩ → 0`". It is whole-value, so `δ` may only vanish at a polynomial rate — `δₙ = 2^(−n)` is excluded by `not_polyFueled_two_pow`, and the paper's `→ 0` gives no such rate. `δ` is in the conclusion (it sets the interval the price must fall inside), so the restriction is not eliminable. `lic_introspection`, the caller-interface sibling, carries the same hypothesis invisibly as `IntrospectionIntervalQuote.width_codes`/`.inverse_width_codes`. **PE6** records the separate fact that the paper's *own proof* needs more than the paper states: `app:ref` applies `thm:affprovind` to a combination over sentences containing `⌜aₙ⌝`, `⌜bₙ⌝`, which requires those numerals efficiently writable, whereas ℙ-generability gives a feature whose value at the market is the bound. This formalization escapes that gap rather than inheriting it: the quoted sentence is a code-indexed atom (`dd:quote-code`), so its emission cost does not depend on the bounds |
| thm:scon | strengthened | instantiated | both halves at the paper's own quantifier. The two printed forms `lic_conditioned_fixed_machine` / `lic_conditioned_growing_machine_ofProcessComputation` are universal over `[IsMachineLogicalInductor P DP]` with **no** consistency hypothesis — the degenerate branch is `isMachineLogicalInductor_of_stage_unsatisfiable` — and the growing-form `hjoint` is gone, derived by propositional compactness (`Framework/Compactness.lean`). Their premise-free instances over the constructed `LIA` take exactly the hypotheses of the fuel-class pair `lic_conditioned_{fixed,growing}_unconditional` — `(T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]` and the condition, no inductor hypothesis — and conclude the strictly stronger `IsMachineLogicalInductor`, discharging the base by `LIA_isMachineLogicalInductor` where the fuel forms use `LIA_is_logical_inductor`. The machine transports are `conditionedTranslation_preserves_machine` and `eventualConditionedTranslation_preserves_machine`, under the same `RpnSentenceCodes` hypothesis on the condition as the fuel counterparts; the fuel endpoints and their inhabited witnesses are unchanged beside them, so this is a strengthening, not a replacement. (For the *general* forms the machine/fuel swap is on both sides of a closure implication, so those pairs are incomparable; the closed pair is where domination is strict) |
| thm:simcal | qualified | universal | maturity is constructed internally, and the endpoint's hypotheses are reachable from the paper's own up to one metering gap: `AffineCombination.simcal` takes `hpoly : PolySequence (sentenceAffine φ)` and `hWgen : PGenerableWeighting (calibrationIndicator φ a b δ)` as arguments, and both are *proved* here from the paper's own "`⟨φ⟩` is an e.c. sequence of decidable sentences" and "`⟨δ⟩` is an e.c. sequence of positive rationals" — by `AffineCombination.sentenceAffine_polySequence` and `calibrationIndicator_pgenerable` respectively, both shown on this card. (`calibrationIndicator_pgenerable` is exactly the fact tex:1188 asserts without proof.) They are arguments rather than a collapsed single endpoint, which is an ergonomic wart, not a strength loss: no collapsed endpoint exists. **What qualifies the row:** the `⟨δ⟩` half of that derivation is *not* the paper's class. Both `AffineCombination.simcal` and `calibrationIndicator_pgenerable` take `PolyPositiveWidths δ`, whose two `codes`/`inverse_codes` fields are `PolyRatCodes` — whole-value, so the calibration widths may only shrink polynomially, where tex:1193-1195 asks for any e.c. sequence of positive rationals. `δ` is in the conclusion through `calibrationIndicator φ a b δ`. The `⟨φ⟩` half is clean: `sentenceAffine_polySequence` takes the symbol-metered `RpnSentenceCodes` |
| thm:st | qualified | instantiated | unconditional over `LIA` with every representation obligation discharged: the `SelfTrustQuote` reflection data is constructed (`theoremConfidenceQuoteCode`), the quoted product LUV is symbol-metered (`indicatorProductLUV_rpnThresholdCodeSeq` emits the `⋏`-shell as tokens rather than as a `Nat.pair` on Gödel values), and the reciprocal code is *derived* (`PolyRatCodes.inv_of_pos`). The remaining hypotheses are exactly tex:2093's four: a deferral function, an e.c. sentence sequence, an e.c. sequence of positive rationals, and a ℙ-generable rational probability sequence. **What qualifies the row:** `hδ : PolyRatCodes δ` renders the third of those, and it is whole-value, so `δ` may only vanish polynomially — the `thm:ref` narrowing *does* recur here, on `δ` rather than on `p`. (`p` genuinely carries only `PGenerableRat`, which is symbol-metered via `GeneratedRatFeature`; that half of the earlier note stands.) `δ` reaches the conclusion through `theoremConfidenceQuoteCode … δ p hδ hp`, so it is not eliminable. `SelfTrustQuote`'s own `PolyRatCodes` fields are discharged by the construction and add nothing |
| thm:strict | exact | universal | paper strength for **any** `DP` and any inductor. `_ofAtomCodes` needs only computability of the atoms' Gödel codes, `[IsLogicalInductor]` and `0 < C`, building the separator presentation internally via `strictSeparatorPresentationOfKleene`; the separator argument is fully constructed (Kleene's recursively inseparable pair, the constraint enumerator from the atom codes, and the stage classes proved null by the Kučera–Demuth argument rather than assumed). The bare form takes `S : StrictSeparatorPresentation M B` as an explicit caller input and is therefore weaker as a usable statement, so it sits second. Not `instantiated`, for the same reason as `thm:dus`: the `_unconditional` form is over the constantly-empty deductive process |
| thm:tbo | exact | universal | over `[IsLogicalInductor]`; the `sSup`/`sInf` over `fun j => P (n + j) (φ n)` are the paper's sup/inf over `m ≥ n` of `ℙₘ(φₙ)`, and the conclusion is the paper's two liminf/limsup identities verbatim |
| thm:wub | exact | universal | `lic_wub_ofComputation` is universal over `[IsLogicalInductor]` with exactly tex:1249-1258's premises plus `hworld`: a ℙ-generable divergent weighting, a strictly increasing deferral function whose image contains the weighting's support, and timed feedback (`FeedbackTruthComputation`, rendered with a *polynomial* clock at `f(k+1)`, i.e. a weaker hypothesis than the paper's `O(f(n+1))`). It leads for that reason. The `_unconditional` form buys the discharge of `hworld` at the price of three arithmetic-theory class hypotheses the paper does not impose, and of no longer being about all inductors; it is shown second rather than alone |
| thm:wubaff | exact | universal | `boundedCombination_wubaff_ofComputation` takes a plain `BoundedCombinationSequence` — the paper's `⟨A⟩ ∈ 𝓑𝓒𝓢` at any bound — and rescales internally through `h.unitNormalization.scale`; emitter and truth bridge are constructed, leaving the paper's own timed-feedback premise `FeedbackTruthComputation`. It leads because the unit-magnitude siblings `lic_wubaff_ofComputation(_unconditional)` carry `∀ i, (As i).magnitude P ≤ 1` plus a separate `BoundedAffinePrices`, a normalization the paper's `𝓑𝓒𝓢` does not impose; the repo's own docstring calls the bounded-combination form "paper-facing", and it is now the one shown |
| thm:wubexp | exact | instantiated | the normalized threshold mesh, its feedback traders, and its sparse delayed-truth affine family (the one the paper builds *inside* `app:wub`) are all constructed. The remaining premises are exactly tex:1822-1832's — a bounded LUV-combination sequence determined via `Θ` at the *combination* level (`def:affthmval`), the `def:luv` premise `WorldValued`, a ℙ-generable divergent weighting supported on the image of a strictly increasing deferral function, and timed feedback (polynomial clock at `f(k+1)`, as for `thm:wub`). Determination is at the combination level only, so `[(1, X), (-1, X)]` for a wholly undetermined `X` is covered, which it would not be under `LUVCombination.ExactTheoryPresentation`; meshing is nonlinear, so the bridge is built at `ApproxDeterminedViaTheory` with the vanishing `meshErrorBound` (`lem:conluvapprox`). The universal form over any inductor leads; the `LIA`-closed form follows. Note the paper's printed statement is missing the support-⊆-image clause that belongs here (erratum PE2); the Lean carries it, correctly |
