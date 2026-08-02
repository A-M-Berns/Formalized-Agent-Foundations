# Per-label coverage-strength classification

_`scripts/check_endpoint_coverage.py` proves that every annotated paper label has an endpoint in
`AxiomAudit.lean`'s inventory.  That is a yes/no check; this file records **how strong** each of
those coverages is.  The checker machine-reads the table below — it enforces that the rows
classify exactly the non-excluded annotated labels, with a tier drawn from the vocabulary
given here — so a new label cannot ship without an honest strength call, and a row that outlives
its label fails the run.  This file lives beside the script that reads it; keep the two together._

_A tier is a claim about how completely the **whole** paper node is reached by the strongest
inventory endpoints carrying it, and is to be re-derived from their Lean signatures, never from
their prose.  Where a node has several statements (`thm:scon` has two), the weakest half sets the
tier and the row says so._

_Reading the tiers: a hypothesis the paper itself takes does not lower a row.  In particular
stage joint consistency (`∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)`) and `dd:fuel`
efficiency certificates on the statement's **own** data (`RpnSentenceCodes φ`, `PolyRatCodes p`,
`PGenerableWeighting W`, …) are the paper's own requirements; the fuel model is charged once,
globally, at `def:ec`, and never again downstream.  What lowers a row is a retained
representation or operational structure the paper proves or gets definitionally, or a genuine
restriction of the statement's class._

_**The once-globally rule covers the symbol-metered class only.**  `def:ec`'s faithful rendering
is `RpnSentenceCodes` (and its `LUV`/affine analogues), which meters a sentence by its symbol
count, as the paper does.  The whole-value classes — `PolySentenceCodes`, `PolyThresholdCodeSeq`,
`PolyNatCodes` — meter the single pair-code token instead, and the repo **proves** the inclusion
is strict: `ordinaryBitPrefixCodes` and `not_polySentenceCodes_bitPrefixSentence` exhibit a
paper-admissible e.c. sentence family that no whole-value hypothesis can be instantiated at.  So a
whole-value hypothesis is a genuine class restriction and **does** lower a row, even though it
looks like the same fuel certificate.  This distinction is easy to miss because the two classes
are one coercion apart (`RpnSentenceCodes.ofPolySentenceCodes`) and the narrowed endpoints open by
applying it; check whether the hypothesis is also passed as **data** to a quote-code constructor,
which is what forces whole-value metering and blocks the generalization._

**Global model disclosure (applies to every row).**  All tiers are **relative to the disclosed
repository model**: sentences are propositional (`Formula ℕ`), and efficient computability is the
fuel-clocked `Nat.Partrec.Code` interpreter (`dd:fuel`) — not the paper's first-order syntax
or a conventional complexity class.  A row marked *complete* claims the paper statement is reached
**within that model**, not that the model equivalence is proved.

**Tier vocabulary**
- **complete** — unconditional over the constructed `LIA` at paper strength; remaining premises
  are ones the paper itself takes (e.g. joint consistency, a Σ₁-sound `Θ ⊇ IΣ₁` for the
  represents-computations clause).
- **conditional** — paper-strength statement, conditional on `[IsLogicalInductor P DP]` (the
  risk-posture conditionality shared by the property tail); no extra representation or
  operational interfaces.
- **qualified** — full strength only for a restricted class or with a retained
  representation/operational interface the paper discharges (each row says which).
- **interface** — the label is covered by definitional/interface structures or component
  lemmas; the paper-strength statement is not a single endpoint.

| label | tier | justification |
|---|---|---|
| def:affcomsen | complete | direct rendering (`AffineCombination`: a constant feature plus a list of feature/sentence terms) |
| def:bap | complete | direct rendering (`BoundedCombinationSequence`): an efficiency certificate plus one uniform `l1Norm` bound |
| def:blcp | qualified | bounded LUV-combination sequence over the threshold-abstracted `LUV` type; the abstraction is charged at `def:luv` |
| def:dedproc | complete | direct rendering (`DeductiveProcess` plus its `DeductiveProcessComputation` certificate) |
| def:deferralfunc | complete | direct rendering: `n < f n` with the emitter clocked polynomially in `f n`, as the paper asks |
| def:ec | qualified | this row **is** the `dd:fuel` substitution: a symbol-metered clocked interpreter, not a complexity class; lower calibration (paper-e.c. ⊆ this class) is open |
| def:ece | complete | direct rendering of market-generability (`GeneratedRatFeature`): rank bound, emitter, closure, denotation — nothing retained beyond the global fuel model |
| def:fuz | complete | direct rendering of a generable weighting (`PGenerableWeighting`), strictly less data than `def:ece` carries |
| def:lia | complete | the constructed recursive algorithm (`liaStates`/`liaHistory`), certified by `thm:lia` |
| def:lic | complete | range law bundled through `marketComputable`; trader class is `def:ec`'s, disclosed globally |
| def:luv | qualified | threshold-sentence abstraction; the certified first-order bridge exists only for the `dd:luv-arith` class |
| def:trader | complete | direct rendering |
| def:tradestrat | complete | direct rendering, with the paper's rank/horizon bound on traded features |
| lem:mesh | conditional | `mesh_independence_ofSyntax` retains only `WorldValued`, which is the paper's own `def:luv` world-value fact (tex:1642-1648) — the condition that cuts our over-general `LUV` type down to the paper's object, not a restriction |
| lem:tfdom | complete | `trading_firm_dominance`: any efficiently computable exploiter is dominated, over any rational `[0,1]` market, with no inductor hypothesis |
| thm:affcoh | conditional | analytic capstone over `[IsLogicalInductor]` with the paper's bounded-combination data |
| thm:affpolymax | conditional | same, and the price/magnitude bounds are derived from the sequence rather than assumed |
| thm:affprovind | conditional | eventual completed-theory theoremhood, paper-shaped |
| thm:benford | conditional | clock-free: maturity and settlement constructed internally; premises are the paper's theory-truth and pseudorandom frequency over a deferral function |
| thm:ccee | qualified | unconditional over `LIA` with both quoted products constructed, a bare `DeferralFunction`, and — as of the mesh product — the paper's **arbitrary** e.c. source family (`lic_no_expected_net_update_conditional_closed` takes `X : ℕ → LUV` with `RpnThresholdCodeSeq` + `source_valued`, the same premises `thm:cee` carries). What keeps the row below `complete` is a declared type-`(c)` substitution rather than a class restriction: the left quoted product is reflected only to within `1/(n+1)` (`ConditionalExpectationQuote.slack`), because an exactly-reflecting product LUV would need either the value of the deferred weight or an infinite disjunction, neither available. Non-vacuity witnessed at both ends (`meshProductLUV_valuesAt`; `indicatorProductLUV_exact_left_reflected` at zero slack) |
| thm:cee | complete | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq` with the deferred-expectation quote constructed and a bare `DeferralFunction` (`f n > n`, as `def:deferralfunc` asks); the only remaining premise is the paper's own "the source is an LUV of the theory" (`source_valued`) |
| thm:ceu | complete | unconditional over `LIA` at `RpnSentenceCodes` with the quote code constructed; it takes only the sentence sequence, its codes, and a bare `DeferralFunction` — no reflection data and no deferral narrowing |
| thm:con | conditional | genuine trader proof over `[IsLogicalInductor]` |
| thm:dontwait | qualified | unconditional over `LIA` on the provability process (Σ₁-sound `Θ ⊇ IΣ₁`), but `lic_does_not_anticipate_halting_unconditional` takes `hh : PolyNatCodes horizons`, restricting the paper's "any computable function `f`" (tex:1946-1952) to polynomial-time `f`; same abstract-vs-unconditional split as `thm:pac` |
| thm:dus | conditional | paper-strength for **any** `DP` and any inductor via `lic_domination_universalSemimeasure_ofIndependentAtoms` (prefix codes now symbol-metered and inhabited). NOT `complete`: the unconditional endpoints hold only over `emptyBitDeductiveProcess` (`D n = ∅`), where `realizable`/`hworld` are discharged by "no stage asserts anything" — the paper frames `thm:dus` as fresh symbols added *to* Θ (tex:1550,1559), so Θ = ∅ is the degenerate case |
| thm:ec | conditional | `LUV.expect_converges` retains only `[IsLogicalInductor]`, the paper's own `def:ec` threshold codes, stage joint consistency, and `def:luv`'s world-value fact at the paper's `cworlds(Θ)` quantifier (`∀ v, v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x`).  The former stage-quantified per-grid premise is gone — and it needed no compactness entailment to remove: the proof reads a world value only inside `filter_upwards [hae]` where `hae` is `lic_limitCoherence`'s a.e.-support on completed-theory worlds, so the stage quantifier was excess strength that the old helper `approxValuesUpTo_of_consistentWithTheory` discarded on entry |
| thm:ei | conditional | the paper's **varying-sequence** statement (`⟨φ⟩` an ec sequence, `Yₙ` an indicator family for `φₙ`), genuine trader proof over `[IsLogicalInductor]`; `IsIndicator` is the paper's own `1(φ)` rendered relationally and quantified over `cworlds(Θ)` — exactly `app:ei`'s quantifier, not the stronger every-stage reading, which `indicatorWitness_not_stagewise` shows would exclude the paper's own indicator; the class is witnessed inhabited by a non-degenerate indicator (`indicatorWitness_isIndicator`). Remaining premises are the paper's own `def:ec` codes and stage joint consistency |
| thm:epr | complete | unconditional over `LIA` at `def:ec`'s own symbol-metered class (`RpnSentenceCodes`); the quote code is constructed from the market program (`theoremPriceQuoteCode`), leaving only the sentence family and its codes |
| thm:er | complete | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq`; the expectation quote code is constructed via `expectQuote_computable`, leaving only the LUV family and its threshold codes |
| thm:expcoh | conditional | `expcoh_ofSyntax` retains `[IsLogicalInductor]` and a single world-value premise, `WorldValued` — the paper's own `def:luv` fact at `cworlds(Θ)` (`∀ v, v.ConsistentWithTheory DP → …`).  Nothing stage-quantified survives anywhere in its transitive premise set: `ConvergencePresentation.daily_value` became `world_value`, the upstream `TheorySemantics.stage_values` field (a stage-quantified valuation with no constructor anywhere in the repo) was deleted, and the `ConvergencePresentation` argument itself is gone from the signature — `LUVCombinationSyntax.threshold_code` is a *lemma* off the `threshold_poly` field, so the syntax record `S` already in the signature supplies the codes and `WorldValued.convergencePresentation` supplies the rest |
| thm:exppolymax | conditional | `exppolymax_ofSyntax` retains only `WorldValued` (= paper `def:luv`); `exppolymax_arith` additionally discharges it for the certified class |
| thm:expprovind | conditional | **fully unconditional for certified `dd:luv-arith`** (all three comparison forms); the general LUV-combination forms retain only `WorldValued` (= paper `def:luv`) plus `DeterminedViaTheory` (= paper `def:affthmval`), both paper premises |
| thm:halts | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:ifp | qualified | efficiently-patchable perturbations only — the patch certificate is not inhabitable for every computable market; the paper's unrestricted statement has a recorded erratum (PE1) |
| thm:incons | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:lc | conditional | probability measure on completed worlds constructed, over `[IsLogicalInductor]` |
| thm:lex | conditional | propositional rendering over `[IsLogicalInductor]` |
| thm:li | complete | computable finite-support belief-sequence form, including the paper's `def:belseq` emission conjunct (`exists_liaEntries_code`) |
| thm:lia | complete | the central construction, kernel-clean; the sole premise is a computable deductive process |
| thm:loe | conditional | varying-sequence linearity retains only `WorldValued` (= paper `def:luv`) and the `Θ ⊢ Zₙ = aₙXₙ + bₙYₙ` relation in `DeterminedViaTheory` form (= paper `def:affthmval`); fully unconditional for `dd:luv-arith` fixed indices |
| thm:loops | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:lp | complete | public diagonal constructed from the market computation; unconditional over `LIA` |
| thm:nd | conditional | the plausibility premise is the paper's own |
| thm:ob | conditional | paper-strength bounds at genuine universal prefix complexity `κ_U` (invariance proved); presentation, threshold emission, and negation compiler are all constructed, so only `[IsLogicalInductor]` and joint consistency remain |
| thm:obu | qualified | over `[IsLogicalInductor]`, but `lic_uniform_nonDogmatism` takes `EfficientRepeatedEnumeration source` as **data** — the padding-and-repeating transformation the paper performs *inside* its own proof (tex:5651-5656) — while never assuming the source is c.e., which is the paper's actual hypothesis (tex:1540-1546).  No `c.e. → EfficientRepeatedEnumeration` constructor exists, so the interface is undischarged; and the structure's `sound : ∀ j, ∃ i, sequence j = source i` forbids the paper's own ⊤-padding unless `⊤ ∈ range source` |
| thm:pac | qualified | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`), but the unconditional route goes through `BoundedComputation`, whose `steps_poly : PolyNatCodes steps` restricts the paper's "**any** computable function `f`" (tex:1869-1875) to polynomial-time `f`.  The abstract endpoint (`MetaLearning.lean`) is at the paper's `f`-class, needing only `RepresentedDecidableClaims`, but retains the representation interface and `[IsLogicalInductor]` — so no single endpoint is both unconditional and at the paper's `f`-class |
| thm:pazfc | qualified | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`), with the same `PolyNatCodes` restriction on the paper's "any computable function `f`" (tex:1881-1887) as `thm:pac` |
| thm:peraffkno | conditional | analytic capstone over `[IsLogicalInductor]` |
| thm:perexpkno | conditional | `perexpkno_ofSyntax`, same single `WorldValued` premise and same repair as `expcoh`; the `ConvergencePresentation` argument is likewise gone rather than merely derivable |
| thm:perkno | conditional | over `[IsLogicalInductor]` with the paper's own probability sequence |
| thm:prand | conditional | clock-free varied-frequency form; the target rationals enter as a market-generable feature (`def:ece`), as the paper requires |
| thm:prandaff | conditional | clock-free: the patient settlement clock is constructed from the inductor, leaving exactly the paper's bounded-combination, determination and pseudorandomness premises |
| thm:prandexp | conditional | retains `WorldValued` (paper `def:luv`) + `DeterminedViaTheory` (paper `def:affthmval`, tex:1807); clock constructed |
| thm:provind | conditional | eventual completed-theory theoremhood, paper-shaped |
| thm:recunbiasedaff | conditional | maturity constructed internally; no clock or verifier premise remains |
| thm:recurringunbiasedness | conditional | same, over the sentence-affine family |
| thm:recurringunbiasednessexp | conditional | same premises as `prandexp`, both the paper's own; repairs the PE2 hypothesis-swap erratum |
| thm:ref | complete | unconditional over `LIA` at `RpnSentenceCodes`; the interval quote is constructed from the market's exact rational quote, leaving only the paper's own generable interval/width data |
| thm:scon | complete | growing-form `hjoint` deleted — derived by propositional compactness (`Framework/Compactness.lean`) or vacuous by the degenerate branch |
| thm:simcal | conditional | maturity constructed internally; the calibration indicator's generability and divergence are the paper's premises |
| thm:st | complete | unconditional over `LIA` with every representation obligation discharged: the `SelfTrustQuote` reflection data is constructed (`theoremConfidenceQuoteCode`), the quoted product LUV is symbol-metered (`indicatorProductLUV_rpnThresholdCodeSeq` emits the `⋏`-shell as tokens rather than as a `Nat.pair` on Gödel values), and the reciprocal code is now *derived* rather than assumed (`PolyRatCodes.inv_of_pos`).  The remaining hypotheses are exactly tex:2093's four: a deferral function, an e.c. sentence sequence, an e.c. sequence of **positive** rationals, and a P-generable rational probability sequence |
| thm:strict | conditional | paper-strength for any `DP` via `lic_strict_domination_universalSemimeasure_ofAtomCodes`; separator argument fully constructed. NOT `complete` for the same reason as `thm:dus` — the unconditional form is over the constantly-empty deductive process |
| thm:tbo | conditional | over `[IsLogicalInductor]` |
| thm:wub | complete | unconditional over `LIA` at `RpnSentenceCodes`; the emitter and truth bridge are constructed, and the remaining premises are exactly tex:1249-1258's — P-generable divergent weighting, a strictly increasing deferral function whose image contains the weighting's support, and timed feedback (`FeedbackTruthComputation`, rendered with a *polynomial* clock at `f(k+1)`, i.e. a weaker hypothesis than the paper's `O(f(n+1))`) |
| thm:wubaff | complete | same: emitter and truth bridge constructed, leaving only the paper\'s own timed-feedback premise `FeedbackTruthComputation`; unconditional over `LIA` |
| thm:wubexp | conditional | `WorldValued` + `DeterminedViaTheory` + the feedback emission/truth premises already adjudicated as the paper's own at `thm:wub` |
