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
| thm:ccee | qualified | unconditional over `LIA` with both quoted products constructed, a bare `DeferralFunction`, and — as of the mesh product — the paper's **arbitrary** e.c. source family (`lic_no_expected_net_update_conditional_closed` takes `X : ℕ → LUV` with `PolyThresholdCodeSeq` + `source_valued`, the same premises `thm:cee` carries). What keeps the row below `complete` is a declared type-`(c)` substitution rather than a class restriction: the left quoted product is reflected only to within `1/(n+1)` (`ConditionalExpectationQuote.slack`), because an exactly-reflecting product LUV would need either the value of the deferred weight or an infinite disjunction, neither available. Non-vacuity witnessed at both ends (`meshProductLUV_valuesAt`; `indicatorProductLUV_exact_left_reflected` at zero slack) |
| thm:cee | complete | `lic_expected_future_expectations_closed` is unconditional over `LIA` with the deferred-expectation quote constructed and a bare `DeferralFunction` (`f n > n`, as `def:deferralfunc` asks); the only remaining premise is the paper's own "the source is an LUV of the theory" (`source_valued`) |
| thm:ceu | complete | `lic_no_expected_net_update_closed` is unconditional over `LIA` with the quote code constructed; it takes only the sentence sequence, its poly codes, and a bare `DeferralFunction` — no reflection data and no deferral narrowing |
| thm:con | conditional | genuine trader proof over `[IsLogicalInductor]` |
| thm:dontwait | complete | unconditional over `LIA` on the provability process (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:dus | conditional | paper-strength for **any** `DP` and any inductor via `lic_domination_universalSemimeasure_ofIndependentAtoms` (prefix codes now symbol-metered and inhabited). NOT `complete`: the unconditional endpoints hold only over `emptyBitDeductiveProcess` (`D n = ∅`), where `realizable`/`hworld` are discharged by "no stage asserts anything" — the paper frames `thm:dus` as fresh symbols added *to* Θ (tex:1550,1559), so Θ = ∅ is the degenerate case |
| thm:ec | conditional | `LUV.expect_converges` retains the per-grid `hval`, which is the single-LUV `daily_value` and provably entailed by the paper's `def:luv` world-value fact |
| thm:ei | conditional | the paper's **varying-sequence** statement (`⟨φ⟩` an ec sequence, `Yₙ` an indicator family for `φₙ`), genuine trader proof over `[IsLogicalInductor]`; `IsIndicator` is the paper's own `1(φ)` rendered relationally and quantified over `cworlds(Θ)` — exactly `app:ei`'s quantifier, not the stronger every-stage reading, which `indicatorWitness_not_stagewise` shows would exclude the paper's own indicator; the class is witnessed inhabited by a non-degenerate indicator (`indicatorWitness_isIndicator`). Remaining premises are the paper's own `def:ec` codes and stage joint consistency |
| thm:epr | complete | unconditional over `LIA`; the quote code is constructed from the market program (`theoremPriceQuoteCode`), leaving only the sentence family and its codes |
| thm:er | complete | unconditional over `LIA`; the expectation quote code is constructed via `expectQuote_computable`, leaving only the LUV family and its threshold codes |
| thm:expcoh | conditional | `expcoh_ofSyntax` retains `WorldValued` + `ConvergencePresentation`, both paper-implied (`daily_value` is provably entailed by `WorldValued` via Cantor-space compactness) |
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
| thm:obu | conditional | over `[IsLogicalInductor]` with the paper's enumeration data |
| thm:pac | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:pazfc | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:peraffkno | conditional | analytic capstone over `[IsLogicalInductor]` |
| thm:perexpkno | conditional | `perexpkno_ofSyntax`, same premises as `expcoh` and same adjudication |
| thm:perkno | conditional | over `[IsLogicalInductor]` with the paper's own probability sequence |
| thm:prand | conditional | clock-free varied-frequency form; the target rationals enter as a market-generable feature (`def:ece`), as the paper requires |
| thm:prandaff | conditional | clock-free: the patient settlement clock is constructed from the inductor, leaving exactly the paper's bounded-combination, determination and pseudorandomness premises |
| thm:prandexp | conditional | retains `WorldValued` (paper `def:luv`) + `DeterminedViaTheory` (paper `def:affthmval`, tex:1807); clock constructed |
| thm:provind | conditional | eventual completed-theory theoremhood, paper-shaped |
| thm:recunbiasedaff | conditional | maturity constructed internally; no clock or verifier premise remains |
| thm:recurringunbiasedness | conditional | same, over the sentence-affine family |
| thm:recurringunbiasednessexp | conditional | same premises as `prandexp`, both the paper's own; repairs the PE2 hypothesis-swap erratum |
| thm:ref | complete | unconditional over `LIA`; the interval quote is constructed from the market's exact rational quote, leaving only the paper's own generable interval/width data |
| thm:scon | complete | growing-form `hjoint` deleted — derived by propositional compactness (`Framework/Compactness.lean`) or vacuous by the degenerate branch |
| thm:simcal | conditional | maturity constructed internally; the calibration indicator's generability and divergence are the paper's premises |
| thm:st | complete | the abstract endpoint takes P-generable `p` (`def:ece`) with `SelfTrustQuote` reflection data; `lic_self_trust_closed` discharges that data over `LIA` with `p` still P-generable — the quote code recovers `p`'s program from the feature presentation (`PGenerableRat.computable`: parse the emitted serialization, evaluate against the certified market, minimize over the interpreter clock) — and the deferral function is bare (`f n > n`, no injectivity), so nothing is retained beyond the global model |
| thm:strict | conditional | paper-strength for any `DP` via `lic_strict_domination_universalSemimeasure_ofAtomCodes`; separator argument fully constructed. NOT `complete` for the same reason as `thm:dus` — the unconditional form is over the constantly-empty deductive process |
| thm:tbo | conditional | over `[IsLogicalInductor]` |
| thm:wub | complete | unconditional over `LIA`; the emitter and truth bridge are constructed, and the sole remaining premise `FeedbackTruthComputation` is the paper\'s own timed-feedback hypothesis ("`ThmInd(φ_{f(n)})` computable in `O(f(n+1))` time", tex:1250) — rendered here with a *polynomial* clock at `f(k+1)`, i.e. weaker than the paper asks |
| thm:wubaff | complete | same: emitter and truth bridge constructed, leaving only the paper\'s own timed-feedback premise `FeedbackTruthComputation`; unconditional over `LIA` |
| thm:wubexp | conditional | `WorldValued` + `DeterminedViaTheory` + the feedback emission/truth premises already adjudicated as the paper's own at `thm:wub` |
