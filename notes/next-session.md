# Logical Induction working plan — M7 active

> **Build-state correction (2026-07-15):** the previous session (Codex) was cut off
> mid-proof and left `Construction/LIACompiler.lean` **not elaborating** — a `whnf`
> heartbeat timeout in `firmBudgetBreachAtDayData_prim` (the last Budgeter-gate primrec
> piece), cascading to a kernel error downstream. So the earlier "targeted LIACompiler
> build is green" note below was aspirational, not actual. Two genuine bugs in that
> cut-off proof were fixed this session: (1) `hctx` was ascribed `Primrec (fun _ =>
> BudgetWorldContext)` — a `Primrec` into `Type`; (2) the seven-projection block was
> systematically mis-indexed (`hpast/hj/hb/hn` one nesting level too shallow, `hxs`
> computing `p.1.1.2` instead of `p.1.2`). The residual defeq pathology was then
> **diagnosed and fixed** interactively: `set_option diagnostics true` on the final `exact`
> showed it blowing up computing `Nat.sqrt` (~23k unfoldings) via `Nat.unpair` — isDefEq
> reconciling the `Primcodable` instance of the deeply-nested product input type, **not**
> the budget math. (That is why `rfl`/`simp`/`simpa`/heartbeat-bumps/leaf-`irreducible`
> all looped — wrong layer.) Scoping `attribute [local irreducible] Nat.sqrt …` around the
> theorem stops that reduction; `firmBudgetBreachAtDayData_prim` is now **proved, no
> `sorry`**, and `LogicalInduction.Construction` builds **green with zero `sorry`s
> (2437 jobs)**.
> The compiler chain above this point is still unbuilt: `tradingFirmComponentTrades…_prim`
> → `tradingFirmTradesFromStageTradeLists_prim` → `liaPrefixFromTradeListsAtFuel_prim`
> (Option-bind recursion) → `liaPrefixAtFuel`/`liaEncodedQuoteAtFuel` computable →
> `Computable₂ liaEncodedQuoteNatAtFuel` → instantiate `LIABoundedEvaluatorCompiler` →
> `exists_logical_inductor`.

> **M7 goal set (2026-07-14):** M7 now has the falsifiable completion contract in
> `PROGRESS.md`: faithful `Budgeter`, redundant e.c.-trader enumeration, executable
> `TradingFirm` plus dominance, recursive computable rational `LIA`, `thm:lia`/`thm:li`,
> all fifteen named post-M5 representation/compiler witnesses, fully instantiated property
> corollaries, paper comparison, builds/source/diff/axiom gates, Anson's read-through, and a
> separate fresh-context audit with correction recheck. Conditional or analytic progress
> does not close the milestone.
>
> **First construction tranche complete:** the former `EfficientlyComputableTok` required
> a polynomial bound on serialized length but no program computing that length. It therefore
> admitted traders with uncomputable stopping lengths and could not support the paper's
> redundant enumeration. The repaired definition is the paper-aligned total bounded
> emulator: exact length/token programs, a polynomial clock, a clock-clamped emitted stream,
> and validation with malformed outputs normalized to the zero strategy. Exact-emission
> compilers recover all existing traders through `ecTok_of_exactEmission`. The concrete
> `enumeratedTrader : ℕ → Trader` now proves both that every entry is e.c.
> (`enumeratedTrader_ecTok`) and that every e.c. trader occurs
> (`exists_enumeratedTrader_eq`). Construction/Properties/Integration is green at
> 2,461/2,461 jobs. Budgeter is the active construction step.
>
> **Budgeter semantic tranche green:** `Construction/Budgeter.lean` now uses an executable
> enumeration of finite atom assignments, an exact rational past-loss scan, and an adaptive
> action layer over the rational history representation already used by MarketMaker. The
> scan is proved equivalent to the paper's quantification over p.c. worlds. The three
> Budgeter properties are kernel-checked: `BudgeterAt_value_eq_of_safe`,
> `budgetedTrader_netWorth_floor`, and `exists_budgetedTrader_exploits`. The remaining
> Budgeter construction item is to expose the bounded search/stopping-clock wrapper that
> obtains finite `D_m` stages from `DeductiveProcessComputation`, rather than counting
> access to the semantic `DP.D` field as the final computability witness.
>
> **TradingFirm and semantic LIA tranche green:** `Construction/TradingFirm.lean` gives a
> finite exact day strategy for the paper's double geometric mixture, compresses both
> infinite tails with proved `HasSum` identities, proves component/global/residual loss
> floors, and closes `trading_firm_dominance`. `Construction/LIA.lean` recursively feeds
> the actual finite rational prefix to TradingFirm and MarketMaker, proves equality with
> the generic MarketMaker recursion and with the static dominance firm, and proves that no
> e.c. trader exploits the resulting rational `[0,1]` history. All new capstones expose
> only the approved three axioms. `Construction/LIAComputation.lean` now supplies the exact
> bounded operational presentation: one common fuel decodes `D₀,…,Dₙ`, executes the
> explicit-stage TradingFirm/MarketMaker recursion, and returns the encoded rational quote.
> Soundness, monotonic-success, and finite-clock existence are proved end to end. A generic
> `Partrec.rfindOpt` bridge derives the exact `ComputableMarket` program and criterion once
> the bounded evaluator's conclusion-free `Computable₂` certificate is supplied. The active
> blocker is precisely that certificate (primitive-recursive compilation of the finite
> syntax/rational/list evaluator), not recursion correctness or stopping. Until it is
> instantiated, `LIA_is_logical_inductor` and `exists_logical_inductor` remain open.
>
> **Compiler tranche active:** `Construction/LIACompiler.lean` now proves exact
> primitive-recursive normalize-after-decode functions for the concrete Foundation
> `Formula ℕ` Gödel coding, Mathlib's reduced rational coding, and the project's recursive
> `EF.toNat`/`EF.ofNat` coding. It proves agreement with each real `Encodable.decode`, covers
> every malformed/failure branch, and installs matching hole-free `Primcodable` instances
> for `Sentence`, `ℚ`, and `EF`. Exact primitive-recursive rational arithmetic/comparison is
> now complete, as are proof-erased validated `RationalBeliefState` and day-indexed
> `Strategy n` encodings (including a concrete compiler for `EF.rank`), plus exact
> primitive-recursive belief-state quotation, finite chronological history lookup,
> MarketMaker candidate decoding, and the stock sorted `Finset Sentence` encoding. The
> latter compiles insertion sort and uses Mathlib's
> `List.mergeSort_eq_insertionSort` theorem to preserve the already-fixed deductive-process
> encoding exactly; `process.stageAtFuel` and the full common-clock deductive-stage prefix
> are now primitive recursive. The flat trader-program boundary is compiled too: the
> one-token `EF.streamStep`, its full list fold, terminal validation, `deserializeTrades`,
> rank-validated `strategyOfTokens`, decoded polynomial program clocks, the uniformly
> enumerated trader, and its gated `firmRawTrader` action are all exact primitive-recursive
> functions. The dependent-type erasure is now complete as well. `MarketMaker.lean`
> exposes raw-trade acceptance, candidate checking, and bounded search;
> `Budgeter.lean` exposes raw-trade atom support, exact wealth, bankruptcy, world scaling,
> and budgeted trade emission; `TradingFirm.lean` assembles the entire finite mixture as a
> raw trade list; and `LIAComputation.lean` runs the complete bounded recurrence without
> ever constructing a value-dependent `Strategy n`. Every layer has an exact equality
> theorem back to the original typed semantics. The bottom-up compiler now additionally
> includes an exact rational stack machine for the full `EF` language (constants, prices,
> variables, `letE`, arithmetic, `max`, and safe reciprocal), a syntax-derived uniform
> fuel bound, a proof that the fueled result is exactly `EF.denoteRat`, and a generic
> primitive-recursive finite trade-list market-value fold. This has been specialized and
> verified for candidate-updated rational histories and MarketMaker Boolean support
> worlds. The targeted `LIACompiler` build is green. The next compiler step is the finite
> universal Boolean-world acceptance predicate and bounded candidate search, followed by
> the erased Budgeter/TradingFirm/state-prefix operations and final composition into
> `Computable₂ liaEncodedQuoteNatAtFuel`.

> **M6 verified complete (2026-07-14):**
> `LogicalInduction/Construction/MarketMaker.lean` now proves the strategy fixed-point
> lemma, implements the exact rational fuel-clocked first-success MarketMaker, recursively
> generates its history, and proves it is not exploited by its input trader for every
> deductive process. See `notes/m6-verification-packet.md` for the statement comparison and
> modeling disclosures. The construction roll-up passed 2,426/2,426 jobs, the full build
> passed 2,671/2,671, source/diff checks are clean, and capstone axiom reports contain only
> the approved three axioms. At M6 close, M7 (`Budgeter`, `TradingFirm`, `LIA`, existence)
> was wholly unstarted; it has now been explicitly scoped and activated above.

# Historical M5 closeout

> **Fresh-context audit correction pass (2026-07-14):** Anson authorized and a fresh
> subagent completed the adversarial audit. It passed kernel soundness, trader token
> certificates, downside/upside non-vacuity, and conclusion-in-premise attacks, but found
> two real scope gaps plus incomplete boundary tracking. The arbitrary-BCS gap is repaired
> by one canonical positive rational `BoundedCombinationSequence.unitNormalization` and
> paper-facing `recunbiasedaff`, `wubaff`, and `prandaff_{above,below,eq}` wrappers. The
> `thm:ref` endpoint package now carries closed `GeneratedRatFeature`s, exactly matching
> market-generated `aₙ,bₙ`, instead of independently polynomial rational tables. Concrete
> `M7-LUV-SYNTAX`, `M7-DUS-PREFIX-SYNTAX`, and `M7-SCON-PRESENTATION` obligations have been
> added, and the three TeX inconsistencies in `recurringunbiasednessexp`, `wubexp`, and
> `pazfc` are explicitly triaged. The public property/integration build is green at
> 1,958/1,958, the full build is green at 2,670/2,670, wrapper axiom reports expose only
> the approved three axioms, the executable-hole scan is empty, and `git diff --check` is
> clean. The independent correction recheck returned PASS: no new circularity, vacuity, or
> paper-scope defect was found. All eight M5 verification gates are closed.

> **Expectation-property tranche complete (2026-07-14):**
> `Properties/ExpectationProperties.lean` now proves all six remaining paper nodes:
> `BoundedSequence.exppolymax`, `perexpkno`, `expcoh`,
> `recurringunbiasednessexp`, `wubexp`, and the paper-facing nonnegative
> `prandexp`, together with its stated analogous `prandexp_below` and derived
> `prandexp_eq` directions. Arbitrary BLCS magnitude is handled by the explicit positive
> normalization `meshNormScale`; no unit-bound premise is silently substituted. An exact
> first-order presentation determines the completed-world threshold mesh, whose truth
> differs from exact LUV truth by `O(b/n)`. The new Toeplitz theorem proves that every
> nonnegative divergent weighting sends this pointwise null error to a null weighted
> average. This supplies the exact-truth transfers for recurring unbiasedness, feedback
> unbiasedness, and pseudorandom learning rather than assuming them in a certificate.
> Every new capstone prints only `propext`, `Classical.choice`, and `Quot.sound`; the flat
> ledger is updated. The public property/integration roll-up is green at 1,958/1,958 jobs,
> the full project is green at 2,670/2,670 jobs, the executable-placeholder scan is empty,
> and `git diff --check` is clean. Anson confirmed the statement-by-statement paper
> read-through in the project thread on 2026-07-14. The fresh-context audit described in
> `PROGRESS.md` has now run and its findings are in correction/recheck. The
> compact, checkboxed handoff for both reviews is
> `notes/m5-verification-packet.md`; its author-context pre-audit is explicitly not counted
> as the independent audit.
>
> **Latest structural/audit progress (2026-07-14):** the `affpolymax` regression found
> and repaired a real normalization mismatch: the paper-facing theorem now consumes an
> exact `BoundedCombinationSequence` with the trailing constant included in its `L¹` norm,
> derives semantic bounded prices, rationally normalizes an arbitrary real bound, and
> transports all extrema conclusions back. The `thm:lex` regression likewise found that
> fixed equivalence/implication had been mislabeled as the paper theorem; the actual
> fixed-`k` exclusive/exhaustive sum theorem is now proved by a genuinely uniform tuple
> emitter. Both targets and Non-Dogmatism are green and axiom-clean.
>
> `thm:ifp` is now complete as an exact conditional biconditional in
> `Properties/FinitePerturbations.lean`. `EF.freezeBefore` is the paper's literal
> false-report transformation; Lean proves rank/cost preservation, exact tail semantics,
> an explicit finite magnitude bound on net-worth error, and exploitation transport in
> both directions. The audit exposed one honest clock-model gap: `ComputableMarket` does
> not give polynomial-time access to old quotes, so the paper's “hard-code” sentence does
> not by itself prove token-emission closure for arbitrary varying sentence codes.
> `EfficientPrefixPatch` isolates only that concrete compiler fact, and
> `M7-PREFIX-PATCH` records its witness obligation. The 1,693-job target is green and all
> public proof reports contain only the approved foundational axioms.
>
> `thm:obu` is complete as the exact conditional `lic_uniform_nonDogmatism` capstone in
> `Properties/UniformNonDogmatism.lean`. Its varying-sentence scale ladder has a literal
> polynomial token emitter, an explicit global `-2` floor, and non-vacuous unbounded
> jointly consistent-world upside. Fixed-sentence convergence and infinite repetition
> turn failure of a common positive `P∞` bound into one full trigger at every scale. The
> paper's c.e.-enumeration padding step is isolated as the syntax-only
> `EfficientRepeatedEnumeration` witness and ledgered as `M7-CE-REPETITION`; it carries
> no prices or limiting conclusion. The 1,705-job target is green and the capstone is
> axiom-clean.
>
> `thm:ob` is now complete as the exact conditional two-sided `lic_occamBounds` capstone
> in `Properties/OccamBounds.lean`. A single Kraft-weighted ladder diagonalizes the paper's
> trader family: rung `j` spends at most `1/j²`, total net worth is bounded below by `-2`,
> and a full possible-world trigger produces order-`j²` upside. The actual variable-width
> day/sentence/rung/history serialization has a kernel-checked
> `EfficientlyComputableTok` certificate. The lower theorem yields one common multiple of
> `2^{-κ(φ)}`; the upper theorem uses the audited exclusive–exhaustive limit law and one
> fixed negation-program overhead, preserving a single constant for both inequalities.
> `M7-PREFIX-MACHINE` isolates only the concrete universal-prefix-machine syntax,
> rational-token arithmetic, Kraft/coverage proof, and negation compiler; it contains no
> prices or Occam conclusion. Direct checking and the authoritative 1,951-job property
> roll-up are green; the source scan is empty, `git diff --check` passes, and all printed
> declarations expose only the approved foundational axioms.
>
> Work on `thm:dus` has begun in `Properties/UniversalSemimeasure.lean`. The file now
> faithfully defines continuous, lower-semicomputable (with an actual unrestricted
> `Code.evaln` presentation), and universal semimeasures, together with the exact Boolean
> semantics and finite realizability of the paper's independent bit-prefix sentences.
> The central `MeanPayout ≤ MaxPayout` step is proved by finite binary-tree induction;
> semimeasure leakage is handled as stopping at an internal node. A tempting reduction to
> `thm:ob` was audited and removed: continuous prefix mass can stay `1` along an infinite
> deterministic path, while ordinary prefix complexity of its distinct prefix sentences
> cannot remain bounded. Do not reintroduce a fixed Shannon–Fano compiler for sentence
> prefix complexity. The next hard gate is the paper's unit-budget purchase trader (or a
> genuinely equivalent monotone-code proof), followed by its real uniform token emitter
> and a summable diagonal of the scale family.
>
> **DUS completion update (2026-07-14):** `thm:dus` is now green end to end.
> `DUSApproximationPresentation`/`DUSThresholdEmission` isolate the paper's syntax-only
> bounded-simulation slowdown as `M7-DUS-APPROX`. The direct trader uses the equivalent
> dovetail `enumeration n.unpair.2`, revisiting every prefix infinitely often while making
> one chronological purchase decision per day. `dusRemainingEF` is the actual shared
> expressible-feature cash recurrence, `dusSpendThrough_le_one` proves total cost at most
> one, and `dusScaleTrader_netWorth_ge_neg_one` proves a literal all-world downside floor.
> The full recurrence is uniformly serialized across scale and day—prior values are
> referenced with `EF.var`, not duplicated—and `dusScaleTrader_ecTok` is axiom-clean.
> A violating prefix forces semimeasure-weighted payout to reach `k+1`. The finite event
> list is aggregated by prefix into an explicit binary purchase tree; a maximizing branch
> is realized as a same-day `B.prefix_possible` world, so the upside is non-vacuous.
>
> `dusTrader` is the literal scale diagonal: rung `j` runs scale `(j+1)^4` at weight
> `1/(j+1)^2`. `dusTrader_netWorth_ge_neg_two` proves its global floor;
> `dusTrader_exploits_of_failed_scales` proves unbounded plausible wealth if every fixed
> constant fails; and `dusTrader_ecTok` emits the actual joined strategy, including the
> polynomial scale and rational weight. `lic_domination_universalSemimeasure` is the exact
> fixed-`C>0` capstone. All printed DUS declarations expose only `propext`,
> `Classical.choice`, and `Quot.sound`.
>
> **Strict-domination update (2026-07-14):** `Properties/StrictSemimeasure.lean` now proves
> the exact non-domination conclusion. `StrictSeparatorPresentation` exposes the paper's
> nested recursively-inseparable separator prefix class, its efficient repetition and
> finite joint realizability, and the computability-theory fact that universal-semimeasure
> mass tends to zero. `strict_domination_of_null_prefix_theory` combines that fact with
> Uniform Non-Dogmatism; `lic_strict_domination_universalSemimeasure` defeats every `C>0`
> at an actual finite prefix. The concrete c.e.-machine-set instantiation is explicitly
> ledgered as `M7-STRICT-SEPARATORS`; the boundary contains no market or non-domination
> conclusion. Both printed theorems are axiom-clean. Next paper node: `thm:scon`.
>
> **Conditioning substrate update (2026-07-14):** `Properties/Conditioning.lean` now has
> the paper's exact capped `conditionalQuote`, `conditionedHistory`, its `[0,1]` theorem,
> stagewise `DeductiveProcess.union`, and the exact combined-world equivalence.
> `ConditioningPresentation` uniformly covers a fixed condition and growing finite
> conjunctions. `ConditioningTraderCompiler` is the auditable target for the remaining
> Appendix construction: it must emit an actual translated trader, preserve its token
> certificate, track conditional-world wealth within the summable error `1`, and establish
> a global base-world floor. Lean already proves from exactly those fields that exploits
> transport (`ConditioningTraderCompiler.exploits_base`) and that the conditioned market is
> an LI (`lic_conditioned`). The safe-ratio/gated translator itself remains
> `M7-SCON-COMPILER`, so `thm:scon` is still pending rather than oversold.
>
> The translator is no longer wholly abstract. `EF.lowerSafeRecip` implements
> `1/max(ε,p)` from the DSL's safe reciprocal; `EF.conditionalPriceEF` denotes the exact
> capped quote under the patched denominator floor; and `EF.conditionPrices` recursively
> rewrites every price leaf of arbitrary shared feature syntax with exact denotation and
> unchanged rank. `Strategy.conditionalContract` emits the literal conjunction/condition
> stock pair for every original position, and `conditionalContract_value` proves exact
> value agreement in condition-satisfying worlds whenever the cap is inactive.
>
> **Conditioning semantic-compiler update (2026-07-14):** the Appendix economic
> construction is now concrete. `conditioningBudget n = 1/((n+1)(n+2))` is strictly
> positive, telescopes, and has every finite prefix sum `≤1`; it replaces paper `2⁻ⁿ`
> because literal exponential denominators are not polynomial-value tokens in this model.
> `EF.conditioningCapGate` normalizes this budget by the reified strategy magnitude, and
> `gatedConditionalPosition_lower` proves the cap-case loss is at most `|α|δ` while leaving
> negative positions untouched. `Strategy.gatedConditionalContract_value_lower` sums the
> real two-stock contracts and gives the per-day budget loss;
> `Trader.conditionedTranslation_netWorth_lower` sums it to one. Separately,
> `gatedConditionalContract_value_eq_zero_of_not_holds` proves that a false condition
> annihilates payout and cash exactly, and
> `ConditioningPresentation.conditionedTranslation_preserves_floor` formalizes the least
> failed condition argument and global base-world downside floor.
>
> `GatedConditioningOperationalWitness.toCompiler` now assembles those theorems into the
> compiler contract, and `lic_conditioned_gated` is the paper-facing conditional capstone.
> The remaining `M7-SCON-COMPILER` boundary is operational only: construct the finite-prefix
> positive-denominator patch, emit the exact rational conditional market program, and
> transform arbitrary `EfficientlyComputableTok` streams into the concrete translated
> stream. It contains no tracking, floor, exploitation, or LIC conclusion. Targeted project
> build: 1,714/1,714 green; source-hole scan and `git diff --check` clean; all new axiom
> prints expose only `propext`, `Classical.choice`, and `Quot.sound`.

> **Active M5 state (2026-07-13):** the falsifiable M5 verification goal is active and
> `PROGRESS.md` now contains the flat paper-label obligation ledger. `thm:tbo` is proved as
> `lic_preemptive_learning` by an explicit legal one-share specialization of the completed
> affine preemptive-learning trader; its targeted build and axiom report are green. The
> canonical limiting valuation `limitingBelief`, sentence convergence to it, and fixed
> affine-combination convergence are also proved in `Properties/AffinePersistence.lean`.
> `thm:peraffkno` is now proved exactly as `PolySequence.peraffkno`: the day-indexed
> normalized prefix portfolio has explicit polynomial term/feature/sentence emission,
> bounded magnitude and prices, a non-vacuous full-launch argument for every tail dip,
> and uses the completed affine gradual-return ROI hub for the economic contradiction.
> Both negation-dual equalities, targeted build, and axiom inventory are green.
> `thm:perkno` is also complete as `lic_persistence_of_knowledge`: its explicit
> polynomial centered family `φₙ-pₙ` consumes both the sentence and rational code
> witnesses, derives the two uniform one-sided tail bounds from the operational
> persistence gaps, and combines them into the exact future absolute-deviation claim.
> Its targeted build and axiom report are green.
> `thm:affcoh` is complete as `PolySequence.affcoh`. The completed theory is represented
> by consistency with every finite deductive stage; the finite-to-completed uniformization
> is proved by compactness of `ℕ → Bool`, with closed formula-model and affine-sublevel
> sets. A padded constant-member polynomial certificate then reuses the affine provability
> trader to connect completed worlds to `P∞`, and `peraffkno` connects `P∞` to the diagonal.
> The exact lower and upper liminf/limsup chains and axiom inventory are green.
>
> **Repaired verification finding:** `lic_provind_seq` assumes
> `φₙ ∈ Dₙ`. It is a valid same-day-deduction support lemma, but it is not the
> paper's `thm:provind`, whose efficiently generated theorem may be proved much later.
> The paper's real route is now complete: `peraffkno` → `affcoh` →
> `affine_provind_theory_{ge,le,eq}` → `lic_provind`. The new `lic_provind` requires only
> that each theorem (or negation of a disprovable sentence) appear at some deductive stage,
> so it permits arbitrarily late individual proof discovery. Its targeted build and axiom
> report are green. Consistency and halting results must use this declaration, not the
> same-day support lemma.
> The completed persistence/coherence/provability tranche passes the 1,714-job
> roll-up/integration build and a fresh 2,657-job full build.
>
> **Immediate implementation tranche:** implement the recurring calibration/unbiasedness
> spine and its affine/feedback/pseudorandom corollaries. Keep all later M5 nodes pending in the flat
> ledger until their own statement and trust-surface gates pass.
>
> **Recurring-unbiasedness spine progress (2026-07-13):**
> `Properties/Calibration.lean` is now a green, roll-up-imported infrastructure module.
> It defines honest P-generable divergent weightings, normalized averages/bias, standard
> subsequential limit points, the vanishing-step/crossing proof, the paper's continuous
> calibration selector and the exact `simcal` analytic consumer.  On the economic side it
> defines completed-theory determination and proves its finite-stage compactness bridge;
> constructs a continuous one-unit capped affine run; proves genuine summability, exact
> full-risk use under persistent bias, the finite Abel/Cesàro surplus bound, and actual
> positive ROI after controlling finitely many settled positions plus the summable tail.
> The entire two-index run family now has a concrete `PolyTradeEmulatable` token certificate,
> including a family-uniform straight-line emitter for the fractional recurrence.
>
> **Corrected bounded-verification boundary:** `ComputableMarket` and
> `ComputableDeductiveProcess` do not promise that the data for day `m` can be produced in
> polynomial time in `m`.  The paper does not need that stronger claim.  On outer day `n`,
> its openness computation spends a bounded amount of work checking whether some historical
> witness `m ≤ n` has finished verification.  `ROI.lean` now represents this faithfully as
> `HistoricalVerifiedMaturitySchedule`: a successful check carries maturity at tolerance
> `η/2` on an earlier day, and `HistoricalVerifiedMaturitySchedule.toVerified` proves that
> the magnitude monotonicity and post-maturity tail bound promote it to maturity at the
> current day and tolerance `η`.  Thus arbitrary eventual computation and a polynomial
> per-day openness table are no longer conflated.
>
> The complete downstream one-sided contradiction is also green as
> `DeterminedViaTheory.not_eventually_weightedBias_lt_of_historicalVerifier`.  It gates the
> finite non-ROI prefix to the zero trader, proves the magnitude feature is exactly `0` then
> `1`, retains the real uniform `PolyTradeEmulatable` certificate, invokes verified
> repeatable ROI, and contradicts convergence of that eventual-one magnitude stream to zero.
> The two-sided continuation is now green too. `BiasRunHistoricallyVerifiable` isolates the
> remaining boundary as a `Nonempty HistoricalVerifiedMaturitySchedule`, so its payload is
> the actual polynomial Boolean checker plus soundness and eventual completeness, not a
> conclusion-bearing oracle. `recunbiasedaff_of_historicalVerifiers` applies the economic
> contradiction to `As` and `-As`, proves the negated-bias identity, and invokes the
> vanishing-step crossing theorem to obtain the exact zero limit point. The one-share
> `recurringunbiasedness_of_historicalVerifiers` and both-clause
> `simcal_of_historicalVerifiers` specializations are also green and axiom-clean. They remain
> conditional support capstones until the verifier constructor below is discharged.
>
> Exact finite certificate semantics and the first executable checker are now green.
> `ROI.lean` proves rational computations
> of strategy magnitude/value and trader partial magnitude/net worth agree with the real
> semantics; `AffineCoherence.lean` defines sentence atom bounds, finite Boolean worlds, and
> proves restriction/extension preserves evaluation and payouts for every bounded-support
> sentence. `Criterion.lean` exposes the existential computability assumptions as named
> `MarketComputation`/`DeductiveProcessComputation` presentations and proves that any
> terminating `evaln` output is uniquely the certified quote/stage. In
> `Calibration.lean`, `UnitMaturitySemanticCertificate.sound` proves that exact rational
> risk/payoff inequalities over all finite Boolean assignments imply the full real-valued
> `Trader.Matured` predicate; `nonempty_iff_matured` proves the converse using the explicit
> finite support sum over the deductive stage and strategy prefix. `Criterion.lean` and
> `ROI.lean` now also expose monotone bounded decoding for the deductive stage, every market
> quote, every feature, a whole finite strategy, and a whole trader prefix. On top of those
> APIs, `unitMaturityCheckAtFuel` is an actual Boolean program: it rejects timeouts, checks
> the exact rational risk inequality, and exhausts the finite Boolean worlds. A `true`
> result constructs the semantic certificate and hence real `Trader.Matured`; conversely,
> `unitMaturityCheckAtFuel_eventually_complete` proves that every genuine unit-magnitude
> maturity witness is accepted at some common finite process/market fuel. Thus the finite
> checker itself is both sound and eventually complete. The verifier boundary now
> quantifies only over rational bias gaps; arbitrary positive real gaps are reduced to this
> executable core by density of `ℚ`.
>
> **Next hard gate (now sharply isolated):** wrap the completed checker in the paper's
> polynomial historical dovetail. The missing reusable theorem is a `PolyFueled` universal
> bounded simulator: for a fixed partial-recursive checker code, the day-`n` table must run
> only `n` interpreter steps and normalize success to `0/1`, with a proved polynomial fuel
> bound in the repository's own interpreter model. Mathlib proves that `Code.evaln` is
> primitive recursive, and this repository proves polynomial bounded search once a Boolean
> table is certified, but neither fact currently supplies that `PolyFueled` runtime theorem.
> Do not disguise this as another maturity oracle. Prove the universal-simulation lemma (or
> carry it as the one explicit M7 witness), compile `unitMaturityCheckAtFuel` plus the
> `PolyTradeEmulatable` bias-run decoder to a fixed checker code, and then wrap the bounded
> dovetail table as `BiasRunHistoricallyVerifiable`. Once that constructor
> is kernel-checked, the three existing conditional capstones become the unconditional paper
> nodes and can be promoted in the ledger.
>
> **Metamathematical/halting tranche (2026-07-14):**
> `Properties/MetaLearning.lean` now supplies axiom-clean paper-facing declarations for
> `pac`, `pazfc`, `incons`, `halts`, `loops`, and `dontwait`. New one-sided
> `lic_provind_true`/`lic_provind_false` wrappers correctly allow each represented theorem
> or refutation to appear arbitrarily later than its sequence index. The representation
> interfaces are deliberately narrow: they expose polynomial sentence emission and
> truth-to-eventual-theorem/refutation laws, but no prices or asymptotic conclusions.
> `CodeHalts` uses actual `Nat.Partrec.Code` semantics; the `dontwait` proof explicitly
> lifts any bounded `evaln` success to unbounded halting before contradicting its premise.
> The concrete future first-order/Gödel syntax instantiation is ledgered as
> `M7-COMP-SYNTAX`, not hidden in these M5 composition theorems. The targeted property
> roll-up is green at 1,715 jobs and every new capstone prints only the approved axioms.
>
> **Same-day quotation/paradox tranche (2026-07-14):**
> `Properties/Introspection.lean` adds `CompletedAffineQuoteEq`, the same-day analogue of
> the audited future quote portfolio. `lic_expectations_of_probabilities` (`epr`) and
> `lic_iterated_expectations` (`er`) are exact `affprovind` consumers. The new
> `lic_paradox_resistance` (`lp`) is not a packaged convergence assumption: its quote
> supplies two completed-world-zero continuous-gate products, and Lean separately proves
> that prices persistently below or above `p∈(0,1)` would make one product uniformly
> positive. The exact asymptotic equality follows. The concrete first-order quotation and
> diagonal construction is named `M7-QUOTE-AFFINE`. The targeted property roll-up is green
> at 1,716 jobs; all four new axiom reports contain only the approved axioms.
>
> **Exact interval-introspection extension (2026-07-14):** the same file now supplies
> `IntrospectionIntervalQuote` and `lic_introspection` (`ref`). The representation boundary
> contains polynomial sentence codes, closed polynomial market-generated endpoint features,
> the completed-world quotation law, and
> exactly the two affine continuous-gate products from the paper; it contains no error or
> downstream belief bound. Lean learns both products, then independently constructs a
> positive rational `εₙ → 0` by rationally sandwiching the maximum absolute gap plus a
> vanishing `1/(n+1)` margin. Both shrunken-interval belief and expanded-interval disbelief
> implications hold on every day. Direct checking and the 1,716-job property roll-up are
> green, and `#print axioms lic_introspection` lists only the approved axioms.
>
> **Affine pseudorandomness tranche (2026-07-14):**
> `Properties/Pseudorandomness.lean` now proves the exact above, below, and equality
> branches of `thm:prandaff` over every P-generable divergent `f`-patient weighting,
> conditional on the already disclosed historical-verifier constructor and one narrowly
> operational settlement clock. The failed-diagonal selector is an actual uniformly
> emitted expressible-feature recurrence. Lean proves its values lie in `[0,1]`, its
> inclusive `f`-windows have weight at most one, and recurrent full underpricing makes its
> prefix sums tend to infinity via the audited fractional capital-recycling theorem.
> Importantly, the paper's `DeferralFunction` is not monotone: the implementation makes
> the necessary envelope `max_{k≤i} f(k)` explicit rather than silently assuming
> `f(n)≤f(i)` for `n≤i`. The activity table is ledgered as `M7-PATIENT-CLOCK`; it contains
> no price, bias, divergence, or pseudorandomness conclusion. The nonnegative branch then
> combines recurring affine unbiasedness, pseudorandom completed-theory values, and an
> explicit normalized-average contradiction; the other branches use certified affine
> negation. Direct checking reports only the approved foundational axioms.
> The first downstream specialization is also green directly: `GeneratedRatFeature`
> repairs `PGenerableRat` by requiring the emitted target-probability feature to be closed
> (a free internal `EF.var` was previously not excluded), and
> `sentenceMinusFeature` uniformly emits the exact market-generated centered family
> `φₙ-pₙ`. `lic_learning_varied_pseudorandom_above`, `_below`, and the two-sided theorem
> are the three advertised `thm:prand` conclusions, with no new trader or conclusion-
> bearing premise. The authoritative property roll-up completes all 1,717 jobs, and every
> new selector, affine, `prandaff`, and `prand` declaration prints only `propext`,
> `Classical.choice`, and `Quot.sound`.
>
> **Fixed-frequency pseudorandomness extension (2026-07-14):** `thm:benford` is now
> green as the paper's actual rational-squeeze argument. `PseudorandomFrequency` keeps the
> advertised frequency `p : ℝ` and quantifies over every P-generable, divergent,
> `f`-patient weighting. For each ε, the proof chooses a new rational `q∈[0,1]` strictly
> between `p` and the relevant ε-offset, constructs its closed one-token constant market
> feature, derives the appropriate varied-pseudorandom premise, and applies `prand`;
> endpoint frequencies zero and one are discharged from the market probability bounds.
> `PseudorandomFrequencyInfrastructure` packages only the rational centered families'
> settlement clocks and executable historical verifiers, so the existing
> `M7-PATIENT-CLOCK`/`M7-HIST-EVALN` boundary remains explicit and contains no learning
> conclusion. Direct checking and the authoritative 1,717-job property roll-up pass, and
> all six new printed declarations expose only `propext`, `Classical.choice`, and
> `Quot.sound`.
>
> **Affine-feedback Kelly tranche (2026-07-14):** `thm:wubaff` now has its explicit
> economic core. `feedbackWealthFeature` and `feedbackBetaFeature` represent the paper's
> multiplicative wealth and `δ·Wealth·W` share count as closed, rank-legal market
> features. `feedbackRoundTrip` opens each scaled `A_{f k}` position at `f k` and closes
> it at `f(k+1)`; `feedbackTrader` joins the finite prefix of those actual components on
> every day. The accounting proof works on `Trader.netWorth` itself: completed positions
> telescope to `Wealth-1`, exactly one position is live, and all later components are
> unopened. Consequently every world/day has net worth at least `-1`, every feedback day
> has net worth at least `Wealth/2-1`, and recurrent positive supported return gives a
> genuinely bounded-downside/unbounded-upside `Exploits` witness.
>
> The token boundary is explicit rather than smuggled into the economics.
> `FeedbackTraderEmission` exposes the exact day trade count, coefficient syntax, sentence
> codes, and literal `trades_eq`; `feedbackTrader_ecTok` compiles it through the segment
> emitter to a real `EfficientlyComputableTok` certificate. Its concrete bounded-dovetail
> construction from `DeferralFunction.code/fueled` is ledgered `M7-FEEDBACK-EMIT`.
> Separately, `FeedbackTruthSequence.accurate` applies the already verified `affprovind`
> theorem to a zero-valued sparse centered sequence and derives delayed-price accuracy;
> constructing that sequence from the paper's `poly(f(k+1))` truth computation is
> `M7-FEEDBACK-TRUTH`.
>
> The full conditional `wubaff` capstone is now green. `feedbackWeightedAverage_asympEq_zero`
> absorbs delayed quote error under divergent sparse mass;
> `feedbackWeightedBias_asympGE_zero` converts recurrent negative bias into the forbidden
> positive-return condition; `feedbackPrefixSum_tendsto_atTop` and
> `weightedAverage_supported_asympEq_zero_of_feedback` prove the support-image transfer
> without introducing a hidden inverse for `f`; and the explicit negated affine family
> supplies the other sign. `lic_wubaff` concludes the exact all-day `weightedBias ≈ₙ 0`
> statement. Only the disclosed `M7-FEEDBACK-EMIT` and `M7-FEEDBACK-TRUTH` constructors
> remain outside this conditional node, and neither assumes a bias conclusion.
>
> The ordinary `thm:wub` specialization is green as `AffineCombination.lic_wub`.
> It instantiates the affine theorem with the one-share `sentenceAffine` family, derives
> completed-theory determination from `TheoryTruth`, and simplifies the affine price and
> magnitude to the paper's weighted truth-minus-price bias. It inherits exactly the same
> two M7 feedback constructors and adds no new operational boundary.
>
> **Capstone verification evidence (2026-07-14):** the expanded targeted build completes
> all 1,941 jobs and a fresh full build completes all 2,661 jobs. The newly printed
> weighted-Cesàro, sparse-mass, support-transfer, one-/two-sided bias, `lic_wubaff`, and
> `lic_wub` declarations expose only `propext`, `Classical.choice`, and `Quot.sound`.
>
> **Latest verification evidence (2026-07-14):** after the Kelly/trader/feedback-bridge
> tranche, `Pseudorandomness` completes all 1,941 targeted jobs and a fresh full-project
> regression completes all 2,661 jobs. The newly printed feature, accounting, downside,
> upside, exploitation, token-certificate, criterion, and `affprovind`-bridge declarations
> expose only `propext`, `Classical.choice`, and `Quot.sound`. `git diff --check` is clean
> and the executable-placeholder scan of `Pseudorandomness.lean` is empty.

## Completed M4 handoff (historical)

> **Current correction (2026-07-13, M4 implementation complete):** the audited
> Self-Trust gap is repaired. `AffineQuotePortfolio` exposes one normalized fixed affine
> family, its polynomial emitter, its exact day-`n` gap, and bounded risk;
> `AffineQuoteEq`/`AffineQuoteGE` impose coherence only when that same portfolio is repriced
> at the actual deferred day `f n`. The four theorem-specific quote objects bundle this
> operational law with the earlier compact-code and delayed revelation-schedule
> `ValuesAt` semantics.
>
> Reusable two-sided and one-sided preemptive bridges now transport deferred-day
> coherence to the diagonal, and `cee` → `ceu` → `ccee` → `st` are all discharged and
> axiom-clean. The exact Lean `sorry` inventory under `LogicalInduction/` is zero.
>
> **Trust-surface disclosure:** the new cross-grid field is a deliberate type-`(c)`
> interface for the paper's first-order quotation/encoding-coherence mechanism. It is
> non-oracular with respect to `D n`—it constrains an actual later market price—but M7
> must construct it from the concrete quoting machinery rather than let downstream users
> assume it ad hoc. Targeted and full builds are green (2,654 jobs), the source-level
> `sorry`/`sorryAx` inventories are empty, and the six new bridge/final axiom reports contain
> only the three standard axioms. The implementation-session non-vacuity audit is recorded
> in `PROGRESS.md`; the remaining gates are Anson's statement read-through and the separate
> fresh-context audit. Do not return to the invalid polynomial-maturity-checker route.

> Supersedes the 2026-07-07 token-emission plan (fully executed; its record lives in
> `PROGRESS.md` under OPEN RISK 4 and the `def:ec` ledger rows, and in git history).

Written 2026-07-10 for the implementing session(s), possibly a weaker model. **Read
`CLAUDE.md` and `PROGRESS.md` first — they are the law; this file is the task list.**
Phases are ordered; each phase boundary is a safe stopping point with a green build.
Do the phases in order: A → B1 → C → B2 → D → E → F. One phase (or less) per session
is the right pace; do not start a phase you can't leave green.

## 0. Context snapshot (updated 2026-07-12, session 7 — M4 started)

> **M4 trust-surface/API audit and affine core started.** The seven parked theorem
> signatures were not provable as written: without daily plausible worlds their relational
> linkages are vacuous (an inconsistent `DP` makes every history satisfy `def:lic`), and
> arbitrary Lean LUV/sentence sequences need not be legal for an e.c. trader. Signatures now
> carry price bounds, plausible-world existence, non-vacuous `ValuesAt` witnesses where
> needed, and compact fixed/varying-family code interfaces (`PolySentenceCodes`,
> `PolyRatCodes`, `PolyThresholdCodeSeq`, `PGenerableRat`). `HasROI` now explicitly carries
> summability—without it, Mathlib's non-summable real `tsum = 0` convention understated
> infinite risk. Axiom-clean finite-magnitude downside bounds are proved. New
> `Affine.lean` defines `AffineCombination`, buying/scaling/negation, and the DSL
> `priceFeature`, with value/rank laws proved. The semantic repeatable-ROI core is now also
> kernel-checked: finite magnitude gives uniform downside control, ROI witnesses have finite
> `Trader.Matured` days, and `ROI.lean` proves the adaptive `β` budget stays in `[0,1]` with
> at most one unit of open capital. Semantic maturity schedules eventually close. The honest
> computability edge has now been repaired at the criterion boundary: `IsLogicalInductor`
> carries exact computable-rational-market and computable-deductive-process certificates,
> and EF has an exact rational evaluator agreeing with real denotation. The Appendix A.2
> representation gate is now closed: `EF.var`/`EF.letE` provide shared straight-line bindings
> with continuity, exact rational semantics, structural rank/cost, and injective postfix
> serialization. `sharedFeatureWeight` binds `β₀…βₙ` once each and is proved equal to the real
> budget recurrence, rank-legal, and additive in cost; `sharedBudgetedTrader` has proved
> value/magnitude formulas. The uniform emission gate is now **closed end-to-end**:
> `featureWeightBody_polySeg` emits the triangular recurrence;
> `sharedFeatureWeight_polySeg` emits the binding chain; `PolyTradeEmulatable` supplies honest
> polynomial trade counts/coefficient segments/sentence codes; and
> `sharedBudgetedTrader_ecTok` performs the nested trade/component concatenations and reaches
> the criterion's faithful `EfficientlyComputableTok`. The conditional semantic construction
> is closed too:
> `netWorth_lower_of_matured` controls post-close tails, `activeAllocation_le_one` bounds live
> risk, `allocationPrefix_not_bddAbove` proves recycling is unbounded, and `repeatableROI`
> packages the shared trader with both `EfficientlyComputableTok` and `Exploits`. The theorem
> explicitly requires a summable tolerance schedule, daily plausible worlds, and verified
> maturity; none is hidden in classical choice. Sparse/frequently-positive magnitudes are now
> supported. `VerifiedMaturitySchedule` closes the generic computability bridge: one polynomial
> checker is scanned only through the current day to obtain the exact polynomial openness table,
> while the first successful day may remain classically selected. **Next hard gate:** define and
> certify the concrete rational finite-day checker for the affine component traders from the
> computable market/process certificates. Then build/consume `thm:affpolymax` and discharge the
> seven parked expectation/Self-Trust statements.

## 0-prev-7. Context snapshot (updated 2026-07-12, session 6 — Phase F complete)

> **Phase F exit package complete.** `PROGRESS.md` now has a current ledger, an explicit
> proved-versus-M4 inventory, a flat statement/definition read-through list with source
> locations, and the fresh-context audit brief. `IntegrationTest.lean` now discharges
> concrete LUV expectation convergence via `LUV.expect_converges` in addition to the
> existing provability-induction and deference-interface checks. Targeted integration and
> full-project builds are green. The only Lean `sorry`s are exactly the seven intended M4
> statements. **M3 is implementation-complete; remaining gates are Anson's statement
> read-through and the separate fresh-context adversarial audit.**

## 0-prev-6. Context snapshot (updated 2026-07-12, session 5 — all M3 certs DONE; M3 = F)

> **Session 5 result: `excTrader_ecTok` discharged; `LUV.expect_converges` is now
> axiom-clean.** The statement now explicitly requires `LUV.PolyThresholdCodes`, a
> poly-fueled emitter for `⌜X > i/n⌝` from `⟨n,i⟩`; this is the disclosed
> propositional interface for the paper's compact Θ-definable LUV syntax. New reusable
> infrastructure in `Computable.lean`: `PolySegStream.comp`, segment-level EF constructor
> closures, and **`PolySegStream.concatVar`**, whose `segPrefix`/`segLocate` primitive-
> recursive scan emits variable-width concatenations. The certificate composes inner
> fixed-width threshold blocks, variable-width historical hysteresis blocks, and the outer
> uniform threshold-trade bundle. Full `lake build` green; remaining Lean `sorry`s are
> exactly the 7 intended M4 statements. **Remaining M3 work: Phase F only** (ledger sweep,
> statement inventory/read-through, integration re-check, fresh-context audit).

## 0-prev-5. Context snapshot (updated 2026-07-12, session 4 — thm:nd certs DONE; M3 = excTrader cert + F)

> **Session 4 result: both `thm:nd` ladder e.c. certs discharged — `lic_nonDogmatism`,
> `lic_nonDogmatism_dual`, `lic_limit_pos/lt_one` all axiom-clean.** New reusable infra
> (in `Computable.lean`): `mul_polyFueled`, `divmod1_polyFueled` (divisor `w+1` from
> input — total spec), `PolySegStream.concat` (n-fold, j-uniform runtime width),
> `PolyTokenStream.serialize_const_comp`; (in `Hysteresis.lean`):
> `buyIndEF/sellIndEF_tokenStream_comp` (rung-varying constants). **Key discovery:
> `Encodable.encode` on ℚ/ℤ is `rfl`-transparent** — `encode q = pair (encodeℤ q.num)
> q.den`, `encodeℤ (n:ℕ) = 2n`, `encodeℤ (negSucc k) = 2k+1` — so ℚ-constant tokens are
> pure poly-fueled arithmetic (`encode_ndThr`, `encode_rat_neg_div` for the sell side's
> negative numerators via `Rat.mk'`, whose num/den are `rfl`).
> - **Remaining sorry inventory: `excTrader_ecTok` (thm:ec) + 7 intended stmt-sorries.**
> - **excTrader cert (next session):** two genuinely new obstacles: (i) the hysteresis
>   chain's day-`i` blocks contain the Θ(i)-size expectation feature ⇒ **variable-width
>   blocks** — needs a prec-scan emitter (state = (block, cumulative offset), step via
>   `PolyFueled.prec`) or an affine-width `PolySegStream.blocksVar`; (ii) the
>   `⌜X.gt (i/n)⌝` sentence tokens need a **`LUV` threshold-code interface** — a new
>   hypothesis (`∃ c, PolyFueled c (fun m => encode (X.gt (m.unpair.1/m.unpair.2 : ℚ)))`
>   -shaped) added to `excTrader_ecTok` AND threaded into `LUV.expect_converges` — a
>   disclosed statement change (faithful: paper LUVs are Θ-definable, hence computable).
>   The bundle's per-threshold coefficient is *identical* across `i`, so the trade-list
>   emission itself is `concat`-shaped once the coefficient stream exists.
> - Then **F** (exit package): ledger sweep (incl. stale `thm:con` rows 114/115),
>   statement inventory for Anson, integration re-check, hand off the fresh-context
>   audit.

## 0-prev-4. Context snapshot (2026-07-12, session 3b — D2 DONE; M3 = F + cert session)

> **Session 3b result: Phase D2 landed — `thm:ec` is proved** (`LUV.expect_converges`,
> `Properties/ExpectationConvergence.lean`), exploitation axiom-clean, e.c. cert a
> disclosed `sorry`. Design as derived in the session-3 notes below, plus:
> - New **feature-generic hysteresis layer** (`buyIndF`/`sellIndF`/`hystChain` +
>   facts 1–3 + variation bookkeeping `hcDelta`/`hcBpos`/`hcBneg`/`hcBneg_unbounded`)
>   built *alongside* `Hysteresis.lean` (C's certs untouched; its `clipVal_*` lemmas
>   un-privated). Reusable for any future feature-driven hysteresis (M4's `thm:ei`
>   bundle engine should reuse it directly).
> - **`thm:ec`'s statement gained hypotheses** vs the old sorried form (trust-surface
>   change, flag at read-through): `hcons` (daily plausible worlds) and `hval`
>   (`∀ n v, ConsistentWith → ∃ x, v.ValuesAt X x` — the type-`(c)` linkage). Old
>   `Expectations.lean` sorry deleted; `expectInf` re-homed with the new hypotheses.
> - `excTrader_ecTok` sorry needs the B2 three pieces **plus a fourth**: emission of
>   `⌜X.gt (i/n)⌝` sentence-code tokens — an encodability interface on the `LUV`
>   threshold family (new modeling hypothesis to design at cert time).
> - Sorry inventory now: **3 × `ecTok` certs** (`ndLadderTrader`, `ndSellLadderTrader`,
>   `excTrader`) + 7 intended stmt-sorries. Everything else in M3 is proved.
> - **Remaining in M3: the e.c.-cert session (all three certs; see the B2 notes) and
>   F (exit package, incl. the stale `thm:con` ledger rows 114/115 sweep).**

## 0-prev-3. Context snapshot (2026-07-12, session 3 — B2 and D1 DONE; D2 started)

> **2026-07-12 session 3 result: Phase B2 (full `thm:nd`, both directions) and Phase D1
> landed; D2 step 1 (reduction generalization) done.** What changed vs. session 2:
> - **B2 REDESIGNED — read this before touching the e.c. certs.** The plan's §6 recursive
>   budget trader is **not poly-size expressible as an `EF` tree**: its update
>   `r(n+1) = r n − Pₙ·clip((r n/2 − Pₙ)·2^{n+2})` consumes the state twice ⇒ the tree
>   doubles per day; and *no* single-occurrence chain can express it (single-occurrence
>   recursions are compositions of unary affine/max steps, hence monotone-or-antitone in
>   the state; the budget update is non-monotone). Replaced by the **paper's own `app:obu`
>   scale-ladder** (sketch `main.tex:1533`), rescaled polynomially for `dd:fuel` (the
>   paper's `2^{-j}` constants have exponential-*value* encodings under the fuel clock):
>   rung `j` buys ≤ `j³` shares below `1/j³` at weight `1/j²` (coefficient const `j`);
>   spend ≤ `Σ1/j² ≤ 2`; a fired rung banks `≥ j − 1`. Both directions proved
>   (`lic_nonDogmatism`, `lic_nonDogmatism_dual`, **no price-range hypotheses**) + limit
>   corollaries (`lic_limit_pos`, `lic_limit_lt_one`). Key new engine: `armChain`
>   (generic single-occurrence arming chain, `Π(1 − sig i)`, with telescoping shares sum)
>   + `δ = 0` degenerate-ctsind padding for uniform rung widths (`1/0 = 0` in ℚ).
> - **The two `ndLadder…_ecTok` sorries are the only B2 gap** and need a dedicated
>   session: (i) runtime-divisor `divmod` (`divmodc` bakes the divisor in; block width
>   here is `Θ(n)`); (ii) `PolySegStream.concat` (n-fold segment concatenation);
>   (iii) poly-fueled emission of rung-varying ℚ-constant tokens (`⌜ndThr j⌝` from `j` —
>   requires `PolyFueled` codes for `Encodable.encode ∘ (rational function of j)`, which
>   means opening up Mathlib's ℚ-encoding; expect real friction, budget accordingly).
>   Note the paper certifies its parametric traders by **dynamic programming**
>   (`app:dynamicprogramming`) — sharing our `EF` trees don't have; that's why the ladder
>   uses product-form state.
> - **D1 done**: `PCWorld.ValuesAt.expectApprox_near` (`lem:conluvapprox`, single-LUV):
>   `ValuesAt v X x → |𝔼ₙ − x| ≤ 1/n` (one-sided `x ≤ 𝔼ₙ ≤ x + 1/n`), needs `0 < n`.
>   Floor/ceil sandwich, no filter cards. Axiom-clean.
> - **D2 step 1 done**: `exists_rat_oscillation_of_not_exists_convergesTo` (general
>   `u : ℕ → ℝ` in `[0,1]`; price form now a corollary). **D2 design notes (derived,
>   not yet implemented):** (i) generalize C's signals/state to an arbitrary feature
>   family — `buyIndOn (e : EF) a δ` with `buyIndEF φ a δ n = buyIndOn (.price φ n) a δ`
>   definitional, then `hystN` over `feat : ℕ → EF`; the expectation feature
>   `eEF n = (1/n)·Σ_{i<n} price (X.gt (i/n)) n` is a Θ(n) EF. (ii) Day-`n` trade =
>   `(List.range n).map (fun i => ((1/n)·Δₙ, X.gt (i/n)))` — bundle value in world `v`
>   with `ValuesAt X x` is `Δₙ·(Wₙ − Eₙ)`, `Wₙ ∈ [x, x + 1/n]` by D1. (iii) The C2
>   analog picks up an error term `Σ|Δₙ|/n ≤ (2B₋ + h)/n₀ + C(n₀)` — **gate the trader
>   to start at day `n₀ := ⌈8/(b−a)⌉`** (padding, as in B2) so the linear-in-`B₋` gain
>   `(b−a−2δ − 2/n₀)·B₋` keeps a positive coefficient. (iv) hval hypothesis:
>   `∀ n v, ConsistentWith (DP.D n) → ∃ x, v.ValuesAt X x`.
> - Sorry inventory: `thm:ec` (`Expectations.lean`), 2 × `ndLadder…_ecTok`
>   (`NonDogmatism.lean`), + the seven intended stmt-sorries (4 Self-Trust, 3
>   expectation-family). All disclosed, all ledgered.
> - **Remaining: D2 proper (`thm:ec` bundle-hysteresis — the feature-generic refactor
>   of `Hysteresis.lean` is the first, mechanical step), the B2 e.c.-cert session, F
>   (M3 exit package — includes the stale `thm:con` ledger rows sweep: rows 114/115
>   still say `sorry`/conditional though C closed them).**

## 0-prev-2. Context snapshot (2026-07-11, session 2 — A, B1, C, E, D3 all DONE)

> **2026-07-11 session 2 result: Phases E (per Anson's G2 decision: "the non-vacuous
> way"), C (COMPLETE — `oscillation_exploitable` un-sorried, `lic_price_convergesTo`
> axiom-clean end-to-end), and D3 landed.** What changed beyond the session-1 note below:
> - **G2 resolved**: Self-Trust stated with the faithful revelation-schedule modeling
>   (linkage at finite day `r n`, not by day `n`; dischargeable by M7, no oracle `DP`).
>   `Properties/SelfTrust.lean`: `DeferralFunction` (both paper conditions),
>   `cee`/`ceu`/`ccee`/`st` stmt+sorry+TODO(M4). `PCWorld.ValuesAt` (D1's def) is in
>   `Expectations.lean`.
> - **Phase C complete** (`Properties/Hysteresis.lean` + `PolySegStream` in
>   `Computable.lean`): hysteresis holdings state `hystN` (recursive-branch-first ⇒
>   one-sided block accretion), C2 sign-decomposition accounting
>   (`netWorth ≥ (b−a−2δ)·B₋ − (a+δ)` in every world), C3 `B₋ → ∞` by induction (no
>   interleaved-sequence construction), C4 five-segment emission. **`PolySegStream`**
>   (emitter + runtime length, closed under `append`, `blocks`, `ofTokenStream`) is the
>   new emission workhorse — use it for B2/D2, not `ecTok_of_blockStream`.
> - **D3 done**: `LUV.IsIndicator` (relational) + `thm:ei`/`loe`/`expprovind` stmts in
>   `Expectations.lean`, sorry+TODO(M4) per G1.
> - **Remaining: B2 (full `thm:nd`), D1 (`lem:conluvapprox` counting lemma), D2
>   (`thm:ec` bundle-hysteresis attempt), F (M3 exit package).** For B2's e.c.: the
>   budget state `r n` has *growing-width* increments (the Θ(j) pow-chain inside `β j`),
>   which neither `ecTok_of_blockStream` nor a fixed `PolySegStream.append` chain
>   expresses — that is the plan's option (i)/(ii) decision point; consider option (ii)
>   (constant-width restructure) first now that C is done, or an honest e.c. `sorry`.
> - Sorry inventory: `thm:ec` (`Expectations.lean:83`) — the only pre-existing one left —
>   plus the seven *intended* stmt-sorries (4 Self-Trust + 3 expectation-family).
> - Gates: G1 in force (proofs → M4); G2 resolved 2026-07-11; G3 in use since B1.

## 0-prev. Context snapshot (2026-07-11 session 1 — Phases A and B1)

> **Session-1 result: Phase A (all of A1–A3) and Phase B1 landed, green,
> axiom-clean, zero new `sorry`s.** What changed:
> - A1 was done *generically*: `evaln_prec` + **`PolyFueled.prec`** (closure of
>   `PolyFueled` under `Code.prec` for poly-bounded states) replace the planned bespoke
>   `subAux_evaln`-style proof; `divmodc_polyFueled`, `addc_polyFueled`, `mulc_polyFueled`,
>   `PolyFueled.addConst`, `PolyFueled.of_eq` are corollaries (`Computable.lean`). Any
>   future prec combinator (B2's option (i) offsets included) is now a few lines.
> - A2 = **`ecTok_of_blockStream`** (+ `length/getD_flatMap_const_width`); A3 =
>   `histTrader_ecTok`. Both in `Computable.lean`, end of file.
> - B1 = `Properties/NonDogmatism.lean` (`lic_nonDogmatism_weak`, trader `ndTrader`,
>   pow-chain `twoPowChain` — **left-nested** so the blocks are homogeneous width-3;
>   reuse it in B2/C) + the new engine `exploits_of_bddBelow_of_unbounded`
>   (`Properties/Basic.lean`, end of file). G3's hypothesis form used and ledgered.
> - Gates: **G1/G2/G3 still await Anson** (G2 blocks Phase E only). Ledger rows all in.

- Branch `logical-induction`, build green, exactly **two `sorry`s**, both disclosed
  (unchanged from 2026-07-10):
  - `oscillation_exploitable` — `LogicalInduction/Properties/Convergence.lean:62`
  - `LUV.expect_converges` (`thm:ec`) — `LogicalInduction/Expectations.lean:83`
- **Done in M3:** `thm:provind` (fixed-φ and 𝓔𝓒-sequence forms), all three `thm:lc`
  bullets, `thm:lex` (both directions), the `thm:con` reduction
  (`exists_rat_oscillation_of_not_convergesTo`), the LUV bridge object (`def:luv`,
  `def:e`), the integration test, and the entire e.c. pipeline: the token-indexed
  `def:ec` (`EfficientlyComputableTok`, wired into `IsLogicalInductor`), all seven
  traders re-certified, and the varying-length emission toolkit
  (`ifzSel`/`predc`/`subc`/`ecTok_of_tokenFn`, validated by `deepTrader_ecTok`).
- **Remaining in M3 (roadmap §4):** the `thm:con` arbitrage trader; `thm:nd`; the
  expectation family (`thm:ec`, `thm:loe`, `thm:ei`, `thm:expprovind`) + LUV approx
  lemmas; Self-Trust (`thm:cee`/`ceu`/`ccee`/`st`); the M3-exit audit package.
- No remaining trust-surface blockers: what's left is **construction and analysis**,
  plus two modeling decisions that go to Anson (§1).

## 1. Decision gates for Anson (surface early, don't guess)

Raise these in your first report; only **G2** blocks work (and only Phase E).

- **G1 — the M3/M4 boundary for the expectation family.** The paper proves `thm:ec`
  via `thm:exppolymax`, and `thm:loe`/`thm:expprovind` via the affine machinery
  (`thm:affpolymax`, `alta`, softmax traders) — all of which the roadmap places in
  **M4** (the lift hubs). Proving them ad hoc inside M3 would duplicate M4's work.
  **Recommendation:** M3 closes with `thm:con` + `thm:nd` proved, `thm:ec` proved via
  the direct bundle-hysteresis route (Phase D2, attempted after C), and
  `loe`/`ei`/`expprovind` **stated faithfully** with proofs assigned to M4. This plan
  is written to that recommendation; if Anson wants full M3 proofs instead, M4's hub
  (`thm:affpolymax`) must be pulled forward first — a different, larger plan.
- **G2 — Self-Trust reflection modeling.** `thm:cee`/`ceu`/`ccee`/`st` quantify over
  *quoted* sentences (`⌜𝔼_{f(n)}(X_n)⌝`, `⌜P_{f(n)}(φ_n)⌝`) — first-order reflection
  our propositional `Sentence` cannot express. Phase E proposes the modeling
  (reflection as explicit payout hypotheses); **statements need Anson's sign-off
  before any proof effort**, since they are pure trust surface.
- **G3 — hypothesis form for `thm:nd`.** The paper's `Θ ⊬ ¬φ` becomes, in our
  semantic substrate, "φ-satisfying plausible worlds keep existing":
  `∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ`. This is the honest
  per-day form (weaker than one world consistent forever, hence a *stronger* theorem).
  Phase B uses it; flag it in the ledger as the `def:lang`-level rendering of `⊬` and
  let Anson veto at read-through.

## 2. API cheat sheet (verified anchors — do not re-derive, do not invent)

| What | Where |
|---|---|
| `EF` syntax + `serialize` (postfix tags 0–5; trades add `[6, ⌜φ⌝]`) | `Criterion.lean:47`, `:301`, `:408` |
| `EfficientlyComputableTok` (the `def:ec` in force) | `Criterion.lean:609` |
| `IsLogicalInductor` | `Criterion.lean:623` |
| `Trader.netWorth` = `∑_{i≤n}` of `Strategy.value` = `∑ e(V)·(w φ − Vᵢ φ)` | `Criterion.lean:515`, `:534` |
| `PolyFueled` (+`const/id/pair/succ_comp/left/right/comp`) | `Computable.lean:172`–`618` |
| Arithmetic codes: `predc`, `ifzSel`, `subc` (all poly-fueled) | `Computable.lean:306`, `:631`, `:919` |
| **`ecTok_of_tokenFn`** — varying-length e.c. workhorse | `Computable.lean:1022` |
| Worked deep-trader example: `deepTrader_ecTok` | `Computable.lean:1138` |
| Fixed-length e.c.: `ecTok_of_stream` + `PolyTokenStream` combinators | `Computable.lean:809`–`908` |
| Exploitation engines (`=` and `≥` partial-sums forms) | `Properties/Basic.lean:85`, `:122` |
| `buySignal` clipped-signal template + `PCWorld.holds_*` | `Properties/Basic.lean:28`–`72` |
| `thm:con` reduction + `sorry` + chain | `Properties/Convergence.lean:17`, `:62`, `:78` |
| LUV + `expectApprox`/`expect`/`expectSeq`, `thm:ec` `sorry` | `Expectations.lean:33`–`92` |
| Paper: `thm:nd` 1528 (sketch below it) · `thm:ec` 1688 · `thm:loe` 1700 · `thm:ei` 1719 · `thm:expprovind` 1753 · `cee/ceu/ccee/st` 2045–2092 · `def:ctsind` 1174 · `def:deferralfunc` 1240 · approx lemmas 4982/5015/5111 | `notes/1609.03543v5-main.tex` |

Recurring `EF` idioms (no new constructors exist; build from these):
`x − y` = `add x (mul (const (-1)) y)`; `min x y` = `mul (const (-1)) (max (−x) (−y))`;
the paper's continuous indicator `ctsind_δ(x < c)` = `max 0 (min 1 ((c − x)·(1/δ)))`
with δ a **rational constant** (so `1/δ` is `const`; never divide by a feature —
`safeRecip` is `1/max(1,·)` and is useless below 1).

## 3. Phase A — emission tooling: `divmodc` + repeating-block streams

**Why.** Every remaining trader is *deep*: its day-`n` feature scans history, so its
token stream is `head ++ block(0) ++ block(1) ++ … ++ block(k) ++ tail` with
fixed-width blocks, where `block(j)` contains the day index `j` (a `price φ j` node
serializes to `[0, ⌜φ⌝, j]`). To emit token `i` you must compute the block index and
offset — **division/remainder by a constant width `w`**, which the toolkit does not
yet have (`deepTrader`'s blocks were width 1). This is the one genuinely new fuel
proof; everything after it is mechanical.

- **A1 — `divmodc`.** One `Code.prec` recursion on `i` whose state is
  `Nat.pair q r` (quotient, remainder): step = "if `r+1 = w` then `pair (q+1) 0` else
  `pair q (r+1)`". Equality-with-constant tests via `subc` both ways
  (`a = w` iff `(a−w)+(w−a) = 0`) fed to `ifzSel`. Model the fuel proof on
  `subAux_evaln` (`Computable.lean:949`) — it is the same shape (nested prec: the
  step applies `subc`/`ifzSel`, themselves prec), one nesting level deeper. Deliver
  `divmodc_polyFueled : PolyFueled divmodc (fun m => Nat.pair (m.unpair.1 / m.unpair.2 …))`
  — fix the exact input convention yourself (constant `w` may be baked into the code
  per-width, like `Code.const`; that is simpler than taking `w` as input and is all
  we need). **Budget: this is the phase's hard part.** If the fuel accounting won't
  close after ~2 serious attempts, `sorry` it with `-- TODO(blueprint:def:ec): need
  poly fuel bound for divmodc`, report, and continue — downstream work stays honest
  (economics don't depend on it).
- **A2 — the block-emission workhorse.** Prove once, in `Computable.lean`:
  a trader whose day-`n` stream is `head n ++ (List.range (cnt n)).flatMap (body n)
  ++ tail n` — `head`/`tail` fixed-length lists of poly-fueled tokens, `body n j` a
  fixed-width-`w` list of poly-fueled tokens of `⟨n,j⟩`, `cnt` poly — is
  `EfficientlyComputableTok`. Proof: assemble `tokenFn` from `subc` (region tests),
  `divmodc` (block index/offset), `ifzSel` (dispatch), then apply `ecTok_of_tokenFn`.
  Follow `deepTrader_ecTok`'s assembly style and `deepStream_getD`'s region-case
  lemma style. Get the statement shape right by *first* writing A3's example and
  generalizing from it — don't design the helper in the abstract.
- **A3 — validation.** A worked size-Θ(n) example whose blocks contain the day
  index: e.g. `histSum φ n = Σ_{k<n} price φ k` (left-nested adds; stream =
  `[0,⌜φ⌝,0] ++ ([0,⌜φ⌝,k,2] blocks)`), a trader trading it, certified via A2.
  This is the direct dress rehearsal for B and C's emissions.

**Done when:** A1–A3 green, `#print axioms` clean, ledger rows
(`dd:fuel (divmodc)`, `def:ec (block workhorse)`) in the same commits.

## 4. Phase B1 — `thm:nd`, weak fragment (first real deep trader)

Easiest economics of the remaining nodes; exercises Phase A end-to-end.

- **Statement** (new file `Properties/NonDogmatism.lean`):
  under `[IsLogicalInductor P DP]`, prices in `[0,1]`, and G3's hypothesis
  `hφ : ∀ n, ∃ v, v.ConsistentWith (DP.D n) ∧ v.Holds φ`:
  `∀ᶠ n in atTop, 2^(-(n+2) : ℤ) ≤ P n φ`. Ledger as `thm:nd (weak fragment)`,
  kind `C` — it is honestly *weaker* than `thm:nd` (the bound decays); B2 is the
  real node.
- **Trader** (memoryless): day-`n` buy signal `β n = max 0 (1 − 2^(n+1)·(price φ n))`
  shares of φ. The power `2^(n+1)` is a right-nested `mul`-chain of `const 2` —
  size Θ(n), constant-content width-2 blocks + a run of `[3]` tags: A2 emits it.
  Spend on day `n` is `β·P ≤ 2^(-(n+1))` (signal support is `P < 2^(-(n+1))`), so
  total spend ≤ 1.
- **New engine** (in `Properties/Basic.lean`): the existing engines force
  world-*independent* growth; here growth happens only in φ-worlds. Add the
  definitional one:
  `exploits_of_bddBelow_of_unbounded (h1 : ∀ x ∈ Tr.plausibleAssessments P DP, −C ≤ x)`
  `(h2 : ∀ B, ∃ x ∈ Tr.plausibleAssessments P DP, B < x) : Tr.Exploits P DP` —
  a few lines from `Exploits`' definition (`BddBelow ∧ ¬BddAbove`). Kind `P`.
- **Economics.** BddBelow: in any plausible world, `netWorth = Σ βᵢ(w φ − Pᵢ) ≥
  −Σ βᵢPᵢ ≥ −1`. Unbounded: if `P n φ < 2^(-(n+2))` frequently, then `β n ≥ 1/2`
  frequently, and in the day-`n` φ-world from `hφ` every term `βᵢ(1 − Pᵢ)` is ≥ 0
  with the triggered terms ≥ 1/4 — accumulate along the frequent subsequence
  (imitate `buyDaily_exploits_freq`, `Properties/ProvabilityInduction.lean:118`).
  Conclude by contradiction with `IsLogicalInductor`.

## 5. Phase C — `oscillation_exploitable`: the `thm:con` hysteresis trader

The hardest single item and the highest-value one (it un-`sorry`s
`lic_price_convergesTo`, and `P∞` then exists for B2/D). Everything is in place:
the statement is fixed (`Properties/Convergence.lean:62` — do not weaken it), the
e.c. tooling is Phase A, the target engine is B1's. Given: rationals `a < b`,
`P n φ < a` frequently, `b < P n φ` frequently, plausible worlds daily.

- **C1 — the state feature.** Fix `δ := (b−a)/4` (rational ⇒ `const`s). Signals:
  `buyInd n = ctsind` supported **inside the gap**: `1` when `P ≤ a`, `0` when
  `P ≥ a+δ` (i.e. `max 0 (min 1 ((a+δ − price φ n)·(1/δ)))`); `sellInd n`: `1` when
  `P ≥ b`, `0` when `P ≤ b−δ`. Holdings state, recursively:
  `H 0 = buyInd 0`, `H (n+1) = max (buyInd (n+1)) (H n · (1 − sellInd (n+1)))`.
  Each day adds a constant number of nodes wrapping `H n` ⇒ size Θ(n), rank ≤ n,
  block-structured stream (A2 emits; the day-`n` trade coefficient is the EF
  `H n − H (n−1)`, with the day-0 case just `H 0`).
- **C2 — the accounting (the genuine analysis).** Denote by `h i ∈ [0,1]` the real
  value `(H i).denote P` and `Δᵢ = h i − h (i−1)` (with `Δ₀ = h 0`). Key pointwise
  facts, straight from the `max`/`ctsind` shapes:
  1. `Δᵢ > 0 → P i φ < a + δ` (buys only while `buyInd > 0`);
  2. `Δᵢ < 0 → P i φ > b − δ` (sells only while `sellInd > 0`);
  3. `P i φ < a → h i = 1` (full buy); `P i φ > b → h i = 0` (full sell).
  Then **decompose by sign** — no per-swing induction needed. With
  `B₊ = Σ_{i≤n} max Δᵢ 0` and `B₋ = Σ_{i≤n} max (−Δᵢ) 0` (so `B₊ − B₋ = h n`):
  `netWorth = Σ Δᵢ(w φ − Pᵢ) = (w φ)·h n − Σ ΔᵢPᵢ ≥ −Σ ΔᵢPᵢ`
  `≥ −(a+δ)B₊ + (b−δ)B₋ = (b−a−2δ)·B₋ − (a+δ)·h n ≥ ((b−a)/2)·B₋ − (a+δ)`.
  So plausible-world net worth ≥ `((b−a)/2)·B₋ − 1` **in every world** — BddBelow is
  immediate, and unboundedness reduces to `B₋ → ∞`.
- **C3 — `B₋ → ∞`.** From the two frequency hypotheses extract an interleaved
  sequence `n₁ < m₁ < n₂ < m₂ < …` with `P n_j φ < a` and `P m_j φ > b` (standard
  double-`extraction_of_frequently_atTop` argument). By fact 3, `h n_j = 1` and
  `h m_j = 0`, so on `(n_j, m_j]` the negative variation is ≥ 1: `B₋(m_j) ≥ j`.
  Feed C2+C3 to B1's engine; close `oscillation_exploitable`; verify
  `lic_price_convergesTo` and its downstreams drop `sorryAx` from `#print axioms`.
- **C4 — e.c.** Mechanical: write `serialize (H n)` in A2's block shape (a
  `serialize_H` lemma by induction, like `serialize_srChain`), apply the workhorse.
- **Guardrail:** C2's inequality chain is where a session can thrash. The
  decomposition above is believed correct but **re-derive it, don't transcribe it**;
  if the pointwise facts 1–2 resist your exact `ctsind` encoding after ~2 serious
  attempts, adjust the *encoding* (band placement), not the statement. A session
  that lands only C1+C2 (with C3/C4 `sorry`+TODO) is a success — commit it.

## 6. Phase B2 — full `thm:nd` (budget-halving trader)

Needs C for nothing *logically*, but do it after C — the limit-form statement wants
`P∞` and the proof reuses C's state-feature techniques.

- **Statement:** under `[IsLogicalInductor]`, prices in `[0,1]`, G3's hypothesis for
  φ ⇒ `∃ ε > 0, ∀ᶠ n, ε ≤ P n φ` (liminf form; with `thm:con`, `P∞ φ > 0` as a
  corollary — state that too, with the convergence as an explicit hypothesis, like
  `lic_limit_additive`, `Properties/Coherence.lean:337`). Dual (`Θ ⊬ φ` ⇒
  `P∞ φ < 1`): apply the first form to `∼φ`? **No** — prices of `φ` and `∼φ` are not
  linked without coherence; instead run the mirrored *sell* trader (imitate
  `sellDaily` vs `buyDaily`). Ledger `thm:nd`, kind `C`.
- **Trader (paper's sketch, rendered without dividing by a feature):** carry the
  **remaining budget** `r` as the state: `r 0 = const 1`,
  `β n = max 0 (min 1 ((r n / 2 − price φ n)·2^(n+2)))` (the `2^(n+2)` is B1's
  pow-chain — a *fixed* sharpening schedule, avoiding `1/r`),
  `r (n+1) = r n − β n·(price φ n)`. Buys `β n` shares. Support of `β n` is
  `P < (r n)/2`, so `r` never drops below half its previous positive value:
  after `m` full purchases `r ≥ 2^(−m)`, total spend `≤ 1`.
- **Economics:** BddBelow by −1 as in B1. If `liminf P n φ = 0`: show by induction
  on `m` that infinitely many *full* (`β = 1`) purchases occur — having made `m`,
  `r ≥ 2^(−m)`, and eventually `2^(−(n+2)) < 2^(−(m+3))` while `P` dips below
  `2^(−(m+3)) ≤ r/4` frequently, forcing a full trigger. Each full purchase adds
  `≥ 1 − P ≥ 1/2` of φ-world value; accumulate via B1's engine. Conclude
  `¬(liminf = 0)`, i.e. the ε exists (`Filter.liminf` API, or elementarily:
  `¬∃ε` gives the frequent dips directly — prefer the elementary route, matching
  the codebase's style).
- **e.c.:** `r n` is again a constant-nodes-per-day recursive EF ⇒ A2.
  Size note: `β n` contains the Θ(n) pow-chain *and* `r n` contains all past `β`s ⇒
  `size (r n) = Θ(n²)`. **Fine** — poly-size is all `def:ec` asks; but the A2 block
  widths are now day-dependent (block `j` embeds a Θ(j) pow-chain), so A2's
  fixed-width form does not apply directly. Two options, pick at implementation
  time: (i) generalize A2 to affinely-growing block widths (offset of block `j` is
  a quadratic in `j` — still poly-fueled arithmetic via `divmodc`-style search, but
  a real generalization); (ii) restructure: replace the pow-chain sharpening with
  the constant-width trick of tracking `s n = 2^(n+2)·(r n)/2` … — **do not decide
  in advance**; try (i), stop-and-report if it balloons. An honest B2 with the
  economics proved and the e.c. cert `sorry`+TODO is committable progress —
  Rule 1 cuts the other way here (the *trader* is real; only its cert is pending),
  but say so loudly in the ledger row.

## 7. Phase D — expectation family (statements + what's provable without M4)

- **D1 — `lem:conluvapprox`, single-LUV form** (in `Expectations.lean`). Model a
  world's LUV value: `def PCWorld.ValuesAt (v) (X : LUV) (x : ℝ) : Prop :=`
  `x ∈ Icc 0 1 ∧ ∀ r : ℚ, ((r:ℝ) < x → v.Holds (X.gt r)) ∧ (x < r → ¬ v.Holds (X.gt r))`
  (the threshold-coherence rendering of the paper's "Θ represents computations";
  disclosed type-`(c)`, ledger it). Prove: `ValuesAt v X x →`
  `|X.expectApprox (fun s => v.payout s) n − x| ≤ 1/n` — pure counting
  (`#{i < n : i/n < x}` vs `n·x`, floor arithmetic; `Nat.floor` API). Kind `P`.
  The combination (`b/n`) form waits for M4's affine layer.
- **D2 — `thm:ec` via bundle hysteresis** (only after C is green). Route:
  1. Generalize `exists_rat_oscillation_of_not_convergesTo` to an arbitrary
     `u : ℕ → ℝ` with `u ∈ [0,1]` (the proof already is that general — refactor,
     keep the φ-specialization as a corollary), apply to `expectSeq P X`.
  2. The exploiter trades the **day-`n` threshold bundle** `{(1/n)·gt(i/n)}_{i<n}`
     with C's hysteresis state driven by the *expectation* value — note
     `expect P n X` is an EF-expressible function of prices (a rational-coefficient
     sum of `price` nodes), so the signals are EFs; the bundle trade list has
     length `n` (growing trade lists are fine — `serializeTrades` handles any list;
     emission is A2-shaped with the D-block caveat of B2).
  3. New wrinkle vs C: bought day-`n` bundles are sold as day-`m` bundles; in any
     world satisfying `ValuesAt v X x` (add D1's hypothesis for plausible worlds:
     `hval : ∀ n v, v.ConsistentWith (DP.D n) → ∃ x, v.ValuesAt X x`), the two
     bundles' payouts differ by ≤ `1/n + 1/m` (D1), so late swings still bank
     ≥ `(b−a)/2 − small` — thread an `n₀` cutoff through C3's extraction.
  This is C's proof again with bookkeeping, not new ideas — but it is real work.
  **Permission to stop-and-report** after a serious attempt; `thm:ec` staying
  `sorry` with C landed is still a strong M3.
- **D3 — statements only** (kind `stmt` ledger rows, proofs → M4 per G1):
  - `thm:ei` (**relational form — do not construct a canonical indicator**):
    define
    `def LUV.IsIndicator (Y : LUV) (φ : Sentence) (DP : DeductiveProcess) : Prop :=`
    `∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ r : ℚ,`
    `(r < 0 → v.Holds (Y.gt r)) ∧ (0 ≤ r → r < 1 → (v.Holds (Y.gt r) ↔ v.Holds φ))`
    `∧ (1 ≤ r → ¬ v.Holds (Y.gt r))`
    and state: `IsIndicator Y φ DP → AsympEq (Y.expectSeq P) (fun n => P n φ)`.
    **Why relational:** the tempting canonical construction (`gt r := φ` on
    `[0,1)`) makes `𝔼ₙ(indicator φ) = Pₙ φ` *definitionally* — the theorem
    evaporates. That collapse is a modeling artifact: the paper's `1(φ)`
    thresholds are *distinct sentences provably linked* to `φ`, and `thm:ei`'s
    content is the inductor learning that growing bundle of equivalences
    uniformly. Quantifying over any linked family `Y` restores exactly that
    content — and note per-threshold `thm:lex` does **not** suffice (the
    threshold set grows with `n`; it needs a bundle trader, D2's shape). So:
    state now, `sorry` with TODO(M4/D2 engine), ledger `stmt` with this
    rationale. **General principle for Phases D and E:** paper-side LUV
    *constructions* (indicators, sums `aX+bY`, quoted expectations) enter our
    modeling as **relational predicates over arbitrary threshold families**,
    never as canonical `LUV` values — constructing a representative silently
    pre-discharges the learning content.
  - `thm:loe`: state with world-level hypotheses replacing `Θ ⊢ Z = aX + bY`:
    `∀ n v (h : v.ConsistentWith (DP.D n)) x y z, v.ValuesAt X x → v.ValuesAt Y y →`
    `v.ValuesAt Z z → z = a·x + b·y` ⇒ `AsympEq (a·𝔼(X) + b·𝔼(Y)) (𝔼(Z))`
    (fixed X,Y,Z first; the 𝓔𝓒-sequence form is the M4 target). `sorry`, TODO(M4).
  - `thm:expprovind`, single-LUV form: `(∀ n v, ConsistentWith → ValuesAt … ≥ b)`
    ⇒ `AsympGE (expectSeq P X) b`-style. `sorry`, TODO(M4).
  Keep every statement short and paper-checked against the anchors in §2.

## 8. Phase E — Self-Trust statements (gate G2 first)

Statements only; **do not start proofs in M3.** Propose to Anson:

- `structure DeferralFunction` — `f : ℕ → ℕ`, `n ≤ f n`, monotone(?) — check the
  paper's `def:deferralfunc` (`main.tex:1240`) for the exact conditions; carry only
  those.
- Reflection rendered as payout hypotheses (the propositional substitute for
  quoting), e.g. for `thm:ceu`: given `φ : ℕ → Sentence`, `f : DeferralFunction`,
  and a family `Y : ℕ → LUV` with
  `hrefl : ∀ n v, v.ConsistentWith (DP.D n) → v.ValuesAt (Y n) (P (f n) (φ n))`
  ("`Y n` is the LUV ⌜P_{f n}(φ n)⌝: every plausible world values it at the actual
  future price"), conclude `AsympEq (fun n => P n (φ n)) (fun n => expect P n (Y n))`.
  State `cee` (LUV version: `X : ℕ → LUV`, `Y n` reflects `expect P (f n) (X n)`),
  `ccee` (adds the `w`-weighting — needs a product-LUV modeling note), `st`
  (adds the `ctsind` conditioning) the same way. Mind the roadmap's naming caution:
  deference "cee" = paper `thm:ceu`.
- **Two sub-decisions inside G2 — flag both explicitly:**
  1. *Timing.* The sample `hrefl` above makes day-`n` plausible worlds already
     value `Y n` at the day-`f n` price. The paper only guarantees the linkage
     facts are revealed by the deductive process *eventually* (Θ proves them;
     they enter `D` at some finite day, not necessarily by day `n`). The strong
     by-day-`n` form is simpler and may serve the deference corpus; the faithful
     form carries an explicit revelation-schedule hypothesis. Anson picks.
  2. *Non-vacuity.* In the paper the quoted sentences **exist** because `P` is a
     computable rational-valued market and `Θ` represents computations. Our
     substrate has neither (`History` is arbitrary `ℝ`-valued; `DeductiveProcess`
     carries no computability — both disclosed type-`(c)`s), so the linkage
     hypothesis is where that entire mechanism is imported. It *is* satisfiable —
     take fresh atoms per `(n, q)` and a `DP` revealing the true threshold
     literals — but that witness is an oracle-like `DP` that "knows" the future
     market: exactly the **degenerate non-vacuity** the audit protocol hunts.
     The principled discharge is M7's construction, where `P` is the computable
     `LIA` and the reflective `DP` is built, not conjured. Write both facts into
     the ledger rows at statement time.
- Ledger all four as `stmt`, provenance noting the reflection hypothesis is a
  disclosed type-`(c)` substitute for first-order quoting, awaiting G2 sign-off.
  If a statement fights the types, **that is a finding** — write it up, don't force.

## 9. Phase F — M3 exit package

1. Ledger sweep: every row's status/kind/provenance current; the two old `sorry`s'
   rows updated (hopefully to `done`); milestone table row for M3 updated with an
   honest inventory: proved / stated-only / moved-to-M4 (per G1).
2. Statement inventory for Anson's read-through: append to `PROGRESS.md` a flat
   list — every M3 top-level theorem + `file:line` + one-line gloss. Definitions
   too (`ValuesAt`, `indicator`, `DeferralFunction`, the reflection hypotheses).
3. Re-run the integration test file; confirm the deference-corpus hypotheses that
   are now discharge-able actually discharge (`thm:con` should let you strengthen
   Part C — check).
4. Remind Anson to launch the **fresh-context adversarial audit** (CLAUDE.md §audit;
   it must not be run by the session that wrote the proofs). Hand it the §2 table
   and the inventory from item 2. Known audit bait to hand over explicitly:
   the relational `IsIndicator`/`ValuesAt` modeling (D1/D3 — check the linkage
   hypotheses aren't conclusion-shaped), the Self-Trust reflection hypotheses and
   their oracle-`DP` degenerate witness (E), G3's rendering of `⊬`, and any
   engine whose hypotheses were tailored to one trader.

## 10. Standing guardrails (unchanged; the failure modes this plan is designed against)

1. **Never invent a Mathlib/Foundation name.** `rg` `.lake/packages` or `#check`
   before first use; missing ⇒ `sorry` + `-- TODO(blueprint:LABEL): need <stmt>`.
2. **Green at every commit;** small commits; `lake build LogicalInduction.<Module>`
   to iterate, full `lake build` before committing.
3. **Every new theorem ships with its ledger row in the same commit**, kind and
   provenance filled at proof time.
4. **`#print axioms` every new theorem in-file** (copy the existing idiom).
5. **No arithmetic stub may stand in for a trader** (Rule 1). A `sorry` on a
   construction is honest; a fake trader is the one unforgivable move.
6. **Don't touch:** `Construction/Brouwer.lean` interior, `Barasz/`, `lakefile.lean`,
   `lean-toolchain`, `lake-manifest.json`, the Foundation pin. Never `lake update`;
   never the `import Mathlib` umbrella.
7. **Don't redefine limit vocabulary** — `Asymptotics.lean` owns it (`dd:asymp`).
8. **Stop-and-report is a success.** ~2 serious attempts, then write up what fails
   (imitate the `oscillation_exploitable` docstring) and move on.
9. ProofWidgets "failed to reuse pre-built JS" ⇒ `cd .lake/packages/proofwidgets
   && lake build` once.
10. Use the `lean4-theorem-proving` skill. Commits: no AI co-authorship lines;
    push to `origin` freely, nowhere else.
