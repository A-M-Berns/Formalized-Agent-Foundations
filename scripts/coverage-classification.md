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
| lem:mesh | interface | the paper-strength statement exists (`LUVCombination.BoundedSequence.mesh_independence`) but is not an inventory endpoint; the inventory covers the label via the mesh-softmax witness structure |
| lem:tfdom | complete | `trading_firm_dominance`: any efficiently computable exploiter is dominated, over any rational `[0,1]` market, with no inductor hypothesis |
| thm:affcoh | conditional | analytic capstone over `[IsLogicalInductor]` with the paper's bounded-combination data |
| thm:affpolymax | conditional | same, and the price/magnitude bounds are derived from the sequence rather than assumed |
| thm:affprovind | conditional | eventual completed-theory theoremhood, paper-shaped |
| thm:benford | conditional | clock-free: maturity and settlement constructed internally; premises are the paper's theory-truth and pseudorandom frequency over a deferral function |
| thm:ccee | qualified | unconditional over `LIA` with both quoted products constructed; retained are the indicator-family source (general sources are impossible in the token model, disclosed) and injective deferral |
| thm:cee | qualified | unconditional over `LIA`, deferred-expectation quote constructed; retained are injective deferral (vs. the paper's `f n > n`) and the paper's own "the source is an LUV of the theory" premise |
| thm:ceu | qualified | unconditional over `LIA`, quote code constructed; the sole qualification is now the deferral narrowing — `f` assumed injective where `def:deferralfunc` asks only `f n > n` |
| thm:con | conditional | genuine trader proof over `[IsLogicalInductor]` |
| thm:dontwait | complete | unconditional over `LIA` on the provability process (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:dus | qualified | unconditional over `LIA` **and over the semimeasure**: the constructed dovetail dominates every lower-semicomputable continuous semimeasure with no approximation or emission input; the retained input is the prefix-sentence code emitter `BitPrefixCodeComputation` |
| thm:ec | qualified | retains the rate-free per-grid world-valuation `hval` (`ApproxValuesUpTo`, the paper's `lem:conluvapprox`) and the LUV threshold-code interface |
| thm:ei | conditional | genuine trader proof over `[IsLogicalInductor]`; `IsIndicator` is the paper's own `1(φ)` hypothesis rendered relationally by design, not a retained interface |
| thm:epr | complete | unconditional over `LIA`; the quote code is constructed from the market program (`theoremPriceQuoteCode`), leaving only the sentence family and its codes |
| thm:er | complete | unconditional over `LIA`; the expectation quote code is constructed via `expectQuote_computable`, leaving only the LUV family and its threshold codes |
| thm:expcoh | qualified | representation discharged from arithmetic for `dd:luv-arith` (`expcoh_arith`); the mesh-softmax operational witness is retained even there, and general LUVs also retain `WorldValued`/`ConvergencePresentation` |
| thm:exppolymax | qualified | same pattern (`exppolymax_arith`), mesh-softmax witness retained |
| thm:expprovind | qualified | **fully unconditional for certified `dd:luv-arith`** (all three comparison forms); general LUV-combination forms retain the exact-theory presentation |
| thm:halts | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:ifp | qualified | efficiently-patchable perturbations only — the patch certificate is not inhabitable for every computable market; the paper's unrestricted statement has a recorded erratum (PE1) |
| thm:incons | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:lc | conditional | probability measure on completed worlds constructed, over `[IsLogicalInductor]` |
| thm:lex | conditional | propositional rendering over `[IsLogicalInductor]` |
| thm:li | complete | computable finite-support belief-sequence form, including the paper's `def:belseq` emission conjunct (`exists_liaEntries_code`) |
| thm:lia | complete | the central construction, kernel-clean; the sole premise is a computable deductive process |
| thm:loe | qualified | varying-sequence linearity retains a world-valuation premise (exact-theory presentation for the combination form); fully unconditional for `dd:luv-arith` fixed indices |
| thm:loops | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:lp | complete | public diagonal constructed from the market computation; unconditional over `LIA` |
| thm:nd | conditional | the plausibility premise is the paper's own |
| thm:ob | conditional | paper-strength bounds at genuine universal prefix complexity `κ_U` (invariance proved); presentation, threshold emission, and negation compiler are all constructed, so only `[IsLogicalInductor]` and joint consistency remain |
| thm:obu | conditional | over `[IsLogicalInductor]` with the paper's enumeration data |
| thm:pac | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:pazfc | complete | unconditional over `LIA` (Σ₁-sound `Θ ⊇ IΣ₁`) |
| thm:peraffkno | conditional | analytic capstone over `[IsLogicalInductor]` |
| thm:perexpkno | qualified | `perexpkno_arith` discharges the representation for `dd:luv-arith`; the mesh-softmax witness is retained, and general LUVs also retain the convergence presentation |
| thm:perkno | conditional | over `[IsLogicalInductor]` with the paper's own probability sequence |
| thm:prand | conditional | clock-free varied-frequency form; the target rationals enter as a market-generable feature (`def:ece`), as the paper requires |
| thm:prandaff | conditional | clock-free: the patient settlement clock is constructed from the inductor, leaving exactly the paper's bounded-combination, determination and pseudorandomness premises |
| thm:prandexp | qualified | clock-free (the mesh settlement checker is constructed against a vanishing tolerance); retains only the threshold-LUV world-valuation `WorldValued` and a share-norm bound |
| thm:provind | conditional | eventual completed-theory theoremhood, paper-shaped |
| thm:recunbiasedaff | conditional | maturity constructed internally; no clock or verifier premise remains |
| thm:recurringunbiasedness | conditional | same, over the sentence-affine family |
| thm:recurringunbiasednessexp | qualified | takes the paper's combination-level determination (`def:affthmval`), repairing the PE2 hypothesis-swap erratum; retains `WorldValued` and a share-norm bound |
| thm:ref | complete | unconditional over `LIA`; the interval quote is constructed from the market's exact rational quote, leaving only the paper's own generable interval/width data |
| thm:scon | complete | growing-form `hjoint` deleted — derived by propositional compactness (`Framework/Compactness.lean`) or vacuous by the degenerate branch |
| thm:simcal | conditional | maturity constructed internally; the calibration indicator's generability and divergence are the paper's premises |
| thm:st | qualified | the abstract endpoint takes P-generable `p` (`def:ece`) with `SelfTrustQuote` reflection data; `lic_self_trust_closed` discharges that data over `LIA` at the cost of e.c. `p` and injective deferral |
| thm:strict | qualified | the separator argument is fully constructed from Kleene inseparability (the stage classes are proved null); the retained input is the bit-prefix sentence presentation and its atom-code computability |
| thm:tbo | conditional | over `[IsLogicalInductor]` |
| thm:wub | qualified | unconditional over `LIA`; the emitter and truth bridge are constructed, leaving only the deadline-bounded truth program `FeedbackTruthComputation` |
| thm:wubaff | qualified | same: emitter and truth bridge constructed, only `FeedbackTruthComputation` retained, unconditional over `LIA` |
| thm:wubexp | qualified | same plus the threshold-LUV world-valuation; `wubexp_arith` discharges the representation half for `dd:luv-arith` |
