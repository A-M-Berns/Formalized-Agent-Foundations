# M5 verification packet

This is the compact exit-review surface for the conditional M5 property tail. It does not
replace `PROGRESS.md`: the flat ledger remains authoritative for dependencies, proof status,
and trust classification. This packet records the two independent review gates and their
falsifiable sign-off evidence.

Current mechanical evidence (2026-07-14):

- `lake build LogicalInduction.Properties LogicalInduction.IntegrationTest`: 1,958/1,958.
- `lake build`: 2,670/2,670.
- Executable `sorry`/`admit`/`sorryAx` scan: empty (broad word matches are comments only).
- Printed M5 capstones: only `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check`: clean.

Mechanical evidence is not sign-off for either review below.

## A. Human paper-statement read-through

**Confirmed by Anson in the project thread on 2026-07-14.** This confirmation covers every
row in section A; the individual boxes are retained as the original review worksheet.

For every row, compare the paper statement at the vendored TeX anchor with the named Lean
declaration. Check quantifier order, uniformity, comparison direction, conclusion strength,
and whether every extra premise is a disclosed representation/operational boundary rather
than a hidden form of the conclusion.

### Timely, affine, calibration, and statistical nodes

| Check | Paper anchor | Lean declaration(s) | Statement checkpoint |
|---|---|---|---|
| [ ] | `thm:perkno`, TeX 1105 | `lic_persistence_of_knowledge` | All three future-knowledge clauses; varying rational targets are uniformly generated. |
| [ ] | `thm:tbo`, TeX 1130 | `lic_preemptive_learning` | Exact one-share preemptive-learning extrema, not pointwise convergence. |
| [ ] | `thm:simcal`, TeX 1193 | `AffineCombination.simcal_of_historicalVerifiers` | Both recurring-calibration conclusions; verifier is `M7-HIST-EVALN`, not calibration evidence. |
| [ ] | `thm:recurringunbiasedness`, TeX 1225 | `AffineCombination.recurringunbiasedness_of_historicalVerifiers` | Zero is a limit point for every legal divergent weighting. |
| [ ] | `thm:wub`, TeX 1249 | `AffineCombination.lic_wub` | All-day weighted bias converges to zero under good feedback. |
| [ ] | `thm:benford`, TeX 1283 | `lic_learning_pseudorandom_frequency` | Real target frequency, including endpoint cases; no rational-target weakening. |
| [ ] | `thm:prand`, TeX 1314 | `lic_learning_varied_pseudorandom_{above,below}` and `lic_learning_varied_pseudorandom` | Above, below, and equality directions for generated varying targets. |
| [ ] | `thm:affprovind`, TeX 1378 | `PolySequence.affine_provind_theory_{ge,le,eq}` | Completed-theory premise and exact asymptotic comparison; no same-day-deduction substitution. |
| [ ] | `thm:affcoh`, TeX 1399 | `PolySequence.affcoh` | Both completed-world/limiting-belief/diagonal liminf–limsup chains. |
| [ ] | `thm:peraffkno`, TeX 1437 | `AffineCombination.PolySequence.peraffkno` | Uniform future `sInf`/`sSup` equalities, not fixed-sequence convergence only. |
| [ ] | `thm:affpolymax`, TeX 1451 | `BoundedCombinationSequence.affpolymax` | Arbitrary bounded combination sequence; constant included in the `L¹` bound. |
| [ ] | `thm:recunbiasedaff`, TeX 1469 | `BoundedCombinationSequence.recunbiasedaff` | Arbitrary `BCS`; exact zero limit point after canonical positive normalization; outer historical dovetail alone remains `M7-HIST-EVALN`. |
| [ ] | `thm:wubaff`, TeX 1480 | `BoundedCombinationSequence.wubaff` | Arbitrary `BCS`; exact weighted-bias convergence after scale cancellation; support-image reindexing and both signs are proved. |
| [ ] | `thm:prandaff`, TeX 1492 | `BoundedCombinationSequence.prandaff_{above,below}` and `.prandaff` | Arbitrary `BCS`, all comparison directions; patient selector is legal for nonmonotone deferrals. |

### Closure, non-dogmatism, and semimeasures

| Check | Paper anchor | Lean declaration(s) | Statement checkpoint |
|---|---|---|---|
| [ ] | `thm:ifp`, TeX 1521 | `lic_iff_of_finitePerturbation` | Biconditional closure; prefix compiler is `M7-PREFIX-PATCH`, not exploitation transport. |
| [ ] | `thm:nd`, TeX 1528 | `lic_nonDogmatism`, `lic_nonDogmatism_dual`, `lic_limit_pos`, `lic_limit_lt_one` | Both non-dogmatism directions and correct non-provability conditions. |
| [ ] | `thm:obu`, TeX 1540 | `lic_uniform_nonDogmatism` | One common positive limit bound for the whole efficient enumeration. |
| [ ] | `thm:ob`, TeX 1552 | `lic_occamBounds` | Lower and upper bounds use one common constant and fixed negation overhead. |
| [ ] | `thm:dus`, TeX 1561 | `lic_domination_universalSemimeasure` | One fixed positive domination constant for every finite prefix. |
| [ ] | `thm:strict`, TeX 1575 | `lic_strict_domination_universalSemimeasure` | Genuine failure of reverse domination, not a definitional counterexample. |
| [ ] | `thm:scon`, TeX 1613 | `lic_conditioned_gated` | Logical-inductor closure for the exact capped conditional market and combined process. |

### Expectation nodes

| Check | Paper anchor | Lean declaration(s) | Statement checkpoint |
|---|---|---|---|
| [ ] | `thm:expcoh`, TeX 1762 | `LUVCombination.BoundedSequence.expcoh` | Both completed-world/limiting-expectation/diagonal chains. |
| [ ] | `thm:perexpkno`, TeX 1782 | `LUVCombination.BoundedSequence.perexpkno` | Both uniform future-expectation extrema equal limiting expectation. |
| [ ] | `thm:exppolymax`, TeX 1794 | `LUVCombination.BoundedSequence.exppolymax` | Both diagonal/cross-day expectation extrema equalities. |
| [ ] | `thm:recurringunbiasednessexp`, TeX 1812 | `LUVCombination.BoundedSequence.recurringunbiasednessexp` | Exact determined LUV truth; zero limit point after weighted mesh-error transfer. |
| [ ] | `thm:wubexp`, TeX 1822 | `LUVCombination.BoundedSequence.wubexp` | Exact expectation bias converges to zero; normalization is cancelled. |
| [ ] | `thm:prandexp`, TeX 1834 | `LUVCombination.BoundedSequence.prandexp`, `.prandexp_below`, `.prandexp_eq` | Paper-facing above direction plus the appendix's below/equality variants. |

### Consistency, computation, and introspection

| Check | Paper anchor | Lean declaration(s) | Statement checkpoint |
|---|---|---|---|
| [ ] | `thm:pac`, TeX 1869 | `lic_belief_finitistic_consistency` | Every true represented finite consistency claim tends to one. |
| [ ] | `thm:pazfc`, TeX 1881 | `lic_belief_stronger_theory_consistency` | Same conclusion for the represented stronger-theory consistency sequence. |
| [ ] | `thm:incons`, TeX 1893 | `lic_disbelief_inconsistent_theories` | Inconsistency claims tend to one and consistency claims to zero. |
| [ ] | `thm:halts`, TeX 1923 | `lic_learns_halting_patterns` | Actual unrestricted halting implies belief tends to one. |
| [ ] | `thm:loops`, TeX 1935 | `lic_learns_provable_nonhalting_patterns` | Provable non-halting, not arbitrary semantic non-halting, implies belief tends to zero. |
| [ ] | `thm:dontwait`, TeX 1946 | `lic_does_not_anticipate_halting` | Non-halting programs do not receive persistent bounded-horizon halting probability. |
| [ ] | `thm:ref`, TeX 1969 | `lic_introspection`; `IntrospectionIntervalQuote.{lower,upper}_pgenerable` | Market-generated endpoint features; both interval implications with positive rational error tending to zero. |
| [ ] | `thm:lp`, TeX 1992 | `lic_paradox_resistance` | Diagonal paradox price converges to the specified interior rational `p`. |
| [ ] | `thm:epr`, TeX 2014 | `lic_expectations_of_probabilities` | Same-day price equals expectation of its represented quote asymptotically. |
| [ ] | `thm:er`, TeX 2022 | `lic_iterated_expectations` | Same-day expectation equals expectation of its represented expectation quote. |

### Regression nodes

| Check | Paper anchor | Lean declaration(s) | Statement checkpoint |
|---|---|---|---|
| [ ] | `thm:lex`, TeX 1346 | `lic_learning_exclusive_exhaustive` | Fixed positive `k`, uniform tuple emitter, and diagonal price sum tends to one. |
| [ ] | `thm:nd`, TeX 1528 | declarations above | Recheck scale-ladder token certificates and non-vacuous plausible-world upside after M5 imports. |

Human reviewer: Anson (confirmed in project thread)  Date: 2026-07-14

Disposition: [x] aligned  [ ] findings recorded below

Findings / required changes:

1. The confirmed reading is subject to three explicit TeX errata identified by the fresh
   audit: `recurringunbiasednessexp` contains a support clause using an unbound `f` (Lean
   proves the coherent stronger every-divergent-weighting reading); `wubexp` omits the
   support-in-feedback-image premise used by the ordinary/affine theorem and proof (Lean
   restores it); and `pazfc` uses an unbound `f` (Lean quantifies through the represented
   arbitrary fixed computable bound). These readings are ledgered in `PROGRESS.md`.

## B. Separate fresh-context adversarial audit

The auditor must not rely on this packet's “statement checkpoint” prose as proof. Inspect the
actual declarations, structures, and theorem bodies.

Required attacks:

1. Search every public capstone premise for the conclusion itself, an asymptotically
   equivalent restatement, or an opaque certificate that entails the central proof step.
2. For every `M7-*` structure, classify each field as syntax, computability, semantics, or
   economics. Reject any field containing the advertised market limit, bias, calibration,
   domination, exploitation, or logical-inductor conclusion.
3. For every constructed trader, locate the exact `EfficientlyComputableTok` theorem, global
   downside/ROI theorem, and non-vacuous unbounded-upside theorem. Check that the plausible
   worlds used by the upside proof exist under the capstone's hypotheses.
4. Attack the known repaired points: arbitrary-bound `affpolymax`; uniform future extrema in
   `peraffkno`; same-day versus eventually proved `affprovind`; nonmonotone deferrals;
   conditioning's polynomial telescoping budget; exact LUV truth versus mesh truth.
5. Check that each conditional representation boundary is named in `PROGRESS.md` and paired
   with one concrete M7 construction obligation. Reject generic “assume computable” or
   “assume the theorem's semantic bridge” placeholders.

Known boundary inventory:

- `M7-HIST-EVALN`
- `M7-COMP-SYNTAX`
- `M7-QUOTE-AFFINE`
- `M7-PATIENT-CLOCK`
- `M7-FEEDBACK-EMIT`
- `M7-FEEDBACK-TRUTH`
- `M7-PREFIX-PATCH`
- `M7-CE-REPETITION`
- `M7-PREFIX-MACHINE`
- `M7-DUS-APPROX`
- `M7-DUS-PREFIX-SYNTAX`
- `M7-STRICT-SEPARATORS`
- `M7-SCON-COMPILER`
- `M7-SCON-PRESENTATION`
- `M7-LUV-SYNTAX`

Fresh-context auditor: Codex subagent `/root/m5_adversarial_audit`  Date: 2026-07-14

Disposition: [x] pass  [x] findings fixed  [x] paper errata explicitly triaged below

Findings / triage:

1. **Arbitrary-BCS affine scope:** the initial audit found unit-magnitude-only public
   capstones. Fixed by `BoundedCombinationSequence.unitNormalization` and the paper-facing
   `recunbiasedaff`, `wubaff`, and `prandaff_{above,below,eq}` wrappers, which formulate the
   M7 inputs for the canonical normalized family and cancel the positive scale.
2. **`thm:ref` endpoint scope:** the initial audit found independently polynomial rational
   endpoints instead of market-generated endpoints. Fixed by replacing `lower_codes` and
   `upper_codes` with closed `GeneratedRatFeature` witnesses; the package now entails
   `PGenerableRat P a` and `PGenerableRat P b` exactly.
3. **Boundary inventory:** added concrete `M7-LUV-SYNTAX`,
   `M7-DUS-PREFIX-SYNTAX`, and `M7-SCON-PRESENTATION` obligations and extended
   `M7-QUOTE-AFFINE` to consume generated interval features.
4. **TeX inconsistencies:** explicitly triaged the stray/omitted `f` support clauses for
   `recurringunbiasednessexp`, `wubexp`, and `pazfc` in section A and the flat ledger.
5. **Correction recheck:** the same independent auditor returned PASS after inspecting each
   repaired declaration and boundary, finding no new circularity or vacuity, and directly
   checking `AffinePreemptiveLearning`, `Calibration`, `Pseudorandomness`, `Introspection`,
   `ExpectationProperties`, and `MetaLearning`. The public roll-up and full-project builds
   independently pass at 1,958 and 2,670 jobs; printed dependencies remain only `propext`,
   `Classical.choice`, and `Quot.sound`.

## C. Author-context pre-audit (not gate B)

Run on 2026-07-14 to remove avoidable defects before independent review. This section is
evidence of inspection, but cannot satisfy the fresh-context requirement.

### Boundary-field inspection

| Boundary | Actual field classes | Author-context result |
|---|---|---|
| `M7-HIST-EVALN` / `BiasRunHistoricallyVerifiable` | Quantified ROI antecedent; existence of a concrete `HistoricalVerifiedMaturitySchedule` with checker/clock/soundness/completeness | No bias, limit point, or market-learning conclusion. The economic ROI antecedent is proved outside; the boundary supplies only the outer historical dovetail. Pass with fresh-audit attention. |
| `M7-COMP-SYNTAX` | Sentence streams, polynomial sentence codes, eventual proof/refutation representation laws | No prices or asymptotic conclusions. Pass. |
| `M7-QUOTE-AFFINE` | Polynomial quote syntax, exact reflected semantics, explicit polynomial affine portfolio, exact completed-world-zero or deferred-price identity | No asymptotic conclusion. This is intentionally the quotation representation boundary; fresh audit must ensure each exact identity follows from the future first-order syntax. Pass as disclosed type-`(c)`. |
| `M7-PATIENT-CLOCK` | Polynomial Boolean activity, antitonicity, deadline coverage, eventual inactivity, exact finite-stage settlement | No divergence, bias, pseudorandomness, or diagonal-price conclusion. Pass. |
| `M7-FEEDBACK-EMIT` | Trade counts, coefficient/sentence token streams, exact reconstruction of the concrete trader for all small Kelly fractions and both signs | No market values, wealth, exploitation, or bias. Pass. |
| `M7-FEEDBACK-TRUTH` | Determination, explicit sparse polynomial affine sequence, bounds, zero completed-world value, exact delayed quote-error price identity | The price identity is an exact syntax/representation equation, not asymptotic accuracy; `FeedbackTruthSequence.accurate` derives accuracy via `affprovind`. Pass with fresh-audit attention. |
| `M7-PREFIX-PATCH` | Exact finite rational quote table and preservation of token emission under literal `freezeBefore` | No exploitation or logical-inductor conclusion. Pass. |
| `M7-CE-REPETITION` | Polynomial repeated sentence stream, infinite repetition, source soundness and coverage | No prices or limiting belief. Pass. |
| `M7-PREFIX-MACHINE` | Sentence enumeration, from-below Kraft approximations, finite Kraft law, coverage, gate-token compilers, fixed negation overhead | No market or Occam inequality. Pass. |
| `M7-DUS-APPROX` | From-below prefix-mass table, polynomial rational tokens, convergence, derived gate-token compiler | No price, purchase, plausible world, or domination conclusion. Pass. |
| `M7-DUS-PREFIX-SYNTAX` | Polynomial prefix sentences, exact independent-bit semantics, finite realizability | No price, trader payoff, semimeasure domination, or asymptotic conclusion. Pass as disclosed type-`(c)`. |
| `M7-STRICT-SEPARATORS` | Nested prefixes, length growth, repetition, finite joint possibility, semimeasure mass tending to zero | Contains the intended computability-theory separator theorem but no market or non-domination conclusion. Pass as disclosed type-`(c)`. |
| `M7-SCON-COMPILER` | Positive denominator patch, computable conditional market, preservation of token emission for the concrete gated translation | No wealth, floor, exploitation, or LIC field; those are proved by `toCompiler`. Pass. |
| `M7-SCON-PRESENTATION` | Polynomial conjunction syntax, exact stagewise union semantics, computable combined process | No conditional price, trader, wealth, exploitation, or LIC field. Pass as disclosed type-`(c)`. |
| `M7-LUV-SYNTAX` | Exact threshold truth, threshold-code emission, daily values, softmax polynomiality/bounds/magnitude | No expectation limit, bias, persistence, or learning conclusion. Pass. |

### Trader/certificate inspection

The criterion-facing exploiters have literal token certificates and separate economic
proofs:

- `eqTr_ec` + `eqTr_exploits`;
- `obuTrader_ecTok` + the global `-2` floor and `obuTrader_exploits`;
- `obTrader_ecTok` + `obTrader_netWorth_ge_neg_two` + `obTrader_exploits`;
- `feedbackTrader_ecTok` + `feedbackTrader_netWorth_lower` +
  `feedbackTrader_exploits_of_frequently_positive_return`;
- `dusScaleTrader_ecTok` / `dusTrader_ecTok` + the `-1` / `-2` floors + explicit
  consistent-world upside and `dusTrader_exploits_of_failed_scales`;
- `sharedBudgetedTrader_ecTok` + its floor/upside theorem in the ROI hub, which is the
  actual criterion-facing trader assembled from the uniformly `PolyTradeEmulatable`
  gradual and bias-run families;
- conditioning and finite-prefix transformations preserve `EfficientlyComputableTok`
  through their named operational witnesses, while their floor and exploitation transport
  are proved separately.

No criterion invocation was found that supplies only a family-level computability claim
for the actual exploiting trader: the repeatable-ROI routes construct
`sharedBudgetedTrader` and prove its `EfficientlyComputableTok` certificate before invoking
`IsLogicalInductor.noExploit`.

Author-context disposition: no new blocking finding. The three items explicitly marked
“fresh-audit attention” remain priority attacks for the independent auditor.
