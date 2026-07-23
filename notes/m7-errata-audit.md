Anson: keep in mind that this was written by an adversarial instance! take these criticisms seriously but check them against your own judgment.

# M7-ERRATA-AUDIT — adversarial audit for faithfulness to *Logical Induction*

_Run 2026-07-22 against the current workspace and reclassified 2026-07-23 to separate paper
errata from repository findings. This report supersedes the 2026-07-21 version of this file.
The audit compared the Lean statements and boundary structures with
`notes/1609.03543v5-main.tex`, rather than treating theorem names, `Paper node:` annotations,
README claims, or successful compilation as evidence of statement fidelity._

Paper-level defects found during that comparison are maintained separately in
[`logical-induction-paper-errata.md`](logical-induction-paper-errata.md) and are outside this
repository audit's findings. Finding identifiers remain stable when an item leaves scope, so
later identifiers are not renumbered.

## Verdict

The development is kernel-clean and contains a substantial, non-vacuous construction of an
LIA-like market. It is **not yet a faithful full formalization of the paper**.

The strongest defensible description is:

> A sound formalization of the central construction and many of the paper's economic
> arguments, relative to a repository-specific efficiency model, together with a partly
> conditional and sometimes weakened formalization of the property theorems.

No Lean soundness failure was found. The discrepancies are statement-level:

1. the Lean Logical Induction Criterion applies to a broader class than the paper's markets;
2. some named paper theorems are represented only by components or strict special cases;
3. several property families retain operational or representation hypotheses that the paper
   discharges;
4. some advertised “unconditional” wrappers discharge only the base market/inductor, while
   retaining the main theorem-specific construction as a caller hypothesis; and
5. the build-enforced endpoint inventory does not cover the full paper-facing surface.

The central LIA construction itself held up well: it reaches `noExploit` through the actual
TradingFirm-dominance and MarketMaker argument, not through a stub or conclusion-bearing
interface.

## Findings, ranked

### F0 — HIGH / definition mismatch: `IsLogicalInductor` does not require prices in `[0,1]`

**Paper.** `def:market`, `def:pricing`, and `def:marketprocess` make `[0,1]` part of the
definition of valuations, pricings, and markets (`main.tex:670–691`). The Logical Induction
Criterion is a predicate on those markets.

**Lean.** `Framework/Foundations.lean:40–53` defines

```lean
Valuation := Sentence → ℝ
History   := ℕ → Valuation
```

and says the range restriction will be imposed downstream. It is not imposed in
`ComputableMarket` (`Framework/Criterion.lean:962–972`) or `IsLogicalInductor`
(`Criterion.lean:1448–1463`). The latter stores only:

```lean
marketComputable
processComputable
noExploit
```

Most property theorems therefore take an additional
`hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1`; for example, `lic_price_convergesTo`
(`Properties/Coherence.lean:411–428`).

**Consequence.** `IsLogicalInductor P DP` is strictly broader than “`P` is a market satisfying
the LIC” in the paper. A computable rational history with out-of-range prices is eligible for
the Lean class. This makes the docstring's claim that the class is `def:lic` “on the nose” too
strong, even though the constructed `liaHistory` separately satisfies `liaHistory_range`.

**Required repair.** Put the range law into `ComputableMarket`, `MarketComputation`, or
`IsLogicalInductor`, then remove the redundant downstream hypotheses. A compatibility layer
could retain unrestricted `History` for expressible-feature semantics.

### F1 — HIGH / incomplete theorem: Limit Coherence does not construct the paper's measure

**Paper.** `thm:lc` says that `P∞` gives rise to a probability measure on the worlds
consistent with the theory (`main.tex:1015–1021`). The proof invokes the three Gaifman
conditions and then obtains the measure.

**Lean.** `Properties/Coherence.lean` proves component identities:

- `lic_disprovable_tendsto_zero`;
- `lic_excl_gap_tendsto_zero`; and
- `lic_limit_additive`.

There is no construction or existence theorem for a probability measure on completed worlds,
and no formalized Gaifman extension step.

Two components also use stronger hypotheses than the paper:

```lean
hdis  : ∀ n, (∼φ) ∈ DP.D n
hexcl : ∀ n, (∼(φ ⋏ ψ)) ∈ DP.D n
```

(`Coherence.lean:113–116`, `312–315`). A theorem of the completed theory need only appear at
some finite stage. Later `lic_provind_true` / `lic_provind_false` wrappers correctly accept
eventual theoremhood, so some missing components may be recoverable, but the labeled
`thm:lc` surface is not the paper theorem.

**Required repair.** Package convergence, theorem/refutation limits, and finite additivity
under the paper's completed-theory hypotheses, then prove the measure-existence conclusion.

**Repair status (2026-07-22): resolved.** `Properties/LimitCoherence.lean` now derives the
finite Gaifman conditions from the logical-inductor laws, constructs a projective family of
finite Boolean laws, proves its cylinder content countably additive by compactness, and
extends it to a probability measure on `PCWorld`. The paper-facing `lic_limitCoherence`
theorem identifies every sentence-event probability with `limitingBelief` and proves the
measure is almost-everywhere concentrated on worlds consistent with the completed deductive
process. Its theorem/refutation lemmas accept membership at an arbitrary finite stage. The
endpoint is exported and guarded by `#assert_axioms_clean`.

### F2 — RESOLVED: recurring unbiasedness and statistical learning

**Repair status (2026-07-22): resolved.**
`Construction/Witnesses/HistoricalMaturity.lean` compiles the semantic finite-world
maturity test into a primitive-recursive, non-dependent Boolean checker. It flattens each
uniformly emulatable trader family's dated trades, computes exact rational magnitude and
world value from `IsLogicalInductor.marketComputable` and `.processComputable`, semidecides
successful maturity checks, and uses the shared bounded dovetail to construct a
`HistoricalVerifiedMaturitySchedule`. Soundness and eventual completeness are proved by an
equivalence with the existing semantic `unitMaturityCheckAtFuel`.

The constructor is consumed internally by the one-sided recurring-bias contradiction and
therefore by the exact paper-facing `recunbiasedaff`, `recurringunbiasedness`, and `simcal`
endpoints. The same unconditional route now feeds affine, sentence, and expectation
pseudorandom learning. `PseudorandomFrequencyInfrastructure` carries settlement clocks
only; the old verifier-bearing interface and the old conditional capstones remain available
under explicit `..._of_historicalVerifiers` names. Integration tests no longer accept an
`hverify` premise for recurring unbiasedness, `prandaff`, or `prandexp`.

### F3 — RESOLVED: Paradox Resistance derives its public diagonal

**Repair status (2026-07-22): resolved.**
`Construction/Witnesses/QuotationAffine.lean` now constructs the diagonal from a named
`MarketComputation`. `diagonalPriceDecisionPart` runs the market on the public atom selected
by a candidate program and returns `1` exactly when that atom's same-day price is below `p`;
Mathlib's formalized Kleene second recursion theorem supplies
`diagonalPriceDecisionCode`, whose evaluation is proved equal to that computation.

The value-`1` and value-`0` fibers of this actual fixed program supply both sides of the
inherited `BooleanQuoteCode`. `diagonalPriceBody` represents the same predicate in FFL
arithmetic, `diagonalPriceFixedpoint_spec` connects its genuine
`parameterizedFixedpoint` to the program predicate, and
`parameterizedDiagonalQuoteCodeOfMarket_public_fixedpoint` proves that this represented
fixed point is exactly the same-day price comparison for the inherited public sentence.
Together with `ParameterizedDiagonalQuoteCode.diagonal_law`, this gives both the internal
arithmetic diagonal equation and its public market semantics.

`paradoxResistanceQuoteOfDiagonal` and `lic_paradox_resistance_ofDiagonal` now take the
named market computation and construct the quote internally. They accept no `truth`,
`ParameterizedDiagonalQuoteCode`, or semantic self-reference premise. The constructed-LIA
wrapper names `theoremMarketComputation` and `theoremDiagonalQuoteCode`; its public signature
contains only `p`, the ordinary vanishing-width data, and the bounds on `p`.

### F4 — HIGH / weakened theorem: Closure Under Conditioning does not reach `thm:scon`

The capped conditional-price definition and the gated-trader economics are substantive.
The missing edge is the passage from a consistent fixed/growing condition to a concrete
conditioning compiler for the original market.

`gatedConditioningOperationalWitness`
(`Construction/Witnesses/ConditioningCompiler.lean:2658–2665`) requires a uniform floor

```lean
∀ d, ε ≤ P d (C.condition d)
```

for every day. The paper obtains eventual positivity from consistency/non-dogmatism and
repairs the finite prefix. Lean constructs `denominatorPatchedGatedConditioningOperationalWitness`,
but its docstring explicitly says transport back to the original history remains behind the
qualified finite-perturbation theorem (`ConditioningCompiler.lean:2671–2685`).

`lic_conditioned_gated_ofComputationsAndMarket` still assumes the all-days floor
(`ConditioningCompiler.lean:2702–2713`). `lic_conditioned_unconditional`
(`Construction/Witnesses/UnconditionalOverLIA.lean:71–80`) still takes the entire
`ConditioningPresentation` and `ConditioningTraderCompiler` as caller inputs.

**Consequence.** The paper theorem for arbitrary fixed consistent conditions and arbitrary
efficiently computable growing condition sequences is not obtained.

**Required repair.** Complete finite-prefix transport for the conditioned construction or
prove a direct prefix-insensitive compiler theorem adequate for this use. Then expose fixed
and growing-condition corollaries with only the paper's consistency/computability premises.

### F7 — MEDIUM / abstraction boundary: Lean LUVs do not encode unique definability

The paper's `def:luv` is a formula that the theory proves defines a unique `[0,1]` value
(`main.tex:1635–1661`). Lean's core type is only

```lean
structure LUV where
  gt : ℚ → Sentence
```

(`Framework/Expectations.lean:59–66`). Unique existence, `[0,1]`-valuedness, and agreement of
thresholds with a world value are supplied through `ValuesAt`, `WorldValued`,
`ExactTheoryPresentation`, `ConvergencePresentation`, or theorem-local hypotheses.

`LUV.expect_converges`, for example, assumes that every finite-stage plausible world assigns
the LUV some coherent value (`Properties/ExpectationConvergence.lean:990–996`).

In addition:

- `lic_linearity_of_expectation` is a fixed `a,b,X,Y,Z` theorem, while the paper states a
  varying efficiently generated sequence result; and
- `lic_expectation_provind` treats one LUV lower bound, while the paper's theorem is for an
  arbitrary bounded LUV-combination sequence with all three comparison forms.

Closer sequence-level capstones exist in `ExpectationProperties.lean`, but carry the
presentation/compiler interfaces above and are not all in the main endpoint audit.

**Full repair scope.** Fixing this rather than merely disclosing the abstraction would require
all of the following:

1. Define a first-order arithmetic LUV as a one-free-variable formula together with proofs
   that the background theory proves unique existence and that the unique value lies in
   `[0,1]`.
2. Construct the rational threshold sentences used by the market from that formula, and
   prove that their truth in standard and completed-theory worlds agrees with comparison
   against the uniquely defined value. This includes the paper's treatment of worlds whose
   encoded model may be nonstandard.
3. Derive the current `ValuesAt`, `WorldValued`, `ExactTheoryPresentation`, and
   `ConvergencePresentation` interfaces from this certified syntax, rather than accepting
   them as independent caller hypotheses. The derivation must also provide the uniform
   polynomial threshold-code generators consumed by the trader compilers.
4. Refactor the LUV-combination and expectation development to consume the certified object
   directly, or give a verified erasure from a paper-faithful first-order LUV into the
   current propositional threshold interface.
5. Finish the paper-strength sequence endpoints on top of that bridge: linearity for
   efficiently generated varying LUV sequences, and expectation provability induction for
   arbitrary bounded LUV-combination sequences in each of the paper's three comparison
   forms. Add those endpoints and their constructed-LIA instantiations to `AxiomAudit.lean`.

**Disposition.** This can remain an explicit propositional abstraction, but public claims
must say that `def:luv` and the expectation tail are formalized relative to threshold and
world-value presentation interfaces, not that the paper's first-order LUV definition itself
has been reconstructed.

### F8 — MEDIUM / weakened public conclusion: `thm:li` omits finite support

The paper's main theorem concludes existence of a **computable belief sequence**, whose daily
belief states have finite support (`main.tex:926–929`; definitions at `670–719`).

The Lean construction internally has the stronger data:

- `liaStates DP n : RationalBeliefState` (`Construction/LIA.lean:15–20`);
- rational `[0,1]` entries with finite support (`Construction/MarketMaker.lean:537–565`);
  and
- an exact computable quote table.

But `exists_logical_inductor` concludes only

```lean
∃ P : History, IsLogicalInductor P DP
```

(`Construction/LIACompiler.lean:6745–6750`).

**Required repair.** Define/package a computable belief sequence and state the main theorem
with finite support, range, exact rational computation, and the LIC. The existing `liaStates`
should make this mainly a statement/packaging task.

### F9 — MEDIUM / audit-process defect: `AxiomAudit.lean` is not the full public surface

README says `AxiomAudit.lean` enumerates every public endpoint. Its Tier-1 list omits several
declarations identified elsewhere as paper-facing, including:

- `PolySequence.affcoh`, `affpolymax`, and `peraffkno`;
- the theory-valued affine provability wrappers;
- `BoundedSequence.expcoh`, `exppolymax`, and `perexpkno`;
- `BoundedSequence.wubexp`; and
- newer `_unconditional` endpoints in `Construction/Witnesses/ComputationDP.lean` and
  `UnconditionalOverLIA.lean`, including paradox resistance and conditioning.

The F2 repair added the recurring-unbiasedness, calibration, affine pseudorandomness,
expectation recurring-unbiasedness, and expectation pseudorandomness endpoints to the
inventory, but the unrelated omissions above remain.

The paper-node checker establishes that annotations on inventory members cite real labels;
it does not prove that all paper-facing declarations are inventory members, nor that every
paper theorem has a full-strength endpoint.

`#assert_fields` usefully freezes selected structure field sets, but it cannot detect a
missing semantic relation between existing fields. F3 required separate theorem-level
inventory checks for precisely that reason.

**Required repair.** Generate the Tier-1 seed mechanically from all declarations carrying a
`Paper node:` annotation (with a small explicit exclusion list for internal lemmas), add the
omitted capstones, and add a coverage check from paper theorem labels to reviewed endpoint
statements. Axiom cleanliness and statement faithfulness should be recorded separately.

### F10 — MEDIUM / disclosed modeling substitution: efficiency is repository-relative

The paper uses ordinary polynomial-time generation in unary `n`. The repository uses
`Nat.Partrec.Code` under explicit polynomial fuel, with token-indexed length and element
programs (`EfficientlyComputableTok`, `Criterion.lean:1392–1446`). This fixes a real defect in
the earlier whole-number serializer and supports deep polynomial-size strategies.

However, no equivalence theorem relates this class to a conventional Turing-machine or RAM
polynomial-time class. The model also retains a per-token value restriction, particularly on
varying sentence codes. README discloses this at `README.md:29–33`.

**Consequence.** The construction and all efficiency-sensitive properties are correct
relative to the token/fuel model. Claims of literal faithfulness to the paper's complexity
class remain unproved.

## Retired finding: the old quotation-presentation vacuity is fixed

The previous version of this audit reported that a free-schema
`QuotationTheoryPresentation` forced both a sentence and its negation into the deductive
process by choosing identical positive and negative schemas.

That finding is **obsolete in the current tree**. Quotation now uses fixed complementary
universal schemas indexed by a code. `Construction/Witnesses/ComputationDP.lean` constructs
`quotationPresentation`, and `quotation_presentation_nonvacuous` (`:536–541`) proves the
existence of a deductive process, a quotation presentation, and a plausible world at every
finite stage.

This repairs the old mode-1 vacuity. The distinct diagonal-link problem recorded in F3 is now
also repaired by the market-derived fixed program and its FFL representation.

## Coverage assessment by paper section

| Paper area | Current assessment |
|---|---|
| Markets, worlds, traders, exploitation | Substantial and mostly faithful; market range is missing from the LIC bundle |
| Efficient computability | Coherent repository model, but only a disclosed substitution for paper polynomial time |
| LIA construction and `thm:lia` | Strong, non-vacuous, kernel-clean relative to the repository criterion |
| Main existence `thm:li` | Constructed object has finite support, but public conclusion omits it |
| Convergence | Genuine trader proof, conditional on separately supplied market bounds and plausible worlds |
| Limit Coherence | Only component identities; no probability measure theorem |
| Provability induction and timely learning | Strongest wrappers use eventual completed-theory proof appearance and are close to the paper |
| Affine coherence/persistence | Substantial, but several paper-facing capstones are outside `AxiomAudit` |
| Calibration and recurring unbiasedness | Historical maturity is compiled and dovetailed; paper-facing endpoints construct it internally |
| Feedback unbiasedness (`wub`) | Significant compiler construction; unconditional-over-LIA variants still take the paper's semantic/operational data |
| Pseudorandom learning | Affine, sentence, expectation, and fixed-frequency endpoints construct historical maturity internally |
| Logical relationships | Substantial propositional rendering |
| Non-dogmatism / uniform non-dogmatism | Substantial; relies on explicit global theory/world and range hypotheses |
| Conditioning | Compiler and economics present; full fixed/growing closure theorem not reached |
| Expectations | Threshold-interface abstraction; basic convergence is genuine, later theorems retain semantic/compiler presentations |
| Consistency and halting | Generic represented-claim interfaces are sound; concrete end-to-end instantiation uses stronger arithmetic assumptions such as Σ₁ soundness |
| Introspection and self-trust | Many affine consumers and quotation paths are real, but representation/reflection data remain explicit inputs |
| Paradox resistance | Public diagonal program, quoted atom, and FFL fixed point are constructed from the computable market; no semantic self-reference premise remains |

## Positive verification

### Central construction

`LIA_is_logical_inductor` and `exists_logical_inductor`
(`Construction/LIACompiler.lean:6735–6750`) reduce to the actual recursive quote compiler and
the semantic theorem `lia_no_efficient_trader_exploits`. The latter uses
`trading_firm_dominance`, identifies the adaptive firm with the realized LIA trader, and
contradicts `marketMaker_not_exploited` (`Construction/LIA.lean:95–124`). No exploitation
conclusion is assumed through an operational witness.

### Exploitation and worlds

`Trader.Exploits` is `BddBelow ∧ ¬ BddAbove` over all finite-stage plausible assessments
(`Framework/Criterion.lean:1341–1351`), matching the paper's bounded-downside/unbounded-upside
criterion. `PCWorld` is a Boolean valuation over the countable atom language, so Boolean
consistency is built into the world object rather than assumed.

### Constructed market quality

Although the criterion omits the range law, `liaHistory_range` proves the constructed LIA's
prices lie in `[0,1]` (`Construction/LIA.lean:87–89`). `RationalBeliefState` provides finite
support and rational values, so the actual construction is closer to the paper than the
headline type indicates.

### Non-vacuity and trust

The current quotation presentation is inhabited together with finite-stage plausible worlds.
The construction and the checked property endpoints report only Lean/Mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound`; there is no project-specific axiom in the
Logical Induction development.

### Disclosures that are accurate

README accurately discloses:

- the token/fuel efficiency model;
- that the property tail is conditional; and
- that the autoformalized Brouwer interior has not received a human line-by-line review.

## Mechanical checks run

The following checks were rerun during this audit:

```text
lake build
scripts/check-paper-nodes.sh
python3 scripts/lint_paper_labels.py
rg scan for executable sorry/admit and axiom declarations
git status --short
```

Results:

- full build passed: **2786 jobs**;
- paper-node validation passed: **60 distinct referenced labels**;
- theorem-label lint passed;
- no executable `sorry`, `admit`, or `axiom` declaration was found in `LogicalInduction/`;
- checked axiom reports contained only `propext`, `Classical.choice`, and `Quot.sound`; and
- the worktree was clean before this report replaced its predecessor.

These checks establish kernel cleanliness and annotation consistency. They do not discharge
the statement-faithfulness findings above.

## Recommended order of repair

1. Close the finite-prefix transport needed by Conditioning.
2. Package `thm:li` as existence of a computable finite-support belief sequence.
3. Expand the endpoint inventory and distinguish “complete,” “conditional,” “qualified,” and
   “interface only” coverage per paper node.
4. Only after those repairs, revisit the three deliberately disclosed classical-computability
   boundaries and the token/fuel equivalence question.

Until at least items 1–3 are addressed, the repository should continue to describe the
Logical Induction development as **in progress**, with unconditional central construction and
a conditional/qualified property tail.
