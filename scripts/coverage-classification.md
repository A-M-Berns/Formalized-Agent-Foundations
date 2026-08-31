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
  representation obligations discharged. Stage joint consistency is a premise the paper
  itself takes, and so are the theory premises: the arithmetic-theory family is stated over
  `(T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`, plus
  `[RepresentsComputations T]` on the bounded computational-knowledge lane and `[𝗜𝚺₁ ⪯ T]`
  on the three endpoints that spend it. Consistency and representability are the paper's
  own premises (tex:600-606, tex:993-997); `[T.Δ₁]` and the diagonal's `[𝗜𝚺₁ ⪯ T]` are
  representation infrastructure, charged once globally under *Global model disclosure*
  below; `[𝗣𝗔⁻ ⪯ T]` is a genuine small strengthening, charged globally by ruling
  (2026-08-31) and discussed only there. Read the status column, not the axis,
  for whether a given row is charged for a residual.
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
* **`dd:fuel` on the property tail's own *token-metered* data sequences**
  (`RpnSentenceCodes φ`, `LUV.RpnThresholdCodes(Seq) X`,
  `AffineCombination.PolySequence As`,
  `PGenerableWeighting W`, `GeneratedRatFeature P q ξ`, …) is a **representation
  interface**: it restricts who can supply the input, not what is proved. It is the paper's
  own e.c. requirement, is charged once at `def:ec`, and does **not** lower a row
  downstream. `RpnThresholdCodes(Seq)` belongs here, and an earlier edition of this file
  moved it out on the mistaken ground that it excluded `def:luv`-admissible data; that
  charge is withdrawn — see *LUV-threshold metering: rendering sensitivity, witnessed*
  below, which also records how formula families are metered: on the paper's own **source**
  language (`ArithSource`, `PolyArithmeticSourceSeq`), one token per node as the paper
  writes it, with the normal-form-metered `PolyArithmeticFormulaSeq` retained only as a
  strictness foil. `dd:nnf` names that two-layer architecture and is **not** a charge
  against any row. Two of those — `PGenerableWeighting` and `GeneratedRatFeature` — are stronger
  than token-metered: their emission field is the *write-out* class `BigSpliceStream`, so a
  single feature token may be exponential in the day. `GeneratedRatFeature.polyTok` was
  `RpnSpliceStream` until the write-out migration, which made this bullet's claim about it
  true rather than aspirational: a constant leaf `EF.const (q n)` carries `⌜q n⌝` as one
  token, so under the old field the paper's own `δ n = 2⁻ⁿ` was **not** admissible data
  (`digitRatCodes_two_pow_inv_not_polyRatCodes`), and now is
  (`PGenerableRat.ofDigitRatCodes`, `pGenerableRat_two_pow_inv`); the emission classes themselves are separated at that family by `bigSpliceStream_two_pow_inv_not_rpnSpliceStream`. Stage joint consistency (`∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)`) is
  likewise the paper's own.
* **`dd:symbolcount` on §4.10's finite proof search** is a stated **counting convention**, not a
  substitution, and is recorded here rather than charged against any row. `Con(Θ′)(ν)` is now read
  as the paper writes it — “no `Θ′`-derivation of `⊥` has `ν` **or fewer symbols**”, the bound
  **inclusive**. Foundation exposes no size function on its internal derivations, so
  `Framework/DerivationSize.lean` builds one: `dSize`, by external recursion over the derivation
  codes at `V := ℕ`, tied to Foundation's own derivation constructors by equation (`dSize_axL`,
  `dSize_cutRule`, …), with the load-bearing converse bound `le_G_dSize : d ≤ G (dSize d)` —
  unconditional, no well-formedness hypothesis — which is what keeps a symbol-bounded search
  finite, and so decidable in both polarities. The Gödel-number metering that used to stand here,
  disclosed as the type-`(c)` substitution `dd:proofcode`, **was retired in tranche 9a** and is
  gone from the development; the endpoints' statements are unchanged. What remains is unavoidable
  rather than substitutive: the paper fixes neither a Gödel encoding nor an alphabet (“written in
  `ℒ` using a Gödel encoding”), so some counting convention must be chosen. Ours charges one
  symbol per rule name, connective, quantifier, predicate symbol, function symbol and variable
  occurrence, one separator per argument-list entry, and — at its binary digit length **plus one marker token** (`idxLen n = Nat.size n + 1`, the marker separating an index numeral from the following material) — every
  variable, function and relation index. The index clause is forced, not cosmetic: charging a
  variable occurrence one symbol regardless of its index would make the measure
  **infinite-fibred** — unboundedly many derivations of symbol count `1` — and the bounded search
  undecidable in the negative polarity. It is the same write-out metering the rest of this
  development uses for `def:ec`. The residual error only ever *over*-counts, so `conWithin T k` is
  if anything a **weaker** claim than under a leaner convention, never a stronger one; and the
  truth of every instance is proved from consistency alone (`conWithin_of_consistent`),
  independently of the convention. `thm:pac` and `thm:pazfc` read `exact` with nothing charged
  against them here. It does **not** reach `thm:incons`, whose sentence is the *unbounded*
  existential over proofs: nothing is metered there, so no counting convention arises.
* **`dd:machinetheory` on `thm:incons`'s theory sequence** is a stated **presentation convention**, not a
  substitution, and is recorded here rather than charged against the row — the same status
  `dd:symbolcount` has. The paper says only that the day's theory is recursively axiomatizable and
  efficiently named; reading a machine *as* a theory requires fixing a convention, and ours is: the
  machine's outputs are `ArithSource.sourceNat` names of axiom *sources* (`theoryOf`,
  `Construction/Witnesses/ComputationRepresented.lean`), an output contributing the sentence its named
  source writes and **anything else contributing nothing**, and the budget-`b` window at inputs `is` is
  `is.map (fun i => gateName ((evaln b m i).getD verumSourceNat))`, a diverging *or inadmissible* output
  contributing the inert `⊤`. **Admission is decided, not assumed** (R11): `AdmissibleName`
  (`Construction/Witnesses/SourceWindow.lean`) admits a number only if it is literally the name of its own
  decoded run *and* that run is the complete emitted run of one `ArithSource 0` whose compiled form is a
  sentence, the second test run by the recognizer `sourceRun`
  (`Construction/Witnesses/SourceRecognizer.lean`), which tracks binder depth and rejects the
  free-variable tag. The gate is load-bearing rather than hygiene: ungated, the represented predicate held
  of machines presenting the **empty** theory; gated, `machineTheoryInconsistent_iff` proves
  `MachineTheoryInconsistent m.sourceNat ↔ ¬Entailment.Consistent (theoryOf m)`. The convention's
  **surjectivity** justification is *scoped*: what is proved is the per-sentence half,
  `theoryOf_const_ofNNF` (`theoryOf (Code.const ⌜written σ⌝) = {σ}` — every one-axiom theory presented
  exactly, `ArithSource.ofNNF` writing every sentence); the *uniform* half — one machine enumerating the
  names of any given r.e. set of sentences — is **not formalized**, would need
  `encodeArithmeticFormulaSymbols` certified primitive recursive, and is not consumed by the endpoint,
  whose `hinc` is stated at the caller's own machine. Any other convention gives a coextensive class
  of theories but a different represented predicate, hence a different schema — which is exactly why it is
  stated rather than left implicit. Defined in the glossary at `LogicalInduction.lean`.
* The **arithmetic-theory instance binders** divide the same way, and the division is
  settled by ruling (2026-08-30) rather than re-argued per row. `[Entailment.Consistent T]`
  and `[RepresentsComputations T]` are **the paper's own premises** — tex:600-606's "Θ
  represents computations", imposed for §4.8–§4.12 at tex:993-997, which the paper notes
  already forces Θ consistent. `[𝗣𝗔⁻ ⪯ T]` is a **genuine, small strengthening** — *not*
  implied by representability, and an earlier edition of this file said it was; see the
  disclosure below. `[T.Δ₁]` and the diagonal's `[𝗜𝚺₁ ⪯ T]` are **representation
  infrastructure**, charged here once and never against a row — see *Arithmetic-theory
  hypotheses* below for all three. Σ₁-soundness — `[T.SoundOnHierarchy 𝚺 1]`,
  which the paper explicitly declines to assume (tex:2673) — is **gone**: 0 of the 105
  canonical endpoints carry it.

**The once-globally rule covers the token-metered classes only.** The distinction is at
the *definition*, not the name, and it is one conjunct of `PolyFueled`:

```
PolyFueled c f  :=  ∃ b, Fueled c f b ∧ IsPolyBounded f ∧ IsPolyBounded b
```

`IsPolyBounded f` bounds the **output value** `f n ≤ a·(n+1)^k + a`, over and above the fuel
bound `IsPolyBounded b`. So there are two different things a hypothesis built from
`PolyFueled` can be doing, and only reading the definition tells them apart:

* **token-metered** (called *symbol-metered* in earlier revisions of this development, before
  §4.10 introduced a genuine derivation-symbol count) — `RpnSentenceCodes`,
  `RpnThresholdCodes(Seq)`, `RpnSpliceStream`,
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
  (`DUSApproximationPresentation.approximation_codes`, `DUSThresholdEmission`,
  `PrefixMachinePresentation`, `PatientSettlementClock`). Three structures earlier editions
  listed here have since left the class and are **not** whole-value any more:
  `IntrospectionIntervalQuote` (its `inverse_width_codes` is `DigitRatCodes`),
  `SelfTrustQuote` (`product_codes`/`confidence_codes` widened to
  `LUV.BigThresholdCodeSeq` when `thm:st` moved to the write-out class), and
  `ParadoxResistanceQuote`, which carries no code field on its width at all — only
  `sentence_codes : BigSentenceCodes`. Here `PolyFueled` is applied directly to
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
   costs nothing. `thm:lp` used to be the standing example of clause (3), and the final
   fix-wave **executed** the argument instead of making it: the four `width` binders are
   gone from `lic_paradox_resistance_ofDiagonal_unconditional` and the tolerance is
   discharged internally at `2⁻ⁿ`. The clause is kept because the reasoning is still the
   right test; it now has no live instance on the paper-facing surface.

This is easy to miss twice over. The token-metered and whole-value sentence classes are one
coercion apart (`RpnSentenceCodes.ofPolySentenceCodes`), so a narrowed endpoint opens by
applying it; and several whole-value hypotheses are **not visible in the elaborated
signature at all**, because they are fields of a structure the signature names
(the presentation objects above; `IntrospectionIntervalQuote` was the original example and
has since been migrated off the class). Read the structure, not
the binder list — that is how the `input_poly` fields of the
since-retired `BoundedComputation` and `SemidecidableComputation` structures went unnoticed
for as long as they did. **No such
hypothesis is left on a datum the paper quantifies over as e.c.** Every one has been
migrated to a write-out class: `⟨δ⟩` and `⟨p⟩` to `DigitRatCodes`, `⟨φ⟩` to
`BigSentenceCodes`, `⟨m⟩` to `DigitMachineCodes`, `⟨x⟩`/`⟨y⟩` — including the `input_poly`
fields of the two structures since retired — to `BigDigits`, and `thm:incons`'s theory sequence `⟨Θ′⟩`
twice: in tranche 9-pre from a Gödel-code digit count to `PolyArithmeticSourceSeq` on the **written
source** of the day's adjoined axiom, and in tranche 10 again — the day's theory is no longer named by one
adjoined axiom at all, so the premise moved to `DigitMachineCodes` on the **machine's** own written source,
which is what tex:1931 meters. That was the last hypothesis on paper-quantified data still metered by a
Gödel code rather than by a write-out. What remains in the list above is repo-side
presentation objects and facts the repo proves about objects it constructs, neither of
which is a class restriction on the paper's own data.

## The single market (settled 2026-08-31, round 13)

The paper prices every §4 property in **one** market `𝕡`, built once over one deductive
process. Since round 13 that is literally what this formalization does. Of the canonical
endpoints whose statements name a market, **18** read `liaHistory (paperDP T)`, where
`paperDP T := (theoremDP T).union (paperTheoryDP T)` — Θ's own theorem stream in union with
the literal provability/quotation stream the constructed quote codes are read off. There is
one further market-bearing endpoint, and it is the ruled exception below.

**This supersedes a split this ledger used to disclose.** Earlier editions described two
market lanes: the quotation family (`thm:ref`, `thm:lp`, `thm:st`, `thm:epr`, `thm:er`,
`thm:cee`, `thm:ceu`) priced at `liaHistory (theoremDP T)`, and the computational-knowledge
family (`thm:halts`, `thm:loops`, `thm:dontwait`, `thm:pac`, `thm:pazfc`, `thm:incons`) at
`liaHistory (paperTheoryDP T)`. Both descriptions are retired; every row below that named
one of those two processes as *its* market now names `paperDP`. The round-6 consolidation
question — whether the two lanes could be collapsed onto the paper's single `𝕡` — is
therefore **resolved by construction rather than by argument, and closed**. The union
process already existed, unused, under the name `theoremPaperDP`; it was collapsed into the
load-bearing name `paperDP` rather than layered beside it, so no suffixed or parallel market
survives.

**Nothing was bought with a hypothesis, and that is the substantive check.** The binder
census over the 105 canonical endpoints is *identical* before and after the unification —
`𝗣𝗔⁻ ⪯ ·` 16, `𝗜𝚺₁ ⪯ ·` 3, `[T.Δ₁]` 23, `[Entailment.Consistent ·]` 15,
`[RepresentsComputations ·]` 3, `[T.SoundOnHierarchy 𝚺 1]` 0 — because the union's
stage-world witness (`paperDP_nonvacuous`, `paperDP_hworld`) is discharged from exactly the
instances the two component witnesses were. No endpoint paid for its new market. Every
hypothesis-position occurrence of a component process moved in lockstep with the conclusion.

**One ruled exception, and it is the only one.** `thm:ccee`'s
`lic_no_expected_net_update_conditional_exact_canonical` stays at
`liaHistory (canonicalCCEEDP T)`, whose fixed enlarged language is what makes exact semantic
multiplication available; that lane was out of scope for the unification by ruling, and its
row says so. It is the one canonical endpoint priced outside `paperDP`. (Its `source_valued`
premise still mentions `theoremDP`, an asymmetry with its `canonicalCCEEDP` conclusion that
predates round 13 and is the only surviving canonical occurrence of that name.)

`theoremDP` and `paperTheoryDP` themselves survive, but only as **construction ingredients**
of `paperDP` and as the CCEE lane's base — no canonical endpoint is stated at either, and
neither is a parallel endpoint lane. Two further appearances of `paperTheoryDP` in this file
are correct as they stand and are *not* market claims: `PaperLUV.source_valued`'s
completed-world premise `v.ConsistentWithTheory (paperTheoryDP T)` and the `def:luv`
frontend lemmas built on it quantify over completed worlds of Θ's theorem stream, not over a
market's prices.

**The provability world's tag spaces were renumbered in the same round** (T8/8), and this
matters for reading older text here. The two dead atoms — the `inconsistency` and
`consistency` computation claims, which no endpoint consumed — were deleted, along with the
two `ComputationTheoryPresentation` obligations that discharged them, so that structure now
has **six** fields and states a strictly *weaker* interface: every endpoint consuming it is
thereby strengthened, never weakened. The `theoremDP` **event** tag space is now gapless
`0`–`5` (halting ±, bounded halting ±, quotation ±), and the **global atom-payload** space is
gapless `0`–`6` with the finite-perturbation counterexample's advice tags at `7`/`8`, strictly
above it rather than colliding with it, so that layer's disjointness argument is numeric
rather than incidental. Where earlier editions of this file said "tag 7" for the
quotation-negation fiber, today's number is **5**.

## LUV-threshold metering: rendering sensitivity, witnessed

`LUV.RpnThresholdCodes(Seq)` is `RpnSentenceCodes` on the threshold family `⌜Xₙ > i/k⌝`, a
`PolySegStream`. An earlier edition of this file held that this costs the paper a
restriction on its own `def:luv` data, on the ground that the only route in —
`PaperLUVSeq.structural : PolyArithmeticFormulaSeq` — meters Foundation's numerals in unary
and so excludes the paper-natural `X > 2⁻ⁿ`. **That reasoning was wrong**, and the error is
recorded here rather than quietly repaired.

* **What is metered is the formula string**, one token per `ℒₒᵣ` node. Along this route
  every emitted token is a fixed small constant — the payload alphabet is `0..18`
  (`encodeArithmeticFormulaSymbols_lt`) and the framing adds `0`/`1`/`19`
  (`structuredPaperPrimeBlock_span`) — so `PolySegStream`'s per-token *value* clause is
  vacuous here and the class is exactly *polynomial length*, i.e. write-out. Gödel codes are
  never emitted and no numeral is expanded beyond what the author wrote.
* **On the paper's connectives, and on numerals, this is the paper's own condition.**
  `def:ec` (tex:753) asks for a polynomial-time writer of the object. For `¬`, `∧`, `∨`, `⟹`,
  `∀` and `∃` the count here is one token per node, which is the paper's own symbol count. On
  numerals the paper fixes **no** notation — it writes them positionally (tex:614, tex:757) —
  so nothing follows from Foundation's numerals about what the paper's `ℒₒᵣ` excludes. The
  unary cost of `Semiterm.Operator.numeral` is an artifact of Foundation's *default* numeral,
  and the value is nameable compactly inside `ℒₒᵣ` (next bullet), so the class is not narrowed
  on numerals; `unaryRendering_two_pow_not_polyArithmeticFormulaSeq` documents that artifact.
  An earlier edition of this file argued instead that "the paper's `ℒₒᵣ` has unary numerals
  too, so a formula literally containing `2ⁿ` successor symbols is excluded there as well".
  That claim is unsupported by the paper and is **withdrawn**; the paper names large values by
  compact terms or by definitions (tex:614 — writing `⌜f(3) > 4⌝` "does not involve computing
  the value `f(3)`"), and never fixes a numeral notation at all.
* **The compact naming is available inside `ℒₒᵣ`.** `binNumeral v` is the Horner term for
  `v` in `O(log v)` nodes (`binNumeralEnc_length_le : (binNumeralEnc v).length ≤
  6 * Nat.log 2 v + 1`) with value `v` in every model of `𝗣𝗔⁻` (`binNumeral_val`).
* **The class demonstrably reaches the value in question.** `dyadicPaperLUVSeq T` is the
  family of literal paper LUVs of value **`2⁻ⁿ`** — the value the paper writes as
  `X > 2⁻ⁿ` — with denominator named by `binNumeral (2 ^ n)` in `O(n)` symbols
  (`dyadic_polyArithmeticFormulaSeq`); `dyadicPaperLUVSeq_frontend` gives it both frontend
  conclusions (world-valued on the completed worlds of `paperTheoryDP T`, and
  `LUV.RpnThresholdCodeSeq`). It sits beside `unitFracPaperLUVSeq` at `1/(n+1)`; the two
  share one template (`invFormula` / `invPaperLUV`) and differ only in how the denominator
  is named.

On numerals, then, what remains is **an artifact, not a class restriction**:
`unaryRendering_two_pow_not_polyArithmeticFormulaSeq` proves that the *same* value spelled
with Foundation's unary numeral has no certificate, while the compact `ℒₒᵣ` name of the same
value does. It is disclosed, not charged, and **no row is lowered by it**; the per-row charge
the previous edition introduced is withdrawn at all nine rows that carried it (`thm:ec`,
`thm:ei`, `thm:expcoh`, `thm:exppolymax`, `thm:perexpkno`, `thm:er`, `thm:cee`, `thm:ccee`,
`thm:st`) and at the two disclosure rows `def:luv` and `def:blcp`.

### The metering is on the paper's source language

`def:ec` (tex:753) asks for a polynomial-time *writer* of the object, over a language whose
primitive connectives are `¬`, `∧`, `∨`, `⟹`, `⟺`, `∀`, `∃` (tex:560: the language
"includes the basic logical connectives ¬, ∧, ∨, ⟹, ⟺"). Foundation's `Semiformula` is a
**negation-normal-form** datatype — constructors `verum/falsum/rel/nrel/and/or/all/exs` —
with no biconditional constructor, so metering the *normal form* would charge
`3 + 2|a| + 2|b|` symbols for `a ⟺ b` (`encodeArithmeticFormulaSymbols_iff`): both sides
duplicated, a factor of two per nesting level. That is not what is metered.

Formula families are metered on a **source** language. `ArithSource k`
(`LogicalInduction/Construction/Witnesses/ArithmeticSource.lean`) has the paper's own
primitive connectives plus atomic leaves; `ArithSource.compile` gives it its meaning as an
`ArithmeticSemiformula ℕ k`, with `eval_compile` the semantic bridge (the `iff` case is a
metalevel `↔`, not a pair of implications); and the `def:ec` condition is
`PolyArithmeticSourceSeq s := PolySegStream (sourceTokens ∘ s)` — **one emitted token per
node of the formula as the paper writes it**. Normal-form expansion happens inside
`parseStructuredArithmeticFormula` (source tags `20` = `¬`, `21` = `⟹`, `22` = `⟺`) and is
never charged to the emitter. `PaperLUVSeq` carries the source (`source`), a proof that it
denotes the LUV's defining formula (`compiles`), and the `def:ec` certificate on the
source (`structural`).

The normal-form-metered class `PolyArithmeticFormulaSeq` is retained, not deleted, and its
role is now a **strictness foil**: it embeds (`PolyArithmeticFormulaSeq.toSource`), and the
inclusion is *strict*. The witness is the left-nested chain `Φ₀ := A`, `Φₖ₊₁ := Φₖ ⟺ A`,
which is linear for the paper's writer and exponential in the normal form:

* in the paper's class, certified at `5n + 4` emitted tokens —
  `iffChainSource_polyArithmeticSourceSeq`, `sourceTokens_iffChainSource_length`;
* in the foil, refuted — `iffChain_not_polyArithmeticFormulaSeq`, on
  `two_pow_le_encode_iffChain` (`≥ 2ⁿ` nodes) and `encodeArithmeticFormulaSymbols_iff`.

So `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq` is **proved, not asserted**, and the
same family is carried all the way to a literal paper LUV family: `iffPaperLUVSeq` is a
`PaperLUVSeq` whose `n`-th defining formula is `O(n)` characters to write and whose
Foundation normal form has `≥ 2ⁿ` nodes, with `iffPaperLUVSeq_frontend` giving both frontend
conclusions (world-valued over `paperTheoryDP T`, and `LUV.RpnThresholdCodeSeq`).

`dd:nnf` therefore no longer names a substitution charged against `def:ec`. It names the
two-layer architecture — paper source above, Foundation NNF below, compiled between — and
the fact that the foil class is kept as the strictness witness. Nothing pays twice for a
`⟺`, and the earlier per-node disclosure that this section carried ("the token-metered
class is strictly finer than `def:ec`, on `⟺` and only on `⟺`") is **withdrawn**: it was
accurate about the foil and is not accurate about the class the statements now use.

A binary-numeral *source* node — a class that names numerals in binary at the encoder
rather than in the object language — was considered and **rejected**, and that rejection
stands. It would admit formula strings the paper's own `def:ec` writer cannot produce in
polynomial time, so it is a permissive widening past `def:ec`, not a faithful repair. The
faithful move on numerals is the one taken: name the value compactly *in `ℒₒᵣ`*. The
objection never transferred to the connective source language above, because `⟺` **is** one
of the paper's own primitives, so restoring it costs no permissiveness.

The one boundary that remains here is the **pre-existing `dd:fuel` charge**, and it is not
re-levied by this section: `PolySegStream` is a fuel-clocked emitter certificate rather than
a `Complexity.FP` witness. That substitution is disclosed once at `def:ec`, above.

## Arithmetic-theory hypotheses (applies to the arithmetic-theory family)

The arithmetic-theory family is **not** stated at one uniform instance set, and this
section used to say it was ("every theorem that quantifies over an arithmetic theory is
stated over `[T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`"). There are three layers, with
different binders:

* the **universal** layer of the §4 tail (`[IsLogicalInductor P DP]` /
  `[IsMachineLogicalInductor P DP]`) names no theory at all and is instance-free;
* the **syntax / representation** layer over a theory — the arithmetic-syntax lemmas of
  `Construction/Witnesses/ComputationSyntax.lean` and the `_ofRepresentation` / `_ofCode`
  statements built on them (the §4.10 `_ofComputation` lane, over `BoundedComputation` /
  `SemidecidableComputation`, was retired in tranche 8) — is stated over
  `(T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T]`, with **no** soundness instance;
* the **closed / `_unconditional`** layer over the constructed `LIA` is stated over
  `(T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`, with three
  variations, all verified against the elaborated signatures rather than the sources: the
  bounded computational-knowledge lane (`thm:dontwait`, `thm:pac`, `thm:pazfc`) takes
  `[RepresentsComputations T]` *in place of* the consistency binder, that class supplying
  consistency itself; `thm:incons` adds **no theory hypothesis at all** beyond the market's — its
  day-`n` theory arrives as a machine code and carries no `Δ₁` instance of its own, the second theory `T'`
  and its `[T'.Δ₁]` having gone with the deduction family in tranche 10 (its redundant `[𝗥₀ ⪯ T]` was
  dropped in T8/iii); `thm:lp` adds `[𝗜𝚺₁ ⪯ T]`, one of the
  three endpoints that carry it (census below). `thm:scon`'s two closed endpoints are
  lighter still, at `[T.Δ₁]` alone.

Which of those binders is charged against a row, and which is infrastructure disclosed
once, is settled by ruling (2026-08-30) and stated once here.

### The paper's own premises: consistency and representability

`[Entailment.Consistent T]` and `[RepresentsComputations T]` are the paper's standing
assumption on Θ, not a strengthening of it. tex:600-606 asks that Θ *represent
computations* — that for every total computable `f : ℕ → ℕ` there be a two-variable
Θ-formula `γ_f` with

    y = f n  ↔  Θ ⊢ ∀ν (γ_f(n̄, ν) ⟺ ν = ȳ)

— a condition on what Θ *derives*, with no reference to truth in `ℕ`, which the paper
notes at tex:604 already forces Θ consistent (`RepresentsComputations.consistent`).
tex:993-997 imposes exactly that for §4.8–§4.12. `Framework/RepresentsComputations.lean`
is the Lean rendering of that premise, and it is a **rendering, not a substitution**: it is
non-vacuous (`representsComputations_of_peanoMinus`, with instances registered at `𝗣𝗔⁻`,
`𝗜𝚺₁` and `𝗣𝗔`), it supplies both literals over one sentence (`represents_proves`,
`represents_refutes_all`), and *consuming* it never appeals to truth in `ℕ` even though
*verifying* it at a concrete theory does. Taking consistency as an explicit binder where
the retired soundness instance used to supply it by derivation
(`Basic/Hierarchy.lean:481`) is the paper's own premise made visible, and lowers no row.

One clause of the paper's premise is **weaker than it looks**, and this is where an
earlier edition of this file was wrong. `RepresentsComputations T` also quantifies over
`f : ℕ → ℕ` where the paper writes `ℕ⁺ → ℕ⁺` (tex:600-606) — an at-least-as-strong
hypothesis on Θ, disclosed here and costing no row anything.

### Representation infrastructure, charged once and never per row

**`[T.Δ₁]` — representation infrastructure, charged globally by ruling (2026-08-31).**
Disclosed 2026-08-30 (R5-F15). The endpoints over a theory require a `Δ₁`-definable axiom
set, strictly stronger than the paper's "computably enumerable" as a condition on the
presented `T`. Four facts settle it as infrastructure rather than as a charge against any
row:

* **Craig's trick** supplies a deductively equivalent `Δ₁` (indeed primitive recursive)
  axiomatization of any c.e. theory, and every row is a `T ⊢`-statement, which such a
  re-axiomatization preserves. So the theorems transfer.
* **That transfer is not formalized** here. It is the honest residual, and the reason this
  is a disclosure at all rather than a non-event.
* **The paper never defines "recursively axiomatizable"** and fixes no presentation of Θ
  (tex:600-606); the phrase is used informally throughout §4, so the formalization had to
  choose a presentation condition in order to state anything.
* **The paper's own arithmetized sentences are presentation-relative** in exactly the same
  way — `Con(Θ′)(ν)`, the halting claims and “`⌈Θ′ₙ⌉` is inconsistent” all depend on how
  the axiom set is written down, both for their symbol counts and for their provability.
  Fixing a presentation is a precondition of the paper's §4.10 material, not an extra ask.

What consumes it is the enumeration of `T`'s theorems, never a step of a paper proof.
Charged once, globally; it does not lower a row on its own.

**`[𝗣𝗔⁻ ⪯ T]` — a genuine strengthening, charged globally by ruling (2026-08-31).**
Disclosed 2026-08-30 (blind audit, round 6). The charging question is **settled**: like
`[T.Δ₁]`, this binder is charged once, globally, discussed here and nowhere else, and
levied against no row. Census: **16** of the 105 canonical endpoints (table below). The
full brief, compactly:

* **It is not implied by representability**, and an earlier edition of this file asserted
  that it was. The paper's premise yields `Θ ⊬ n̄ = m̄` for `n ≠ m` but never `Θ ⊢ n̄ ≠ m̄`
  — that is `𝗥₀`'s Ω₃ — and Robinson's **R** is the standing counterexample: it
  represents every computable function while not containing `𝗣𝗔⁻`. Three independent
  blind audits confirmed the gap. So the binder is a finite set of ordered-semiring axioms
  strictly beyond the paper's stated premises.
* **What it buys, (i): compact-`binNumeral` value transfer** (`provable_subst_iff_of_val`).
  `def:ec` forces the compact numeral — Foundation's unary numeral costs its own value in
  symbols, which no write-out certificate can pay — and transferring provability across
  that spelling is Gödel completeness over models of `𝗣𝗔⁻`.
* **What it buys, (ii): object-level fiber exclusivity** (`code_uniq`'s `rfind` case), at
  `theoremDP_hworld`'s tag 5, the quotation-negation fiber (numbered tag 7 until the T8/8
  retirement of 2026-08-31 deleted the two dead inconsistency/consistency atoms and
  renumbered the event space gapless `0`–`5`; earlier editions of this file called it tag
  7). This is the step that let **Σ₁-soundness be deleted from all 105 endpoints** — one
  small *syntactic* assumption traded for zero *semantic* hypotheses, which is the trade
  the ruling endorses. The paper's own exclusivity argument is *metatheoretic*, running
  through the representability biconditional and needing no arithmetic inside Θ at all;
  ours is object-level, so that the stage-world proof stays constructive.
* **The paper's own printed proof tacitly consumes it.** The proof of `thm:incons`
  (app:incons, tex:4487-4491) cites representability (tex:600-604) at exactly the point
  where Σ₁-completeness of Θ is what the step needs — arithmetical strength beyond the
  paper's stated premises, of precisely the kind this binder supplies (`𝗣𝗔⁻ ⪯ T` yields
  `𝗥₀ ⪯ T` and with it Σ₁-completeness). The erratum is recorded in
  `LogicalInduction/notes/paper-errata.md`. So the assumption is not foreign to the
  paper's own reasoning; it is what that reasoning silently uses.
* **Foundation had it at `𝗣𝗔⁻` to begin with.** `code_uniq` was *originally* stated at
  `𝗣𝗔⁻`; the `𝗥₀` text in Foundation is dead code, and reviving the commented-out
  block restores the `𝗣𝗔⁻` statement rather than inventing a new one.
* **Every theory in the paper's intended range satisfies it** — `𝗜𝚺₁`, `𝗣𝗔`,
  `𝗣𝗔 + Con(𝗣𝗔)`, and the arithmetic of ZFC. A reader of the paper who instantiates
  Θ at anything the paper actually discusses pays nothing for it.

No row was promoted or demoted on account of `𝗣𝗔⁻`, and no row re-argues it.

**The diagonal's `[𝗜𝚺₁ ⪯ T]` (ruled 2026-08-30).** `thm:lp`'s
`lic_paradox_resistance_ofDiagonal_unconditional` builds its paradoxical sequence through
Foundation's `parameterized_diagonal₁`, which is stated over `𝗜𝚺₁`. That is where the
Gödel fixed point lives in the substrate, not a theory-strength assumption the statement
needs of its own accord — the same infrastructure charge as `[T.Δ₁]`, and on the same
footing: disclosed here, not levied against the row. It is the *only* arithmetic-strength
binder that endpoint carries: it is declared outside the `𝗣𝗔⁻` section of `ComputationDP.lean`
and recovers that weaker instance inside its proof term from `𝗜𝚺₁ ⪯ T`, so no redundant pair
reaches the signature.
The two literal-`PaperLUV` frontends
`unitFracPaperLUVSeq` and `unitFracPaperLUVBoundedSequence` carry it for a different and
equally infrastructural reason: `threshold_provable_of_neg` / `rationalCutAt` /
`source_valued` prove rational-cut arithmetic *inside* `T`.

**Census, re-derived 2026-08-30.** Measured by elaborating `#check @name` over exactly the
`LI-CANONICAL-BEGIN` … `LI-CANONICAL-END` block and grepping the printed binder lists —
not by reading docstrings:

| binder | occurrences among the 105 canonical endpoints |
|---|---|
| `[T.SoundOnHierarchy 𝚺 1]` | **0** (was 16, then 12, then 0) |
| `𝗜𝚺₁ ⪯ T` (either spelling) | **3** — `unitFracPaperLUVSeq`, `unitFracPaperLUVBoundedSequence`, `lic_paradox_resistance_ofDiagonal_unconditional` |
| `RepresentsComputations T` | **3** — the bounded computational-knowledge lane (`thm:dontwait`, `thm:pac`, `thm:pazfc`) |
| `𝗣𝗔⁻ ⪯ T` | **16** — every closed arithmetic-theory endpoint except the two literal-`PaperLUV` frontends and `thm:lp` (which carry the stronger `𝗜𝚺₁ ⪯ T`) and `thm:scon`'s two, which carry `[T.Δ₁]` alone |
| `𝗥₀ ⪯ T` | **0** — `lic_disbelief_inconsistent_theories_unconditional` carried it redundantly beside the stronger `𝗣𝗔⁻ ⪯ T`; the binder was dropped in T8/iii (R6-F03) and the proof elaborates unchanged, reaching `𝗥₀` through Foundation's `instance [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T` |
| `T.Δ₁` | **23** |

An earlier edition of this file ruled (2026-08-29) that the residual `[𝗜𝚺₁ ⪯ Θ]` was "a
real theory-strength hypothesis beyond the paper's, not a representation choice", and held
`thm:dontwait`, `thm:halts` and `thm:loops` at `qualified` on it alone. **That ruling is
superseded, in two independent ways, and the rows it demoted are promoted.** First, the
premise it rested on is gone: those endpoints no longer carry `𝗜𝚺₁` at all. Tranche 7
deleted `QuotationTheoryPresentation.theory_sigmaOne` and let each site take the weaker
instance its proof actually spends, and the r.e.-ness step that was said to need `𝗜𝚺₁`
(`provable_instances_re` over Foundation's internal `Bootstrapping` predicate) is not in
their elaborated binder lists. Second, where `𝗜𝚺₁` does survive it is the substrate's index
for a fixed-point or numeral-arithmetic step, which is the `[T.Δ₁]` kind of charge —
infrastructure — not a hypothesis the paper's reader must verify of their Θ before using
the theorem.

### The Σ₁-soundness premise — closed 2026-08-30 (historical)

**This subsection is history.** No declaration in `LogicalInduction/` carries a
`SoundOnHierarchy` instance binder; the only remaining occurrence of the name is
`loopsTheory_soundOnSigma1`, a fact about one concrete theory used as a non-vacuity witness
for `thm:loops`'s `hloops`. It is kept because the reasoning is what a future reader needs
when tempted to reintroduce a second independent schema.

Soundness *was* genuinely consumed, not decorative. Foundation's weak-representation lemma
`re_complete : A x ↔ T ⊢ (codeOfREPred A)/[‘↑x’]`
(`.lake/packages/Foundation/Foundation/FirstOrder/Arithmetic/R0/Representation.lean:257-262`)
is stated under `[T.SoundOnHierarchy 𝚺 1]`, and its **`.mpr` direction is the soundness
direction** — provable ⇒ true. Exactly two constructions used it that way, both about
keeping the *constructed stage world* consistent: `luvWorld_consistent`
(`Construction/Witnesses/LUVDeductiveProcess.lean`, migrated 2026-08-29) and
`theoremDP_hworld`'s **tag 5**, the quotation lane (migrated 2026-08-30). Every other
`re_complete` call uses `.mp`, which is Σ₁-completeness and is discharged by the paper's own
hypothesis. tex:2673 treats soundness as a **further** assumption the paper explicitly
declines to take: "If we assumed further that Θ were sound as a theory of the natural
numbers, this would allow us to solve the halting problem…".

What made that tag need it was the *shape* of the quotation schemas, not a missing proof.
`universalQuotePos` and `universalQuoteNeg` used to be two **independent** `codeOfREPred`
Σ₁ schemas, so the only thing separating their fibers was that no computation returns both
`1` and `0` — a fact about `ℕ`, reached through `re_complete`'s `.mpr`. They are now the
value-`1` and value-`0` fibers of **one** Foundation `code` formula for the universal quote
evaluation (`Framework/QuoteRepresentability.lean`):

```
universalQuoteCode : Nat.ArithPart₁.Code 1     -- one code for the whole partial evaluation
universalQuotePos  := valueSchema universalQuoteCode 1
universalQuoteNeg  := valueSchema universalQuoteCode 0
```

`valueSchema_prov` gives either literal from Σ₁-completeness (`[𝗥₀ ⪯ T]` only — previously
only the positive one was that cheap), and `valueSchema_exclusive_prov` gives
`T ⊢ ∼(pos/[w̄] ⋏ neg/[w̄])` from single-valuedness of `code` in every model of `𝗣𝗔⁻`
(`code_uniq`, revived from Foundation's commented-out block) plus Gödel completeness. Tag 5
then closes from `Entailment.Consistent Θ` exactly like tags 1 and 3, and the binder that
propagated through the `theoremDP` layer is `[Entailment.Consistent T]`. No module moved,
no endpoint statement changed shape, and — decisively — `thm:lp` survived: a per-decider γ
would have been `Classical.choose`-obtained and hence not computable in the decider, which
would have broken `diagonalPriceDecisionPart_partrec`, whereas the two schemas here are
still compile-time constants. The superseded architectural diagnosis (a per-decider γ, a
paper-prime atom, an import-layer reorganization) was **wrong**, and the reason is worth
keeping: the universal quote evaluation is *partial*, so it has no `RepresentsComputations`
γ — but it needs none, because one `code` formula already carries both literals as two
value fibers.

The bounded computational-knowledge lane went the paper's own way rather than losing
soundness by refactoring. If Θ represents computations it *refutes* every false decidable
claim, so fiber exclusivity follows from consistency alone, without truth;
`Construction/Witnesses/ComputationRepresented.lean` names the `thm:pac` / `thm:pazfc` /
`thm:dontwait` claim family the paper's way, through `⌜f⌝(⌜n⌝)` for a *total* computable
decider, so both literals come from one sentence and the stage world exists from
`Entailment.Consistent Θ` (`paperDP_nonvacuous`, the single market's union process). The unbounded lane needs even less:
`thm:halts`'s positive literal is Σ₁-completeness alone (`re_complete_mp`) and `thm:loops`'s
negative one is its own `hloops` premise, which the paper likewise assumes outright
(`app:loops`).

**Blast radius: zero.** Of the 105 canonical endpoints, **0** name `[T.SoundOnHierarchy 𝚺 1]`
in their elaborated signature. That is down from 16, in three migrations; the last
(2026-08-30) removed twelve at once — `lic_introspection_closed`,
`lic_paradox_resistance_ofDiagonal_unconditional`, `lic_self_trust_closed`,
`lic_expectations_of_probabilities_closed`, `lic_iterated_expectations_closed`,
`lic_expected_future_expectations_closed`, `lic_no_expected_net_update_closed`,
`lic_no_expected_net_update_conditional_exact_canonical`,
`lic_disbelief_inconsistent_theories_unconditional`,
`FeedbackTruth.lic_wub_ofComputation_unconditional`,
`boundedCombination_wubaff_ofComputation_unconditional` and
`luv_wubexp_ofComputation_unconditional` — all of which reached the instance through tag 5,
and all of which now carry `[Entailment.Consistent T]` in its place.

### How this is charged

A row is demoted to `qualified` when **no** endpoint shown for that label renders the
paper's printed statement under the paper's own hypotheses. Two different things can spoil
that, and both must be checked; an earlier edition checked only the first and then
dismissed the second by fiat.

1. The endpoint carries a hypothesis the paper does not take. Σ₁-soundness was the standing
   case; no endpoint carries it any more, and the check is kept as a live test rather than
   as a description. `[T.Δ₁]` and the diagonal's `[𝗜𝚺₁ ⪯ T]` do **not** trip this check, by the rulings
   above: both are representation infrastructure disclosed globally. `[𝗣𝗔⁻ ⪯ T]` is a
   real strengthening beyond the paper's premises, and by the user's ruling of 2026-08-31 it is
   charged **globally**, alongside `[T.Δ₁]` — disclosed once under *Arithmetic-theory
   hypotheses* and levied against no row, which is why no row below re-argues it.
2. The endpoint is instance-free, but reaches that state by **assuming an interface the
   paper derives**. The paper's `thm:halts` / `thm:loops` / `thm:dontwait` obtain the
   provability (or refutability) of the halting claims *from* the standing assumption that
   Θ represents computations. The universal forms `lic_learns_halting_patterns` and
   `lic_learns_provable_nonhalting_patterns` (`Properties/MetaLearning.lean:108-133`,
   inventoried in `AxiomAudit.lean`) name no theory at all: they take
   `R : RepresentedSemidecidableClaims DP (fun n => CodeHalts (machines n) (inputs n))`,
   a caller-supplied sentence family already carrying `provable_of_true`. That is the
   *conclusion* of representability handed in as data, not the paper's hypothesis, so it
   does not restore the printed statement either.

The criterion, then, is: a shown endpoint spares the row iff its hypotheses are the printed
ones — or globally-disclosed infrastructure — rather than a stand-in for something the
paper derives from Θ. Applied uniformly under the 2026-08-30 rulings:

* **Spared** — `thm:ref`, `thm:lp`, `thm:st`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`,
  `thm:ccee`, `thm:halts`, `thm:loops`, `thm:dontwait`, plus `thm:scon`, `thm:wub`,
  `thm:wubaff`, `thm:wubexp`. For the first eleven, the shown endpoint is the closed /
  `_unconditional` form over `LIA`, whose binders are now the paper's own premises plus
  globally-disclosed infrastructure; check (2) is satisfied because that endpoint *derives*
  the represented-claims interface rather than taking it as data — it is the *universal*
  layer of `thm:halts`/`thm:loops`/`thm:dontwait` that takes it, and that layer is not what
  is shown. For the last four, the shown `_ofComputation` endpoint is instance-free *and* at
  the paper's printed hypotheses: `lic_wub_ofComputation` takes the paper's own truth bridge
  `TheoryTruth φ DP truth` and its timed-feedback program `FeedbackTruthComputation`
  (tex:1249-1258's premises), and `thm:scon`'s two printed forms quantify over conditioning
  data with no theory anywhere in the statement.
* **`qualified` — now empty for theorem and lemma nodes.** No theorem or lemma node in this
  ledger carries that status. `thm:incons`, the last one, moved to `exact` in tranche 10, when
  its theory sequence became an arbitrary **machine-enumerated** recursively axiomatized family
  (`hm : DigitMachineCodes m`, `hinc : ∀ n, ¬Consistent (theoryOf (m n))`) rather than the
  deduction family `Θ′ₙ = Θ₀ ∪ {σₙ}` over a fixed Δ₁ base. The **tranche-9b obstruction is not
  withdrawn**: Foundation's fixpoint blueprint for `Derivation` still cannot host satisfaction
  over coded formulas, so there is still no uniform-in-theory-code derivability predicate to be
  had at this level, and any repair that wanted one would still be a truth-predicate project.
  What changed is that `thm:incons` no longer depends on it — the T10 rendering never forms such
  a predicate. It quantifies over coded machines *externally*, at `V := ℕ`, and buys the
  uniformity from **compactness**: an inconsistency is witnessed by finitely many axioms, a
  finite list of written axioms splices into one written conjunction at token level, and
  refuting that conjunction is a question of pure logic — so the represented predicate runs over
  the **empty** theory and mentions no base theory at all. Both charges this bullet used to
  carry are therefore gone: the deduction-family paraphrase (retired, tranche 10) and, before
  it, the Gödel-code-metered `def:ec` premise `hσ : BigDigits (deductionFamilyArg σ)` (retired,
  tranche 9-pre), now `DigitMachineCodes` on the machine's own written source. The only
  `qualified` row left anywhere in this ledger is the **definition** node `def:ec`, which is not
  in the theorem/lemma table and which likewise now stands on a **verified obstruction** rather
  than on unexplored ground — see its row for the split converse and the missing
  fuel-accounting compiler.
  `thm:pac` and `thm:pazfc` both **left this list in tranche
  8**: they are one construction at two theories, each pricing the arithmetized
  finite-consistency family of a theory `Θ′` built by `Framework/BoundedConsistency.lean` —
  `thm:pac` at the diagonal `Θ′ = Θ` with consistency proved from the paper's own
  representability premise, `thm:pazfc` at a second theory with the paper's own explicit
  consistency premise and a discharged `𝗜𝚺₁`/`𝗣𝗔` witness — and since tranche 9a retired
  `dd:proofcode` in favour of the paper's own symbol measure, nothing stands between either and
  its printed statement but the stated counting convention `dd:symbolcount`. The `rfl` identity between the two nodes has been deleted and is false: the
  abstract `lic_belief_stronger_theory_consistency` layer no longer exists, and the two
  endpoints differ in which theory is metered.

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
| def:blcp | exact | n/a | direct rendering of the paper's two clauses — an efficiency certificate on the compiled threshold mesh plus one uniform `L¹` bound — and stated over the paper's own LUVs as well as the abstract carrier: `PaperLUVCombination` carries its shares as literal `PaperLUV`s and reaches `LUV` only through `toLUV`, `boundedSequence` discharges the bounded-sequence interface from that data with the family's own structural threshold certificate, and `unitFracPaperLUVBoundedSequence` inhabits it with the genuinely varying `1/(n+1)` family. The carrier-level charge that used to sit here is gone, on the same footing as `def:luv`'s **status disclosure**. The shown rendering `LUVCombination.BoundedSequence` carries no token-metered threshold hypothesis — its metering runs through `AffineCombination.PolySequence.sentence_poly : BigSentenceCodes`, the write-out class — so the row keeps its status. The literal-paper endpoints `PaperLUVCombination.boundedSequence` and `unitFracPaperLUVBoundedSequence` do inherit `PaperLUVSeq.structural`, which is the paper's own `def:ec` condition on the shares' defining formulas and not a narrowing of the admissible LUVs; see *LUV-threshold metering: rendering sensitivity, witnessed* above. |
| def:dedproc | exact | n/a | `D` and `mono` are the paper's nondecreasing finite sets; "computably enumerable" lives in the separate certificate `DeductiveProcessComputation`, taken as a hypothesis exactly where the paper says "computable deductive process" |
| def:deferralfunc | exact | n/a | `n < f n` with the emitter clocked polynomially in the *output* `f n`, as the paper asks, so `f` may grow fast |
| def:ec | qualified | n/a | **The trader half is closed.** `MachineEfficientTrader` is an honest complexity class — some `Complexity.FP` function of the *unary* day emits the day's strategy — and it is the class the construction dominates: the trader enumeration is sound and complete for exactly it (`enumeratedTrader_machineEfficient`, `exists_enumeratedTrader_eq`), and `IsMachineLogicalInductor` is what `LIA_isMachineLogicalInductor` proves. `dd:fuel` is a certification device for that class (`EfficientlyComputable.toMachine`), not a substitution for it. What qualifies the row is the other half: the efficiently computable *sequence* classes the property tail takes as its own data are still the **fuel** rendering — an `evaln` certificate rather than a machine — so those statements quantify over a possibly smaller set of admissible data than the paper's. **Where the charge actually sits (census, corrected).** An earlier edition of this row named `RpnSentenceCodes`, `RpnThresholdCodes` and `PolySequence` as its carriers; that list predates the write-out migration and is stale. Counted over the 105 canonical endpoints, through the structures they bind and not only their printed binders, the charge is carried by the **write-out** classes: `BigSentenceCodes` reaches **51** endpoints and `BigSpliceStream` **52**, **64** of the 105 in all, while the token-metered `RpnSentenceCodes` binds **none**. It bound exactly one until the final fix-wave — `lic_self_trust_closed`, which had to discharge a `LUV.RpnThresholdCodeSeq` obligation and had no write-out threshold class to reach for. `LUV.BigThresholdCodeSeq` now exists (`Framework/Expectations.lean`, with `LUV.RpnThresholdCodeSeq.toBig` and `LUV.BigThresholdCodeSeq.reindex`), `SelfTrustQuote.product_codes`/`.confidence_codes` were widened to it, and that endpoint now takes `hφ : BigSentenceCodes φ` like the rest. Two token-metered retentions remain on the surface, both off the canonical endpoint census: `LUV.RpnThresholdCodeSeq` on the `_ofRepresentation` layer of the quotation family, and `CompactConditioningProcessComputation.condition_codes` / `ConditioningPresentation.condition_codes` at `thm:scon`, where the retention is forced and is disclosed on that row. Those classes are wider than the token-metered ones and none of them bounds a value; what is charged is that their certificates are fuel certificates. **The machine reading has no consumer, and the earlier claim that it had one was wrong.** `MachineSentenceCodes` (`Framework/Machine/SentenceCodes.lean`) exists, with the inclusion `RpnSentenceCodes.toMachine`, and is consumed **nowhere in the development** — an earlier edition of this row said it was consumed at `thm:scon`, and that is false: `thm:scon`'s transports consume `RpnSentenceCodes` through the separately defined `CondStep.MachineSentenceBlocks` (`machineSentenceBlocks_of_rpn`, `Construction/Machine/CondStep.lean`), a different predicate that happens to read similarly. **The converse inclusion does not merely stand open — it splits, and the open half is a verified obstruction.** At the *length-metered* target — a machine write-out certificate compiled back to an `evaln`-fuel one — it is open, and the obstruction is named rather than unexplored: the missing ingredient is a TM → `Nat.Partrec.Code` compiler that carries fuel accounting, because `evaln`'s fuel guard decrements per constructor while the machine's cost is measured in emitted symbols, so the `comp` case cannot be reconciled without one; a machine whose output word is exponential in its input is exactly where the two meterings come apart. At the *value-metered* target the converse is **false**, not open: `not_polyFueled_two_pow` refutes it at `2^n`, which is a `Complexity.FP` function once its output is written in binary. Both repair directions need that same missing compiler, so closing this would mean redefining `dd:fuel` — an index-oracle certification device rather than a complexity class — not proving one more lemma. The row therefore stays `qualified` **on a verified obstruction**, which is what it is now recorded as standing on. This is the global fuel charge, levied here and nowhere else. It covers the **token-metered** classes only: the whole-value classes (`PolyRatCodes`, `PolyNatCodes`, `PolyMachineCodes`, `PolySentenceCodes`, `PolyThresholdCode(Seq)`) bound the Gödel *value* rather than the symbol count, are strictly smaller, and are charged at each row that takes one — see the disclosure section above. **No paper-facing row takes one any more.** The write-out classes now exist for every kind of datum the property tail consumes — `BigDigits` for naturals, `DigitRatCodes` for rationals, `DigitMachineCodes` for machine codes, `BigSentenceCodes` for sentences, `BigSpliceStream`/`BigTokenStream` for the emission surface — and the machine/input migration retired the last consumers: `thm:halts`, `thm:loops` and `thm:dontwait` traded `PolyMachineCodes`/`PolyNatCodes` for `DigitMachineCodes`/`BigDigits`, and the `input_poly` field of the since-retired `SemidecidableComputation` became `BigDigits`. `PolyMachineCodes` is now named only inside `digitMachineCodes_nest_not_polyMachineCodes`, the witness that refutes it; `PolyNatCodes` survives only in `not_polyNatCodes_ack`, in `bigDigits_two_pow_not_polyNatCodes`, and in one internal helper (`quotationClaimSentence_poly`) that names a *caller-chosen index sequence*, never the paper's `⟨x⟩`. What remains charged here is the fuel rendering itself, not a value bound. **No second charge is levied here for the object language.** An earlier edition charged one — the token-metered classes were *not coextensive with this node* on `⟺`, since Foundation's negation-normal-form `Semiformula` duplicates both sides of a biconditional while the paper's language has `⟺` as a primitive (tex:560). That is repaired, not disclosed: formula families are metered on the paper's **source** language (`ArithSource`, `PolyArithmeticSourceSeq`), one emitted token per node of the formula as the paper writes it, with normal-form expansion done inside the parser and never charged. `dd:nnf` now names that two-layer architecture, and the normal-form-metered `PolyArithmeticFormulaSeq` is retained only as a strictness foil, with `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq` proved at the biconditional chain (`iffChainSource_polyArithmeticSourceSeq` / `iffChain_not_polyArithmeticFormulaSeq`) and carried to a literal paper LUV family (`iffPaperLUVSeq`). See *LUV-threshold metering: rendering sensitivity, witnessed* above. |
| def:ece | exact | n/a | direct rendering of market-generability: rank bound, emitter, closure, denotation — nothing retained beyond the global fuel model. The emitter field `polyTok` is **write-out** metered (`BigSpliceStream`), so a feature's constant leaf may name a rational whose Gödel code is exponential in the day; `PGenerableRat.ofDigitRatCodes` is the general constructor and `pGenerableRat_two_pow_inv` witnesses that the width is real (the paper's `δ n = 2⁻ⁿ` is admitted, and is refuted by the value-bounded `PolyRatCodes`). This is a **strengthening of an already-`exact` row**: the field was `RpnSpliceStream` before, which silently excluded that datum; `PGenerableRat.ofPolyRatCodes` survives only as the derived value-bounded corollary |
| def:fuz | exact | n/a | direct rendering of a generable weighting: the same data as `def:ece` minus the denotation clause, so a trader can trade on the weighting without knowing its values. That relation is now a theorem rather than a remark — `pGenerableWeighting_iff` (`Properties/Calibration.lean`) proves `GeneratedRatFeature P q W ↔ PGenerableWeighting W ∧ ∀ n, (W n).denote P = q n`, which became statable once both structures metered emission by `BigSpliceStream` |
| def:lia | exact | n/a | the recursion itself: `liaStates DP n` is the market maker's fixed point against the trading firm run on the history of days `< n`, and `liaHistory` is the market it induces. The three components are separate audited constructions; `thm:lia` certifies the assembly |
| def:lic | exact | n/a | `IsMachineLogicalInductor` states the criterion at the paper's own quantifier — no `Complexity.FP` trader exploits the market — and is the criterion the construction proves. Its field set is frozen at Tier 2 alongside `IsLogicalInductor`, the fuel-class compatibility reading reached from it by `IsMachineLogicalInductor.toIsLogicalInductor`; the fuel class is what the whole §4 tail is *conditioned* on, which makes those theorems stronger, not weaker. Both bundle two facts the paper leaves ambient — the market and the process are computable |
| def:luv | exact | n/a | `PaperLUV` is the paper's object literally: an `ArithmeticSemisentence 1` carrying object-level `T`-proofs of unique existence and `[0,1]` membership. `toLUV` compiles it into the abstract threshold carrier `LUV` (field `gt`) that downstream results consume; `PCWorld.ValuesAt` is *derived* through `paperTheoryDP` and the rational cut rather than assumed, and `PaperLUVSeq` compiles the literal threshold syntax to `RpnThresholdCodeSeq`. Inhabited by a varying `1/(n+1)` family. The abstract `LUV` is shown second precisely because it is the over-general one. **Status disclosure.** `PaperLUV`, the shown rendering of the node, carries no efficiency field at all, which is why the row stays `exact`; the *sequence* wrapper `PaperLUVSeq` does carry one — `structural : PolyArithmeticSourceSeq` on its `source` field, the paper's own writing of the defining formula, with `compiles` the bridge to the Foundation formula — so `PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq` quantifies over `PaperLUVSeq`, not over `ℕ → PaperLUV`, and an earlier edition of `LogicalInduction/README.md` was wrong to cite it as placing *every* literal `PaperLUV` sequence in `RpnThresholdCodeSeq`. That field is the paper's own `def:ec` condition on the defining formula and not a narrowing of `def:luv`: it meters the formula string one token per `ℒₒᵣ` node, so the paper-natural `X > 2⁻ⁿ` is admissible once its denominator is named compactly, as the paper names large values (`dyadicPaperLUVSeq`, `dyadicPaperLUVSeq_frontend`), beside `unitFracPaperLUVSeq` at `1/(n+1)`. What is left on numerals is an artifact of Foundation's *unary* `Operator.numeral` and not a narrowing (the paper fixes no numeral notation, tex:614/tex:757). The former `⟺` gap is closed rather than charged: the metering is on the paper's source language, and the frontend is additionally inhabited at the biconditional family `iffPaperLUVSeq` — `O(n)` characters to write, `≥ 2ⁿ` nodes in the Foundation normal form. See *LUV-threshold metering: rendering sensitivity, witnessed* above |
| def:trader | exact | n/a | a trader is its day-indexed strategy function; all economic content (holdings, exploitation) is derived, matching the paper's reading of a trader as a strategy sequence |
| def:tradestrat | exact | n/a | direct rendering: `trades` is the paper's `ξ₁φ₁ + …`, `rank_le` the paper's rank condition that an `n`-strategy mentions only prices of days `≤ n` |
| lem:mesh | exact | universal | `mesh_independence_ofSyntax` retains `[IsLogicalInductor]`, the `def:blcp` bounded sequence, and `S : LUVCombinationSyntax` — the paper's own ℙ-generable presentation, inhabited by `ordinaryLUVCombinationSyntax`. It is cleaner than the sibling `mesh_independence`, which additionally demands a `MeshSoftmaxOperationalWitness` and an explicit rational bound |
| lem:tfdom | strengthened | universal | no inductor hypothesis, as in the paper: any rational `[0,1]` market exploited by *some* efficient trader is exploited by the firm. Strengthened because the exploiter hypothesis is `MachineEfficientTrader`, the *larger* class, hence the weaker premise; the fuel-class corollary `trading_firm_dominance_of_ec` is correctly internal. The enumeration covering the whole class is `exists_enumeratedTrader_eq` |
| thm:affcoh | exact | universal | analytic capstone over `[IsLogicalInductor]` with the paper's bounded-combination data. `BoundedCombinationSequence` is *defined* as `PolySequence` + `L¹` bound, so stating the endpoint over `PolySequence` + `BoundedAffinePrices` + a magnitude bound is a decomposition of the paper's class, not a narrowing |
| thm:affpolymax | strengthened | universal | same conclusion shape as the paper, but over the bare `BoundedCombinationSequence`: the price and magnitude bounds are derived from the sequence rather than assumed |
| thm:affprovind | exact | universal | the printed display is `≳ₙ`, "and similarly for `=`/`≈ₙ` and `≤`/`≲ₙ`", so all three directions are the node. `_ge` is shown first because it is the printed one; `_eq`'s hypothesis (`value = b`) implies both one-sided ones and its body is `asympEq_iff_asympLE_asympGE` over them, so it is the weakest of the three and sits last |
| thm:benford | strengthened | universal | `PseudorandomFrequency` quantifies only over additionally `DeferralPatient` weightings — a *weaker* premise than `def:pseudorandom`, hence a stronger theorem; `f = n+1` recovers the paper's case. Clock-free: maturity and settlement are constructed internally. The paper's headline is `≈ₙ`, so the two-sided form leads |
| thm:ccee | exact | instantiated | `lic_no_expected_net_update_conditional_exact_canonical` takes exactly the paper-facing source interface (`X : ℕ → LUV`, `RpnThresholdCodeSeq X`, completed-world `source_valued`), a bare `DeferralFunction`, and a ℙ-generable `[0,1]` weight — write-out metered since `GeneratedRatFeature.polyTok` became `BigSpliceStream`, so a weight sequence with exponential codes but polynomial write-out (`pGenerableRat_two_pow_inv`) is admissible. Zero slack — the generic `_ofRepresentation_unconditional` carries a vanishing `slack` and an approximation premise; this signature has neither — and no caller-visible freshness or proof-carrying certificate, unlike the sibling `lic_no_expected_net_update_conditional_exact_productExtension`, which demands `ProductAtomFresh X` and a caller-supplied extension. The sole market is `liaHistory (canonicalCCEEDP T)` — **the one canonical endpoint priced outside the single market `paperDP`**, by the round-13 scope ruling (see *The single market* above) — whose computable, explicitly non-vacuous process is fixed from `T` before `X`, `f`, or `w`; one canonical enlarged language from the outset, not a source-dependent extension. **Disclosed gap:** the process side of non-vacuity is witnessed (`canonicalCCEEDP_computable`, `canonicalCCEEDP_hworld`), but there is no witness that this endpoint's `weight_generable` hypothesis is inhabited by a non-constant weight — the only such N+, `lic_no_expected_net_update_conditional_exact_productExtension_nonvacuous`, lives over `exactProductDP`, not over `canonicalCCEEDP`. **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` was **deleted outright** in tranche 7, with `QuotationTheoryPresentation.theory_sigmaOne`: the endpoint had inherited it from that field and from no step of its own, and now spends only `𝗣𝗔⁻`. The `_exact_canonical` form is the only endpoint shown for this label. **Residual disclosure:** the `weight_generable` non-vacuity gap named above — no `N+` exhibits a non-constant admissible weight over `canonicalCCEEDP` — which is a missing witness rather than a weakening of the statement, so it does not lower the status |
| thm:cee | exact | instantiated | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq`, with the deferred-expectation quote constructed and a bare `DeferralFunction` (`f n > n`, as `def:deferralfunc` asks). The only remaining premise is the paper's own "the source is an LUV of the theory" (`source_valued`). **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` was **deleted outright** in tranche 7, with `QuotationTheoryPresentation.theory_sigmaOne`: the endpoint had inherited it from that field and from no step of its own, and now spends only `𝗣𝗔⁻`. The `_closed` form is the only endpoint shown for this label, and it is now at once closed over `LIA` and at the paper's own theory hypotheses; nothing is charged against the row |
| thm:ceu | exact | instantiated | the cleanest endpoint in the paper: exactly a deferral function, the sentence sequence, and its `BigSentenceCodes` (the write-out class; widened from `RpnSentenceCodes`, which was consumed only via `.primrec`). The quote code is constructed; no reflection data and no deferral narrowing. **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` was **deleted outright** in tranche 7, with `QuotationTheoryPresentation.theory_sigmaOne`: the endpoint had inherited it from that field and from no step of its own, and now spends only `𝗣𝗔⁻`. The `_closed` form is the only endpoint shown for this label, and it is now at once closed over `LIA` and at the paper's own theory hypotheses; nothing is charged against the row |
| thm:con | exact | universal | genuine trader proof over `[IsLogicalInductor]`; the oscillation trader is constructed inside the proof, and the statement carries only the criterion instance and stage consistency. `lic_limitingBelief_tendsto` leads because the paper's statement *defines* `ℙ∞(φ) := lim ℙₙ(φ)`, and `limitingBelief` is the `ℙ∞` that `thm:lc`, `thm:perkno`, `thm:nd` and `thm:ob` consume downstream; `lic_price_convergesTo` proves the same fact in bare `∃ L` form |
| thm:dontwait | exact | instantiated | **Soundness-free, and the sentence names the machine.** Unconditional over `LIA` on the paper's own provability process, under `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [RepresentsComputations T]` — the last being the Lean rendering of tex:600-606's “Θ represents computations”, which supplies consistency itself — with **no** `[T.SoundOnHierarchy 𝚺 1]` and no `[𝗜𝚺₁ ⪯ T]` (census 2026-08-30: 0 of 105 endpoints carry the former, 3 the latter, none of them this one). **What is represented is universal.** The decider is `universalRunValue steps`: it decodes a packed `⟨⟨source, input⟩, day⟩` argument, runs the decoded machine under `evaln` for `steps day` interpreter steps, is *total* (`Code.ofSource` and `evaln` are everywhere defined) and mentions **no machine sequence** — so `RepresentsComputations` supplies **one** `γ` per horizon program, which is exactly the paper's `⌜f⌝` (`exists_reprAll_of_representsComputations`). The day-`n` claim is that one `γ` at the argument `t = binNumeral (boundedArg machines inputs n)`, i.e. at the compact name of `⟨⟨⌜qₙ⌝, yₙ⟩, n⟩`, and reads `∀ν (γ(t, ν) ⟺ ν = 0̄)` — the paper's `⌜f⌝(⌜n⌝)` idiom with the machine and its input written in. **Both literals come from that one sentence:** failure gives a proof of it and success a proof of its literal negation (`represents_proves` / `represents_refutes_all`), carried to the compact spelling by `provable_subst_iff_of_val`, so the constructed stage world is consistent from `Entailment.Consistent Θ` alone (`paperDP_nonvacuous`, over the single market's union process), which representability already gives (tex:604). This also answers charge (2) of *How this is charged*: the represented-claims interface is **derived** from the paper's standing premise rather than supplied as data. **The horizon is the paper's own, and strictly wider than it was.** `hh : ComputableHorizon horizons` is a program plus its specification with no growth bound, so **any** computable `f` (tex:1946-1952) is admissible where the former `PolyNatCodes horizons` restricted it to polynomial time; the generalization is *proved strict* (`ComputableHorizon.ackermann` admissible, `not_polyNatCodes_ack` excluding it from the old class). Genuine subject matter: `machines : ℕ → Nat.Partrec.Code` under a real `∀ n, ¬CodeHalts (machines n) (inputs n)` hypothesis. **The two e.c. class hypotheses are the paper's own, and they are load-bearing.** `hm : DigitMachineCodes machines` and `hi : BigDigits inputs` are metered by *write-out*: tex:1931-1933 says in as many words that it must be possible to write out the source code of `mₙ` in time polynomial in `n`, and a poly-time writer emits polynomially many **symbols**, so source of length `poly n` — codes of magnitude up to `2^poly(n)` — is admissible, and `⟨x⟩` is a sequence of *bitstrings*. This row previously took the whole-value pair `PolyMachineCodes`/`PolyNatCodes` (`IsPolyBounded` on the Gödel *value*), which `not_polyFueled_two_pow` refutes at `2^n`. The widening is **proved strict in both coordinates**: `bigDigits_two_pow_not_polyNatCodes` exhibits `xₙ = 2ⁿ` — an `n`-bit string, the paper's own `⟨x⟩` shape — as `BigDigits` and not `PolyNatCodes`, and `digitMachineCodes_nest_not_polyMachineCodes` exhibits `Nat.Partrec.Code.nest` — `nest 0 = zero`, `nest (n+1) = pair (nest n) zero` — a real machine sequence whose source is `2n + 1` symbols long while its source number is at least `2^n`, as `DigitMachineCodes` and not `PolyMachineCodes`. **Their consumer is the `def:ec` obligation itself.** The argument numeral's symbol run is emitted digit by digit from exactly those two certificates (`boundedArg_digits` → `polySegStream_binNumeral_const` → `representedClaimSentence_bigSentenceCodes`), so deleting either breaks the emission proof — the deletion test the previous rendering failed, where their only consumer was an r.e.-ness step that is free for a constant predicate. The token-metered classes themselves remain under `def:ec`'s global fuel charge, levied there and not re-levied here. **Non-vacuity of the naming is proved, not asserted.** `representedClaimSentence_ne_of_runValue_ne`: if the represented decider takes different values at two arguments, the two claim sentences are different propositions — proved from the representability premise alone, with nothing assumed about `γ`. **The applied client discharges everything:** `neverHaltMachine` with non-halting *proved*, the paper's `⟨y⟩ = 2 ^ n` inputs and the identity horizon through `ComputableHorizon.of`. **The earlier reading that the paper-literal shape is unavailable on `paperTheoryDP` is withdrawn.** It was true only of Foundation's *unary* `Semiterm.Operator.numeral`, where a numeral costs its own value in symbols; the paper fixes no numeral notation (tex:564, tex:614), and the compact Horner term `binNumeral` names the same value in `O(log v)` `ℒₒᵣ` nodes. Provability is insensitive to the choice — `provable_subst_iff_of_val` is Gödel completeness in both directions and needs only the `𝗣𝗔⁻ ⪯ T` already in the binder list — so only the emission cost changes, and the write-out class is what pays it. **Nothing remains charged on theory strength (settled 2026-08-30).** This row used to carry a residual `[𝗜𝚺₁ ⪯ Θ]`, on the ground that `paperTheoryDP` is proved computable through Foundation's *internal* provability predicate (`provable_instances_re`, `ComputationDP.lean`). Tranche 7 deleted that binder: with `QuotationTheoryPresentation.theory_sigmaOne` gone, each site takes the weaker instance its proof actually spends, and the census over the 105 canonical endpoints — elaborated `#check`, not docstrings — finds `𝗜𝚺₁ ⪯ ·` in exactly three signatures, none of them this one. What the endpoint asks for now is the paper's own standing assumption on Θ. Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. **Naming note:** `DigitMachineCodes` meters the machine's *source* encoding (`Code.sourceNat`), which is linear in the description and decodable in steps linear in the source length (`ofSource_peelSteps`, `sourceNat_peelSteps_le`); Mathlib's `Encodable.encode` on `Nat.Partrec.Code` squares per constructor node and is deliberately not the naming map here. **The defect the source encoding repaired.** Under Mathlib's `Encodable.encode` this class silently excluded the paper's own example: `nest n` has `2n + 1` syntax nodes but base-4 `encode` digit counts 0, 2, 4, 8, 16, 33, 67, 134 — *exponential* in `n`, hence an encoded **value** doubly exponential in `n`, against a source linear in `n` — because `encodeCode` squares at every `pair`/`comp`/`prec` node. `Code.sourceNat` is linear in the syntax tree, so the class now contains what the paper says it contains. *Superseded 2026-08-30 (R5-F08/F09).* Previously `γ` was `RepresentsComputations.repr` of `boundedRunValue machines input steps`, a decider that *mentions* the sequence, and `RepresentsComputations.repr` sees only the `ℕ → ℕ` function it denotes; under this endpoint's own `hnever` that function is constantly `0`, so one formula served every admissible machine/input/horizon triple and the class hypotheses were decorative. `boundedHaltingClaimInput_digits` was the old lane's generator; it was re-verified dead in the T8/8 consolidation sweep and **deleted** (2026-08-31). `haltingClaimSentence_digits` is *not* consumer-less and is retained deliberately: it is the write-out certificate of a surviving event-tag row, and is fed by `computationClaimSentence_digits`, which an earlier edition of this ledger also called consumer-less and which survives for the same reason |
| thm:dus | exact | instantiated | quantifies over **any** `DP` and any `[IsLogicalInductor P DP]`, the paper's own generality. Inputs are the paper's semantic premise `IndependentBitAtoms`, the naming certificate, and the semimeasure's from-below presentation; prefix codes are metered by the **write-out** class `BigSentenceCodes` (`Framework/WriteOut.lean`) and inhabited (`ordinaryBitPrefixCodes`); the whole-value form is provably uninhabited here (`not_polySentenceCodes_bitPrefixSentence`). **Metering note, checked and deliberately not charged here:** `DUSApproximationPresentation.approximation_codes` and both fields of `DUSThresholdEmission` are whole-value `PolyRatCodes`. They do not lower the row under the disclosure section's test, on clauses (1) and (2): the datum they constrain is the repo-side rational approximation *table*, which the paper never quantifies over (it constructs one, "slowing an arbitrary lower approximation down to a polynomial-time table"), and the repo constructs and *proves* both certificates for its own universal semimeasure (`dusApproximationPresentation`, `dusThresholdEmission`). The presentation being a caller input at all is the retained representation interface this row already declares. **Instantiation: two witness layers, and only the second one counts.** The `_unconditional` forms fix `DP = emptyBitDeductiveProcess`, where every stage is `∅` and `realizable` is discharged **vacuously**; they are re-signposted at the declarations as *inhabitation only*, since the paper frames the node as fresh symbols added *to* `Θ`, and at `Θ = ∅` there is no "as well as". The substantive layer, landed in the final fix-wave, is `paperIndependentBitAtoms` / `paperBitPrefixSentences` over `paperDP T` — the same non-empty market the whole §4 tail runs on, with the bit atoms grafted at a freshly reserved `bitAtomTag := 7` and `realizable` proved rather than vacuous — carrying `lic_domination_universalSemimeasure_paperDP` (`Construction/Witnesses/UnconditionalOverLIA.lean`) and, through the constructed dovetail, the fully closed `lic_domination_dovetailSemimeasure_paperDP` and `lic_domination_everyLowerSemicomputable_paperDP`: **no caller input remains and no premise is vacuous.** That is what moves this row's axis to `instantiated`. Those three are deliberately not added to the canonical endpoint census above, which stays at 105 and whose class counts are computed against it; cite them from here. `thm:strict` has no such layer and stays `universal` |
| thm:ec | exact | universal | retains `[IsLogicalInductor]`, the paper's own `def:ec` threshold codes, stage joint consistency, and `def:luv`'s world-value fact at the paper's `cworlds(Θ)` quantifier (`∀ v, v.ConsistentWithTheory DP → ∃ x, v.ValuesAt X x`). The limit is constructed, not assumed. The former stage-quantified per-grid premise is gone and needed no compactness entailment to remove: the proof reads a world value only inside `filter_upwards [hae]`, where `hae` is `lic_limitCoherence`'s a.e. support on completed-theory worlds. |
| thm:ei | exact | universal | the paper's varying-sequence statement, genuine trader proof over `[IsLogicalInductor]`. `LUV.IsIndicator` quantifies over `v.ConsistentWithTheory DP` — completed worlds — which is exactly `app:ei`'s own quantifier (tex:5229) and not the stronger every-stage reading, which `indicatorWitness_not_stagewise` shows would exclude the paper's own indicator; `indicatorWitness_isIndicator` exhibits a non-degenerate inhabitant. |
| thm:epr | exact | instantiated | unconditional over `LIA` at `def:ec`'s own **write-out** class: the quote code is constructed from the market program (`paperPriceQuoteCode`), leaving exactly `φ` and `BigSentenceCodes φ`. (`BigSentenceCodes` is the write-out class; `RpnSentenceCodes` is the per-token-value-metered one, and an earlier edition of this row called this hypothesis token-metered and then named the write-out class.) **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` was **deleted outright** in tranche 7, with `QuotationTheoryPresentation.theory_sigmaOne`: the endpoint had inherited it from that field and from no step of its own, and now spends only `𝗣𝗔⁻`. The `_closed` form is the only endpoint shown for this label, and it is now at once closed over `LIA` and at the paper's own theory hypotheses; nothing is charged against the row |
| thm:er | exact | instantiated | unconditional over `LIA` at `LUV.RpnThresholdCodeSeq`; the expectation quote code is constructed via `expectQuote_computable`, leaving exactly `X` and its threshold codes. **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` was **deleted outright** in tranche 7, with `QuotationTheoryPresentation.theory_sigmaOne`: the endpoint had inherited it from that field and from no step of its own, and now spends only `𝗣𝗔⁻`. The `_closed` form is the only endpoint shown for this label, and it is now at once closed over `LIA` and at the paper's own theory hypotheses; nothing is charged against the row |
| thm:expcoh | exact | universal | retains `[IsLogicalInductor]`, the `def:blcp` bounded sequence, `S : LUVCombinationSyntax`, and `WorldValued` — the paper's own `def:luv` fact at `cworlds(Θ)`. `S` is the paper's own ℙ-generable presentation and is inhabited by `ordinaryLUVCombinationSyntax`, so it is not a retained interface. Nothing stage-quantified survives anywhere in the transitive premise set: `ConvergencePresentation.daily_value` became `world_value`, the upstream `TheorySemantics.stage_values` field was deleted, and the `ConvergencePresentation` argument is gone from the signature. Dominates the sibling `expcoh`, which additionally demands a `MeshSoftmaxOperationalWitness`, per-term threshold codes and an explicit bound. |
| thm:exppolymax | exact | universal | same premise set as `thm:expcoh` — the bounded sequence, `S : LUVCombinationSyntax`, and `WorldValued` — with the operational witness discharged; `exppolymax_arith` additionally discharges `WorldValued` for the certified class. |
| thm:expprovind | exact | universal | the printed display is `≳ₙ`, "and similarly for `=`/`≈ₙ` and `≤`/`≲ₙ`", so all three directions are the node and all three are shown, `_ge` first. Each takes precisely tex:1753-1757's one-sided bound at `cworlds(Θ)`, with each completed world free to pick its own valuation; `DeterminedViaTheory` is gone from them. The `_ofDetermined` variants take the *stronger* determinacy hypothesis, hence are weaker theorems and are internal; the fixed-LUV `lic_expectation_provind*` quantify over stage-plausible worlds and are a separate, weaker rendering. |
| thm:halts | exact | instantiated | **Soundness-free, and the sentence names the machine.** Unconditional over `LIA`, on the paper's own provability process: the endpoint is stated over the single market `liaHistory (paperDP T)` under `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]` — no `[T.SoundOnHierarchy 𝚺 1]` and no `[𝗜𝚺₁ ⪯ T]` (census 2026-08-30: 0 of 105 and 3 of 105 respectively, none of the latter this one), and no `RepresentsComputations` either, this lane needing no *represented* negative literal — with real subject matter: `machines : ℕ → Nat.Partrec.Code`, `inputs : ℕ → ℕ` and a genuine `∀ n, CodeHalts (machines n) (inputs n)` hypothesis, nothing bounding an individual machine's runtime, matching tex:1931. **The day-`n` claim is the fixed universal schema at a machine-naming argument.** `haltingArgClaimSentence machines inputs n` is `universalHaltingSchema` — Foundation's `codeOfREPred` for `UniversalCodeHalts z := ((Code.ofSource z.unpair.1).eval z.unpair.2).Dom`, one formula fixed once for the whole theorem — at the argument `⟨⌜mₙ⌝, xₙ⟩`, written into the sentence as the compact Horner numeral `binNumeral (haltingClaimInput (machines n) (inputs n))`. The machine and its input are therefore *in* the sentence, not inside the schema, which is what makes the claim family depend on them at all. The positive literal is Σ₁-completeness alone (`re_complete_mp` at the universal schema), the deductive process is the single market's `paperDP` — Θ's own provability process `paperTheoryDP` in union with the literal stream `theoremDP` — and market non-vacuity is `paperDP_nonvacuous` from consistency of `T`; the paper's own proof (tex:4495-4520) uses exactly Σ₁-completeness and consistency, so the “premise the paper does not take” qualification this row used to carry is gone. The public atom wraps that sentence in a vacuous `∃⁰` whose invisibility is **proved, not assumed** (`provable_schemaArgClaim_iff`, `provable_neg_schemaArgClaim_iff`). **The two e.c. class hypotheses are the paper's own, and they are load-bearing.** `hm : DigitMachineCodes machines` and `hi : BigDigits inputs` are metered by *write-out*: tex:1931-1933 says in as many words that it must be possible to write out the source code of `mₙ` in time polynomial in `n`, and a poly-time writer emits polynomially many **symbols**, so source of length `poly n` — codes of magnitude up to `2^poly(n)` — is admissible, and `⟨x⟩` is a sequence of *bitstrings*. This row previously took the whole-value pair `PolyMachineCodes`/`PolyNatCodes` (`IsPolyBounded` on the Gödel *value*), which `not_polyFueled_two_pow` refutes at `2^n`. The widening is **proved strict in both coordinates**: `bigDigits_two_pow_not_polyNatCodes` exhibits `xₙ = 2ⁿ` — an `n`-bit string, the paper's own `⟨x⟩` shape — as `BigDigits` and not `PolyNatCodes`, and `digitMachineCodes_nest_not_polyMachineCodes` exhibits `Nat.Partrec.Code.nest` — `nest 0 = zero`, `nest (n+1) = pair (nest n) zero` — a real machine sequence whose source is `2n + 1` symbols long while its source number is at least `2^n`, as `DigitMachineCodes` and not `PolyMachineCodes`. **Their consumer is the `def:ec` obligation itself.** The argument numeral's symbol run is emitted digit by digit from exactly those two certificates (`haltingClaimInput_digits` → `polySegStream_binNumeral_const` → `schemaArgClaimSentence_bigSentenceCodes`), so deleting either breaks the emission proof — the deletion test the previous rendering failed, where their only consumer was an r.e.-ness step that is free for a constant predicate. The token-metered classes themselves remain under `def:ec`'s global fuel charge, levied there and not re-levied here. **Non-vacuity of the naming is proved, not asserted.** `haltingArgClaimSentence_ne_of_halts_ne` shows that two machine/input pairs differing in halting behaviour receive *different* claim sentences. Note what it does not claim: distinct source numbers alone cannot be shown to give distinct sentences, because `universalHaltingSchema` is `Classical.epsilon`-chosen and nothing in the API rules out a formula ignoring its argument; disagreement of the two *runs* is the strongest separation an opaque schema supports. **The applied client is a genuinely varying family.** `Nat.Partrec.Code.nest` — source linear in the day, source *number* exponential, so the whole-value class provably excludes it — with the paper's `⟨x⟩ = 2 ^ n` inputs, both class certificates discharged (`Nat.Partrec.Code.bigDigits_sourceNat_nest`, `bigDigits_two_pow`) and the halting hypothesis *proved* (`codeHalts_nest`); nothing is left to the caller. **The earlier reading that the paper-literal shape is unavailable on `paperTheoryDP` is withdrawn.** It was true only of Foundation's *unary* `Semiterm.Operator.numeral`, where a numeral costs its own value in symbols; the paper fixes no numeral notation (tex:564, tex:614), and the compact Horner term `binNumeral` names the same value in `O(log v)` `ℒₒᵣ` nodes. Provability is insensitive to the choice — `provable_subst_iff_of_val` is Gödel completeness in both directions and needs only the `𝗣𝗔⁻ ⪯ T` already in the binder list — so only the emission cost changes, and the write-out class is what pays it. **Nothing remains charged on theory strength (settled 2026-08-30).** This row used to carry a residual `[𝗜𝚺₁ ⪯ Θ]`, on the ground that `paperTheoryDP` is proved computable through Foundation's *internal* provability predicate (`provable_instances_re`, `ComputationDP.lean`). Tranche 7 deleted that binder: with `QuotationTheoryPresentation.theory_sigmaOne` gone, each site takes the weaker instance its proof actually spends, and the census over the 105 canonical endpoints — elaborated `#check`, not docstrings — finds `𝗜𝚺₁ ⪯ ·` in exactly three signatures, none of them this one. What the endpoint asks for now is the paper's own standing assumption on Θ. Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. **The universal layer is not what is shown, and would not have spared the row on its own.** `lic_learns_halting_patterns` (`Properties/MetaLearning.lean`) takes no theory instance — but it does not restore the printed statement either, and the reason is *not* that it was left uncurated (an earlier edition said exactly that, which was a fact about curation, not about strength). It takes `R : RepresentedSemidecidableClaims DP (fun n => CodeHalts (machines n) (inputs n))`: a caller-supplied sentence family already carrying `provable_of_true`. The paper derives that from its standing assumption that Θ represents computations (tex:600-606), so assuming it is assuming the conclusion of the representability step. See check (2) of *How this is charged* above. **Naming note:** `DigitMachineCodes` meters the machine's *source* encoding (`Code.sourceNat`), which is linear in the description and decodable in steps linear in the source length (`ofSource_peelSteps`, `sourceNat_peelSteps_le`); Mathlib's `Encodable.encode` on `Nat.Partrec.Code` squares per constructor node and is deliberately not the naming map here. **The defect the source encoding repaired.** Under Mathlib's `Encodable.encode` this class silently excluded the paper's own example: `nest n` has `2n + 1` syntax nodes but base-4 `encode` digit counts 0, 2, 4, 8, 16, 33, 67, 134 — *exponential* in `n`, hence an encoded **value** doubly exponential in `n`, against a source linear in `n` — because `encodeCode` squares at every `pair`/`comp`/`prec` node. `Code.sourceNat` is linear in the syntax tree, so the class now contains what the paper says it contains. *Superseded 2026-08-30 (R5-F08/F09).* The previous rendering built the family as the day-numeral instance of `haltingSchema machines inputs := codeOfREPred (fun n => CodeHalts (machines n) (inputs n))`. `codeOfREPred` takes only the *proposition-valued* predicate, so under this endpoint's own `hhalts` the coded predicate is `fun _ => True` and the sentence family was literally the same for every everywhere-halting machine sequence, naming no machine and leaving `hm`/`hi` decorative. Every clause of that rendering — the day-indexed schema, the `haltingSeq_re` role of the class hypotheses, and the claim that the machine-naming shape was not emittable — is withdrawn |
| thm:ifp | refuted | n/a | **The printed theorem is false, and the corrected theorem is proved.** `not_overgeneral_ifp` negates exactly the printed quantifier — `∀ P P' DP N, IsMachineLogicalInductor P DP → ComputableMarket P' → tail agreement → IsMachineLogicalInductor P' DP` — with no theory parameter, `sorry`-free and axiom-clean, using the constructed `LIA` as the inductor and a day-`0` advice tape as the perturbation. The published proof's invalid step is the "only finitely many constants" claim at tex:6047-6062; the ledger is `notes/paper-errata.md` PE1. The **corrected** theorem is `FreezeOracle.machine_lic_iff_of_recognizableSupport`: two computable markets differing on only finitely many `(day, sentence)` coordinates satisfy the criterion together — strictly stronger than the paper's tail agreement in the direction that survives, and exactly the case where the appendix's constant table really is finite. It takes **no** patch argument, discharging the two `MachineFiniteSupportPatch` inputs of `machine_lic_iff_of_finiteSupportPerturbation` internally. Its one residual hypothesis, `Recognizable`, is a condition on the *syntax* of the finitely many moved sentences, not on any market: representation residue standing for two `Complexity.FP` primitives this toolkit lacks (integer square root, a structured-payload parser), both proved necessary rather than convenient. `machine_lic_iff_twoPoint` makes it non-vacuous and `machineLogicalInductor_liaPerturbed` makes it informative — applied to `LIA` with one price moved, it derives a machine logical inductor no construction here produces. Deliberately **not** canonical: the fuel-class carriers `lic_iff_of_finitePerturbation` and `lic_iff_of_finiteSupportPerturbation`, whose `EfficientPrefixPatch`/`FiniteSupportPatch` hypotheses are *uninhabited* at the `dd:fuel` inverse-operation ceiling, and `machine_lic_iff_of_finiteSupportPerturbation`, which the corrected theorem supersedes. They remain axiom-checked internals |
| thm:incons | exact | instantiated | **What the paper asserts** (tex:1893-1903): for an **e.c. sequence of recursively axiomatizable inconsistent theories** `⟨Θ′⟩`, `ℙₙ(⌜⌜Θ′ₙ⌝ is inconsistent⌝) ≈ₙ 1` and hence `ℙₙ(⌜⌜Θ′ₙ⌝ is consistent⌝) ≈ₙ 0`, those two sentences being the universal generalization of `Con(Θ′)(ν)` and *its negation* (tex:1855-1866). **What the Lean theorem proves:** the same, at the same generality. Signature: `lic_disbelief_inconsistent_theories_unconditional (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] (m : ℕ → Nat.Partrec.Code) (hm : DigitMachineCodes m) (hinc : ∀ n, ¬Entailment.Consistent (theoryOf (m n))) : ((fun n => liaHistory (paperDP T) n ((representedInconsistentTheoryClaims T m hm).inconsistencySentence n)) ≈ₙ fun _ => 1) ∧ ((fun n => liaHistory (paperDP T) n ((representedInconsistentTheoryClaims T m hm).consistencySentence n)) ≈ₙ fun _ => 0)`. Both paper conjuncts are concluded. The premises are the paper's own two and no others: `hm` is `def:ec` on the *naming* of the theory sequence (tex:1905 “efficiently named”; tex:1931 “write out the source code specifying `mₙ` … the runtime of an individual `mₙ` is immaterial”), stated at `DigitMachineCodes`, the standing write-out class the halting lane already uses for machines; `hinc` is the paper's inconsistency premise, stated at the day's *theory* itself. `Θ′ₙ = theoryOf (mₙ)` is an arbitrary recursively axiomatized theory: freestanding (no base theory), unrelated to the market's `T`, carrying no `Δ₁` hypothesis of its own, and possibly **infinitely axiomatized**. **The deduction-family charge is RETIRED (tranche 10), not paraphrased differently.** The previous rendering restricted the theory sequence to `Θ′ₙ = Θ₀ ∪ {σₙ}` over a fixed `Δ₁` base, because Foundation's `Derivation T` takes `T` as a *meta* parameter and there is no uniform-in-theory-code derivability predicate to represent. **The 9b obstruction still stands verbatim; this rendering sidesteps it rather than contradicting it.** It never forms an internal uniform derivability predicate. It quantifies over coded machines *externally*, at `V := ℕ`, and buys the uniformity from **compactness**: inconsistency is always witnessed by finitely many axioms (Foundation's proof object carries its own axiom list, so `exists_inconsistent_list` is `rcases` and no induction), a finite list of *written* axioms splices into one written conjunction at token level (`combineSourceNats`, `Construction/Witnesses/SourceWindow.lean`) — **gated per entry** (R11), so that a window slot contributes only a number that is literally the name of its own decoded run *and* whose run is the complete emitted run of one `ArithSource 0` compiling to a sentence (`AdmissibleName`, applied by `gateName`, the completeness test run by the recognizer `sourceRun` of `Construction/Witnesses/SourceRecognizer.lean`, which tracks binder depth and rejects the free-variable tag); anything else is replaced by the inert `⊤` — and refuting that conjunction is a question of **pure logic**. So the represented predicate, `MachineTheoryInconsistent z := ∃ w, ProvableCode (∅ : ArithmeticTheory) (negWindowCode z w)`, runs over the **empty theory** (`Theory.Δ₁.empty`) and mentions no base theory at all. It is r.e. because its matrix is decidable (`proofPacked_computable ∅`, from `Proof` being `𝚫₁`), via `Partrec.rfind`/`Partrec.dom_re` — Mathlib has no r.e.-projection lemma and none is used. **Charge (ii), the over-strength `def:ec` premise, was already retired in tranche 9-pre** (`hσ : BigDigits (deductionFamilyArg σ)` metered a formula's Gödel code). It does not return in any form: what the day-`n` sentence writes out is `binNumeral ((m n).sourceNat)`, the machine's own tag stream read base-16, whose base-4 digit count is linear in the machine's written source. Nothing about the day's axioms is metered — they are produced *inside* the machine and the spliced window is parsed *inside* the represented predicate, where the paper asks only for recursive enumerability. **No symbol measure is in play here.** Unlike `thm:pac`/`thm:pazfc`, this node's sentence is the *unbounded* existential over proofs (tex:1863-1866), so nothing is metered and §4.10's counting convention `dd:symbolcount` does not arise. **Anti-extensionality (R5-F08 discipline) — now unconditional.** `inconsistencySchema := codeOfREPred MachineTheoryInconsistent` is one universal schema for the whole theorem, with the day's data written in as `binNumeral (machineArg m n)`. `inconsistencySchema_mentions_zero` is proved with **no hypothesis at all**, where the deduction-family version needed `Entailment.Consistent Θ₀`: the predicate is non-constant outright, since the machine that keeps writing `⊥` presents an inconsistent theory (`not_consistent_theoryOf_falsumMachine`) and the machine that never writes presents the empty one (`not_machineTheoryInconsistent_of_diverges`, resting on `consistent_empty`). `inconsistencyArgClaimSentence_ne_of_arg_ne` is therefore unconditional too. Representing “the theory is inconsistent” directly would have been the trap: under `hinc` that predicate is constantly `True`. **Non-vacuity is discharged by the construction, at two witnesses the old rendering could not state.** (i) `thm_incons_applied_deep`: `mₙ = dayMachine (comp deepSourceCode left) n`, whose day-`n` theory is the single axiom `(∀x. A(x) ⟺ ⋯ ⟺ A(x)) ∧ ⊥` — `5n + 7` symbols as the paper writes it, `≥ 2^n` nodes in Foundation's normal form (`two_pow_le_encode_iffChain`), Gödel code doubly exponential in that — while the *machine's* source is `O(n)` symbols, so this is the witness that exercises the metering gap. `inconsistencyArgClaimSentence_deep_ne` separates the claim sentences of every pair of distinct days. (ii) `thm_incons_applied_infinite`: `mₙ = dayMachine deepSourceCode n` writes a *different* axiom on every input, so `theoryOf (mₙ)` is **infinite** (`infinite_theoryOf_infiniteDayMachine`, via `deepInconsistentAxiom_injective` ← `iffChain_injective`) — genuinely recursively axiomatized rather than finitely axiomatized, which is what the paper's own examples `𝗣𝗔` (tex:1859) and `𝗭𝗙𝗖` (tex:1889) are, and which a deduction family adjoining one sentence can never be. Both are fully applied with nothing left to the caller, `def:ec` discharged by `digitMachineCodes_dayMachine`. **The sentence families collapsed to one.** `InconsistentTheoryClaims` is `inconsistencySentence inconsistency_poly inconsistency_provable`, with `InconsistentTheoryClaims.consistencySentence R n := ∼R.inconsistencySentence n` — the paper's own shape (tex:1863-1866). **Residuals.** Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Both are on the **market's** theory; `[Entailment.Consistent T]` beside them is the paper's own assumption on `Θ`. Nothing is charged against this row. The presentation convention `dd:machinetheory` (what it means for a machine to *present* a theory) is a **convention, not a modelling substitution** — the same status `dd:symbolcount` has — and is disclosed under *Global model disclosure* above and in the glossary. **The window is now sound against that convention, and the sentence is an equivalence.** Ungated, `MachineTheoryInconsistent` was strictly *broader* than the convention's inconsistency claim, holding of machines that present the **empty** theory, by three independent leaks: prefix truncation (`tokensOfNat` reads digits up to the first sentinel, so a number carrying digits at or above it decodes like a shorter one), splice-across-entries (`combineTokens` is list surgery, so two *incomplete* outputs concatenate into one complete refutable run), and free variables (a genuine `ArithSource 0` may compile to a formula with free variables, which `∅` refutes without its being a sentence of any theory — a leak no “parses completely” test would have caught). The per-entry gate closes all three, and `machineTheoryInconsistent_iff` now proves `MachineTheoryInconsistent m.sourceNat ↔ ¬Entailment.Consistent (theoryOf m)`: the day-`n` sentence says exactly what `hinc` assumes, in both directions. **The surjectivity justification is scoped, not assumed.** What is proved is the per-sentence half — `theoryOf_const_ofNNF`, `theoryOf (Code.const ⌜written σ⌝) = {σ}`, every one-axiom theory presented exactly, `ArithSource.ofNNF` writing every sentence. The *uniform* half — one machine enumerating the names of any given r.e. set of sentences — is **not formalized**: it would need `encodeArithmeticFormulaSymbols` certified primitive recursive at the level of Foundation formula codes, and the endpoint does not consume it, `hinc` being stated at the caller's own machine. Both `machineTheoryInconsistent_iff` and `theoryOf_const_ofNNF` carry `Paper node: thm:incons`. **What died, precisely:** the deduction-family paraphrase; the binders `T'`, `[T'.Δ₁]`, `σ`, `s`, `hs : PolyArithmeticSourceSeq s`, `hcompile`; the consistency hypothesis on the anti-extensionality lemma; the declarations `deductionFamilyArg`, `falsumSource_polyArithmeticSourceSeq`, `provableCode_negSource_re`, `deepInconsistentSource_sourceNat_ne`, `deepInconsistentAxiom_inconsistent`, `provableCode_neg_iff_not_consistent_adjoin`, `not_provableCode_quote_falsum`, and the one-line `⊥`-adjunction `example`. *Superseded 2026-08-31 (T10): the previous cell recorded charge (i), the deduction-family paraphrase, as standing on a verified obstruction with only an “optional upstream middle rendering” available. That reading is withdrawn — the obstruction was real but not binding, because compactness supplies the finite window from the paper's own premise instead of restricting the theories to finite ones.* *Superseded 2026-08-31 (R11): the pre-gate window admitted non-names and incomplete runs; three leak mechanisms closed by the source recognizer.* |
| thm:lc | exact | universal | the measure `μ` plays the paper's `Pr`: a genuine probability measure on completed worlds, constructed rather than assumed, agreeing with `limitingBelief` on every sentence event and (a.e.) supported on worlds consistent with `Γ`. All three paper clauses in one theorem, over `[IsLogicalInductor]` plus `hworld` |
| thm:lex | exact | universal | propositional rendering over `[IsLogicalInductor]`; the exclusive-exhaustive premise is the completed-world payout-sum rendering, disclosed at the site |
| thm:li | strengthened | instantiated | sole hypothesis is a computable deductive process. The conclusion mirrors `def:belseq` — one `Nat.Partrec.Code` emits each day's finite association list, supports are finite, quotes are rational in `[0,1]` — *and* concludes `IsMachineLogicalInductor`, the paper's own quantifier. Strengthened in the `def:belseq` emission conjunct relative to the bare existence forms |
| thm:lia | exact | instantiated | the central construction, kernel-clean; the sole premise is a computable deductive process. `LIA_isMachineLogicalInductor` leads because it concludes the paper's own quantifier — `LIA_is_logical_inductor` is literally its `toIsLogicalInductor` projection, and showing only the projection contradicted the sibling node `thm:li`, which already shows the machine class |
| thm:loe | exact | universal | the paper's varying-sequence form: `a b : ℕ → ℚ` and `X Y Z : ℕ → LUV`. `Θ ⊢ Zₙ = aₙXₙ + bₙYₙ` is `DeterminedViaTheory` on the linearity combination (= paper `def:affthmval`), and `WorldValued` is `def:luv`'s own fact. The fixed sibling `lic_linearity_of_expectation` quantifies its hypothesis over *stage*-plausible worlds — a strictly stronger premise, correctly internal. |
| thm:loops | exact | instantiated | **Soundness-free, and the sentence names the machine.** Dual of `thm:halts`, over the same single market `paperDP T`, the same instances `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]` — no soundness, no `𝗜𝚺₁`, no `RepresentsComputations` — and the same `representedHaltingClaims` family, so the claim-sentence account, the `def:ec` accounting and the anti-vacuity witness of the `thm:halts` row apply verbatim, including the applied client at `Nat.Partrec.Code.nest`. **`hloops` is the paper's own premise in literal form:** `∀ n, T ⊢ ∼(haltingArgClaimInstance machines inputs n)` — object-level `T`-refutability of exactly the sentence whose atom the conclusion is about, with the machine named in it. It is not a deductive-process emission surrogate, and it is not stated at the vacuous `∃⁰` wrapper, whose invisibility is separately proved (`provable_neg_schemaArgClaim_iff`). The paper assumes the same thing outright (`app:loops`). **Disclosure, type `(c)`, on the *witness* and not on the statement: `hloops` is inhabited only by axiom fiat.** This is a non-vacuity note, not a charge against the row — the hypothesis itself is the paper's own premise in literal form, as the previous sentence records, and what is disclosed here is the quality of the only theory exhibited that satisfies it. `loopsTheory = insert (∼haltingArgClaimInstance (fun _ => neverHaltMachine) (fun _ => 0) 0) 𝗜𝚺₁` is `Δ₁`, consistent, Σ₁-sound and has every axiom *true* in `ℕ` (`models_loopsWitnessSentence`, through `haltingArgClaimInstance_true_iff`), and the machine it speaks of provably never halts, so the endpoint's `≈ₙ 0` conclusion is the semantically correct one — but `loopsTheory_refutes` is `Entailment.by_axm`, not arithmetic reasoning. The obstruction is representational and is untouched by this repair: `universalHaltingSchema` is `codeOfREPred`, picked by `Classical.epsilon`, so its shape is unreachable from the API and the only bridges Foundation gives to `T ⊢ …` are positive (`re_complete`, `re_complete_mp`); no `T` can be *shown* to refute a particular false instance. What is **not** claimed is that no natural theory could: `∼σ` is a true Π₁ sentence and `𝗜𝚺₁` would refute a natural arithmetization of this non-halting fact by induction. The disclosure at `loopsTheory` names the two honest strengthenings — a Π₁-reflection hypothesis on `T`, or a hand-rolled Δ₀/Σ₁ halting formula carrying its own representability lemma. One simplification came with the repair: the witness axiom is a *single* sentence again rather than the `∀`-closure `∀⁰(∼loopsWitnessSchema)` the day-indexed rendering needed, and `loopsTheory_refutes` is plain `by_axm` with no specialization step — because the witness *machine family* is constant, not because the day has left the claim. `thm_loops_applied_at_loopsTheory` applies the endpoint with every instance and every hypothesis discharged. **Nothing remains charged on theory strength (settled 2026-08-30).** This row used to carry a residual `[𝗜𝚺₁ ⪯ Θ]`, on the ground that `paperTheoryDP` is proved computable through Foundation's *internal* provability predicate (`provable_instances_re`, `ComputationDP.lean`). Tranche 7 deleted that binder: with `QuotationTheoryPresentation.theory_sigmaOne` gone, each site takes the weaker instance its proof actually spends, and the census over the 105 canonical endpoints — elaborated `#check`, not docstrings — finds `𝗜𝚺₁ ⪯ ·` in exactly three signatures, none of them this one. What the endpoint asks for now is the paper's own standing assumption on Θ. Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. *Superseded 2026-08-30 (R5-F08/F09).* Previously `hloops` was stated at the day instance of the extensional schema, `∀ n, T ⊢ ∼((haltingSchema machines inputs)/[↑n])`, which under `thm:halts`'s companion hypothesis named no machine; see the supersession note on that row |
| thm:lp | strengthened | instantiated | the paradoxical sequence is **constructed** (`paperDiagonalQuoteCode`, by Gödel fixed point from the market computation) where the paper merely posits one, and the whole result is closed over `LIA`. **Width premises: gone, not argued away.** The signature is now `theorem lic_paradox_resistance_ofDiagonal_unconditional [𝗜𝚺₁ ⪯ T] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)` and nothing else: the four `width` binders (the sequence, its positivity, its vanishing, and its code certificate) were removed in the final fix-wave and the tolerance is discharged **internally** at `width n := ((2^n : ℕ) : ℚ)⁻¹`, certified by the write-out `digitRatCodes_two_pow_inv`. Earlier editions of this row argued that the premises were harmless — universally quantified, inhabited, absent from the conclusion (`(fun n => ℙₙ(χᵖₙ)) ≈ₙ fun _ => p`), hence eliminable by instantiation under clause (3) of the disclosure section's test. That argument was correct and is now executed rather than argued, so the qualification comes off. The paper states no `δ` at this node, and no metering note is owed here: `ParadoxResistanceQuote` carries no whole-value field. The conditional twin `lic_paradox_resistance_ofDiagonal` (`QuotationAffine.lean`) deliberately keeps its width parameters — they are consumed by its proof, through `ParadoxResistanceQuote`'s `width`/`width_pos`/`width_tendsto_zero`, and it is the parametric `_ofDiagonal` rung over an arbitrary market, which is where a caller-supplied tolerance belongs. **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` **survives here** — unlike at the seven closed quotation endpoints, where deleting `QuotationTheoryPresentation.theory_sigmaOne` in tranche 7 removed it — because this endpoint spends `𝗜𝚺₁` at a step of its own, next. **Residual disclosure:** this endpoint is one of the three that still carry `[𝗜𝚺₁ ⪯ T]`, because its diagonal is Foundation's `parameterized_diagonal₁`, stated over `𝗜𝚺₁`. By the 2026-08-30 ruling that is where the substrate's Gödel fixed point lives — representation infrastructure, charged once globally — and not a theory-strength assumption levied against the row. (It prints `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] [𝗜𝚺₁ ⪯ T]`; the pair is redundant, since `𝗜𝚺₁ ⪯ T` implies `𝗣𝗔⁻ ⪯ T` by instance, but not removable — the proof term references the section's `𝗣𝗔⁻` instance and Lean rejects `omit` on a referenced section variable. Read it as charging `𝗜𝚺₁`, not as two assumptions.) With the theory premise no longer charged, what is left is the strengthening: the paradoxical sequence the paper merely posits is **constructed** here, which is why this row is `strengthened` rather than `exact` |
| thm:nd | strengthened | universal | the conclusion `∃ ε > 0, ∀ᶠ n, ε ≤ ℙₙ(φ)` is stronger than the paper's limit claim; the literal `ℙ∞` forms `lic_limit_pos`/`lic_limit_lt_one` are corollaries needing a `ConvergesTo` input and are internal. The plausibility premise is the paper's own, made stagewise |
| thm:ob | exact | universal | paper-strength bounds at genuine universal prefix complexity `κ_U`, with `prefixWeight κ φ = 1/2^(κ φ)` literally the paper's `2^(−κ)`. Invariance is proved (Kraft, the negation compiler, the invariance theorem); presentation and threshold emission are constructed, so only `[IsLogicalInductor]` and stagewise plausibility survive. Both halves in one statement. No `_unconditional` Occam endpoint exists anywhere, so nothing stronger is available |
| thm:obu | exact | universal | `_ofCE` takes the paper's own premises (tex:1540-1546): a c.e. source — `CEEnumeration`, a program whose dovetailed run returns `⌜source i⌝` at every index, with no clock — plus stagewise joint consistency of `Γ ∪ φ̄`, and concludes the paper's `ε` and `ℙ∞`. The padded efficient repetition the paper builds *inside* its proof (tex:5651-5656) is constructed by `EfficientRepeatedEnumeration.ofCE`, so `lic_uniform_nonDogmatism`, which assumes that structure directly, is the strictly stronger premise and sits second |
| thm:pac | exact | instantiated | **Status: `exact`.** The §4.10 finite search is metered as the paper meters it, in **symbols**; the only global note reaching this row is the counting convention `dd:symbolcount`, which is a convention rather than a substitution and is charged against nothing. **What the paper asserts** (tex:1869-1875): for any computable `f`, `ℙₙ(Con(Θ)(⌜⌜f⌝(⌜n⌝)⌝)) ≈ₙ 1`, with `Con(Θ′)(ν)` the one-free-variable formula “there is no proof of `⊥` from `⌜Θ′⌝` with `ν` or fewer symbols” (tex:1855-1866). **What the Lean theorem now proves:** `lic_belief_finitistic_consistency_unconditional T horizons hh` prices exactly that family. Its day-`n` sentence is `conClaimSentence (conGamma T T hh) n` — the value-`0` sentence `∀ν (γ(t, ν) ⟺ ν = 0̄)` of the formula `γ` that `RepresentsComputations` returns for the **universal bounded-provability decider** `conRunValue T f` (`Framework/BoundedConsistency.lean`), at the compact argument `binNumeral ⟨⌜(⊥ : ArithmeticSentence)⌝, n⟩`. So the sentence names `⊥` and the day, the `γ` names the theory (the decider's extension is `T`'s bounded theorems), and one `γ` serves every day of a horizon, which is the paper's `⌜f⌝`. **This node is the diagonal of a two-theory family:** `conGamma`, `conGamma_spec`, `exists_reprAll_conRunValue` and `representedConClaims` all take a second theory parameter, and `thm:pac` is literally the instantiation `Θ′ = Θ` — `representedConClaims T T (RepresentsComputations.consistent T) hh` — of the parametric family that `thm:pazfc` runs at a genuinely stronger `Θ′`; its consistency argument is *derived* rather than assumed, the explicit `hcons` appearing only where the paper itself assumes it, on `Θ′`. The horizon is an arbitrary computable function named by its program (`ComputableHorizon`) and evaluated *inside* the represented decider, so `Ack` is admissible; the in-file `example` runs the theorem at `Θ = 𝗜𝚺₁` with horizon `fun n => ack n n`, every instance discharged. **The truth premise is proved, not assumed:** the endpoint carries no `hconsistent` and no `[Entailment.Consistent T]` — consistency comes from `RepresentsComputations.consistent`, and `conWithin_of_consistent` derives the truth of every day's claim from it through `Bootstrapping.provable_of_standard_proof`. The former schematic `consistentWithin : ℕ → Prop` / `BoundedComputation` carrier is gone from this node. **Non-collapse is a theorem, not a side condition.** The day sentences are pairwise distinct because `γ` genuinely mentions its argument: `mentions_zero_of_repr_ne` (`Framework/RepresentsComputations.lean`, from `Semiformula.rew_eq_of_not_mentions`) derives `γ.Mentions 0` from the representation spec alone whenever the represented decider is non-constant, and the Con lane discharges it at `conGamma_mentions_zero`, with two usable sufficient conditions — `conGamma_mentions_zero_of_bProv` (some sentence code has a derivation under some day's horizon) and `conGamma_mentions_zero_of_horizon_unbounded` (the horizon is unbounded, so some derivation code eventually fits) — and fully at the paper's own illustration by `conGamma_mentions_zero_ackermann`. The only case where collapse remains possible is degenerate and disclosed at the endpoint: at an eventually bounded horizon (in the limit, constantly `0`) the decider is constant, and there a `γ` ignoring its argument does represent it. *(Corrected R7: this was formerly recorded as an undischargeable occurrence side condition with a permanent counterexample; the counterexample survives only in that degenerate scope.)* **The metering is the paper's own.** The day-`n` search is `BProv T ⌜(⊥ : ArithmeticSentence)⌝ k := ∃ d, Proof T d ⌜⊥⌝ ∧ dSize d ≤ k` — “`ν` or fewer symbols”, with the bound **inclusive**, as the paper's is (tex:1855-1866). `dSize` (`Framework/DerivationSize.lean`) is a total symbol count on Foundation's internal derivation codes, tied to Foundation's own constructors by equation (`dSize_axL`, `dSize_cutRule`, …), and the converse bound `le_G_dSize : d ≤ G (dSize d)` is what keeps the symbol-bounded search finite and decidable in both polarities. The Gödel-number metering formerly disclosed here as `dd:proofcode` was **retired in tranche 9a**, with no change to this endpoint's statement shape; what remains is the counting convention `dd:symbolcount`, recorded globally above — the paper fixes neither encoding nor alphabet, ours charges each index at its binary digit length plus one marker token (`idxLen n = Nat.size n + 1`, which is what makes the measure finite-fibred), it can only over-count, and the truth of every instance is independent of it (`conWithin_of_consistent`; the convention affects only which horizons discharge the non-degeneracy side conditions). **Residual disclosures.** Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Nothing else. *Superseded and retired 2026-08-30 (T8/iii): the previous rendering priced the represented claim of an arbitrary decidable `consistentWithin` presented by a `BoundedComputation`, with the finitistic consistency of `T` supplied by the caller's `hconsistent`. That carrier (`lic_belief_finitistic_consistency_ofComputation`) and the `BoundedComputation` structure under it have been deleted; this node now has exactly one carrier.* |
| thm:pazfc | exact | instantiated | **Status: `exact`.** The §4.10 finite search is metered as the paper meters it, in **symbols**; the only global note reaching this row is the counting convention `dd:symbolcount`, which is a convention rather than a substitution and is charged against nothing. **What the paper asserts** (tex:1881-1886): let `Θ′` be a stronger consistent recursively axiomatizable theory — the paper's examples are `𝗣𝗔 + Con(𝗣𝗔)` and `ZFC`. Then a logical inductor over `Θ` satisfies `ℙₙ(Con(Θ′)(⌜⌜f⌝(⌜n⌝)⌝)) ≈ₙ 1` for every computable `f`: the inductor comes to believe every finite consistency statement about a theory it cannot prove consistent. **What the Lean theorem now proves:** `lic_belief_stronger_theory_consistency_unconditional T T' hcons horizons hh` prices exactly that family. The market is `Θ`'s — the single market `paperDP T`, whose process is the union of `paperTheoryDP T` (which enumerates the propositions `T` proves) with the literal stream `theoremDP T`, and the inductor `liaHistory (paperDP T)` is trained on `Θ`'s own commitments and on nothing about `Θ′`. The day-`n` sentence is `conClaimSentence (conGamma T T' hh) n`, the value-`0` sentence `∀ν (γ(t, ν) ⟺ ν = 0̄)` of the **`T`-formula** `γ` that `RepresentsComputations T` returns for the universal bounded-provability decider of the **second theory**, `conRunValue T' f` (`Framework/BoundedConsistency.lean`), at the compact argument `binNumeral ⟨⌜(⊥ : ArithmeticSentence)⌝, n⟩`. The two theories are genuinely distinct parameters: `T'` supplies the derivations being metered, `T` the derivations being enumerated. One `γ` serves every day of a horizon (the paper's `⌜f⌝`); the horizon is an arbitrary computable function named by its program (`ComputableHorizon`) and evaluated *inside* the represented decider, so `Ack` is admissible. **The paper's own illustration is the in-file `example`:** `T = 𝗜𝚺₁`, `T' = 𝗣𝗔`, horizon `fun n => ack n n` — a theory that does not prove `Con(𝗣𝗔)`, whose inductor's belief in `Con(𝗣𝗔)(⌜Ack(n,n)⌝)` nevertheless converges to `1`. Every instance of that example is discharged (`𝗜𝚺₁`'s three from `Construction/Witnesses/R0Representability.lean`, `𝗣𝗔.Δ₁` and `Entailment.Consistent 𝗣𝗔` from Foundation), and it is axiom-clean. **The truth premise is the paper's own premise, not a stub:** `hcons : Entailment.Consistent T'` is exactly “let `Θ′` be consistent”, and `conWithin_of_consistent` derives the truth of every day's claim from it alone, through `Bootstrapping.provable_of_standard_proof`. There is no soundness hypothesis anywhere on the endpoint, no `hworld`, no presentation argument, and the former schematic `strongerConsistentWithin : ℕ → Prop` / `BoundedComputation` carrier is gone from this node. **No hypothesis relating `Θ` and `Θ′` is stated, and the paper states none either.** tex:1881-1886 assumes of `Θ′` only that it is a stronger consistent recursively axiomatizable theory (its examples: `𝗣𝗔 + Con(𝗣𝗔)`, `ZFC`); there is **no** `Θ ⊆ Θ′` hypothesis anywhere in the paper's statement, so the Lean statement **matches** the paper's hypotheses rather than generalizing them. Nor would a containment be usable: `conRunValue T' f` is total computable for any `T'` with a Δ₁ axiom set (`conRunValue_computable`, a fact about `T'`'s derivation codes); `RepresentsComputations T` then supplies a `T`-formula representing it, by the paper's own standing premise on `Θ`; and the truth of the day-`n` claim is `conWithin_of_consistent T' hcons`, a fact about `T'`. What makes the theorem *interesting* is the informal case where `Θ` cannot prove `Con(Θ′)`, and the `𝗜𝚺₁`/`𝗣𝗔` witness carries that concretely. *(Corrected R7: earlier revisions of this row, of the README, of the `LI_READING` note and of the endpoint docstring called the Lean statement “more general than the paper” for omitting a `Θ ⊆ Θ′` premise the paper never had; every such passage has been deleted, in the `.lean` source too. This removes an unearned generality claim, not a charge — the row's status is unchanged.)* **Non-collapse is a theorem, not a side condition.** The day sentences are pairwise distinct because `γ` genuinely mentions its argument: `mentions_zero_of_repr_ne` (`Framework/RepresentsComputations.lean`, from `Semiformula.rew_eq_of_not_mentions`) derives `γ.Mentions 0` from the representation spec alone whenever the represented decider is non-constant, and the Con lane discharges it at `conGamma_mentions_zero`, with two usable sufficient conditions — `conGamma_mentions_zero_of_bProv` (some sentence code has a derivation under some day's horizon) and `conGamma_mentions_zero_of_horizon_unbounded` (the horizon is unbounded, so some derivation code eventually fits) — and fully at the paper's own illustration by `conGamma_mentions_zero_ackermann`. The only case where collapse remains possible is degenerate and disclosed at the endpoint: at an eventually bounded horizon (in the limit, constantly `0`) the decider is constant, and there a `γ` ignoring its argument does represent it. *(Corrected R7: this was formerly recorded as an undischargeable occurrence side condition with a permanent counterexample; the counterexample survives only in that degenerate scope.)* **The metering is the paper's own.** The day-`n` search is `BProv T ⌜(⊥ : ArithmeticSentence)⌝ k := ∃ d, Proof T d ⌜⊥⌝ ∧ dSize d ≤ k` — “`ν` or fewer symbols”, with the bound **inclusive**, as the paper's is (tex:1855-1866). `dSize` (`Framework/DerivationSize.lean`) is a total symbol count on Foundation's internal derivation codes, tied to Foundation's own constructors by equation (`dSize_axL`, `dSize_cutRule`, …), and the converse bound `le_G_dSize : d ≤ G (dSize d)` is what keeps the symbol-bounded search finite and decidable in both polarities. The Gödel-number metering formerly disclosed here as `dd:proofcode` was **retired in tranche 9a**, with no change to this endpoint's statement shape; what remains is the counting convention `dd:symbolcount`, recorded globally above — the paper fixes neither encoding nor alphabet, ours charges each index at its binary digit length plus one marker token (`idxLen n = Nat.size n + 1`, which is what makes the measure finite-fibred), it can only over-count, and the truth of every instance is independent of it (`conWithin_of_consistent`; the convention affects only which horizons discharge the non-degeneracy side conditions). **Residual disclosures.** Hypotheses beyond the paper's stated premises: only the two globally charged binders — `[T.Δ₁]`, here on both `T` and `T'`, and `[𝗣𝗔⁻ ⪯ T]` — see *Arithmetic-theory hypotheses* above. Nothing else. *The superseded `BoundedComputation` lane — `lic_belief_stronger_theory_consistency`, its `_ofComputation` instance and the structure they consumed — was deleted in T8/iii; this node now has exactly one carrier, `lic_belief_stronger_theory_consistency_unconditional`.* |
| thm:peraffkno | exact | universal | analytic capstone over `[IsLogicalInductor]`; sole carrier, hypotheses are the paper's |
| thm:perexpkno | exact | universal | same premise set as `thm:expcoh` — the `def:blcp` bounded sequence, `S : LUVCombinationSyntax`, `WorldValued` — and the same repair: the `ConvergencePresentation` argument is gone from the signature rather than merely derivable. |
| thm:perkno | exact | universal | over `[IsLogicalInductor]`, sole carrier, and the conclusion is a **three**-way conjunction matching the paper's three displayed clauses (`≈`, `≲` and `≳` against the future sup/inf) clause for clause; `limitingBelief P (φ n)` is `ℙ∞(φₙ)`. `φ` carries `BigSentenceCodes`, the write-out class — widened from the value-bounded `RpnSentenceCodes` by the machine/input migration, since `lic_persistence_of_knowledge` routes `φ` through `sentenceMinusProbability_polySequence`. This is `def:ec`'s own charge and costs nothing here; the widening is a strengthening on an already-`exact` row, admitting `φ` families with exponentially large codes. The second data hypothesis, on the paper's "e.c. sequence of rational-number probabilities" (tex:1105-1107), **was** the row's sole qualification and is now discharged: `hp` is `DigitRatCodes p`, and `sentenceMinusProbability_polySequence` emits `p` with `serialize_const_write` in place of `serialize_const_comp`. Sequences approaching their limits faster than polynomially — `pₙ = 1 − 2^(−n)`, which the paper admits and the whole-value class excluded — are now admissible. `p` is in both hypothesis and conclusion, so this had to be widened rather than dropped |
| thm:prand | corrected | universal | clock-free varied-frequency form; the target rationals enter as a market-generable feature (`def:ece`), as the paper requires, and the two-sided `≈ₙ` headline is exact. `def:ece`'s emitter is write-out metered, so `pₙ` may be value-exponential and polynomially writable — `pₙ = 1 − 2⁻ⁿ` included (`pGenerableRat_two_pow_inv`); this was a silent narrowing until `polyTok` was widened from `RpnSpliceStream` to `BigSpliceStream`. **Erratum PE5:** the centering of the one-sided notions is *inverted* relative to the printed `def:seqprand`, which displays the weighted average of `(pᵢ − ThmInd(φᵢ))` and calls its `≳ₙ` form "varied pseudorandom *above*". With the paper's centering, `def:seqprand`'s `≳ₙ` and `thm:prand`'s `ℙₙ(φₙ) ≳ₙ pₙ` point in opposite directions; the repo centers the other way (`VariedPseudorandomAbove truth p := PseudorandomAbove (truth − p)`), which is what the exploiting-trader argument needs and what makes the paper's advertised conclusion come out right. The `≈ₙ` form is unaffected, being sign-symmetric |
| thm:prandaff | exact | universal | clock-free: the patient settlement clock is constructed from the inductor, leaving exactly the paper's bounded-combination, determination and pseudorandomness premises. The printed display is `≳ₙ`, "and similarly for `≈ₙ` and `≲ₙ`", so `prandaff_above` leads; the two-sided `prandaff` sits last because its hypothesis is the conjunction of the two one-sided ones and its body is `asympEq_iff_asympLE_asympGE` over them |
| thm:prandexp | exact | universal | retains `WorldValued` (paper `def:luv`) and `DeterminedViaTheory` (paper `def:affthmval`, tex:1807); the clock is constructed. The paper prints only the `≳` direction, so `prandexp` leads and the `_below`/`_eq` forms follow. |
| thm:provind | exact | universal | both halves of the paper's statement in one theorem, with `BigSentenceCodes` — the write-out class — on both sequences. Those binders were `RpnSentenceCodes`, which additionally bounds every emitted token's *value* by a polynomial in the day; widening them admits sentence families whose Gödel codes grow exponentially while their symbol count stays polynomial, which is what tex:753-757's e.c. actually permits. A widened hypothesis is a strengthening, and the row stays `exact` because the narrower class was already inside the paper's; `lic_provind`'s conclusion is unchanged. "Sequence of theorems" becomes `∀ n, ∃ k, φ n ∈ DP.D k` — each `φₙ` eventually appears in the process — and dually for the disprovable `ψₙ`, which is the paper's eventual-deducibility premise |
| thm:recunbiasedaff | exact | universal | maturity constructed internally; clock-free, and no verifier premise remains |
| thm:recurringunbiasedness | exact | universal | same, over the sentence-affine family. Despite the namespace this is genuinely sentence-level — `φ` is lifted by `sentenceAffine` — not an affine substitution |
| thm:recurringunbiasednessexp | corrected | universal | same premises as `thm:prandexp`, both the paper's own. **Erratum PE2:** the printed statement (tex:1812-1820) is garbled — it carries a spurious "support of `⟨w⟩ ⊆ image of f`" clause referring to an `f` the statement never introduces, a clause that belongs to `thm:wubexp` and is missing there. The affine twins `thm:wubaff`/`thm:prandexp` prove the intended placement. The Lean statement is the repair, and says so at the declaration: no deferral function, no support clause, concluding `HasLimitPoint 0` — the mirror half of `thm:wubexp`'s, where the un-printed clause is carried |
| thm:ref | exact | instantiated | unconditional over `LIA` at `BigSentenceCodes`, the write-out class, with the interval quote constructed from the market's exact rational quote. Its hypotheses are the paper's (tex:1969-1981) up to one metering gap: ℙ-generable interval bounds via their market-generated feature presentations, an e.c. sentence sequence, the vanishing width, and the range side conditions. Two `PolyRatCodes` hypotheses formerly stood on `ā` and `b̄`; they were **redundant** — consumed only as `.computable`, which `PGenerableRat.computable` supplies from the `MarketComputation` already in scope, the route `thm:st` already took — and have been removed. The third hypothesis, on the paper's "any e.c. sequence of positive rationals `⟨δ⟩ → 0`", **was** the row's sole qualification and is now discharged: `IntrospectionIntervalQuote.inverse_width_codes` is `DigitRatCodes (1/δ)`, the write-out class, in place of the whole-value `PolyRatCodes`. The paper's `→ 0` states no rate and the write-out class demands none: `δₙ = 2^(−n)` — whose reciprocal `2ⁿ` is refuted for the old class by `not_polyFueled_two_pow` and admitted for the new one by `bigDigits_two_pow` — is now an admissible width. `δ` still reaches the conclusion, so this could not be eliminated by dropping the hypothesis; it had to be widened. The ℙ-generable bounds `ā`, `b̄` were widened on the same footing in a later pass: `GeneratedRatFeature.polyTok` is now `BigSpliceStream` rather than `RpnSpliceStream`, so a bound whose day-`n` numeral has an exponential Gödel code is admissible feature data (`pGenerableRat_two_pow_inv`). **PE6** records the separate fact that the paper's *own proof* needs more than the paper states: `app:ref` applies `thm:affprovind` to a combination over sentences containing `⌜aₙ⌝`, `⌜bₙ⌝`, which requires those numerals efficiently writable, whereas ℙ-generability gives a feature whose value at the market is the bound. This formalization escapes that gap rather than inheriting it: the quoted sentence is a code-indexed atom (`dd:quote-code`), so its emission cost does not depend on the bounds. **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` was **deleted outright** in tranche 7, with `QuotationTheoryPresentation.theory_sigmaOne`: the endpoint had inherited it from that field and from no step of its own, and now spends only `𝗣𝗔⁻`. `lic_introspection_closed` is now at once closed over `LIA` *and* at the paper's own theory hypotheses, which is what promotes this row; the sibling `lic_introspection` stays shown as the caller-interface form, and its retained quotation interface is a disclosed representation, not a charge |
| thm:scon | strengthened | instantiated | both halves at the paper's own quantifier. The two printed forms `lic_conditioned_fixed_machine` / `lic_conditioned_growing_machine_ofProcessComputation` are universal over `[IsMachineLogicalInductor P DP]` with **no** consistency hypothesis — the degenerate branch is `isMachineLogicalInductor_of_stage_unsatisfiable` — and the growing-form `hjoint` is gone, derived by propositional compactness (`Framework/Compactness.lean`). Their premise-free instances over the constructed `LIA` take exactly the hypotheses of the fuel-class pair `lic_conditioned_{fixed,growing}_unconditional` — `(T : ArithmeticTheory) [T.Δ₁]` and the condition, no inductor hypothesis — and conclude the strictly stronger `IsMachineLogicalInductor`, discharging the base by `LIA_isMachineLogicalInductor` where the fuel forms use `LIA_is_logical_inductor`. The machine transports are `conditionedTranslation_preserves_machine` and `eventualConditionedTranslation_preserves_machine`, under the same `RpnSentenceCodes` hypothesis on the condition as the fuel counterparts; the fuel endpoints and their inhabited witnesses are unchanged beside them, so this is a strengthening, not a replacement. **Class disclosure — the condition is metered narrower than `def:ec`, and this is now the only such retention on the day-indexed surface.** `CompactConditioningProcessComputation.condition_codes` and `ConditioningPresentation.condition_codes` are `RpnSentenceCodes`, the *token-metered* class: polynomially many emitted tokens **and** a polynomial bound on each token's value. That is **not** `def:ec`'s class. `def:ec` is the write-out `BigSentenceCodes`, which bounds only how many tokens a poly-time writer emits and leaves their magnitudes free; `RpnSentenceCodes` embeds into it (`BigSentenceCodes.ofRpnSentenceCodes`) and the datum that separates them is a single atom of exponential index, admitted by the write-out class and excluded here — argued rather than carried by a strictness lemma, as the write-out class table records for this pair. Two docstrings claimed the field *was* `def:ec`'s class and have been corrected at both sites. **The retention is forced, on a line-level obstruction, not left unexplored.** `CondStep.machineSentenceBlocks_of_rpn` opens the certificate as *emission data*: it destructures the stream, obtains a clocked token schedule from `PolySegStream.clockedTokens_certificate`, and runs `TraderMachine.traderOutput`, whose digit clamp is the identity only because the stream bounds each token's value (`CondStep.mem_digitize_le_four`). A write-out stream supplies no such clock, so widening is not a statement change but a `BigSentenceCodes → CondStep.MachineSentenceBlocks` re-blocking that has to be proved in `FP`, at the scale of `CondStep.lean`'s own ~50 `_mem_FP` lemmas rather than of a lemma. Read it as a **retained representation interface, disclosed here rather than covered by the `def:ec` charge**: it restricts which conditioning data a caller may supply — token-metered rather than write-out — and leaves untouched what the row's `strengthened` status stands on, namely that the conclusion is `IsMachineLogicalInductor` at the paper's own quantifier. Every other day-indexed sentence certificate on this surface now sits at `BigSentenceCodes`. (For the *general* forms the machine/fuel swap is on both sides of a closure implication, so those pairs are incomparable; the closed pair is where domination is strict). **Σ₁-soundness: gone.** The `_unconditional` endpoints over `LIA` used to be stated under `[T.SoundOnHierarchy 𝚺 1]` and no longer are: the instance was carried purely by inheritance and has been dropped, as was `[𝗜𝚺₁ ⪯ T]` in tranche 7, leaving `[T.Δ₁]` alone (census 2026-08-30, elaborated `#check`). The universal `_ofComputation` endpoints shown beside them carry no theory premise at all and are the paper's printed statement, which is what the row's status stands on **Criterion note.** The sparing passes check (2) of *How this is charged* as well as check (1): the universal endpoint's premises are the printed ones — the two printed forms quantify over conditioning data and name no theory at all — not a stand-in for a step the paper derives from Θ, which is exactly what disqualifies the instance-free universal layer at thm:halts / thm:loops / thm:dontwait. |
| thm:simcal | exact | universal | maturity is constructed internally, and the endpoint's hypotheses are reachable from the paper's own up to one metering gap: `AffineCombination.simcal` takes `hpoly : PolySequence (sentenceAffine φ)` and `hWgen : PGenerableWeighting (calibrationIndicator φ a b δ)` as arguments, and both are *proved* here from the paper's own "`⟨φ⟩` is an e.c. sequence of decidable sentences" and "`⟨δ⟩` is an e.c. sequence of positive rationals" — by `AffineCombination.sentenceAffine_polySequence` and `calibrationIndicator_pgenerable` respectively, both shown on this card. (`calibrationIndicator_pgenerable` is exactly the fact tex:1188 asserts without proof.) They are arguments rather than a collapsed single endpoint, which is an ergonomic wart, not a strength loss: no collapsed endpoint exists. The `⟨δ⟩` half of that derivation **was** the row's sole qualification and is now the paper's class. `AffineCombination.simcal` asks only `∀ n, 0 < (δ n : ℝ)`, and the `hWgen` discharge `calibrationIndicator_pgenerable` takes `PolyPositiveWidths δ`, whose `codes` field is now `DigitRatCodes` — the write-out class, so the calibration widths may shrink at any rate, which is what tex:1193-1195 asks of an e.c. sequence of positive rationals. `δ` is in the conclusion through `calibrationIndicator φ a b δ`, so this had to be widened rather than dropped. The `⟨φ⟩` half was already clean and is now wider still: `sentenceAffine_polySequence` takes `BigSentenceCodes`, the write-out class, where it previously took the value-bounded `RpnSentenceCodes`. That is a strengthening of an already-`exact` row rather than a repair — the paper's `⟨φ⟩` is e.c. in the write-out sense, so a sentence family with exponentially large Gödel codes but polynomially many emitted symbols is now admissible data for `thm:simcal` |
| thm:st | exact | instantiated | unconditional over `LIA` with every representation obligation discharged: the `SelfTrustQuote` reflection data is constructed (`paperConfidenceQuoteCode`), the quoted product LUV is emitted as tokens rather than as a `Nat.pair` on Gödel values (`indicatorProductLUV_bigThresholdCodeSeq` emits the `⋏`-shell), and the reciprocal code is *derived* (`PolyRatCodes.inv_of_pos`). The remaining hypotheses are exactly tex:2093's four: a deferral function, an e.c. sentence sequence, an e.c. sequence of positive rationals, and a ℙ-generable rational probability sequence. `hδ` renders the third of those and is now `DigitRatCodes δ`, at both `lic_self_trust_ofRepresentation` and `lic_self_trust_closed`, so the `thm:ref` narrowing no longer recurs here: `δ` may vanish at any write-out rate. (`p` carries only `PGenerableRat`, and that class is now **write-out** metered via `GeneratedRatFeature.polyTok : BigSpliceStream`, so `p n = 1 − 2⁻ⁿ` and every other polynomially-writable but value-exponential probability sequence is admissible data; under the previous `RpnSpliceStream` field it was not, and the earlier note's claim that this half was already token-metered was wrong.) `δ` reaches the conclusion through `selfTrustQuoteOfRepresentation`, which needs `inv_of_pos`, so it is not eliminable. `paperConfidenceQuoteCode` used to demand `PolyRatCodes δ` too but consumed it only as `.computable`, and now asks for that; `SelfTrustQuote.delta_codes` was projected nowhere and has been deleted. **Theory hypotheses, settled 2026-08-30.** The elaborated binder list is `[T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]`; consistency is the paper's own standing assumption on Θ (tex:600-606, tex:993-997). Hypotheses beyond the paper's stated premises: only the two globally charged binders (`[T.Δ₁]`, `[𝗣𝗔⁻ ⪯ T]`) — see *Arithmetic-theory hypotheses* above. Two hypotheses were shed to get here. `[T.SoundOnHierarchy 𝚺 1]`, which the paper explicitly declines (tex:2673), was load-bearing only through `theoremDP_hworld`'s tag-5 fiber-exclusivity step, and that step is now a theorem of Θ — the positive and negative quotation schemas are the value-`1`/value-`0` fibers of one Foundation `code` formula, so `Θ ⊢ ∼(pos ⋏ neg)` follows from `code_uniq` plus Gödel completeness. The residual `[𝗜𝚺₁ ⪯ Θ]` that then held this row at `qualified` was **deleted outright** in tranche 7, with `QuotationTheoryPresentation.theory_sigmaOne`: the endpoint had inherited it from that field and from no step of its own, and now spends only `𝗣𝗔⁻`. **Class residual: retired.** `φ` used to stay at `RpnSentenceCodes` here, unlike the sibling `thm:epr`/`thm:ceu`/`thm:ref` endpoints, because `lic_self_trust_closed` had to discharge `product_codes : LUV.RpnThresholdCodeSeq (indicatorProductLUV … φ)` and no write-out threshold class existed. Both halves of that are gone. `LUV.BigThresholdCodeSeq` was built (`Framework/Expectations.lean`, with `LUV.RpnThresholdCodeSeq.toBig` and `LUV.BigThresholdCodeSeq.reindex`), `SelfTrustQuote.product_codes` and `.confidence_codes` were widened to it — `#assert_fields` freezes field *names* only, so the type change passed the Tier-2 freeze silently and is recorded at the structure — and `indicatorProductLUV_rpnThresholdCodeSeq` was renamed and generalized to `indicatorProductLUV_bigThresholdCodeSeq` rather than duplicated, its single consumer moving with it. The endpoint now takes `hφ : BigSentenceCodes φ`, `def:ec`'s own write-out class, like the rest of the migrated surface. What made the migration possible was a determination about consumption, not a new bound: the token-metered form of `hφ` was consumed **nowhere** on the self-trust lane — `paperConfidenceQuoteCode` uses it only via `.primrec`, and every threshold consumer either reindexes (`.comp`/`.reindex`) or hands the certificate to `AffineCombination.PolySequence.sentence_poly`, already write-out metered. The `def:ec` census row records the consequence: `RpnSentenceCodes` now binds **zero** canonical endpoints |
| thm:strict | exact | universal | paper strength for **any** `DP` and any inductor. `_ofAtomCodes` needs only computability of the atoms' Gödel codes, `[IsLogicalInductor]` and `0 < C`, building the separator presentation internally via `strictSeparatorPresentationOfKleene`; the separator argument is fully constructed (Kleene's recursively inseparable pair, the constraint enumerator from the atom codes, and the stage classes proved null by the Kučera–Demuth argument rather than assumed). The bare form takes `S : StrictSeparatorPresentation M B` as an explicit caller input and is therefore weaker as a usable statement, so it sits second. Not `instantiated`, for the same reason as `thm:dus`: the `_unconditional` form is over the constantly-empty deductive process |
| thm:tbo | exact | universal | over `[IsLogicalInductor]`; the `sSup`/`sInf` over `fun j => P (n + j) (φ n)` are the paper's sup/inf over `m ≥ n` of `ℙₘ(φₙ)`, and the conclusion is the paper's two liminf/limsup identities verbatim |
| thm:wub | exact | universal | `lic_wub_ofComputation` is universal over `[IsLogicalInductor]` with exactly tex:1249-1258's premises plus `hworld`: a ℙ-generable divergent weighting, a strictly increasing deferral function whose image contains the weighting's support, and timed feedback (`FeedbackTruthComputation`, rendered with a *polynomial* clock at `f(k+1)`, i.e. a weaker hypothesis than the paper's `O(f(n+1))`). It leads for that reason. **Non-vacuity of the feedback premise, upgraded.** `FeedbackTruthComputation` is inhabited by more than the constant-truth certificate the lane used to offer: `alternatingFeedbackTruthComputation_nonempty` (`FeedbackTruth.lean`, annotated at `thm:wub`, `thm:wubaff`, `thm:wubexp`) is a genuine mixed-truth witness, and `exists_nonconstant_feedbackTruthComputation` exhibits the instantiation visibly — `truth (f 0) = 1`, `truth (f 1) = 0`. It is built from existing machinery (`BigDigits.mod_two` on `PolyFueled.id`, `ifzSel_polyFueled`), so no new interface was added to get it. This also narrowed a standing claim that was wrong: `ordinaryFeedbackTruthComputation`'s docstring asserted no non-constant certificate was available in-repo, reasoning from the `Encodable ℚ` `Denumerable` obstruction — which applies only to *unboundedly*-valued streams, while a finitely-valued stream needs only constant codes behind a poly-fueled test. The `_unconditional` form buys the discharge of `hworld` at the price of three arithmetic-theory class hypotheses the paper does not impose, and of no longer being about all inductors; it is shown second rather than alone. **Σ₁-soundness, retired 2026-08-30.** The `_unconditional` endpoint over `LIA` used to be stated under `[T.SoundOnHierarchy 𝚺 1]`, stronger than the paper's own Θ hypothesis (tex:993-997; tex:2673 treats soundness as a further assumption it declines); it now takes `[Entailment.Consistent T]`, the paper's own premise. The universal `_ofComputation` endpoint shown beside it carries no theory premise at all and is the paper's printed statement, so the row's status stands on that one and the charge is confined to the extra instantiation **Criterion note.** The sparing passes check (2) of *How this is charged* as well as check (1): the universal endpoint's premises are the printed ones — `TheoryTruth φ DP truth` and `FeedbackTruthComputation truth f`, tex:1249-1258's own truth bridge and timed-feedback program — not a stand-in for a step the paper derives from Θ, which is exactly what disqualifies the instance-free universal layer at thm:halts / thm:loops / thm:dontwait. |
| thm:wubaff | exact | universal | `boundedCombination_wubaff_ofComputation` takes a plain `BoundedCombinationSequence` — the paper's `⟨A⟩ ∈ 𝓑𝓒𝓢` at any bound — and rescales internally through `h.unitNormalization.scale`; emitter and truth bridge are constructed, leaving the paper's own timed-feedback premise `FeedbackTruthComputation`. It leads because the unit-magnitude siblings `lic_wubaff_ofComputation(_unconditional)` carry `∀ i, (As i).magnitude P ≤ 1` plus a separate `BoundedAffinePrices`, a normalization the paper's `𝓑𝓒𝓢` does not impose; the repo's own docstring calls the bounded-combination form "paper-facing", and it is now the one shown. **Σ₁-soundness, retired 2026-08-30.** The `_unconditional` endpoint over `LIA` used to be stated under `[T.SoundOnHierarchy 𝚺 1]`, stronger than the paper's own Θ hypothesis (tex:993-997; tex:2673 treats soundness as a further assumption it declines); it now takes `[Entailment.Consistent T]`, the paper's own premise. The universal `_ofComputation` endpoint shown beside it carries no theory premise at all and is the paper's printed statement, so the row's status stands on that one and the charge is confined to the extra instantiation **Criterion note.** The sparing passes check (2) of *How this is charged* as well as check (1): the universal endpoint's premises are the printed ones — a plain `BoundedCombinationSequence` plus `FeedbackTruthComputation`, the paper's `⟨A⟩ ∈ 𝓑𝓒𝓢` and timed feedback — not a stand-in for a step the paper derives from Θ, which is exactly what disqualifies the instance-free universal layer at thm:halts / thm:loops / thm:dontwait. |
| thm:wubexp | exact | instantiated | the normalized threshold mesh, its feedback traders, and its sparse delayed-truth affine family (the one the paper builds *inside* `app:wub`) are all constructed. The remaining premises are tex:1822-1832's, **one of them relocated, and the relocation is declared rather than denied** — a bounded LUV-combination sequence determined via `Θ` at the *combination* level (`def:affthmval`), the `def:luv` premise `WorldValued`, a ℙ-generable divergent weighting, timed feedback (polynomial clock at `f(k+1)`, as for `thm:wub`), and `hsupport`: the support of `⟨w⟩` lies in the image of the strictly increasing deferral function `f`. **Erratum PE2.** `hsupport` is *not* printed at this node. It is printed at `thm:recurringunbiasednessexp` (tex:1812-1820), a statement that introduces no `f` at all, so it cannot be read there; the affine twins `thm:wubaff`/`thm:prandexp` prove the intended placement, since the clause is exactly what their own proofs need and only the `f`-carrying node can state it. The Lean is the repair, taken in both directions: this node carries the un-printed `hsupport`, and the mirror theorem `LUVCombination.BoundedSequence.recurringunbiasednessexp` drops the spurious printed clause. Earlier editions of this row claimed the premises were exactly the printed ones; that claim was false in both halves and is withdrawn. All three statements (`luv_wubexp_ofComputation`, `luv_wubexp_ofComputation_unconditional`, `BoundedSequence.recurringunbiasednessexp`) now declare the transposition in their docstrings, and `hsupport`'s provenance line reads "the paper's own hypothesis, at the node it was transposed away from (`PE2`)". Recorded in `notes/paper-errata.md`. Determination is at the combination level only, so `[(1, X), (-1, X)]` for a wholly undetermined `X` is covered, which it would not be under `LUVCombination.ExactTheoryPresentation`; meshing is nonlinear, so the bridge is built at `ApproxDeterminedViaTheory` with the vanishing `meshErrorBound` (`lem:conluvapprox`). The universal form over any inductor leads; the `LIA`-closed form follows.  **Σ₁-soundness, retired 2026-08-30.** The `_unconditional` endpoint over `LIA` used to be stated under `[T.SoundOnHierarchy 𝚺 1]`, stronger than the paper's own Θ hypothesis (tex:993-997; tex:2673 treats soundness as a further assumption it declines); it now takes `[Entailment.Consistent T]`, the paper's own premise. The universal `_ofComputation` endpoint shown beside it carries no theory premise at all and is the paper's printed statement, so the row's status stands on that one and the charge is confined to the extra instantiation **Criterion note.** The sparing passes check (2) of *How this is charged* as well as check (1): the universal endpoint's premises are the paper's own — the `def:blcp` bounded sequence, `WorldValued`, a ℙ-generable divergent weighting and timed feedback, all tex:1822-1832's, plus the `hsupport` clause PE2 transposed to the wrong node — not a stand-in for a step the paper derives from Θ, which is exactly what disqualifies the instance-free universal layer at thm:halts / thm:loops / thm:dontwait. |
