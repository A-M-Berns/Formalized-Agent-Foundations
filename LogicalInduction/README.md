# Logical Induction

A Lean 4 formalization of Garrabrant, Benson-Tilsen, Critch, Soares, Taylor,
[*Logical Induction*](https://arxiv.org/abs/1609.03543) (arXiv:1609.03543v5).

## Downstream use

Use `import LogicalInduction.API` for the semantic framework and general property
theorems: sentences, markets, deductive processes, features, traders and exploitation,
the logical-induction criterion, affine combinations, LUVs, expectations, asymptotics,
and the `lic_*` families. It intentionally excludes the concrete LIA construction and
compiler. Some raw digit/RPN machinery is necessarily visible through transitive theorem
imports, but is not thereby designated as supported API. Import
`LogicalInduction.Construction.LIACompiler` for the concrete construction endpoints, or
`LogicalInduction` for the complete rollup. The API module documents the supported
high-level efficiency certificates and the unchanged `dd:fuel`, propositional-LUV, and
finite-perturbation boundaries.

The existence theorem is proved in the paper's full sense. 53 of the paper's labelled
results are carried as annotated nodes — named after the paper's own label, build-audited,
and rendered on the trust surface. Eight further labelled appendix lemmas
(`lem:fpl`, `lem:mm`, `lem:budgeter`, `prop:enumeration`, `lem:type2`, `lem:type3`,
`lem:conluvapprox`, `lem:limexpapprox`) are also formalized, but as construction machinery
cited from their module headers rather than as annotated nodes; they are listed and gated in
`scripts/check_endpoint_coverage.py`, which fails if a labelled paper result is neither
carried nor explicitly excused. How strong each node is, over the 53 annotated theorem and
lemma nodes:

| | count | what it means |
|---|---:|---|
| **exact** | 30 | proved as the paper states it, on the paper's own hypotheses |
| **strengthened** | 6 | the Lean statement is stronger than the printed one |
| **corrected** | 2 | the printed statement is defective; the corrected statement is proved (`thm:prand`, `thm:recurringunbiasednessexp`) |
| **refuted** | 1 | the printed statement is **false**, and is refuted here (`thm:ifp`) |
| **qualified** | 14 | proved with an explicitly named representation interface, class restriction, or hypothesis stronger than the paper's, retained |

The paper's 13 *definition* nodes are classified separately (12 exact, 1 qualified) and are
not mixed into the table above.

Each non-exact node says in one line what it retains, strengthens, corrects or refutes. The
per-node table is [`scripts/coverage-classification.md`](../scripts/coverage-classification.md),
machine-checked against the endpoint inventory so a node cannot ship without a strength
call, and so that a name shown on the trust surface must resolve, carry the node it is
listed under, and be axiom-checked. A browsable guide — every paper statement rendered
beside the Lean endpoint that carries it — is generated from the repository at
[`docs/trust-surface.html`](../docs/trust-surface.html) (`python3 scripts/gen-trust-surface.py`
to regenerate). That guide covers every formalized paper, one section each; only this
paper's section carries per-node tiers, reading notes and audit notes, because only this
paper has the strength classification they are read from. The others are correspondence
views, and say so.

Of the 53, **18 are also instantiated over the concrete inductor constructed here** — 4 of
them at exact or strengthened, 14 at qualified — so they hold of a specific algorithm rather
than a hypothetical one. The paper states no such theorems; that is a strengthening, not a
different degree of faithfulness.

**Two caveats on those counts, because both are easy to miss.** First, every tier is
relative to the disclosed model — propositional sentences, and machine polynomial time as
the trader class with the fuel calculus as its certificate (see *The modeling boundary*);
"exact" means the paper's statement is reached *within that model*, not that the model
equivalence is proved.

Second, the cause that used to dominate the `qualified` count — a **whole-value**
efficiency hypothesis where the paper asks only for efficient computability — is now gone
from the paper-facing surface. `PolyFueled` bundles `IsPolyBounded f`, a bound on the
function's *output value*, so `PolyNatCodes` and `PolyMachineCodes` admit only sequences
whose values grow polynomially, while the paper's e.c. is polynomial *time*: poly time to
write an object bounds its **symbols**, permitting values up to exponential.
`not_polyFueled_two_pow` proves that restriction strict.

The *write-out* classes exist for most kinds of datum the property tail
consumes — `BigDigits` for naturals, `DigitRatCodes` for rationals, `DigitMachineCodes` for
machine codes, `BigSentenceCodes` for sentences, and `BigTokenStream`/`BigSpliceStream` for
the emission surface they are consumed on. **One kind is metered differently: LUV
thresholds.** `lic_iterated_expectations_ofCode_unconditional`,
`lic_expected_future_expectations_ofRepresentation_unconditional`,
`lic_no_expected_net_update_ofRepresentation_unconditional`, its `_conditional_` sibling,
and `lic_self_trust_ofRepresentation_unconditional` take `RpnThresholdCodeSeq`, which is
`RpnSentenceCodes` on the threshold family rather than one of the write-out classes.
**That is not a restriction on the paper's own first-order LUVs**, and this file has now
been wrong about it in both directions.

The route from a literal paper LUV into the class is
`PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq`
(`Construction/Witnesses/StructuredPaperRpn.lean`). It quantifies over `PaperLUVSeq`, not
over `ℕ → PaperLUV`: that structure bundles a field `PaperLUV` itself does not carry —
`structural : PolyArithmeticFormulaSeq`, a `PolySegStream` certificate on the defining
formula's *symbol list*. An earlier edition of this file overlooked the field and claimed
the residue cost the paper nothing; the field is real and is stated here.

What the field asks for is the paper's own `def:ec` condition, on the paper's connectives.
It meters the formula string, one token per node of the Foundation formula, and along this
route every emitted token is a fixed small constant (`encodeArithmeticFormulaSymbols_lt`,
`structuredPaperPrimeBlock_span`), so the class is polynomial *length* — write-out — and
never expands a Gödel code or a numeral beyond what the author wrote. Large values are named
compactly, as the paper names them (tex:614): `binNumeral v` is the Horner `ℒₒᵣ` term for `v`
in `O(log v)` nodes (`binNumeralEnc_length_le`, `binNumeral_val`) — the same term that names
the machine/input argument of the computational-knowledge claims below — and
`dyadicPaperLUVSeq` is
the family of literal paper LUVs of value **`2⁻ⁿ`** built on it, with
`dyadicPaperLUVSeq_frontend` giving both frontend conclusions. It stands beside
`unitFracPaperLUVSeq` at `1/(n+1)`; the two share the template `invFormula`/`invPaperLUV` and
differ only in the denominator's name. `PaperLUV.rpnThresholdCodes` is the single-LUV route
into the non-sequence `LUV.RpnThresholdCodes`, the hypothesis `thm:ec`
(`LUV.expect_converges`) takes.

Two boundaries of that metering are recorded as named refutations, and they are of different
kinds. The first is an **artifact**: the same value spelled with Foundation's *unary*
`Operator.numeral` has no certificate
(`unaryRendering_two_pow_not_polyArithmeticFormulaSeq`). The paper fixes no numeral notation
— it writes numerals positionally (tex:614, tex:757) — and the value is nameable compactly
inside `ℒₒᵣ`, so the class is not narrowed on numerals.

The second concerns the **connectives**, and it is settled by where the metering sits.
Foundation's `Semiformula` is a negation-normal-form datatype with no `⟺` constructor, so
metering the normal form would charge `3 + 2|A| + 2|B|` tokens for `A 🡘 B`
(`encodeArithmeticFormulaSymbols_iff`) while the paper's language has `⟺` as a **primitive**
(tex:560). Nothing here meters the normal form. `PaperLUVSeq` carries each LUV's defining
formula as the paper writes it — `source : ℕ → ArithSource 1` over the primitive connectives
`¬ ∧ ∨ ⟹ ⟺ ∀ ∃`, a proof `compiles` that it denotes the LUV's Foundation formula, and
`def:ec`'s condition on that writing, `structural : PolyArithmeticSourceSeq` — one emitted
token per **source** node, with normal-form expansion done inside the parser (tags
`20`/`21`/`22`) and never charged. The normal-form-metered `PolyArithmeticFormulaSeq` is
kept as a **strictness foil**: it embeds (`PolyArithmeticFormulaSeq.toSource`) and the
inclusion is strict, witnessed by the left-nested chain `Φ₀ = A`, `Φₖ₊₁ = Φₖ ⟺ A`, which is
certified in the paper's class at `5n + 4` emitted tokens
(`iffChainSource_polyArithmeticSourceSeq`, `sourceTokens_iffChainSource_length`) and refuted
in the foil at `≥ 2ⁿ` (`iffChain_not_polyArithmeticFormulaSeq`,
`two_pow_le_encode_iffChain`). `iffPaperLUVSeq` carries that family all the way to a literal
paper LUV family, with `iffPaperLUVSeq_frontend` giving both frontend conclusions, so
`PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq` is proved rather than asserted. That
two-layer architecture is what `dd:nnf` labels; it is not a charge. The residual `dd:fuel`
substitution is levied once at `def:ec` and is not re-levied here.

Of the write-out/value-metered class pairs listed above, four containments are **proved
strict**: `bigDigits_two_pow_not_polyFueled` (`BigDigits` over `∃ c, PolyFueled c v`),
`bigTokenStream_not_polySegStream` (`BigTokenStream` over `PolySegStream`),
`digitRatCodes_two_pow_inv_not_polyRatCodes` (`DigitRatCodes` over `PolyRatCodes`) and
`bigSpliceStream_two_pow_inv_not_rpnSpliceStream` (`BigSpliceStream` over
`RpnSpliceStream`, at the constant feature for `δₙ = 2^(−n)`). The remaining pair —
`BigSentenceCodes` over `RpnSentenceCodes` — is an inclusion with **no strictness proof**;
what is established for it is that its write-out constructor `ofDigitSentenceCodes` has no
value-bounded counterpart. Building the rational one retired
exactly the four rows this classification predicted it would: `thm:ref`, `thm:st`,
`thm:perkno` and `thm:simcal` now take the paper's own class, so `δₙ = 2^(−n)` and
`pₙ = 1 − 2^(−n)` are admissible data.

The machine and input classes then retired the last three. `thm:halts`, `thm:loops` and
`thm:dontwait` took the `PolyMachineCodes`/`PolyNatCodes` pair, where the mismatch was
sharpest — tex:1931-1933 asks for poly time to *write out* `⟨m⟩`, and a length-`n` bitstring
has value `2^n` — and now take `DigitMachineCodes`/`BigDigits`. The migration is proved
strict in both coordinates: `bigDigits_two_pow_not_polyNatCodes` exhibits `xₙ = 2ⁿ`, the
paper's own `⟨x⟩` shape, as admissible for `BigDigits` and refuted for `PolyNatCodes`, and
`digitMachineCodes_nest_not_polyMachineCodes` does the same for `Nat.Partrec.Code.nest`,
a machine sequence whose source is `2n + 1` symbols long while its source number is at
least `2^n`. Machines are named by `Code.sourceNat`, linear in the syntax tree; Mathlib's
`Encodable.encode` squares per node and is deliberately not the naming map. The same change
carried `BoundedComputation.input_poly` and `SemidecidableComputation.input_poly` to
`BigDigits`, which removes a smaller restriction from the §4.10 rows without touching what
actually qualifies them. `PolyMachineCodes` is now named only inside the witness that
refutes it, and no paper-facing endpoint takes a whole-value class **on a datum the paper
quantifies over as e.c.** One paper-facing endpoint still takes one on a repo-side object:
`lic_domination_universalSemimeasure_ofIndependentAtoms` (`thm:dus`) takes a
`DUSThresholdEmission`, whose `threshold_sum_codes` and `inverse_width_codes` fields are
whole-value `PolyRatCodes` (`Properties/UniversalSemimeasure.lean:405-407`). It constrains
the repo's own rational approximation table, which the paper never quantifies over and
which the repo constructs and proves the certificate for (`dusThresholdEmission`), so it
does not lower that row — the `thm:dus` row states this and the test it passes.

Widening a hypothesis strengthens the theorem that takes it, so the same change strengthened
several rows already classified `exact`: `lic_provind`, `lic_persistence_of_knowledge`,
`sentenceAffine_polySequence` and the rest of the affine/trader lane now accept sentence
families whose Gödel codes grow exponentially while their emitted symbol count stays
polynomial. Their status is unchanged — the narrower class was already inside the paper's —
and their rows record the widening.

Three of the qualified nodes are the §4.10 consistency family (`thm:pac`,
`thm:pazfc`, `thm:incons`), whose rows say exactly what is and is not formalized. In
particular `thm:pazfc` is **not** a qualified rendering of the paper's theorem: its
distinctive second-theory parameter is absent, and the kernel accepts
`@lic_belief_finitistic_consistency = @lic_belief_stronger_theory_consistency := rfl`.

The other eleven — `thm:ref`, `thm:lp`, `thm:st`, `thm:epr`, `thm:er`, `thm:cee`,
`thm:ceu`, `thm:ccee`, `thm:halts`, `thm:loops`, `thm:dontwait` — are qualified for a
theory-hypothesis reason rather than a mathematical one. Eight of them carry
`[T.SoundOnHierarchy 𝚺 1]` at their canonical endpoint, a **stronger** hypothesis than the
paper's. Three no longer do — `thm:dontwait`, `thm:halts` and `thm:loops` — being stated
over `paperTheoryDP`; what holds each of those at `qualified` is the single disclosed
residual `[𝗜𝚺₁ ⪯ Θ]` —
by ruling a real theory-strength hypothesis beyond the paper's "computably enumerable",
not a representation choice. (An extensionality defect found in those three claim families
by the 2026-08-30 audit was repaired the same day; see *Instantiating the arithmetic-theory
family* below.) See *Instantiating the arithmetic-theory family* below, and
the *Σ₁-soundness premise* section of the classification ledger for the
endpoint-by-endpoint blast radius (12 of the 105 canonical endpoints) and for where the
load-bearing use actually sits. The
universal layer of each of those nodes is free of the instance, but that is not uniformly
the paper's theorem: for the quotation family the universal endpoints take the paper's own
premises, whereas for `thm:halts`, `thm:loops` and `thm:dontwait` the theory-free
endpoints take `Represented*Claims` interfaces — the *result* of the paper's
representability step handed in as data — so they are useful generic theorems but not the
printed theorem under the paper's `Θ represents computations` hypothesis. What is charged
in every case is the closed, over-`LIA` form that the trust surface shows.

These numbers are recomputed from the classification ledger by
`scripts/check_endpoint_coverage.py`, which fails the build if any figure here drifts from
it — in both directions, so a count cannot be lost by rewording the sentence that carries
it. Rows that have
since moved were re-derived again from the merged signatures. Where a count is uncertain
we have rounded against ourselves.

**Zero `sorry`, zero `axiom` declarations** — every public endpoint reports only Lean's
standard `propext`, `Classical.choice`, `Quot.sound`, enforced by the build
(`AxiomAudit.lean` enumerates the public surface and fails compilation on any
regression), and every paper-label citation is verified two-way by script. That holds when
the arithmetic-theory family is *instantiated* as well as parametrically. The one standing
modeling substitution, and the representation interfaces that are not substitutions, are
described under *The modeling boundary* below.

## The main theorem

For every computable deductive process, a logical inductor exists — in the paper's full
sense:

* `exists_computable_beliefSequence_logical_inductor` — there is a computable sequence
  of explicit finite-support rational belief states (one program emits the day-`n`
  association list) whose induced pricing satisfies the logical induction criterion.
* `LIA_isMachineLogicalInductor` — the concrete recursively-constructed rational market
  built here (the paper's §5 algorithm: market maker via a from-scratch Sperner/Brouwer
  fixed point, budgeter, trading firm over a universal trader enumeration) satisfies
  the criterion **at the paper's own quantifier**: no trader in ordinary machine
  polynomial time exploits it. `LIA_is_logical_inductor` is the same statement at the
  fuel-class compatibility predicate, and follows.
* `exists_machine_logical_inductor` — the bare existence statement at that quantifier.

The chain the criterion's efficiency side runs along, all of it proved and axiom-clean:

```text
EfficientlyComputable Tr                     fuel certificate (how traders are built)
      │  EfficientlyComputable.toMachine     evaln → complexitylib TM, concrete bounds
      ▼
MachineEfficientTrader Tr                    def:ec: Complexity.FP on the unary day
      │  exists_enumeratedTrader_eq          exact coverage
      ▼
∃ i, enumeratedTrader i = Tr                 finite TMDesc + polynomial clock
      │  trading_firm_dominance
      ▼
(tradingFirmTrader DP Q).Exploits P DP       lem:tfdom
      │  lia_no_machine_trader_exploits
      ▼
LIA_isMachineLogicalInductor                 thm:lia at the machine class

and, in the other direction,
∀ i, MachineEfficientTrader (enumeratedTrader i)     enumeratedTrader_machineEfficient
```

so the enumeration is an enumeration *of* machine-efficient traders, not merely one that
covers them.

The §4 property tail — convergence, coherence, provability induction, persistence,
preemptive learning, calibration, unbiasedness, pseudorandomness, logical
relationships, non-dogmatism, Occam bounds, universal-semimeasure domination, closure
under conditioning and perturbation, expectations, introspection, paradox resistance,
and self-trust — is proved for **every** logical inductor (`[IsLogicalInductor P DP]`),
with paper-facing names mirroring the paper's labels (`lic_provind` ↔ `thm:provind`).
Where a theorem needs representation machinery (quotation, arithmetic,
computation-representing theories), that machinery is *constructed* over the concrete
inductor wherever the model permits, yielding `_unconditional` and `_closed` endpoints
with no hypotheses beyond the statement's own data; where a residual interface remains,
the per-node table says which.

## Domination of the universal semimeasure — how it is witnessed

`thm:dus` and `thm:strict` quantify over a *presentation* of finite bit prefixes as
sentences: an independent atom family, an enumeration of all finite bit strings, and an
efficient naming of the corresponding prefix conjunctions. Both nodes are proved at paper strength for **any** deductive process and any logical
inductor, and that presentation is now constructed (`ordinaryBitPrefixSentences`), so
endpoints exist that take **no caller input** at all
(`lic_domination_everyLowerSemicomputable_unconditional`,
`lic_strict_domination_universalSemimeasure_unconditional`).

One qualification on those input-free endpoints, because it is easy to miss and it is why
these two nodes are not counted as instantiated over the arithmetic inductor: they hold
over `emptyBitDeductiveProcess` — the constantly-empty theory — where the atoms'
independence and the plausible-world hypothesis are discharged by "no stage asserts
anything". That is a real logical inductor and a real theorem, but the paper frames these
results as fresh symbols added *to* a theory Θ, so the reasoner handles empirical
uncertainty *as well as* logical uncertainty (tex:1550, 1559); at Θ = ∅ there is no "as
well as". The general forms carry the content.

One point on the surface is worth stating plainly, since it constrains the interface.
`BitPrefixSentences.prefix_codes` is metered in **symbols**, not in the Gödel *value* of the
sentence code. That is forced, and the forcing is proved rather than asserted: a binary
connective costs two nested `Nat.pair`s (a fourth power) while a `List Bool` cons costs one
(a square), so the prefix conjunction's code is about `2^(4^m)` at an enumeration index of
about `5^(2^m)`, and no polynomial closes that gap for any atom family over any deductive
process (`not_polySentenceCodes_bitPrefixSentence`). Symbol metering — the repo's
`RpnSentenceCodes`, built for exactly this pathology — is also the paper's own cost measure
at `def:ec`, and the prefix conjunction's Polish run is `Θ(m)` small tokens.

The emitter that discharges it (`BitChain`) walks the enumeration index's own `Nat.pair`
chain: two fuel-clocked `prec` scans recover the string's length and a *global* head-validity
flag, and a variable-width concatenation emits two- or four-token literal blocks. The
validity scan is a correctness obligation, not a cost one — `Encodable Bool` sends every code
`≥ 2` to `none` and the list decoder is applicative, so one malformed head collapses the whole
string to `[]` (the sentence becomes `⊤`) rather than truncating it, and a position-local
emitter would silently disagree with the enumeration on every malformed index.

## Instantiating the arithmetic-theory family

The theorems that quantify over an arithmetic theory come in two shapes now, and the
difference is the paper's own standing hypothesis on Θ.

**The paper's premise, as a class.** `RepresentsComputations T`
(`Framework/RepresentsComputations.lean`) is the Lean rendering of the paper's §2
assumption that *Θ represents computations* (tex:600-606, imposed for §4.8–§4.12 at
tex:993-997): for every total computable `f : ℕ → ℕ` there is a two-variable Θ-formula
`γ_f` with

    y = f n  ↔  Θ ⊢ ∀ν (γ_f(n̄, ν) ⟺ ν = ȳ).

It is a condition on what Θ *derives*, with no reference to truth in ℕ; the paper notes at
tex:604 that it already forces Θ consistent, and `RepresentsComputations.consistent` is
that observation. It supplies both literals over one sentence — `represents_proves` and
`represents_refutes` / `represents_refutes_all`, which need `[𝗥₀ ⪯ T]` for the numeral
apparatus and no semantic hypothesis at all. It is non-vacuous:
`representsComputations_of_peanoMinus` (`Construction/Witnesses/R0Representability.lean`)
proves it for any theory `U` with `[𝗣𝗔⁻ ⪯ U]` that is true in `ℕ`, and the instances are
registered at `𝗣𝗔⁻`, `𝗜𝚺₁` and `𝗣𝗔`. Not at `𝗥₀`: Foundation's `code_uniq` is stated for
`𝗥₀` only inside a commented-out block, and `𝗥₀` has no trichotomy axiom, so the `rfind`
case of single-valuedness is unavailable there — `𝗣𝗔⁻` is the weakest theory in
Foundation's hierarchy for which the argument closes. Note the asymmetry, which is
deliberate: **verifying** the premise for a particular theory uses that theory's truth in
`ℕ` (through Gödel completeness and soundness), while **consuming** it never does. No
endpoint carries a semantic hypothesis on `T`; the concrete instances pay for themselves.

**Endpoints stated at that premise, with no soundness.** `thm:dontwait`
(`lic_does_not_anticipate_halting_unconditional`), `thm:pac`
(`lic_belief_finitistic_consistency_unconditional`) and `thm:pazfc`
(`lic_belief_stronger_theory_consistency_unconditional`) are stated over
`liaHistory (paperTheoryDP T)` under `[T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T] [RepresentsComputations T]`.
Their claim family (`Construction/Witnesses/ComputationRepresented.lean`) is named the
paper's own way, `⌜f⌝(⌜n⌝)` for a *total* decider, so the positive literal and its literal
negation come from one sentence and the stage world is consistent by `Entailment.Consistent
Θ` alone (`paperTheoryDP_nonvacuous`), which representability already gives. The LUV
threshold lane went the same way: `ArithmeticLUVPresentation` now carries
`[RepresentsComputations T]` and takes `threshold_enters` / `threshold_refutes` over one
schema and its negation, so `luvWorld` is the provability world and
`ComputableLUV.luvWorld_consistent` runs on consistency.

`thm:halts` (`lia_learns_halting_patterns_unconditional`) and `thm:loops`
(`lic_learns_provable_nonhalting_patterns_unconditional`) are now in this list too, and ask
for even less: they are stated over `liaHistory (paperTheoryDP T)` under
`[T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗥₀ ⪯ T] [Entailment.Consistent T]`, taking `Entailment.Consistent`
rather than `RepresentsComputations`, because this lane needs no *represented* negative
literal — `thm:halts`'s positive literal is Σ₁-completeness alone (`re_complete_mp`) and
`thm:loops`'s negative one is its own `hloops` premise, which the paper (`app:loops`) also
assumes outright. Their day-`n` claim is the *fixed* universal r.e. schema
`universalHaltingSchema` at the compact name of `⟨⌜mₙ⌝, xₙ⟩`, and `thm:loops`'s `hloops` is
the literal negation of that same sentence, so both endpoints speak about a claim that names
the machine.

So five paper-facing endpoints — `thm:halts`, `thm:loops`, `thm:dontwait`, `thm:pac`,
`thm:pazfc` — plus the LUV threshold lane now carry no soundness instance at all.

**The computational-knowledge endpoints name their machines.** `thm:halts`, `thm:loops`,
`thm:dontwait`, `thm:pac` and `thm:pazfc` are stated over `paperTheoryDP`, the paper's own
`Θ`-complete deductive process, with **no semantic hypothesis on `T`**. What each day-`n`
claim is *about* is fixed by an argument written into the sentence — the machine's source
number and its input, packed and spelled by the compact Horner term `binNumeral`, whose
`O(log v)` symbol run is emitted digit by digit from the paper's own write-out certificates
`DigitMachineCodes` and `BigDigits`, which is what makes those two hypotheses load-bearing
on `def:ec`. What is *represented* is universal and fixed once per theorem: the r.e.
`universalHaltingSchema` on the unbounded lane, and one `γ` per horizon program for the
total `universalRunValue f` on the bounded lane — the paper's `⌜f⌝`.

This replaces a rendering (through 2026-08-30, found by a blind audit that day, R5-F08/F09)
that hid the machine sequence *inside* a `codeOfREPred` schema or inside the represented
decider. Both constructions see their data only up to extensional equality, and each
endpoint's own hypothesis pinned that extension to a constant — all halt, never halt,
everywhere consistent — so the claim family was the same sentence family for every
admissible machine sequence and the write-out hypotheses did no work. The standing test
against that failure mode is now proved in-repo rather than assumed:
`haltingArgClaimSentence_ne_of_halts_ne` and `representedClaimSentence_ne_of_runValue_ne`
show that data differing in halting behaviour receive different claim sentences. Any future
represented claim family should carry the same witness. **The LUV threshold lane was never
affected** — `thresholdValue` is non-constant under that lane's hypotheses, and it was
audited clean.

**Where Σ₁-soundness remains, and why.** It remains at `theoremDP_hworld`'s **tag 7**, the
quotation lane, and reaches every endpoint over `theoremDP T` through it — the quotation
family (`thm:ref`, `thm:lp`, `thm:st`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`,
`thm:ccee`), `thm:incons`, and the three `FeedbackTruth`
`_unconditional` endpoints: twelve of the 105 canonical endpoints, counted from the
elaborated signatures. The soundness direction used is `re_complete`'s `.mpr` — provable ⇒
true — which keeps the positive and negative atom fibers of the constructed stage world
mutually exclusive. The reason it cannot simply be replaced there is **architectural**, and
it has two parts. `RepresentsComputations` supplies γ *existentially*, one per total
computable function, with no computable map from a quote code to `⌜γ⌝`; the universal quote
evaluation is partial, so γ has to be produced per decider rather than once for a universal
schema. That in turn forces the atom naming a quote to be the paper-prime of the represented
claim, carried by a schema-free process — and in this development the paper-prime atom layer
(`PaperFirstOrder.lean`) and its emission (`ArithmeticSource.lean`) sit strictly *downstream*
of `Construction/Witnesses/QuotationAffine.lean`. Closing it is therefore an import-layer
reorganization, not a local edit. It is the next tranche of this work, and nothing here
promises it.

**The residual `[𝗜𝚺₁ ⪯ Θ]`, disclosed in the same breath.** The migrated endpoints still
carry `[𝗜𝚺₁ ⪯ T]` where the paper assumes only that Θ is computably enumerable. It is
needed for exactly one thing: provability of the claim family is shown r.e. through
Foundation's *internal* arithmetization (`provable_instances_re`, over the `Bootstrapping`
provability predicate at `V = ℕ`), and that apparatus is stated over `𝗜𝚺₁`. This is a real
theory-strength hypothesis beyond the paper's, not a representation choice, so it is
charged the way the soundness instance is: a row whose only shown endpoint carries it stays
`qualified` on that single named residual. `thm:dontwait`, `thm:halts` and `thm:loops` are
exactly those rows.

**And `[T.Δ₁]`, one notch below.** Every endpoint over an arithmetic theory also asks for a
`Δ₁`-definable *axiom set* (`Theory.Δ₁`), where the paper asks only that Θ be computably
enumerable. The two are not the same condition on `T` as presented: a c.e. axiom set need not be
`Δ₁`. They are the same condition on the *theory*: by Craig's trick every c.e. theory has a
deductively equivalent `Δ₁` (indeed primitive recursive) axiomatization, and every statement
here is about `T ⊢ ·`, which such a re-axiomatization preserves. That step is not formalized;
`[T.Δ₁]` is charged once here as representation infrastructure for enumerating `T`'s theorems,
and does not by itself lower a row.

The nodes this still demotes, and the endpoint-by-endpoint blast radius, are in the
*Σ₁-soundness premise* section of
[`scripts/coverage-classification.md`](../scripts/coverage-classification.md).

They are also axiom-clean when *instantiated*. Foundation proves `Δ₁`-definability of `𝗜𝚺₁`
and `𝗣𝗔` outright at the pinned revision (`InductionSchemeDelta1.lean`, whose header records
that it discharges the two `axiom`s that previously stood in `Examples.lean`), so a concrete
instance over `𝗜𝚺₁` reports the same three axioms as everything else here.

## The modeling boundary

1. **Efficient computability is now the machine class; the fuel model is a certification
   device.** `def:ec` is `MachineEfficientTrader` — a trader is efficient when some
   `Complexity.FP` function of the *unary* day emits its day-`n` strategy. The
   construction enumerates that class (`enumeratedTrader`, sound and covering), the
   Trading Firm dominates it (`trading_firm_dominance`), and the capstone is
   `LIA_isMachineLogicalInductor` / `exists_machine_logical_inductor`: `def:lic` and
   `thm:li` at the paper's own quantifier.

   The fuel-clocked class `EfficientlyComputable` survives as the *certification
   technology* every concrete exploiting trader is built with, and
   `EfficientlyComputable.toMachine` proves those certificates imply genuine machine
   efficiency, through a real `evaln` → Turing-machine compiler with concrete register and
   step bounds. The converse is neither proved nor claimed, and nothing paper-facing needs
   it. `IsLogicalInductor` — the criterion over the fuel class — is kept as a
   compatibility predicate; every machine logical inductor is one, so the whole property
   tail transfers unchanged.

   **What this leaves.** The two statements whose *conclusion* is itself the criterion —
   they transport an arbitrary trader backwards across a market change, so restating them
   needs the machine class closed under the same trader translations. Both transports are
   now proved:

   * **closure under conditioning** (`thm:scon`) — **complete at the machine quantifier**,
     in all three forms. `conditionedTranslation_preserves_machine` and
     `eventualConditionedTranslation_preserves_machine` are the `Complexity.FP` transports,
     under the same hypothesis on the condition as their fuel counterparts; the endpoints
     are `lic_conditioned_machine`, `lic_conditioned_gated_machine` and
     `lic_conditioned_eventual_machine`. The fuel theorem and its witnesses are untouched
     beside them.
   * **closure under finite perturbations** (`thm:ifp`) — no longer a boundary of this
     kind, and for a stronger reason than the transport being built: the published
     unrestricted statement is **false**, and `not_overgeneral_ifp` proves it so. A single
     changed pricing day is an infinite computable function, so it can carry unbounded
     computational advice to an efficient trader. The corrected finite-*support* theorem is
     proved at both classes, and its machine form
     (`machine_lic_iff_of_recognizableSupport`) asks only for two computable markets and a
     perturbation — the freeze certificate is compiled from the market's own certificate
     rather than supplied. One residual hypothesis remains, `Recognizable`, and it is a
     condition on syntax rather than on markets; see the `thm:ifp` entry below for what it
     stands for.

   One thing this boundary is *not*, and it is worth saying plainly because the word
   "substitution" invites the opposite reading: choosing an efficiency notion is a
   choice the paper explicitly leaves open. Immediately after `def:ec` it says its
   framework "is not wedded to this definition," that stricter notions "would yield
   'dumber' inductors with better runtimes, and vice versa," and that it picks
   polynomial-time functions "because it has some closure properties that are convenient
   for our purposes" (tex:757). So a different-but-honest efficiency class is a
   variation the paper anticipates, not a departure from it. What is *not* thereby
   licensed — and what the model card states as the open question — is the claim that
   this particular class contains the paper's, which is why the calibration gap above is
   disclosed rather than waved through.

   The model bites in a second, subtler place, and it is what keeps most of the
   qualified rows qualified. Within the fuel model there are two ways to meter a
   sentence sequence: by **symbol count** (`RpnSentenceCodes`) — the faithful reading of
   `def:ec`, and the paper's own cost measure — or by the **Gödel value** of the single
   pair-code token (`PolySentenceCodes`). These are not interchangeable: the same
   pathology proved in the domination section above (`not_polySentenceCodes_bitPrefixSentence`)
   exhibits a paper-admissible e.c. sentence family that the whole-value class provably
   excludes, so whole-value metering is a genuine restriction of the paper's class.

   The property tail is stated at the faithful symbol-metered class throughout, and so
   is the whole quotation family's *unconditional-over-`LIA`* layer (`thm:epr`, `thm:er`,
   `thm:ref`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st` and `thm:wub`). The
   metacomputation family `thm:pac`/`thm:pazfc`/`thm:dontwait` used to sit at a narrower
   class here too, because the analogous `PolyNatCodes` on the *horizon* restricted the
   paper's "any computable function `f`" to polynomial-time `f`. That is now fixed: the
   claim schema defers the horizon term (`ComputableHorizon` names `⌜f⌝`; the arithmetic
   schema evaluates it), so any computable `f` is admissible and
   `not_polyNatCodes_ack` exhibits one — diagonal Ackermann — that the old class
   provably excluded.

   For the quotation family the gap turned out to be **residue, not obstruction**, and
   the distinction is recorded because it was got wrong once — in this file. What the
   quote-code constructors consume from the hypothesis is a *computability* fact,
   `Primrec fun n => encode (φ n)`, used to key the market's quote table by sentence
   code; no polynomial bound on the code value is needed anywhere downstream. The
   symbol-metered class already supplies that fact (`RpnSentenceCodes.primrec`, written
   for exactly this boundary, and noting in its own docstring that the codes are *not*
   polynomially fueled). The six above were therefore signature generalizations. The
   lesson generalizes past this instance: a hypothesis being consumed as *data* does not
   establish that its strength is load-bearing — check what the consumer extracts.

   `thm:st` was the one place in the quotation family where the generalization had real
   content: its product LUV used to inline the sentence's Gödel value into a `Nat.pair`
   shell. The token-level `⋏` emitter that repairs it is built
   (`indicatorProductLUV_rpnThresholdCodeSeq`), so the closed endpoint now sits at the
   symbol-metered class like the rest.

   The metacomputation family is a genuinely different defect, and a syntactic one: the
   paper's sentence names the *term* `⌜f⌝(⌜n⌝)`, whereas `BoundedComputation` carries the
   *evaluated* horizon `steps n` inside the claim's input, which is why its value must be
   polynomially bounded. Restoring the paper's reading means an unevaluated-term claim
   schema, not a better bound.

   Worth noting: the paper itself is explicit (remark after `def:ec`) that its
   framework is not wedded to polynomial time — any efficiency class with suitable
   closure properties yields logical inductors, with stricter classes giving weaker
   but faster ones. Poly-time was their choice of convenience, not a load-bearing
   one. The fuel class carries the closure properties the theory's core needs — the
   construction and all but one of the property theorems completed inside it — so even
   if the inclusion question resolves negatively, what is formalized here is a logical
   inductor over a legitimate neighboring instantiation of the framework, not a
   different kind of theorem. The `thm:ifp` exception above is the one place where the
   class's closure gap is load-bearing rather than cosmetic.
2. **Retired — the propositional substrate.** Sentences are still Foundation's
   propositional formulas, and the paper's first-order theory Θ still enters through
   explicit interfaces instantiated by arithmetic theories. That is now an ambient
   representation choice rather than a standing modeling *substitution*, because the one
   node it was charged at is no longer abstracted. A logically uncertain variable is
   presented to downstream results by its family of threshold sentences `⌜X > r⌝`, but
   that family is now produced by a literal first-order object: `PaperLUV` is an actual
   one-variable arithmetic formula carrying object-level `T`-proofs of unique existence
   and `[0,1]` membership, its threshold syntax is the paper's own, and its world-value
   semantics is *derived* through `paperTheoryDP` and the rational cut rather than carried
   as a build-frozen certificate. `PaperLUVSeq` additionally compiles that literal
   threshold syntax to the symbol-metered `RpnThresholdCodeSeq`, and the frontend is
   inhabited by varying concrete families at both ends of the range the paper writes:
   `unitFracPaperLUVSeq` at `1/(n+1)` and `dyadicPaperLUVSeq` at `2⁻ⁿ`, the latter naming
   its denominator by the compact `ℒₒᵣ` term `binNumeral (2 ^ n)`; `PaperLUV.rpnThresholdCodes`
   is the single-LUV route into the non-sequence `LUV.RpnThresholdCodes`. Nothing remains
   charged to this item; `dd:nnf`, listed as item 3 below, is no longer a substitution
   either. See
   [`notes/fol-luv-frontend.md`](notes/fol-luv-frontend.md); `def:luv` is classified
   `instantiated` accordingly.

   `def:blcp` is closed the same way: `PaperLUVCombination` reaches the abstract carrier
   only through `PaperLUV.toLUV`, and its bounded-sequence certificate comes from the paper
   family's own structural data rather than from anything assumed of the shares. What
   remains charged to this item is narrow and stated where it bites: the object-level value
   of a `PaperLUV` is named by a numerator/positive-denominator pair code rather than by a
   canonical rational arithmetic inside `ℒₒᵣ`.

   The flat atom representation once forced the closed `thm:ccee` endpoint through a
   `1/(n+1)` mesh product. That historical endpoint remains available, but it is no longer
   the endpoint of record. `Construction/Witnesses/SemanticLiftedCCEE.lean` constructs one
   canonical language and deductive process from `T` before the source, deferral, or weight
   is selected. A fixed injective renaming places every caller source in an old-language
   namespace disjoint from semantic handles. The renamed theorem stream is a genuine
   independent copy—there are no alias axioms back to the original atoms—so the prior
   self-reference diagonal is unavailable.

   Source admission is not proof-carrying. From the existing completed-world
   `source_valued` premise, rational-cut laws follow semantically; propositional compactness
   gives a finite theorem stage, and an executable finite entailment checker lets the fixed
   universal registry discover that stage. `RpnThresholdCodeSeq` supplies the mesh-query
   emitter needed by exact semantic multiplication. Thus
   `lic_no_expected_net_update_conditional_exact_canonical` has the same caller source class as
   the former mesh endpoint, constructs the deferred weight and right quotation internally,
   and instantiates the conditional trader theorem with slack identically zero.

   This is not the rejected source-dependent `productDefDP` maneuver. There is one market,
   `liaHistory (canonicalCCEEDP T)`, constructed over a fixed enlarged language from the
   outset; no equality with prices of `liaHistory (theoremDP T)` is asserted or needed.
   `canonicalCCEEDP_hworld` supplies an explicit completed-world witness for the full
   universal source, quotation, and product process.

   **The slack is invisible at the one known downstream interface.** The deference port
   of "Deference Done Better" into this framework consumes `thm:ccee` as a hypothesis
   `hCcee : Approx Exw Eew` — two abstract real sequences related by `≈ₙ`, with no LUV
   structure, no deductive process, and no slack term crossing the boundary. The mesh
   endpoint's conclusion has exactly that shape, so it discharges the hypothesis as well
   as an exactly-reflecting one would.

3. **Retired — the object language (`dd:nnf`).** The *semantic* object language is still
   Foundation's negation-normal-form `Semiformula` (`verum/falsum/rel/nrel/and/or/all/exs`),
   but *writing* is no longer metered there. The paper's language has `⟺` as a primitive
   connective (tex:560, "includes the basic logical connectives ¬, ∧, ∨, ⟹, ⟺"), and formula
   families are metered on a matching **source** language: `ArithSource k`
   (`Construction/Witnesses/ArithmeticSource.lean`) carries those primitives plus atomic
   leaves, `ArithSource.compile` gives it its meaning (`eval_compile` is the semantic
   bridge), and `def:ec`'s condition is `PolyArithmeticSourceSeq` — one emitted token per
   node of the formula **as the paper writes it**. Normal-form expansion happens inside
   `parseStructuredArithmeticFormula` (source tags `20` = `¬`, `21` = `⟹`, `22` = `⟺`) and
   is never charged to the emitter. So nothing pays twice for a biconditional, and the
   substitution this item used to disclose is gone.

   What the label now marks is the two-layer architecture and one deliberate retention: the
   normal-form-metered class `PolyArithmeticFormulaSeq` is kept as a **strictness foil**. It
   embeds (`PolyArithmeticFormulaSeq.toSource`), and the inclusion is strict, proved at the
   left-nested chain `Φ₀ = A`, `Φₖ₊₁ = Φₖ ⟺ A`: `5n + 4` source tokens
   (`iffChainSource_polyArithmeticSourceSeq`, `sourceTokens_iffChainSource_length`) against
   `≥ 2ⁿ` normal-form tokens (`iffChain_not_polyArithmeticFormulaSeq`,
   `two_pow_le_encode_iffChain`). `iffPaperLUVSeq` carries that family to a literal paper LUV
   family whose `n`-th defining formula is `O(n)` characters to write, with
   `iffPaperLUVSeq_frontend` reaching `LUV.RpnThresholdCodeSeq`. So
   `PolyArithmeticFormulaSeq ⊊ PolyArithmeticSourceSeq` is proved, not asserted, and the
   symbol-metered class the statements use is the paper's own condition on its own syntax.

The fuel model is no longer a modeling substitution: `def:ec` is the machine class, and the
fuel certificate is proved to imply membership in it. What is disclosed at the affected
statements is now the *residue* — the two machine-class transport theorems named above.

## The two closure statements

`thm:scon` and `thm:ifp` are the two theorems whose *conclusion* is itself the criterion, so
the machine ⟸ fuel bridge never reached them: their proofs transport an arbitrary trader
backwards across a market change and must certify the transported trader. Both are now
settled, and they settled differently — one strengthened to the machine class, the other
refuted and replaced.

* **`thm:scon` — closure under conditioning.** *Strengthened paper theorem.* Complete at
  the machine quantifier in all three forms — abstract compiler, gated translator and
  finite-zero translator. The `Complexity.FP` transports
  (`conditionedTranslation_preserves_machine`,
  `eventualConditionedTranslation_preserves_machine`) carry the same `RpnSentenceCodes`
  hypothesis on the condition as the fuel counterparts, so nothing is weakened and the
  trader hypothesis is strictly stronger. The fuel-level theorem and its concrete witnesses
  (`GatedConditioningOperationalWitness`, `EventualConditioningOperationalWitness`) are
  unchanged and inhabited beside them.
* **`thm:ifp` — closure under finite perturbations.** All four categories are represented,
  and the published statement is in the first only as a refutation.

  * *Exact paper theorem* — **refuted**. `not_overgeneral_ifp`
    (`Construction/Witnesses/FinitePerturbationWitness.lean`) proves the unrestricted
    finite-day statement **false** at the paper's own quantifier: closed but for the
    deductive process, `sorry`-free, `[propext, Classical.choice, Quot.sound]`.
  * *Corrected theorem* — `machine_lic_iff_of_recognizableSupport` (`FreezeOracle`):
    two computable markets differing on only finitely many `(day, sentence)` price
    coordinates satisfy the criterion together. Finite support is the natural repair,
    because it is exactly the case in which the appendix's "hard-code the constants" step
    is literally valid. It is **strictly stronger** than the paper's tail agreement
    (`FiniteSupportPerturbation.tail_agree` one way; the day-`0` huge-numeral market the
    other), so this is a proper restriction, not a restatement. `Properties/FinitePerturbations.lean`
    holds the class-agnostic form and its fuel-class twin.
  * *Compatibility* — `lic_iff_of_finitePerturbation` keeps the paper's own hypothesis
    shape and its explicit prefix-patch premises. It is retained so the repo's coverage of
    the paper's quantifier is legible; it is **not** the corrected paper-facing theorem.
  * *Auxiliary* — the freeze compiler and run-oracle machinery (`FreezeStep`,
    `FreezeOracle`, `RpnFreeze`, `CanonicalCodes`) are implementation, not statements.

  **Why the paper's proof fails.** The paper has finitely many changed *days*, not finitely
  many changed `(day, sentence)` constants. A single day is an infinite pricing function, so
  it can carry unbounded computational advice — which is exactly what the counterexample
  makes an efficient trader read, through historical price features, without ever computing
  it.

  **The one residual hypothesis, and what it is.** The corrected theorem asks that the
  finitely many sentences whose price moves be `Recognizable` — `BotFree` and `NoReserved`.
  That is a condition on *syntax*, not on markets, traders or perturbations: representation
  residue, not mathematics. Each half stands for one `Complexity.FP` primitive this toolkit
  lacks — integer square root for `BotFree` (Foundation's `ofNat` discards the payload at
  tag `0`, so deciding whether a code denotes `⊥` is deciding whether it is a perfect
  square) and a structured-payload parser for `NoReserved`. Both are polynomial time
  mathematically. Neither half has slack: `decode_and_noncanonical` proves the first
  necessary, and a structured spelling at any subterm breaks completeness. So the
  unrestricted finite-support statement is, as far as this development can tell, **true** —
  and unprovable here for want of two primitives rather than for want of a theorem.

  **Witnesses.** `machine_lic_iff_twoPoint` is closed but for the deductive process — a
  concrete pair of computable markets, proved to differ at the frozen coordinate,
  discharging every hypothesis at once — so the corrected theorem is **non-vacuous**. It is
  also **informative**: `LIAPerturbation.machineLogicalInductor_liaPerturbed` applies it to
  the constructed `LIA` with one price moved and *derives* that the perturbed market is
  itself a machine logical inductor. That market is not the output of any construction here,
  so its inductor-hood is exactly what the theorem buys. It inherits `Construction/LIA.lean`'s
  own two hypotheses — LIA's market program and a computable deductive process — which are
  pre-existing and unchanged.

  The fuel-class certificates `EfficientPrefixPatch` and `FiniteSupportPatch` remain
  **uninhabited**, because the fuel calculus does not close over the escape-leaf decode: the
  `dd:fuel` inverse-operation ceiling, binding where it was predicted to.

## Faithfulness

Every paper-facing statement carries the paper's own `\label` in a `Paper node:` docstring
line, checked in both directions by `scripts/check-paper-nodes.sh`: every cited label exists
in the committed TeX, and every audited endpoint carries a label. `scripts/check_endpoint_coverage.py`
records each node's strength, `AxiomAudit.lean` asserts axiom cleanliness at every canonical
endpoint, and `docs/trust-surface.html` renders the node-by-node correspondence for a human
read-through.

The formalization surfaced six defects in the paper itself, recorded with their repairs in
[`notes/paper-errata.md`](notes/paper-errata.md). One of them is not a repairable slip: the
printed closure under finite perturbations is **false**, and is refuted here.

## Layout

* `Framework/` — the paper's §2–3: sentences, markets, features, traders,
  exploitation, the criterion, efficient computability, expectations, and the shared
  asymptotic vocabulary.
* `Properties/` — the §4 property tail, one file per theorem family.
* `Construction/` — the §5 existence proof, with `Construction/Witnesses/` holding the
  constructed representation machinery that discharges the property tail's interfaces
  over the concrete inductor.
