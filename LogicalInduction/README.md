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
| **exact** | 42 | proved as the paper states it, on the paper's own hypotheses |
| **strengthened** | 7 | the Lean statement is stronger than the printed one |
| **corrected** | 2 | the printed statement is defective; the corrected statement is proved (`thm:prand`, `thm:recurringunbiasednessexp`) |
| **refuted** | 1 | the printed statement is **false**, and is refuted here (`thm:ifp`) |
| **qualified** | 1 | proved with an explicitly named representation interface, class restriction, or hypothesis stronger than the paper's, retained |

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

Of the 53, **18 are also instantiated over the concrete inductor constructed here** — 17 of
them at exact or strengthened, 1 at qualified — so they hold of a specific algorithm rather
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
carried the `input_poly` fields of the §4.10 presentation structures to `BigDigits`,
removing a smaller restriction from those rows without touching what actually qualified
them; both structures (`BoundedComputation`, `SemidecidableComputation`) were themselves
retired in tranche 8, when the two nodes moved onto arithmetized subject matter. `PolyMachineCodes` is now named only inside the witness that
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

**The one remaining qualified node is `thm:incons`**, and it is qualified on two disclosed
charges, neither of them a theory-hypothesis one. `thm:incons` is stated for the **deduction family**
`Θ′ₙ = Θ₀ ∪ {σₙ}` over a fixed Δ₁ base theory, rather than for an arbitrary efficiently
computable sequence of recursively axiomatizable theories: Foundation's derivability
predicate takes its theory as a meta parameter, so there is no uniform-in-theory-code
derivability to represent. The deduction theorem makes the day's theory nameable by the
single code `⌜∼σₙ⌝`, which the day's sentence writes out, so the claim genuinely names the
day's theory; the restriction on *which* theory sequences are covered is the disclosed part,
and its row says exactly what is and is not formalized. A **second** charge is disclosed on
the same row: the `def:ec` premise `hσ : BigDigits (deductionFamilyArg σ)` meters the day's
theory name by the base-4 digit count of a formula's *Gödel code*, not by its source length —
Foundation's encoding pairs at every node, so that count is `~2^depth`, and the premise admits
only `O(log n)`-depth families, excluding paper-admissible short-source/deep-parse ones. It is
neither `dd:fuel` nor `dd:proofcode` but the ordinary write-out class applied to the wrong
quantity, and being an over-strong *hypothesis* it narrows which theory sequences the endpoint
covers rather than weakening its conclusion; the faithful repair is to state the premise on
`PolyArithmeticSourceSeq`, and it is queued with the 9-series. The paper's own subject matter
is exhibited — the in-file example runs at base theory `𝗜𝚺₁` with `σₙ := ⊥`, so every day's
theory `𝗜𝚺₁ ∪ {⊥}` is actually inconsistent — and a genuinely day-varying witness,
`alternatingInconsistentAxiom n := if n % 2 = 0 then ⊥ else ⊥ ⋏ ⊥`, sits beside it with its
emission certificate and a fully applied endpoint, exercising day separation at days `0` and
`1`. That family takes two values, not unboundedly many: an unbounded-length family is blocked
on a missing `BigDigits` combinator, signposted at the witness.

Its two §4.10 neighbours **left that list in tranche 8**. `thm:pac` and `thm:pazfc` are one
construction at two theories. Both endpoints price the arithmetized finite-consistency family
of a theory `Θ′`, rendered as the value-`0` sentence of a `Θ`-formula representing `Θ′`'s
bounded-provability decider (`Framework/BoundedConsistency.lean`, metered by derivation code —
`dd:proofcode`). `lic_belief_finitistic_consistency_unconditional` is the diagonal `Θ′ = Θ`,
where the consistency needed for the claims' truth is already implied by `Θ`'s representing
computations; `lic_belief_stronger_theory_consistency_unconditional` takes `Θ′` as a second
parameter with consistency as the paper's own explicit premise, and is witnessed at
`Θ = 𝗜𝚺₁`, `Θ′ = 𝗣𝗔`. No hypothesis relates `Θ` and `Θ′` in either statement: the paper
assumes of `Θ′` only that it is a stronger consistent recursively axiomatizable theory
(tex:1881-1886) and states no containment, so the Lean hypotheses **match** the paper's rather
than generalizing them; what makes the result interesting is the informal case where `Θ` cannot
prove `Con(Θ′)`, which the `𝗜𝚺₁`/`𝗣𝗔` witness carries concretely. Both are `exact` modulo the disclosed `dd:proofcode` metering substitution. The
`@lic_belief_finitistic_consistency = @lic_belief_stronger_theory_consistency := rfl` identity
that the kernel once accepted has been deleted and is false: the second endpoint's abstract
layer no longer exists, and the two nodes differ in which theory is metered.

The eleven arithmetic-theory nodes that used to sit beside them — `thm:ref`, `thm:lp`,
`thm:st`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:halts`, `thm:loops`,
`thm:dontwait` — no longer are. They were qualified for a theory-hypothesis reason, and
that reason is gone in both of its parts: **no canonical endpoint carries
`[T.SoundOnHierarchy 𝚺 1]`** (0 of 105, the quotation lane having been the last holdout),
and the residual `[𝗜𝚺₁ ⪯ Θ]` that then held them was deleted everywhere it was merely
inherited — it survives on exactly three of the 105 endpoints, where the substrate's Gödel
fixed point and rational-cut arithmetic are indexed at `𝗜𝚺₁`, and is disclosed there as
representation infrastructure alongside `[T.Δ₁]`. What each shown endpoint asks for now is
the paper's own standing assumption on Θ. `thm:lp` lands at `strengthened` rather than
`exact`, because it *constructs* the paradoxical sequence the paper merely posits. The
per-node residual disclosures, and the rulings behind them, are in the
*Arithmetic-theory hypotheses* section of the classification ledger; the construction they
describe is in *Instantiating the arithmetic-theory family* below.

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

The paper's §2 Notation fixes a single standing assumption on the background theory Θ, and
this development's arithmetic-theory family is stated at it and nothing more. The path from
that assumption to a property theorem has four steps, and each is a named object here.

**1. The paper's premise, as a class.** tex:600-606 assumes that Θ *represents
computations*: for every total computable `f : ℕ → ℕ` there is a two-variable Θ-formula
`γ_f` with

    y = f n  ↔  Θ ⊢ ∀ν (γ_f(n̄, ν) ⟺ ν = ȳ),

imposed for §4.8–§4.12 at tex:993-997. `RepresentsComputations T`
(`Framework/RepresentsComputations.lean`) is that condition verbatim modulo the disclosed ℕ⁺→ℕ index shift (see the premise
list below). It is a condition on
what Θ *derives*, with no reference to truth in ℕ; the paper notes at tex:604 that it
already forces Θ consistent, and `RepresentsComputations.consistent` is that observation.

**2. Both literals, from one sentence.** `represents_proves` and
`represents_refutes` / `represents_refutes_all` deliver the positive claim and its literal
negation from that class alone — no semantic hypothesis, only the `[𝗥₀ ⪯ T]` numeral
apparatus, which the premise itself supplies in substance. On the unbounded halting lane
less is needed still: the positive literal is Σ₁-completeness alone (`re_complete_mp`).

**3. A computable deductive process over Θ.** `paperTheoryDP T` enumerates Θ's theorems,
and its stage worlds are non-vacuous from consistency (`paperTheoryDP_nonvacuous`). What
each day-`n` claim is *about* is fixed by an argument written into the sentence — the
machine's source number and its input, packed and spelled by the compact Horner term
`binNumeral`, whose `O(log v)` symbol run is emitted digit by digit from the paper's own
write-out certificates `DigitMachineCodes` and `BigDigits`, which is what makes those two
hypotheses load-bearing on `def:ec`. What is *represented* is universal and fixed once per
theorem: the r.e. `universalHaltingSchema` on the unbounded lane, and one `γ` per horizon
program for the total `universalRunValue f` on the bounded lane — the paper's `⌜f⌝`. That
the family genuinely separates its data is proved, not assumed:
`haltingArgClaimSentence_ne_of_halts_ne` and `representedClaimSentence_ne_of_runValue_ne`
show that data differing in halting behaviour receive different claim sentences. Any future
represented claim family should carry the same witness.

**4. The property theorem over `LIA`.** `lia_learns_halting_patterns_unconditional`
(`thm:halts`), `lic_learns_provable_nonhalting_patterns_unconditional` (`thm:loops`),
`lic_does_not_anticipate_halting_unconditional` (`thm:dontwait`),
`lic_belief_finitistic_consistency_unconditional` (`thm:pac`) and
`lic_belief_stronger_theory_consistency_unconditional` (`thm:pazfc`) are stated over
`liaHistory (paperTheoryDP T)`. The bounded lane takes `[RepresentsComputations T]`; the
unbounded lane takes only `[Entailment.Consistent T]`, needing no *represented* negative
literal — `thm:loops`'s negative literal is its own `hloops` premise, which the paper
(`app:loops`) also assumes outright. The quotation family (`thm:ref`, `thm:lp`, `thm:st`,
`thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`) reaches its closed forms over
`theoremDP T` under `[Entailment.Consistent T]` in the same way, its two quotation schemas
being the value-`1` and value-`0` fibers of one Foundation `code` formula
(`universalQuoteCode`, `Framework/QuoteRepresentability.lean`), so that
`Θ ⊢ ∼(pos ⋏ neg)` is a theorem of Θ (`universalQuote_exclusive_prov`, from `code_uniq`
plus Gödel completeness) rather than a fact about ℕ.

**§4.10 belief in finitistic consistency.**
`lic_belief_finitistic_consistency_unconditional` (`thm:pac`) is stated at the paper's own
subject matter: for any computable horizon `f`, the constructed inductor's day-`n` price
of the arithmetized claim "no `Θ`-derivation of `⊥` has code below `f(n)`" tends to `1`.
The claim family is built from one representing formula per horizon — the formula
`RepresentsComputations` returns for the universal bounded-provability decider — with
`⌜⊥⌝` and the day written into the sentence as a compact numeral, so the family names the
theory and the day. That it does not collapse to a constant is a **theorem**, not a side
condition: `mentions_zero_of_repr_ne` derives `γ.Mentions 0` from the representation spec alone
whenever the represented decider is non-constant, and the Con lane discharges it at
`conGamma_mentions_zero`, with `conGamma_mentions_zero_of_bProv` and
`conGamma_mentions_zero_of_horizon_unbounded` as usable sufficient conditions and
`conGamma_mentions_zero_ackermann` fully discharged at the paper's own illustration. The only
boundary is degenerate and disclosed at the endpoints: at an eventually bounded horizon (in the
limit, constantly `0`) the decider is constant, and there a `γ` ignoring its argument does
represent it. It assumes no consistency hypothesis: consistency comes from the paper's
own representability premise, and the truth of every day's claim is derived from it. The
one disclosed substitution is `dd:proofcode` — the finite search is metered by the
derivation's Gödel number rather than the paper's symbol count, Foundation exposing no
symbol measure on internal derivations. `lic_belief_stronger_theory_consistency_unconditional`
(`thm:pazfc`) is the same construction at a second theory: it takes `Θ′` as a parameter with
the paper's own `Entailment.Consistent Θ′` as its premise, represents `Θ′`'s bounded-provability
decider **in `Θ`**, and is witnessed at `Θ = 𝗜𝚺₁`, `Θ′ = 𝗣𝗔` with horizon `fun n => ack n n` —
an inductor over a theory that cannot prove `Con(𝗣𝗔)` coming to believe every finite
consistency statement about it. `lic_disbelief_inconsistent_theories_unconditional`
(`thm:incons`) prices the paper's inconsistent-theory family, at the **deduction family**
`Θ′ₙ = Θ₀ ∪ {σₙ}` over a fixed Δ₁ base: the day's sentence is the universal provability schema
of `Θ₀` at the compact numeral `⌜∼σₙ⌝`, the premise `∀ n, ¬Consistent (σ n ∷ Θ₀)` is the
paper's own, and the two disclosed parts are the restriction to deduction families and the
code-metered `def:ec` premise (see *The one remaining qualified node* above).

**The premise is inhabited, and the instances are registered.**
`representsComputations_of_peanoMinus` (`Construction/Witnesses/R0Representability.lean`)
proves the class for any theory `U` with `[𝗣𝗔⁻ ⪯ U]` that is true in `ℕ`, and instances are
registered at **`𝗣𝗔⁻`, `𝗜𝚺₁` and `𝗣𝗔`**. Not at `𝗥₀`: Foundation's `code_uniq` is stated
for `𝗥₀` only inside a commented-out block, and `𝗥₀` has no trichotomy axiom, so the `rfind`
case of single-valuedness is unavailable there — `𝗣𝗔⁻` is the weakest theory in
Foundation's hierarchy for which the argument closes. Note the asymmetry, which is
deliberate: **verifying** the premise for a particular theory uses that theory's truth in
`ℕ` (through Gödel completeness and soundness), while **consuming** it never does. No
endpoint carries a semantic hypothesis on `T`; the concrete instances pay for themselves.
`AxiomAudit.lean` pins concrete instantiations at `𝗣𝗔⁻`, `𝗜𝚺₁` and `𝗣𝗔` so that a
regression would fail the build, and they are axiom-clean: Foundation proves
`Δ₁`-definability of `𝗜𝚺₁` and `𝗣𝗔` outright at the pinned revision
(`InductionSchemeDelta1.lean`), so a concrete instance reports the same three axioms as
everything else here.

**The residuals, named once.** Beyond the paper's own premise three binders appear, and all
three are representation infrastructure rather than theory strength:

* `[𝗣𝗔⁻ ⪯ T]`, on **17** of the 105 canonical endpoints — a finite set of ordered-semiring
  axioms, and the one item on this list that is a **genuine strengthening** rather than
  infrastructure. It is *not* implied by "Θ represents computations": the paper's premise
  yields `Θ ⊬ n̄ = m̄` for `n ≠ m` but never `Θ ⊢ n̄ ≠ m̄`, and Robinson's **R** represents
  every computable function without containing `𝗣𝗔⁻`. Two steps spend it — the compact
  `binNumeral` value transfer `def:ec` forces (`provable_subst_iff_of_val`), and
  `code_uniq`'s `rfind` case, which buys object-level fiber exclusivity at tag 7 and is the
  price of not assuming Σ₁-soundness there. The paper's own exclusivity argument is
  metatheoretic, through the representability biconditional, and needs no arithmetic inside
  Θ; ours is object-level so the stage-world proof stays constructive. **Whether this is
  charged globally or against each row is pending a ruling**, and no row's status turns on
  it today. (`lic_disbelief_inconsistent_theories_unconditional` used to carry a redundant
  `[𝗥₀ ⪯ T]` beside it; that binder was dropped in tranche 8 and the proof elaborates
  unchanged, reaching `𝗥₀` through Foundation's `instance [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T`, so no
  canonical endpoint carries it. `RepresentsComputations` also quantifies
  over `f : ℕ → ℕ` where the paper writes `ℕ⁺ → ℕ⁺` — an at-least-as-strong hypothesis.)
* `[T.Δ₁]` — a `Δ₁`-definable *axiom set*, where the paper asks only that Θ be computably
  enumerable. The two are not the same condition on `T` as presented: a c.e. axiom set need
  not be `Δ₁`. They are the same condition on the *theory*: by Craig's trick every c.e.
  theory has a deductively equivalent `Δ₁` (indeed primitive recursive) axiomatization, and
  every statement here is about `T ⊢ ·`, which such a re-axiomatization preserves. That step
  is not formalized; `[T.Δ₁]` is charged once, here, and does not lower a row.
* `[𝗜𝚺₁ ⪯ T]` — on **three** of the 105 canonical endpoints and no others.
  `lic_paradox_resistance_ofDiagonal_unconditional` (`thm:lp`) builds its paradoxical
  sequence through Foundation's `parameterized_diagonal₁`, which is stated over `𝗜𝚺₁`;
  `unitFracPaperLUVSeq` and `unitFracPaperLUVBoundedSequence` prove rational-cut arithmetic
  inside `T`. Both are places where the substrate's apparatus is indexed at `𝗜𝚺₁`, so this
  is charged with `[T.Δ₁]` and not against a row.

**Σ₁-soundness is gone from the whole development.** No declaration in `LogicalInduction/`
carries a `SoundOnHierarchy` instance binder, and **0 of the 105** canonical endpoints name
one — the paper treats soundness as a *further* assumption it explicitly declines
(tex:2673), and nothing here takes it. The only surviving occurrence of the name is
`loopsTheory_soundOnSigma1`, a fact about one concrete theory used as a non-vacuity witness
for `thm:loops`'s `hloops`. How the last consumption was retired is recorded in the
*Arithmetic-theory hypotheses* section of
[`scripts/coverage-classification.md`](../scripts/coverage-classification.md), together with
the per-row accounting.

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

   The retired `BoundedComputation` carrier was a genuinely different defect, and a
   syntactic one: the paper's sentence names the *term* `⌜f⌝(⌜n⌝)`, whereas that structure
   carried the *evaluated* horizon `steps n` inside the claim's input, which is why its
   value had to be polynomially bounded. The fix was not a better bound but a different
   claim schema, and that is what tranche 8 landed: `thm:pac` and `thm:pazfc` both sit on
   the arithmetized `Con(Θ′)` family of item 4 below, where the horizon is named by its
   *program* and evaluated inside the represented decider, and the structure — together
   with `SemidecidableComputation`, the corresponding carrier for `thm:incons` — has been
   deleted.

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

4. **Live — the proof-search measure (`dd:proofcode`).** §4.10's finite proof searches are
   metered by the **Gödel number of the derivation**, not by the paper's symbol count:
   `Con(Θ′)(ν)` is read as "no `Θ′`-derivation of `⊥` has code below `ν`"
   (`Framework/BoundedConsistency.lean`). Foundation's internal derivations expose no size
   function — `Semiformula.bv` measures a formula, not a derivation — so no symbol measure is
   available to state the paper's own bound. This is a disclosed type-`(c)` substitution: it
   changes *which* finite search each day names, and nothing else. The family's decidability,
   its `def:ec` emission and the truth of every instance are proved from consistency alone
   (`conWithin_of_consistent`), with no relation between the two measures assumed. **Queued
   for retirement** by the Foundation symbol-measure work (tranche 9a), after which the same
   statements hold with `ν` a symbol bound. It is the one thing standing between `thm:pac`
   and `thm:pazfc` and an unqualified `exact`, and it is charged globally, as `dd:fuel` is,
   rather than against those rows. It does not reach `thm:incons`, whose sentence is the
   *unbounded* existential over proofs: nothing is metered there, so the substitution does
   not arise.

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
