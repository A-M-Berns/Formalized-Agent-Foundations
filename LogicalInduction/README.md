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
the emission surface they are consumed on. **One kind has no write-out class: LUV
thresholds.** `lic_iterated_expectations_ofCode_unconditional`,
`lic_expected_future_expectations_ofRepresentation_unconditional`,
`lic_no_expected_net_update_ofRepresentation_unconditional`, its `_conditional_` sibling,
and `lic_self_trust_ofRepresentation_unconditional` still take `RpnThresholdCodeSeq`,
which is symbol-metered rather than write-out. That is not a further restriction for the
paper's own first-order LUVs: `PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq`
(`Construction/Witnesses/StructuredPaperRpn.lean:1128`) proves every literal `PaperLUV`
sequence lands in the class, so the paper's data is admissible. What is not established is
whether some write-out-nameable threshold family falls outside it; the containment is
charged once at `def:ec` with the other symbol-metered classes and not re-levied per
row. Four of those containments are **proved
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
single shared reason, and it is a correction to what this file used to claim: their
canonical endpoints carry `[T.SoundOnHierarchy 𝚺 1]`, a **stronger** hypothesis than the
paper's. See *Instantiating the arithmetic-theory family* below, and the *Σ₁-soundness
premise* section of the classification ledger for the endpoint-by-endpoint blast radius
(19 of the 105 canonical endpoints) and for where the load-bearing use actually sits. The
universal layer of each of those nodes is free of the instance and remains at paper
strength; what is charged is the closed, over-`LIA` form that the trust surface shows.

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

The theorems that quantify over an arithmetic theory — the quotation family (`thm:ref`,
`thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`) and the
computation family (`thm:halts`, `thm:pac`, …) — are stated parametrically:
`(T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`. The endpoints are
axiom-clean as stated.

**That last instance is stronger than the paper's hypothesis, and this file used to say
otherwise.** The paper's standing assumption for §4.8 onward is that Θ is consistent,
computably enumerable, and *represents computations* — the representability theorem for
computable functions (tex:600-606, imposed for §4.8–§4.12 at tex:993-997). That implies
consistency but does not make Θ true in ℕ, and the paper says so in as many words at
tex:2673: "If we assumed further that Θ were sound as a theory of the natural numbers,
this would allow us to solve the halting problem…". Σ₁-soundness is that further
assumption. The paper's own proofs of `thm:halts`, `thm:loops` and `thm:dontwait`
(tex:4495-4520) use Σ₁-completeness and consistency only.

It enters because a decidable claim about a computation is represented here by an r.e.
Σ₁ schema (design note, `Construction/Witnesses/ComputationSyntax.lean:23-27`), reached
through Foundation's weak-representation lemma `re_complete`, which is *stated* under the
soundness instance; and because the stage world of the constructed process is built from
the standard model, so `theoremDP_hworld` keeps the positive and negative atom fibers
mutually exclusive by passing through truth — the `.mpr`, provable ⇒ true, direction. That
is the whole load-bearing use; every other `re_complete` call in the development uses the
`.mp` direction, which is only Σ₁-completeness. The eleven nodes this demotes to
`qualified`, and the endpoint-by-endpoint blast radius, are in the *Σ₁-soundness premise*
section of [`scripts/coverage-classification.md`](../scripts/coverage-classification.md).

Removing it — building the stage world from a model of Θ, so that fiber exclusivity comes
from Θ refuting false claims plus consistency, as the paper's own argument does — is under
investigation. Nothing here promises it.

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
   inhabited by a varying concrete family. See
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
