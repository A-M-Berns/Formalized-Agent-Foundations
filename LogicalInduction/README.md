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

The existence theorem is proved in the paper's full sense, and every named theorem and
lemma of the paper — 53 of them — is formalized, named after its paper label, and
build-audited. How strong each one is:

| | count | what it means |
|---|---:|---|
| **paper strength** | 51 | proved exactly as the paper states it — for every logical inductor, on the paper's own hypotheses |
| **qualified** | 2 | proved with an explicitly named representation interface or class restriction retained |

Each qualified node says in one line which premise it retains and why. The per-node
table is [`scripts/coverage-classification.md`](../scripts/coverage-classification.md),
machine-checked against the endpoint inventory so a node cannot ship without a strength
call. A browsable guide to the whole trust surface —
every paper statement rendered beside the Lean endpoint that carries it — is generated
from the repository at [`docs/trust-surface.html`](../docs/trust-surface.html)
(`python3 scripts/gen-trust-surface.py` to regenerate). That guide covers **all three**
formalized papers, one section each; only this paper's section carries per-node tiers,
reading notes and audit notes, because only this paper has the strength classification
they are read from. The others are correspondence views, and say so.

Of the 51, **20 are also instantiated over the concrete inductor constructed here** at
full paper strength, so they hold of a specific algorithm rather than a hypothetical
one. The paper states no such theorems; that is a strengthening, not a different degree
of faithfulness.

**Two caveats on those counts, because both are easy to miss.** First, every tier is
relative to the disclosed model — propositional sentences and fuel-clocked efficiency
(see *The two modeling boundaries*); "paper strength" means the paper's statement is
reached *within that model*, not that the model equivalence is proved. Second, the computation
family (`thm:halts`, `thm:loops`, `thm:pac`, `thm:pazfc`, `thm:dontwait`) still meters its
machine and input sequences by the **whole-value** class `PolyMachineCodes`/`PolyNatCodes`
rather than the symbol-metered `RpnSentenceCodes`; those are the paper's own e.c.
`⟨m⟩`/`⟨x⟩` sequences and the family is tiered uniformly on that basis. The whole quotation
family, and the horizon `f` of the metacomputation nodes, are at the paper's own class.

These numbers come from a signature-level re-derivation: 35 of the 53 nodes were
re-derived from their elaborated final signatures against the paper text in a dedicated
adversarial pass, which corrected 11 rows downward; the remainder carry classifications
from earlier passes, two of which that pass then corrected by propagation. Rows that have
since moved were re-derived again from the merged signatures. Where a count is uncertain
we have rounded against ourselves.

**Zero `sorry`, zero `axiom` declarations** — every public endpoint reports only Lean's
standard `propext`, `Classical.choice`, `Quot.sound`, enforced by the build
(`AxiomAudit.lean` enumerates the public surface and fails compilation on any
regression), and every paper-label citation is verified two-way by script. One
qualification to that, stated up front because it is easy to miss: see *One upstream
gap* below. The two declared modeling choices, and the planned future work that would
tighten them further, are described after it.

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

## One upstream gap

The theorems that quantify over an arithmetic theory — the quotation family (`thm:ref`,
`thm:lp`, `thm:epr`, `thm:er`, `thm:cee`, `thm:ceu`, `thm:ccee`, `thm:st`) and the
computation family (`thm:halts`, `thm:pac`, …) — are stated parametrically:
`(T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]`. As stated they are
axiom-clean, and the paper's own hypothesis is the same ("Θ represents computations").

But *instantiating* them at a concrete theory currently costs one upstream axiom:
Foundation provides `Δ₁`-definability of `𝗜𝚺₁` and `𝗣𝗔` only as `axiom
ISigma1_delta1Definable` / `axiom PA_delta1Definable`, marked *TODO: Prove* in
Foundation's own source. So a concrete instance of, say, `thm:st` over `𝗜𝚺₁` reports that
axiom, even though the parametric endpoint does not.

This is an upstream gap rather than a modeling choice here, and nothing in this
development assumes it — but it is invisible to a parametric axiom check, so
`AxiomAudit.lean` now pins it explicitly: it builds one concrete instantiation and
asserts it clean *except* for that named axiom. If Foundation proves `𝗜𝚺₁.Δ₁`, that
assertion starts failing and gets promoted to a plain clean assertion.

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

   **What this leaves.** Two statements whose *conclusion* is itself the criterion still
   sit at the fuel class, because they transport an arbitrary trader backwards across a
   market change and certify the transported trader in the fuel calculus:

   * **closure under conditioning** (`thm:scon`) — needs
     `MachineEfficientTrader Tr → MachineEfficientTrader (conditioning translation of Tr)`,
     a direct `Complexity.FP` transport theorem for the strategy serialization. Nothing is
     weakened meanwhile: the existing fuel-level theorem and its witnesses are unchanged.
   * **closure under finite perturbations** (`thm:ifp`) — the same shape, and separately
     under revision: the published unrestricted finite-day statement is overgeneral, since
     arbitrary finite-day perturbations can encode unbounded computational advice. The
     intended endpoint is a corrected finite-*support* theorem together with a formal
     counterexample to the unrestricted one, not a machine-strength restoration of the
     published statement. Its restricting interface `EfficientPrefixPatch` still has **no
     inhabitant anywhere in this repo**, so that endpoint has no exhibited witness for its
     own hypothesis.

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

   What remains charged to this item is narrow and stated where it bites: the abstract
   `LUV` carrier still admits threshold families that are not literal paper LUVs, which
   is why `def:blcp` — a combination sequence over that carrier — stays qualified, and
   the object-level value of a `PaperLUV` is named by a numerator/positive-denominator
   pair code rather than by a canonical rational arithmetic inside `ℒₒᵣ`.

   The historical record of this boundary, and of the source-dependent extension that was
   rejected before the frontend existed, is below and in
   [`notes/boundary-propositional-substrate.md`](notes/boundary-propositional-substrate.md).

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
   `lic_no_expected_net_update_conditional_closed_exact` has the same caller source class as
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
   as an exactly-reflecting one would. Details, and the rest of the compatibility
   surface, in [`notes/deference-compatibility.md`](notes/deference-compatibility.md).

The fuel model is no longer a modeling substitution: `def:ec` is the machine class, and the
fuel certificate is proved to imply membership in it. What is disclosed at the affected
statements is now the *residue* — the two machine-class transport theorems named above.

## What is left, and what it is blocked on

The `thm:ccee` qualification is closed by the fixed language-lift construction above, and
the efficiency-model boundary is closed by the machine-class migration. What remains is two
closure statements that sit at the fuel class for a specific, named reason.

**The two closure statements, and why they are not the efficiency boundary (2).**

Both are theorems whose *conclusion* is the criterion, so the machine ⟸ fuel bridge does not
reach them: their proofs transport an arbitrary trader backwards across a market change and
certify the transported trader. They stay at the fuel class, with nothing weakened and no
proved content withdrawn.

* **`thm:scon` — closure under conditioning.** The fuel-level theorem and its concrete
  witnesses (`GatedConditioningOperationalWitness`, `EventualConditioningOperationalWitness`)
  are unchanged and inhabited. The machine-level statement wants one new theorem:
  `MachineEfficientTrader Tr → MachineEfficientTrader (conditioning translation of Tr)`, a
  direct `Complexity.FP` closure result for the strategy serialization.
* **`thm:ifp` — closure under finite perturbations.** Same shape, and separately under
  revision. The published unrestricted finite-day statement is overgeneral: arbitrary
  finite-day perturbations can encode unbounded computational advice, so the intended
  endpoint is a corrected finite-*support* theorem together with a formal counterexample to
  the unrestricted one — not a machine-strength restoration of the published statement.
  Meanwhile, stated plainly because it is the sharpest disclosure on this page:
  `EfficientPrefixPatch` has **no inhabitant anywhere in the repo**, so
  `lic_iff_of_finitePerturbation` has no exhibited witness for its hypothesis, and the
  restricted statement must not be described as non-vacuous. (An earlier version of the
  errata ledger did so, citing a declaration that does not exist; corrected there.) The
  paper's own proof of `thm:ifp` is separately invalid — see erratum PE1.

## Closing the boundaries

The efficiency-model boundary has a scoped feasibility note, written against the
installed toolchain rather than against hypothetical APIs.

**Former Boundary 1 — the efficiency model.** Closed, by exactly the two-model
architecture this section used to propose: efficiency is defined at a genuine machine class
(`Complexity.FP`, from a pinned Lean-4.31 compatibility fork of `complexitylib`), the
trading firm enumerates that class through a finite `TMDesc`-plus-clock enumeration that is
both sound and covering, and the fuel calculus is kept as the certification tool through
the inclusion `EfficientlyComputable.toMachine`. The inclusion is a real compiler from
`Nat.Partrec.Code.evaln` to register machines with concrete bounds, not a simulation axiom;
the converse is not claimed. The staged history is in
[`notes/complexitylib-adoption.md`](notes/complexitylib-adoption.md), and the original
diagnosis in [`notes/boundary-efficiency-model.md`](notes/boundary-efficiency-model.md).

What remains from that programme is not the efficiency model but the two machine-class
*transport* theorems named above — conditioning and the corrected finite-support
perturbation — each of which asks for `Complexity.FP` closure under a specific trader
translation.

**Former Boundary 2 — the propositional substrate.** The historical diagnosis and the
rejected source-dependent extension remain documented in
[`notes/boundary-propositional-substrate.md`](notes/boundary-propositional-substrate.md).
The fixed language lift plus entailment-gated registry closes the endpoint without a
global first-order migration; see [`notes/semantic-source-repair.md`](notes/semantic-source-repair.md).

## Faithfulness

The current statement surface was checked by a fresh, current-state adversarial audit.
Its findings are a snapshot of the final signatures and verified obstructions, without
the superseded diagnoses or repair history of earlier passes:
[`notes/faithfulness-audit-2026-08-08.md`](notes/faithfulness-audit-2026-08-08.md).
Two of its findings have since been closed rather than merely disclosed: `thm:wubexp`
(B1) and exact `thm:ccee`. The historical audit carries dated resolution banners.
The process surfaced five errata in the paper itself, recorded with repairs in
[`notes/paper-errata.md`](notes/paper-errata.md).

`brouwer_fixed_point`, used by the market maker, was proved from scratch via Sperner's
lemma (Mathlib has no Brouwer theorem); its proof body was autoformalized by Harmonic's
Aristotle and kernel-revalidated here. Its statement and axiom report are audited
surface; the generated proof interior has not had a human line-by-line read.

## Layout

* `Framework/` — the paper's §2–3: sentences, markets, features, traders,
  exploitation, the criterion, efficient computability, expectations, and the shared
  asymptotic vocabulary.
* `Properties/` — the §4 property tail, one file per theorem family.
* `Construction/` — the §5 existence proof, with `Construction/Witnesses/` holding the
  constructed representation machinery that discharges the property tail's interfaces
  over the concrete inductor.
