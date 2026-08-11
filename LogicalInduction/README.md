# Logical Induction

A Lean 4 formalization of Garrabrant, Benson-Tilsen, Critch, Soares, Taylor,
[*Logical Induction*](https://arxiv.org/abs/1609.03543) (arXiv:1609.03543v5).

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
every paper statement rendered beside the Lean endpoint that carries it, with its tier
and audit note — is generated from the repository at
[`docs/trust-surface.html`](../docs/trust-surface.html)
(`python3 scripts/gen-trust-surface.py` to regenerate).

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
* `LIA_is_logical_inductor` — the concrete recursively-constructed rational market
  built here (the paper's §5 algorithm: market maker via a from-scratch Sperner/Brouwer
  fixed point, budgeter, trading firm over a universal trader enumeration) satisfies
  the criterion.

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

## The two modeling boundaries

1. **Efficient computability is a fuel-clocked interpreter model, not a machine
   complexity class.** Traders and every "polynomial" certificate are metered by
   Mathlib's clocked interpreter `Nat.Partrec.Code.evaln` under a polynomial fuel
   bound. The model card (`Framework/Computable.lean`) proves its calibration facts
   and states the open question plainly: there is no theorem that every
   polynomial-time trader in the paper's sense lands in this class. Precisely: the
   existence theorem defeats this class rather than the paper's, and is weaker than the
   paper's `thm:li` if the inclusion fails. For the property tail the choice is
   conservative wherever a theorem's exploiting trader is constructed and certified
   inside the class — which is everywhere except **closure under finite perturbations**
   (`thm:ifp`), whose transported trader needs a fuel-class closure property the model
   provably lacks (the inverse-operation ceiling on the digit calculus), so that
   endpoint stays restricted to efficiently patchable market prefixes and has no
   instantiation over the constructed inductor. Sharper than that, and worth stating
   because it is easy to read past: the restricting interface `EfficientPrefixPatch` has
   **no inhabitant anywhere in this repo**, so that endpoint currently has no exhibited
   witness for its own hypothesis. It is the one place on this page where a theorem is
   stated but not yet shown to be about anything.

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
2. **The logical substrate is propositional.** Sentences are Foundation's
   propositional formulas; the paper's first-order theory Θ enters through explicit
   interfaces, instantiated by arithmetic theories for the unconditional endpoints. In
   particular a logically uncertain variable (LUV) is presented by its family of
   threshold sentences `⌜X > r⌝`, with its world-value semantics carried as explicit,
   build-frozen certificate structures rather than derived from first-order syntax.

   This boundary has one consequence sharp enough to name on its own.
   **`thm:ccee`'s quoted product is realized only to within `1/(n+1)`, not exactly.**
   The paper's quoted product `⌜Xₙ · w_{f(n)}⌝` is a first-order term, whereas here a
   product LUV must be built from threshold sentences, and an *exact* one needs either the
   value of `w_{f(n)}` (unavailable to an emitter: the weight is only P-generable, and
   deferred, and the resulting threshold's denominator is not polynomially sized) or the
   infinite disjunction `⋁_{s∈ℚ} (⌜w > s⌝ ∧ ⌜X > r/s⌝)` — the existential the propositional
   substrate lacks. What *is* emittable is the finite **mesh** product
   `⋁_{j<n+1} (⌜w_{f(n)} > j/(n+1)⌝ ∧ ⌜Xₙ > r(n+1)/(j+1)⌝)`, built only from the deferred
   weight's own threshold atoms; it values the product within `1/(n+1)`. So
   `ConditionalExpectationQuote.left_reflected` is a **vanishing-slack** condition rather
   than an equation — a declared type-`(c)` substitution — and in exchange the fully-closed
   endpoint `lic_no_expected_net_update_conditional_closed` takes the paper's arbitrary
   e.c. source family. The slack is inert downstream: it enters the exploiting trader's
   block-price bound additively beside the existing `1/(m+1)` grid errors, and the
   conclusion is unchanged in form. Non-vacuity is witnessed at both ends — the mesh
   inhabits the relaxed field for a general source, and the indicator product still
   inhabits it at zero slack (`indicatorProductLUV_exact_left_reflected`).

   **The slack is invisible at the one known downstream interface.** The deference port
   of "Deference Done Better" into this framework consumes `thm:ccee` as a hypothesis
   `hCcee : Approx Exw Eew` — two abstract real sequences related by `≈ₙ`, with no LUV
   structure, no deductive process, and no slack term crossing the boundary. The mesh
   endpoint's conclusion has exactly that shape, so it discharges the hypothesis as well
   as an exactly-reflecting one would. Details, and the rest of the compatibility
   surface, in [`../notes/deference-compatibility.md`](../notes/deference-compatibility.md).

All three are disclosed at every affected statement, not just here.

## What is left, and what it is blocked on

Both remaining qualified nodes trace back to the two modeling boundaries; there is no
longer a third that is merely unfinished. (`thm:wubexp` was that third one. Its route —
build the mesh feedback bridge from the *approximate* determination that combination-level
`def:affthmval` actually supplies, rather than from a per-component-LUV strengthening — is
now landed; see `FeedbackTruth.luv_wubexp_ofComputation`.) Estimates are engineering
judgment, not measurements — the ones marked *checked* were made after confirming the
required lemmas exist, and the rest are structural reads that have twice moved upward on
contact.

**Blocked on a disclosed modeling boundary (2).**

* **`thm:ccee` — the propositional substrate.** An *exactly* reflecting product LUV needs
  either the deferred weight's value (unavailable to an emitter: only P-generable,
  deferred, and the resulting threshold's denominator is not polynomially sized) or the
  infinite disjunction `⋁_{s∈ℚ}(⌜w > s⌝ ∧ ⌜X > r/s⌝)`. Propositional logic has neither, so
  the landed mesh product reflects only to within `1/(n+1)`. The exact route is a
  definitional extension of the *deductive process* — fresh product atoms plus their
  defining biconditionals — not of the theory, and its first four components are built
  (`Construction/Witnesses/ProductDefinition.lean`: the process, its computability, the
  world-extension lemma, threshold emission, and exact reflection at `slack = 0`). What
  is not built is the closed endpoint, and the reason is named rather than estimated:
  the weight's quote LUV needs `Computable (w ∘ f)`, which `PGenerableRat.computable`
  supplies only from a market that is itself a function of the process. Escaping that
  circle costs either a narrowing of `w` to `PolyRatCodes` — which would drop the
  paper's own worked example at tex:2077, a continuous indicator of a market
  expectation, and is therefore worse than the slack it removes — or a second
  P-generability premise about the extended market. Two further costs are known: the
  endpoint would be stated over `base ∪ product-definitions` (a rendering with Tier-1
  precedent in `lic_conditioned_gated_ofComputations`, but not for this use), and an
  atom-freshness premise the paper does not state. Full assessment in
  [`../notes/boundary-propositional-substrate.md`](../notes/boundary-propositional-substrate.md). The one known
  downstream consumer does **not** need exactness — see the interface note above — so
  the mesh endpoint keeps the row.
* **`thm:ifp` — the fuel class.** The transported trader needs a closure property the
  model provably lacks (the inverse-operation ceiling: the emitted freeze stream's
  certificate needs a decode test on exponentially large codes, which the digit calculus
  does not close under). Closing boundary 1 closes this and nothing smaller does. Stated
  plainly, because it is the sharpest disclosure on this page: `EfficientPrefixPatch` has
  **no inhabitant anywhere in the repo**, so `lic_iff_of_finitePerturbation` currently has
  no exhibited witness for its hypothesis — the restricted statement must not be described
  as non-vacuous until one is built. (An earlier version of the errata ledger did so, citing
  a declaration that does not exist; corrected there.) The paper's own proof of `thm:ifp` is
  separately invalid — see erratum PE1.

## Closing the boundaries

Each of the two modeling boundaries has a scoped feasibility note, written against what
the installed toolchain actually provides rather than against what one might hope for.
Both conclude that the boundary is real; they differ in what it would cost and in what
closing it would buy.

**Boundary 1 — the efficiency model.** The realistic route is a two-model architecture:
define efficiency at a genuine machine class, let the trading firm enumerate it via
poly-overhead universal simulation, and keep the fuel calculus as the certification tool
through the easy inclusion (fuel-poly ⟹ machine-poly). A direct bridge theorem for the
current class is judged unlikely — the fuel model lacks cheap poly-bit random-access
state. Closing it would free `thm:ifp`, the one endpoint whose restricting interface has
no inhabitant, and would retire the calibration caveat that qualifies every efficiency
certificate on this page. The staged plan, the two places Mathlib stops short (no timed
simulation theory; `FinTM2` not enumerable as-is), and the effort estimate are in
[`notes/boundary-efficiency-model.md`](../notes/boundary-efficiency-model.md).

**Boundary 2 — the propositional substrate.** Here the note reaches a sharper and less
expected conclusion: upgrading the substrate to first-order sentences would be
research-scale *and would not buy what it appears to buy*. The paper's own `def:world`
builds worlds by Boolean algebra over **prime sentences**, so this repo's propositional
worlds are a faithful rendering of the paper's, not an approximation of them; and the
paper's quoted product `⌜Xₙ · w > r⌝` is itself a prime sentence, so what relates it to
`⌜Xₙ > r/s⌝` is not first-order syntax but **Θ**. The tractable move is therefore to
supply those relating facts through the deductive process, which is the exact-valuation
route — built as far as its own binding constraint, with that constraint named. What
closing this boundary would and would not free, and the worked `thm:ccee` instance, are in
[`notes/boundary-propositional-substrate.md`](../notes/boundary-propositional-substrate.md).

## Faithfulness

The current statement surface was checked by a fresh, current-state adversarial audit.
Its findings are a snapshot of the final signatures and verified obstructions, without
the superseded diagnoses or repair history of earlier passes:
[`notes/faithfulness-audit-2026-08-08.md`](../notes/faithfulness-audit-2026-08-08.md).
One of its findings has since been closed rather than merely disclosed — `thm:wubexp`
(B1), which is why the counts above read 51/2 where that snapshot reads 50/3; the finding
carries a dated resolution banner.
The process surfaced five errata in the paper itself, recorded with repairs in
[`notes/logical-induction-paper-errata.md`](../notes/logical-induction-paper-errata.md).

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
