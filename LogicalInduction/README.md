# Logical Induction, formalized

A Lean 4 formalization of Garrabrant, Benson-Tilsen, Critch, Soares, Taylor,
[*Logical Induction*](https://arxiv.org/abs/1609.03543) (arXiv:1609.03543v5).

The existence theorem is proved in the paper's full sense, and every named theorem and
lemma of the paper — 53 of them — is formalized, named after its paper label, and
build-audited. How strong each one is:

| | count | what it means |
|---|---:|---|
| **paper strength** | 45 | proved exactly as the paper states it — for every logical inductor, on the paper's own hypotheses |
| **qualified** | 8 | proved with an explicitly named representation interface or class restriction retained |

Each qualified node says in one line which premise it retains and why. The per-node
table is [`scripts/coverage-classification.md`](../scripts/coverage-classification.md),
machine-checked against the endpoint inventory so a node cannot ship without a strength
call.

Of the 47, **16 are also instantiated over the concrete inductor constructed here** at
full paper strength, so they hold of a specific algorithm rather than a hypothetical
one. The paper states no such theorems; that is a strengthening, not a different degree
of faithfulness.

**Two caveats on those counts, because both are easy to miss.** First, every tier is
relative to the disclosed model — propositional sentences and fuel-clocked efficiency
(see *The two modeling boundaries*); "paper strength" means the paper's statement is
reached *within that model*, not that the model equivalence is proved. Second, three nodes
still have unconditional-over-`LIA` endpoints stated at a **whole-value-metered** class,
which this repo *proves* is strictly narrower than the paper's `def:ec`
(`ordinaryBitPrefixCodes` exhibits a paper-admissible e.c. family that no whole-value
hypothesis admits): the metacomputation family `thm:pac`/`thm:pazfc`/`thm:dontwait`. The
whole quotation family has now been restated at the paper's own symbol-metered class.

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
   instantiation over the constructed inductor.

   The model bites in a second, subtler place, and it is what keeps most of the
   qualified rows qualified. Within the fuel model there are two ways to meter a
   sentence sequence: by **symbol count** (`RpnSentenceCodes`) — the faithful reading of
   `def:ec`, and the paper's own cost measure — or by the **Gödel value** of the single
   pair-code token (`PolySentenceCodes`). These are not interchangeable: the same
   pathology proved in the domination section above (`not_polySentenceCodes_bitPrefixSentence`)
   exhibits a paper-admissible e.c. sentence family that the whole-value class provably
   excludes, so whole-value metering is a genuine restriction of the paper's class.

   The property tail is stated at the faithful symbol-metered class throughout, and so
   now are the *unconditional-over-`LIA`* endpoints for `thm:epr`, `thm:er`, `thm:ref`,
   `thm:cee`, `thm:ceu` and `thm:wub`. Four endpoints still sit at the narrower class:
   `thm:st`, and the metacomputation family `thm:pac`/`thm:pazfc`/`thm:dontwait`, where
   the analogous `PolyNatCodes` restricts the paper's "any computable function `f`" to
   polynomial-time `f`.

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

   `thm:st` is the one place in the quotation family with real content left: its product
   LUV inlines the sentence's Gödel value into a `Nat.pair` shell, so it needs a
   token-level `⋏` emitter rather than a restatement.

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

All three are disclosed at every affected statement, not just here.

## Planned future work

Each item has a verified obstruction on record; none blocks the results above.

* **An *exactly* reflecting general-source `thm:ccee`** — would remove the vanishing-slack
  substitution described under boundary 2. The mesh route (which landed, and which buys
  the paper's arbitrary source family) is approximate by construction. The exact route
  needs a world-dependent product-atom schema entered by the deductive process — a
  compound-axiom entry on the quotation presentation, comparable in scale to the existing
  quote-code layer. This is the one substitution with a known downstream consumer: work on
  deference in logical induction uses `thm:ccee` at general option-value LUVs, where
  whether the `1/(n+1)` slack is acceptable depends on the consuming argument.
* **An unevaluated-term claim schema for the metacomputation family** (`thm:pac`,
  `thm:pazfc`, `thm:dontwait`) — would restore the paper's "any computable function `f`".
  `computationClaimSentence` puts the claim's input *value* directly in the sentence code,
  so carrying the evaluated horizon `f(n)` forces `PolyNatCodes steps`. The paper instead
  names the term `⌜f⌝(⌜n⌝)` and lets the arithmetic schema evaluate it. The change is a
  claim schema whose input pairs `⌜f⌝` with `n` unevaluated, plus the corresponding
  `truth_iff` bridge — the sentence code is then polynomial in `n` for *any* computable
  `f`, which is exactly the paper's point.
* **A `c.e. → EfficientRepeatedEnumeration` constructor** — would lift `thm:obu` to the
  paper's actual hypothesis. The paper does the padding-and-repeating transformation
  inside its own proof (tex:5651-5656); here it is taken as data. Note the current
  structure's `sound` field forbids ⊤-padding, so the constructor needs a relaxed
  soundness condition alongside it.
* **An efficient prefix patch over the constructed inductor** — would lift `thm:ifp`
  from the efficiently-patchable restriction to the paper's unrestricted statement. The
  obstruction is the same fuel-class closure gap as boundary 1 (the emitted freeze
  stream's certificate needs a decode test on exponentially large codes, which the
  digit calculus provably does not close under), so closing boundary 1 would also close
  this. Note the paper's own proof of `thm:ifp` is separately invalid — see paper
  erratum PE1.
* **Close boundary 1** — the realistic route is a two-model architecture: define
  efficiency at a genuine machine class, let the trading firm enumerate it via
  poly-overhead universal simulation, and keep the fuel calculus as the certification
  tool through the easy inclusion (fuel-poly ⟹ machine-poly). A direct bridge theorem
  for the current class is judged unlikely: the fuel model lacks cheap poly-bit
  random-access state. A staged plan with effort estimates, scoped against what
  Mathlib actually provides, is in
  [`notes/two-model-ec-feasibility.md`](../notes/two-model-ec-feasibility.md).

## Faithfulness

The statement surface was hardened by fresh-context adversarial audit (independent
auditors plus a cross-family model check) and a fix wave that repaired every finding at
the statement level or pinned it to a verified obstruction; the finding-by-finding
ledger — including its own corrected misjudgments — is
[`notes/faithfulness-audit-2026-07-28.md`](../notes/faithfulness-audit-2026-07-28.md).
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
