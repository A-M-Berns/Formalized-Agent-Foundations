# Boundary 2 — the propositional substrate: what closing it would cost

> **Superseded resolution (2026-08-21).** The historical source-dependent extension
> assessed below remains correctly rejected, but its claimed exhaustiveness was wrong.
> `SemanticLiftedCCEE.lean` uses a fixed old-language atom injection plus an executable
> finite-entailment gate to admit every raw `RpnThresholdCodeSeq` source satisfying the
> paper's completed-world `source_valued` premise. One canonical non-vacuous process is
> fixed from `T` before the source, deferral, or weight; exact semantic multiplication then
> gives zero slack. The endpoint of record is
> `lic_no_expected_net_update_conditional_closed_exact`. The analysis below is retained as
> the record of why `productDefDP` itself was not a faithful solution.

_2026-08-08. Two questions, answered against the installed toolchain and the paper text:
what would it take to close this boundary outright, and what does the one endpoint it
blocks (`thm:ccee`) actually cost to fix? Every claim about what an endpoint takes or
calls was made with the signature or the proof body open, and every named lemma was
`rg`-confirmed to exist at the cited line._

## Resolution (2026-08-11) — the route is built, and adjudicated *not* a `thm:ccee` rendering

**Read this before the rest of the note.** Everything below §(D) was written while the
exact route was a proposal and while (C) and (A2) were open questions. Both have since been
answered, and the answer to (C) is **no**. The assessment below remains useful as the
engineering record; its *recommendation* is superseded by this section.

### What was built

§(D)'s work plan was carried out: `productDefDP_computable` now follows from the source
families' own `def:ec` certificates (the named `LUVThresholdComputation` of §(A1) is
deleted), freshness is proved by construction for the base stages and the weight quote LUV
(§(B)), `QuotationTheoryPresentation.mono` lifts the presentation along `DP ⊆ DP'`, the
market-dependent quote codes are market-parametric, and the closed statement
`lic_no_expected_net_update_conditional_exact_closed` is green with clean axioms, with a
jointly satisfiable premise set exhibited by `..._nonvacuous`.

§(A2) was **pessimistic** on one point and it is worth recording: it says the plan's route
"is circular in the closed setting", and it is, but the escape is cheaper than the note
implies. The weight quote is built against the **base** market, which exists before the
extended process does, so only the certificate's `weight_generable` field needs the extended
market. That is option 2, and it costs exactly one premise.

### The ruling on (C): rejected

A cross-family adjudication on 2026-08-11 (question: certify or reject the union rendering
as a representation of `thm:ccee`; rank the three renderings; name any missed route)
returned **rejected**, on grounds this note's own §(C) "Against" column had gestured at but
underweighted:

> Rendering (2) proves an exact result for a different constructed inductor,
> `LIA(base ∪ product-definitions)`, not for `LIA(base)`. **Conservativity of completed-world
> truth does not imply equal logical-inductor prices or conditional expectations.** It also
> retains `ProductAtomFresh`, a real restriction on arbitrary e.c. `X` in the flat-atom
> model.

This is correct and it is the decisive point. `productDefDP_union_consistentWithTheory`
proves the extension adds no completed-world commitments in the base language; §(C)'s "For"
column then slid from that to treating the extended endpoint as *about* the same subject
matter. It is not. A logical inductor's prices are not determined by its process's
completed-world truth, and no market-preservation correspondence for conservative extensions
is proved anywhere in this repository — nor is one available cheaply.

The ranking returned was **mesh > extension > weight-narrowing**: the mesh result "remains
about the intended base inductor and arbitrary source class"; the extension is "a useful
exact extended-process instance, but not a replacement"; narrowing `w` "excludes the paper's
motivating P-generable weight example". That confirms §(A2)'s judgment against option 1 and
overturns the recommendation ordering at the end of this note.

The missed fourth route named by the adjudication, recorded here because it is the only
identified way to actually move the row:

> Retain the base-market theorem and formulate an abstract exact-product representation
> theorem over that same base process, with exact reflection as an explicit premise. To
> discharge it generally requires a richer typed/term syntax (or a proved
> market-preservation correspondence for a conservative extension); merely changing the
> deductive process cannot establish the base market's expectations.

### What the built material is now for

It is kept, and repositioned as the **obstruction-closure demonstration** for this boundary:
proof that the mesh endpoint's `1/(n+1)` slack is an artifact of the propositional substrate
rather than of logical induction, since the same trader and the same criterion give an exact
conclusion the moment the product exists syntactically. Its docstrings, the `thm:ccee`
coverage row, the README entry and the audit delta all now say — in those words — that it
establishes nothing about the base inductor's conditional expectations, and all state the
two costs it pays that the mesh endpoint does not (the freshness restriction on the source
class, and `def:pgen` at the extended market).

`lic_no_expected_net_update_conditional_closed` is and remains the `thm:ccee` endpoint of
record. The row stays `qualified`. The boundary is now **fully mapped**: mesh = the maximal
faithful statement about the inductor the paper is talking about; demonstration = proof that
the residual is substrate-shaped. That is a settled state, not pending work.

The one piece of the delivered work that is independent of all this, and stays regardless:
the market-parametric `deferredWeightQuoteCode` / `conditionalExpectationQuoteCode` and
`liaMarketComputation` in `QuoteCodeOfMarket.lean` / `ComputationDP.lean` are pure
generalisations, with the `theorem…`-prefixed names surviving as their specialisations at
the base market with unchanged signatures.

## Part 1 — closing the boundary outright: expensive, and aimed at the wrong mechanism

The obvious reading of this boundary is "sentences should be first-order, and then the
quoted product would be a term, and `thm:ccee` would be exact for free." That reading is
wrong twice over, and it is worth recording why before anyone prices the work.

**The paper's own worlds are propositional.** `def:world` (tex:727) calls a world p.c.
iff `W(φ)` "is determined by Boolean algebra from the truth values that `W` assigns to the
prime sentences of `φ`", and `pcworlds`/`cworlds` are built from that. This repo's
`Sentence := Propositional.Formula ℕ` and `PCWorld := Boolean.Valuation ℕ` — with atoms
already being codes — render exactly that. The world notion is not the gap.

**First-order syntax would not dissolve the `thm:ccee` obstruction.** ~~In the paper,
`⌜Xₙ · w_{f(n)} > r⌝` is a *prime* sentence — propositionally an atom, just as here. What
relates it to `⌜Xₙ > r/s⌝` is not the term structure but **Θ**, which contains arithmetic
and proves the relating facts. So the paper gets those facts free from its theory; this
repo has to supply them. That is a question about the deductive process, not about the
formula type, which is why Part 2's route is the tractable one.~~
*Corrected 2026-08-11 by the dedicated feasibility spike
([`boundary-substrate-fol-scope.md`](boundary-substrate-fol-scope.md) §6.2): this claim
is wrong on the emitter half.* What the propositional substrate lacks is not the product
*term* but **deferred denotation** — a sentence that names a value without computing it.
A first-order `LUV` (a formula free in one variable, `def:luv` verbatim) lets the emitter
write `⌜Xₙ · w_{f(n)} > r⌝` as a sentence whose threshold family is emitter-computable
even though `w`'s value is not, which is exactly what the A2 circularity below is about.
The prime-sentence half of the old claim stands: worlds stay Boolean-over-primes either
way, and Θ still supplies the relating facts.

**And the cost would be research-scale.** ~~`Sentence` is touched by 68 of 77 files~~ —
*that figure counted mentions; the spike's structural census
([`boundary-substrate-fol-scope.md`](boundary-substrate-fol-scope.md) §2.1) finds 36 of 82
files carrying propositional structure (~2× smaller blast radius), concentrated in two
clusters: the emission calculus (which cannot be deferred) and the Boolean-world layer
(which transports along a change of atom type).* The migration **is** stageable in
principle (the spike's plan has five stages) — but its middle is *regressive*: between
prime-atom refinement and the rebuilt FO emission calculus, the repo would carry an
**empty** emission class, an uninhabitable state worse than today's disclosed slack.

**Verdict: do not close this boundary** — unchanged, now for the spike's sharper reasons
(10–20 months, half of it Foundation-side work; no green stopping point before the end;
the payoff inert at the one known consumer). If the direction is ever taken, the first
move is a Foundation PR for strong representability, not a repo refactor. Supply the
missing relating facts through the process instead; what that costs is Part 2.

## Part 2 — the `thm:ccee` exact-valuation route, and why it is shaped this way

The goal is to replace the mesh product's `1/(n+1)` reflection slack — the one type-`(c)`
substitution with a known downstream consumer — by **exact** left reflection for an
arbitrary e.c. source family, i.e. a `ConditionalExpectationQuote` at `slack ≡ 0`.

Three facts fix the shape, all verified against the code:

1. **The master theorem needs no change.** `lic_no_expected_net_update_conditional`
   (`Properties/SelfTrust.lean`) is deductive-process generic and consumes slack through
   `slack_tendsto`; `slack ≡ 0` is a special case.
2. **The certificate needs no change.** `ConditionalExpectationQuote`'s `slack` field
   already admits `0` — `indicatorProductLUV_exact_left_reflected` inhabits it there for
   indicator sources. No `#assert_fields` churn.
3. **The extension is of the deductive process, not of the theory.** The blocker was
   always the *emitter*: it cannot know `w (f n)`. But a deductive process is only
   required computable, so it can enter defining biconditionals for fresh product atoms
   directly. Propositionally this is exactly a definitional extension — fresh atoms plus
   explicit definitions — which is why no new `T`-provability or internalization is
   needed. The paper's first-order `Θ` contains the product *term* natively; this is its
   propositional counterpart.

What is built (`Construction/Witnesses/ProductDefinition.lean`): the fresh-tag process
and its computability, the world-extension lemma, threshold emission, exact reflection at
`slack = 0`, and the non-closed endpoint
`lic_no_expected_net_update_conditional_exact`. The schema actually used is a **pair
schema** over `(s,t)` guarded by `r ≤ s·t` / `s·t ≤ r`, which never names the weight's
value — a change forced by the circularity described in (A2) below, and one that also
removes the `w = 0` case split the obvious schema needs.

## The bar being assessed

`scripts/coverage-classification.md` line 81: `thm:ccee` is `qualified`, and what keeps it
below `instantiated` is **only** the `1/(n+1)` slack — "a declared type-`(c)` substitution
rather than a class restriction". The incumbent
`lic_no_expected_net_update_conditional_closed` is closed over the constructed `LIA`,
unconditional, at the paper's arbitrary e.c. source family, with premises exactly those
`thm:cee` carries. So the exact endpoint takes the row only if it removes the slack **and
gives up nothing else**.

Short answer: **the union rendering and the freshness premise are both defensible as
already-charged (details in (B), (C)), but the weight `w` is not.** There is a
circularity in the closed setting that forces one of two non-zero costs on `w`. That is
the finding that decides this.

---

## (A) Is `_closed` reachable?

**Reachable, but not premise-free on the weight.** Two independent sub-questions.

### A1. The source/weight threshold emitters — reachable, and *cheaper than planned*

The process needs to emit `(X n).gt s` and `(W n).gt t`. I built this from a new named
structure `LUVThresholdComputation` (`ProductDefinition.lean`), and
`productDefDP_computable` is green with clean axioms. **That structure should not
survive**, and the plan's worry about "one small caller-facing structure — Tier-2
addition, `#assert_fields` entry" (plan, Risks) is unfounded:

* `RpnSentenceCodes.primrec` (`Construction/LIACompiler.lean:3285`):
  `RpnSentenceCodes φ → Primrec fun n ↦ Encodable.encode (φ n)`.
* `RpnSentenceCodes.exists_code` (`LIACompiler.lean:3301`): the same as a named
  `Nat.Partrec.Code` (already used this way by `conditionedQuoteCode`,
  `ConditioningCompiler.lean:151`).
* `LUV.RpnThresholdCodeSeq X` **is** `RpnSentenceCodes (fun m ↦ (X m.unpair.1).gt (i/k))`
  at index `⟨n,⟨k,i⟩⟩` (`Framework/Expectations.lean:95`).
* `ratNum_prim` / `ratDen_prim` (`LIACompiler.lean:431,436`) convert a nonneg rational to
  its `(den, num)` index, and the schema only ever needs `s, t ≥ 0`.

So: re-index the schema's `s` and `t` by `(k,i)` instead of by an encoded rational, and
`ComputableDeductiveProcess (productDefDP X W)` follows from
`hX : LUV.RpnThresholdCodeSeq X` and `hW : LUV.RpnThresholdCodeSeq W` — **exactly the
premises the mesh endpoint already carries**. No new caller-facing certificate, no
`#assert_fields` entry. `ComputableDeductiveProcess` is a `Prop` (`∃ code`), so the
`∃`-shaped premises suffice; nothing needs to be data.

The rest of the closed-form plumbing is present and unblocked:

* `DeductiveProcessComputation.union` / `.union_toComputable`
  (`ConditioningPresentation.lean:112,130`), then `LIA_is_logical_inductor`
  (`LIACompiler.lean:7273`) gives `IsLogicalInductor (liaHistory (union)) (union)`.
* `hworld` is already proved: `productDefDP_union_consistentWithTheory` plus
  `theoremDP_hworld T` (which is literally `ConsistentWithTheory` pointwise).
* `QuotationTheoryPresentation`'s quotation fields are `∃ k, … ∈ DP.D k`, monotone under
  `DP ⊆ DP'`; lifting `quotationPresentation T` to the union is a small new lemma, no
  obstruction found.

One *non-additive* consequence: `theoremMarketComputation`,
`theoremDeferredWeightQuoteCode` and `theoremConditionalExpectationQuoteCode`
(`QuoteCodeOfMarket.lean:1050,1061`) are stated at `theoremDP T` specifically. The closed
exact endpoint needs their analogues at the union process. They are parametric in
`MarketComputation P` internally, so the fix is to weaken `theoremDP T` to a parameter —
mechanical, but it edits `QuoteCodeOfMarket.lean`/`ComputationDP.lean` and therefore
breaks the "everything additive, easy to exclude" isolation constraint. Duplicating them
in `ProductDefinition.lean` instead would violate consolidation discipline. This is a
sequencing decision, not an obstruction.

### A2. The weight `w` — a genuine circularity, and it costs something

This is the finding that decides the assessment.

`productDefDP X W` needs `W`, a LUV family whose completed-world value is `w (f n)`. The
only such family available propositionally is a quotation-atom family, i.e.
`(theoremDeferredWeightQuoteCode …).luv`, whose construction runs
`RationalQuoteCode.ofComputable` and therefore needs `Computable (fun n ↦ w (f n))`.

The plan proposes getting that from `PGenerableRat.computable`
(`BoundedEvaluation.lean:1461`), which needs a `MarketComputation P` for the market `w` is
generable against. But the endpoint is stated over `liaHistory (theoremDP T ∪ productDefDP X W)` —
so the market is a function of the process, and the process is a function of the market.
**The plan's route is circular in the closed setting**, and the pair schema I landed
(which never names `w`'s value) does not fix this: the circularity is in `W`'s
*construction*, not in the schema.

Breaking it costs one of:

1. **Narrow `w` to `PolyRatCodes` (e.c. rationals).** Then `Computable w` is immediate and
   `PGenerableRat P w` holds for *every* `P` via `ratCodeFeature_generated`
   (`QuotationAffine.lean:877`). Clean, fully closed — but it is exactly a **class
   restriction**, the thing the row header says lowers a tier, and it excludes the paper's
   own motivating example for `thm:ccee` (tex:2077: `w_n = ctsind_{δ_n}(𝔼_{f(n)}(X_n) > 0.7)`,
   which depends on the market's own prices and is P-generable, not e.c.). **This loses
   more than the slack does.**

2. **Carry P-generability twice.** Take `PGenerableRat (liaHistory (theoremDP T)) w` — the
   incumbent's own premise, against the *base* market — to build the quote code and hence
   `W` and hence the union process; then take
   `PGenerableRat (liaHistory (theoremDP T ∪ productDefDP X W)) w` separately for
   `ConditionalExpectationQuote.weight_generable`. No circularity, `w` stays `def:pgen`.
   Cost: one extra premise, about a market the caller cannot easily reason about, where the
   incumbent has one.

   The second premise cannot be derived from the first: a `GeneratedRatFeature`'s
   `denote` field is evaluated *at the history*, and the union market's prices differ from
   the base market's. Nor is it derivable from computability — `ratCodeFeature_generated`
   needs `PolyRatCodes`, not `Computable`.

   It also cannot be dropped: `weight_generable` is a frozen field of
   `ConditionalExpectationQuote` (Tier-2 `#assert_fields`). It is inert in the proof —
   `lic_no_expected_net_update_conditional` (`SelfTrust.lean:365`) uses only
   `hquote.affine` — but it must still be supplied.

3. A simultaneous process/market fixed point. Not available and not worth pricing.

**So the exact closed endpoint cannot be premise-neutral on `w`.** Option 2 is the honest
choice (it keeps `def:pgen`), and its cost is small but real and must be disclosed.

---

## (B) Can `ProductAtomFresh` be discharged by construction?

**Partly — and the residue is the substrate boundary, not a new modeling choice.**

The premise (`ProductDefinition.lean`) is: no atom of `(X n).gt r` carries `productTag`.
It is used in exactly one place, `productExtensionWorld_holds_schema`, to know that
reassigning the product atoms does not change the world's verdict on `X`'s and `W`'s own
thresholds. It is **not** an artifact: an adversarial `X` with
`(X n).gt s = ∼productAtom n r` makes a stage genuinely unsatisfiable, so without it the
union process has no consistent world and the endpoint would be vacuous.

What can be discharged by construction:

* **The base stages.** `(theoremDP T).D k` is an image of `eventAtom`, whose atoms are
  `computationClaimSentence` (tags `0`–`3`, `ComputationSyntax.lean:196`) and `quoteAtom`
  (tag `4`, `QuotationAffine.lean:39`). `productTag = 5`. So the base-stage half is a
  short lemma, not a premise. Same for `W` in the closed setting: it is a quotation-atom
  family, tag `4`.
* **`X`.** Not dischargeable. `LUV.RpnThresholdCodeSeq X` constrains only the *size* of
  `X`'s threshold blocks, never which atoms they mention; a poly-fueled emitter can emit
  tag-`5` atoms. So for a genuinely arbitrary e.c. `X` this must be assumed.

Where it is automatic: every family this repo constructs (`arithmeticThresholdLUV`,
`indicatorProductLUV`, `meshProductLUV`, `ComputableLUV.toLUV`, the quote LUVs) — all
built from tags `0`–`4`.

**Why I think this is already-charged rather than a new class restriction.** In the paper
the product is a *term* over Θ's signature and the definitional extension introduces a new
function symbol; a source LUV in Θ's language then cannot mention it, freshness being
guaranteed *by the language*. Propositionally there is one flat atom space, so the same
fact has to be written down as a side condition. Freshness is not an extra modeling
assumption — it is the first-order guarantee, re-stated in a substrate that has no
signatures. That is precisely what README §"The logical substrate is propositional"
already discloses.

A hostile reader's counter, which I think is answerable but should be recorded: the
substrate disclosure is about *LUVs being threshold families*, and this is a new
consequence of it (atom-space collision) that the disclosure does not currently name. If
we take this route the disclosure paragraph has to be rewritten to name it, exactly as it
now names the slack.

---

## (C) Is the union rendering a second rendering, or already charged? — the crux

**I believe it is already charged, and the coordinator's precedent check is incorrect on
one point.**

### Correction: there *is* union-DP precedent, at `instantiated`

`lic_conditioned_gated_ofComputations` (`ConditioningPresentation.lean:222`) is a Tier-1
inventory endpoint (`AxiomAudit.lean:394`) whose **conclusion** is
`IsLogicalInductor (conditionedHistory P …) (DP.union extra)`. `thm:scon` is classified
**instantiated** (`coverage-classification.md:120`). `DeductiveProcess.adjoinSentence`
(`ConditioningPresentation.lean:192`) is a union too. So the repo's tiering demonstrably
does not penalize a union-DP rendering per se.

The disanalogy is real and should be stated: in `thm:scon` the union *is* the paper's own
construction (the paper conditions on a new theorem set), whereas here the union is our
device for something the paper gets from its term language. The precedent establishes that
the *shape* is acceptable, not that this *use* of it is.

### For "already charged"

* The paper's `⌜X_n · w_{f(n)}⌝` is a first-order term; there is no term former in
  `Formula ℕ`. The faithful propositional counterpart of a term denoting a defined value
  is a fresh atom plus its defining axioms, and the deductive process is the only place
  axioms can be added (the theory interface is fixed). So the union is not a shortcut
  around a proof — it is the propositional *translation* of what the paper already has.
* ~~`thm:ccee` in the paper quantifies over deductive processes: it holds for every logical
  inductor over every computable Θ. `theoremDP T ∪ productDefDP` is a computable deductive
  process, so the exact endpoint is a legitimate instance of the paper's own theorem, not a
  weakened variant of it.~~ **This is the argument the 2026-08-11 adjudication overturned;
  see the resolution section at the top.** It is a true statement about *which theorem is
  being instantiated* and a false one about *what the instance tells you*: `thm:ccee` at
  `D′ = base ∪ product-definitions` is a claim about `LIA(D′)`'s conditional expectations,
  and nothing carries it to `LIA(base)`. Left struck through rather than deleted because the
  slide it makes — from "the extension is conservative on completed-world truth" to "the
  extension is about the same subject matter" — is the exact error a future reader is most
  likely to repeat here.
* Precedent for charging a boundary once and never downstream is explicit in the tiering
  header for `dd:fuel`, and the substrate boundary is stated in the same global-disclosure
  paragraph.

### Against

* The endpoint is about a **different market**. `liaHistory (theoremDP T ∪ productDefDP)`
  is not `liaHistory (theoremDP T)`; the incumbent's conclusion and the exact one are
  statements about two different inductors. A reader comparing the two rows is entitled to
  notice that we did not remove the slack from *the* endpoint — we produced a different
  one.
* The tiering header counts "a retained representation or operational structure the paper
  proves or **gets definitionally**" as a downgrade, and the defense above is literally
  "the paper gets this definitionally". The header's sentence and the defense point in
  opposite directions, and the header is the written rule.
* Zero precedent for a *definitional-extension* union (as opposed to `thm:scon`'s
  paper-mandated one).

### My position (superseded — see the resolution section at the top)

The union rendering is defensible and I would argue for it — the "different market"
objection proves too much, since the paper's theorem is universally quantified over
processes, and every closed endpoint in this repo already picks *a* particular process. But
it is a judgment call that needs Anson's ruling, and the header sentence should be amended
in the same commit if the ruling is favourable, because as written it reads against us.

**However, (C) is not the binding constraint. (A2) is.** Even with a favourable ruling on
(C) and (B), the weight premise cost from (A2) remains, and the row would have to say so.

---

## (D) Estimate for the remaining work

Assuming a favourable ruling on (C) and acceptance of (A2) option 2:

| Step | Est. |
|---|---|
| Re-index the schema by `(k,i)`; derive the emitters from `RpnThresholdCodeSeq` via `RpnSentenceCodes.primrec`; delete `LUVThresholdComputation` | 0.5–1 |
| Freshness by construction for the base stages and the weight quote LUV (tags `0`–`4` vs `5`) | 0.5 |
| `QuotationTheoryPresentation` lifting along `DP ⊆ DP'` | 0.5 |
| Generalize `theoremMarketComputation` / the two `theorem…QuoteCode` defs from `theoremDP T` to an arbitrary computable DP over `T` (**non-additive**: edits `QuoteCodeOfMarket.lean`, `ComputationDP.lean`) | 1–2 |
| Assemble `lic_no_expected_net_update_conditional_exact_closed`, discharge `hworld`, `source_valued`, `weight_valued`, `right_reflected` | 1 |
| Disclosure: ccee row rewrite, README boundary paragraph, audit inventory, trust-surface note, and the tiering-header amendment if (C) is ruled favourably | 1 |

**Total 4.5–6 sessions.** Lower than the plan's residual because A1 removed the named-code
certificate work; the non-additive step is the schedule risk, and it is the step that ends
the "easy to exclude" property.

---

## Recommendation (historical — superseded by the resolution section at the top)

_Kept as the record of what was recommended before the ruling. Item 1 was followed and (C) came back **rejected**; item 2 is therefore moot — the exact statement does not take the row, and the material is kept as item 1 anticipated, "a verified statement of what the propositional substrate *can* reach". Item 3 was confirmed by the adjudication's ranking._

Do not proceed on the assumption that this is a clean upgrade. It is not: (A2) forces
either a class restriction on `w` that is worse than the slack, or a second P-generability
premise. My recommendation, in order of preference:

1. **Rule on (C) first**, since everything else is wasted if the union rendering is
   rejected. If rejected, stop — the landed material (exact reflection, the world
   extension, the threshold emitter, the computability certificate) still stands as a
   verified statement of what the propositional substrate *can* reach, and is worth keeping
   as a documented obstruction rather than deleted.
2. If (C) is ruled favourable, land option 2 of (A2) and **keep both rows is not the
   ask** — the exact endpoint takes the `thm:ccee` row only if Anson judges "one extra
   P-generability premise about the extended market" milder than "the left product is
   reflected within `1/(n+1)` for every source family". I lean that it is milder (the slack
   weakens the certificate for *all* callers; the premise is discharged by construction for
   every family this repo builds), but that is Anson's call and not mine.
3. The one thing I would not do is take (A2) option 1. Narrowing `w` to e.c. rationals
   drops the paper's own worked example for this theorem, which is a strictly worse trade
   than the slack.
