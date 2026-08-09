# `thm:ccee` exact valuation — the route, what is built, and what it would cost to finish

_2026-08-08. Written after landing the route's first four components (commits `013a8a9`,
`857e95d`, `ea28ab8`, `b80c610`); every claim below about what an endpoint takes or calls
was made with the signature or the proof body open, and every named lemma was
`rg`-confirmed to exist at the cited line._

## The route, and why it is shaped this way

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
* `thm:ccee` in the paper quantifies over deductive processes: it holds for every logical
  inductor over every computable Θ. `theoremDP T ∪ productDefDP` is a computable deductive
  process, so the exact endpoint is a legitimate instance of the paper's own theorem, not a
  weakened variant of it.
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

### My position

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

## Recommendation

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
