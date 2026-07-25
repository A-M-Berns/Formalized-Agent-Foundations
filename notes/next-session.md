# Logical Induction — handoff

_Last updated: 2026-07-24 (fresh errata audit + boundary-shoring plan).
Branch: `logical-induction`._

# 🎯 ACTIVE PLAN — boundary shoring (2026-07-24, after fresh errata audit)

Context: the 2026-07-24 fresh code-level audit (`m7-errata-audit.md`, commits
`c162dbc`..`631d743`) found no load-bearing errata; its §3 minor errata are fixed. Two
disclosed boundaries remain worth *shrinking* rather than just disclosing: the `dd:fuel`
poly-token-value residual and the caller-supplied reflection data on the quotation
endpoints. Tranches below in execution order (value-to-effort descending). Keep the build
green between tranches; commit per tranche.

## Tranche 0 — AxiomAudit surface additions (guard-only, small)  ✅ when committed

Audit §3.6: the `_unconditional` quotation + meta-learning endpoints in
`Construction/Witnesses/ComputationDP.lean:595–735` are the strongest forms of their
theorems but are **absent from `AxiomAudit.lean`**, hence outside the axiom guard and the
surface freeze. Add to `#assert_axioms_clean`:
`lic_iterated_expectations_ofCode_unconditional`, `lic_introspection_ofCode_unconditional`,
`lic_self_trust_ofRepresentation_unconditional`,
`lic_expected_future_expectations_ofRepresentation_unconditional`,
`lic_no_expected_net_update_ofRepresentation_unconditional`,
`lic_no_expected_net_update_conditional_ofRepresentation_unconditional`, and the five
meta-learning `_unconditional` siblings (`lic_belief_finitistic_consistency_unconditional`
etc. — enumerate from the file, don't trust this list). Check `RationalQuoteCode` /
`ParameterizedDiagonalQuoteCode` field freezes already exist (`#assert_fields`) — they do.
Then mark audit §3.6 FIXED.

## Tranche 1 — `rationalQuoteCodeOfMarket`: witness-free `thm:epr`/`thm:er`

> **Status 2026-07-24: DONE, both halves** (`Witnesses/QuoteCodeOfMarket.lean`, on the
> audit surface, axiom-clean). Landed:
> * `arithmeticThresholdLUV_polyThresholdCodeSeq` — first-ever `threshold_poly` discharge
>   (kind `P`, provenance `(a)` via `gcdc`/`divmod1`/`ifzSel` + `(b)` `natCast_div_num/den`);
> * `RationalQuoteCode.ofComputable` (kind `C` over `BooleanQuoteCode.ofComputable`);
> * `MarketComputation.expectQuote` + `_cast`/`_mem_Icc`/`_computable` — the exact
>   rational day-`n` expectation program (bounded `Nat.rec` sum over the market program,
>   `ratAdd_prim`/`ratDiv_prim`);
> * `theoremPriceQuoteCode` / `theoremExpectationQuoteCode`, and the two closed endpoints
>   `lic_expectations_of_probabilities_closed` (`thm:epr`) and
>   `lic_iterated_expectations_closed` (`thm:er`) — over the constructed LIA with **zero
>   reflection hypotheses** (only the sequence + its poly codes remain).
> Lean gotchas: the `(… : _)` ascription on Computable compositions over ℚ-product types
> is load-bearing (whnf unification loop otherwise; NOT fixed by irreducible `Nat.sqrt`
> or heartbeats); `set_option … in` must precede the docstring; `Computable₂.comp` takes
> its two component functions separately, not paired.

**Goal.** Discharge the reflection data for epr/er the way `thm:lp` already does:
`parameterizedDiagonalQuoteCodeOfMarket` derives its quote object from
`theoremMarketComputation` with *no caller-supplied semantic relation*. Build the analog
for straight (non-diagonal) quotes:

* `rationalQuoteCodeOfMarket (c : MarketComputation P) (φ : ℕ → Sentence) (hφ : PolySentenceCodes φ) : RationalQuoteCode T (fun n => c.quote n ⌜φ n⌝)`
  — the value program runs the certified market code; `pos_complete`/`neg_complete` come
  from T ⊢ each exact-output Σ₁ instance (T ⊇ 𝗜𝚺₁, Σ₁-complete). Threshold codes:
  code-indexed quotation atoms over the *program*, never running the market at
  strategy-emission time (`threshold_poly` from the fixed program code + numeral inputs).
* Same composed with the finite expectation sum for er: `value n = (X n).expect P n`
  is a rational sum over the same program; one summation-code layer on top.

**Payoff endpoints** (new, put on the audit surface in the same commit):
`lic_expectations_of_probabilities_unconditional_closed` and
`lic_iterated_expectations_unconditional_closed` (naming: `_closed` = no reflection
hypotheses; only `φ`/`X` + poly-codes remain) over `liaHistory (theoremDP T)` — the
paper's §4.11 statements witness-free. `hexact` becomes definitional
(`liaHistory = cast of liaQuote`).

**Where the pieces live.** `QuotationAffine.lean` (RationalQuoteCode, the `_ofCode`
constructors, `diagonalPriceDecisionPart_partrec` toolkit), `ComputationDP.lean`
(quotationPresentation, theoremMarketComputation, Σ₁-instance lemmas),
`Criterion.lean` (MarketComputation.quoteAtFuel bounded evaluator). Search before
proving: the Σ₁-completeness instance lemmas likely already exist for the diagonal case —
reuse, don't re-derive.

## Tranche 2 — token sub-digitization (dd:fuel) — **design revised 2026-07-24**

Original idea (rewrite `EF.serialize`'s `const` case to a digit stream) is **wrong**: it
breaks the two-sided seam `serialize_length ≤ 3·cost` (a constant's digit count is not
bounded by `cost (const q) = 1`) and ripples into every cost bound. Revised design — a
**digit layer on top of the untouched token stream** — which also subsumes Tranche 4
(sentence codes get digitized for free, since *every* token is digitized):

1. `digitize : List ℕ → List ℕ` — each token becomes a self-delimiting base-4 digit
   block (digits `0..3`, terminator `4`); prove roundtrip + injectivity. `serialize`,
   `readM`, `streamStep`, `EF.cost`, and every seam lemma stay untouched.
2. `EfficientlyComputableTok₂` := two programs under one poly clock emit
   `digitize (serializeTrades …)` token-by-token (mirror `clockedTokens` /
   `strategyOfTokens` with an undigitize front end).
3. **Inclusion lemma** `EfficientlyComputableTok → EfficientlyComputableTok₂`: an old
   poly-value token has an `O(log n)` digit block; the digit emitter runs the old token
   program and extracts a digit — poly overhead. Transfers every existing `_ecTok`
   certificate unchanged.
4. Criterion flip: `IsLogicalInductor.noExploit` field quantifies over `Tok₂`; keep a
   *lemma* named `noExploit` with the old signature (field + inclusion) so no property
   file changes. Construction side: mirror `TraderEnumeration` (digit decode), rebuild
   `TradingFirm` coverage over the new enumeration, re-close `LIA`.
   Direction check (why this is safe): the e.c. class widens ⟹ `IsLogicalInductor`
   strengthens toward the paper's LIC ⟹ `LIA_is_logical_inductor` must beat more
   traders — and does, since the firm enumerates the same (length, token, clock)
   triples; property exploiters transfer by inclusion.
5. Faithfulness payoff: per-day rational literals (`2^{-n}`) and deep/large sentence
   codes become emittable — audit §2.1's concrete narrowing closes; the residual
   dd:fuel disclosure reduces to the fuel-vs-TM-time model sentence (see Terminal).

Sequencing within the tranche: (1)+(2)+(3) are green-standalone (no criterion change) —
land and commit them first; (4) is the breaking flip — do it in one focused pass with
the build gate between construction files.

> **Status 2026-07-24: steps 1–2 DONE** (commit `bbaebdb`): `natDigits4`/`tokenBlock`/
> `digitize` with proved round-trip (`undigitize_digitize`) and injectivity, plus
> `clockedTrader₂`/`EfficientlyComputableTok₂`, all in `Framework/Criterion.lean`;
> purely additive, build green.
>
> **Status 2026-07-24 (later): step 3 DONE** — `divPow4`/`digitAt`/`len4` fuel loops,
> `PolySegStream.block`, `PolySegStream.digitizeStream`, `ecTok₂_of_rawEmission` /
> `ecTok₂_of_rawSegStream` (Framework/Computable.lean), and the capstone
> **`EfficientlyComputableTok.toTok₂`** (M7Witnesses, after `end PrefixPatchCompile`);
> all on the AxiomAudit surface, axiom-clean, build+coverage green.  One rule-2b catch:
> `PolySegStream.of_eq` already existed (Computable.lean:2098) — reuse, don't re-prove.
> Remaining: **step 4, the criterion flip** (see plan below).  Note for step 4: the
> `noExploit`-compat lemma must live where `toTok₂` is visible — either move
> `codeEvalnNat`(+`_polyFueled`) and the `clockedTokens_polySegStream` block upstream
> from M7Witnesses into Framework/Computable.lean so `toTok₂` can live in Framework and
> `IsLogicalInductor` can re-expose the old-signature `noExploit` lemma directly, or
> keep the class field `noExploit₂` in Criterion and derive the old-named lemma
> downstream (worse: property files import only Framework).
>
> **Step 3 implementation plan (scoped in-session; all reuse points verified to exist):**
> the inclusion `EfficientlyComputableTok → EfficientlyComputableTok₂` composes as
> `PrefixPatchCompile.clockedTokens_polySegStream` (M7Witnesses — old clocked stream IS a
> `PolySegStream`, already proved) → new digit transformer → new `₂` realization bridge.
> New pieces, in build order:
> 1. **`len4`/`digitAt` fuel loops** (Computable.lean, next to `gcdc_polyFueled` and in
>    its style): `len4 t = (natDigits4 t).length` and `digitAt j t = (t div 4^j) % 4`,
>    both by `PolyFueled.prec` iterating `(·/4)` with pair state (`divmod1_polyFueled` +
>    `ifzSel_polyFueled`); crude bounds suffice (`len4 t ≤ t`, `digitAt ≤ 3`, state ≤
>    input — no log accounting needed).
> 2. **Block stream**: `PolySegStream (fun m => tokenBlock (tokenFn m))` given
>    `PolyFueled tokenFn` — length `len4 ∘ tokenFn + 1`; token `⟨m,j⟩ ↦ if j < len4 then
>    digitAt j else 4`.
> 3. **Digit transformer**: `PolySegStream s → PolySegStream (digitize ∘ s)` =
>    `PolySegStream.concatVar` (exists, Computable.lean:2478) applied to the block
>    stream with `cnt := lenFn`, plus the list identity
>    `digitize (s n) = (range (lenFn n)).flatMap (tokenBlock ∘ tokenFn ⟨n,·⟩)`
>    (from the seg spec by `List.ext`).
> 4. **`₂` bridge**: mirror `ecTok_of_rawEmission` → `ecTok₂_of_rawEmission` (same
>    realization `clockedTokens = raw n`; conclusion via `clockedTrader₂` +
>    `undigitize_digitize`), then mirror `ecTok_of_rawTokenFn`'s clock-max juggling
>    verbatim (Computable.lean:1707–1740) for `ecTok₂_of_rawSegStream`.
> 5. **`EfficientlyComputableTok.toTok₂`**: destructure the certificate, apply 3 to
>    `clockedTokens_polySegStream`, close with `undigitize_digitize` (`hstrategy` is
>    definitional: both sides are `strategyOfTokens n (old stream)`).
> Gotchas already learned this session: `(… : _)` ascription on Computable/PolyFueled
> compositions over product types (whnf loop otherwise); `attribute [local irreducible]
> Nat.sqrt` in a section (but NOT nested twice — hard error); `set_option … in` precedes
> the docstring.
>
> **Status 2026-07-24 (later still): step 4 DONE, as a layered class** (not a field
> rewrite — see design note).  Landed:
> * `IsLogicalInductor₂ extends IsLogicalInductor` (Criterion.lean) with `noExploit₂`
>   over `EfficientlyComputableTok₂`, layering disclosed in the docstring;
> * `enumeratedTrader` redefined as the tagged two-model enumeration (even = token
>   decode, odd = digit decode; `TraderProgram.trader₂`), with coverage lemmas for both
>   classes (`exists_enumeratedTrader_eq` / `_₂_eq`) and per-parity ec lemmas;
> * `trading_firm_dominance_of_covered` (the factored `lem:tfdom` core) + both
>   emission-model instances, incl. `trading_firm_dominance₂`;
> * `undigitize_prim`/`undigitizeStep_prim` + the parity dispatch in
>   `enumeratedTraderTrades_prim` (the compiler's ONLY decode coupling — everything
>   downstream consumes `firmRawTraderTrades_prim` opaquely);
> * `lia_no_efficient_trader_exploits₂`, `lia_isLogicalInductor₂_of_computableMarket`,
>   **`LIA_is_logical_inductor₂`**, `exists_logical_inductor₂` — `thm:lia`/`thm:li` in
>   the digit-metered (paper-faithful) e.c. class, unconditional over any computable DP;
> * AxiomAudit: new endpoints asserted + `#assert_fields IsLogicalInductor₂`;
>   `lem:tfdom` classified complete in coverage-classification.md.
>
> **Design note (why layered, not flipped in place).**  Every theorem *constructing* an
> `IsLogicalInductor` instance must defeat the class it claims.  The LIA construction now
> defeats `Tok₂`; but the conditioning transformations (`thm:scon`) construct instances
> for the *conditioned* market by translating an exploiting trader back to the base
> market, and their translation compilers (`ConditioningCompiler`) carry token-model
> emission certificates only.  Flipping the single field would silently break (or force
> a rushed re-engineering of) that whole family.  The layered class keeps everything
> green and makes the residual explicit:
>
> **RESIDUAL (recorded tranche): digit-model conditioning translation.**  Extend
> `conditionedTranslation_preserves_ec` (and the gated/eventual variants) to
> `Tok₂ → Tok₂` so `lic_conditioned*` can produce `IsLogicalInductor₂` and the two
> classes can collapse into one field (renaming `noExploit` to quantify over `Tok₂`,
> with the token-model lemma derived via `toTok₂`).  Until then, property-tail results
> conditional on `[IsLogicalInductor P DP]` are discharged by
> `LIA_is_logical_inductor₂.to…` as before, and the paper-facing existence statement
> should cite `LIA_is_logical_inductor₂`.
>
> ⚠️ **Scoping correction (2026-07-24, discovered while closing step 4): this residual
> is NOT the quick "undigitize → transduce → redigitize" wrapper the first draft
> suggested.**  The conditioning transducer rewrites price leaves `[0, ⌜φ⌝, day]` into
> conditional-price expressions whose sentence codes are *derived* from the input's
> (`⌜φ ⋏ ψ⌝` from `⌜φ⌝` — a `Nat.pair`-shell computation).  In the digit model, `⌜φ⌝`
> may have exponential *value*, held only as a digit stream; the clocked machine cannot
> materialize it as a number (evaln values are fuel-bounded).  Deriving the output
> block therefore needs **big-number arithmetic on digit streams** (`Nat.pair` = square
> + add at exponential values ⇒ schoolbook multiplication as a poly digit emitter).
> That is a bignum-emitter library at the `evaln` level — a genuine sub-project, not a
> wrapper.  Same wall applies to migrating `𝓔𝓒`-sequence hypotheses for any theorem
> whose trader *computes* on sentence codes (rather than copying them verbatim into
> trade frames, which is digit-copyable and fine).  Plan accordingly: the class
> layering is the honest steady state until someone wants the bignum layer.
>
> **Status 2026-07-25: bignum layer STARTED — B0 (the bignum emitter core) DONE**
> (`Framework/DigitArith.lean`, registered in `Framework.lean`, green, axiom-clean).
> * Spec layer: `dig4`/`len4` laws (`len4_eq_iff`, `mod_pow_succ4`, `dig4_mod_pow`,
>   `len4_mod_pow_succ`), addition carries (`addCarry4_succ`, `dig4_add`),
>   **schoolbook column multiplication** (`conv4`/`mulCarry4`/`colSum4`;
>   `colSum4_decomp` is the loop invariant — partial column sums = poly-bounded carry +
>   product truncation, via the triangle/complement split of the digit double sum —
>   and `dig4_mul` the digit formula), and the MSB comparison flag (`ltFlag4_succ/_spec`).
> * Implementation: `BigDigits x` (poly-fueled len4 + per-digit access to families with
>   possibly exponential values), closed under `add` (ripple carry), `mul` (nested
>   `PolyFueled.prec`: inner column convolution, outer carry — states poly-bounded,
>   values never materialized), `ltNat` (flag), **`natPair`** (branch on flag between
>   the two square-and-add arms — the `⌜φ⋏ψ⌝`-shell prerequisite), `succ`, `comp`,
>   `of_polyFueled`, and the generic length scanner `len_of_digits`.  Delivery
>   interface back to emission: `BigDigits.blockSeg` (digit block family is a
>   `PolySegStream`).
> * Gotcha log: `Nat.max` vs `max` breaks omega/rw — state bounds additively;
>   `PolyFueled.of_eq` targets need type ascription or the metavar sticks; beta-reduce
>   (`simp only []`) before omega in `IsPolyBounded` side goals.
>
> **Status 2026-07-25 (later): B1a (undigitize block view) also DONE** (same file,
> green, axiom-clean, committed `265cc93`/`183ad57`/`9179693`):
> * list spec: `blockSplit`/`digitVal` re-expression of `undigitize`
>   (`undigitize_eq_blockSplit`), `blkTrack` (mid-fold block view) with its
>   `blockStep` recurrence, digit/length/getD facts;
> * fueled scans: `blockCount_polyFueled`, `blkTrackLen_polyFueled`,
>   `blkDig_polyFueled` — `PolyFueled.prec` over the *virtual prefix*
>   (`vpre`, so step equations hold on garbage inputs too), small packed states;
> * capstone **`PolySegStream.undigitizeTokens`**: any digit `PolySegStream` gives
>   poly-fueled token count + `BigDigits` token access (never materializing values).
> * Gotchas added to the log: `rw [if_pos (by …)]` with anonymous/untyped proofs
>   binds the *first* `if` in the goal — always `show`/type-ascribe the condition;
>   identical if-conditions rewrite all copies at once (don't repeat the rw);
>   `List.getD_eq_default` needs `(l := …)` when nested getDs both match;
>   higher-order `len_of_digits`-style applications need the family given
>   explicitly (`(s := …)`) or the bound-proof goal keeps a metavariable.
>
> **Remaining plan (B1–B3), scoped 2026-07-25:**
> * **B1 — digit transducer for the price rewrite.**  Input: a `Tok₂` certificate's
>   clocked digit stream (a `PolySegStream`, possibly *not* `digitize` of anything, and
>   with possibly-huge token values).  Key scoping facts settled this session:
>   (a) the token-model transducer spec is *not implementable* verbatim in the digit
>   model — `ψCode token` at a huge day token needs fuel poly in the *value* — so the
>   digit transducer must **guard**: a scan (small control state: freeze mode ≤ 5 +
>   pending *position*, not value) checks every mode-2 (price-day) token against `n` by
>   digit comparison (`ltFlag4` against `natDigits4 n`); oversized day ⟹ emit `[]`.
>   (b) Honesty obligation for the guard branch: day-token > n ⟹ `rank > n` ⟹
>   `strategyOfTokens n` of BOTH source and rewritten stream is the empty strategy
>   (`rank_price` = the day; validation is `∀ trade, rank ≤ n`), so `[]` realizes the
>   translation.  Needs a token-level lemma "decoded stream's mode-2 tokens are price
>   days of decoded trades" (fuel-free; prove by the `serializeTrades` induction that
>   the existing `_serialize` lemmas use).
>   (c) Good path: per-source-token digit segments assembled by
>   `PolySegStream.concatVar`; copied tokens are digit-copies via a **BlockView** (poly
>   locate of the `j`-th terminator, per-block digit access = a `BigDigits` family);
>   the ONLY bignum token is `conjunctionCode pending ψc` =
>   `(BigDigits.natPair pendingView (of_polyFueled ψcode)).natPair (const 3) |>.succ`
>   (shell order: `pair 3 (pair φ ψ) + 1`) rendered by `blockSeg`.
> * **B2 — digit frame passes** (`safeSeparatedFrameTokenOutput` analogue): budgets are
>   poly (day, trade count); trade bodies are digit-copied twice; needs the same
>   BlockView + a digit-level `frameTradeCount`/`parserStructurallyAccepts` — check
>   their state sizes first (if the structural parser state embeds token *values*, use
>   position-indexed state like the freeze scan).  Then
>   `conditionedTranslation_preserves_ec₂` + `eventualConditionedTranslation_…₂`
>   (zero-day membership test needs day materialized — same ≤ n guard).
> * **B3 — criterion collapse**: `lic_conditioned*` produce `IsLogicalInductor₂`;
>   then either collapse the two classes into one field or record the (now much
>   smaller) residual.
> * Effort note: B1+B2 mirror ~2000 lines of ConditioningCompiler proofs; expect
>   multiple sessions.  B0 is committed independently — it is the reusable part
>   (any future digit-model computation on sentence codes needs exactly these
>   emitters).

## Tranche 3 — ctsInd-composed quotes + indicator product: witness-free `thm:st` (and cee/ceu)

> **Status 2026-07-25: ceu, cee, st CLOSED** (`Witnesses/QuoteCodeOfMarket.lean`, on the
> audit surface, axiom-clean, build+coverage green):
> * `theoremFutureQuoteCode` + `lic_no_expected_net_update_closed` (`thm:ceu`);
> * `expectQuoteAt` (two-index expectation program; `expectQuote` refactored to its
>   diagonal) + `theoremDeferredExpectationQuoteCode` +
>   `lic_expected_future_expectations_closed` (`thm:cee`; `source_valued` remains — it
>   is the paper's own premise about the caller's `X`);
> * `ratCtsInd` (+cast/range/computability via the min = a+b−max trick, no Boolean
>   branch) + `theoremConfidenceQuoteCode`, and `indicatorProductLUV` with its product
>   law `indicatorProductLUV_valuesAt` and shared-emitter poly certificate
>   (`quoteAtom_mesh_encode_polyFueled` factored out of Part A) +
>   **`lic_self_trust_closed`** (`thm:st`) — both quoted LUVs constructed, zero
>   reflection hypotheses.
> **2026-07-25 (later): ref also CLOSED** — `theoremIntervalQuoteCode`
> (`BooleanQuoteCode.ofComputable` over the rational interval predicate, with
> `PolyRatCodes a b` as the honest e.c. hypothesis and casts bridged by `quote_exact`)
> + `lic_introspection_closed`.  The `GeneratedRatFeature` bound presentations remain
> caller data (the repo's operational rendering of the paper's e.c. bounds — qualified
> tier, unchanged).
>
> **2026-07-25 (later): ccee CLOSED — indicator-source form** (`QuoteCodeOfMarket.lean`
> Part F, on the audit surface, axiom-clean).  The design question resolved as follows:
> the general-caller obstruction is **impossibility, not missing engineering** — a finite
> Boolean combination of `X`-thresholds only jumps at thresholds it uses, so the scaled
> LUV's mesh threshold must contain `X.gt (r / w (f n))`, whose emitter would have to
> *compute* `w (f n)` in poly-`n` fuel; `def:deferralfunc` (and the paper) withhold
> exactly that.  (The note's "option A" — arbitrary-rational caller codes — founders the
> same way and would also demand *more* than the paper.)  The honest closure is the
> paper's motivating conditional-probability instance: source = caller **relational
> indicator family** (`IsIndicator`, D3-compliant), `Z` = `indicatorProductLUV` over
> `theoremDeferredWeightQuoteCode` (a quote code *naming* the `w ∘ f` program — deferral
> costs nothing at emission), `Z'` = `theoremConditionalExpectationQuoteCode`
> (`expectQuoteAt X n (f n) · w (f n)` via `ofComputable`).  New small lemma
> `PCWorld.ValuesAt.eq` (uniqueness, Framework/Expectations.lean) links the caller's
> arbitrary source value to the payout.  Endpoint:
> **`lic_no_expected_net_update_conditional_closed`** (kind `C`; provenance `(a)`
> throughout, caller keeps only the paper's own premises: φ+codes, indicator linkage,
> weight `[0,1]`+codes+P-generability, deferral).  Quotation family §4.11–4.12 is now
> fully witness-free over LIA: epr/er/ceu/cee/ccee/st/ref/lp.

Two constructions on top of Tranche 1:
* **Composed quote compiler**: rational-continuous-function-of-a-quote → quote code with
  pos/neg completeness. Target: `B n` valued at `ctsInd (δ n) (P (f n) (φ n)) (p n)` —
  comparisons against ctsInd outputs reduce to comparisons against the underlying
  (T-provably exact) future quote. Future day `f n` is fine: the atom quotes the
  *program*, not the run.
* **Indicator-product LUV** for `A n` valued at `payout(φ n) · ctsInd(…)`: thresholds
  `A.gt r := φ n ⋏ Atom⟨ctsInd-code, n, r⟩`; `product_reflected` from
  `quote_positive_enters`/`quote_negative_refutes` + Boolean `⋏` semantics. Poly-value
  codes: conjunction of two poly-value formula codes is poly-value.

Payoff: `lic_self_trust_unconditional_closed` (+ cee/ceu/ccee closures). Hardest
assembly of the quotation tranches; do after 1 proves out the recipe.

## Tranche 4 — sentence-code sub-tokenization (dd:fuel, the long pole)

Same move as Tranche 2 one level down: `price φ n` / trade frames emit an RPN stream
over Foundation's `Formula ℕ` constructors (atom-index, ⊤, ⊥, ∼, ⋏, ⋎, →; check the
actual constructor set — `NegAbbrev`?), atom indices digit-split. Migrate
`PolySentenceCodes`-shaped hypotheses to a stream predicate via an inclusion lemma
(poly-value code ⟹ poly stream) so all current instantiations transfer. This is the
tranche that finally admits deep poly-size sentence sequences and closes audit §2.1's
concrete narrowing.

## Terminal (not a tranche — document, don't build)

After 2+4 the only dd:fuel residual is fuel-model vs TM-time equivalence. **Blocked in
principle**: Mathlib has no time-bounded computability/complexity theory (no poly-time
TM class; `Turing.PartrecToTM2` is unbounded). Per CLAUDE.md rule 6 this is a
stop-and-report boundary: keep the model-card calibrations (`PolyFueled.primrec`,
`not_polyFueled_two_pow`, closure ops) and one disclosure sentence. Likewise the last
quotation type-(c) — code-indexed atoms *mean* their arithmetic instances via
`theoremDP`'s enter/refute clauses — is closed by an intended-semantics bridge lemma
(Σ₁-soundness ⟹ truth-in-ℕ for entering atoms) if one is missing, **not** by replacing
the propositional substrate.

## Paper errata boundary and F4 repair (2026-07-23)

The former audit F5 is not a repository-faithfulness defect: the unrestricted
finite-perturbation theorem has a genuine gap in the paper's proof. It has been removed from
`m7-errata-audit.md` and moved to the durable
[`logical-induction-paper-errata.md`](logical-induction-paper-errata.md) ledger. That ledger
also records the research stretch goal of formalizing either the unrestricted theorem or,
more likely, a counterexample to it.

The former F6 was also removed from the finding list: its prefix-machine, DUS-approximation,
and strict-separator boundaries were already accurately disclosed, so it did not belong in
an errata audit. F7 now records the full scope of replacing the disclosed propositional LUV
abstraction with a paper-faithful first-order construction.

F4 is now resolved by a conditioning-specific finite-prefix construction that does not use
unrestricted finite-perturbation closure. Uniform Non-Dogmatism plus Preemptive Learning
produce the eventual condition-price floor; the exact rational market program shrinks it
over the finite prefix and records the zero-denominator days. A zero-aware token compiler
replaces only those historical conditional-price leaves by the capped value `1` and launches
after the finite cutoff. Fixed and growing paper-facing corollaries, plus constructed-LIA
instantiations, now take only the expected consistency/computability premises.

## ✅ F9 done + F0 confirmed; hP cleanup recorded as a tranche (2026-07-23)

**F0 (range law) is resolved in-tree** — the audit doc is stale. The `[0,1]` range now lives
in the `ComputableMarket` certificate and is exposed as `IsLogicalInductor.price_mem_Icc`
(`Framework/Criterion.lean`). `IsLogicalInductor` bundles the range; the class is no longer
strictly broader than the paper's markets.

**F9 (endpoint inventory + coverage) is done and green.** Added `scripts/check_endpoint_coverage.py`
— the missing *paper → inventory* direction (every `Paper node:` label has ≥1 endpoint in
`AxiomAudit.lean`; Tier-1 `#assert_axioms_clean` or Tier-2 `#assert_fields`). Wired into
`scripts/check-paper-nodes.sh` so one run checks both directions. Coverage is **complete**
(60 labels, 0 uncovered, `app:ifp`/`app:prandaff` excluded as appendix proof-refs). Added the
two genuinely-missing unconditional-over-LIA capstones — `lia_learns_halting_patterns_unconditional`
(`thm:halts`) and `lic_expectations_of_probabilities_ofCode_unconditional` (`thm:epr`, docstring
normalized to the `Paper node:` convention) — both build axiom-clean. Added a header note to
`AxiomAudit.lean` separating the two independent claims: axiom cleanliness (listed endpoints
are sorry/axiom-free) vs surface completeness (the list covers every annotated label); neither
implies faithfulness, which is the read-through's job.

### ✅ DONE (2026-07-24) — redundant-`hP` cleanup (F0 residual, consolidation-phase)

**Executed in full**: 137 endpoints across 21 files (regenerated fresh, per the caution below);
all callers repaired; build/AxiomAudit/coverage/lint green. Original tranche record kept below.

**What.** 120 paper-facing endpoints across 14 files still carry a redundant
`(hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)` even though they have `[IsLogicalInductor P DP]` in
scope, from which `hP` is derivable via `IsLogicalInductor.price_mem_Icc`. The endpoints are
*correct*; `hP` is pure noise that the deferred human read-through would have to wade through.
This is **cosmetic/legibility only** — nothing is blocked by leaving it, so it is safely
deferrable, but it should land *before* the frozen-surface read-through (step 2 of the
`CLAUDE.md` sequencing override) so the surface read is clean.

**Why not done in the F9 session.** It is a genuine cascading refactor (each removal breaks
that endpoint's call sites), and a partial/slightly-wrong pass leaves the build red — it wants
its own careful per-file run, not a bolt-on.

**How (the mechanical recipe).**
1. Per endpoint: delete the `hP` binder from the signature; inside the proof add
   `have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ => IsLogicalInductor.price_mem_Icc n φ`
   and feed it to the `_ofComputations` / `_ofHistoricalVerifiers` variant (those are the
   *abstract* building blocks — they legitimately keep `hP`; do **not** strip it there).
2. Fix that endpoint's callers to drop the now-absent `hP` argument (mostly the
   `IntegrationTest.lean` `_discharged` wrappers, which also have the instance and can drop
   their own `hP` in turn).
3. One file at a time, `lake build` between each; keep green at every stopping point.

**Scope / caution.** The endpoint list was generated by matching `[IsLogicalInductor` + the
`hP` shape in a decl's signature; the generator's fixed-line window can bleed across decls, so
**re-derive the list and hand-confirm each signature** rather than trusting a saved list.
Regenerate with the same `check_endpoint_coverage.py` helpers (`inventory_members`) or an
equivalent per-decl scan. Watch the `[[li-primrec-natsqrt-blowup]]` files if any touched proof
goes near `Finset`/`Nat.sqrt`.

## ✅ F7 IMPLEMENTATION STATUS (2026-07-23) — items 1/2/3 done; item 5 endpoints certified

**Update (later same day):** the "D blocked" note below was resolved. The blocker — endpoints
requiring full `ValuesAt` at a single finite stage — was fixed by (a) restructuring the endpoints
to the *satisfiable finite-precision* hypothesis they actually consume, and (b) building a
scheduled-reveal process that discharges that hypothesis from arithmetic. Both named weak
endpoints now have certified `_arith` forms.

Files (all green, axiom-clean `propext/Classical.choice/Quot.sound`, in `LogicalInduction`):

- `Framework/Expectations.lean` — `PCWorld.expectApprox_near_ofGrid`: the day-`n` precision bound
  from **grid** coherence (the `n` points `i/n`) only, not the infinite cut. `expectApprox_near`
  is now its wrapper. **(item 5b)**
- `Properties/ExpectationAffine.lean` — `lic_linearity_of_expectation` and
  `lic_expectation_provind` restructured to the **finite-precision, eventual** (`∀ᶠ n`) world
  hypothesis `|𝔼_n^v(X) − x| ≤ 1/n` — satisfiable at a finite stage (the old `ValuesAt`-at-stage-`n`
  hypothesis was not). Original `ValuesAt` statements kept as `_ofValuesAt` corollaries. **(item 5a)**
- `Construction/Witnesses/LUVExpectationCertified.lean` — `gridDP` (scheduled-reveal process, stage
  `n` holds the `Θ`-decided grid literals for `i ≤ n`, `j/n`), and
  `lic_expectation_provind_arith` / `lic_linearity_of_expectation_arith`: the paper's endpoints
  with the **world-value hypothesis replaced by arithmetic** (`c ≤ numᵢ/denᵢ`, resp.
  `valueₖ = a·valueᵢ + b·valueⱼ`). This is the audit's "operational hypotheses the paper
  discharges", resolved end-to-end. **(item 5c)** Wired into `AxiomAudit.lean`; paper-node +
  endpoint-coverage checks pass.

**Item 5 — three comparison forms, varying-sequence linearity, three sequence capstones:**
- `lic_expectation_provind_le` / `_eq` (ExpectationAffine, via neg-duality of the affine mesh) —
  the paper's **three comparison forms** (`≥`,`≤`,`=`); certified `_arith` versions in
  `LUVExpectationCertified.lean`.
- `lic_expect_combination_provind_zero` — **combination-level** expectation provability induction
  (`E` of a determined-at-0 bounded LUV-combination sequence `≈ₙ 0`), assembled from the
  combination mesh via `affine_provind_theory_tendsto_zero` (whose `ConsistentWithTheory`
  hypothesis Phase B's `ExactTheoryPresentation` supplies — no fresh polySequence needed).
- `lic_linearity_of_expectation_seq` — the paper's genuine **varying-sequence** Linearity of
  Expectation (`aₙEₙ(Xₙ)+bₙEₙ(Yₙ) ≈ Eₙ(Zₙ)`), derived exactly as the paper does (`app:loe`) from
  the combination provind on `aX+bY−Z`.
- `ComputableLUV.exppolymax_arith` and `wubexp_arith` — the **sequence-level** `thm:exppolymax`
  and `thm:wubexp` for arbitrary `dd:luv-arith` LUV-combination sequences, with the
  `WorldValued` / `ExactTheoryPresentation` *representation* hypotheses discharged from arithmetic
  via Phase B (over `luvThresholdDP`). Residual mesh-softmax / feedback witnesses are the
  disclosed operational boundaries.
- All in `AxiomAudit`; paper-node + coverage checks pass (61 labels).

**Combination provind in all three forms at any constant `c` (done):**
- `PolySequence.affine_provind_theory_le_const` / `_ge_const` (AffineCoherence) — one-sided
  affine provability induction with **vanishing error**, the one-sided analogue of
  `affine_provind_theory_tendsto_zero`, absorbing the mesh's `O(1/n)` slack on one side.
- `lic_expect_combination_provind_le` / `_ge` / `_eq` — expectation provability induction for an
  arbitrary bounded LUV-combination sequence determined `≤`/`≥`/`= c` (any `c`), all via the mesh
  + Phase B. `..._zero` is now the `c = 0` corollary of `_eq`. This is the audit's explicit
  item-5 ask ("expprovind for arbitrary bounded LUV-combination sequences in each of the paper's
  three comparison forms"), complete.

**`perexpkno` / `expcoh` certified (done):**
- Two restructures of the **core M4 convergence chain** made this possible, both green and
  behaviour-preserving (the trader math is untouched):
  - **`ValuesAt → ApproxValuesUpTo`**: `excTrader_netWorth_ge` only ever used `expectApprox_near`
    at precisions `≤ N`, so the chain (`excTrader_exploits` / `expect_converges` /
    `expectTerms_converge` / `ConvergencePresentation.daily_value`) now takes finite-precision
    world agreement; `ValuesAt.approxValuesUpTo` keeps every prior caller working.
  - **`∀ → ∀ᶠ`**: `BddBelow` comes from trader boundedness (`abs_netWorth_le_partialMagnitude`,
    new) not the value hypothesis, and the unbounded direction uses only the arbitrarily-large
    `excBneg_unbounded` stages — so the value agreement need hold only *eventually*. This is
    exactly what a scheduled-reveal DP provides (no finite stage reveals LUV `i`'s grid before
    stage `i`; every stage `≥ i` does).
- `combinedDP = gridStage ∪ luvThresholdDP` supplies both `WorldValued` (completed-world values,
  all thresholds, from the provability enumerator) and `ConvergencePresentation` (eventual daily
  finite-precision values, from the scheduled grid).  `expcoh_arith` / `perexpkno_arith` discharge
  both representation hypotheses from arithmetic; only the disclosed mesh-softmax operational
  witness and threshold-code efficiency remain.  In `AxiomAudit` (63 labels); checks pass.

**Efficiency certificates — DONE (2026-07-23, Anson-requested reversal of the earlier scope-out):**
- **`gcdc_polyFueled`** (`Framework/Computable.lean`): runtime gcd in the fuel model, by
  `PolyFueled.prec`-iterating the Euclid step (`divmod1` + `ifzSel` + `predc`) — the toolkit's
  `prec`/varying-divisor `divmod1` combinators (which I'd earlier wrongly believed absent) make
  this bounded engineering, not a model extension.
- **`toLUV_polyThresholdCodes`** (`LUVArithmetic.lean`): the **first `PolyThresholdCodes`
  certificate proved rather than assumed in the repo** — gcd + two `divmod1` reductions + `ifzSel`
  `k=0` fallback + fixed atom shell emit the encoded `⌜Xᵢ > b/k⌝` from `⟨k,b⟩`; `ℚ` lemmas
  (`natCast_div_num/den`) identify `((b:ℚ)/k).num/.den` with the gcd-reduced pair;
  `thresholdCodeNat` + `_eq` + `_primrec` expose the ℕ-level code.
- **`luvThresholdDP_computable`** (mirrors `theoremDP_computable`), **`gridDP_computable`**
  (total `gridEmit` + `Computable.nat_rec`-built range map — the literal polarity runs
  `L.num`/`L.den`, so this layer is `Computable`, not `Primrec`), **`combinedDP_computable`**
  (via `DeductiveProcessComputation.union`).
- **Payoff — first fully unconditional expectation endpoints in the repository**
  (`LUVExpectationCertified.lean`): `lic_expectation_provind_{,le_,eq_}arith_unconditional` and
  `lic_linearity_of_expectation_arith_unconditional`, over the constructed LIA on the computable
  scheduled process with proved threshold codes. **Sole hypothesis: the rational bound/identity on
  the LUV values.** In `AxiomAudit`; all gates pass.

**dd:fuel hardening slate — DONE (2026-07-24):** separation witness (`not_polyFueled_two_pow`,
size-based only), model card section in `Framework/Computable.lean` with six trust facts in
`AxiomAudit` under `def:ec`, two-sided `EF.cost` ↔ token-length seam
(`cost_le_serialize_length` + `Strategy.serializeTrades_length_le_cost`), and the README
disclosure now names the `evaln` anchor and output-exceeds-fuel subtlety.

**Remaining (dd:fuel-adjacent, disclosed):** the sequence capstones' operational witnesses
(`MeshSoftmaxOperationalWitness`, feedback emission/truth, `BoundedSequence.poly` for *arbitrary*
combination sequences) are still caller data — they are per-sequence constructions the paper also
treats as given. F10's fuel↔poly-time equivalence question stays a permanent disclosure.

**Net:** F7 items 1, 2, 3 complete and non-vacuous. Item 5's explicit repair list — varying-sequence
linearity and expectation provability induction (single-LUV in all three comparison forms, plus the
combination-level `= 0` form the paper uses) — is done and certified against arithmetic, together
with two sequence-level capstones. What the certified endpoints still *assume* is exactly the
project-wide disclosed set (inductor existence + efficiency codes), never a LUV-specific world-value
hypothesis. The `dd:luv-arith` boundary (computable-function LUVs, not arbitrary value-defining
formulas) is disclosed in `LUVArithmetic.lean`'s header.

## 🗄 (superseded, kept for history) F7 Phases A/B/C landed green; D blocked on endpoint restructure

Three new axiom-clean, sorry-free files (built into `LogicalInduction`, 2658 jobs green):

- **Phase A — `Construction/Witnesses/LUVArithmetic.lean`** (`dd:luv-arith`, item 1+2).
  `ComputableLUV` = the paper's computable-`[0,1]`-valued-function LUV (`def:luv`'s own worked
  example): value `num i / den i`. Threshold queries arithmetized as `codeOfREPred` of a
  **decidable ℕ cross-multiplication** predicate (ℚ/ℤ have no `Primrec` in this Mathlib, so the
  sign+magnitude are folded into a single `<` over ℕ). `thresholdPred_code_iff` proves the ℕ
  predicate matches `r < value`; `threshold_provable`/`threshold_refutable` give, via
  `re_complete`, that `Θ` **proves** every true threshold and **refutes** every false one.
  Watch: the `Nat.unpair`→`Nat.sqrt` whnf blowup ([[li-primrec-natsqrt-blowup]]) hits the
  computability proof — fixed with `attribute [local irreducible] Nat.sqrt in`.

- **Phase B — `Construction/Witnesses/LUVPresentation.lean`** (item 3, the core payoff).
  `ArithmeticLUVPresentation L DP T` (DP reveals the `Θ`-provable threshold literals — the exact
  analogue of `ComputationTheoryPresentation`). `threshold_holds_iff`: **every world consistent
  with the process holds `⌜Xᵢ > r⌝` iff `r < numᵢ/denᵢ`**, no nonstandard slack (the decidable
  collapse of `def:luv`'s sup). From it, `exactTheoryPresentation_ofArithmetic`,
  `worldValued_ofArithmetic`, `valuesAt_ofArithmetic` — the presentation interfaces are now
  **theorems**, not raw hypotheses, for the `dd:luv-arith` class.

- **Phase C — `Construction/Witnesses/LUVDeductiveProcess.lean`** (non-vacuity / satisfiability).
  `luvThresholdDP` (two-tag provability-enumerator mirroring `theoremDP`) + `luvArithmeticPresentation`
  proving the Phase-B premise **satisfiable**; `luvWorld` (standard truth) is consistent with every
  stage → `luvThresholdDP_hworld`. Meets the `CLAUDE.md` satisfiability bar for Phase B.

**What is NOT done (F7 is not fully finished):**

1. **Efficient-computability certificate for `luvThresholdDP`** — the `theoremDP_computable`
   analogue (~200 lines primrec encoding, natsqrt hazard). Needed to compile the process into an
   actual `LIA` via the generic `LIA_is_logical_inductor (DP) (ComputableDeductiveProcess DP)` and
   get *fully unconditional* endpoints. Deferred; mechanical copy of `ComputationDP`'s tail.

2. **`PolyThresholdCodes (toLUV i)`** — the efficiency certificate the affine/expectation traders
   consume (`ConvergencePresentation.threshold_code`). `toLUV`'s codes are primrec but proving
   `PolyFueled` needs the `EF.cost` machinery; not built.

3. **Item 5 (the two weakened endpoints) — BLOCKED on an architectural obstruction I hit.**
   `lic_linearity_of_expectation` / `lic_expectation_provind` (`Properties/ExpectationAffine.lean:394,461`)
   take `hvals : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∃ x, v.ValuesAt X x` — quantified
   over worlds consistent with a **single finite stage** `DP.D n`. But `PCWorld.ValuesAt` demands
   cut-coherence for **all** `r : ℚ`, which no finite stage can pin. Phase B's derivation only
   yields `ValuesAt` for **fully** `ConsistentWithTheory` worlds (all stages). So the certified
   discharge of these endpoints requires **restructuring them to quantify over theory-consistent
   worlds** (or reformulating `hvals` to per-stage-finite-precision) — a change to the pre-existing
   `ExpectationAffine`/`ExpectationProperties` surface, not a bolt-on wrapper. This is the real
   remaining content of item 5 and was not attempted (it risks the green invariant on a large,
   already-audited surface). The varying-sequence linearity and 3-form bounded-combination provind
   sit on top of that restructure.

4. **AxiomAudit wiring** for any new capstones (pending item 5).

**Assessment:** items 1, 2, and 3 (for theory-consistent worlds) are done and green; the world-value
interfaces are genuinely derived-from-arithmetic rather than assumed, and the premise is proved
satisfiable. Item 5 and the unconditional instantiation remain, gated respectively on the endpoint
restructure and the efficiency certificate. The `dd:luv-arith` boundary (computable-function LUVs,
not arbitrary value-defining formulas) is disclosed in `LUVArithmetic.lean`'s header and must appear
in any public claim.

## 🔎 F7 full-scope plan — first-order LUV reconstruction (2026-07-23, scoped after repo+Foundation survey)

**Question that prompted this:** how much work is *full-scope* F7 (replacing the disclosed
propositional-threshold LUV abstraction with a certified first-order arithmetic LUV)?

**Headline: not a Brouwer-class blocker.** My first-pass worry was that F7 item 2 ("worlds
whose encoded model may be nonstandard") needed arithmetized satisfaction Foundation doesn't
expose. **That worry is wrong.** Foundation ships the whole toolkit, and the repo already uses
it for the computation/halting tail. The infrastructure exists; F7 is a substantial *replication
+ refactor*, not a missing dependency.

### What the survey found (so the next session doesn't re-derive it)

**Foundation has everything item 2 needs:**
- Tarski semantics over an *arbitrary* carrier `M` — `Structure L M`, `Semiformula.Eval`,
  `Models`, `⊧ₘ` (`.lake/packages/foundation/Foundation/FirstOrder/Basic/Semantics/Semantics.lean`).
  Nonstandard models are just non-`ℕ` choices of `M`; nothing special is required to talk about them.
- Absoluteness across models — `Foundation/FirstOrder/Arithmetic/Definability/Absoluteness.lean`:
  `shigmaZero_absolute` (Δ₀/Σ₀ absolute), `sigmaOne_upward_absolute`, `piOne_downward_absolute`,
  `deltaOne_absolute`, `models_iff_of_Delta1`, `models_iff_provable_of_Delta1_param`. **These are
  the tools that discharge the standard↔nonstandard agreement** — a Δ₁-defined threshold predicate
  agrees across every `V ⊧ₘ* T`. This is exactly how the paper's "Θ represents computations"
  clause is meant to be cashed.
- `Definability/{Definable,BoundedDefinable,Hierarchy}.lean` for the Σ/Π/Δ classification and
  `DefinedFunction` graph-definability.

**The repo already does this pattern — for computations, not LUVs.** `Construction/Witnesses/
ComputationSyntax.lean` (572 lines) is the template to copy:
- `ArithmeticSemisentence 1` one-free-var schemas (`universalHaltingSchema`, etc.);
- agreement proofs `ℕ ⊧ₘ schema/[↑z] ↔ <recursion-theoretic predicate>` via `models_iff`,
  `Semiformula.eval_substs`;
- `computationClaimSentence : ComputationClaim → Sentence` erasing an arithmetic claim to a
  **propositional** atom (the repo's `Sentence = LO.Propositional.Formula ℕ`, `Framework/
  Foundations.lean:34` — the market language is propositional; FFL lives only in the Witnesses layer);
- `ComputationTheoryPresentation` carrying `Theory.Δ₁ T`, and the represented-claim interfaces
  that already lean on Σ₁ soundness for the nonstandard-world direction.

So F7's "new" content is: **redo ComputationSyntax's arithmetic→atom→agreement pattern for a
value-defining formula and rational thresholds**, then derive the existing presentation
interfaces from it instead of assuming them.

**Where the current abstraction sits (item 3/4 refactor surface):**
- `Framework/Expectations.lean` — `structure LUV where gt : ℚ → Sentence` (line 64) is a
  Dedekind-cut-of-threshold-atoms; `PCWorld.ValuesAt v X x` (line 143) is the world↔value
  coherence condition; `expectApprox`/`expect` (89–94) and the proven `ValuesAt.expectApprox_near`
  counting lemma are all *value-level* and stay as-is.
- The four caller-supplied interfaces to be *derived* rather than *assumed*: `ValuesAt`,
  `WorldValued`, `ExactTheoryPresentation`, `ConvergencePresentation`. Usage counts:
  `ExpectationProperties.lean` **63**, `QuotationAffine.lean` 35, `ComputationDP.lean` 8,
  `SelfTrust.lean` 8, plus ~10 more files — **~130 use-sites total across 14 files.**
- `Construction/Witnesses/LUVSyntax.lean` (1340 lines) already builds the **varying-sequence**
  triangular-mesh threshold-code machinery (`meshSentence`, `triangularWeight`, uniform code
  generators) and its own `convergencePresentation`/`exactTheoryPresentation`/`worldValued`
  defs — but **propositionally** (it does *not* import FirstOrder). Item 5's varying-sequence
  scaffolding is here; what's missing underneath is the arithmetic certification.

**The two named weakened endpoints (item 5):**
- `lic_linearity_of_expectation` — fixed `a,b,X,Y,Z`; paper wants an efficiently-generated
  *varying sequence*. Sequence-level cousins already exist (`BoundedSequence.exppolymax/perexpkno/
  expcoh/wubexp`, `ExpectationProperties.lean:1861/1912/1980/2204`) but carry the presentation
  interfaces and aren't all in `AxiomAudit`.
- `lic_expectation_provind` — one LUV lower bound; paper wants arbitrary bounded LUV-combination
  sequence in all three comparison forms.

### Scoped plan, in dependency order (each step green before the next)

1. **`LUVArithmetic.lean` (new Witness, ~ComputationSyntax-sized, 400–600 ln).** Define a
   one-free-variable arithmetic LUV: a `Semisentence ℒₒᵣ 1` (or a `DefinedFunction` graph) with
   proofs the theory proves unique existence and `[0,1]`-valuedness. Build the rational threshold
   `Semisentence`s `⌜X > q⌝` and prove `ℕ ⊧ₘ thresh q ↔ (definedValue > q)`. **Copy
   ComputationSyntax's `models_iff`/`eval_substs` idiom.** *Risk here is not availability but
   arithmetization labor* — expressing "unique real in [0,1] via its rational cuts" as a Δ₁
   predicate and proving properness (`ProperOn ℕ`, `ProperOn V`). Budget the most uncertainty here.
2. **Nonstandard-world agreement (the item-2 core).** Prove the threshold predicate is Δ₁ and
   apply `deltaOne_absolute` / `models_iff_of_Delta1` so `V ⊧ₘ thresh q ↔ ...` for every
   `V ⊧ₘ* T`, matching against the uniquely-defined value in the (possibly nonstandard) `V`.
   This is where the paper's "consistent worlds assign the true value" clause is actually earned.
   **If a step needs full satisfaction of an unbounded formula in a nonstandard model** (not just
   Δ₁ absoluteness) that is the one place to stop-and-report — but the computation tail suggests
   Σ₁-soundness + Δ₁ absoluteness suffices.
3. **Erasure to the propositional interface + derive the four presentations.** Map the certified
   arithmetic LUV to `Framework.LUV` via `computationClaimSentence`-style erasure, then *prove*
   `ExactTheoryPresentation`/`WorldValued`/`ValuesAt`/`ConvergencePresentation` (currently
   hypotheses) as lemmas about the erased object. Provide the uniform polynomial threshold-code
   generators the trader compilers consume (LUVSyntax's mesh generators are the propositional
   half; wire them to the arithmetic source). This is the wide, mostly-mechanical refactor across
   the ~130 sites — but done by *supplying* the instances, so most call sites shrink rather than
   change shape.
4. **Finish the paper-strength sequence endpoints (item 5).** Promote `lic_linearity_of_expectation`
   to the efficiently-generated varying sequence (consume LUVSyntax's triangular mesh), and
   `lic_expectation_provind` to arbitrary bounded LUV-combination sequences in all three comparison
   forms. Add these + their constructed-LIA instantiations to `AxiomAudit.lean` and the coverage
   checker.

### Effort estimate & recommendation

- **If Σ₁-soundness + Δ₁ absoluteness suffices for step 2 (my expectation):** roughly the size of
  **F1 (LimitCoherence) + F4 (Conditioning) combined** — call it 3–4 focused sessions, dominated by
  step 1's arithmetization and step 3's breadth. Bounded and tractable.
- **If step 2 hits a genuine full-satisfaction-in-nonstandard-models wall:** that sub-step blocks
  and F7 stays disclosed; steps 1/3/4 are still independently worth landing.

**Recommendation unchanged from the survey:** full-scope F7 is *off* the critical path to the
conditional+disclosed green endpoint, and the audit's own Disposition allows it to remain a
disclosed propositional abstraction provided public claims say the expectation tail is relative
to threshold/world-value presentation interfaces (not a first-order `def:luv` reconstruction).
The cheap honest win is **step 4 alone** — finish the sequence-level capstones on the *existing*
propositional bridge and inventory them — which closes the "weakened conclusion" half of F7
without the arithmetization. Open steps 1–3 only as a deliberate, separately-scoped spike.
See [`m7-errata-audit.md`](m7-errata-audit.md) F7 for the paper-faithfulness framing.

## ✅ Session 5 summary (2026-07-22) — F3 public diagonal constructed

The adversarial audit's F3 finding is resolved. `QuotationAffine.lean` now applies Kleene's
second recursion theorem to the named exact market program, producing a selector that prices
its own public quotation atom and decides whether that same-day price is below `p`. Its
positive and negative fibers build the `BooleanQuoteCode`; a matching FFL
`parameterizedFixedpoint` represents the same predicate, and the public bridge theorem proves
that the fixed point is equivalent to the market-price comparison for the inherited sentence.

`paradoxResistanceQuoteOfDiagonal` and `lic_paradox_resistance_ofDiagonal` construct this
artifact internally. The constructed-LIA wrapper now exposes `theoremMarketComputation` and
`theoremDiagonalQuoteCode` and accepts no caller-supplied `truth`, quote package, or
`truth_spec`. The affected quotation and computation modules build with only the repository's
standard `propext`/`Classical.choice`/`Quot.sound` dependencies.

**Next focus:** continue the adversarial audit at F8 after the F4 verification/commit, with
the F3 and F4 public endpoints frozen in `AxiomAudit.lean`.

## ✅ Session 4 summary (2026-07-22) — F2 historical maturity constructed

The adversarial audit's F2 finding is resolved. `HistoricalMaturity.lean` compiles the
finite-world maturity predicate for every uniformly emulatable trader family, proves the
compiled checker equivalent to the semantic checker, semidecides it with a single program,
and builds the required polynomial historical schedule by bounded dovetailing the logical
inductor's market and deductive-process computations.

Recurring unbiasedness, calibration, and the affine/sentence/expectation/fixed-frequency
pseudorandom capstones now construct this schedule internally. Their paper-facing APIs no
longer accept historical-verifier premises; the old conditional declarations remain under
explicit `_of_historicalVerifiers` names. The fixed-frequency infrastructure now contains
settlement clocks only, and the integration tests exercise the unconditional APIs.

**Next focus at that handoff:** F3, now completed in session 5.

## ✅ Session 3 summary (2026-07-22) — feedback and LUV complete over constructed LIA

The last property-tail instantiation is complete. `FeedbackUnconditional.lean` adds four
strictly axiom-clean endpoints over `liaHistory (theoremDP T)`:

- `lic_wub_ofComputation_unconditional` (`thm:wub`);
- `lic_wubaff_ofComputation_unconditional` and
  `boundedCombination_wubaff_ofComputation_unconditional` (`thm:wubaff`); and
- `luv_wubexp_ofComputation_unconditional` (`thm:wubexp`, completing the deferred LUV path).

The spike resolved in the cheap direction: **no feedback-specific deductive process is
needed.** `FeedbackTruthComputation` is the paper's explicit deadline-bounded program for
completed-theory values, not a presentation of literals that a DP must enumerate. The existing
`theoremDP` therefore discharges every missing market-side premise: it is computable,
`LIA_is_logical_inductor` supplies the inductor, `liaHistory_range` supplies probability bounds,
and `theoremDP_hworld` supplies finite-stage plausible worlds. The caller appropriately retains
the paper's substantive affine/LUV determination, weighting, deferral, and delayed-value program
premises.

The ordinary-sentence specialization was also closed: `FeedbackTruth.lic_wub_ofComputation`
now constructs both feedback boundaries for `thm:wub`, matching the existing affine and LUV
consumers. All eight generic/unconditional feedback consumers are in `AxiomAudit.lean`.
Full build green (2723 jobs); `AxiomAudit`, paper-node validation, theorem-label lint, and
`git diff --check` all pass.

**Next focus:** verification phase — full build and repository gates, then the deferred human
statement read-through / fresh `M7-ERRATA-AUDIT` pass. After that, the orthogonal `dd:fuel`
hardening remains before the stronger “fully done” claim.

## ⏱ Session 2 summary (2026-07-22) — property tail largely unconditional over LIA

Full build green throughout (2720 jobs), strictly axiom-clean, all label/node gates pass.
Landed this session (commits `f79807d`…`1d24ad1`):

- **Quotation / self-reference — DONE, all 3 steps.** Code-indexed redesign kills the vacuity;
  `quotation_presentation_nonvacuous` certifies `Q ∧ hworld`; all **8** endpoints unconditional
  over `LIA` (`*_unconditional` in `ComputationDP.lean`).
- **Meta-learning — DONE, 6/6.** The 5 siblings joined the halting MVP (`ComputationDP.lean`).
- **Universal semimeasure — DONE** and **Conditioning — DONE** over `LIA`
  (`UnconditionalOverLIA.lean`; empty process proved computable, `hworld` trivial).
- **`dd:fuel`** unit-cost seam recorded in the roadmap: an option-A bit-cost hardening over
  `Framework/Computable.lean` is **owed before "fully done"** (poly-fuel ⊋ poly-time; the
  equivalence is appealed to, not proved). Consolidation-phase, orthogonal to the tail.

**Key reframe established this session:** the central `LIA_is_logical_inductor` (Layer 1) is
**already proved, unconditional, strictly axiom-clean, build-enforced** — only needs the
satisfiable `ComputableDeductiveProcess DP`, discharged concretely by `theoremDP`/`emptyBit`.
There is *no* remaining proof-engineering gap in the criterion theorem; what's left there is
trust-surface work (read-through fidelity to Def 4.1.2 + the `dd:fuel` seam), not proving.

**Remaining proof engineering:** feedback and LUV are now complete (session 3); the entire
property tail is instantiated over constructed `LIA` processes, bracketing the three disclosed
boundaries. Next comes the verification phase (read-through + `M7-ERRATA-AUDIT`, including a
fresh pass over the changed quotation surface), then the orthogonal `dd:fuel` hardening.

**External:** Kraft Aristotle — first attempt (`bc2df18a…`) FAILED (returned `sorry`); resubmit
`65eaafaa-2ba0-4501-8002-8e9e2043f4d8` RUNNING at handoff (poller task `b7q730kzu`). Even a
proof only removes step 1 of 5 for the *disclosed* `M7-PREFIX-MACHINE`.

**Pre-publish:** delete `LogicalInduction/IntegrationTest.lean` before publication (Anson;
recorded in `notes/consolidation.md`). It is the M3 deference-corpus integration/regression
guard — keep it until then.

---

## ✅ M7-QUOTE-DP meta-learning MVP — DONE (2026-07-22)

The **M7-QUOTE-DP meta-learning MVP is complete** and merged (commits `ad80bd3`, `671f8c1`,
unpushed). `LogicalInduction/Construction/Witnesses/ComputationDP.lean` delivers the
project's first genuinely **unconditional, strictly axiom-clean** epistemic result over the
constructed `LIA` inductor:

> `lia_learns_halting_patterns_unconditional` (Paper node `thm:halts`) — for a Σ₁-sound
> `T ⊇ 𝗜𝚺₁`, the constructed `LIA` over a **constructed, proved-computable** provability
> deductive process learns every provably-halting pattern, with **no** market/price/`hworld`
> hypotheses remaining. `hworld` is *proved* (from `T`-consistency + Σ₁-soundness), not assumed.

What landed (all axiom-clean — `propext`/`Classical.choice`/`Quot.sound` only):
- **Tall pole A** `provable_instances_re`: `REPred (fun z => T ⊢ φ/[z])` from FFL's
  `Halting.lean` template (`definability` + `re_iff_sigma1` + `Theory.Provable.sound` +
  `internalize_provability`).
- A single combined event stream (tags 0–5), r.e. via `provable_instances_re` + `REPred`
  closure; `theoremDP` enumerates fired atoms with a fuel-clocked dovetailer.
- `theoremDP_covers` (coverage → all six enters/refutes fields) and `theoremDP_hworld`
  (the non-vacuity heart: one provability world consistent with every stage).
- **Tall pole B** `theoremDP_computable`: the enumerator is primitive recursive
  (`encode_toFinset_eq` + `eventAtom_prim` 6-way encoder + `listFilterMap`/`primrec_evaln`
  + `sentenceDedup_prim`/`sentenceInsertionSort_prim`). Full build green (2720 jobs).

**Scope note carried out as planned:** computation side only. The *quotation* side remains
blocked by the vacuity obstruction (below) and still needs a frozen-boundary redesign.

---

# ✅ QUOTATION RESCUE — COMPLETE, all 3 steps (2026-07-22)

The quotation family is **fully unconditional over the constructed `LIA`** — vacuity fixed,
certified, and all eight endpoints instantiated (`logical-induction`, full build green,
strictly axiom-clean). **Step 3 done:** `lic_introspection_ofCode_unconditional`,
`lic_paradox_resistance_ofDiagonal_unconditional`, `lic_expectations_of_probabilities_ofCode_unconditional`,
`lic_iterated_expectations_ofCode_unconditional`, `lic_self_trust_ofRepresentation_unconditional`,
`lic_expected_future_expectations_ofRepresentation_unconditional`,
`lic_no_expected_net_update_ofRepresentation_unconditional`,
`lic_no_expected_net_update_conditional_ofRepresentation_unconditional` (all in
`ComputationDP.lean`) discharge market / `IsLogicalInductor` / `Q` / `hworld` via
`quotationPresentation` + `theoremDP_hworld` + `LIA_is_logical_inductor` + `liaHistory_range`;
the paradox-resistance endpoint additionally constructs its own self-referential quoted
decision from `theoremMarketComputation`. Steps 1–2 detail below.

## Steps 1–2 (redesign + certify) — DONE

The quotation-side vacuity is **fixed and certified** (full build green, strictly axiom-clean).
What landed:

- **Redesign (code-indexed), step 1.** `QuotationTheoryPresentation`'s two quote fields no
  longer quantify over free schema pairs. They are now keyed by a selector `code : ℕ` and
  `input`, with two **fixed** universal schemas `universalQuotePos`/`universalQuoteNeg`
  (`= codeOfREPred` of the value-1 / value-0 fibers of the universal computation, folded pair
  `⟨code,input⟩`). The `⊤,⊤` attack can no longer be phrased (schemas fixed & complementary).
  Field **names unchanged** ⇒ `#assert_fields QuotationTheoryPresentation` still frozen; the
  disclosed change is in field **types**. `BooleanQuoteCode`/`RationalQuoteCode`/
  `ParameterizedDiagonalQuoteCode` re-shaped to carry `code` (+ completeness data);
  `#assert_fields` for those three re-frozen in `AxiomAudit.lean`. `ArithmeticDecision`
  (now dead) removed. Diagonal decoupled per plan (`represents_fixedpoint` faithfulness cert;
  `diagonal_law` restated about `parameterizedFixedpoint body` directly).
- **Construction + `hworld` (certify the fix), step 2.** The **same** computable `theoremDP`
  (`ComputationDP.lean`) now also enumerates the quotation atoms (event tags 6/7), so it
  inhabits the redesigned `QuotationTheoryPresentation` (`quotationPresentation`) **and**
  `theoremDP_hworld` covers tags 6/7 (positive: coverage; negative: determinism/fiber
  exclusivity via `re_complete`). `quotation_presentation_nonvacuous` is the explicit `N+`
  certificate: `∃ DP, ∃ (_ : QuotationTheoryPresentation DP T), ∀ n, ∃ v, v.ConsistentWith
  (DP.D n)` — i.e. `Q ∧ hworld` is satisfiable. Vacuity gone.

**Disclosure owed & recorded (type-`(c)`-adjacent narrowing, `dd:quote-code`):** quotation now
only quotes **computable/decidable decisions of the market state** (selector `code` decodes to
a total `{0,1}` decider; positive = value-1 fiber, negative = value-0 fiber). This is *not* a
new semantic restriction — the paper's dual-schema `ArithmeticDecision` already required dual
weak representation (= decidability). It *is* a real modeling commitment on the presentation.
The interface stays general over any `DP`/`T`; only the quotable-decision class is fixed. See
docstrings in `QuotationAffine.lean` (`universalQuotePos`/`BooleanQuoteCode`) and
`ComputationDP.lean` (`quotationPresentation`).

**F3 follow-on (session 5): complete.** The old `truth_spec` input has been removed from the
generic and unconditional paradox-resistance endpoints. A Kleene-fixed selector prices its
own public atom, and `diagonalPriceBody` plus FFL parameterized diagonalization represent that
same predicate arithmetically.

---

# 🎯 (superseded) THE NEXT FOCUS — quotation / self-reference non-vacuity rescue

Anson's next focus (2026-07-22). The introspection / self-trust / expectation-representation /
paradox-resistance family (`M7-QUOTE-AFFINE`, endpoints `lic_introspection_ofCode`,
`lic_paradox_resistance_ofDiagonal`, `lic_self_trust_ofRepresentation`,
`lic_expectations_of_probabilities_ofCode`, `lic_iterated_expectations_ofCode`, the
`_ofRepresentation` net-update endpoints) was **vacuous** and needed rescue before
it can be made unconditional over `LIA`. **Steps 1–2 are now DONE (see the section above);**
this analysis is retained for the step-3 instantiation and the diagonal handling.

### The exact obstruction

`QuotationTheoryPresentation` (`QuotationAffine.lean:103–114`) has two fields quantifying over
**two independent, arbitrary schemas**:

```lean
quote_positive_enters : ∀ (positive negative : ArithmeticSemisentence 1) (input : ℕ),
    T ⊢ positive/[↑input] → ∃ k, quotationClaimSentence positive negative input ∈ DP.D k
quote_negative_refutes : ∀ (positive negative : ArithmeticSemisentence 1) (input : ℕ),
    T ⊢ negative/[↑input] → ∃ k, (∼quotationClaimSentence positive negative input) ∈ DP.D k
```

The atom is keyed on **both** schemas; the positive literal fires from `T ⊢ positive/[i]`, the
`∼` of the *same atom* from `T ⊢ negative/[i]`, and nothing ties the two schemas together. Take
`positive = negative = ⊤`: `T ⊢ ⊤/[i]` is trivial, so both fire on `X = quotationClaimSentence
⊤ ⊤ i`, forcing `X` and `∼X` into a common stage (by `mono`) ⇒ no consistent world ⇒
`Q ⟹ ¬hworld`. So `(Q ∧ hworld)` is unsatisfiable and every consuming endpoint is vacuously
true. (Computation escapes this: its enters/refutes quantify over the **input only**, with
**fixed** complementary schemas, so both-firing means `T` proves a Σ₁ statement and its
standard-model complement — killed by Σ₁-soundness. Quotation lost that guardrail by freeing
the pair.) Note the consumers **never use** the freedom: every call site passes
`q.decision.positive, q.decision.negative` from an `ArithmeticDecision`, which already bundles
complementarity (`positive_standard`/`negative_standard`). The bad field simply promises more
than any consumer needs. See [[quotation-presentation-vacuity]].

### The rescue = two coupled moves (need both)

- **(A) Boundary redesign** kills the *vacuity* (makes `Q ∧ hworld` satisfiable).
- **(B) Construction** builds a concrete quotation DP, proves its `hworld`, inhabits the
  redesigned `Q`, and instantiates over `liaHistory` — making the endpoints *unconditional*.

### Recommended redesign — mirror the MVP (index by predicate code)

Make quotation structurally identical to computation: **fix the schema-former to
`codeOfREPred` and index enters/refutes by a predicate code + input**, not arbitrary schemas.

```lean
-- pos code = codeOfREPred (decode code); neg code = codeOfREPred (¬ decode code)
quote_positive_enters : ∀ (code input : ℕ),
    T ⊢ (quoteSchemaPos code)/[↑input] →
      ∃ k, quotationClaimSentence (quoteSchemaPos code) (quoteSchemaNeg code) input ∈ DP.D k
quote_negative_refutes : ∀ (code input : ℕ),
    T ⊢ (quoteSchemaNeg code)/[↑input] →
      ∃ k, (∼quotationClaimSentence (quoteSchemaPos code) (quoteSchemaNeg code) input) ∈ DP.D k
```

- **Vacuity gone:** the `⊤,⊤` attack needs `⊤ = codeOfREPred truth` *and* `⊤ = codeOfREPred
  (¬truth)` at once — impossible.
- **`hworld` provable verbatim from the MVP:** world believes the atom iff `T ⊢ (pos code)/[i]`;
  both literals ⟹ `T ⊢ pos/[i]` and `T ⊢ neg/[i]` ⟹ (Σ₁-soundness + `codeOfREPred_spec`)
  `truth i ∧ ¬truth i`, contradiction. This is `theoremDP_hworld`'s tag-3 argument.
- **DP = the MVP construction with the schema as a decoded argument.** Fires-predicate is
  `T ⊢ codeOfREPred(decode code)/[i]` — provability where the *formula is a computable function
  of `code`*. The M7-QUOTE-DP spike already cleared this (`Bootstrapping.subst`/`⌜⌝`/`numeral`
  primrec ⇒ `⌜codeOfREPred(decode code)⌝` computable in `code`). This is the **one genuinely new
  piece** over the MVP; everything else reuses [[quote-dp-mvp-computable-recipe]].
- Consumers barely change: `BooleanQuoteCode`/`RationalQuoteCode` gain a `code : ℕ` field with
  `decision = ArithmeticDecision.ofComputable (decode code)`; `.reflected` proofs pass `code`.

_Lighter variant of (A):_ quantify the fields over `ArithmeticDecision T truth` directly. Kills
the vacuity with a smaller diff, but gives **no** computable enumeration for (B) (can't decode
an `ArithmeticDecision` from ℕ). Use it only to unblock the audit fast; go code-indexed for the
construction.

### Historical diagonal analysis — superseded by the session 5 F3 repair

The question "does paradox resistance need the *atom* to carry the fixed-point schema, or only
the fixed-point *law*?" is **resolved: neither.** Evidence (grepped whole `LogicalInduction/`):
`positive_fixedpoint`/`body`/`parameterizedFixedpoint` are used **only** inside the standalone
`ParameterizedDiagonalQuoteCode.diagonal_law` (`QuotationAffine.lean:2243`); `diagonal_law` is
consumed by **nothing**; and `paradoxResistanceQuoteOfDiagonal` (2259) + `lic_paradox_resistance_ofDiagonal`
(3278) use **only** `q.toBooleanQuoteCode` + `truth_spec` (they go through `reflected` /
`completedGated{Complement,Affirmative}Quote`, all of which take a bare `BooleanQuoteCode` and
structurally cannot see the fixed-point fields). So the fixed-point schema is a pure
**faithfulness certificate**, not a proof ingredient of any endpoint.

**Consequence — the diagonal rides the universal code-indexed DP with no special-casing:**

- Atom uses `codeOfREPred truth` (`truth n ↔ P n (atom n) < p` is computable — LIA prices are
  rational/computable). Same DP, same tag-3 `hworld` argument. **No dedicated `diagonal_enters/refutes`
  field. No paradox-resistance proof changes.**
- Keep `diagonal_law` as a **standalone honesty artifact** (a genuine `parameterizedFixedpoint body`
  representing the same `truth` exists + satisfies the diagonal equation). Optionally add a one-line
  bridge `T ⊢ codeOfREPred truth 🡘 parameterizedFixedpoint body` (both represent `truth`) so the
  atom's schema *is* the fixed point up to `T`-provable equivalence.
- **Honest nuance (instantiation, not boundary):** the fixed point is still *essential* to
  **construct `truth_spec`** when instantiating paradox resistance over LIA — exhibiting `truth`
  with `truth n ↔ price(atom n) < p` is circular, and `parameterizedFixedpoint` is what breaks the
  circularity. So the fixed point moves *out* of the atom's schema (→ `codeOfREPred`, for the
  DP/`hworld`) and *stays* where it does real work: defining the self-referential `truth` in the
  instantiation, plus the faithfulness cert. This keeps the quotation family at the **low end** of
  the ~2–4 session estimate — one universal DP, no boundary special-casing.

### Order of operations (frozen-surface aware)

The `⊤,⊤` vacuity argument is taken as an established (traced, not kernel-checked) premise —
we redesign to make it inapplicable rather than first proving it. The redesign is only truly
"fixed" once an inhabitant of `Q ∧ hworld` exists (step 2), which is what certifies satisfiability.

1. **Redesign the fields** (code-indexed), **re-freeze** `#assert_fields QuotationTheoryPresentation`
   (Tier-2 audited surface — this is the *disclosed* frozen-boundary change), fix the ≤6 consumer
   proofs, **re-run `M7-ERRATA-AUDIT`** over the changed surface. (~1 session; the frozen-surface
   care lives here.) This re-shapes the boundary but does **not** by itself certify non-vacuity.
2. **Build the quotation DP + `hworld` = certify the fix.** The MVP recipe with the schema as a
   decoded argument: construct the DP, prove `hworld`, **inhabit `Q`** (this is the step that
   *demonstrates* `Q ∧ hworld` is satisfiable — the real "vacuity is fixed" milestone). (~1–2
   sessions; a known pattern except the formula-as-argument enumeration and the diagonal decoupling.)
3. **Instantiate over `liaHistory`** — add `_unconditional` corollaries for introspection /
   self-trust / expectations / paradox resistance, resolving the diagonal per above. (Follow-on.)

**Disclosure owed when this lands:** narrowing quotation to `ofComputable` (code-indexed)
decisions asserts *the market only quotes computable decisions of its own state* — true of the
paper's reflection/expectation/self-trust constructions, but a real modeling commitment. Record
it in the ledger as a type-`(c)`-adjacent narrowing, don't let an auditor find it. Not blocked
by any missing Foundation lemma (`codeOfREPred`/`re_complete`/FFL fixed points already used here).

---

# Remaining proof engineering — full accounting (2026-07-22)

**Framing.** Two layers stand between the corpus and a *fully unconditional* formalization
(bracketing the 3 disclosed witnesses):

- **Layer 1 — the inductor exists. DONE.** `LIA_is_logical_inductor : ComputableDeductiveProcess
  DP → IsLogicalInductor (liaHistory DP) DP`, strictly axiom-clean. So the `[IsLogicalInductor P
  DP]` hypothesis on the whole property tail is **not a real gap** — instantiate `P := liaHistory
  DP` (one line). The criterion, trading-firm dominance, and efficient-computability plumbing all
  landed clean.
- **Layer 2 — discharge the boundary witnesses + `hworld`, per family.** Each property theorem
  also assumes (a) a boundary/representation structure and (b) `hworld : ∀ n, ∃ v, v.ConsistentWith
  (DP.D n)`. There are ~166 sites threading `hworld`; before the MVP it was discharged in **zero**.
  "Unconditional" = per family: construct a concrete DP, **prove** `hworld`, **inhabit** the
  boundary structure, instantiate over `liaHistory`. The MVP is the first (and only) endpoint that
  does all four; it also makes the hard part (r.e.-provability substrate + a *proved* `hworld`) a
  reusable template ([[quote-dp-mvp-computable-recipe]]).

**Per-family status and remaining work** (bracketing the 3 disclosed):

| Family (paper cluster) | State | Remaining | Est. |
|---|---|---|---|
| **Meta-learning** (halting/consistency, `M7-COMP-SYNTAX`) | **COMPLETE** (2026-07-22): all 6 endpoints unconditional over `LIA` (`*_unconditional` in `ComputationDP.lean`) | — (done) | **0** |
| **Universal semimeasure** (`M7-DUS-PREFIX-SYNTAX`) | **DONE** (2026-07-22): `lic_domination_universalSemimeasure_unconditional` over LIA on the proved-computable empty process (`UnconditionalOverLIA.lean`); `hworld` trivial | Only the *disclosed* `M7-DUS-APPROX` approximation `A`/`emit` remains an input (bracketed); full Occam bound also needs disclosed Kraft | **~0 (disclosed remainder)** |
| **Conditioning** (`M7-SCON-*`) | **COMPLETE** (2026-07-23): the direct finite-zero compiler proves fixed and growing `thm:scon`; `lic_conditioned_fixed_unconditional` and `lic_conditioned_growing_unconditional` instantiate the constructed `LIA` (`ConditioningCompiler.lean`, `UnconditionalOverLIA.lean`) | — (only joint consistency and ordinary condition/process computation remain) | **0** |
| **LUV combinations** (`M7-LUV-SYNTAX`) | **COMPLETE** (2026-07-22): `luv_wubexp_ofComputation_unconditional` over `liaHistory (theoremDP T)` | — (caller retains the paper's exact-theory presentation and delayed-value program) | **0** |
| **Feedback / pseudorandomness** (`wub`, `M7-FEEDBACK-TRUTH/EMIT`) | **COMPLETE** (2026-07-22): all four computation-backed consumers instantiated over constructed `LIA`; ordinary `thm:wub` specialization added | — (no new DP was needed; `theoremDP_computable` + `theoremDP_hworld` discharge the market side) | **0** |
| **Quotation / self-reference** (`M7-QUOTE-AFFINE`) | **COMPLETE** (2026-07-22): redesign + certify + all 8 endpoints unconditional over `LIA` | — (done) | **0** |

**Bottom line:** proof engineering for the property tail is complete, including quotation,
feedback, and LUV. The feedback uncertainty collapsed because its `_ofComputation` boundary is
operational data rather than a DP presentation, so the established `theoremDP`/`hworld`
corollary pattern applies directly. Remaining work is verification/read-through and the
separately disclosed `dd:fuel` hardening, not another property construction.

**Verification still owed (not proof engineering, but part of "done"):** the deferred **human
statement read-through** (Anson) over the frozen surface, then the final `M7-ERRATA-AUDIT` pass —
the steps that certify the statements are the paper's. Sequencing override in `CLAUDE.md` still
governs.

_Original MVP brief retained below for the quotation-side redesign, which reuses the same shape._

## Where things stand (audit + GL discharge + QUOTE-DP spike done, 2026-07-21)

The **12/15 conditional+disclosed green endpoint is complete**; consolidation (step 2 of the
`CLAUDE.md` sequencing override) is done. Recent landings (older consolidation detail is in
git history):

- **`M7-ERRATA-AUDIT` complete** (`notes/m7-errata-audit.md`). No soundness defects on the
  critical path. One disclosure-scope finding **F1** (introspection/self-trust/meta-learning
  family conditional on an arithmetic-representability substrate no in-repo object inhabits),
  **now upgraded** to a concrete **vacuity finding** on the quotation side (below).
- **GL fixed-point axiom discharged** — the whole repo is now strictly axiom-free. Via the
  vendored autoformalized `ProvabilityLogic/` sequent calculus (Aristotle); notations
  `scoped` to avoid Foundation collisions. See the Aristotle section.
- **`M7-QUOTE-DP` spike done — verdict GO.** Provability-in-`T` r.e. is assemblable (no
  Foundation wall); details + recipe in the `M7-QUOTE-DP` section.

Earlier consolidation landings (still true, now background):

- **Paper-node inventory, two tiers, build-enforced.** `AxiomAudit.lean` (a
  `@[default_target]`, so `lake build`/CI runs it) is the endpoint inventory: Tier 1 = 103
  proof endpoints under `#assert_axioms_clean`; Tier 2 = boundary structures under a new
  `#assert_fields` (freezes each structure's hypothesis fields — adding/removing a field
  fails the build). Membership is mechanical: a structure is Tier 2 iff it appears in a
  Tier-1 endpoint's type, transitively through fields (`SurfaceProbe.lean`). Rationale and
  judgment calls: `notes/endpoint-inventory.md`.
- **`Paper node:` annotations** on every inventory member's docstring, labels verbatim from
  `notes/1609.03543v5-main.tex`. Enforced by `scripts/check-paper-nodes.sh` (every cited
  label exists; every member carries one). `scripts/lint_paper_labels.py` is now blocking
  (every `theorem` ⇔ a paper node; no `private theorem`).
- **Whole-repo axiom audit, now strictly clean throughout.** `AxiomAudit.lean` covers
  `ModalAgents/` too. The former sole intentional axiom `glFixedPoint_thm42` has been
  **discharged** (2026-07-21) via the autoformalized `ProvabilityLogic/` sequent calculus
  (Aristotle job `9226321a…`, validated in-repo, notations scoped to avoid Foundation
  collisions); every ModalAgents endpoint is now under strict `#assert_axioms_clean`.
- **Duplication sweep.** Removed two genuine duplicate helper lemmas (`max_sub_max_neg`,
  `oneMinus_denote`). Construction/ has no duplicate *facts* — its parallel shapes
  (`*FromStages`/`*FromStageLists`, triangular/gap/frame families) are by-design over
  distinct types.
- **Stale-reference repair.** Fixed a merged-away README path (`StrictSemimeasure.lean` →
  `UniversalSemimeasure.lean`) and three dead `PROGRESS.md` pointers (that ledger was
  deleted; the comments are now self-contained). Includes a live `thm:ifp` paper-erratum
  note in `FinitePerturbations.lean`; the durable paper-level record and stretch goal now
  live in `notes/logical-induction-paper-errata.md`.

**State:** working tree clean; full `lake build` green (2720 jobs); AxiomAudit strictly clean
(no intentional axioms anywhere). Several commits on `logical-induction` unpushed (per Anson's
workflow, nothing is pushed without asking).

## What remains, in order

> Superseded by **"Remaining proof engineering — full accounting"** and **"THE NEXT FOCUS —
> quotation non-vacuity rescue"** at the top of this file (2026-07-22). Kept as a one-line index:
> (1) ~~M7-QUOTE-DP MVP~~ DONE · (2) quotation non-vacuity rescue — **the next focus** · (3) the
> four near-trivial family finishes (meta-learning siblings, universal-semimeasure, conditioning,
> LUV) · (4) feedback/pseudorandomness DP · (5) human read-through + paper comparison · (6)
> optional Kraft/`M7-PREFIX-MACHINE`.

---

# THE NEXT TASK — M7-QUOTE-DP meta-learning MVP

**Goal.** Produce the project's first *unconditional* epistemic theorem over the constructed
`LIA` inductor: "there is a concrete computable deductive process `DP` such that `LIA` over
`DP` provably learns provable halting patterns" (or a sibling meta-learning endpoint), with
**no remaining hypotheses** — in particular the market non-vacuity `hworld` is *proved*, not
assumed. This turns one `_ofComputation` endpoint from conditional-on-assumed-substrate into
constructed-over-LIA. Read the `M7-QUOTE-DP` section below first (spike verdict + recipe).

**Scope — computation side ONLY.** Build `ComputationTheoryPresentation DP T` (fixed schemas:
`universalHaltingSchema`, …). Do **not** touch `QuotationTheoryPresentation` — it is blocked
by the vacuity obstruction (below) and needs a frozen-boundary redesign, which is a separate,
larger task. The computation presentation is consistently inhabitable; the quotation one is not.

**Plan (est. ~4–5 focused sessions; tall poles flagged):**
1. Fix `T := 𝗜𝚺₁`; gather instances (`Theory.Δ₁`, `𝗜𝚺₁ ⪯ T`, `SoundOnHierarchy 𝚺 1`,
   `𝗥₀ ⪯ T`). ~½ session; risk = FFL instance resolution.
2. **[tall pole A]** Assemble `REPred {z | T ⊢ universalHaltingSchema/[z]}` (and the refutes
   duals) following `Foundation/FirstOrder/Incompleteness/Halting.lean:25-27`:
   `Provable.definable` (Σ₁ via `definability`) + `re_iff_sigma1` + `Theory.Provable.sound`.
   ~1 session; risk = Bootstrapping coding (`subst`/`⌜⌝`/`numeral`).
3. **[tall pole B]** Wrap the r.e. semi-decider into a monotone `Finset Sentence` stage
   function `D n` and prove `ComputableDeductiveProcess DP`. Reuse the proven dovetail infra
   — `dovetailFound` / `polyFueled_dovetailFound` / `dovetailFound_mono`
   (`Construction/Witnesses/M7Witnesses.lean:787+`). No "r.e. set → DP" helper exists yet, so
   this glue is new but built on proven primitives. ~1 session; **residual risk = Primrec over
   `Finset` (see [[li-primrec-natsqrt-blowup]] — scope `irreducible Nat.sqrt`).**
4. Prove `enters`/`refutes` from enumeration coverage, and **`hworld`** (each stage
   consistent, from `T`-consistency + fixed complementary schemas). ~1 session.
5. Assemble `ComputationTheoryPresentation` and instantiate one meta-learning corollary over
   `LIA` (consumer already exists in `Construction/Witnesses/ComputationSyntax.lean`). ~½ session.

**Derisking move (recommended first sitting):** do tall pole B in isolation on a trivial
predicate — build the computable `Finset`-stage program from `dovetailFound` and prove
`ComputableDeductiveProcess`. If Primrec-over-`Finset` behaves, the ~week estimate is solid;
if it fights back you learn it in one session, not a week. The spike cleared "provability is
r.e."; it did **not** clear this piece.

**The atom-coding caveat.** The stage program must emit *exactly* `haltingClaimSentence z`
(and its negation) — the frozen coding. Preserve literal token/list equalities at the
representation boundary; semantic equality is not enough for the witness (a repeated lesson).

## Aristotle experiments in flight (external state — survives context, IDs do not)

Two jobs testing whether Aristotle can discharge remaining hard pieces. **Job IDs live only
here now — a fresh context needs them to poll.** Trust rule: a returned proof is trusted
only after it compiles in *this* repo; the kernel is the gate, never Aristotle's word.

- **GL fixed-point axiom** (`glFixedPoint_thm42`) — **DONE, integrated 2026-07-21.**
  Aristotle job `9226321a-32f8-414b-9d30-6ef06093b7f0` returned a complete sorry-free proof.
  Its ~9.5k-line `ProvabilityLogic/` sequent calculus was vendored into the repo (a
  `lean_lib` in `lakefile.lean`), validated to build against our Foundation @ aada66ef
  (868 jobs), and its `Formula`-level notations were made `scoped` to stop them colliding
  with Foundation's modal notation in `ModalAgents`. The `axiom` in `FixedPoint.lean` is
  replaced by a proved `theorem` via the `GlFixedPointBridge` translation; AxiomAudit now
  asserts the cooperation endpoints strictly clean. Kernel-gated (interior not human-read),
  disclosed in the README like Brouwer. Original download kept at
  `…/scratchpad/gl-result/gl-fixedpoint_aristotle/`.
- **Kraft inequality** (`kraft_inequality`, the Mathlib-only core of `M7-PREFIX-MACHINE`).
  **Submitted 2026-07-22, FAILED.** Aristotle job `bc2df18a-a33d-4c0f-a5ec-e048986d85df`
  completed but returned the file with the `sorry` unchanged (no proof produced). Options:
  resubmit with a sharper hint (the counting argument needs an explicit length-`L` block
  enumeration Mathlib doesn't hand you), or prove it manually. Statement in
  `notes/m7-prefix-machine-scope.md`; Mathlib-only, validated to elaborate in-repo. Note even
  a proof only removes step 1 of 5 for `M7-PREFIX-MACHINE` (a disclosed boundary).

**Scratchpad projects may be ephemeral** (session-specific dir):
`…/scratchpad/gl-fixedpoint/` and `…/scratchpad/kraft/`. Both are tiny and reconstructible —
the Kraft statement is in the scope note; the GL project is `require Foundation @ aada66ef…`
+ the `Modalized`/`diag` defs + the axiom-as-`sorry` (see `ModalAgents/FixedPoint.lean:45`). If
resubmitting, use `scripts/aristotle-prove.sh <project-dir> "<prompt>"`.

## Deliberately disclosed boundaries

- `M7-PREFIX-MACHINE` — supplies standard universal self-delimiting-machine, from-below
  weight, finite Kraft, and fixed negation-overhead facts for Occam Bounds; the paper-
  specific market proof is already formalized. Optional post-target showcase; the finite
  Kraft core is the Aristotle-able piece (`notes/m7-prefix-machine-scope.md`).
- `M7-DUS-APPROX` and `M7-STRICT-SEPARATORS` — remain disclosed unless Anson reopens them.

These three are the only intentional disclosures at the 12/15 target. The audit should
confirm no fourth boundary is assumed anywhere it isn't named.

## Recorded future tranche — `M7-QUOTE-DP` (arithmetic-representability substrate)

Surfaced by `M7-ERRATA-AUDIT` finding F1 (`notes/m7-errata-audit.md`). The
introspection / self-trust / expectation-representation / meta-learning / paradox-resistance
family is conditional on `QuotationTheoryPresentation` / `ComputationTheoryPresentation`
(and the diagonal codes), which **no in-repo construction inhabits** — and nothing connects
that family to the constructed `LIA`. Not a soundness bug (disclosed per-boundary in the
README), but a disclosure-scope gap: "12/15 constructed" reads as if these results reach the
constructed inductor; they do not.

### Vacuity obstruction — computation side OK, quotation side blocked (traced 2026-07-21)

Attempting the construction surfaced what the statement-level audit missed. The two
presentations behave differently under the market non-vacuity hypothesis
`hworld : ∀ n, ∃ v, v.ConsistentWith (DP.D n)` (`ConsistentWith v D := ∀ φ ∈ D, v.Holds φ`, so a
stage containing both `X` and `∼X` has no consistent world):

- **`ComputationTheoryPresentation` — consistently inhabitable.** Its enters/refutes fields
  quantify over inputs `z` for **fixed** schemas. `T` consistent ⟹ never proves both
  `haltingSchema/[z]` and `∼haltingSchema/[z]` ⟹ `haltingClaim z` and `∼haltingClaim z` never
  co-occur. **This is the MVP target.**
- **`QuotationTheoryPresentation` — NOT inhabitable alongside `hworld`.** `quote_positive_enters`/
  `quote_negative_refutes` quantify over **arbitrary** `positive negative : ArithmeticSemisentence 1`.
  Take `positive = negative = ⊤` (or `#0 = #0`): `T ⊢ ⊤/[i]` trivially, so `enters` forces the
  atom `X = quotationClaimSentence ⊤ ⊤ i` into `DP` **and** `refutes` forces `∼X` in — an
  inconsistent stage, so `hworld` is false. Hence **any** `Q : QuotationTheoryPresentation ⟹ ¬hworld`,
  so the conjunction `(Q ∧ hworld)` in `lic_introspection_ofCode` / `lic_paradox_resistance_ofDiagonal`
  / the `_ofCode`/`_ofRepresentation` endpoints is **unsatisfiable → those Tier-1 endpoints are
  vacuously true**. This *upgrades* audit finding F1 from disclosure-scope to a genuine mode-1
  vacuity, and is why the quotation side needs a frozen-boundary redesign (restrict the quote
  fields to complementary decisions), not just a DP. The `⊤,⊤` argument is traced but not
  kernel-checked; the plan is to redesign so it no longer applies (not to first prove it), and to
  certify the fix by inhabiting `Q ∧ hworld`. See THE NEXT FOCUS above and
  [[quotation-presentation-vacuity]].

The fix is a genuine construction, and — unlike Brouwer/GL — **not blocked by any missing
Foundation lemma**; the FFL pieces are already used by `M7-COMP-SYNTAX`/`M7-QUOTE-AFFINE`
(`codeOfREPred`, `re_complete`, `DeductiveProcessComputation.union`, `deductiveStageCondition`).
Shape (full family; the MVP does only step 1's computation half + a computation corollary):
1. Build a concrete deductive process enumerating the theorems of a fixed Σ₁-sound theory
   `T` (e.g. `𝗜𝚺₁`), reusing the SCON stage/union machinery.
2. Discharge `QuotationTheoryPresentation`/`ComputationTheoryPresentation` for it:
   `theory_sigmaOne`/`theory_deltaOne` from `T`'s strength; `quote_positive_enters` /
   `quote_negative_refutes` from FFL provable-⇒-enumerated representability.
3. Add a corollary instantiating the `_ofCode`/`_ofDiagonal`/`_ofRepresentation`/
   `_ofComputation` endpoints over `LIA` on that DP — turning the family from
   conditional-on-assumed-substrate into unconditional-over-a-concrete-inductor.
   Would let the "12/15 constructed" headline honestly cover the self-reference span.

M7-scale (multi-session); tractable and unblocked. Deferred by Anson 2026-07-21 (record only).

**Spike done 2026-07-21 — verdict GO (no Foundation wall).** The one go/no-go risk was
whether Foundation exposes provability-in-`T` as a meta-level r.e./computable object (needed
because `quote_positive_enters` is ∀-quantified over all provable instances, so the DP must
enumerate them). It is not pre-packaged as `REPred (T ⊢ ·)`, and `Derivation` is a
proof-relevant `Type _` (not `Encodable`) — but the r.e. enumeration is **assemblable** from
ingredients Foundation already uses in its own incompleteness proofs
(`FirstOrder/Incompleteness/Halting.lean:25-27` is the template):
- `Provable.defined`/`Provable.definable` + the `definability` tactic: internal `T.Provable`
  is `𝚺₁-Predicate` (`Bootstrapping/Syntax/Proof/Basic.lean`).
- `re_iff_sigma1 : REPred P ↔ 𝚺₁-Predicate P` (`Incompleteness/First.lean`).
- internal-provability ↔ `⊢` bridge (`Theory.Provable.sound`; the `□`/provability iff used
  across Solovay/Jeroslow/Yablo).
- `Bootstrapping.subst`/`.neg`/`⌜⌝`/`numeral` are primrec, so the formula-as-argument coding
  (`⌜positive⌝` as a computable function of `positive`'s code) is supported.

So the labor is: (1) assemble `REPred {(pos,neg,i) | T ⊢ pos/[i]}` following the Halting.lean
pattern; (2) turn that semi-decider into a growing computable `Finset Sentence` stage program
(dovetail — repo has the `Nat.rfindOpt`/`evaln` patterns in `LIAComputation.lean` and
`DeductiveProcessComputation.union` for stage assembly), coding each provable instance as its
`quotationClaimSentence` atom; (3) prove `enters`/`refutes` from enumeration coverage; (4)
pick `T` for `theory_sigmaOne`/`theory_deltaOne`; (5) instantiate the corollary over LIA. The
one delicate boundary is the atom-coding alignment (the stage program must emit exactly
`quotationClaimSentence`/`quotationClaimCode` — the "preserve literal token equalities" caveat).
**MVP (the active next task): the *computation* half only** — DP + `ComputationTheoryPresentation`
+ `hworld` + one meta-learning corollary over LIA (e.g. learns provable halting patterns). The
quotation flagships (paradox resistance, self-trust) are the blocked side — see the vacuity
obstruction above; they need the boundary redesign first, not this MVP.

## Verification and commit discipline

Before any commit, smallest relevant build first, then:

```sh
lake build
rg -n '(^|[[:space:]])(sorry|admit)([[:space:]]|$)' LogicalInduction ModalAgents --glob '*.lean'
./scripts/check-paper-nodes.sh
python3 scripts/lint_paper_labels.py
git diff --check && git status --short
```

Axiom reports of any new public endpoint must contain only `propext`, `Classical.choice`,
`Quot.sound` — the whole repo (LogicalInduction and ModalAgents) is now strictly clean, with
no intentional axioms. Keep historical detail in git rather than appending superseded plans
below the active handoff.

## Aristotle usage

Via `scripts/aristotle-prove.sh`; only after a goal is fully stated and self-contained.
Prefer small extracted Mathlib-only projects, not the whole repo. `ARISTOTLE_API_KEY` must
be in the environment. Toolchain versions may differ; a returned proof is trusted only after
it compiles here.

## Reusable construction notes

- Search before proving. Anchors: `codeEvalnNat_polyFueled`, `deadlineRun`,
  `scheduledMatch`, `segPrefix_polyFueled`, `segLocate_polyFueled`,
  `PolySegStream.concatVar`, `PolySequence.priceFeature_polySeg`, `PGenerableWeighting.polySeg`.
- Deep `PolyFueled` proofs with nested `Nat.unpair` can trigger `Nat.sqrt` whnf blowups;
  prefer a narrow local `attribute [irreducible] Nat.sqrt` over raising heartbeats.
- Preserve literal token/list equalities at representation boundaries; semantic equality
  alone is not enough for the witness constructors.
- Keep computation certificates conclusion-free; economic/asymptotic conclusions belong in
  the already-proved consumer layer.
