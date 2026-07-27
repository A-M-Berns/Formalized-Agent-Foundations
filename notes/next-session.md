# Logical Induction — handoff

_Last updated: 2026-07-26 (collapse + prefix machine + FULL EC-SEQ flip merged at `ca0d452`; RPN-5 transducer core merged, endpoints in flight).
Branch: `logical-induction`._

# 🎯 ACTIVE PLAN 2 — remaining: RPN-5 + EC-SEQ (updated 2026-07-26, collapse landed)

Goal (Anson): all remaining 𝓔𝓒-sequence-hypothesis work via the layered RPN route,
landed in **collapsed single-class form** (consolidation directive).

## DONE — the collapse surgery (steps A–F, commits `212174d`..`4148c02` + F cleanup)

* RPN-1..4 (coding, contraction, class, primrec decode) — in git history.
* **A**: M7Witnesses partitioned — simulation core + clocked emission + `toTok₂` in
  `Framework/Emission.lean`; freeze-coupled parser control stayed (names stable).
* **B**: grammar/decode defs (`rpn`, `parseRpn`, `unRpnTokens`, `unRpn`,
  `clockedTrader`, the class) live in `Framework/Criterion.lean` beside the
  serializers; `RpnSentence.lean` keeps the lemma corpus.
* **C**: inclusions are the emission constructors in `Framework/RpnEmission.lean`;
  `digitize_flatMap` moved to Criterion; RpnCriterion deleted (primrec assemblies
  moved into LIACompiler ahead of the enumeration compiler).
* **D+E** (`4148c02`): plain `EfficientlyComputable` := the symbol-metered `def:ec`
  (legacy whole-number def deleted; old traders renamed
  `clockedTraderTok`/`clockedTraderDigit`, internal).  ONE `IsLogicalInductor`
  (marketComputable, processComputable, noExploit over the collapsed class);
  `IsLogicalInductor₂` gone.  Constructors `EfficientlyComputable.ofTokenEmitter`/
  `.ofDigitEmitter` + compat lemmas `IsLogicalInductor.noExploitTok`/`.noExploitDigit`
  (property files route token certs through `noExploitTok`; imported via
  Properties/Basic → Framework.RpnEmission).  Enumeration: single RPN decode, no
  parity dispatch; one coverage lemma, one `trading_firm_dominance`, one
  `LIA_is_logical_inductor`/`exists_logical_inductor`;
  `enumeratedTraderTrades_prim` = `strategyOfTokensTrades_prim ∘ unRpn_prim ∘
  undigitize_prim ∘ clockedTokens_prim`.  AxiomAudit re-froze `#assert_fields
  IsLogicalInductor`.
* **F**: ₂/₃-suffixed public names absorbed; `Tok₃` docstring archaeology removed.
  Remaining subscripted names are internal by design (`EfficientlyComputableTok`/
  `Tok₂` as constructor inputs, `..._preserves_ec₂` digit compilers) or Mathlib
  arity suffixes.

## INTERIM SEAMS (disclosed, both closed by RPN-5)

1. **Conditioning (`thm:scon`)**: the abstract closures (`lic_conditioned`,
   `lic_conditioned_gated`, `lic_conditioned_eventual` in Properties/Conditioning.lean)
   kept FULL class strength — their witness structures now carry symbol-metered
   `translation_ec` fields (hypothesis-carrying; witness-free transport lemmas
   `Trader.conditionedTranslation_exploits_base` /
   `Trader.eventualConditionedTranslation_exploits_base` added).  The CONCRETE
   endpoints moved to DigitConditioning under plain names
   (`ConditioningCompile.lic_conditioned_*`) with interim conclusions = digit-class
   no-exploitation transfer of the conditioned market (subsumes the old token family
   via `toTok₂`).  UnconditionalOverLIA fixed/growing forms match.
2. **Finite perturbations (`thm:ifp`/`app:ifp`)**: `EfficientPrefixPatch.preserves_ec`
   upgraded to the collapsed class; `lic_iff_of_finitePerturbation` unchanged and fully
   proved (patch structures were always explicit hypotheses).  The LIA inhabitant is
   interim-reduced to `liaFreezeBefore_preserves_ecTok` (token-level content); the
   RPN freeze transducer restores `liaEfficientPrefixPatch`.

## NEXT: RPN-5 — symbol-level translation compilers

### RPN-5 part 2 PROGRESS (2026-07-26, worktree agent, second tranche — parse
### localization LANDED)

On top of the merged transducer core (ca0d452), the exactness item's hard theory is
now green and axiom-clean in RpnConditioning.lean:

* `parseRpn_strip` — a successful parse factors as a complete block ++ remainder.
* Run-step normal forms: `rpnCondStep_price` / `rpnCondStep_priceEsc` (offset-counter
  step equations), `rcCnt_run_step_ge`, `rcLen_run_step`, `run_step_decrement`.
* **`parse_of_priceRunWalk`** (the converse walk lemma): a run the automaton walks
  from counter c+1 to its FIRST return at counter c — strictly inside on every proper
  prefix — either parses completely as one block, or POISONS EVERY EXTENSION
  (`parseRpn fuel (u ++ tail) = none` for all fuel/tail).  Proof by strong induction
  + first-passage decomposition (Nat.find on the counter's first return).  The only
  failure mode of an arity-complete run is an undecodable escape payload.

WHY THIS UNBLOCKS THE MASTER COMMUTATION: to prove
`unRpn ((rpnConditionRun blocks ε (rcPack 0 0 0, []) ts).2) =
 (conditionPriceTokenRun ψCode ε (0,0) (unRpn ts)).2`
for ALL ts, induct on ts by grammar chunks (run_append decomposition; transducer
returns to base at chunk boundaries).  Price/trade chunk with run u:
- if the walk never completes: pure copy on both sides (truncation ⇒ parse fails ⇒
  unRpn stops with [tag, 0] on both);
- if it completes: `parse_of_priceRunWalk` splits: (a) u parses ⇒ `parseRpn_strip` +
  `unRpn_price_rewrite_chunk` / `unRpn_trade_chunk_block` give the exact contraction
  on both sides; (b) u poisons every extension ⇒ both sides' unRpn stop with
  [tag, 0] AT THE SAME CHUNK (the transducer's insertion sits beyond the poisoned
  run, so the ∀-tail form kills the rewritten stream too).
Uniqueness of the completion point (needed to align (a)'s block with the automaton's
emission position): successful parse ⇒ its consumed prefix is a first-return walk
(add the no-early-exit conjunct to `foldl_rpnCondStep_run` — mechanical extension),
and two first-return prefixes of the same list coincide (determinism).

2026-07-27 UPDATE (third tranche, worktree agent): the no-early-exit conjunct is
LANDED — `foldl_rpnCondStep_run` (+ price/trade instances, block corollaries) now
also give: every proper prefix of the consumed block stays in the run modes.  This
supplies (i) transducer copy-behavior on blocks (no spurious mode-2 emission), and
(ii) the converse walk lemma's hypotheses at first-exit positions.  NEXT concrete
steps for the master commutation (design fully worked out, see the mapped chunk
induction below): (a) a general copy lemma
`rpnConditionRun blocks ε (st, buf) ts = ((foldl rpnCondStep st ts, bufFold …), ts)`
whenever no prefix of ts hits mode 2 from st (define bufFold; trivial induction);
(b) buffer values over run blocks (price: buf ++ b via rcLen_run_step ≠ 0; trade:
[] at exit); (c) the chunk induction itself: payload/single chunks transparent;
price chunk 0 :: rest splits on parse rest (some: strip + copy + day emission +
`unRpn_price_rewrite_chunk`; none: either no completion (pure copy, both sides
[0,0]-poison) or first completion at k₀ (converse lemma ⇒ u parses ⇒ contradiction
with none, or u poisons ⇒ both sides [0,0]-poison — the mode-2 first-exit state is
`rcPack 2 0 k₀` via an exit-shape lemma `rcMode (step st t) = 2 → step st t =
rcPack 2 0 (rcLen st + 1)` + cnt ≥ 1 invariant in run modes); trade chunk mirrors
with `unRpn_trade_chunk_block`, EXCEPT trade-(b2) needs the converse lemma in TRADE
modes — either generalize `parse_of_priceRunWalk` over (a,b,exit) with step-shape
hypotheses (mirror `foldl_rpnCondStep_run`'s design), or prove a mode-swap walk
correspondence (1↔4, 6↔7, exits pack 2 0 (r+1) ↔ pack 0 0 0) by induction using
trade-mode step normal forms (mirrors of `rpnCondStep_price`/`_priceEsc`).

2026-07-27 UPDATE (fourth tranche, worktree agent): items 1 and 2 of the previous
list are LANDED, green + axiom-clean (commits `85fb581`, `64b5b5f`, `f844a5a`):

* `parse_of_runWalk` — the converse walk lemma generalized over the run-mode pair
  `(a, b, exit)` exactly as `foldl_rpnCondStep_run` (step-shape hypotheses + exit
  counter/mode disambiguators `hexitCnt`/`hexitMode`); `parse_of_priceRunWalk` /
  `parse_of_tradeRunWalk` are instances.  Trade step normal forms
  `rpnCondStep_trade`/`_tradeEsc`; generic step facts `runWalk_step_cases`,
  `rcCnt_runWalk_step_ge`, `runWalk_step_decrement`.
* **Master commutation** `unRpn_rpnConditionRun`: on EVERY stream,
  `unRpn ((rpnConditionRun blocks ε (rcPack 0 0 0, []) ts).2) =
  (conditionPriceTokenRun (encode ∘ ψ) ε (0,0) (unRpn ts)).2`, given
  `hblocks : ∀ D, parseRpn (blocks D).length (blocks D) = some (ψ D, [])`.
  Support layer: `rpnConditionRun_cons`/`_from_day`/`_from_payload`, base/reset
  step equations (`rpnCondStep_base*`, `rpnCondStep_fallback`), the buffer fold
  `rpnCondBufFold` (append/run/reset laws), copy lemma
  `rpnConditionRun_copy_of_ne_two`, trajectory invariants `runWalk_inside` /
  `runWalk_first_exit` (+ price/trade instances), and token-model per-chunk run
  equations (`conditionPriceTokenRun_single/_payload/_price/_price_pair/_trade`).
* **Guarded strategy-level equality**
  `strategyOfTokens_rpnGuardedConditionTokens_trades`: contraction of the guarded
  symbol rewrite = retained-condition-price map of the contraction's trades, all
  streams.  Guard honesty `strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay` via
  `rpn_mode2_localize` (symbol mode-2 either survives as a token mode-2 with the
  same day — `mode2_witness_shift` — or the contraction is `Unreadable`; poison
  tails reject from every base-mode state, transported by
  `Unreadable.cons_chunk` through the `Matches` machinery).

Fifth tranche (same session, commit `5ccc739`): the frame-pass **contraction
anchor** is LANDED — `ContractsTo` (prefix-contraction algebra generalizing
`UnRpnTransparent`: append/single/payload + expanded-block `priceSym`/`tradeSym`
chunk contractions + the full raw-combinator algebra `constTok`..`gateTok`),
`rpnFrameEmit` (the symbol-level frame-leg emission), and
`rpnFrameEmit_contractsTo` (its contraction = token-model
`rawLocallyGated{Beta,Second}BodyTokens` leg + re-emitted trade pair — the mirror
of `unRpn_price_rewrite_chunk`).  The remaining frame work is the run + its
commutation + certificate, per the map below.

Sixth tranche (2026-07-27, worktree agent): the frame pass's **transducer + master
commutation** are LANDED, green + axiom-clean:

* `rpnFrameEmitAt` / `rpnFrameRun` / `rpnFrameOutput` — the streaming frame rewrite,
  REUSING `rpnCondStep`/`rpnCondBuf` (no new automaton, so `rpnCondControlAt`,
  `rpnCondWindow`, `rpnCondScan` all apply verbatim to it).  Base-mode `6` is
  withheld, trade-run tokens are buffered silently, the token that returns the
  automaton to base fires `rpnFrameEmit` on `buf ++ [t]`, everything else is copied;
  an unfinished trade run is flushed with a bare `6` at end of stream (mirror of
  `conditioningFrameTokenOutput`'s flush).
* Support: `rpnFrameRun_append/_cons/_state`, `rpnFrameRun_copy_of_modes` (copy off
  base/trade modes), `rpnFrameRun_silent` + `rcLen_trade_run_step` (buffering inside
  a live trade run), `rpnFrameRun_trade_block`, `rpnFrameOutput_append_base` (chunk
  peel), `priceWalk_inside`, and the token-model per-chunk equations
  `conditioningFrameTokenOutput_{nil,single,payload,one,price,price_pair,trade,
  trade_flush}`.
* **`frameAgree_unRpn_rpnFrameOutput`** — the master statement, on EVERY stream.
  DESIGN NOTE (important, and NOT the price pass's shape): exact equality is
  **false** at a malformed trade run.  The token model sees the contracted `[6, 0]`
  and expands a full leg body around the poison code `0`; the symbol side has no
  block to splice and can only flush.  Both outputs are nevertheless *unreadable* —
  the token side because its ratio's numerator price carries
  `conjunctionCode 0 ⌜ψ⌝` (undecodable, via `conjunctionCode_decode_none`), the
  symbol side because the flushed/emitted run fails to parse — so the invariant is
  `FrameAgree a b := a = b ∨ (Unreadable a ∧ Unreadable b)`, which is preserved by
  `FrameAgree.cons_chunk` and collapses to strategy equality
  (`FrameAgree.strategyOfTokens_trades_eq`).  Price-poison chunks still give exact
  equality (both sides copy).  Supporting: `Unreadable.append_right`,
  `unreadable_price_code`/`unreadable_cons_price`,
  `rawConditioningRatioTokens_eq_price_head`, `rpnFrameEmit_eq_price_head`,
  `parseRpn_cons_and_poison`, `unRpn_cons_and_poison`,
  `unRpn_rpnFrameEmit_poison`, `unreadable_conditioningFrameTokenOutput_poison`.
* **`strategyOfTokens_unRpn_rpnFrameOutput_trades`** — the consumable corollary: the
  contraction of the symbol frame output decodes to the same validated strategy as
  the token-model frame output of the contraction, on every stream.

* Per-position view for the certificate: `rpnFrameSegment` +
  **`rpnFrameRun_range`** (final state = `rpnCondControlAt`, buffer =
  `rpnCondWindow`, output = flatMap of the segments — the exact mirror of
  `rpnConditionRun_range`, and it reuses `rpnCondBuf_window` verbatim) and
  `rpnFrameSegment_eq` (the three-way dispatch form the poly-fueled assembly
  consumes: base-mode `6` ⇒ `[]`, trade modes ⇒ emission iff the successor control
  mode is `0`, otherwise copy).

Gotcha added: `0 :: blk ++ [d]` parses as `(0 :: blk) ++ [d]` (`::` binds tighter
than `++`) — chunk-peel lemmas must parenthesise `0 :: (blk ++ [d])` or the
`List.foldl_cons` rewrites silently miss.

Eighth tranche (2026-07-27, worktree agent): the **join gate** is LANDED, green +
axiom-clean.  `rpnDepthNext` / `rpnDepthRuns` / `tokDepthRuns` (+ append laws,
`rpnDepthRuns_price_block` = depth-neutral, `rpnDepthRuns_trade_block` = one pop),
the master agreement **`depthMode_unRpn_agree`** (on EVERY stream, symbol depth AND
final mode agree with the contraction's, or the contraction is `Unreadable` — the
same skeleton as `tradeRuns_unRpn_agree`, ~200 lines, no walk analysis), the
position bridges `rpnDepthAt_eq_runs` / `parserDepthScanAt_eq_runs`, the symbol test
**`rpnStructurallyAccepts`** mirroring `parserStructurallyAccepts`, its poly scan
**`rpnDepthScan`**, and the gate-agreement consumable
**`rpnStructurallyAccepts_agree`**.

KEY DESIGN FACT worth recording: the symbol mode numbering was already chosen to
mirror the token freeze automaton (0 base, 2 price-day, 3/5 base payloads), so the
depth step is *literally* `parserDepthNext 0 t d` at base positions, `d+1` at the
2/3/5 slots, `d.pred` at a trade-run exit, and identity inside a sentence run.

Also landed in the eighth tranche: **`unRpn_split`** (+ `ContractsTo.self`,
`UnRpnStops`, `UnRpnStops.cons_chunk`) — on any stream the run automaton walks back to
base mode, `ContractsTo A (unRpn A) ∨ (UnRpnStops A ∧ Unreadable (unRpn A))`.  This is
the generic form of the append wrinkle: it is exactly what licenses
`unRpn (first ++ second) = unRpn first ++ unRpn second` (transparent branch) or
`= unRpn first` (poison branch, and then both sides are unreadable).  ~230 lines,
first-exit localization (`priceWalk_first_exit`/`tradeWalk_first_exit` +
`parse_of_*RunWalk`) supplies the poisons-every-extension branch; the "run never
exits" branches are now *contradictions* against the base-mode hypothesis, which is
why the `hex` quantifier is `k ≤ rest.length` (not `<`, as in the `frameAgree` proof).

STILL OPEN for the join (the actual blocker, do NOT underestimate — two candidate
routes, both real work):

* ROUTE A (feed `unRpn_split`): prove
  `List.foldl rpnCondStep (rcPack 0 0 0) (rpnFrameOutput second blkψ ε day bc ibc ts) = rcPack 0 0 0`
  from the same hypothesis on `ts`.  Copies replay the source's transitions; each
  `rpnFrameEmit` block must be shown automaton-neutral.  It IS neutral even on
  unparseable buffers — its shell `0 :: (3 :: buf ++ blk) ++ day :: …` runs the
  buffered trade tokens one counter level up (the `3` bumps the pending counter, `buf`
  drives 2→1, the complete block `blk` drives 1→0, exit at the boundary, then the day
  token returns to base) — but proving that needs a *counter-shift* form of
  `foldl_rpnCondStep_run` (currently only the `c+1 → exit` instance exists).  Then the
  mixed FrameAgree branches also need `freezeMode4 (conditioningFrameTokenOutput …) = 0`.
* ROUTE B (strengthen in place): restate `frameAgree_unRpn_rpnFrameOutput` (~530
  lines) as
  `ContractsTo out tok ∨ (UnRpnStops out ∧ Unreadable (unRpn out) ∧ Unreadable tok)`
  and re-run its chunk induction with `ContractsTo` in place of the raw `unRpn`
  equality.  The ingredients exist (`ContractsTo.*` algebra, `rpnFrameEmit_contractsTo`,
  and `unRpn_rpnFrameEmit_poison` is already in poisons-every-extension form), and the
  proof's poison branches are already written continuation-generically (`hunL : ∀ Y`).
  Mechanical but large; ROUTE B subsumes the mixed-branch bookkeeping ROUTE A needs.

The join's **definition and certificate** are already landed:
`rpnSafeSeparatedFrameOutput` (gated exactly like `safeSeparatedFrameTokenOutput`) and
`rpnSafeSeparatedFrameOutput_polySegStream` (three lines off `rpnAcceptScan`, day slot
= `n` as in `safeSeparatedFrameDigitOutput_polySegStream`).  So what is missing is
ONLY the join *agreement* (route A or B above); with it, items 2–4 below follow.

Seventh tranche (2026-07-27, worktree agent): the frame pass's **`PolySegStream`
certificate** and **budget exactness** are LANDED, green + axiom-clean (commits
`ca54d22`, `87722ab`).  Item 1 of the REMAINING list below is now closed except for
the two-leg join.

* `rpnTradeCountAt` / `rpnTradeCountScan` — the symbol-level trade-run exit count
  (control mode `4`/`7` with successor mode `0`), poly-fueled over any digit
  `PolySegStream` by the same `PolyFueled.prec` pattern as `rpnCondScan`.
* `rpnFrameCore` / `rpnFrameTailMid` / `rpnFrameEmit_split` /
  `digitize_rpnFrameEmit` / `digitize_rpnCondWindow_snoc` /
  `rpnFrameTailMid_polyTokenStream`, and the certificate
  **`rpnFrameOutput_polySegStream`** (any digit `PolySegStream` source, any poly
  block stream, poly day/budget emitters).  Window copy = `concatVar` over
  `rcLen + 1` exactly as predicted; the flush is a two-step mode test.
* CONSOLIDATION done in passing: the raw-combinator `PolyTokenStream` algebra
  (`PolyTokenStream.rawMul/rawAdd/rawMax/rawSafeRecip/rawMin/rawClip01/rawAbs/
  rawConst/rawConstQ/rawLowerSafeRecip/varTok/rawGate`) was lifted out of
  `frameMid_polyTokenStream`'s local `have`s into public lemmas in
  DigitConditioning; both frame emitters now share it (no duplicate algebra).
* **Budget exactness** — the load-bearing one.  `rpnTradeRuns` / `tokTradeRuns`
  (list-level counters + append laws), `rpnTradeRuns_price_block` (0 exits),
  `rpnTradeRuns_trade_block` (exactly 1), and **`tradeRuns_unRpn_agree`**: on
  EVERY stream, either the symbol count equals the contraction's completed-trade
  count or the contraction is `Unreadable`.  KEY SIMPLIFICATION (worth recording):
  this chunk induction needs **no** walk/first-exit analysis — the count depends
  only on the mode trajectory, so every `parseRpn … = none` branch is discharged
  immediately by `unreadable_price_poison` / `unreadable_trade_poison`, and
  `Unreadable.cons_chunk` carries the disjunct across completed chunks.  ~200
  lines, not the ~500 of the master commutations.  Position bridges
  `rpnTradeCountAt_eq_runs` / `tradeScanAt_eq_runs` give the consumable
  **`rpnTradeCountAt_eq_frameTradeCount`** (symbol scan = `frameTradeCount` of the
  contraction, or unreadable — and in the unreadable case both validated
  strategies are empty, so the budget never reaches a trade).

REMAINING (in feasibility order):
1. Frame-pass mirror — CORRECTNESS, CERTIFICATE and BUDGET EXACTNESS DONE (sixth +
   seventh tranches above); what is left is only the **two-leg join**.  Original
   architecture note, kept for the join:
   REUSE `rpnCondStep` (no new automaton).  Emission (`rpnFrameEmit` + anchor +
   run + commutation: LANDED) is exit-triggered
   — at position (st, t) with
   `rcMode st ∈ {4,7}` and `rcMode (rpnCondStep st t) = 0` (detected by
   `runWalk_first_exit` trade instance) emit the RPN expansion of
   `rawLocallyGated{Beta,Second}BodyTokens` with each price leaf `[0, code, day]`
   expanded to `0 :: block ++ [day]` where the conjunction block is
   `3 :: (buf ++ [t]) ++ blockψ(n)` and the ψ-leaf block is `blockψ(n)`; base-mode
   token 6 emits `[]` (tag dropped; body closes with `8` and re-emits
   `6 :: block'`).  Per-chunk contraction anchor mirrors
   `unRpn_price_rewrite_chunk` (needs `parseRpn_and_block` + the existing
   payload/single chunk lemmas over the body shape).  Its master commutation is
   the SAME chunk-induction skeleton as `unRpn_rpnConditionRun` (trade converse
   lemma + first-exit localization already landed).  Budget codes: the digit
   model's `frameTradeCount tfP lenP` reads the CONTRACTED priced stream — at
   symbol level count trade-run exits by a scan over `rpnCondScan`'s mode stream
   (exit flag = mode ∈ {4,7} ∧ next mode 0), or reuse
   `PolySegStream.tradeCountScan` on the digitized contracted stream if a
   contraction emission is interposed (decide when implementing).  Certificate
   assembly shape = `rpnGuardedConditionRun_polySegStream` (window copy via
   `concatVar` over `rcLen + 1` — the emission splices `buf ++ [t]`, i.e. positions
   `j - rcLen .. j` — constant frames, blocks and budget codes constant per day).
   THE ONLY OPEN PIECE OF ITEM 1: the two legs join under the structural-acceptance
   gate (`safeSeparatedFrameTokenOutput`'s shape:
   `if parserStructurallyAccepts … = 0 then first else first ++ second`).  Needs a
   symbol-side acceptance scan (the token one is `PolySegStream.acceptsScan` over
   `parserDepthScanAt`) plus a join agreement.  NOTE a wrinkle the token model does
   not have: `unRpn (A ++ B) ≠ unRpn A ++ unRpn B` when `A` is poisoned, so the join
   needs the token model's none-absorbing argument replayed through `FrameAgree`.
   (Certificate side of the join is cheap: `rpnFrameOutput_polySegStream` twice,
   `.append`, and `.ifZero` on the acceptance scan — exactly
   `safeSeparatedFrameDigitOutput_polySegStream`'s three lines.)
2. Zero-aware variants (mirror `guardedZeroAwareConditionTokens`; the master
   commutation's day-emission case splits on `D ∈ zeroDays` with the short
   `[D, 1, encode 1, 8]` expansion — everything else identical).
3. Endpoints `conditionedTranslation_preserves_ecRpn` /
   `eventualConditionedTranslation_preserves_ecRpn` (statements recorded as
   comments at file end).  Proof skeleton now fully determined: mirror
   `conditionedTranslation_preserves_ec₂` with source = the RPN clocked stream of
   the `EfficientlyComputable` witness, priced = digitized
   `rpnGuardedConditionTokens` (certificate landed), framed = the symbol frame
   pass (item 1); strategy equality via
   `strategyOfTokens_rpnGuardedConditionTokens_trades` + the frame mirror; guard
   path via `strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay`.  `blocks` for a
   condition family comes from `RpnSentenceCodes ψ` (`Framework/RpnSplice.lean`)
   — its block stream satisfies `hblocks` by construction.  Budget exactness in the
   final assembly is `rpnTradeCountAt_eq_frameTradeCount`: split on
   `(T.strat n).trades = []` exactly as `conditionedTranslation_preserves_ec₂` does;
   the nonempty branch gives a readable contraction, so the `Unreadable` disjunct is
   discharged and the budget matches `frameBudget n (T.strat n).trades.length`.
4. Witness constructors (translation_ec fields in Properties/Conditioning.lean
   structures) ⇒ restore class-instance lic_conditioned_* endpoints, delete
   interim digit-transfer forms ⇒ UnconditionalOverLIA class-instance forms ⇒
   AxiomAudit; mark the thm:scon interim seam CLOSED here.

### RPN-5 part 1 PROGRESS (2026-07-26, worktree agent — price pass LANDED, MERGED)

New `Construction/Witnesses/RpnConditioning.lean` (registered in Witnesses.lean),
all green + axiom-clean except the two sorried endpoints:

* **Run-aware automaton** `rpnCondStep` on packed state `⟨mode, counter, runLen⟩`
  (modes: 0 base / 1,6 price run+escape / 2 price-day / 4,7 trade run+escape /
  3,5 base payloads); clamp (`min t 9` — matches `clampVal`'s `B+1`!), bounds,
  runLen reset-or-increment dichotomy.
* **Run–parse correspondence** `foldl_rpnCondStep_run` (+ price/trade instances and
  complete-block corollaries): a parseRpn-consumed block is walked exactly, exiting
  at the boundary with runLen = block length.  Generic over the mode pair via two
  step-shape hypotheses — instantiate, don't duplicate.
* **The price rewrite** `rpnConditionRun` (streaming; buffer = current run,
  recovered by position via `rpnCondWindow`), `rpnConditionRun_range` (per-position
  segment form), `rpnGuardedConditionTokens` (day guard).  DESIGN: letE-preserving —
  the original chunk is copied, then at the day position the emitted expression
  re-splices the buffered run into the conjunction shell `3 :: run ++ blk` and the
  ψ-block twice, closing with `8`; so the contraction per chunk is EXACTLY the
  token-model segment: `unRpn_price_rewrite_chunk` proves
  `unRpn (0 :: b ++ rpnConditionEmit blk ε b D ++ rest) = [0,⌜φ⌝,D] ++
  rawConditionalPriceTokens ⌜φ⌝ ⌜ψ⌝ D ε ++ 8 :: unRpn rest` (uses new
  `parseRpn_and_block`).
* **Scans**: `rpnCondScan` (packed control poly-fueled over any digit PolySegStream;
  via scalar component functions `rcModeF/rcCntF/rcLenF` + reusable
  `polyFueled_ifEq`/`polyFueled_ifLeOne` dispatch combinators — this pattern makes
  prec-scan side goals rfl-close, no split_ifs in the scan itself), day-guard flag
  `rpnBigDayFlagAt` + `rpnBigDayFlagScan`.
* **Emission certificate** `rpnGuardedConditionRun_polySegStream`: digitized guarded
  rewrite of any digit PolySegStream is a PolySegStream over any poly block stream
  (window copy = `concatVar` over the recorded run length with `BigDigits` position
  access; blocks at the clamped day; flagged days emit []).

OPEN (recorded as statement comments in RpnConditioning.lean — mainline sorry-free;
worktree agent resumed on them 2026-07-26): the endpoints
`conditionedTranslation_preserves_ecRpn` / `eventualConditionedTranslation_preserves_ecRpn`.
Remaining distance, itemized in the file's "Endpoints (open)" section:
(1) whole-stream contraction exactness for the price pass (well-formed chunks via
`unRpn_price_rewrite_chunk` + run–parse correspondence; malformed via rejection
preservation); (2) guard-honesty transfer to the contracted stream (then digit-model
`strategyOfTokens_trades_eq_nil_of_bigDay` applies); (3) the FRAME pass mirror
(two legs, trade slot as `3 :: run ++ blockψ(n)`, same assembly shape as the landed
certificate); (4) zero-aware variants for the eventual translation.  After those:
witness constructors return to ConditioningCompiler, `lic_conditioned_*` regain
class-instance conclusions, AxiomAudit update (endpoints not added there while
sorried).

Gotchas hit (add to the log): the `Nat.sqrt` irreducible scoping is NECESSARY BUT
NOT SUFFICIENT for deep recursive definitions — the whnf blowup only clears once the
DOMAIN LEAVES (the recursive defs themselves) are also made locally irreducible per
declaration (Tranche U: rawStep/rawVal/childPair/colOf/rootVal/tabCol/trim/
universalApprox all needed it); `clampVal (const B)` clamps at `B+1`, so automaton
clamp lemmas must use `min t (B+1)`; omega chokes on `True ∧ _` conjuncts (add
`true_and, and_true` to the pack-equality simp set) and on goals whose only closing
hyp is `False` (`first | omega | (exfalso; assumption)`); `rcMode`-style projection
defs print as raw `unpair` in goals — insert `show`/`rfl` rewrites before `if_pos/
if_neg` on them.

Two constructions, both stream rewrites over the RPN grammar (sentence-slot spans now
recognized by the pending-counter scan; conjunction of sentence blocks is
CONCATENATION — `rpn (φ ⋏ ψ) = 3 :: rpn φ ++ rpn ψ` — no bignum pair shells):
1. **Conditioning**: mirror DigitConditioning's guarded compiler with sentence slots
   spliced at the symbol level ⇒ `conditionedTranslation`/`eventualConditionedTranslation`
   preserve `EfficientlyComputable` ⇒ witness constructors return, concrete
   `lic_conditioned_*` endpoints regain class-instance conclusions, interim digit
   forms deleted.
2. **Freeze**: RPN-aware `freezeBefore` transducer (parser control skips/copies
   sentence runs; quote table replacement at slot boundaries) ⇒ symbol-level
   `preserves_ec` ⇒ `liaEfficientPrefixPatch` restored.

## EC-SEQ — 𝓔𝓒-sequence migration: **COMPLETE (2026-07-26)**

Every property-family sentence-sequence hypothesis now quantifies over
`RpnSentenceCodes` (the paper's 𝓔𝓒 class): the PolySequence-routed families
(thm:tl/perkno, thm:prand/benford chains, wubaff, pseudorandomness, affine
provind/coherence/persistence/preemptive, calibration, LUV meshes), the direct
families thm:provind (seq fragment), thm:lex (`RpnSentenceCodes.modDispatch` —
finite mod-k block dispatch), and thm:obu (obu chain re-certified through
`RpnSpliceStream`, variable-length arm blocks via `concatVar`; token chain
deleted).  Deliberate whole-value residuals, each with a reason:
* `QuoteCodeOfMarket`/arithmetic quotation hypotheses — Gödel-coding is
  value-dependent; wraps via `.ofPolySentenceCodes` where spliced consumers need it.
* `PrefixMachinePresentation.sentence_codes` (OccamBounds) — the concrete prefix
  enumeration's whole-value certificate is PROVED (M7-PREFIX-MACHINE); nothing gained
  by weakening the field.
* `ConditioningPresentation.condition_codes` — conditions are r.e.-stage sentences;
  the RPN-5 transducer takes `RpnSentenceCodes ψ` and wraps at call time.
* `LUV.PolyThresholdCodes` — threshold sentences stay whole-value (deep-threshold
  LUVs would need a block-form threshold interface; not demanded by any paper node).

Gotchas: Mathlib names are `Option.bind_some`/`bind_none`; `rcases h : e`
substitutes `e` in the GOAL too; suffixed lemmas inside a namespace break
dot-notation; `Formula.ofNat` is WF-compiled (use its equations); fuel-congr binders
must be EXPLICIT or `by omega` side goals see metavariables; fully bind branch
`have`s before `of_eq`; constructor-form `cases` for casesOn iota;
`(Primrec.encdec.comp _).of_eq fun _ => rfl` bridges Primcodable-instance mismatches.

# Completed work record (compressed 2026-07-26)

The 2026-07-24 boundary-shoring plan is **complete**: Tranche 0 (audit surface),
Tranche 1 (`thm:epr`/`thm:er` witness-free), Tranche 2 in full (digit layer B0-B3:
`EfficientlyComputableTok₂`, `LIA_is_logical_inductor₂`, the guarded digit
conditioning compilers, `IsLogicalInductor₂`-closure of `thm:scon`), Tranche 3
(quotation family §4.11-4.12 witness-free over LIA: epr/er/ceu/cee/ccee/st/ref/lp).
Tranche 4 was rescoped into ACTIVE PLAN 2 above.  The F0-F9 errata fixes, the F7
LUV-arithmetic program, the quotation vacuity rescue, and the 2026-07-22 session
records live in git history and `m7-errata-audit.md` — this file no longer carries
them.  F7 full-scope (first-order LUV reconstruction) remains a scoped, deliberately
unopened spike; see the audit's §2.2 disposition.

## External state

* **Kraft / `M7-PREFIX-MACHINE` — LANDED (2026-07-26, merged).** The subagent run
  completed and its branch is merged (commits `511363b`/`d88faf9`/`1988a4c`/`f15d750`).
  Aristotle job `65eaafaa…` genuinely discharged the Kraft sorry (unlike `bc2df18a…`);
  `kraft_inequality` is re-elaborated and kernel-checked in-repo
  (`Construction/Witnesses/KraftInequality.lean`), axioms strictly clean.  On top of it
  `Construction/Witnesses/PrefixMachine.lean` constructs the concrete self-delimiting
  sentence code and discharges every *mathematical* field of the Occam boundary — see
  the M7-PREFIX-MACHINE record below for the remaining work.
* GL fixed point: discharged and vendored (`ProvabilityLogic/`), 2026-07-21.

## M7-PREFIX-MACHINE — COMPLETE (2026-07-26, second session)

Full detail in `notes/m7-prefix-machine-scope.md` (rewritten this session; read it
before reopening).  Compressed state:

**Done, kernel-clean, audited:** `kraft_inequality` (Aristotle-produced body, in-repo
validated); `natCode`/`sentCode` prefix-free-injective; `prefixKappa = |sentCode|+1`
with negation depth factored out (that factoring is what makes the overhead
*additive*); enumeration `prefixSentenceEnum` (canonical decode + `atom n` fallback,
surjective, multiplicity ≤ 2); the presentation's `kraft` field proved
(`prefixKraft`: half-budget per injective index class); `covers`; exact
approximation + `nonneg`/`le`/`tendsto`; **`prefixNegationCompiler` fully proved
(overhead = 2)**; both `OccamThresholdEmission` streams **derived** from the weight
emission (`prefixThresholdSum_polyRat`/`prefixInverseWidth_polyRat`).  Endpoints:
`lic_occam_lower_ofPrefixMachine` / `lic_occamBounds_ofPrefixMachine`.

**Both former residual certificates are now PROVED** (second 2026-07-26 session,
worktree agent):
1. `prefixSentenceEnum_polySentenceCodes : PolySentenceCodes prefixSentenceEnum` —
   canonicity of `n` (membership in `Formula.toNat`'s range) decided poly-fueled by a
   breadth-first *packed* descent: slots shrink as `√` per level, levels packed as
   `Nat.ofDigits` in the level-varying base `sbChain n d + 2` with width `2^d`,
   resolution at depth `size (size n) + 3`; conjunction conserved level-to-level
   (`validCode m = validCode (chL m) && validCode (chR m)` with `0`/`1` absorbing
   resolved slots).  No bespoke stack machine was needed — BFS level-packing sidesteps
   the stack entirely.
2. `prefixApprox_polyRatCodes : PolyRatCodes prefixApprox` — derived from (1) by
   code-level negation stripping (`dcIter`) + halving-driven doubling (`p2s`; the
   doubling is clocked by the halving, so no clamp is needed there) + `prefixDen_eq`.

`PrefixMachineComputation` is **deleted** (consolidation): `prefixMachinePresentation`
and the endpoints `lic_occam_lower_ofPrefixMachine` / `lic_occamBounds_ofPrefixMachine`
are unconditional (modulo `[IsLogicalInductor P DP]` + market hypotheses, as
everywhere).  All new endpoints axiom-clean and in `AxiomAudit.lean`.  Full
construction record in `notes/m7-prefix-machine-scope.md` (closing record).

**Disclosures recorded:** type-`(c)` in `PrefixMachine.lean`'s module docstring —
`prefixKappa` is a *fixed computable* self-delimiting code, not universal prefix
complexity; universality (dovetailing, lower-semicomputable weights) remains undone
and is a strictly larger construction.  The multiplicity-2 slack bit and the
non-injective-decode gotcha (`Formula.ofNat (pair 0 c + 1) = some ⊥` for every `c`,
so plain decode-fallback enumerations double-spend — the canonical-index guard in
`prefixSentenceEnum` exists for this) are documented in the scope note.

## Terminal (not a tranche — document, don't build)

After Tranche 2 the dd:fuel residuals are (a) fuel-model vs TM-time equivalence and
(b) the pair-code bit-size vs symbol-size gap for skewed formulas (Tranche 4 item 3). **Blocked in
principle**: Mathlib has no time-bounded computability/complexity theory (no poly-time
TM class; `Turing.PartrecToTM2` is unbounded).  Watch item (checked 2026-07-26): CSlib
(`leanprover/cslib`, active) now owns TM machine models (single/multi-tape, det/nondet)
but still no resource bounds/complexity classes — if it grows a poly-time class, the
missing bridge is an `evaln`-fuel ↔ TM-step polynomial simulation theorem. Per CLAUDE.md rule 6 this is a
stop-and-report boundary: keep the model-card calibrations (`PolyFueled.primrec`,
`not_polyFueled_two_pow`, closure ops) and one disclosure sentence. Likewise the last
quotation type-(c) — code-indexed atoms *mean* their arithmetic instances via
`theoremDP`'s enter/refute clauses — is closed by an intended-semantics bridge lemma
(Σ₁-soundness ⟹ truth-in-ℕ for entering atoms) if one is missing, **not** by replacing
the propositional substrate.


# REOPENABLE TRANCHES (scoped 2026-07-27, Anson-approved taxonomy)

> **Stage-3 gate (Anson, 2026-07-27): DISCHARGED.**  Stage 3 (universal prefix κ) was
> dispatched and landed the same day; see Tranche U below.  The surface is free to freeze
> for the read-through, which should now cover `Construction/Witnesses/UniversalPrefix.lean`
> (`UHalt`, `kappaU`, `kappaU_le_of_prefixMachine`, `uMinLen`/`uCode`, and the
> two new endpoints).

Three bins beyond the in-flight RPN-5/freeze line.  Everything not listed here is
either **closed** (prefix-enumeration whole-value row: proved, zero debt) or
**permanently disclosed in principle** (dd:fuel↔TM-time: no time-bounded machine
theory exists anywhere to bridge to; keep the model-card calibrations + the CSlib
watch item — if CSlib ever grows a poly-time class, the remaining gap is one
`evaln`-fuel ↔ TM-step polynomial simulation theorem, and that alone).

## Tranche U — universality: M7-DUS-APPROX + prefix-code universality

**Stage 1 landed 2026-07-27** (`Construction/Witnesses/UniversalDovetailer.lean`,
commit "Tranche U stage 1: the universal dovetailer with clocked approximants").
`M*` exists as an explicit dovetail over `Nat.Partrec.Code` with a stage clock:

* `Dovetail.rawTable` — running max of the first `n` dovetail readings, reading
  `(index, fuel) = n.unpair` at stage `n`.  One clock, monotone, no unbounded search.
* `Dovetail.trim` — each raw stage trimmed top-down into a semimeasure, every value
  remembering the previous stage.  **The memory is load-bearing**: the ordered trim
  alone is *not* monotone in `n` (the sibling subtraction moves the wrong way), and
  without the memory the stage table can overshoot its own limit, so
  `approximation_le` would fail.  `trim_tendsto_of_exact` shows the memory costs
  nothing in the limit.
* `Dovetail.universalMass` — the `(1/2)^(i+1)`-weighted mixture; a `ContinuousSemimeasure`
  (`Dovetail.continuousSemimeasure`) dominating every lower-semicomputable continuous
  semimeasure with explicit constant (`Dovetail.universalMass_dominates`).  Both
  axiom-clean and on the AxiomAudit surface.
* `Dovetail.universalApprox` — the monotone from-below stage table (first `n` programs,
  each at trimmed stage `n`), with `_nonneg`/`_mono`/`_le`/`_tendsto` all proved.

**Step 1 landed 2026-07-27** (`exists_universalApprox_code` + packaging).  The emission
program is constructed by **column tabulation** (`tabCol`, `childPair`, `trim_prim`,
`universalApprox_prim`, `approxEmit_prim`), so `Dovetail.lowerSemicomputable` and
`Dovetail.universalSemimeasure` are real, axiom-clean defs on the audit surface.  Two
things learned that are worth keeping:
* `Nat.sqrt` being section-`irreducible` was **not** sufficient for the documented whnf
  blowup — it only cleared once the *domain leaves* (`rawStep`, `rawVal`, `childPair`,
  `colOf`, `rootVal`, `tabCol`, `trim`, `universalApprox`) were made locally irreducible
  per declaration.  Worth adding to the gotcha log as the standard second step.
* `list_range_map_sum` existed twice, both `private`, both ℝ-only.  Generalized upstream
  (`ExpectationConvergence.lean`, now public, `AddCommMonoid`), downstream duplicate
  deleted.

**Step 3 landed 2026-07-27 — `M7-DUS-APPROX` is COMPLETE.**  The polynomial clock is
discharged, and *not* by the clamped-recursion route the previous session predicted.  The
prediction was that the poly emitter would have to round inside the `trim` recursion (grid
rounding, with a drift/error-accumulation bound replacing the broken monotonicity).  That
turned out to be unnecessary, because **`Code.evaln` is already self-clamping**:

* every `evaln` clause guards `n ≤ k`, so a code run with fuel `k` can neither read an
  input above `k` nor return a value above `codeEvalBound c k` — and for a **fixed** code
  that bound is *polynomial* in `k` (`codeEvaln_result_le` + `codeEvalBound_poly`);
* the exact emitter `approxEmit` is a fixed code (`Dovetail.approxCode`), so
  `codeEvalnNat_polyFueled` (`M7-HIST-EVALN`) makes *reading it under a polynomial clock*
  poly-fueled, with a poly-bounded output, for free.

So the emitter does not approximate the table — it **selects** from it.  `dusState` scans
`j < n` at clock `⟪z,z⟫` keeping the last reading that finished; `dusStage` names the stage
that reading came from; `dusApprox z = universalApprox (dusStage z z.1) σ` is therefore an
*exact* stage value.  `nonneg`/`le_mass` are then `universalApprox_nonneg`/`_le` verbatim,
and `tendsto` is a two-sided squeeze (`≤ mass` always; `≥ universalApprox m σ` eventually,
since the clock grows past the fuel stage `m` needs and `le_dusStage` never lets the
recorded stage slip back).  No drift bound, no clamped recursion, no `tabCol` rewrite.

Landed, all axiom-clean and on the audit surface:
* `Dovetail.approxCode` / `approxCode_eval` / `stageRead` / `dusState` / `dusStage` /
  `dusApprox`, with `dusApprox_polyRatCodes` (`PolyFueled.prec` over the packed step
  `dusStep`; state bounded by `codeEvalBound approxCode ⟪z,z⟫ + 2`);
* `Dovetail.dusApproximationPresentation` and `Dovetail.dusThresholdEmission` — every
  field constructed.  The threshold streams reuse a new generic
  `Dovetail.encode_natDiv_polyFueled` (runtime `gcdc` reduction of `(a:ℚ)/(b:ℚ)`, zero
  denominator ↦ `⌜0⌝`), which is the DUS analogue of `prefixThresholdSum_polyRat`;
* endpoints `lic_domination_dovetailSemimeasure_unconditional` (no semimeasure input at
  all) and `lic_domination_everyLowerSemicomputable_unconditional` (the paper's actual
  conclusion: the constructed market dominates *every* lower-semicomputable continuous
  semimeasure).  Only `BitPrefixCodeComputation` (`M7-DUS-PREFIX-SYNTAX`) remains a caller
  input on that family.

`Dovetail.gridApprox` and its four lemmas are **kept**: they are the record of the
alternative route (rounding the stage onto the `1/(n+1)` grid), they independently
discharge the same two analytic fields, and `isPolyBounded_encode_gridApprox` is the only
place in the repo where a stage table's *size* bound is proved directly.

Two things worth keeping:
* `UniversalDovetailer.lean` now imports `QuoteCodeOfMarket` for `encode_rat_natCast_div`.
  That lemma (and `ComputableLUV.natCast_div_num`/`_den` under it) are generic `Encodable ℚ`
  facts sitting in `Construction/Witnesses/`; the consolidation-correct home is
  `Framework/Computable.lean` next to `encode_rat_natCast`.  Deferred, noted.
* `cases hev : e` substitutes `e` in the **goal** but *not* in existing hypotheses — the
  mirror image of the recorded `rcases h : e` trap.  `rw [hev] at h` first.

**Tranche U is COMPLETE (2026-07-27).**  Item 3 — the universal prefix machine — landed;
see below.  Nothing in Tranche U remains open.

3. ~~Upgrade `PrefixMachine.lean`'s κ to universal prefix complexity.~~ **DONE
   (2026-07-27, `Construction/Witnesses/UniversalPrefix.lean`).**  The estimate above ("a
   genuine new construction, 1–2 sessions, the Kraft field is the hard part") was wrong
   about *where* the difficulty sat, and the correction is the reusable lesson:

   * The sketch assumed the Kraft field would need "the halting set of a prefix-free
     universal machine enumerated with its codewords".  It does not.  Making the domain
     prefix-free **by construction** — a tagged three-family machine, each family
     prefix-free, the recursive family prefix-free *because the whole domain is* (structural
     recursion on codeword length) — turns Kraft into `kraft_inequality` applied to the
     selected shortest codewords, roughly 20 lines.  `UHalt_prefixFree` /
     `UHalt_functional` are the whole content.
   * The genuinely expensive field is the **approximation**, exactly the opposite of the
     prediction.  `κ_U` is uncomputable, so the from-below stage table has to mine a
     dovetailed enumeration; the poly-fuel emitter then needs the `M7-DUS-APPROX`
     self-clamping trick verbatim (`uRead`/`uStage`/`uState`/`uSel`, `PolyFueled.prec`).
     That copy is real but mechanical — `uTab` shifts the stage index by one purely so the
     `prec` base case is a *constant*.
   * The three families: `0 ∷ natCode n ↦ n` (coverage — this is why no sentence-code
     computability is ever needed), `1 ∷ 0 ∷ v ↦ ¬(U v)` (the hard-wired negation
     instruction: `PrefixNegationCompiler` overhead is an explicit **2**, not the size of a
     compiler index — this is what the sketch's "negation compiler" item wanted and it is
     free once negation is an instruction), and `1 ∷ 1 ∷ natCode e ++ w` over the
     prefix-ified dovetail `acc`.
   * `acc` prefix-ifies by the standard guard (accept `w` for machine `e` only if it halts
     and is incomparable with everything already accepted for `e`).  The one lemma that
     earns the word *universal* is `kappaU_le_of_prefixMachine`: if a code's halting domain
     is already prefix-free the guard never fires, so its whole domain reappears inside
     family 3 and `κ_U ≤ κ_M + 2·|natCode ⌜M⌝| + 3`.

   **Residual: none (discharged 2026-07-27, kind `P` provenance `(a)`).**  What had been
   an input — a `Nat.Partrec.Code` for the **exact** stage table — is now
   `UPrefix.uCode`/`exists_uCode`.  The table is the bounded search `uMinLen n y` (minimum
   length over the finitely many codewords of length `≤ |natCode y| + 1` that the stage-`n`
   decision procedure `uVal` accepts), `uMinLen_eq` proves it equals `sInf (uLenSetBy n y)`,
   and `uEmit_prim` runs the `Primrec` chain: `Nat.size`/`testBit` → `natCode` → `natVal`;
   `evaln` → `candHit` → `accOK` → `acc`; `uUniv`/`uVal`; `wordsLen`/`wordsUpto`; `uMinLen`.
   Two things worth remembering from doing it: (i) `UHaltBy`'s negation family recurses
   *two* positions down, which `Primrec.list_rec` cannot express directly — the scan
   (`uValP`) carries the value of the tail alongside the value of the list; (ii) Mathlib
   has no `Primrec` for `List.take` or `<+:`, so the codeword enumeration `wordsLen` does
   double duty as the prefix decision (`u <+: v` iff some string of length `|v| - |u|`
   extends `u` to `v`).  `Nat.size` and the sentence-enumeration canonicity bit came free
   from `PolyFueled.primrec` over the existing `sizec_polyFueled` / `invalidBit_polyFueled`.
   **A `PolyRatCodes` obligation on the *exact* table would have been unsatisfiable**
   (reading stage `n` costs `n` dovetail stages) — that trap is why it was stated as a
   code, and why the selection layer is inside the file rather than assumed.

   Endpoints: `UPrefix.lic_occam_lower_ofUniversalPrefix` /
   `UPrefix.lic_occamBounds_ofUniversalPrefix`, minted **alongside** the fixed-code ones,
   which stay unconditional.  The type-`(c)` non-universality paragraph is gone from
   `PrefixMachine.lean`'s docstring, replaced by an accurate statement of what each of the
   two instances means.  Consolidation done in the same pass:
   `sum_prefixWeight_le_half_of_code` / `prefixKraft_of_code` (Kraft, generic over the
   code) and `gateEmitBase` / `gate*_polyRat` (gate tokens, generic over any reciprocal
   weight stream) in `PrefixMachine.lean`, with the fixed-code lemmas as one-line
   instantiations; the universal machine's gate tokens reuse
   `Dovetail.encode_natDiv_polyFueled`.

Tranche S does **not** need this: its one open statement is written against
`UniversalContinuousSemimeasure`'s own approximation fields (see Tranche S).

## Tranche S — M7-STRICT-SEPARATORS — redesigned, landed, and CLOSED (2026-07-27)

**What happened.**  The old interface (nested prefix family) was proved *uninhabitable*
(`no_ce_null_prefix_family`, `Construction/Witnesses/StrictSeparators.lean`: a nested
family with a computable string enumeration carries a lower-semicomputable point-style
semimeasure `ceNestedSemimeasure`, so universality keeps its mass above a positive
constant forever).  Anson approved the redesign; it is now in, in collapsed form.

**Interface now (`Properties/UniversalSemimeasure.lean`), all conclusion-free:**

| field | status |
| --- | --- |
| `constraint : ℕ → Sentence` | constructed (`separatorConstraint`, the stage-`n` conjunction of decided Kleene literals) |
| `repetition` | constructed from a `CEEnumeration` via `EfficientRepeatedEnumeration.ofCE` |
| `jointly_possible` | proved, from infinite independent realizability of the atoms |
| `consistentAt : ℕ → List (List Bool)` | constructed (`separatorConsistentAt`, filtered `allBitStrings`) |
| `class_covers` | proved (read the world's bits off the atoms) |
| `mass_class_tendsto_zero` | constructed (`separatorClass_mass_tendsto_zero`, Kučera–Demuth — see below) |

**Market half.**  `strict_domination_of_null_separator_class` replaces
`strict_domination_of_null_prefix_theory`: UND floors the constraint theory at ε; limit
coherence (`GaifmanCoherent.mono` / `.or_le` / `.le_sum_of_covers`, new in
`Properties/LimitCoherence.lean`) spreads the floor over the stage class; pigeonhole
against vanishing class mass finishes.  **`lic_strict_domination_universalSemimeasure`'s
statement is unchanged** — only the type of its separator argument changed, and `hworld`
comes from the interface's own `jointly_possible`, so no hypothesis was added.

**Discharged concretely** in `StrictSeparators.lean`: `kleeneSet`, `kleeneSet_disjoint`,
`kleene_recursively_inseparable` (the diagonalization — proved, axiom-clean),
`kleeneDecide` + soundness, `separatorConstraint` (a `Nat.rec` over decided bits) + exact
semantics, its Gödel-code mirror and computability, `separatorConstraintCE`,
`allBitStrings`, `separatorConsistentAt` + membership, `ordinaryAtom_code_computable`,
and `strictSeparatorPresentationOfKleene`.

**Residual inputs of `strictSeparatorPresentationOfKleene` — two of three discharged
(2026-07-27):**

1. ~~`hatoms` (infinite realizability)~~ — **discharged.**  `IndependentBitAtoms.realizable`
   and `BitPrefixSentences.realizable` now state the *total* form (every total Boolean
   assignment is compatible with every finite stage); the finite-prefix forms survive as
   derived lemmas `*.finite_realizable`, so the DUS uses are untouched, and
   `ordinaryIndependentBitAtoms` proves the total form directly.  `jointly_possible` now
   comes from `B.realizable` applied to the non-computable Kleene assignment.
2. ~~`hce` (constraint-theory enumerator)~~ — **discharged, and built rather than assumed.**
   `separatorConstraint` is a left-nested `Nat.rec` over the decided bits; Foundation's
   propositional encoding is tagged `Nat.pair` arithmetic (`sepAndCode` / `sepNegCode` /
   `sepTopCode`, all `rfl`), so `separatorConstraintCodeAux_computable` gives
   `separatorConstraint_computable`, hence `separatorConstraintCE : CEEnumeration …` and
   `repetition` via `.ofCE`.  Mathlib's `Nat.Partrec.Code.primrec_evaln` + `Primrec.ofNat`
   carry the dovetailing.  The construction now assumes only `hatom : Computable fun k ↦
   encode (B.atom k)`, itself proved for the repo's atoms by
   `ordinaryAtom_code_computable`.
3. ~~`hmass` (vanishing class mass)~~ — **discharged 2026-07-27, and with it `thm:strict`
   is CLOSED.**  `separatorClass_mass_tendsto_zero` (`Construction/Witnesses/
   StrictSeparators.lean`) proves it outright, axiom-clean, against the interface's own
   approximation fields — no Tranche-U dependency.

### How `hmass` was proved (Kučera–Demuth, `app:strict`)

1. **Antitone.**  `classMass M p n` (the mass of the part of the stage class selected by
   `p`) is non-increasing for every truncation-stable `p`: a stage-`(n+1)` consistent
   string truncates into the stage-`n` class (`kleeneDecide_mono`,
   `take_mem_separatorConsistentAt`), and `ContinuousSemimeasure.sum_le_of_take` sums
   `children_le` over the fibres of the truncation map.  `allBitStrings_nodup` is what
   lets the list sums become `Finset` sums.
2. **Limit.**  `tendsto_atTop_ciInf` gives `r := ⨅ n, classMass … n ≥ 0`; assume `r > 0`.
3. **Pivot.**  A stage `k` with class mass `< 6r/5`, and a rational `r/5 < q < r/2`
   (`exists_rat_btwn`).
4. **The separator.**  `sepGuard` dovetails over stages `s = k+j+1+…`, fuel and
   approximation level, and fires on the first bit `b` whose part of the stage class
   approximates above `q`.  The key simplification: instead of extracting a *total*
   computable `M.approximation`, the search reads `M.approximation_code` under a fuel
   bound (`boundedApprox`, `0` when it has not printed yet).  That keeps the whole guard
   **`Primrec`** — `separatorConsistentAt_primrec`, `boundedApprox_primrec`,
   `sepApproxSum_primrec` — and is sound because `0` underestimates the mass.
   Totality of the search is `Nat.rfindOpt` + `Partrec.of_eq_tot` (the
   `LIAComputation` pattern).
5. **Correctness.**  Termination: the two parts sum to `≥ r > 2q`, so one exceeds `q`, and
   `approximation_tendsto` makes a finite approximant see it (`exists_sepGuard`).
   Soundness: a fired guard really witnesses mass `> q` (`sepGuard_spec`).  Wrongness is
   impossible: if `j ∈ kleeneSet b` then the `b`-part keeps mass `≥ r` from `k` on, so the
   other part is `< 6r/5 − r = r/5 < q` (`classMass_wrong_bit_lt`).  The resulting total
   computable function contradicts `kleene_recursively_inseparable`.

**Consequences landed in the same tranche.**  `strictSeparatorPresentationOfKleene` no
longer takes `hmass`; its only input is `hatom` (atom Gödel codes computable, proved for
the repo's atoms).  New corollary `lic_strict_domination_universalSemimeasure_ofAtomCodes`
discharges the separator argument of the endpoint.  README boundary row + status table
(13/15) and `AxiomAudit.lean` updated.

## Tranche P — 𝓔𝓒 polish (cheap optionals, ~½–4 sessions total, no paper-node demand)

1. **OPEN** — `ConditioningPresentation.condition_codes` → `RpnSentenceCodes`
   (½–1 session): field flip + `fixedConditioningPresentation` /
   `conditioningPresentationOfComputations` + call-site plumbing; value = conditioning
   on DEEP condition sequences.  Do after the RPN-5 packaging sweep settles (same
   files).
2. **DONE 2026-07-27** — `LUV.PolyThresholdCodes` block form.  `LUV.RpnThresholdCodes`
   / `LUV.RpnThresholdCodeSeq` (`Framework/Expectations.lean`) are the `def:ec` block
   forms — literally `RpnSentenceCodes` at the paired-index conventions — with
   `ofPolyThresholdCodes` / `ofPolyThresholdCodeSeq` embedding the whole-value
   interfaces by escape blocks, and `RpnThresholdCodes.constSeq` bridging the two.
   Re-plumbed: `ExpectationAffine` (expect/indicator/linearity mesh),
   `ExpectationConvergence` (the `thm:ec` bundle trader moved off `PolySegStream` /
   `EfficientlyComputableTok` onto `RpnSpliceStream` / `EfficientlyComputable` — its
   `excThresholdBlk` block is now variable-width via `serialize_price` + `concatVar`),
   `ExpectationProperties.ConvergencePresentation.threshold_code`,
   `LUVCombinationSyntax.threshold_poly`, `QuotationAffine` (expectAffineSeq /
   crossPrecision / reindex), `SelfTrust`, `Introspection`, `ComputationDP`,
   `LUVExpectationCertified`.  `QuoteCodeOfMarket` deliberately stays whole-value and
   wraps at the boundary (see item 3).  Dead `PolySegStream` ramp closures in
   `AffinePreemptiveLearning` removed; the `PolySegStream.serialize_oneMinus/efMin/
   clip01` trio moved next to its `RpnSpliceStream`/`PolyTokenStream` siblings in
   `Hysteresis.lean`.
3. **SKETCH ONLY — do not implement as scoped** (arithmetic-quotation numerals).
   Design sketch below; verdict: this is a genuinely new layer, ≥2 sessions, and the
   block form buys *nothing* for the object it would flip.

### Item 3 sketch — digit-wise numerals in `QuoteCodeOfMarket` (verdict: don't build)

**What the object actually is.**  The quotation LUV's threshold sentence is
`arithmeticThresholdLUV code n |>.gt r = quoteAtom (pair code (pair n ⌜r⌝))`
(`QuotationAffine.lean:262`) — a *propositional atom* whose index is a Gödel number.
Depth 1.  So the `RpnSentenceCodes` block form gains nothing structurally here: the
block for an atom is one escape pair, and the only cost is the atom's index *value*.

**Where the value-exponential blowup actually sits.**  Two places, both value-typed:
* `quoteAtom_mesh_encode_polyFueled` (`QuoteCodeOfMarket.lean:63`) builds the atom index
  by *arithmetic on the reduced fraction* (`gcdc`/`divmod1`/`ifzSel`) and then wraps it
  in a fixed `pair` shell.  That is already poly in the *values* `n, k, i`; nothing to
  digitize.
* `indicatorProductLUV_polyThresholdCodeSeq` (`:444`) and `theoremFutureQuoteCode` /
  `theoremConfidenceQuoteCode` (`:511`, `:598`) take `hφ : PolySentenceCodes φ` and use
  `Encodable.encode (φ n)` *as a numeral inside the quoted formula* (the `⋏`-shell, and
  the market's own `quote day ⌜φ n⌝`).  **This** is the deep-φ obstruction: a deep `φ n`
  has poly symbol count but its pair code — hence the numeral naming it — is
  exponential in that count, so no poly-fueled program can emit it as a token.

**What accepting deep φ would require (the new layer).**
  (a) A *digit-stream* numeral interface: `PolyDigitCodes (f : ℕ → ℕ)` = the base-`b`
      digits of `f n` are poly-emittable, plus closure under the pair/succ shells that
      `encode_and` and `encode_quoteAtom` use.  Nothing like this exists — the current
      digit layer (`Criterion.lean`'s `clockedTraderDigit`, `digitize`/`undigitize` in
      `RpnEmission.lean`) digitizes *token streams*, not *arithmetic operands*, and has
      no arithmetic closure lemmas at all.
  (b) A bridge `RpnSentenceCodes φ → PolyDigitCodes (fun n => Encodable.encode (φ n))`,
      i.e. "compute the Gödel number's digits from the parse blocks" — a
      carry-propagating streaming encoder for Foundation's `Encodable (Formula ℕ)`.
      This is the genuinely new work and is where the ≥2 sessions go.
  (c) A *second* consumer to satisfy, which the block form does not serve at all:
      `MarketComputation.expectQuoteAt_computable` (`:262`) destructures the whole-value
      certificate and uses `hcX.primrec` to feed `Nat.Partrec.Code`-level composition.
      There is **no** `RpnSentenceCodes → Computable (encode ∘ φ)` bridge in the repo
      (checked `Framework/RpnSplice.lean`, `Framework/RpnEmission.lean`), and building
      one means running `parseRpn` over the reassembled segment — provable, but another
      independent lemma.

**Why it is not worth it.**  The paper's §4.11–12 chains are quantified over
*Θ-definable* quotation families, whose numerals are exactly the value-typed objects
above; the whole-value interface is the faithful reading there, and the disclosure is
already recorded (`dd:fuel`).  Flipping it would strengthen only hypothetically-deep φ
in `thm:st`/`thm:ceu`/`thm:cee`, at the cost of a new arithmetic-digit layer that
nothing else in the repo consumes.  **Recommendation: leave `QuoteCodeOfMarket`
whole-value; the item-2 flip already wraps at that boundary via
`LUV.RpnThresholdCodeSeq.ofPolyThresholdCodeSeq`.**  Revisit only if a consumer
genuinely needs deep quoted sentences.

## Deliberately disclosed boundaries

- `M7-PREFIX-MACHINE` — **fully discharged 2026-07-26** (both emission certificates
  constructed; `PrefixMachineComputation` deleted). The only remaining disclosure for
  this node is the type-`(c)` non-universality of `prefixKappa` (a modeling statement,
  not a proof gap). See the record above and `notes/m7-prefix-machine-scope.md`.
- `M7-DUS-APPROX` — **narrowed to the polynomial clock, 2026-07-27** (Tranche U stages
  1–2): `M*` is constructed, universal, and lower-semicomputable — `universalSemimeasure`
  is a real axiom-clean inhabitant — and two of the three `DUSApproximationPresentation`
  fields plus the output-size half of the third are proved for the rounded table
  `gridApprox`.  What is still disclosed is **only** the poly-fuel emitter, and it needs a
  clamped dovetailer rather than the tabulation that landed.  See the Tranche U entry.

These two are the only intentional disclosures at the 13/15 target. The audit should
confirm no third boundary is assumed anywhere it isn't named.

`M7-STRICT-SEPARATORS` was the third until 2026-07-27; it is now **constructed** (see
Tranche S above): the interface was redesigned away from the provably uninhabitable
nested-prefix shape (`no_ce_null_prefix_family`), and all of its fields — including
`mass_class_tendsto_zero` — are discharged by constructions.


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
