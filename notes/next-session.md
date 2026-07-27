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

REMAINING (in feasibility order):
1. Master commutation for the price pass (chunk induction above) ⇒ guarded version ⇒
   guard-honesty transfer (`strategyOfTokens_trades_eq_nil_of_bigDay` on the
   contracted stream) ⇒ a price-pass-only strategy-level equality.
2. Frame-pass mirror (two legs; same automaton + certificate assembly shape as
   `rpnGuardedConditionRun_polySegStream`; trade slot = 3 :: run ++ blockψ(n));
   its commutation reuses the SAME localization lemmas (trade-run instance).
3. Zero-aware variants (mirror guardedZeroAwareConditionTokens).
4. Endpoints `conditionedTranslation_preserves_ecRpn` /
   `eventualConditionedTranslation_preserves_ecRpn` (statements recorded as comments
   at file end) ⇒ witness constructors (translation_ec fields in
   Properties/Conditioning.lean structures) ⇒ restore class-instance
   lic_conditioned_* endpoints, delete interim digit-transfer forms ⇒ AxiomAudit.

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

**Remaining: the polynomial clock only** (`M7-DUS-APPROX` proper).  Step 1 gives
*lower-semicomputability*; `DUSApproximationPresentation` wants `PolyRatCodes`.  The
session pinned down what that actually costs:

1. **`universalApprox` can never satisfy it, and the fix is legitimate.** `PolyFueled`
   demands `IsPolyBounded` of the *encoded output*, and the `(1/2)^(i+1)` weights alone
   force denominators of order `2^n`.  But `DUSApproximationPresentation` requires only
   `nonneg`/`le_mass`/`tendsto` — **not** monotonicity — so the table may be rounded down
   onto the `1/(n+1)` grid.  That is done and proved: `Dovetail.gridApprox`, with
   `gridApprox_le_mass`, `gridApprox_tendsto`, and `encode_gridApprox_le` /
   `isPolyBounded_encode_gridApprox` (encoding `≤ (2(n+1)+1)^2`).  All axiom-clean, on the
   audit surface.  **Two of the three presentation fields, plus the size half of the
   third, are therefore already discharged.**
2. **What is left is exactly the fuel half:** a code computing `gridApprox` in `evaln`
   fuel polynomial in `⟪n, i⟫`.  This is *not* a re-certification of `tabCol`: a program
   run for `n` steps can emit rationals of doubly-exponential magnitude, and the trimming
   threads those exact values, so the poly emitter must round **inside** the recursion
   (onto the same `1/(n+1)` grid) — a different, clamped dovetailer, whose exactness proof
   must be redone since grid rounding breaks the monotonicity the current
   `trim_tendsto_of_exact` relies on.  `DUSThresholdEmission` then derives by rational
   arithmetic on those denominators, as `prefixThresholdSum_polyRat` did.  Estimate 1–3
   sessions; do not start it expecting to reuse `tabCol`.
3. Then upgrade `PrefixMachine.lean`'s κ to universal prefix complexity: dovetailing
   weights are lower-semicomputable, so the presentation's `tendsto` field does real
   work (from-below stage convergence); the Kraft field needs the universal machine's
   prefix-free domain (adapt `kraft_inequality` application to the c.e. domain
   enumeration).  This removes the type-(c) in PrefixMachine's docstring and makes
   `lic_occamBounds_ofPrefixMachine` paper-strength Occam (up to the additive-constant
   slop the paper itself has).  Untouched.

Tranche S does **not** need this: its one open statement is written against
`UniversalContinuousSemimeasure`'s own approximation fields (see Tranche S).

## Tranche S — M7-STRICT-SEPARATORS — redesigned and landed (2026-07-27)

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
| `mass_class_tendsto_zero` | **open** — the disclosed residue |

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
3. `hmass` — **open, and now the sole boundary of `thm:strict`.**

### The one remaining statement

```lean
Tendsto (fun n ↦ ((separatorConsistentAt n).map M.mass).sum) atTop (𝓝 0)
```

for `M : UniversalContinuousSemimeasure`.  Everything it needs is in place:
`kleene_recursively_inseparable` (proved here) is the computability side, and `M`'s
`approximation` / `approximation_mono` / `approximation_tendsto` fields are the
measure side.  **No Tranche-U dependency** — the proof is against the interface, not a
concrete dovetailer.

Proof plan (Kučera–Demuth, following `app:strict`'s sketch), with the Lean-side costs:

1. **Antitone.**  `m n := ((separatorConsistentAt n).map M.mass).sum` is non-increasing:
   every `σ ∈ separatorConsistentAt (n+1)` has `σ.take n ∈ separatorConsistentAt n`
   (`evaln` is monotone in fuel, so stage-`n` decisions are among stage-`(n+1)` ones), the
   map is at most 2-to-1, and `children_le` bounds each fibre by the parent's mass.  Lean
   cost: list-sum bookkeeping over `allBitStrings` (needs `Nodup`, or a switch of
   `consistentAt` to `Finset`).  This is the fiddly-but-routine part.
2. **Limit `r := ⨅ n, m n ≥ 0` exists.**  Antitone + bounded below.  If `r = 0` we are
   done, so assume `r > 0` for contradiction.
3. **Fix a level.**  Choose `k` with `m k ∈ [r, 6r/5)` and a rational `q ∈ [4r/5, r)`.
4. **The separator.**  On input `j`, search over stages `s` for an approximation-level
   witness that the mass of the level-`s` class restricted to `bit j = 0` (resp. `1`)
   exceeds `q`; output the majority side.  Termination uses `approximation_tendsto` (the
   true sum exceeds `q`, so some finite approximation does).  Computability: the search is
   `Nat.rfind` over a decidable rational predicate built from `M.approximation_code`
   (`Nat.Partrec.Code.evaln` + `Primrec.ofNat`, exactly the pattern in
   `kleeneDecideNat_computable`), then `Computable` by totality — the
   `Partrec.rfind` + `Part.get` pattern.
5. **Correctness.**  If the vote says `0` but `j ∈ A₁`, the class consistent with the
   constraints keeps mass `≥ r` while the chosen side holds `≤ 6r/5 − 2r/5 = 4r/5 < r`;
   contradiction.  Feed the resulting computable separator to
   `kleene_recursively_inseparable`.

Estimate: 2–4 sessions, most of it steps 1 and 4.  Step 1 is worth doing first and
independently — it is a clean lemma about `M` and `separatorConsistentAt` with no
computability content, and it is what makes `r` exist.

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
- `M7-STRICT-SEPARATORS` — **DEFECTIVE AS STATED (kernel-checked, 2026-07-27)**:
  `StrictSeparatorPresentation` is uninhabitable modulo one mechanical bridge —
  its `repetition` field forces `M.mass (prefixes i) ≥ c > 0` by universality
  (`strictSeparatorPresentation_not_ce`, Construction/Witnesses/StrictSeparators.lean),
  contradicting `mass_tendsto_zero`.  The paper's `app:strict` uses single-bit
  CONSTRAINT theories + class-mass, not nested prefixes.  DECISION (Anson,
  2026-07-27): **redesign approved** — and **EXECUTED the same day**: the interface
  was redesigned in place (the old nested-prefix shape is provably uninhabitable —
  `no_ce_null_prefix_family`); the market half is
  `strict_domination_of_null_separator_class`; the endpoint statement is UNCHANGED.
  Kleene recursive inseparability is fully proved.  All fields but
  `mass_class_tendsto_zero` are constructed; see Tranche S above for the three named
  residual inputs (hatoms / hce / hmass — hypotheses, not sorries).

These three are the only intentional disclosures at the 12/15 target. The audit should
confirm no fourth boundary is assumed anywhere it isn't named.


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
