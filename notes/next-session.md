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

Gotchas hit (add to the log): `clampVal (const B)` clamps at `B+1`, so automaton
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


## Deliberately disclosed boundaries

- `M7-PREFIX-MACHINE` — **fully discharged 2026-07-26** (both emission certificates
  constructed; `PrefixMachineComputation` deleted). The only remaining disclosure for
  this node is the type-`(c)` non-universality of `prefixKappa` (a modeling statement,
  not a proof gap). See the record above and `notes/m7-prefix-machine-scope.md`.
- `M7-DUS-APPROX` and `M7-STRICT-SEPARATORS` — remain disclosed unless Anson reopens them.

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
