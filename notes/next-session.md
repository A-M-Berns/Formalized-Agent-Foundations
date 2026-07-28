# Logical Induction — handoff

_Last updated: 2026-07-27 (RPN-5 **COMPLETE** — both `thm:scon` symbol-metered endpoints proved and the criterion-level packaging restored; interim seam 1 CLOSED).
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

## INTERIM SEAMS (disclosed; seam 1 closed, seam 2 RESTING at route (B) — see below)

1. **Conditioning (`thm:scon`)** — **CLOSED 2026-07-27 (RPN-5).**  Both symbol-metered
   translation certificates are proved in `Witnesses/RpnConditioning.lean`
   (`conditionedTranslation_preserves_ecRpn`,
   `eventualConditionedTranslation_preserves_ecRpn`, both
   `EfficientlyComputable → EfficientlyComputable` over `RpnSentenceCodes ψ`), so the
   `translation_ec` fields of `GatedConditioningOperationalWitness` /
   `EventualConditioningOperationalWitness` are discharged by construction.  The
   operational witness constructors are back
   (`gatedConditioningOperationalWitness`, `eventualConditioningOperationalWitness`,
   `denominatorPatchedGatedConditioningOperationalWitness`) and the paper-facing
   endpoints again conclude `IsLogicalInductor` of the conditioned market
   (`ConditioningCompile.lic_conditioned_gated_ofMarketComputation`,
   `_eventualOfFloor`, `_eventual_ofMarketComputation`,
   `_fixed_ofComputationAndMarket`, `_growing_ofComputationsAndMarket`,
   `_gated_ofComputationsAndMarket`; over the constructed LIA,
   `lic_conditioned_fixed_unconditional` / `lic_conditioned_growing_unconditional`).
   The interim digit-transfer forms in `DigitConditioning.lean` are DELETED — no
   parallel layer survives.  The digit compilers (`..._preserves_ec₂`) remain as the
   internal Tok₂ route.

2. **Finite perturbations (`thm:ifp`/`app:ifp`)** — **RESTING at route (B), permanently
   disclosed (2026-07-28; blocked primitive proven structurally unbuildable — see the
   route-(A) stop-and-report and RESTING STATE below).**
   `EfficientPrefixPatch.preserves_ec` is the collapsed class;
   `lic_iff_of_finitePerturbation` is unchanged and fully proved (patch structures were
   always explicit hypotheses).  The LIA inhabitant remains reduced to
   `liaFreezeBefore_preserves_ecTok` (token-level content only); **`liaEfficientPrefixPatch`
   does not exist and the README row for `M7-PREFIX-PATCH` has been corrected to say so.**

   *What landed* (`Witnesses/RpnFreeze.lean`, green, axiom-clean): the symbol-level freeze
   transducer as the **third instance** of RpnConditioning's emitter-generic run rewriter —
   `freezeEmit` into `rpnConditionRun`, with the whole-stream contraction exactness
   `unRpn_rpnFreezeRun` following from the master commutation `unRpn_rpnConditionRun_of`
   against the token-model freeze (`freezeTokens`, the seven chunk equations, spliced body
   `freezeBody`).  Plus the run-level quote lookup the freeze needs: since the LIA prefix
   table is a finite entry list and a run for a *fixed* target is a constant-depth pattern
   (the target's Polish traversal with any subterm optionally escaped), the lookup is
   `matchRun` — a bounded composition of token comparisons, **not** a scan — characterized
   by `matchRun_sound` / `matchRun_complete` / `matchRun_iff` and transferred to the table
   by `runQuoteFromEntries_exact` / `runPrefixQuoteFromStates_exact`, with positional forms
   (`..._segOf`) for the emission side and the fuel certificate `matchRun_polyFueled`.

   *The obstruction.*  `matchRun_polyFueled` needs `PolyFueled ct tf` — a **poly-bounded**
   token function.  In the symbol-metered model the stream is a *digit* stream, so tokens
   are only `BigDigits` (values may be exponential; that is the point of the digit model,
   and `EfficientlyComputable.ofDigitEmitter` really does produce such streams).  All of
   `matchRun`'s tests factor through a small clamp — grammar tags `0/1/2/3/4`, atom tokens
   `a+5` — **except one**: at an escape leaf `1 :: c` it must decide
   `Encodable.decode c = some ψ` for a fixed subformula `ψ` and an exponentially large `c`.

   That decision is not expressible with the current `BigDigits` API (`add`, `mul`,
   `ltNat`, `natPair`, `succ`, `clampVal`, `comp`, `blockSeg`).  Reason: Foundation's
   `Formula.ofNat` ignores the payload at tag `0`, so `decode` is **not injective** —
   `decode (Nat.pair 0 k + 1) = ⊥` for every `k`.  Hence `{c : decode c = some ψ}` is
   infinite whenever `ψ` has a `⊥` subformula (i.e. essentially always, since negation is
   `φ 🡒 ⊥`), and membership in it reduces to *perfect-square testing* / `Nat.unpair`,
   i.e. to integer square root.  `PolyFueled` cannot carry the huge intermediates
   (`PolyFueled c f` demands `IsPolyBounded f`, and `evaln`'s guard forbids feeding a value
   larger than the fuel), and a digit-level `sqrt` does not fit `PolyFueled.prec`, whose
   iterated state must be poly-bounded while sqrt's natural state (partial root and
   remainder) is as large as the value.  **In the intended complexity model the claim is
   true** — `unpair` on poly-bit inputs is poly-time — so this is a `dd:fuel`-model
   limitation (type `(c)`), not a paper gap.

   **DECISION (Anson, 2026-07-28): route (A)** — build the `BigDigits` sqrt/`unpair`
   closure faithfully; (C) rejected (narrowing `def:ec` post hoc is what the audit
   exists to catch).

   ### Route (A) — ATTEMPTED, STOP-AND-REPORT (2026-07-28, worktree agent)

   Route (A) does **not** materialize, and the reason is structural rather than a matter
   of effort.  Recording it in full, because the boundary it exposes is a property of the
   whole `dd:fuel` calculus, not of this seam.

   **(A1) What the toolkit's closures actually have in common.**  Read `add`, `mul`,
   `ltNat`, `natPair`, `clampVal` in `Framework/DigitArith.lean` side by side: each is a
   `PolyFueled.prec` digit loop whose *carry* is `O(1)`- or `O(poly index)`-sized —
   `addCarry4 ≤ 1`, `mulCarry4 x y p ≤ 3(p+1)`, `conv4Partial ≤ 9i`, `ltFlag4 ≤ 1`, and
   `clampVal`'s pair of clamped accumulators.  The design invariant is exactly:
   **`BigDigits` is closed under an operation iff that operation's base-4 digit
   recurrence has a poly-bounded carry.**  Nothing else is available, because
   `PolyFueled.prec` requires `IsPolyBounded (fun m => st m.unpair.1 m.unpair.2)` — the
   iterated state is poly in `⟨m, i⟩`, hence poly in `m`, while a `BigDigits` value is
   `4 ^ poly m`.

   **(A2) The ceiling is the fuel model itself, not `prec`'s statement.**  `PolyFueled c f`
   bundles `Fueled c f b` with `IsPolyBounded b`, and `evaln`'s guard bounds a code's
   *input* by its fuel.  So every value ever fed to a sub-code is bounded by a polynomial:
   **the calculus has no big intermediates at all.**  Big values exist in this repo only
   through the hand-built `BigDigits` digit-array interface, which is an *interface*, not
   a computation model — so every new closure must come with an explicit small-carry
   algorithm.  There is no weaker `prec` hypothesis to relax.

   **(A3) Why square root has no small carry.**  The intended algorithm (base-4 restoring
   digit recurrence, consuming two digits of `v` per output digit) carries the pair
   `(R_j, W_j)` with `R_j = Nat.sqrt (v / 4 ^ (2j))` and `W_j = v / 4 ^ (2j) - R_j ^ 2`,
   satisfying `R_j = 4 R_{j+1} + d_j` and
   `W_j = 16 W_{j+1} + e_j - d_j (8 R_{j+1} + d_j)`, with `d_j` the largest `d ≤ 3` making
   the subtraction nonnegative.  Both components have `Θ(L - j)` base-4 digits.  This is
   not an artifact of the presentation: the residual is what determines every remaining
   output digit, so it carries `Ω(L)` bits, and **no MSD-first sequential recurrence for
   `sqrt` can have an `O(log)`-sized carry.**  (Contrast division by a *poly-bounded*
   divisor, whose running remainder is bounded by the divisor and therefore *is* a legal
   carry — that closure would be routine.  The blocked operations are exactly the
   *inverses* of the forward closures: `sqrt`, `unpair`, big-divisor `div`.  The toolkit
   is closed under the forward monotone big-value operations and open under inversion.)

   **(A4) Why the state-history trick does not rescue it.**  `prec` exposes `st m i` at
   *all* `i`, so nested `prec`s give random-access DP tables — that is how `mul`'s inner
   convolution feeds its outer carry.  But the sqrt recurrence is genuinely 2-D (row `j`,
   digit `k`) with a row-to-row dependence, and a `prec` step sees only the immediately
   preceding state *of its own row*.  Producing row `j` from row `j+1` needs either one
   `prec` per row (code depth `L`, and `PolyFueled` demands a single fixed `Code`) or a
   state holding a whole row (`Θ(L)` digits, forbidden by (A1)).  Recomputing instead of
   storing is exponential: the greedy `d_j = max {d ≤ 3 | (4 R_{j+1} + d) ^ 2 ≤ v / 4 ^ (2j)}`
   needs every higher digit, so `C(j) = poly + Σ_{i > j} C(i)`, i.e. `4 ^ L`.

   **(A5) The claim is still true in the intended model — and that is the disclosure.**
   `sqrt`/`unpair` on poly-bit inputs is poly-time (in fact uniform `TC⁰ ⊆ L`,
   Hesse–Allender–Barrington), and the fuel calculus *can* express any logspace
   computation (a single `prec` carrying an `O(log)`-bit machine configuration).  So
   `BigDigits.sqrt` is a true statement about the model, whose only known proof route is
   the Chinese-remainder / iterated-product division machinery of HAB.  That is a
   research-scale formalization, not a tranche.  Type `(c)`, disclosed; **not** a paper gap.

   **(A6) Two facts derived on the way, worth keeping.**
   * The escape test is *exactly* perfect-square testing.  `Formula.ofNat` ignores the
     tag-0 payload, so `decode c = some ψ` iff `c ∈ Image E_ψ`, where `E_ψ` is the fixed
     nest of `Nat.pair`/`succ` with one free parameter per `⊥` leaf.  At the base:
     `Nat.pair 0 k = k ^ 2`, so `decode c = some ⊥ ↔ c - 1` is a perfect square.  Deciding
     membership therefore *is* `sqrt`, with no cheaper special case.
   * **Expanding an escape shrinks the digit stream.**  `encode` is a tower: a formula with
     `s` nodes has depth `≥ log₂ s`, hence `≳ s ^ 2` base-4 digits.  So the escape payload's
     digit block is at least the square of the fully expanded Polish run it abbreviates.
     Consequences: the escape clause buys no *asymptotic* expressiveness (support for
     route (C)/(C′) being harmless in fact, though still not provably so — canonicalizing
     an existing emitter needs `decode`); and it re-explains why whole-value metering was
     never viable (`unRpn` of a length-`L` run is a canonical code of `≈ 4 ^ L` digits).

   **Recommendation for the next decision.**  Given (A2), the choices are genuinely three:
   stay at (B); adopt (C) as a *disclosed* modeling decision on `def:ec` (with (A6)'s
   second bullet as the honest argument that nothing is lost in fact); or adopt a new
   route **(D)**: state `BigDigits.sqrt` as a single named, isolated **axiom** (or `sorry`)
   in `Framework/DigitArith.lean`, disclosed in the README's Axioms section exactly like
   `ModalAgents`' two facts, and let Phases 2–3 of this seam land unconditionally on top
   of it.  (D) is the option that keeps `def:ec` untouched *and* makes the cost a single
   kernel-visible line rather than a silent narrowing — but it breaks the mainline's
   sorry-free/axiom-clean invariant, so it is Anson's call, not this agent's.  **No axiom,
   `sorry`, or grammar change was introduced by this tranche.**

   *Routes out (recorded)*:
   * **(A)** Add a `BigDigits` integer-square-root / `unpair` closure to `DigitArith`.
     Faithful, but needs a big-value recursion principle the file does not have today;
     this is a real development, not plumbing.
   * **(B)** Leave the seam open and disclosed (current state): `thm:ifp` stays fully
     proved but conditional on `EfficientPrefixPatch`, with no LIA inhabitant at the
     collapsed class — only the token-level `liaFreezeBefore_preserves_ecTok`.
   * **(C)** Restrict the RPN grammar's escape clause to *canonical* codes
     (`parseRpn`, `Framework/Criterion.lean`: accept `1 :: c` only when
     `Encodable.encode (decode c) = c`).  Then `matchRun`'s escape test becomes equality
     with a **constant**, which `BigDigits.ltNat` decides, and everything already landed in
     `RpnFreeze.lean` closes the seam with only the emission certificate left to assemble.
     Canonicalization only shrinks codes, so morally the class is unchanged — but *proving*
     the two versions of `def:ec` agree needs exactly the blocked primitive, so adopting
     (C) is a disclosed modeling decision about `def:ec` itself, not a theorem.

   ### RESTING STATE: route (B) (2026-07-28)

   Route (A) proven structurally impossible (above); (C) rejected — **polarity argument**:
   `EfficientlyComputable` occurs *negatively* in `noExploit`, so narrowing `def:ec`
   silently weakens every `IsLogicalInductor` conclusion repo-wide, which is exactly the
   move the audit exists to catch.  (D) (a named `BigDigits.sqrt` axiom) not adopted — it
   would break the mainline's axiom-clean invariant for one witness instance.  So the seam
   rests at **(B)**: `thm:ifp` fully proved, hypothesis-carrying; token-level content
   `liaFreezeBefore_preserves_ecTok` proved; no LIA inhabitant of `EfficientPrefixPatch`
   at the collapsed class.  **Severity, for the record: this ceiling bit exactly once in
   the entire ~85k-line program** — every paper construction (all fifteen boundaries, the
   universal semimeasure, the universal prefix machine, Kučera–Demuth) landed inside the
   fuel class, which is now an empirical fact, not a hope.  Directionality of the gap:
   our class ⊆ the paper's poly class, so every constructed exploiting trader is a
   legitimate paper trader (property conclusions paper-valid as-is); the only weakening
   is in the criterion-satisfaction claim (`noExploit` quantifies over fewer traders —
   a hypothetical "sqrt trader" whose digit extraction needs big-value inverse arithmetic
   is not proven defeated).  Audit item carried forward: `EfficientPrefixPatch` is
   inhabited only degenerately (`cutoff = 0`).

## RPN-5 — symbol-level translation compilers — **COMPLETE (2026-07-27)**

Final record.  `Witnesses/RpnConditioning.lean` now carries the whole symbol-level
conditioning compiler, green and axiom-clean (`propext, Classical.choice, Quot.sound`
throughout; no `sorryAx`).

**Architecture (as landed).**  The transducer is generic in its mode-2 emitter:
`rpnConditionRun (emit : List ℕ → ℕ → List ℕ)`, with `rpnConditionSegment` /
`rpnGuardedConditionTokens` likewise.  Two instances:
`rpnPriceEmit blocks ε` (conditional-price body) and
`rpnZeroAwareEmit zeroDays blocks ε` (finite zero-day set bound to the constant `1`).
Both the master commutation and the emission certificate are proved once in
emitter-generic form and instantiated twice:

* `unRpn_rpnConditionRun_of` — whole-stream contraction exactness for any emitter,
  given the token-model run's chunk equations (`hRnil/hRsingle/hRone/hRpayload/
  hRprice/hRpricePair/hRtrade`) and the per-chunk emitter contraction `hemit`.
  Instances: `unRpn_rpnConditionRun` (price), `unRpn_rpnZeroAwareConditionRun`.
* `rpnGuardedConditionRun_polySegStream_of` — the digitized guarded rewrite of any
  digit `PolySegStream` is a `PolySegStream`, given that the emitted segment read at
  the **clamped** day is polynomially emittable (exact wherever the guard passes).
  Instances: `rpnGuardedConditionRun_polySegStream`,
  `rpnGuardedZeroAwareConditionRun_polySegStream`.

Strategy-level agreement: `strategyOfTokens_rpnGuardedConditionTokens_trades` and
`strategyOfTokens_rpnGuardedZeroAwareConditionTokens_trades` (both routed through
guard honesty `strategyOfTokens_unRpn_trades_eq_nil_of_rpnBigDay`, so a failed guard
empties both sides).

Frame pass and gated join (unchanged from the ninth tranche): `rpnFrameRun` /
`rpnFrameOutput` with `frameAgree_unRpn_rpnFrameOutput` and its prefix form
`frameContract_rpnFrameOutput`; the certificate `rpnFrameOutput_polySegStream`; budget
exactness `rpnTradeCountAt_eq_frameTradeCount`; the acceptance gate
`rpnStructurallyAccepts` / `rpnStructurallyAccepts_agree` / `rpnDepthScan`; the gated
join `rpnSafeSeparatedFrameOutput` with `rpnSafeSeparatedFrameOutput_polySegStream`
and `strategyOfTokens_unRpn_rpnSafeSeparatedFrameOutput_trades`.

**The two endpoints (final assembly).**  Both follow one shape: source certificate ⇒
clocked digit stream of the RPN-expanded serialization; guarded price pass; budget
codes from the symbol-level trade-run count (`rpnTradeCountScan`, exact against
`frameTradeCount` by `rpnTradeCountAt_eq_frameTradeCount` — the `Unreadable` disjunct
is discharged in the nonempty-trades branch); gated two-leg frame join; digitize;
`ec_of_rawSegStream`.  The eventual form adds the zero-aware price pass and the launch
gate `if F.cutoff ≤ n then … else []`.  Trades-shape reconciliation mirrors
`conditionedTranslation_preserves_ec₂`'s last section verbatim.

**Packaging.**  See INTERIM SEAMS item 1 above — CLOSED.  `AxiomAudit.lean` gained an
`RpnConditioning.lean` block (12 construction endpoints + 3 witnesses + 6 criterion
endpoints); the `DigitConditioning.lean` block lost the interim transfer names.

Remaining RPN work: **interim seam 2 only** — the RPN freeze transducer restoring
`liaEfficientPrefixPatch` (run-walk + finite run-comparison against the
`liaPrefixQuote` table, in `M7Witnesses.lean`).

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
   `preserves_ec` ⇒ `liaEfficientPrefixPatch` restored.  *(Transducer + run lookup landed
   2026-07-28 in `Witnesses/RpnFreeze.lean`; the emission certificate is blocked on the
   escape-payload decode test — see INTERIM SEAMS item 2.)*

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
`not_polyFueled_two_pow`, closure ops) and one disclosure sentence.

**(c) — added 2026-07-28 — the inverse-operation ceiling is the same disclosure at
root.**  The route-(A) stop-and-report (seam 2, above) proved the fuel calculus has no
big intermediates at all, so `BigDigits` closes exactly under poly-carry digit
recurrences: forward ops yes, inverses (`sqrt`, `unpair`, big-divisor `div`) provably
no.  This is an artifact of *interpreter-clock metering specifically*: on a TM with
binary tapes, `sqrt` is trivially poly-time (uniform `TC⁰ ⊆ L`, Hesse–Allender–
Barrington).  Consequence for the watch item: if CSlib (or anyone) ships a usable
poly-time TM class, the single `evaln`-fuel ↔ TM-step polynomial simulation theorem
would not just retire disclosure (a) — it would dissolve the inverse-op ceiling and
un-block the `EfficientPrefixPatch` LIA inhabitant too.  One bridge theorem, two
disclosures closed.  Until then, the only in-model route is the HAB CRR/iterated-
product machinery (research-scale, not a tranche). Likewise the last
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

1. **DONE 2026-07-28** — `ConditioningPresentation.condition_codes` →
   `RpnSentenceCodes`.  `thm:scon` now accepts DEEP condition sequences.

   *Flipped:* `ConditioningPresentation.condition_codes` (Properties/Conditioning.lean)
   and — because growing finite conjunctions are exactly the deep case — the constructor
   input `CompactConditioningProcessComputation`, whose two whole-value fields
   (`condition_code` + `condition_code_poly`) collapse into the single field
   `condition_codes : RpnSentenceCodes fun n ↦ deductiveStageCondition (extra.D n)`.
   `fixedConditioningPresentation` (constant ψ) wraps via `.ofPolySentenceCodes`;
   `conditioningPresentationOfComputations` now just forwards `more.condition_codes`.
   Downstream in `ConditioningCompiler.lean`: `conditionedQuoteCode(_spec)`,
   `conditionedMarketComputation`, `denominatorPatchedQuoteCode(_spec)`,
   `denominatorPatchedMarketComputation`, `exists_eventual_condition_price_floor`,
   `eventualConditioningFloor_nonempty_of_jointConsistency`,
   `eventualConditioningFloorOfJointConsistency`.  Payoff at the RPN-5 packaging
   (`RpnConditioning.lean` §`ConditioningCompile`): the two
   `RpnSentenceCodes.ofPolySentenceCodes C.condition_codes` wraps are gone.

   *The one genuine whole-value consumer*, and how it was discharged: the conditioned
   **market quote table** is keyed by sentence *code*, so `conditionedQuoteCode` needs a
   program emitting `Encodable.encode (ψ n)` as a value.  It never needed that program
   to be *poly* — only recursive.  New in `Construction/LIACompiler.lean`
   (§`RpnDecodePrimrec`, beside `parseRpnC_prim`): `RpnSentenceCodes.primrec`
   (`PolySegStream.primrec` + `parseRpnC_prim` + `parseRpnC_eq`) and
   `RpnSentenceCodes.exists_code`.  So symbol-metered emission gives *recursive*, not
   polynomial, whole-value naming — which is exactly what that boundary asks for.  This
   is the reusable move for any future "flip blocked by a value-typed quotation
   boundary" (cf. Tranche P item 3): check whether the boundary wants poly or merely
   computable.

   *`EfficientRepeatedEnumeration.ofPoly` is now dead.*  **DEMOLITION EXECUTED
   2026-07-28**: `EfficientRepeatedEnumeration.ofRpn` now lives beside `ofCE` in
   `M7Witnesses.lean` (`ConditioningPresentation.lean`'s parked copy deleted), and
   `ofPoly` + `triangularRepeat_codes` + their `#print axioms` lines are gone.  `ofRpn`
   joined the `M7Witnesses.lean` `#assert_axioms_clean` inventory block.  No
   ₙ-suffixed or superseded layer survives here.
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
