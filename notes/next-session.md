# Logical Induction — handoff

_Last updated: 2026-07-26 (collapse surgery landed; M7-PREFIX-MACHINE certificates proved & merged).
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

## THEN: EC-SEQ — 𝓔𝓒-sequence migration (INTERFACE + ENGINE LANDED 2026-07-26)

DONE (Framework, all axiom-clean):
* `RpnSentenceCodes φ` := ∃ block stream `s`, `PolySegStream s` ∧ each `s n` parses
  (`parseRpn`) to `φ n` with empty remainder.  Constructors: `.ofCanonical` (deep
  sequences at poly symbol count), `.ofPolySentenceCodes` (2-token escape blocks),
  `.comp` (poly reindex).  In `Framework/RpnEmission.lean`.
* Splice engine (`Framework/RpnSentence.lean`): `parseRpn_append` (self-delimitation),
  `parseRpn_block_head`, general-block chunk contractions
  `unRpn_price_chunk_block`/`unRpn_trade_chunk_block`, transparency layer
  (`UnRpnTransparent`, `.nil/.append/.payload/.single`), `EF.priceFree` +
  `EF.serialize_unRpnTransparent`, and the trade-splice contraction
  `unRpn_tradeBlocks`.
* Realizations (`Framework/RpnEmission.lean`):
  `EfficientlyComputable.ofSingleTradeBlocks` (one trade/day, price-free coefficient
  stream + 𝓔𝓒 sentence stream) and `.ofTradeBlocks` (variable count via `concatVar`).

REMAINING (the per-family march):
1. Coefficients WITH price leaves (buy-signal `max(0, c − φ*ⁿ)` shapes) need the
   price-slot splice: serialize-with-blocks for concrete coefficient shapes, using
   `unRpn_price_chunk_block` + transparency for the non-slot fragments.  Per-family
   concrete shapes; no new theory expected.
2. Structure-field migration: `PolySequence.sentence_poly` (Affine),
   `PolyTradeEmulatable.sentence_poly` (ROI), and the Pseudorandomness local mirror
   → `RpnSentenceCodes`.  Construction sites adapt via `.comp`/`.ofPolySentenceCodes`;
   consumer emission assemblies (ROI `serializeTrades` streams, e.g.
   `PolyTradeEmulatable` ~ROI:683) re-assemble with block slots and realize through
   `ec_of_rawSegStream` — the deep part is the ROI family layer
   (`EfficientlyEmulatable`), which meters the firm's universal-program emulation and
   needs its RPN mirror before the budgeted/fractional composite traders certify in
   the collapsed class directly (today they go through `noExploitTok`, which stays
   correct meanwhile — migration is a strengthening, not a fix).
3. Then swap property-statement hypotheses `PolySentenceCodes` → `RpnSentenceCodes`
   family by family.  FIRST FAMILY MIGRATED (2026-07-26): `lic_provind_seq`
   (thm:provind fragment) — `buySeq_ec_rpn` via `ofSingleTradeBlocks` (const-1
   coefficient is price-free), hypothesis now `RpnSentenceCodes φ`, endpoint invoked
   through the collapsed `noExploit`.  Next targets in feasibility order:
   (a) price-slot splice families with CONCRETE serialize shapes (thm:pi buy-signal
       `buySig` — one price leaf on the traded sentence; use `UnRpnContractsTo`
       composition: transparent frames ++ `.priceChunk` ++ transparent ++
       `.tradeChunk`, both slots fed from the same hφ block stream);
   (b) thm:und (obuTrader): restructure the obu emission from equal-length
       `PolySegStream.blocks` to `concatVar` variable segments with block slots
       (arm blocks lose fixed length once slots vary); also migrate
       `EfficientRepeatedEnumeration.sequence_poly` (constructors adapt via
       `.ofPolySentenceCodes`, triangular reindex via `.comp`);
   (c) the `PolySequence.sentence_poly` (Affine) migration — **the EC-SEQ critical
       path**.  SURGICAL MAP (derived 2026-07-26, execute like the collapse map):
       * Field flip: `PolySequence.sentence_poly : RpnSentenceCodes sentence`
         (Affine.lean:236; add `import ...Framework.RpnEmission` — no cycle:
         RpnEmission ← DigitArith/RpnSentence/Emission ← Computable/Criterion,
         Affine imports Criterion+Computable only).  Same flip for the mirrors:
         `PolyTradeEmulatable.sentence_poly` (ROI:76) and the Pseudorandomness
         local structure (:854).
       * Affine-internal: `priceFeature_polySeg` (294) — obtain the block stream
         `⟨s, hs, hparse⟩`, replace `hpriceTok`'s middle token
         `[encode (sentence …)]` with `s ∘ hcanonical`-indexed segments
         (`priceSlotSeg hs (hcanonical …)`), producing the SPLICED stream; its
         statement becomes `PolySegStream (fun z => splicedPriceFeature …)` plus a
         companion contraction fact via `UnRpnContractsTo` (price chunks + payload/
         operator transparency; the coefficient serializations must be shown
         transparent — they may contain price leaves in general! Check: coefficient
         price leaves are on *coefficient* sentences, which are NOT covered by the
         sentence field; families with priced coefficients need those slots spliced
         too — survey each PolySequence inhabitant's coefficient shapes first;
         PolySequence may need a `coefficient_priceFree` (or spliced coefficient
         stream) field mid-flight).  Same for `magnitudeFeature_polySeg` (536).
       * Construction sites (wrap, cheap): TimelyLearning 32/90, Relationships
         (exclusiveExhaustive_polySequence), Pseudorandomness 79, AffinePersistence
         553/725, AffineCoherence 387, FeedbackTruth 330, ComputationSyntax
         320/338/391/408, LUV inhabitants — use
         `(.ofPolySentenceCodes ⟨c, h⟩).comp hindex`.
       * Consumers (the long tail; each ends in an ecTok realization that must
         become `ec_of_rawSegStream` with a whole-stream contraction proof):
         AffinePersistence 224, AffinePreemptiveLearning 303/363/394,
         Calibration 1459, QuotationAffine 589, LUVSyntax 643, FeedbackEmission
         262-263, Affine 632, and the ROI budgeted/fractional composites
         (`PolyTradeEmulatable` ~683, `EfficientlyEmulatable` RPN mirror).
       * Keep the interim compat (`noExploitTok`) callers green until each chain is
         flipped; flip `hLI.noExploitTok → hLI.noExploit` per chain as its cert
         lands in the collapsed class.: survey 2026-07-26 confirms thm:tl/perkno, thm:lex
       (`exclusiveExhaustive_polySequence`), pseudorandomness, and the presentation
       structures (SelfTrust/Introspection/MetaLearning `sentence_codes` fields) all
       route through PolySequence or PolySentenceCodes-field interfaces, so per-family
       splices don't reach them; the field flip + the ROI family layer
       (`PolyTradeEmulatable`, `EfficientlyEmulatable` RPN mirrors) unlocks them all
       at once.  Construction sites adapt via `.ofPolySentenceCodes`/`.comp`;
       consumers re-assemble their `serializeTrades` streams with block slots
       (engine: `priceSlotSeg`, `UnRpnContractsTo`, `unRpn_tradeBlocks`) and realize
       through `ec_of_rawSegStream`.

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
