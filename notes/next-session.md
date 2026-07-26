# Logical Induction — handoff

_Last updated: 2026-07-26 (RPN layer + collapse surgery plan; history pruned to git).
Branch: `logical-induction`._

# 🎯 ACTIVE PLAN 2 — the `Tok₃`/RPN layer + 𝓔𝓒-sequence migration (2026-07-26)

Goal (Anson): do all remaining 𝓔𝓒-sequence-hypothesis work via the **layered RPN
route** — a third emission model `Tok₃` where sentence slots carry Polish-notation
symbol runs (poly digit length = poly *symbol* count, the paper's `𝓔𝓒` metering with
no pair-code-balance caveat), then migrate the property-tail hypotheses.

**Done so far (commits `edaf2c7`..`d0eefa0`, all green, Framework/RpnSentence.lean +
Framework/RpnEmission.lean + Construction/Witnesses/RpnCriterion.lean):**
* RPN-1: Polish coding `rpn` (tags 0=⊥,2=➝,3=⋏,4=⋎, atoms t+5, escape tag 1 =
  literal pair code), fuelled block parser `parseRpn` (Option.bind form; strict
  suffix, fuel-mono), canonical + escape round trips, injectivity.
* RPN-2: `unRpn` grammar-driven stream contraction (fuel = length; failed blocks emit
  the undecodable code 0 and stop, preserving rejection), fuel-invariance, chunk
  equations; `escExpand` (escape splice, ≤ 2× length) with chunk equations; the
  **parser simulation** `streamReadFrom_unRpn_escExpand` (equal results, or the
  contraction failed while the original is stranded non-ready) with corollaries
  `deserializeTrades_unRpn_escExpand` / `strategyOfTokens_unRpn_escExpand`.
* RPN-3: `clockedTrader₃`/`EfficientlyComputableTok₃` (decode = `strategyOfTokens ∘
  unRpn ∘ undigitize`); slot automaton `escModeStep/escModeList` (clamp-invariant) +
  fold form + per-position range form; poly `escModeScan`; realization bridges
  `ecTok₃_of_rawEmission`/`ecTok₃_of_rawSegStream`; **both inclusions**
  `EfficientlyComputableTok₂.toTok₃` (escape splice via concatVar + the simulation)
  and `EfficientlyComputableTok.toTok₃`.  KEY DESIGN WIN: the escape tag makes the
  inclusions verbatim splices — **no digit-level sqrt/unpair needed** (drop that from
  the old sizing).

**CONSOLIDATION DIRECTIVE (Anson, 2026-07-26, supersedes the layered plan below):**
do the flip in **collapsed single-class form** — no ₃-suffixed public layer.  Rename
the symbol-metered semantics to plain `EfficientlyComputable` (the paper's `def:ec`),
demote `EfficientlyComputableTok`/`Tok₂` to internal emission constructors
(`EfficientlyComputable.ofTokenEmitter`/`.ofDigitEmitter` — today's `toTok₃`/`toTok₂`
inclusions renamed), give `enumeratedTrader` a SINGLE decode (the RPN decode; the
parity/mod-3 tagging disappears — it existed only because multiple decode conventions
were separate classes), one `trading_firm_dominance`, one `IsLogicalInductor` with one
`noExploit` field, one `LIA_is_logical_inductor`.  Absorb every ₂-suffixed public name
(incl. `lic_conditioned*₂`, `IsLogicalInductor₂`) in the same sweep; property files
keep compiling via the constructors.  This deliberately re-freezes `#assert_fields
IsLogicalInductor` — same disclosed protocol as the Tranche-2 flip.  Rationale: no
structural evidence of previous versions (consolidation.md).

**RPN-4 status 2026-07-26 (later): the decode is DONE and primitive recursive**
(commits `23c7947`..`3dd7220`): `parseRpnC`/`unRpnTokensC` code-level forms +
correspondences; strong-recursion packages (`parseF`/`parseGCore`/`parseG`,
`unF`/`unGCore`/`unG`) with step laws; `parseRpnC_prim` and **`unRpn_prim`** via
`Primrec.nat_strong_rec` (assemblies live in RpnCriterion.lean where
`sentencePrimcodable` is visible).  Proof-practice: fully bind every branch `have`
before `of_eq` (holes elaborate too early otherwise); constructor-form `cases`
(not `rcases`) for casesOn iota; `simp only [hts]` + `rfl` for under-binder
scrutinee recomputation; `(Primrec.encdec.comp _).of_eq fun _ => rfl` bridges the
Primcodable-vs-raw-instance mismatch.

**THE COLLAPSE SURGERY (next; do stepwise, each green-committable):**
A. Partition M7Witnesses — **exact map derived 2026-07-26, ready to execute**:
   MOVE to new `Framework/Emission.lean` (imports Framework.Computable only; all
   verified free of Properties/LIACompiler deps): the simulation core lines 15-793
   (codeEvalBound … dovetailFound, incl. Prec/Rfind compile sections), the
   PrefixPatchCompile block 2697-2809 ONLY (namespace opener + ecClock …
   clockedTokens_polySegStream; close the namespace there), and root-level
   `EfficientlyComputableTok.toTok₂` 3478-3502.  STAY in M7Witnesses: the middle
   794-2693 (polyFueled_eqConst + Settlement sections — polyFueled_eqConst is NOT
   used by the moved block, only by the staying freeze part), the freeze-coupled
   PPC decls 2810-3092 (freezeNextNat … freezeBefore_preserves_ec — re-open
   `namespace PrefixPatchCompile` around them, names stay stable), the
   sentenceMatches/liaPrefixQuote tail 3093-3477, and `liaEfficientPrefixPatch`.
   M7Witnesses gains `import LogicalInduction.Framework.Emission`; register
   Emission in Framework.lean.  Then steps B-F as below.
   (Original survey note: move the simulation core
   (lines ~15-793: `codeEvalBound`..`BoundedEvalnCompiler` + the base/pair/comp/prec/
   rfind compile sections) and the `PrefixPatchCompile` namespace (2697-3477, incl.
   `ecClock`, `clockedTokens_polySegStream`, `freezeControlNat`) **name-stably** into
   a new `Framework/Emission.lean` (import Framework.Computable).  KEY INTEL: the
   file has ZERO uses of Properties/IsLogicalInductor, and its only true LIACompiler
   deps are in the MIDDLE sections that stay behind (`deserializeTrades_prim` at
   1816 inside SettlementCompile 1315-2693; the eq-const/dovetail section 794-1315
   may also stay or move if clean) — verify the moved block references nothing from
   the middle, else move the specific helpers too.  M7Witnesses then imports
   Emission; all call sites keep their names (PrefixPatchCompile prefix preserved).)
B. Move the grammar/decode DEFS (`rpn`, `parseRpn`, `unRpnTokens`, `unRpn`,
   `clockedTrader₃`, the class) from RpnSentence into Framework/Criterion.lean next
   to `serialize`/`streamStep` (thematically the serialization layer); RpnSentence
   keeps the lemma corpus.
C. Post-A, move the inclusions (`toTok₂` from M7Witnesses, `toTok₃` from
   RpnCriterion) into Framework as the emission constructors.
D. Rename: `EfficientlyComputable` := the symbol-metered class (paper's `def:ec`);
   constructors `EfficientlyComputable.ofTokenEmitter`/`.ofDigitEmitter`; ONE
   `IsLogicalInductor.noExploit` field over it; property files fixed via a compat
   lemma (`noExploit` applied to token certificates through the constructor —
   one-line diffs at call sites).
E. Enumeration: single decode (`TraderProgram.trader` := the RPN decode; parity/tag
   dispatch deleted); coverage = one lemma; one `trading_firm_dominance`; LIACompiler
   `enumeratedTraderTrades_prim` uses `strategyOfTokensTrades_prim ∘ unRpn_prim ∘
   undigitize_prim ∘ clockedTokens_prim`; one `LIA_is_logical_inductor`.
F. AxiomAudit: re-freeze `#assert_fields IsLogicalInductor`; absorb ALL ₂/₃-suffixed
   public names (incl. `lic_conditioned*₂`, `IsLogicalInductor₂`,
   `LIA_is_logical_inductor₂`); update README/docstrings so no layering archaeology
   remains.  Then RPN-5 (conditioning compilers against the one class — RPN
   conjunction is concatenation) and EC-SEQ (`RpnSentenceCodes` + `PolySequence`
   migration).

**RPN-4 progress + the exact continuation point (superseded by the above; kept):**
* DONE (`Framework/RpnComputation.lean`, commit `169f014`): suffix discipline
  (`parseRpn_suffix`/`parseRpnC_suffix`), `encode_lt_encode_cons`/
  `encode_le_of_suffix`, and the strong-recursion package `parseF`/`parseGCore` (+
  step law `parseGCore_spec` — lookups below `m` are hit because
  `pair fuel' (encode suffix) < pair (fuel'+1) (encode ts)`) and `parseG`/
  `parseG_spec` over the value table.  ALSO DONE earlier: `parseRpnC`/`unRpnTokensC`
  code-level forms with exact correspondences (`23c7947`).
* NEXT (attempted, reverted — pitfalls recorded): `parseG_prim : Primrec parseG` by
  combinator assembly over `PCtx := (List (Option (ℕ×List ℕ)) × ℕ) × (ℕ × List ℕ)`,
  then `Primrec₂ parseRpnC` via `Primrec.nat_strong_rec` (α := Unit, g := parseG on
  snd, H := parseG_spec) and the pair/encode wrapper (`Denumerable.ofNat_encode`
  closes it).  Pitfalls hit: (a) `Primrec.encdec` for `Sentence` produced an
  *instance mismatch* (`Primcodable.toEncodable` vs `Formula.instEncodable`) — find
  how the repo's existing Sentence-decode primrec proofs (e.g. the streamStep chain
  feeding `strategyOfTokensTrades_prim` in LIACompiler) pin the instance, and reuse
  that idiom; (b) the nested-bind branch (`hbin`) needs its inner lambdas built over
  explicit pair projections with `.to₂.of_eq` normalization — write the target
  function of each `have` VERBATIM as it appears in `parseGCore` and let `of_eq`
  discharge the association differences; (c) assemble the outer dispatch as
  `Primrec.option_some.comp (Primrec.nat_casesOn hfuel (const none) hinner.to₂)`
  with `hinner := (Primrec.list_casesOn hts0 (const none) hbody.to₂).of_eq …` — the
  final `of_eq fun prev => by rw [parseG, parseGCore]; rcases …length.unpair.1 …;
  rcases Denumerable.ofNat …` (both matches iota-reduce; close with `rfl`).
* After `parseRpnC_prim`: `unRpnTokensC` primrec the SAME way (its recursion also
  shrinks the pair; subroutine calls to `parseRpnC` via `parseRpnC_prim`), then
  `unRpn_prim`, then the collapsed flip per the directive above.

**The superseded layered plan (naming only — the technical content stands):**

**Next: RPN-4, the criterion flip.**  Scoped this session, execute in order:
1. **`unRpn` Primrec (the tall pole), via code-level parsing.**  Do NOT build
   Formula-constructor primrec-ness.  Define `parseRpnC : ℕ → List ℕ →
   Option (ℕ × List ℕ)` emitting the *pair code*: ⊥ ↦ `pair 0 0 + 1`, atom t ↦
   `pair 1 (t-5) + 1`, binop ↦ `pair tag (pair c1 c2) + 1`; the **escape validity
   test is the `Primcodable Sentence` round-trip field** (`Primcodable.prim` gives
   primrec `c ↦ encode (decode c : Option Sentence)`; result 0 = invalid, `e+1` =
   the canonical re-encode `e`).  Correctness: `parseRpnC fuel ts = (parseRpn fuel
   ts).map (fun (φ, r) => (Encodable.encode φ, r))` by the same induction.
   Primrec via `Primrec.nat_strong_rec` (Mathlib, Computability/Primrec/List.lean:274)
   on the paired index `m = Nat.pair fuel (encode ts)`: recursive calls hit
   `pair (fuel-1) (encode rest)` with `encode rest < encode ts` (cons strictly grows
   the list code; sub-parse outputs are suffixes — need a small
   `parseRpn_isSuffix` + encode-suffix-mono lemma).  Then `unRpnC`/`unRpn_prim` the
   same way (its recursion also shrinks the pair).
2. **Enumeration flip**: redefine `enumeratedTrader` dispatch from parity to `j % 3`
   (residue 0 = token decode, 1 = digit decode, 2 = RPN decode via
   `TraderProgram.trader₃`), mirror the per-residue ec lemmas + THREE coverage
   lemmas (`exists_enumeratedTrader₃_eq`), patch `enumeratedTraderTrades_prim`
   (LIACompiler ~2928 — the compiler's ONLY decode coupling) with the third branch
   using `unRpn_prim`.
3. **Dominance + LIA**: `trading_firm_dominance₃` (via the factored
   `trading_firm_dominance_of_covered`), `lia_no_efficient_trader_exploits₃`,
   `IsLogicalInductor₃ extends IsLogicalInductor₂`, `LIA_is_logical_inductor₃`,
   `exists_logical_inductor₃`.  Mirror the Tok₂ flip (TraderEnumeration/TradingFirm/
   LIACompiler + AxiomAudit entries).
4. **RPN-5, conditioning at level 3**: translation compilers `Tok₃ → Tok₃`.  In RPN
   the conjunction shell is CONCATENATION (`rpn (φ ⋏ ψ) = 3 :: rpn φ ++ rpn ψ`) — no
   bignum pair shells; mirror DigitConditioning's guarded compiler with the sentence
   slots spliced at the symbol level.  Then `lic_conditioned*₃` and the
   unconditional-over-LIA forms.
5. **EC-SEQ**: `RpnSentenceCodes φ := PolySegStream (fun n => rpn (φ n))` (the
   paper's 𝓔𝓒 class on the nose) + inclusion from `PolySentenceCodes` (poly-value
   code ⟹ its rpn stream is poly — needs a code→rpn-length bound: rpn length ≤
   code value; emitter via... scope when reached); `PolySequence₃` mirror of
   `AffineCombination.PolySequence` (sentence_poly → RpnSentenceCodes;
   const/coefficient serialize streams → digitized-with-rpn-slots), then per-family
   migration (copy-only families first: thm:tl, thm:und).

Gotchas this session: Mathlib names are `Option.bind_some`/`bind_none`; `rcases h : e`
substitutes `e` in the GOAL too (existential witnesses become `rfl`s); ₂/₃-suffixed
lemmas placed inside a namespace break dot-notation (declare `_root_.…` or call
explicitly); `Formula.ofNat` is WF-compiled (no defeq reduction — use its equations);
the `(fuel fuel' : ℕ)` binders of fuel-congr lemmas must be EXPLICIT or `by omega`
side goals see metavariables.

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

## M7-PREFIX-MACHINE — remaining work (record, 2026-07-26; NOT the active focus)

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

**Residual — `PrefixMachineComputation`, exactly two fuel-model certificates:**
1. `sentence_poly : PolySentenceCodes prefixSentenceEnum`;
2. `approx_poly : PolyRatCodes prefixApprox` (equivalently the denominator stream
   `2^{κᵢ}`, via `prefixDen_polyFueled`).

Believed satisfiable (all output values proved poly-bounded in the scope note —
`2^{κᵢ} ≤ 32(d+1)²(c+1)² ≤ poly(i)`); the obligation is interpreter programming,
not a size obstruction.  Discharge order if reopened:
* `negDepth`/`negCore`/`size` are **single-chain prec iterations** (strip one
  `imp _ ⊥` layer / halve per step) — feasible now; plus **clamped** `2^κ`
  materialization (plain doubling violates `prec`'s poly-state bound off-diagonal;
  clamp by the proved bound — the `BigDigits.clampVal` pattern).  That discharges
  `approx_poly` *given* `sentence_poly`.
* `sentence_poly` needs **canonicity of `n`** (is `n` in `Formula.toNat`'s range) —
  tree-recursive; course-of-values tables are value-exponential in this fuel model,
  so it needs an explicit small-stack/digit encoding (stack shrinks √-per-level,
  ≈ 2·log n bits total).  **This is exactly the ACTIVE PLAN 2 RPN/digit territory**
  — after the `Tok₃` collapse lands, a Polish-token index may sidestep
  `toNat`-canonicity entirely (validity of an RPN run is a linear counter scan).
  Reassess then rather than building a bespoke stack machine.

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
TM class; `Turing.PartrecToTM2` is unbounded). Per CLAUDE.md rule 6 this is a
stop-and-report boundary: keep the model-card calibrations (`PolyFueled.primrec`,
`not_polyFueled_two_pow`, closure ops) and one disclosure sentence. Likewise the last
quotation type-(c) — code-indexed atoms *mean* their arithmetic instances via
`theoremDP`'s enter/refute clauses — is closed by an intended-semantics bridge lemma
(Σ₁-soundness ⟹ truth-in-ℕ for entering atoms) if one is missing, **not** by replacing
the propositional substrate.


## Deliberately disclosed boundaries

- `M7-PREFIX-MACHINE` — **largely discharged 2026-07-26** (Kraft proved in-repo, machine
  model + kraft field + negation compiler constructed, gate emissions derived); residual
  = the two `PrefixMachineComputation` emission certificates plus the disclosed
  non-universality of `prefixKappa`. See the record above and
  `notes/m7-prefix-machine-scope.md`.
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
