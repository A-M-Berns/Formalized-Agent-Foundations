# Handoff — LI machine/input write-out migration (`thm:halts`, `thm:loops`, `thm:dontwait`)

**Goal:** `qualified theorem nodes: 6 → 3`, leaving only the §4.10 family
(`thm:pac`, `thm:pazfc`, `thm:incons`). Do **not** start the §4.10
bounded-consistency (`Con(Θ,k)`) project.

## State

| | |
|---|---|
| Green branch | `agent/li-final-freeze` @ `685a7f1`, pushed |
| WIP branch | `agent/li-machine-track-wip` @ `732ab88`, pushed — **RED, do not merge** |
| Classification now | `exact=37, strengthened=7, corrected=2, refuted=1, qualified=6` |
| Qualified 6 | `thm:halts`, `thm:loops`, `thm:dontwait` + §4.10 `thm:pac`, `thm:pazfc`, `thm:incons` |

`685a7f1` is fully green: `lake build` (3723 jobs), `AxiomAudit`,
`check-paper-nodes`, `check_endpoint_coverage`, `lint_paper_labels`,
`check_paper_wiring`, `check_trust_surface` all pass; no `sorryAx`.

The WIP branch has the whole machine-track migration but fails with **18 errors**
in `CondEndpoints.lean` and `QuoteCodeOfMarket.lean`. Recover it with
`git diff 685a7f1 agent/li-machine-track-wip`.

## What is already established (do not redo)

### The diagnosis is settled, and the migration is mathematically free

Two independent read-only audits confirmed: on this path the Gödel value is used
**only as an opaque payload assembled by `Nat.pair`**. Every proof obligation that
touches it — `re_complete`, `universalHaltingSchema_spec`,
`ComputationTheoryPresentation.halting_enters`, `theoremDP_covers` — is
`∀ z : ℕ` with **no magnitude dependence whatsoever**. Nothing runs the machine,
decodes `z`, or compares magnitudes under a clock. No step needs the whole value.

Paper wording (`notes/1609.03543v5-main.tex`): `def:ec` at tex:753-757 is runtime
polynomial in `n`; `thm:halts` at tex:1931-1933 says in as many words that it must
be possible to *write out the source code* of `mₙ` in time polynomial in `n`, and
`⟨x⟩` is a sequence of **bitstrings**. A length-`n` bitstring has value `2ⁿ`.

### The bottleneck chain (identical for all three nodes)

```
lia_learns_halting_patterns_unconditional        ComputationDP.lean:549   (thm:halts)
lic_learns_provable_nonhalting_patterns_uncond.  ComputationDP.lean:807   (thm:loops)
lic_does_not_anticipate_halting_unconditional    ComputationDP.lean:823   (thm:dontwait)
  ↓ hm, hi
representedHaltingClaims / representedBoundedHaltingClaims  ComputationSyntax.lean:592 / :609
  ↓ sentence_poly
RepresentedSemidecidableClaims.sentence_poly     MetaLearning.lean:25
  ↓ consumed by
lic_provind_true / lic_provind_false             AffineCoherence.lean:888 / :908
  ↓ hφ
AffineCombination.sentenceAffine_polySequence    TimelyLearning.lean:37
  ↓ sets
PolySequence.sentence_poly                       Affine.lean:294
  ↓ consumed ONLY via BigSentenceCodes.ofRpnSentenceCodes at
Affine.lean:363, AffineProvability.lean:49
```

The last line is the key fact: **the polynomial bound is discarded one step
later** — the trader-emission lane is already written against `BigSpliceStream`
with no bound on emitted token values.

`ComputableHorizon` (`ComputationSyntax.lean:405`) is **clean** — program plus
spec, no growth bound. Do not touch it, and do not touch `not_polyNatCodes_ack`
(`ComputationSyntax.lean:427`), which is the proof that the horizon
generalization is strict.

## What is DONE on the WIP branch and worth keeping

1. **Strictness witnesses (complete, compiled, axiom-clean).** In
   `ComputationSyntax.lean`, next to `not_polyNatCodes_ack`:
   - `bigDigits_two_pow_not_polyNatCodes` — `xₙ = 2ⁿ` is an `n`-bit string, in
     `BigDigits`, refuted for `PolyNatCodes`.
   - `twoPowMachine n := Denumerable.ofNat Nat.Partrec.Code (2^n)` with
     `encode_twoPowMachine : encode (twoPowMachine n) = 2^n`
     (`Nat.Partrec.Code` is `Denumerable`, so encode is a bijection — this is why
     the witness is clean), and
     `digitMachineCodes_twoPowMachine_not_polyMachineCodes`.

   Both `[propext, Classical.choice, Quot.sound]`. **These are self-contained and
   could be cherry-picked onto the green branch on their own.**

2. **Claim generators rewritten on digits**, in `ComputationSyntax.lean`
   (`_poly` → `_digits`): `computationClaimSentence_digits`,
   `haltingClaimInput_digits`, `boundedHaltingClaimInput_digits`, and the four
   `*ClaimSentence_digits` wrappers. All go through `BigDigits.const`,
   `BigDigits.natPair`, `BigDigits.succ`, `BigDigits.of_polyFueled` — no
   materialization of the giant `Nat` anywhere.

3. **The three canonical signatures widened** to
   `(hm : DigitMachineCodes machines) (hi : BigDigits inputs)` at
   `ComputationDP.lean` :552, :809, :825 and the three `_ofComputation` layers.

4. **§4.10 secondary defect removed as collateral**: `BoundedComputation.input_poly`
   and `SemidecidableComputation.input_poly` are now `BigDigits input` (their `N+`
   witnesses use `BigDigits.of_polyFueled` / `BigDigits.const`). This does **not**
   touch the `Con` schema and does not change those rows' qualification.

5. **New Big mirrors, all compiled:**
   - `BigDigits.primrec` (`DigitArith.lean`) — a write-out value is recoverable
     from its own digits by `nat_rec'`; this is what lets a `Computable`
     consumer take the wider class. Legitimate because primitive recursion has
     no time budget; it can **not** manufacture a `PolyFueled`.
   - `DigitRatCodes.computable` (`QuoteCodeOfMarket.lean` — must live there,
     `Primcodable ℚ` is not in scope in `Framework/`).
   - `BigTokenStream.primrec`, `BigSentenceCodes.primrec`,
     `BigSentenceCodes.exists_code` (the latter two in `LIACompiler.lean`).
   - `BigSentenceCodes.{ofCanonical, ofPolySentenceCodes, modDispatch}`,
     `EfficientlyComputable.ofSingleTradeBlocksBig`,
     `BigSpliceStream.{payload, serialize_efMin, serialize_clip01, serialize_oneMinus}`.
   - `undigitizeStep_prim` / `undigitize_prim` moved from `private` in
     `LIACompiler` up to `DigitArith`, made public, private copies deleted.

## Why it is red — the one thing to solve

`RpnSentenceCodes` was swept repo-wide to `BigSentenceCodes` (163 occurrences,
32 files). That is correct for the affine/trader lane, but it collides with two
subsystems that **cannot** move:

1. **`LUV.RpnThresholdCodeSeq`** — defined in `Framework/Expectations.lean:106`.
   `DigitArith.lean:21` imports `Expectations`, and `WriteOut` imports
   `RpnEmission → DigitArith`. So `Expectations` sits **below** `WriteOut` and
   cannot name `BigSentenceCodes`. Same import-cycle boundary that already forces
   `GeneratedRatFeature.polyTok` to stay value-bounded.
2. **The conditioning compiler** (`RpnConditioning.lean`, `CondStep.lean`,
   `ConditioningPresentation.lean`, `Conditioning.lean`) destructures its sentence
   certificate into a `PolySegStream` and runs `digitizeStream` on it.

I reverted those files, which then made their *consumers*
(`CondEndpoints.lean`, `QuoteCodeOfMarket.lean`) fail the other way. That
oscillation is the whole remaining problem.

### Recommended fix

Do **not** sweep `RpnSentenceCodes` globally. Instead keep the Rpn class as a
legitimate stronger internal certificate (the user's "public/internal split") and
insert `BigSentenceCodes.ofRpnSentenceCodes` at exactly the boundary where an
Rpn-side producer meets a Big-side consumer. Concretely, widen only:

- `PolySequence.sentence_poly` (`Affine.lean:294`)
- `PolyTradeEmulatable.sentence_poly` (`ROI.lean:103`)
- `RepresentedSemidecidableClaims.sentence_poly` (`MetaLearning.lean:25`) and
  `InconsistentTheoryClaims.{inconsistency,consistency}_poly` (:53, :54)
- `FeedbackTraderEmission.sentence_poly` (`Pseudorandomness.lean:857`)
- the `hφ` binders of `lic_provind_true/false/lic_provind` (`AffineCoherence.lean` 889/909/932)
  and of `sentenceAffine_polySequence` / `sentenceMinusProbability_polySequence`
  (`TimelyLearning.lean` 37/95)

and leave every other `RpnSentenceCodes` alone, wrapping at call sites. That is
roughly what the WIP branch does *plus* an over-broad sweep; the sweep is the
part to drop.

## Also worth knowing

- **`BitPrefixSentences.prefix_codes`** (`UniversalSemimeasure.lean:80`) and
  `LUVCombinationSyntax` thresholds are Rpn producers feeding Big consumers —
  wrap, don't widen.
- **`thm:provind` gets stronger** as a side effect (its `hφ` widens). It is
  currently classified `exact`; widening a hypothesis is a strengthening, so the
  row needs re-reading, not just re-counting. Same for `thm:perkno` and whatever
  else `TimelyLearning.lean:354` / `HistoricalMaturity` hold.
- **`def:ec`'s qualification may narrow.** `RpnSentenceCodes` bounds emitted
  *token values* polynomially, so `BigSentenceCodes` is arguably the more faithful
  rendering of the paper's e.c. sentence sequence. The `def:ec` row says the
  symbol-metered classes "exist for sentences but not for naturals, machine codes
  or rationals" — that sentence is now stale in three ways. Re-read it; do not
  let it block the pass.
- **Record for the final adversarial audit:** the `Expectations`-below-`WriteOut`
  import cycle now pins *two* interfaces to the value-bounded stream
  (`GeneratedRatFeature.polyTok`, `LUV.RpnThresholdCodeSeq`). Determine whether
  that imposes a real restriction on paper ℙ-generability, or whether it is an
  import-cycle artifact masquerading as a faithful interface. Breaking the cycle
  (moving `undigitize`/`BigDigits` below `Expectations`, or moving
  `GeneratedRatFeature` up) would settle it.
- **Do not** convert a `BigDigits` certificate back into a whole-value
  `PolyFueled` to reuse an old constructor. It is not provable —
  `not_polyFueled_two_pow` refutes it — so any such attempt ends in a `sorry`.

## Gates to run before declaring done

```
lake build LogicalInduction && lake build && lake build AxiomAudit && lake build APITests
./scripts/check-paper-nodes.sh
python3 scripts/check_endpoint_coverage.py
python3 scripts/lint_paper_labels.py
python3 scripts/check_paper_wiring.py
python3 scripts/gen-trust-surface.py && python3 scripts/check_trust_surface.py
```

Use `~/.claude/scripts/safe-lake.sh build`, never bare `lake`. Run
`~/.claude/scripts/resource-guard.sh check` first. Regenerate the classification
counts from the ledger — do not hard-code them.
