# M7-PREFIX-MACHINE — construction scope & status

_Drafted 2026-07-20. Reopened and largely discharged 2026-07-26; status below._

The boundary that, if constructed, discharges the Occam-bound disclosures
`lic_occam_lower` and `lic_occamBounds` (paper `thm:ob` / App. `ob`). Previously fully
disclosed; now discharged down to **two residual fuel-model emission certificates**.

## Status after the 2026-07-26 session

Construction lives in `LogicalInduction/Construction/Witnesses/`:

- `KraftInequality.lean` — **`kraft_inequality` PROVED** (step 1 of the original plan).
  Body produced by Aristotle (job `65eaafaa-2ba0-4501-8002-8e9e2043f4d8`, run
  `2d017ff6…`; the earlier `bc2df18a…` attempt had failed), re-elaborated and
  kernel-checked in-repo per the trust rule. Counting argument; axioms
  `propext`/`Classical.choice`/`Quot.sound`. Audited in `AxiomAudit.lean`.
- `PrefixMachine.lean` — **steps 2, 4 (partially), and 5 constructed**:
  - `natCode` (unary-size marker + terminator + `testBit` payload, length
    `2·size(n+1)`), prefix-free-injective (`natCode_prefix_inj`).
  - `sentCode φ = natCode (negDepth φ) ++ natCode (encode (negCore φ))`,
    prefix-free-injective; `prefixKappa φ = |sentCode φ| + 1`. The negation-depth
    factoring is load-bearing: it is what makes the negation overhead **additive**.
  - `prefixSentenceEnum` — total enumeration, canonical `decode` with `atom n`
    fallback; surjective (`covers`), index multiplicity ≤ 2.
  - **`kraft` field proved** (`prefixKraft`): split indices into the canonical and
    fallback classes (each injective), apply `kraft_inequality` to each class's
    prefix-free codeword image; the `+1` slack bit in `prefixKappa` halves every
    weight, paying exactly for multiplicity two.
  - **`PrefixNegationCompiler` fully discharged** (`prefixNegationCompiler`,
    overhead = 2, proved): `κ(∼φ) ≤ κ(φ)+2` because `∼` bumps only the depth field,
    and `size` grows by ≤ 1 per successor.
  - `prefixApprox i = 2^{-κ(sentenceᵢ)}` exact (the concrete κ is computable, so the
    from-below approximation is constant-in-stage); `nonneg`/`le`/`tendsto` proved.
  - **Both `OccamThresholdEmission` streams derived, not assumed**
    (`prefixThresholdSum_polyRat`, `prefixInverseWidth_polyRat`): they are `mulc`
    arithmetic on the weight denominator `D i = 2^{κᵢ}` (`pair 2 (D·j⁴)` and
    `pair (2·(2Dj⁴)) 1` under the closed-form rational encodes).
  - Endpoints `lic_occam_lower_ofPrefixMachine` / `lic_occamBounds_ofPrefixMachine`
    consume only `PrefixMachineComputation` + the standard market hypotheses.
    All axiom-clean, audited, paper-node-annotated.

## Residual input — `PrefixMachineComputation` (the honest remainder)

**Update 2026-07-26 (second session): `approx_poly` is DERIVED, residual is down to
one certificate.** `approx_polyRat_of_sentence` (PrefixMachine.lean) proves
`PolySentenceCodes prefixSentenceEnum → PolyRatCodes prefixApprox`, so the structure
collapsed to the single field `sentence_poly`; `PrefixMachineComputation.approx_poly`
is now a theorem.  The derivation is:

- `dcStep`/`dcIter_encode` — the code-level un-negation scan: iterating the branchless
  strip step `encode φ` times computes `⟨encode (negCore φ), negDepth φ⟩` from
  `encode φ` (saturation via `negDepth_le_encode`); poly-fueled by `PolyFueled.prec`
  with state `≤ ⟨e, j⟩` (`dcIter_polyFueled`).
- `p2s`/`p2s_polyFueled` — materializes `2^{size (x+1)}` by *halving-driven doubling*
  (state `⟨(x+1)/2^j, 2^{min j (size (x+1))}⟩`): the doubling is clocked by the halving,
  so the state stays `≤ 2(x+1)` and the off-diagonal `prec` clamp the original plan
  called for is unnecessary.
- `prefixDen_eq` — `2^κ = 2 · p2s(negDepth)² · p2s(encode ∘ negCore)²`, then `mulc`
  assembly and the rational encode `⟨2, 2^κ⟩` (`encode_prefixApprox`).

Remaining conclusion-free fuel-model certificate, in the exact style of the existing
`BitPrefixCodeComputation` disclosure (`BitPrefixSyntax.lean`):

1. `sentence_poly : PolySentenceCodes prefixSentenceEnum` — a `Nat.Partrec.Code`
   emitting `encode (prefixSentenceEnum n)` with polynomial fuel.

**Further reduced (same session):** `validCode : ℕ → Bool` (structural descent over
`Formula.toNat`'s tagged-pair format) decides canonicity, with both directions proved
(`validCode_encode`, `of_validCode`), and `sentencePoly_of_invalidBit` shows a
poly-fueled emitter of the single **bit** `invalidBit n = if validCode n then 0 else 1`
suffices for `sentence_poly` (`encode_prefixSentenceEnum` collapses the emitted value to
`ifzSel ⟨⟨n, pair 1 n + 1⟩, bit⟩`).  So the entire residual is now: *one poly-fueled
Boolean* — the tree-recursive canonicity decision of the scope note's item (ii).

**Satisfiability (believed, not proved).** Both output values are polynomially
bounded — `encode (sentenceₙ) ∈ {n, pair 1 n + 1}` and
`2^{κᵢ} ≤ 32(d+1)²(c+1)² ≤ poly(i)` (`d = negDepth`, `c = encode ∘ negCore`, both
`≤ encode (sentenceᵢ) ≤ (i+1)² + i + 2`) — so `not_polyFueled_two_pow`-style size
separations do **not** bite; the algorithms are genuinely polynomial-time. The
obligation is interpreter programming in raw `Nat.Partrec.Code`, not a size or
model obstruction.

**The precise obstruction (why this session stopped here).** Emitting
`encode (prefixSentenceEnum n)` requires *deciding canonicity* of `n` — whether
`n` is in the range of `Formula.toNat` — and computing `κ` additionally requires
`negDepth`/`negCore`. In the `dd:fuel` toolkit:

- `negDepth`/`negCore` and `size` are **single-chain iterations** (strip one
  `imp _ ⊥` layer per step; halve per step), implementable via `PolyFueled.prec`
  with poly-bounded state — feasible, a few hundred lines.
- `2^κ` needs **clamped materialization** (plain doubling violates `prec`'s
  poly-state bound at off-diagonal inputs; clamp by the provable
  `2^κ ≤ 32(E+1)⁴` bound, the `BigDigits.clampVal` pattern) — feasible.
- Canonicity/validity of `n` is **tree-recursive** (the `ofNat` descent over both
  `unpair` children). Course-of-values tables are impossible in this fuel model
  (a table of `n` entries has exponential *value*), so it needs an explicit-stack
  simulation. The stack content is small (entries shrink as `√` per level, total
  ≈ `2·log n` bits), so a mixed-radix/digit-stream encoding works **in principle**
  — this is exactly the territory of the in-flight `RpnSentence`/`DigitArith`/
  `BigDigits` tranche (B1a/B1b, other agent), which was out of bounds for this
  session. Estimated multi-session; do not start it casually.

Recommended discharge order if reopened: (i) `negDepth`/`negCore`/`size` prec
chains + clamped `2^κ` ⇒ discharges `approx_poly` *given* `sentence_poly`;
(ii) the validity descent (possibly on top of the landed RPN/digit machinery,
where a token-stream representation may sidestep `toNat`-validity entirely) ⇒
discharges `sentence_poly`.

## Modeling disclosure (type-`(c)`, recorded at construction time)

`prefixKappa` is the length function of a **fixed computable self-delimiting code**,
not a *universal* prefix machine: the paper's `κ` is universal prefix complexity
(uncomputable; weights only lower-semicomputable — which is why the boundary has a
from-below `tendsto` field at all). All downstream theorems are stated for arbitrary
`κ`, so the generic paper-faithful statements are untouched; the new endpoints are a
genuine non-vacuous *instance* in which "simplicity" means code length under this
fixed code (`2^{-κ(φ)} ≈ 1/poly(encode φ)`). The universality upgrade (dovetailing
over all programs) is a strictly larger construction and remains undone. Disclosed
in the module docstring of `PrefixMachine.lean`.

## Original field-by-field table (kept for reference; statuses updated)

`PrefixMachinePresentation κ` (`Properties/OccamBounds.lean:33`):

| Field | Status 2026-07-26 |
|---|---|
| `sentence` | **constructed** (`prefixSentenceEnum`) |
| `sentence_codes` | residual (`PrefixMachineComputation.sentence_poly`) |
| `approximation` + `_nonneg`/`_le`/`_tendsto` | **proved** (exact weights) |
| `approximation_codes` | residual (`PrefixMachineComputation.approx_poly`) |
| `kraft` | **proved** (`prefixKraft` ← `kraft_inequality`) |
| `covers` | **proved** |

`OccamThresholdEmission`: **derived** from `approx_poly`.
`PrefixNegationCompiler`: **fully discharged** (overhead 2, proved).
