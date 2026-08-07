# `thm:ccee` exact valuation — investigation and scoped plan

_2026-08-06. Status: scoped, not started. Investigated against the code (per the
2026-07-31 standing rule: every claim below about what an endpoint calls was made with
the proof body open, not from memory)._

## Goal

Replace the mesh product's `1/(n+1)` reflection slack — the one type-`(c)` substitution
with a known downstream consumer — with **exact** left reflection: an inhabitant of
`ConditionalExpectationQuote` at `slack ≡ 0` for an **arbitrary** e.c. source family,
so `thm:ccee` moves qualified → paper strength.

## What the investigation established (all verified in code)

1. **The master theorem needs no change.** `lic_no_expected_net_update_conditional`
   (`Properties/SelfTrust.lean:365`) is DP-generic and consumes slack through
   `slack_tendsto`; `slack ≡ 0` is a special case.
2. **The certificate needs no change.** `ConditionalExpectationQuote`'s `slack` field
   accommodates the exact case; `indicatorProductLUV_exact_left_reflected` already
   inhabits it at 0 for indicator sources. No `#assert_fields` churn.
3. **The route is a definitional extension of the deductive process, not of the
   theory.** The blocker was always the *emitter*: it cannot know `w (f n)`. But the
   deductive process is only required computable — no clock — and `w` **is** computable
   against the constructed market (`PGenerableRat.computable`,
   `BoundedEvaluation.lean:1461`). So the process itself can compute `w (f n)` exactly
   and enter, stagewise, the **defining biconditionals** for fresh product atoms:

   ```
   productAtom (n, r)  ↔  (X n).gt (r / w (f n))     (w (f n) > 0)
   ¬ productAtom (n, r) for r ≥ 0, productAtom (n, r) for r < 0   (w (f n) = 0)
   ```

   over an enumeration of `r : ℚ`. Every world consistent with the extended process
   then values `Z n := ⟨fun r => productAtom (n, r)⟩` at exactly `x · w (f n)` —
   `left_reflected` at `slack = 0`. Note the `w = 0` case is handled by the process's
   case split, so the old "exact needs `w > 0`" obligation **vanishes** (it was an
   artifact of the scaled-threshold route, not of exactness).
4. **The FFL/theory side is untouched.** No new T-provability, no internalization —
   the paper's first-order Θ contains the product *term* natively; propositionally the
   honest counterpart is exactly a definitional extension (fresh atoms + explicit
   definitions). This is why the old 3–4 week estimate was too high: it priced a
   quotation-presentation extension through T, which is not needed.
5. **All the combinators exist:** `DeductiveProcess.union` +
   `DeductiveProcessComputation.union` (`ConditioningPresentation.lean:112`) for
   `theoremDP T ∪ productDefDP`; the stage-dovetail recipe for computable processes
   (`gridDP`/`luvThresholdDP` pattern); `arithmeticThresholdLUV_polyThresholdCodeSeq`
   as the template for the product atoms' threshold emission (atom code =
   tag ⋅ ⟨n, ⟨k, i⟩⟩, poly-sized regardless of `w`); presentation lemmas
   (`quotationPresentation` fields) lift along `DP ⊆ DP'` monotonically.

## The one real design decision: atom freshness

The defining biconditionals are only jointly satisfiable if the fresh atoms do not
occur inside `X`'s own sentences (an adversarial `X` with
`(X n).gt r = ∼productAtom (n, r)` makes a stage unsatisfiable, killing `hworld`).
The paper has no analogous issue: its product is a *term*, not an atom. Options:

* **(A) Freshness premise (recommended).** The closed endpoint takes
  `hfresh : ∀ n q, productTag ∉ (X n).gt q |>.atoms`-style side condition. Honest,
  decidable-flavored, satisfied by every LUV the paper can express (their atoms carry
  other tags) and by every repo-constructed family. Disclosed as the propositional
  rendering's residue — replacing the slack disclosure with a strictly milder one.
* **(B) Occurrence-stratified atom codes.** Choose atom codes above everything `X`
  mentions at lower indices. Fails against fully adversarial `X : ℕ → LUV` (early
  sentences may mention late atoms); would need a well-foundedness premise anyway.
  Not worth it.

Go with (A) unless Abram's consuming argument needs adversarially self-referential
sources, which would be surprising (his sources are option-value LUVs over the base
language).

## Work plan

| # | Component | Content | Est. |
|---|---|---|---|
| 1 | `productDefDP` | Fresh-tag atom family; stage function computing `w (f n)` via `PGenerableRat.computable` and decoding `X`'s thresholds from a named code certificate; `mono`; `ComputableDeductiveProcess` via the dovetail recipe | 2–3 sessions |
| 2 | `hworld` for the union | Extend any completed world of `theoremDP T` by evaluating product atoms through their definitions (needs freshness); this is also the conservativity/non-vacuity story: every Θ-world extends, uniquely | 1–2 sessions |
| 3 | Exact `left_reflected` | `v ∈ cworlds(union) → v.ValuesAt (X n) x → v.ValuesAt (Z n) (x·w(f n))` from the biconditionals; `ValuesAt` needs all-rational coherence, supplied by enumerating ℚ across stages | 1–2 sessions |
| 4 | Threshold emission | `RpnThresholdCodeSeq` for the product-atom family, mirroring `arithmeticThresholdLUV` | 1 session |
| 5 | Closed endpoint + wiring | `lic_no_expected_net_update_conditional_exact_closed` over `LIA (theoremDP T ∪ productDefDP …)`; named threshold-code data for `X` (the DP consumes the *program*, so the ∃-shaped `RpnThresholdCodeSeq` must be accompanied by named code data — same pattern as `DeductiveProcessComputation` vs `ComputableDeductiveProcess`) | 1–2 sessions |
| 6 | Disclosure + rows | ccee row, README modeling-boundary list (slack paragraph replaced by definitional-extension + freshness paragraph), audit inventory, trust-surface note | 1 session |

**Total: 7–11 focused sessions ≈ 1.5–2 weeks.** Meaningfully below the old 3–4 week
estimate, for the stated reason (#4 above). Estimate history this project: three
overestimates, zero underestimates, all from pricing hypothetical routes instead of
read code — this one is priced from read code, but component 2's world-extension lemma
is the least-precedented piece and the most likely to grow.

## Risks / open questions

* **Statement-over-which-DP.** The exact endpoint is stated over
  `Θ ∪ product-definitions`, not bare Θ. This is faithful (the paper's Θ contains the
  product term; a definitional extension is the propositional counterpart) but it is a
  *different rendering* than the mesh route's bare-Θ statement. Decision for Anson at
  landing time: exact takes the ccee row (recommended), mesh kept or deleted as the
  bare-Θ variant — consolidation discipline says don't keep both without a reason;
  the reason here would be "Abram's argument wants bare Θ".
* **Freshness premise** (above) — mild, but it is a premise the paper doesn't state.
* Component 5's named-code certificate adds one small caller-facing structure —
  Tier-2 addition, `#assert_fields` entry, disclosed.

## Recommendation

Do **not** start before the Abram meeting: the mesh version is disclosed and serviceable,
and the meeting determines whether slack even matters downstream. If it does, this plan
starts with component 1 and the freshness decision already made.
