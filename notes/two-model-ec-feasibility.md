# Two-model `def:ec` — feasibility spike (2026-07-29)

Read-only scoping of the plan to close the fuel-model efficiency boundary (the
"Planned future work" item 1 in `LogicalInduction/README.md`): define efficient
computability at a genuine machine class, enumerate that class in the trading firm via
a poly-overhead universal simulator, and keep the fuel calculus as the certification
tool through the inclusion fuel-poly ⟹ machine-poly. Conducted against the installed
toolchain (Mathlib at the pinned commit; CSlib not present). Every existence claim
below was verified by grep against the installed source.

## What Mathlib provides today

`Mathlib/Computability/TMComputable.lean` **does define a poly-time machine class** —
`Turing.TM2ComputableInPolyTime` (line 210), over `Computability.FinEncoding`, with a
`Polynomial ℕ` time bound — but the class has **zero theory**: its complete contents
are forgetful maps, `Inhabited` instances, and `id` shown poly-time. No composition,
no pairing, no closure, no link to `Partrec`/`Primrec`, and nothing else in Mathlib
imports it.

Three structural facts dominate the costing:

1. **No timed simulation theory exists.** Every simulation in Mathlib
   (`TM2to1.tr_respects`, `TM1to1`, `TM1to0`, `PartrecToTM2.tr_respects`) is stated
   via `Turing.Respects`, defined through `Reaches₁` — a transitive closure that
   discards step counts by construction. `TMToPartrec.lean` says so explicitly: the
   poly-time claim for its compiler is "not proved here."
2. **`FinTM2` is not enumerable as-is.** Its type parameters are arbitrary `Type`s and
   `TM2.Stmt` carries function values; no `Encodable` instance or Fin-normal-form
   lemma exists. A machine-class enumeration must first build that normal form.
3. **Mathlib's two TM stories don't touch.** The `PartrecToTM2` compiler's label type
   is infinite (not a `FinTM2`), so Mathlib proves neither direction of
   "Partrec ↔ TM2-computable" in the bundled sense.

## The easy inclusion (fuel-poly ⟹ machine-poly)

Route: fixed-code `evaln` cost lemma (greenfield; beware `comp`/`pair` fuel-sharing —
a uniform bound in `|c|` needs memoisation, but the per-trader form only needs a fixed
code) → quantitative `Nat.Partrec.Code → ToPartrec.Code` translation (the existing
`exists_code` has no size control and is not reusable) → a **timed** `PartrecToTM2`
(requires a global stack-size invariant Mathlib never states — the substantive new
mathematics) → `FinTM2` packaging + `FinEncoding` combinators (also absent).
Estimate: ~120–200 lemmas / 3000–6000 lines.

## The hard side (universal enumeration)

In the fuel model both halves of the enumeration property are *definitional*
(`EfficientlyComputable` is literally the image of the enumeration;
`enumeratedTrader_ec` is `rfl`-shaped). At a machine class both become theorems, and
the second becomes exactly "a poly-overhead universal simulator" — of which Mathlib
has none, nor the normal form needed to state one. Build: Fin-normal form + index
(fiddly: `Stmt` mixes data and functions), timed fixed-alphabet reduction, the
universal simulator itself (quadratic overhead suffices; ~2000–4000 lines), clamping
to total traders, and exact-coverage. Estimate: ~150–250 lemmas / 4000–7000 lines on
top of the inclusion.

## Verdict — staged plan

* **Stage 0 (days):** check CSlib in a scratch worktree; decide Mathlib-`FinTM2` vs.
  an in-repo machine defined with counted steps from day one. *Recommendation:
  in-repo machine* — the expensive part of the retrofit is re-proving Mathlib's
  simulation files with invariants their proofs weren't designed to carry, and since
  `TM2ComputableInPolyTime` has no attached theory, nothing is lost by not landing on
  it.
* **Stage 1 (2–4 weeks):** the counted machine, `RunsInTime`, the class mirroring
  `EfficientlyComputable`'s `(a,k)` shape. First standalone deliverable: composition
  and pairing closure — the first nontrivial theorems about poly-time TM
  computability in Lean, upstreamable to Mathlib.
* **Stage 2 (2–4 months):** the inclusion `EfficientlyComputable → MachinePolyEC`.
  Half-closes the lower-calibration boundary in the direction the property tail
  uses; every existing fuel certificate is preserved as the certification tool.
* **Stage 3 (4–9 months):** enumeration + universal simulator; `thm:li` at the
  machine class. No partial credit before the end of this stage.
* **Stage 4 — do not attempt:** the converse inclusion (machine-poly ⟹ fuel-poly) is
  false as stated: the digit calculus provably fails to close under inverse
  operations (`sqrt`, `unpair`) whose carries exceed the poly-bounded-state
  requirement of `PolyFueled.prec`. Flip side: a machine class would inhabit
  `EfficientPrefixPatch.preserves_ec`, currently uninhabited for exactly this reason.

**Honest total: 8–15 months of focused work, ~8,000–13,000 lines. Research-scale.**

**Single riskiest step:** the timed simulation chain's global stack/tape-size
invariant (Stage 2). De-risking move before committing: prototype the timed-`Respects`
framework on the smallest simulation (`TM1to0`) first. If the invariant is awkward
there, the whole retrofit route should yield to the in-repo machine immediately.

## Incidental corrections fed back into the repo

The spike surfaced two disclosure-prose defects, both queued to the de-slop wave: the
model card's claim that Mathlib exposes no poly-time machine class (it exposes one
with no theory — a materially different obstruction), and dangling citations of the
retired `notes/next-session.md` at several disclosure sites (the substance survives in
the adjacent docstrings; the pointers must become self-contained).
