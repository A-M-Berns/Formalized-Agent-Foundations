# Boundary 1 — the efficiency model: what closing it would cost

_Read-only feasibility spike, 2026-07-29._

Scoping of the plan to close the fuel-model efficiency boundary (boundary 1 of
*The two modeling boundaries* in `LogicalInduction/README.md`): define efficient
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

The spike surfaced two disclosure-prose defects, both since fixed: the model card's
claim that Mathlib exposes no poly-time machine class (it exposes one with no attached
theory — a materially different obstruction, now stated that way in
`Framework/Computable.lean`), and dangling citations of a retired planning note at
several disclosure sites (the substance survived in the adjacent docstrings; the
pointers are now self-contained).

---

# Stage 0 — decision: build an in-repo counted machine

_Decision recorded 2026-08-11, after the toolchain bump (Lean v4.31.0, current Mathlib
pin). Everything below was re-verified against the **installed** tree; the survey above
was written against the previous pin and its file paths have since moved._

## Re-survey of the installed Mathlib

**The files moved.** `Mathlib/Computability/TuringMachine.lean`, `TMComputable.lean`,
`TMConfig.lean`, `Tape.lean` and `TMToPartrec.lean` are now ten-line
`deprecated_module` shims. The content lives in
`Mathlib/Computability/TuringMachine/{Tape,Config,PostTuringMachine,StackTuringMachine,ToPartrec,Computable}.lean`,
plus a new top-level `Mathlib/Computability/StateTransition.lean`. Mathlib is also on
the module system now (`module` / `public import` / `@[expose] public section`); plain
`import` from this project still works.

**What changed that matters.** `StateTransition.lean` factored `eval`, `Reaches`,
`Reaches₁`, `Reaches₀`, `Respects`, `FRespects` out of the TM files, and it *does* carry a
timed vocabulary: `StateTransition.EvalsTo` (a structure with a `steps` field) and
`EvalsToInTime` (`steps_le_m`). This is more than the previous pin had, and it is worth
being precise about what it buys:

* `EvalsTo`/`EvalsToInTime` are **data, not `Prop`** — `Nonempty` wrappers are needed to
  use them in a class (Mathlib's own `proof_wanted` below does exactly that).
* Their entire theory is `refl` and `trans`. **Nothing connects them to `Respects`,
  `Reaches₁` or any simulation.** Their only consumers are `TM2OutputsInTime` and two
  `Inhabited` instances for the identity machine.
* So the structural fact from the survey above is unchanged: **every simulation in Mathlib
  (`TM1to0.tr_respects`, `TM1to1.tr_respects`, `TM0to1.tr_respects`, `TM2to1.tr_respects`,
  `ToPartrec.tr_respects`) is stated through `Respects`, whose `some` branch concludes
  `Reaches₁ = Relation.TransGen`** — a transitive closure with no length. The step count is
  destroyed at the statement, not merely unstated.

**`TM2ComputableInPolyTime` still has no theory** — and Mathlib now says so in its own
voice: `Mathlib/Computability/TuringMachine/Computable.lean` ends with

```
proof_wanted TM2ComputableInPolyTime.comp … : Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f))
```

i.e. *composition of poly-time TM-computable functions is an open item upstream*. That is
a direct confirmation of the Stage-1 deliverable's value: the first closure theorems for a
poly-time machine class are wanted and do not exist.

Two further observations on `FinTM2` as a candidate carrier: its `Γ : K → Type` carries
`Fintype` only for the **input** stack (`Γk₀Fin`), so "finite work alphabet" is not a field
but a fact needing an argument; and the enumeration obstruction from the survey above is
untouched (no `Encodable`, no Fin-normal form).

**CSlib / other timed developments: not reachable.** The dependency set is Foundation
(pinned by commit) plus a vendored `ProvabilityLogic` subset; Mathlib arrives transitively
through Foundation's manifest. `.lake/packages` contains no computability development
beyond Mathlib's, and no timed-computability library is present. Per the brief, no
dependency was added; this is a record of the state, not a rejection of CSlib on merits.

## The de-risk probe (executed)

`LogicalInduction/Construction/Machine/TimedRespectsProbe.lean` — 224 lines, compiles
clean under the current toolchain, not imported by `LogicalInduction.lean`. It carries a
step-count bound through the smallest Mathlib simulation, `Turing.TM1to0`:

* `ReachesIn f k a b` — counted reachability, with `reaches_iff_reachesIn` and
  `reaches₁_iff_reachesIn` pinning down exactly what `Reaches`/`Reaches₁` retain: the count
  always exists, and it is existentially quantified *inside the relation*, so no bound can
  be recovered downstream. This is the obstruction, stated as a theorem rather than as an
  impression.
* `TimedRespects f₁ f₂ tr cost` — the timed refinement Mathlib lacks, with the lemma that
  makes it worth having (`TimedRespects.reachesIn`: an `m`-step source run costs at most
  `m * cost` target steps).
* `TM1to0Timed.trCost` / `tr_timed` / `timedRespects_tm1to0` — `Turing.TM1to0.tr_respects`
  with a count, proved.

**The probe's finding: reuse of Mathlib's proof is zero, and the retrofit needs new
hypotheses.** `tr_timed` cannot be derived from `tr_respects` — the conclusion it needs is
strictly stronger than the one Mathlib proves — so the induction is redone in full: ~70
lines replacing Mathlib's 16. Beyond re-proving, the timed statement needed two things
Mathlib does not supply: a size measure on `TM1.Stmt` (`trCost`; there is none upstream)
and a `Fintype Λ` uniformity hypothesis, because `Turing.TM1.Supports` constrains *which*
labels are reachable and not *how many*, so it does not yield a uniform `Finset.sup` cost.

And `TM1to0` is the easy one. Its per-step cost is a syntactic measure of a single
statement. `TM1to1` re-encodes each symbol as a fixed-width block, so its costs scale with
the encoding width; `TM2to1` walks stack contents, so its costs scale with the stack sizes
— exactly the global size invariant this note already flagged as the single riskiest step,
now confirmed to be unavoidable rather than merely likely.

## Decision

**Build the in-repo counted machine.** The recommendation in "Verdict — staged plan" above
is confirmed, on the probe's evidence rather than on estimate:

1. The retrofit's cost is not "add a bound to existing lemmas" but "re-prove Mathlib's four
   simulation files with invariants their statements cannot express" — measured at 4.4×
   the original line count on the *easiest* file, with the ratio expected to worsen where
   the cost function stops being syntactic (`TM1to1`, `TM2to1`, `ToPartrec` are 320, 470
   and 1285 lines).
2. Nothing is forfeited by not landing on `TM2ComputableInPolyTime`: it has no theory to
   inherit, and Mathlib's own `proof_wanted` for its composition says the theory a
   consumer would want is not there.
3. A machine defined with counted steps from day one gets the timed statements by
   construction, with no `Respects`-shaped statement to route around.

**What the probe is kept for.** `ReachesIn` and `TimedRespects` are the reusable half of
the retrofit route and stay in the spike file as the Stage-0 record. If Stage 3's universal
simulator ever wants to *quote* Mathlib's machines, this is the interface it would need,
and the file states its cost honestly. The spike claims no paper node and is not part of
the build.

## What Stage 1 landed (2026-08-11)

`LogicalInduction/Construction/Machine/` — additive, imported by nothing in
`LogicalInduction.lean`, so outside the checked gates by construction. See the directory's
own module docstring for the model card. **No strength claim changes** anywhere in the
repo: per this note's staging, there is no partial credit before Stage 3 completes.
