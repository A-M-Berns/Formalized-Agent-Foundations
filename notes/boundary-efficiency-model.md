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
  and pairing closure — the first nontrivial theorems about polynomial-time machine
  computability in Lean known to us (a priority claim not systematically checked;
  nothing rests on it), upstreamable to Mathlib.
* **Stage 2 (2–4 months):** establishes fuel⟹machine — every fuel-certified trader is
  genuinely machine-poly. This does **not** touch the model card's "Lower calibration —
  OPEN" item, which is the converse, which Stage 4 records as not-attempted (structural
  obstruction in the fuel calculus's toolkit; see the Stage-4 bullet); see the Stage-2
  memo §2.0. Every existing fuel certificate is preserved as the certification tool.
* **Stage 3 (4–9 months):** enumeration + universal simulator; `thm:li` at the
  machine class. No partial credit before the end of this stage.
* **Stage 4 — do not attempt:** the converse inclusion (machine-poly ⟹ fuel-poly) is
  **not attempted**: the digit calculus's inverse-operation non-closure is a structural
  toolkit obstruction (`Construction/Witnesses/RpnFreeze.lean`: `BigDigits` is closed
  under forward poly-carry digit recurrences and open under their inverses — `sqrt`,
  `unpair`, big-divisor `div` — whose carries exceed the poly-bounded-state requirement
  of `PolyFueled.prec`; that file also records that "in the intended complexity model the
  claim holds"), and **no class-level refutation of the converse exists in the repo**. The
  model card's "Lower calibration — OPEN" wording is authoritative: the direction is
  undischarged, not disproved. Flip side: a machine class would inhabit
  `EfficientPrefixPatch.preserves_ec`, which is uninhabited so far — no proof that it
  cannot be inhabited by fuel-model means is claimed.

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

`LogicalInduction/Construction/Machine/TimedRespectsProbe.lean` — 226 lines. It compiled
clean under Lean v4.31.0 at the Stage-0 re-survey, 2026-08-11; it is reachable from no
aggregator and therefore in no build target, and may rot — it is a record of the probe, not
a maintained artifact. It carries a step-count bound through the smallest Mathlib
simulation, `Turing.TM1to0`:

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
own module docstring for the model card. **No strength claim changes** anywhere in the repo:
per this note's staging, there is no partial credit before Stage 3 completes.

**The memory architecture, and why it is what it is.** A machine is a finite control over
stacks, one memory action per step. Each machine declares a finite *private* stack block
`Machine.K`; its stacks are `Stack K = Option K`, where `none` is an input/output stack that
**every** machine shares and `some k` is private scratch. A run starts with the input on the
shared stack and the private block empty, and ends with the output on the shared stack;
private stacks may be left dirty, since nothing that embeds the machine can see them.

The first attempt used a fixed four-stack memory shared by all machines, and it got
composition but could not get pairing: with every machine free to touch every stack, there
is nowhere to park a copy of the input across a sub-machine's run. The private-block design
fixes that structurally rather than by side condition. Machines are combined by *relabelling*
each into its own block of a larger index type (`Prog.relabel`); a relabelled program's
transition function is precomposed with the restriction of the stack tops to its own block,
so it cannot even read the other blocks, and `HaltsFrom.relabel` records both halves — the
run mirrors the original on its block, and everything off the block is untouched. That frame
property is what pairing needs, and it now holds by construction.

**Landed, all `sorry`-free.**

* `Machine/Basic.lean` — `Act`/`Cfg`/`Prog`/`stepCfg`/`runFor` over an arbitrary stack index;
  `HaltsFrom` (store-to-store, the form multi-phase constructions chain); `Machine`;
  `RunsInTime`; `MachinePolyEC`, whose clock is `fun n => a * (n + 1) ^ k + a`, the same
  normal form as `EfficientlyComputable`'s. Time bounds output size (one symbol per step).
* `Machine/Closure.lean` — `seqProg` and `HaltsFrom.seq` (additive time, one step of
  handover, and no data movement because the I/O stack is shared); `Prog.relabel` and the
  frame lemma; `seq`; `MachinePolyEC.comp`.
* `Machine/Pairing.lean` — one data-movement primitive `pump` (a three-beat loop: pop a
  symbol, then two symbol-dependent actions, the symbol carried in the control) with its
  three instantiations `xfer`, `dup`, `emitTagged`; the eight-phase pairing machine; and
  `MachinePolyEC.pair` for the self-delimiting encoding `pairWord`.

Both closure results are, to our knowledge, the first nontrivial theorems about
polynomial-time machine computability in Lean — a priority claim we have not systematically
checked, and nothing rests on it. The composition one is the machine-class **analogue** of
the statement Mathlib records as open: Mathlib's `proof_wanted
Turing.TM2ComputableInPolyTime.comp` is over `FinTM2` with its three `FinEncoding`s, and is
not implied by ours.

---

# Stage 2 — design memo (2026-08-11)

_The fuel⟹machine program, pinned before proving. Three statements, in the order they are
built and with the role each actually plays: an **engine** (S1, the fixed-code `evaln`
simulator), a **class-level milestone** (S2, `PolyFueled → MachinePolyEC`), and the
**trader-level headline** (S3, `EfficientlyComputable → MachineComputableTrader`).
Everything below was verified against the installed tree; consumer citations are to the
current files. Standing rule restated: nothing in Stage 2 changes any strength claim, README
text, model-card wording, or `AxiomAudit` endpoint — no partial credit before Stage 3.
The rule freezes **claims**, not **facts**: docstring sentences that report the current
staging state ("that inclusion is Stage 2 and is not started") are factual, and are updated
in the same commit that changes the fact they report. Leaving them stale would itself be a
misstatement._

## 2.0 What the deliverable must say, and what it must not

`EfficientlyComputable : Trader → Prop` and `MachinePolyEC : (List Γ → List Γ) → Prop` do
not share a type, so "the inclusion" needs a bridge object. The consumer survey fixes what
that object must be:

* Every downstream consumer of `EfficientlyComputable` uses **class membership only**.
  The enumeration half is definitional (`TraderProgram` *is* the witness quadruple;
  `enumeratedTrader_ec` is `rfl`-shaped; `TradingFirm.lean` consumes only the coverage
  fact `∃ j, enumeratedTrader j = Tr`). Nothing downstream inspects `evaln`.
* The fuel model's certificate-realizing lemmas (`ecTok_of_*`, `ecDigit_of_*`,
  `ec_of_raw*`, `EfficientlyComputable.ofTradeBlocks`, …) all *produce* class
  membership from fuel certificates. Stage 2 sits after them: it consumes the class's
  witness quadruple `(lengthCode, tokenCode, a, k)` and produces a machine.

So the headline deliverable is a **trader-level** machine class plus the inclusion into it
(S3), with a function-level simulation lemma as the engine (S1) and a class-level inclusion
as the milestone that exercises it (S2).

### The alphabet is pinned, concretely, once

An earlier draft of this memo stated S1 over an abstract `Γ` with abstract distinguished
symbols and no hypotheses on them. That is wrong, for two reasons that compile as
refutations plus a third that is a preference rather than an impossibility:

* **A bare-`RunsInTime` statement over unconstrained `Γ` is oracle-shaped.** The guard lives
  in exactly one place: `MachinePolyEC` carries `[Fintype Γ]`; `Machine` and `RunsInTime`
  carry **no** finiteness on `Γ` at all. So S1 — which is phrased with bare `RunsInTime`,
  not with `MachinePolyEC` — inherits no guard from its own vocabulary, and over an
  unconstrained `Γ` its machines may be oracles: a five-state `Machine ℕ` computes
  `a :: rest ↦ h a :: rest` for an arbitrary, in particular non-computable, `h` (compiled,
  round-2 audit). Pinning `Γ` concretely is what supplies the finiteness that S1's own
  statement vocabulary does not.
* **The symbol distinctness cannot be dropped.** With `u`, `r`, `s₀`, `s₁` unconstrained the
  conclusion is false, and the refutation runs entirely through `pairWord`'s collapse: at
  `Γ = Fin 1` — or, over any `Γ`, whenever `s₀ = s₁ = u` — the input word
  `pairWord s₀ s₁ (unary fuel) (unary n)` is a word of identical symbols of length
  `2·fuel + 1 + n`, hence a function of `2·fuel + n` alone, while `RunsInTime.unique` says
  one machine on one input has one output. Take `c = succ`: `(fuel, n) = (2, 0)` and
  `(1, 2)` give the same input word, but `evaln 2 succ 0 = some 1` and
  `evaln 1 succ 2 = none` (its guard `2 ≤ 0` fails), whose `encodeResult` images differ.
  Note what this refutation does *not* use: `encodeResult` is injective with **no**
  hypothesis on `r` or `u` whatsoever — `none ↦ []` and `some v ↦ r :: unary v` are
  separated by emptiness, and the `some`-fibres by length — and this holds even over
  `Fin 1` (compiled, round-2 audit). An earlier draft's "`encodeResult` needs `r ≠ u`" was
  simply wrong. Where `r`'s distinctness *is* needed is downstream of S1's statement: in
  phases where an `encodeResult` word shares a stack with other unary material — the result
  plumbing of the `pair` and `comp` constructions — the marker must be findable, and that
  is a property of the phase proofs, not of the encoding's injectivity.
* **Carrying the hypotheses generically would work; we choose not to.** A `∀`-quantified
  generic S1 with the distinctness hypotheses instantiates at the concrete alphabet by plain
  function application — no transport lemma is involved, and the "generically, then
  specialize" step does exist (compiled, round-2 audit; an earlier draft of this memo
  claimed it impossible, arguing from `Γ ↪ Γ'` transport, which is simply the wrong
  mechanism for instantiating a `∀`). The concrete pin is chosen on three grounds instead:
  (a) the auto-bound-implicit pitfall below — a generic statement that is *missing* a
  hypothesis elaborates silently into a more general, false claim; (b) `by decide` symbol
  separations are cheaper to use than hypotheses that must be carried through every phase
  lemma and every application; (c) proof simplicity throughout the stage. The generic
  `∀`-form remains viable, and is the likely shape for any later Mathlib upstreaming;
  alphabet-embedding transport lemmas are needed only to move *fixed*-alphabet theorems
  upward to a larger alphabet, which is a different job (§2.4 item 1).

**Resolution: the stage fixes one concrete alphabet up front, and every statement in it.**

```
abbrev Γ_LI := Fin 9
```

**The pinned alphabet size is `K = 9`**, with all five roles at pairwise distinct concrete
values:

| symbol | value | role |
|---|---|---|
| digits `0–4` | `0–4` | base-4 digit material plus the block terminator; digit `d` sits at value `d`, so the interpretation chain's `Fin.val` is the identity on digits (§2.1) |
| `u` | `5` | the unary mark |
| `s₀` | `6` | `pairWord`'s block terminator |
| `s₁` | `7` | `pairWord`'s per-symbol tag |
| `r` | `8` | the result marker of `encodeResult` |

Every separation the stage needs (`s₀ ≠ s₁`, `r ≠ u`, `r ∉ {s₀, s₁}`, digits disjoint from
all four) is then a `by decide` fact about `Fin 9` literals, and no phase lemma carries a
distinctness hypothesis.

Why this and not the earlier draft's illustrative `K = 8` table (`s₀ := 6 = r`, `s₁ := 7`):
at that table `encodeResult (some v) = pairWord s₀ s₁ [] (unary v)` holds **by `rfl`**
(compiled, round-2 audit) — a result word is literally a `pairWord` of an empty first
component, so any phase holding both shapes in one stack cannot tell them apart by their
leading symbol. That collision is what motivates the extra slack, and it is a fact about the
old table rather than a hypothetical.

A second, genuinely viable `K = 8` option was considered and rejected: alias `s₁ = u = 5`,
`s₀ := 7`, `r := 6`. It is sound — `pairWord` needs only `s₀ ≠ s₁`, and with `s₁ = u` the
fuel block reads as a run of `5`s that is still `s₀`-delimited, while `r` stays distinct from
both. It is rejected because the slack is free (one more `Fin` value costs nothing anywhere)
whereas the aliasing taxes every hand-written phase proof, which would have to re-establish
by hand, at each site, that a `5` on top of a stack is being read in the role the phase
intends.

Note that this is a **choice, not a forcing**: an earlier draft claimed that a phase holding
a `pairWord`-tagged word and an `encodeResult` word in one stack would *force* the tags
disjoint from `r` and hence `K = 9`. It would not — the aliasing option above shows `K = 8`
survives such a phase. `K = 9` is pinned for proof economy. With this ruling **tranche 1 no
longer owns an open symbol question**; it owns only the mechanical job of writing the table
down. What the memo commits to beyond the table is the design:

* one concrete `Γ_LI = Fin 9`, the values as tabled above;
* every designated symbol a named **concrete value**, so that `s₀ ≠ s₁`, `u ≠ r`, … are
  `by decide` facts and never hypotheses;
* **every S1–S3 statement over this one alphabet**: no alphabet-generic statements
  anywhere in the plan, and no alphabet transport anywhere in the plan.

The "no free type variables" clause is not fastidiousness. `lake env lean` auto-binds
unbound identifiers as implicit type variables — this repo's standing gotcha (gotcha log in
`notes/consolidation.md`) — so a statement that *should* have failed to elaborate for want
of a symbol or a `Fintype` instance instead elaborates silently into a strictly more
general, and false, claim, which the per-file check will happily accept. A concrete alphabet
removes that failure mode at the source rather than relying on review to catch it.

### The three statements

**(S1) The engine — the fixed-code `evaln` simulator.** Over `Γ_LI`, with the pinned
symbols `u`, `r`, `s₀`, `s₁`:

```
lemma Code.machinePolyEC (c : Nat.Partrec.Code) :
    ∃ (M : Machine Γ_LI) (a k : ℕ), ∀ fuel n : ℕ,
      RunsInTime M (pairWord s₀ s₁ (unary fuel) (unary n))
        (encodeResult (Nat.Partrec.Code.evaln fuel c n))
        (a * ((pairWord s₀ s₁ (unary fuel) (unary n)).length + 1) ^ k + a)
```

with `unary m := List.replicate m u`, `encodeResult none := []`,
`encodeResult (some v) := r :: unary v` (the marker separates `some 0` from `none`).
The conclusion is **extensional equality with `evaln`, including every `none` case**
(fuel `0`, guard failures, sub-computation failures). That is the spec; a simulator
that is only right on `some` has simulated something else, and the audit lens for this
stage should attack exactly that.

**(S2) The class-level milestone — `PolyFueled ⟹ MachinePolyEC`.**

```
lemma PolyFueled.machinePolyEC {c : Nat.Partrec.Code} {f : ℕ → ℕ}
    (h : PolyFueled c f) : MachinePolyEC (fun w : List Γ_LI => unary (f w.length))
```

Input convention: any word of length `n` denotes the day/value `n` (`MachinePolyEC` requires
a *total* function on words; `w.length` is the canonical total reading, with `unary n` the
canonical input). Two things the assembly must supply beyond S1, both easy to miss:

*Input normalization is a phase, not a coercion.* S1 speaks **only** on the canonical input
`pairWord s₀ s₁ (unary fuel) (unary n)`, while `MachinePolyEC` quantifies over **all** words
`w : List Γ_LI` — including words full of `r`s, mixed digits, or nothing at all. So the S2
witness machine opens with a normalization phase: pop `w` symbol by symbol *regardless of
what the symbols are*, pushing one `u` per symbol onto a private stack (a symbol-indifferent
`pump`, i.e. both symbol-dependent actions do the same thing), which computes `unary |w|`;
then write the canonical S1 input `pairWord s₀ s₁ (unary (B |w|)) (unary |w|)` onto the
shared stack. Its cost is linear in `|w|` plus the cost of writing the clock word, and it
enters the S2 clock as its own summand. It is an explicit phase of the S2 assembly and of
the tranche-6 plan.

*Fuel monotonicity is cited, not re-derived.* The bound `b` bundled in `PolyFueled c f` need
not be the polynomial the machine finds convenient to run; the machine runs at a polynomial
**majorant** `B ≥ b` and the answer must be unchanged. The bridge already exists on both
sides and is not to be re-derived: `Fueled.mono` (`Framework/Computable.lean:67`) transports
a certificate along `∀ n, b n ≤ B n`, and it is nothing but Mathlib's
`Nat.Partrec.Code.evaln_mono` (`Mathlib/Computability/PartrecCode.lean:612`) applied
pointwise — so `Fueled.mono` is the citation at the certificate level and `evaln_mono` the
one wherever the S1 simulation is confronted with a raised fuel word directly.

Proof shape, then: normalize the input, write the clock word at `B`, S1, strip the result
marker. `IsPolyBounded f` keeps the output length polynomial.

**S2 is a milestone, not an interface.** An earlier draft billed S2 as "the consumer-facing
inclusion". It is not: consumers consume *trader-level* class membership only (the survey
above), and S3's proof reuses **S1 directly**, at the trader's two codes, rather than
routing through S2's word-length convention. S2 is still worth landing — it is the first
statement in the repo relating the fuel calculus to a machine class, and it exercises the
whole engine end to end on a small target — but it is a stepping stone, and the memo should
not have implied a consumer for it that does not exist.

**(S3) The trader-level headline.** A new definition (placement below):

```
def MachineComputableTrader (Tr : Trader) : Prop :=
    ∃ F : List Γ_LI → List Γ_LI, MachinePolyEC F ∧
      ∀ n : ℕ, strategyOfTokens n (unRpn (undigitize ((F (unary n)).map Fin.val))) = Tr.strat n
```

The two conjuncts *are* the design, and the reasons for this shape over the earlier
`∃ w, RunsInTime M (unary n) w … ∧ interpret w = Tr.strat n` are three, none of them a
strengthening of what is asserted about a single input:

1. **It inherits the model's guard.** Routing through `MachinePolyEC` — rather than
   re-quantifying over a machine and a clock in place — carries the `[Fintype Γ_LI]`
   instance that `RunsInTime` does not (see the first bullet of "The alphabet is pinned"),
   so the definition cannot be satisfied by an oracle-shaped machine.
2. **It inherits the Stage-1 closure theory.** `MachinePolyEC.comp` and `MachinePolyEC.pair`
   apply to `F` directly, with no re-proof; a bespoke machine-and-clock existential would
   have to re-derive both.
3. **`F` is total on all words** — this is the real content of the choice, and it is not
   free. `MachinePolyEC F` constrains the machine at *every* input, while the earlier shape
   constrains it only at the canonical `unary n`. The price is the input-normalization phase
   (§2.0, and the standing risk bullet in §2.5): junk inputs must be given a defined,
   in-clock behaviour rather than being outside the statement.

What the shape does **not** buy is disambiguation of "the" output at a canonical input: the
earlier shape's `∃ w` was never satisfiable by a "lucky" store, because runs are
deterministic and `RunsInTime.unique` (`Machine/Basic.lean`) already pins `w` as a function
of the machine and the input. An earlier draft of this memo argued for the new shape on
exactly that ground; the argument was self-refuting, since it cited the determinism lemma
that makes the old shape unambiguous too. The three reasons above are the real ones.

The inclusion `EfficientlyComputable Tr → MachineComputableTrader Tr` supplies `F` on the
canonical inputs by the concrete emitted word

```
F (unary n) = (clockedTokens lengthCode tokenCode (clock n) n).map (fun d => (⟨min d 4, by omega⟩ : Γ_LI))
```

— and, as in S2, `F` is total on all words via the same normalization phase, reading an
arbitrary `w` as the day `|w|`. The `min d 4` clamp is semantics-preserving by design of
`undigitize`: `undigitizeStep` accumulates `d < 4` and treats **every** `d ≥ 4` as a block
terminator, so clamping changes nothing the interpretation chain can see
(`undigitize ∘ map (min · 4) = undigitize` — a lemma of the tranche plan; audited: verified
by compiled replica). The digit values `0–4` sit at values `0–4` of `Γ_LI` precisely so that
`Fin.val` on the emitted word is the identity on digits. The day is unary on the input
stack, so `MachinePolyEC`'s length-polynomial clock at `|unary n| = n` is exactly the fuel
model's (and the paper's) day-polynomial clock.

**Non-vacuity of `MachineComputableTrader`: already had, and degenerate — do not bill it as
evidence.** The class is inhabited the moment it is defined, by the do-nothing trader, and
the witness is one line:

```
⟨fun _ => [], MachinePolyEC.const_nil, fun _ => rfl⟩
```

(compiled, round-2 audit). It goes through because the interpretation chain's conventions on
the empty word compose to the zero strategy: the erasing machine's output is `[]`,
`undigitize []` is empty, and `strategyOfTokens n` of that is the zero strategy, which is
exactly `Tr.strat n` for the do-nothing trader — every step is `rfl`. This inhabitant is
worth writing down (a definition inhabited by nothing is a definition that may be quietly
unsatisfiable), and worth flagging just as loudly: **it is degenerate**. Every witness
constructible today reads as the zero strategy, because the only machines available are the
Stage-1 non-vacuity witnesses. The class's real non-vacuity is **S3 itself, applied to a
nontrivial trader** — the first witness carrying content is the first exploiting trader
pushed through the inclusion. Tranche 7 must present it that way; the `rfl` inhabitant is
never to be offered as evidence that the bridge says something.

### Where S3 lives

`MachineComputableTrader` and its inclusion go in a **new file**
`LogicalInduction/Construction/Machine/Bridge.lean`, importing `Framework/Criterion` (for
`Trader`, `EfficientlyComputable`, and the interpretation chain `strategyOfTokens ∘ unRpn ∘
undigitize`) and the Machine core. Not in `Basic.lean`, and not in any of the existing three:
the directory's upstreamability invariant — a self-contained counted-machine development
that could be offered to Mathlib — is scoped to `Basic`/`Closure`/`Pairing`, and pulling an
LI `Framework` import into any of them would destroy it for all of them. `Bridge.lean` is
documented at its head as the **LI-facing, deliberately non-upstreamable boundary** of the
directory, and is added to the `Machine.lean` aggregator, so the existing gate
(`lake build LogicalInduction.Construction.Machine`) covers it with no new gate.

**`Bridge.lean` carries no `Paper node:` line during Stage 2** — recorded here as the plan,
so that it is a deliberate deferral and not an omission an auditor has to discover.
`MachineComputableTrader` is a machine-class rendering of the paper's `def:ec` and would be
the natural carrier of that label; but a paper node is a strength claim (the two-way check
`scripts/check-paper-nodes.sh` reads it as "this is the formalization's rendering of that
paper object"), and this note's staging rule is that no strength claim moves before Stage 3.
While `EfficientlyComputable` is the class `thm:li` is proved over, `def:ec`'s node stays
there. The annotation moves to `MachineComputableTrader`, if it moves at all, in Stage 3,
together with the rest of the strength claims.

### What the deliverable must NOT say

The `dd:fuel` model card's *"Lower calibration — OPEN"* item is the **converse** direction
(paper-machine-e.c. ⟹ `EfficientlyComputable`), which Stage 4 records as **not attempted**
(a structural obstruction in the fuel calculus's toolkit, not a refutation; see the Stage-4
bullet). Landing Stage 2 closes nothing in that paragraph and licenses no model-card edit. What
Stage 2 buys is: every constructed exploiting trader in the property tail, certified in the
fuel calculus, is thereby a genuine machine-poly trader — the direction the property tail
consumes. The claim upgrade happens only when Stage 3 re-bases `thm:li` on the machine
class.

## 2.1 Representation of naturals: unary values, symbol-level streams

**Unary input is forced by the fuel model.** `PolyFueled` meters the *value*: `Fueled c f b`
with `b` polynomial in the numeric input `n`. A machine reading base-`b` digits of `n` has
input length `Θ(log n)`, so "poly in input length" would mean `poly(log n)` time — a
strictly smaller class, and the inclusion would be **false** (fuel-poly permits `Θ(n)`-value
work). Unary input makes value-poly and length-poly coincide. That argument is the whole
justification, and it is ours: it comes from what `PolyFueled` measures.

The paper is *consistent with* the choice but is not its authority, and an earlier draft of
this memo cited it as if it were. `def:ec` (§3.3 "Efficient Computability", `sec:efc`;
`notes/1609.03543v5-main.tex` line 749, the `keydef` at line 753) requires "runtime
polynomial in $n$ **(i.e. in the length of $n$ written in unary)**" — the parenthetical
fixes how the *runtime bound* is measured, it does not prescribe an input encoding. Reading
it as a prescription overclaims; reading it as compatible with unary day input is right, and
is all the memo needs.

**Every value the simulator manipulates is unary-representable.** Inside a run of
`evaln fuel c n`: the guard `n ≤ k` keeps every value that is *fed onward* below the
fuel; terminal outputs can exceed the fuel (`evaln_output_can_exceed_fuel`) but are
bounded by `codeEvalBound c fuel` (`codeEvaln_result_le` + `codeEvalBound_poly`,
`Framework/Emission.lean`) — polynomial in the fuel with degree depending on `c`. So
all intermediate values have polynomial unary length, and every arithmetic step on them
at value scale is polynomial-time.

**The exponential-token trap (why S3 emits symbols, not values).** Reassembled tokens
after `undigitize` are **not** value-bounded: a `tokenCode` may emit `clock n` many
base-4 digits of one block, denoting a token of value `≈ 4^{clock n}` — and this is a
feature, not an edge case (deep sentence codes are exactly what the digit layer exists
to admit; cf. the `PolySentenceCodes` lesson that whole-value metering silently lowers
a strength tier). Therefore the Stage-2 machine must never materialize a *token* value
in unary. S3's emitted word is a per-symbol image of the raw digit stream — one output
symbol per simulated `tokenCode` call, each call's *output value* being an `evaln`
output and hence poly-bounded — and all block reassembly stays on the consumer side of
the statement, in the interpretation chain `undigitize ∘ map Fin.val`. Base-4 digit
material appears only at this interface (which is why `Γ_LI`'s values `0–4` are the digit
symbols); the simulator's internals are unary throughout.

## 2.2 Simulation route: per-constructor structural induction

**Decision: prove S1 by structural induction on the eight constructors of
`Nat.Partrec.Code`, one machine construction per constructor, chained store-to-store
with `HaltsFrom`.** The rejected alternative is a universal clocked interpreter machine
(one machine reading an encoded code from a stack).

For the induction: (1) no code encoding or Fin-normal form is needed — that is Stage
3's separate problem, and the 2026-07-29 survey already isolated it as fiddly; (2) each
constructor case is a separately auditable certificate, matching the round structure of
this repo's process; (3) the combinators the induction forces (iteration, branching) are
exactly the toolkit Stage 3's universal interpreter will consume — nothing is thrown away;
(4) the fuel calculus itself was built per-constructor
(`codeEvalnNat_pair_polyFueled` / `_comp_` / `_prec_` / `_rfind_` culminating in
`codeEvalnNat_polyFueled`, `Framework/Emission.lean` 382–729), so the machine-side
induction has a proven structural precedent in-repo to mirror, invariant for invariant.

Against, accepted: the per-code time polynomial has **degree depending on `c`** (nested
`prec` multiplies: the call tree of `evaln fuel c n` for fixed `c` is of size
`fuel^{O(depth c)}`). This is exactly the fixed-code concession the original survey made
("a uniform bound in `|c|` needs memoisation, but the per-trader form only needs a
fixed code"), and `MachinePolyEC`'s `(a, k)` are per-machine existentials, so the
statement absorbs it. **Boundary for Stage 3:** the universal machine cannot be built
by re-running this induction at a universal code; it needs the memoised/shared-work
cost model from the start.

### The fidelity spec: Mathlib's `evaln` fuel discipline, verbatim

Verified against the installed `Mathlib/Computability/PartrecCode.lean` (`evaln`, :568):

* `evaln 0 c n = none`, unconditionally.
* At fuel `k + 1`, **every** constructor first checks `guard (n ≤ k)` on the *current
  argument*.
* `pair`/`comp` pass the same fuel `k + 1` to both children.
* `prec cf cg` at fuel `k + 1`, with `n` unpaired as `(a, y)`, is
  `n.casesOn (evaln (k+1) cf a) fun y => …`. Read the two branches separately, because
  they behave differently:
  - **base branch** (`y = 0`): `cf` runs at the **same-level** fuel `k + 1` of this
    unfolding — *not* at a decremented fuel — and on the argument `a = (unpair n).1`,
    *not* on `n`. Both halves of that are easy to get wrong in a way that agrees with
    `evaln` on `some` and disagrees on `none`.
  - **step branch** (`y + 1`): the self-call is `evaln k (prec cf cg) (Nat.pair a y)` — fuel
    decremented — and then the step code runs as `evaln (k+1) cg (Nat.pair a (Nat.pair y i))`
    at the undecremented fuel.
* `rfind' cf` at fuel `k + 1` runs `cf` at `k + 1` and recurses on `Nat.pair a (m + 1)` at
  fuel `k`.

The simulator must reproduce the guards and decrements bit-for-bit. In particular the
`prec` machine iterates *upward* from the base case while `evaln` recurses *downward*
from the top; the upward loop must fail exactly when the downward recursion would have.
Writing the descent out: the level-`j` unfolding (`0 ≤ j ≤ y`) runs at fuel
`k + 1 − (y − j)`, guards its own argument `Nat.pair a j` against that fuel minus one, and
bottoms out at level `0` with fuel `k + 1 − y`. If `y > k`, the ladder underflows before
reaching the base and the whole call is `none` — the machine's fuel-counter stack must
produce that too, from an underflow test, not from the top-level fuel. This is the single
largest fidelity risk of the stage (see §2.5).

### Per-constructor plan

* `zero`, `succ`: guard-compare (unary), emit.
* `left`, `right`: `Nat.unpair` at value scale — §2.3.
* `pair cf cg`: park a copy of the input (Stage-1 pairing-machine pattern), run both
  simulators, then compute `Nat.pair u v` in unary (`if u < v then v*v + u else
  u*u + u + v`; unary multiplication by repeated addition, `O(value²)` steps).
* `comp cf cg`: `seq` of the two simulators, same fuel word, result-marker plumbing
  between them (`cg` fails ⟹ whole fails).
* `prec cf cg`: unpair `n` into `(a, y)`; descend the fuel ladder to the bottom level
  `k + 1 − y` (failing on underflow); **run `cf`'s simulator there — at fuel `k + 1 − y`, on
  the argument `a`** — and only then start the upward `cg` iteration. The base run is a
  scheduled phase in its own right, before the loop, not the loop's zeroth iteration: it
  runs a *different* sub-simulator at a *different* argument from every `cg` step. The
  upward part is then the loop combinator (§2.4): `y` iterations, iteration `j` running
  `cg`'s simulator on `Nat.pair a (Nat.pair (j−1) i_{j−1})` at fuel `k + 1 − y + j`, with the
  level-`j` guard on `Nat.pair a j`, plus the unary bookkeeping that assembles the next
  argument.
* `rfind' cf`: the loop combinator; at most `fuel` iterations, argument second
  component incremented and fuel decremented per iteration, zero-test on `cf`'s output.

## 2.3 The inverse-operation ceiling, cleared forward

Stage 4's converse is not attempted because the digit calculus (`PolyFueled.prec`'s
poly-bounded-state requirement) does not close under inverse operations
(`sqrt`, `unpair`) whose carries exceed the bounded-state budget — a toolkit obstruction,
not a refutation of the converse (Stage-4 bullet, "Verdict"). The forward direction
needs `unpair` too — `left`, `right`, and the argument decomposition of `prec`/`rfind'`
all unpair their input. The verification that this is no obstacle machine-side:

* `unpair m` at value scale needs `s = Nat.sqrt m`, obtainable by candidate search:
  try `r = 0, 1, 2, …`, comparing `r · r ≤ m` with unary multiplication and comparison
  — `O(m^{3/2})` machine steps, a polynomial in the unary input length. Then
  `unpair m = if m - s*s < s then (m - s*s, s) else (s, m - s*s - s)` by unary
  subtraction and comparison.
* Nothing here touches digit carries at all: pseudo-polynomial search is an honest
  polynomial at value scale. The ceiling is one-directional because the machine may
  spend value-scale time freely, while `PolyFueled.prec` cannot even represent the
  carry propagation of the inverse operations within poly-bounded state.
* Proof-order consequence: the `left` case (with the `sqrt`-by-search machine) is
  scheduled as the *first* nontrivial constructor tranche — it is the de-risk showcase
  for the whole route. (Repo gotcha applies: scoped
  `attribute [local irreducible] Nat.sqrt` if any proof touches `Nat.sqrt` reduction.)

## 2.4 Stage-1 leftovers, and the one new combinator

1. **Alphabet-embedding closure — wanted, but off Stage 2's critical path.** Transport of
   `RunsInTime`/`MachinePolyEC` along an injection `Γ ↪ Γ'`: a machine over `Γ` is a machine
   over `Γ'` computing the embedded function on embedded words. This was previously listed
   as a Stage-2 prerequisite because S1/S2 were alphabet-generic and S3 fixed a small
   alphabet; that plan is retired (§2.0) — **Stage 2 now works in one pinned alphabet
   throughout, so it needs no transport at all** (and, per §2.0, transport was never the
   mechanism that would have connected a generic statement to a concrete one: instantiating a
   `∀` is function application). It remains a genuine
   Stage-1 leftover, worth having for the upstreamable core (a widening-transport lemma is
   what any external consumer of `MachinePolyEC` will want first), and it mirrors
   `Prog.relabel` — which embeds *stacks* — on the symbol side. It is simply no longer
   scheduled ahead of anything.
2. **A counted iteration combinator** (`loop`) — the genuinely new closure, and the
   only new control structure of the stage. Run an embedded sub-machine repeatedly
   under a unary counter stack: initialize, run body, decrement, repeat until the
   counter empties or a flag symbol fires; time = per-iteration bounds summed plus
   per-iteration overhead. `prec` and `rfind'` are its two instantiations. Stage-1's
   `pump` is the degenerate one-symbol-body case; `loop` embeds an arbitrary machine
   per iteration, so it composes `Prog.relabel`'s frame property with a counter
   discipline — the same architecture pairing used, plus recursion.

   **Shared-stack alignment, and why the loop relocates its body.** The halting convention
   lets a machine leave its private stacks dirty, justified in `Machine/Basic.lean` by
   "each embedded machine is started once, on a block that is empty because the embedding
   gives it a fresh one." A loop breaks that invariant twice over, and the second half is
   the one the earlier sketch missed. First: iteration `j + 1` restarts the body on the
   private block iteration `j` dirtied, while the body's specification (`RunsInTime`, and
   S1 through it) speaks only from the canonical initial memory. Second — and this is about
   the *shared* stack, not the private ones — `HaltsFrom.relabel`'s alignment hypothesis
   ranges over **all** of `Stack M.K`, `none` included, and every Stage-1 embedding maps
   `none → none`. So a body embedded that way demands that the *composite's* I/O stack hold
   exactly this iteration's input and nothing else: fine for a phase that runs once at top
   level, wrong inside a loop, where the shared stack is also where the driver keeps the
   material it is iterating over.

   Resolution: **the loop embeds the body under an injection that sends the body's `none`
   to a driver-private work stack.** Nothing hardwires `none → none` — `Prog.relabel` takes
   an arbitrary injection of stack indices, and `HaltsFrom.relabel` only asks that the
   composite store agree with the body's along it — so the body can be made to run entirely
   inside the driver's private block, on a relocated I/O stack the driver owns, leaving the
   composite's shared stack alone. Per-iteration cost then has four parts, all bounded:

   * (i) **input delivery — a *double* transfer through a staging stack.** `xfer`
     **reverses** what it moves: `xfer_run` (`Machine/Pairing.lean`) lands
     `l.reverse ++ T dst` on the destination, because `pump` pops the source and pushes the
     destination. A single `xfer` into the body's relocated I/O stack would therefore hand
     the body its input backwards — a bug that no type catches and that the body's
     specification (stated on the canonical input word) would silently be false of. So
     delivery is two transfers: driver stack → a driver-private **staging** stack →
     the body's relocated I/O stack, the second reversal undoing the first. Cost `3 + 3 = 6`
     steps per symbol of the iteration's input;
   * (ii) the **body run** — its own `RunsInTime` bound, now applied at a memory that
     genuinely is the body's canonical initial one;
   * (iii) **result extraction — the same double transfer, back.** The body's output sits on
     the relocated I/O stack; moving it to where the driver wants it is again two `xfer`s
     through a staging stack, cost `6` steps per output symbol. Extraction could in principle
     be a single reversing transfer wherever the consuming phase is happy to read the result
     backwards, but the plan takes the double transfer **uniformly**: one convention (every
     word is stored in its canonical order, everywhere) is worth more than the saved `3`
     steps per symbol, and per-phase orientation conventions are exactly the kind of
     bookkeeping that produces off-by-one-reversal proof debt;
   * (iv) **cleanup sweep — of the body's private stacks only.** Iteration `j + 1` must find
     the body's private block empty. Pop-to-empty is expressible with the Stage-1 primitive
     as `pump src nop nop`, 3 steps per symbol. The bound is `HaltsFrom.length_le`, which
     gives `|T' k| ≤ |T k| + t` — *dirt plus `t`*, not `t` — so a `≤ t` sweep bound is
     available only for stacks that start the iteration **empty**. That is exactly the body's
     private stacks: empty on the first iteration because the embedding gives a fresh block,
     and empty on every later one because the previous iteration's sweep left them so. The
     sweep therefore costs at most `3 ·` the body's step bound `·` the (finite, per-machine)
     number of stacks in its block.

     **The relocated I/O stack is not in that list, and needs no sweep at all.** It is
     emptied by construction: `pump` halts only when its source is empty (`pump_halt` fires
     on `T src = []`, and `xfer_run` returns the source at `[]`), so the extraction transfer
     of (iii) drains it as a side effect of running. The staging stacks of (i) and (iii) are
     drained the same way. Listing the relocated stack for sweeping — as an earlier sketch
     did — would not merely be wasted work: it would need a dirt bound on a stack that does
     *not* start empty, which `HaltsFrom.length_le` does not supply.

   The clock lemma sums those four: `exists_clock_loop` bounds
   `Σ_{i<y} (6·|inᵢ| + bound(body) + 6·|outᵢ| + 3·|K_body|·bound(body))` uniformly by
   `y ·` the per-iteration maximum and folds it into the `a·(len+1)^k + a` normal form,
   extending the `exists_clock_comp`/`exists_clock_pair` pattern. The output lengths `|outᵢ|`
   are themselves bounded by the body's clock through `RunsInTime.length_output_le`, so
   nothing in the sum is unbounded. The alternative — strengthening the
   body's spec to arbitrary initial private stores — is false in general (a body may read
   leftover garbage) and is not attempted.

   **Consequence for the architecture, worth stating flatly.** Stage-1's `seq` chaining is
   cheap precisely because the I/O stack is shared and no data moves; that is available for
   **top-level phases only** — phases that run once, in order, in the composite's own I/O
   stack. **Anything iterated runs relocated**, and pays the overhead above: `6` steps per
   symbol in, `6` per symbol out, plus the private-block sweep. The loop is not `seq` under a
   counter, and the Stage-2 cost estimates must be read with the relocation overhead
   included.
3. **Branching**: dispatch on a read symbol is finite-control (one state per branch);
   no new combinator planned. **Phase-bundle factoring: not adopted.** The plan's
   justification threshold: adopt only if a third construction repeats the
   copy-run-copy phase pattern of `Pairing.lean` at comparable length — revisit after
   the `pair cf cg` tranche, and record the decision either way.

## 2.5 Risk register

* **`prec` fuel-mirroring** (top risk): upward loop vs downward recursion — the failure
  cases must agree exactly, at every level's guard and fuel, and the base run of `cf` must
  land at fuel `k + 1 − y` on argument `a` rather than anywhere convenient. Mitigation:
  state the loop-invariant of the `prec` machine directly against
  `evaln (k+1-(y-j)) (prec cf cg) (Nat.pair a j)`, not against a paraphrase; audit lens told
  to attack the `none` cases (ladder underflow when `y > k`, guard failures at intermediate
  levels, and `cf` failing in the base).
* **Time bookkeeping through nested loops**: per-iteration bounds vary as values grow;
  bound every iteration uniformly by `codeEvalBound c fuel` before summing, accepting
  the degree loss (absorbed by the per-code `(a, k)`), and remembering that each iteration
  also pays relocation overhead (§2.4).
* **Guard arithmetic off-by-ones**: `guard (n ≤ k)` at fuel `k + 1`; the unary
  comparison machine must implement `≤` against `fuel − 1`. Regression `example`s at
  small concrete fuels (0, 1, 2) for every constructor case, checking agreement with
  `evaln` by `decide`-free evaluation, are part of each tranche's gate.
* **Output-size vs clock**: `RunsInTime` forces `|output| ≤ |input| + t`, so S1's clock
  must dominate `codeEvalBound c fuel` (the `encodeResult` length). The clock normal
  form absorbs it, but the constructor cases must thread it explicitly.
* **Normalization forgotten**: S1's canonical-input convention meeting `MachinePolyEC`'s
  "all words" quantifier is a silent hole if the normalization phase (§2.0) is skipped —
  the S2/S3 statements would then be unprovable at exactly the junk inputs nobody tests.
  Flagged for the tranche-6/7 gates.
* **Whole-value regression at the interface**: any future strengthening of S3 that
  makes the machine *reassemble* tokens (rather than emit symbols) walks into the
  exponential-token trap of §2.1. The statement shape is the guard; flagged for
  auditors as a standing attack surface.

## 2.6 Proof tranches (each round-audited before the next)

1. **Write the alphabet down** — `Γ_LI := Fin 9` and the symbol table of §2.0 (digits `0–4`
   at values `0–4`, `u := 5`, `s₀ := 6`, `s₁ := 7`, `r := 8`) as concrete values with their
   distinctness `by decide`. No open symbol question is left for this tranche to settle:
   §2.0's ruling is the decision, and the `r`-vs-tag question it used to carry is closed.
   Then the word/number toolkit over it: `unary`, `encodeResult`, unary arithmetic machines
   (add, subtract, compare, multiply, guard), I/O plumbing over `pairWord`, and the
   input-normalization phase (length-count + canonical-input writer).
2. `loop` combinator with `exists_clock_loop`, including the relocated-body embedding, the
   order-preserving double transfers in and out, and the cleanup sweep of the body's private
   block (§2.4).
3. Base constructors `zero`/`succ`/`left`/`right` — including the `sqrt`-by-search
   machine (de-risk showcase, §2.3).
4. `pair`, `comp` cases; phase-bundle factoring decision recorded here.
5. `prec`, `rfind'` cases (the fidelity core: base run, ladder, guards — §2.2, §2.5).
6. Assembly: S1 by induction; S2, with its normalization phase and the
   `evaln_mono`/`Fueled.mono` majorant step.
7. New file `Machine/Bridge.lean` (added to the `Machine.lean` aggregator, no `Paper node:`
   line): `MachineComputableTrader`, the `min d 4` clamp lemma, S3; boundary-note update.
   Non-vacuity is presented as **S3 applied to a nontrivial trader**; the one-line `rfl`
   inhabitant of §2.0 may be recorded as a sanity check but never as the class's evidence.
   Still no strength-claim changes anywhere — Stage 3 gates those.

   **Docstring updates that land in the same commit as `Bridge.lean`**, because they are
   statements of fact that this tranche falsifies (the standing rule freezes claims, not
   facts — see the preamble):
   * `Construction/Machine.lean` (the aggregator): "no theorem relates `MachinePolyEC` to
     `LogicalInduction.EfficientlyComputable` — that inclusion is Stage 2 and is not
     started", and the surrounding "**This directory is not part of the formalization's
     trust surface**" sentence, which is no longer true of `Bridge.lean` in the same way
     once it imports `Framework/Criterion`;
   * `Construction/Machine/Basic.lean`, module docstring, "Relation to the rest of the
     repository": "Nothing here is bridged to `LogicalInduction.EfficientlyComputable` —
     that inclusion is Stage 2 of the plan and is not started";
   * `MachinePolyEC`'s own docstring in `Basic.lean`: "It is *not* related to it by any
     theorem — the inclusion is Stage 2 of `notes/boundary-efficiency-model.md` and is not
     started."

   Each becomes a statement of what S3 relates and at what strength, with the "no strength
   claim moves before Stage 3" sentence left standing everywhere it appears.
