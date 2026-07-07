# Session plan — token-emission `def:ec` and the deep-trader unlock

Written 2026-07-07 by the outgoing session, for the next (possibly weaker-model) session.
Read `CLAUDE.md` and `PROGRESS.md` (especially OPEN RISK 4 **and its 2026-07-07 addendum**)
before starting. This file is the task list; those files are the law.

## 0. Context snapshot (verified 2026-07-07)

- Build green (2645 jobs); exactly two `sorry`s in the tree, both disclosed:
  `oscillation_exploitable` (`Properties/Convergence.lean:73`) and `LUV.expect_converges`
  (`Expectations.lean:86`).
- M3 status: provind (both forms), all three lc bullets, lex (both directions), con
  reduction — all proved axiom-clean. Remaining M3 nodes (`thm:con` trader, expectation
  family, `thm:nd`, Self-Trust) are **all** gated on OPEN RISK 4, per the sharpened
  analysis in the addendum (short version: under the current `def:ec`, `evaln` with poly
  fuel can only *output* poly-**value** naturals — O(log n) bits — so any trader whose
  day-`n` strategy needs a description of more than logarithmic size is excluded, no
  matter how it is encoded as a single number. `thm:con` needs a hysteresis state,
  `thm:nd` needs a purchase counter; both are size-Θ(n) features).
- Everything already proved stays valid; the issue is only that `IsLogicalInductor` is
  weaker than the paper's, so the *remaining* theorems don't follow from it.

## 1. Decision gate (Anson) — do not skip

Phase 2 changes the trust surface: it redefines `EfficientlyComputable`. **Get Anson's
explicit go-ahead before starting Phase 2** (he may have already given it in the kickoff
prompt — check). If declined or deferred, do only Phase 4.

Recommendation from the outgoing session: approve. The current def is unfaithful to the
paper on exactly the strategies M3 still needs; the fix below is the paper's poly-size
`def:ec` rendered honestly, and it strictly enlarges the e.c. class (old certs remain
true statements; they get re-proved against the new def mechanically).

## 2. The spec: token-indexed emission

**Why not "whole-value emission of a flatter encoding":** `evaln`'s every clause guards
its input by fuel (`guard (n ≤ k)`, see
`.lake/packages/mathlib/Mathlib/Computability/PartrecCode.lean:569` ff.), so for a fixed
code the output value is ≤ `(fuel+1)^(2^|c|)` — poly value, O(log n) bits. A size-Θ(n)
description has value 2^Θ(n) under *any* injective `List ℕ → ℕ` packing (Mathlib's list
encoding is itself `Nat.pair`-nested and exponentially wasteful). So the machine must
emit the description **one token at a time**.

### T1 — `EF.serialize` (postfix token stream) + roundtrip

```lean
def EF.serialize : EF → List ℕ
  | .price φ n   => [0, Encodable.encode φ, n]
  | .const q     => [1, Encodable.encode q]
  | .add a b     => a.serialize ++ b.serialize ++ [2]
  | .mul a b     => a.serialize ++ b.serialize ++ [3]
  | .max a b     => a.serialize ++ b.serialize ++ [4]
  | .safeRecip a => a.serialize ++ [5]
```

(Exact tag scheme is free — e.g. you may need `price` in postfix form too, or tags offset
so payload tokens can't be confused with tags; pick something and make the roundtrip
proof force correctness.) Write a stack-machine `deserialize : List ℕ → List EF → Option EF`
and prove the roundtrip. **Known technique:** the induction needs the strengthened form
`deserializeAux (e.serialize ++ rest) st = deserializeAux rest (e :: st)`; the naive
statement won't go through. Injectivity of `serialize` falls out — that's the honesty
requirement (the stream determines the feature).

### T2 — `Strategy` stream

Serialize `trades : List (EF × Sentence)` as the concatenation of
`e.serialize ++ [6, Encodable.encode φ]` per trade (tag 6 = trade terminator; adjust to
your tag scheme). Same roundtrip discipline.

### T3 — the new definition (additive, don't break the build)

```lean
def EfficientlyComputableTok (Tr : Trader) : Prop :=
  ∃ (c : Nat.Partrec.Code) (a k : ℕ),
    (∀ n, (serializeTrades (Tr.strat n).trades).length ≤ a * (n + 1) ^ k + a) ∧
    ∀ n i, i < (serializeTrades (Tr.strat n).trades).length →
      Nat.Partrec.Code.evaln (a * (n + 1) ^ k + a) c (Nat.pair n i)
        = some ((serializeTrades (Tr.strat n).trades).getD i 0)
```

Notes, all deliberate:
- The **length bound is a separate clause** — without it the def would admit
  super-poly-size strategies (per-token fuel in `pair n i` grows with `i`).
- Fuel is poly in `n` only; the guard `pair n i ≤ fuel` is satisfiable for `i ≤ poly n`,
  which the length clause guarantees is all we need.
- Token *values* are implicitly ≤ poly(n) by the evaln output ceiling. Consequence:
  `encode φ` and `encode q` ride along as **atomic tokens**, so sentences/constants of
  more than O(log n) code-value on day `n` are still excluded — a remaining, smaller,
  type-`(c)` disclosure (ledger it). All current M3 traders trade *fixed* sentences
  (constants absorbed into `a`), and `buySeq`'s varying `φₙ` already carries a
  `PolyFueled` hypothesis on `encode ∘ φ`, so nothing in scope is hurt. Formula-level
  sub-tokenization is a possible later refinement, not this session's job.
- For rationals that must *grow* with `n` (e.g. `2^-(n+1)` in weak-nd, Phase 3a): do NOT
  use `const (2^-(n+1))` — its `encode` is exponential-value. Build it structurally
  (an `n`-fold `mul` chain of `const (1/2)`), which is exactly what the new def is for.

### T4 — re-certification of the seven existing traders

Build one helper first, then everything is mechanical:

```lean
-- sketch: a "token template" = List (ℕ → ℕ) (each token a poly function of n),
-- with each entry PolyFueled; dispatch on i via a finite case-split code.
theorem ecTok_of_template ...
```

Then re-cert `buyDaily`, `sellDaily`, `priceTrader`, `buySeq`, `exclTr`, `eqTr`, `impTr`
(their day-`n` streams are fixed short templates with `n` and constant codes plugged in).
Existing infra to reuse: `PolyFueled` (`Computable.lean:172`), `PolyEF`
(`Computable.lean:225`), `ec_of_polyEF_seq` (`Computable.lean:272`); existing cert
proofs to imitate: `exclTr_ec` (`Properties/Coherence.lean:244`), `buySeq_ec`
(`Properties/ProvabilityInduction.lean:216`). If fuel accounting fights for more than a
couple of serious attempts on any one trader, `sorry` it with a TODO and report — do not
thrash.

### T5 — the switch (one commit)

Only when all seven re-certs are green: point `IsLogicalInductor`
(`Criterion.lean:435`) at the new def; rename old `EfficientlyComputable` →
`EfficientlyComputableVal` (keep it and its certs — they're true and documented);
rename `EfficientlyComputableTok` → `EfficientlyComputable`; update each property
theorem's cert argument (a one-lemma swap each); update the ledger rows (`def:ec` row:
new def, disclosures above; OPEN RISK 4: resolved-by-redefinition, atomic-token residue
noted). Build green before and after. Nothing gets deleted.

## 3. Stretch (only if Phase 2 is fully green) — first deep traders

Ordered easiest-math-first; each is the first real exercise of the new def. These are
*candidate approaches from the outgoing session — re-derive the math, don't transcribe it.*

- **3a. Weak non-dogmatism fragment** (new, honest fragment of `thm:nd`): under
  `[IsLogicalInductor]`, if every day has a plausible world satisfying `φ`
  (`∀ n, ∃ v, v.ConsistentWith (DP.D n) ∧ v.Holds φ`), then `∀ᶠ n, Pₙφ ≥ 2^-(n+2)`-ish.
  Trader: memoryless buy-signal `max(0, 1 − 2^(n+1)·Pₙφ)` with the power built as a
  mul-chain (size-Θ(n) — legal now). Spend per active day ≤ 2^-(n+1) → total ≤ 1 →
  BddBelow by −1 in *all* plausible worlds; if the price dips below the schedule i.o.,
  profit in the φ-worlds diverges. Needs a small new engine (BddBelow globally +
  divergence along a *family* of plausible worlds — neither existing engine at
  `Properties/Basic.lean:85`/`:122` matches exactly; follow `buyDaily_exploits`'s shape).
  Ledger as `thm:nd (weak fragment)`, kind `C`.
- **3b. Full `thm:nd`** (paper form, `main.tex:1528`): needs the budget-halving purchase
  counter as a size-Θ(n) EF and a continuity-respecting smoothing. Medium-hard.
- **3c. `thm:con` hysteresis trader** (`oscillation_exploitable`): the hard one — the
  banking-`b−a`-per-swing argument is genuine analysis. A session that lands only
  Phase 2 is a **success**; do not manufacture progress here. Rule 1 of CLAUDE.md
  applies with full force: no arithmetic stub may stand in for this trader, ever.

## 4. Fallback (if the decision gate says no, or Phase 2 blocks)

- Statements-only staging: state Self-Trust (`thm:cee`/`ceu`/`ccee`/`st` — mind the
  roadmap's naming caution: deference "cee" = paper `thm:ceu`) and full `thm:nd`,
  `sorry`-bodied, ledgered as `stmt`. Statements are trust surface: short,
  paper-faithful (check `notes/1609.03543v5-main.tex` labels), hypotheses minimal.
- M3-exit audit prep: a flat list of every top-level theorem statement + file:line for
  Anson's read-through, appended to `PROGRESS.md`.

## 5. Guardrails (operational; the failure modes this plan is designed against)

1. **Never invent a Mathlib/Foundation name.** `rg` the `.lake/packages` tree or
   `#check` before first use. Missing → `sorry` + `-- TODO(blueprint:LABEL): need <stmt>`.
2. **Green at every commit.** Additive-then-switch (T3–T5) exists precisely so the build
   is never red across a commit boundary. Small commits.
3. **Every new theorem ships with its ledger row in the same commit**, kind and
   provenance filled honestly at proof time.
4. **`#print axioms` every new theorem in-file** (copy the idiom from existing files).
5. **Do not touch:** `Construction/Brouwer.lean`'s interior (linter warnings included —
   leave them), `Barasz/`, `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, the
   Foundation pin. Never `lake update`. Never `import Mathlib` umbrella.
6. **Don't redefine limit vocabulary** — use `Asymptotics.lean` (`dd:asymp`).
7. **Stop-and-report is a success.** If a definition fights the type system or a fuel
   proof won't close after ~2 serious attempts, write up exactly what fails (imitate the
   `oscillation_exploitable` docstring) and move on.
8. Use the `lean4-theorem-proving` skill for build/repair workflow.
9. Iterate with `lake build LogicalInduction.<Module>` (single module), full `lake build`
   before each commit. If ProofWidgets "failed to reuse pre-built JS": run
   `cd .lake/packages/proofwidgets && lake build` once (see PROGRESS.md).
10. Commit messages: no AI co-authorship lines. Push to `origin` freely, nowhere else.
