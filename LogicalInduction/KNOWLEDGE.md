# Formalization Knowledge — Logical Induction (arXiv:1609.03543)

Permanent, curated facts for harness agents working this formalization. Add an entry only
if a future fresh-context agent would act differently for knowing it. One bullet per fact,
newest last. Cross-reference finding IDs (RN-Fxx) where an entry originated from an audit.

**This file deliberately does not duplicate the repo's canonical documents.** Read them
first; entries here are deltas and harness-run curation only.

- Trust surface and strength claims: `LogicalInduction/README.md`
- Current statement-level audit: `notes/faithfulness-audit-2026-08-08.md`
- Efficiency-model boundary program (Stages 0–4): `notes/boundary-efficiency-model.md`
- Tactic-level gotcha log: `notes/consolidation.md` (wave-gotchas section)
- `dd:*` design-decision glossary and naming conventions: `LogicalInduction.lean`
- `dd:fuel` model card: `Framework/Computable.lean` ("### `dd:fuel` model card")

## Correspondence table

Paper notation ↔ Lean names. The full table for the finished surface is implicit in the
`Paper node:` docstring lines (checked two-way by `scripts/check-paper-nodes.sh`); listed
here are only the names harness agents for the efficiency-model program need.

| Paper (§/symbol) | Lean name | Notes |
|---|---|---|
| `def:ec` (efficiently computable trader) | `LogicalInduction.EfficientlyComputable` (`Framework/Criterion.lean`) | `dd:fuel` type-`(c)` substitution; symbol-metered composite of token/digit/RPN layers |
| — (no paper node; Stage-1 infrastructure) | `LogicalInduction.Counted.MachinePolyEC` (`Construction/Machine/Basic.lean`) | Counted-step stack machine class; NOT related to `EfficientlyComputable` by any theorem yet (Stage 2 in flight) |
| — | `LogicalInduction.PolyFueled` (`Framework/Computable.lean`) | Fuel meters the *value* `n`, not its bit length — any machine-side bridge must use value-scaled (unary-length) input encoding |

- `def:ec` is paper **§3.3** (`\label{sec:efc}`, tex:749; the keydef at tex:753). Earlier
  citations of it as "§2.2" are wrong — §2 is Notation, §3 is the Criterion. (R1-F10)
- `evaln_output_can_exceed_fuel`, `codeEvalBound`, `codeEvaln_result_le`,
  `codeEvalBound_poly` are **repo** lemmas (`Framework/Computable.lean:51`,
  `Framework/Emission.lean:21–76`), not Mathlib — grepping Mathlib for them finds nothing.
- `Trader` is a one-field structure, so `EfficientlyComputable`'s witness equality
  `clockedTrader lc tc clock = Tr` is interchangeable with the pointwise
  `∀ n, strategyOfTokens n (unRpn (undigitize (clockedTokens lc tc (clock n) n))) = Tr.strat n`.
  Machine-side bridges should consume the pointwise form.
- In that chain `clockedTokens` emits the *digit* stream (one digit per `tokenCode` call),
  not tokens. Clamping digits by `min · 4` is semantics-preserving: `undigitizeStep`
  branches only on `d < 4` and treats every `d ≥ 4` as a block terminator (verified by
  compiled replica, round-1 audit — do not re-raise).
- Counted-machine non-vacuity witnesses (round 1): `haltMachine`/`MachinePolyEC.id` at the
  end of `Machine/Basic.lean`; `eraseMachine`/`MachinePolyEC.const_nil` at the end of
  `Machine/Pairing.lean` (split by necessity: `eraseMachine.step` uses `xfer`, which lives
  downstream — don't consolidate into Basic without moving `pump`/`xfer` upstream). Both
  closure endpoints are exercised by `example`s composing/pairing the two.
- Determinism API (round 1, `Machine/Basic.lean`): `runFor_succ_of_halted`,
  `HaltsFrom.unique`, `RunsInTime.unique` — cite these; don't re-derive. Step-count
  uniqueness is derivable from this exported API in ~8 lines (verified compiling,
  round 2) — do not strengthen `HaltsFrom.unique`'s statement to get it.
- `pairMachine_runsInTime`'s clock `9|x| + 6|u| + t₁ + t₂ + 8` is exact with zero
  slack; adding/removing any phase forces editing the *statement*, not just the proof.
- Loop-relocation support verified by compiled probe (round 2): `HaltsFrom.relabel`
  accepts non-`none`-preserving injections; working pattern in the round-2 Lens-B
  report (match-defined injection + `rintro (_|⟨⟩) … <;> simp_all` injectivity).
- Mathlib's open composition item, for surface comparisons:
  `proof_wanted TM2ComputableInPolyTime.comp` at
  `Mathlib/Computability/TuringMachine/Computable.lean:284` — over `FinTM2` with three
  bare encoding functions `α → List αΓ` over `Fintype` alphabets (not `FinEncoding`s —
  corrected round 2) and a `Polynomial ℕ` clock evaluated at the encoded input length,
  concluding `Nonempty (…)`. `MachinePolyEC.comp` is an analogue, not that statement;
  neither implies the other. Mathlib's own note (same file, :26-31) says a TM2 step
  executes multiple fundamental actions — cite it for the "not a restriction of TM2"
  paragraph rather than re-deriving.

## Design decisions

- **Machine memory = private stack block over one shared I/O stack** (`Stack K = Option K`,
  `none` shared). Chosen after a fixed four-stack shared memory got composition but
  provably could not get pairing (nowhere to park a copy of the input across a
  sub-machine's run). The frame property comes from `Prog.relabel` precomposition, by
  construction, not by side condition. See `Machine/Basic.lean` module docstring.
- **Machine/ directory stays outside the default build graph until Stage 3 completes**
  (imported by nothing in `LogicalInduction.lean`; no paper nodes, no `AxiomAudit`
  endpoints). Harness gate for it: `lake build LogicalInduction.Construction.Machine`
  (the aggregator target), not `lake env lean` sweeps.
- `Cfg`'s stack field is named `store`, not `stacks`: Mathlib's `@[stacks]` attribute
  reserves the token.
- **Stage 2 works over one concrete alphabet** `Fin K` (K pinned at tranche 1), never
  alphabet-generic machine statements: `Machine Γ`/`RunsInTime` carry no `Fintype Γ`
  (only `MachinePolyEC` does), so a bare-`RunsInTime` statement over unconstrained `Γ`
  is content-free (a 5-state `Machine ℕ` computes `a :: rest ↦ h a :: rest` for arbitrary
  non-computable `h`), and statements with `pairWord`-shaped inputs are *refutable* at
  degenerate symbol choices (input word stops determining the arguments while runs are
  deterministic). Round-1 audit, compiling witnesses both ways. (R1-F05)
- **The loop combinator relocates the body's I/O stack** into a driver-private work stack
  via `Prog.relabel` (arbitrary injection — nothing hardwires `none → none`). Reason:
  `HaltsFrom.relabel`'s alignment hypothesis ranges over ALL of `Stack M.K` including
  `none`, so a body embedded the Stage-1 way sees (and may destroy) the whole shared
  stack; shared-stack `seq` chaining is for top-level single-entry phases only. (R1-F14)
- `MachinePolyEC.comp` takes the *inner* function first — opposite to `Computable.comp`
  but identical to Mathlib's `proof_wanted TM2ComputableInPolyTime.comp`. Deliberate;
  do not "fix".
- `MachinePolyEC.pair` deliberately carries no `s₀ ≠ s₁` (minimal hypotheses); the
  distinctness lives in `pairWord_injective`, which is otherwise unused — do not clean it
  up as dead. (R1-F01)
- `Machine.step` need not be a computable Lean definition for the class to be honest:
  with `Fintype Γ/K/Λ` the table is a finite object. Noncomputable choices (e.g.
  `Fintype.equivFin` orderings for cleanup sweeps) are harmless.
- **S1 speaks only on canonical `pairWord` inputs; `MachinePolyEC` quantifies over all
  words.** Every statement bridging the two carries an explicit input-normalization
  phase in the witness machine (symbol-indifferent pump counting `|w|`, then write the
  canonical input) — a phase with a cost in the clock, not a coercion. Invisible unless
  junk inputs are tested. (R1-F03)
- **Stage-2 alphabet ruling (round 2, closes tranche 1's open question): K = 9** —
  digits 0–4, `u := 5`, tags `s₀ := 6`/`s₁ := 7`, result marker `r := 8`, all five roles
  pairwise distinct so every separation is a `decide` fact. At the earlier illustrative
  K=8 table (`r = s₀ = 6`), `encodeResult (some v) = pairWord s₀ s₁ [] (unary v)`
  **by `rfl`** (compiled). A K=8 aliasing table (`s₁ = u = 5`, `s₀ = 7`, `r = 6`) is
  *viable* — `pairWord` needs only `s₀ ≠ s₁`, and the fuel block stays `s₀`-delimited —
  but rejected: slack is free, aliasing taxes every hand-written phase proof. The
  collision class is a construction hazard, not a statement refutation: `RunsInTime`
  forces exact outputs and `seq`/`pairMachine` hand exact inputs, so co-tenancy arises
  only inside hand-written `pump`/`xfer` phases of a single machine. (R2-F07, R2-F16)
- `encodeResult r u` (`none ↦ []`, `some v ↦ r :: replicate v u`) is injective with
  **no hypothesis relating `r` and `u`** — `none` vs `some 0` is separated by emptiness
  (compiled, even over `Fin 1`). `r ≠ u` matters only where an `encodeResult` word
  shares a stack with other unary material (`pair`/`comp` result plumbing). Do not cite
  none/some-0 separation as the reason for the symbol table. (R2-F08)
- **Instantiation is not transport**: a `∀ (Γ : Type) [Fintype Γ] (symbols…), hyps → …`
  statement instantiates directly at `Fin 9` by function application; `Γ ↪ Γ'` transport
  is needed only to move a *fixed*-alphabet theorem to a larger alphabet. "Prove
  generically, then specialize" is NOT blocked (compiled check, round 2) — the concrete
  pin is justified by the auto-bound pitfall and proof simplicity, not impossibility.
  The generic form remains viable for later upstreaming. (R2-F11)
- Determinism cuts both ways: given `RunsInTime.unique`, an
  `∃ w, RunsInTime M x w t ∧ P w` shape already pins `w` — never justify a functional
  `MachinePolyEC F` shape by a "lucky store" argument; its real content is totality
  over all words (the normalization burden). (R2-F12)
- **The converse inclusion (machine-poly ⟹ fuel-poly) is NOT refuted in the repo.**
  `RpnFreeze` records a *structural toolkit obstruction* (BigDigits closed under
  forward poly-carry recurrences, open under inverses) and itself says "in the intended
  complexity model the claim holds"; `not_polyFueled_two_pow` separates only
  `PolyFueled` by output size. Write "not attempted; structurally blocked in the fuel
  calculus's toolkit", never "false as stated"/"provably fails". The model card's
  "Lower calibration — OPEN" wording is authoritative. (R2-F13)
- The clamp lemma `undigitize ∘ map (min · 4) = undigitize` should be derived from
  `Framework/DigitArith.lean:934` `undigitize_eq_blockSplit` + `blockStep` (:875,
  branches only on `d < 4`) — a one-line `blockSplit` invariance, not a from-scratch
  induction. **Bridge.lean's import list is `Framework/Computable` +
  `Framework/DigitArith`** (transitively Criterion): Framework import order is
  `Criterion → Computable → DigitArith`, so importing Criterion alone reaches neither
  `PolyFueled` nor `blockSplit`. Bridge is created at tranche 6 and houses both S2 and
  S3. (R3-F08 ruling)
- `lakefile.lean:5` sets `autoImplicit := false` package-wide, but `lake env lean` does
  not apply package `leanOptions` — auto-implicit over-generalization is a *per-file
  checking* hazard only; `lake build` would catch it. The concrete-alphabet pin's
  ground (a) is a workflow argument, not a build-gate argument. (round 3)
- The memo's "with binary input encoding the inclusion would be false" is a real but
  unformalized complexity separation (value-poly vs poly-in-bit-length). Counterfactual
  about a rejected design — fine to state as motivation, never cite as a repo-supported
  fact.
- `Nat.pair` monotonicity for guard arithmetic: `Nat.left_le_pair`, `Nat.right_le_pair`,
  `Nat.pair_lt_pair_left`, `Nat.pair_lt_pair_right`, `Nat.add_le_pair`
  (`Mathlib/Data/Nat/Pairing.lean:102-148`) — cite, don't re-derive.
- `evaln`'s `prec` ladder never underflows and no intermediate guard fails once the
  top-level `guard (n ≤ k)` passes (`y ≤ Nat.pair a y ≤ k`;
  `Nat.pair a j + (y−j) ≤ Nat.pair a y`); the base `cf` guard is free too
  (`a ≤ Nat.pair a 0`). Live `none` sources in a `prec` simulation: fuel 0, top guard,
  `cf`/`cg` *internal* failure, and `cg`'s own guard on the assembled argument
  `Nat.pair a (Nat.pair y i)` (NOT bounded by `n` — genuinely fails). `rfind'`
  contrasts: its argument grows while fuel shrinks, so its guard failures are real.
  No underflow test phase is needed. (R3-F03, compiled twice independently)
- `MachineComputableTrader`'s totality-on-all-words costs proof work but no strength:
  a machine correct on `unary n` becomes total by prepending the symbol-indifferent
  normalization, same outputs, same polynomial. Matters when Stage 3 re-bases `thm:li`.
- Concrete `evaln` spot checks must write arguments as `Nat.pair a y` and use
  `simp only [evaln, Nat.unpair_pair, Nat.unpaired]` — numerals stick (`Nat.unpair 4`
  does not reduce; the `Nat.sqrt` whnf gotcha). (round 3)
- `IsPolyBounded` has `.of_le/.linear/.max/.add_one/.pair/.add/.comp` but **no
  two-function `.mul`** — `exists_clock_loop` needs one (~10 lines, `nlinarith`,
  verified compiling in scratch). The `IsPolyBounded f` conjunct of `PolyFueled` is
  derivable from the other two (via `codeEvaln_result_le` + `codeEvalBound_poly` +
  `.comp`) — S2's output-length constraint is satisfiable from the fuel bound alone.
- Loop input delivery drains its source (`xfer`): anything the driver retains across
  iterations (parked `a`, fuel word, counter) must be `dup`ed, never delivered by
  transfer. (round 3)
- `evaln`-fidelity nuance (round 2, re-derived independently): failure *order* within a
  level is irrelevant to extensional agreement — every branch is a total `Option`
  computation, so an upward `prec` loop need not mirror the downward recursion's
  detection order, only its value.
- `rg -r` is the *replace* flag, not recursive: `rg -rn "foo"` rewrites matches to `n`
  in displayed output (made `EfficientPrefixPatch.preserves_ec` display as a dangling
  name). Use `rg -n --fixed-strings` when auditing names.
- The clock normal form's `+ a` summand and `(n+1)` base are load-bearing for
  satisfiability at degenerate inputs: `|output| ≤ |input| + t` at `w = []` needs
  clock(0) ≥ output length, which `2a` provides and `a·n^k` would not. (round 2)
- S2 degenerate instantiations: `f = const 0` is discharged by `MachinePolyEC.const_nil`;
  `f = id` is NOT discharged by `MachinePolyEC.id` (`fun w => unary w.length ≠ id`,
  refuted at `[r]`) — it genuinely needs the normalization phase. (round 2)
- The interpretation chain's empty conventions cooperate: `undigitize [] = []`,
  `unRpn [] = []`, `deserializeTrades [] = some []`, `strategyOfTokens n [] = ⟨[], _⟩`,
  so `strategyOfTokens n (unRpn (undigitize [])) = Trader.zero.strat n` closes by `rfl`
  — any `∃ F, MachinePolyEC F ∧ interp = Tr.strat` class is inhabited by
  `⟨fun _ => [], MachinePolyEC.const_nil, fun _ => rfl⟩`. Degenerate: not evidence of
  content. (R2-F10) Also: `simp [strategyOfTokens, …]` gets stuck on the dependent
  `match hdecode :` — use bare `rfl`; and `native_decide` fails misleadingly on goals
  with free variables there.

## Intentional deviations from the paper

(See `LogicalInduction/README.md` for the two standing type-`(c)` substitutions:
`dd:fuel` and the propositional substrate. Auditors: entries there and here are not
findings unless the justification itself is wrong.)

## Disclosures (residual modeling substitutions)

(None recorded via this harness yet; the standing substitutions are documented in the
README and at their statement sites.)

## Paper errata

(None beyond what `notes/faithfulness-audit-2026-08-08.md` records.)

## Pitfalls

- `Nat.sqrt` whnf loops in deep `Primrec`/`PolyFueled` work — scoped
  `attribute [local irreducible] Nat.sqrt` (see `notes/consolidation.md`).
- `lake env lean` auto-binds implicits and elaborates against possibly stale upstream
  oleans — it is not a gate for signature changes; only `lake build` of the relevant
  target is.
- `Scratch*.lean` is gitignored via `.git/info/exclude`; use it for throwaway checks.
- Machine runs are deterministic and `HaltsFrom` pins a *halted* configuration, so the
  halting store — hence `RunsInTime`'s output — is unique (`HaltsFrom.unique`, landed
  round 1). Flip side: any family `∀ i, RunsInTime M (enc i) (out i) (t i)` is refutable
  whenever `enc` is non-injective and `out` isn't constant on its fibres.
- `Nat.Partrec.Code.evaln` does not reduce under `decide` (stuck `Decidable` instance);
  use `simp [evaln]` for concrete evaluations.
- `Function.update`-shaped phase lemmas at a concrete bundled machine block `rw`/`simp`
  but NOT `exact`/`refine`. Corrected mechanism (round-2 fix wave, `pp.explicit` probe):
  the `DecidableEq` instances agree on both sides — what diverges is the *type
  argument*, the goal's unreduced projection `Machine.K Γ (eraseMachine Γ)` vs the
  literal (`Unit`) in a hand-written update nest; defeq but not syntactically equal, so
  rewriting doesn't fire while term-mode application does. At composite memories
  written as type expressions (`Stack (pairK M₁ M₂)`) update forms work outright
  (`pairMachine_runsInTime` uses them). The `_val` forms are a rewriting convenience,
  not a correctness requirement — don't rewrite working update-shaped proofs.
  (R1-F19, R2-F03, corrected twice; trust this version.)
- Pop-a-stack-to-empty is `pump src (fun _ => .nop) (fun _ => .nop)` — 3 steps/symbol,
  same induction shape as `xfer_run`.
- `pump_halt` is only the ⇐ direction (`T src = [] → halts`); "pump halts *only when*
  its source is empty" is true of the definition but NOT a repo lemma. What carries the
  drained-stack arguments is `xfer_run`'s output store (sets `src := []`). If a proof
  needs the 'only when' direction, it must be proved first. (round 3)
- `MachinePolyEC` over `Fin 0` holds for every `f` (only word is `[]`, so `f = id`) —
  never cite an empty/one-symbol instantiation as evidence a machine statement has
  content. (round 3)
- `lint_paper_labels.py` requires every `theorem` to carry a paper label — Machine/
  results must stay `lemma` (no paper nodes there until Stage 3); promoting for
  emphasis breaks the gate.
- The 2026-07-29 survey section of `notes/boundary-efficiency-model.md` cites Mathlib
  facts from the *previous* pin (old line numbers, `FinEncoding`-based signature). Only
  the Stage-0 re-survey and later sections are current for Mathlib file/line facts.
- `codeEvalBound c k` is polynomial in the fuel *per fixed code* (degree grows with the
  code: `pair` doubles it); the `n ≤ k` guard caps every value fed onward, which is why
  exponential-growth codes return `none` rather than break the bound.
- `PolyEF` (`Framework/Computable.lean:258`) is a dead-end layer: consumed only by other
  `PolyEF` lemmas, never converted to any emission class. Consolidation candidate
  (out of Stage-2 scope; noted 2026-08-11).
- Machine-store definitions: prefer `match j with | none => a | some _ => b` over
  `fun j => if j = none then a else b` — the ite form defeats `simp` on the projections
  (observed: `(if none = none then [] else …) = []` left open as a split); the match form
  makes both projections `rfl`.
- `Option.none_bind` does not exist in the installed Mathlib; `none.bind f = none` is
  definitional — use `rfl` after rewriting.
- Build calibration for Machine-only changes (2026-08-11, this host): APFS `.lake` clone
  25 s; `lake build LogicalInduction.Construction.Machine` warm 8–30 s; full `lake
  build` incl. `AxiomAudit` 45 s *when the cache came from the same worktree* but
  several minutes when seeded from a different worktree (corrected round 3) — run the
  full gate, budget minutes, start it `run_in_background`.
- At a concrete finite alphabet, routing through `MachinePolyEC` buys **no anti-oracle
  guard**: `Machine` bundles `Fintype K/Λ`, so at `Fin 9` the table is finite regardless
  (compiled `Finite (Prog (Fin 9) …)`). The oracle argument applies only to
  unconstrained `Γ`. S3's shape rests on closure inheritance + totality. (R3-F06)
- Doc comments on `example` are legal in this toolchain (a corrected wrong belief —
  don't refactor away from them on the assumption they error).
