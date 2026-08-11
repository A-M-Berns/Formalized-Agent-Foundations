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
  `HaltsFrom.unique`, `RunsInTime.unique` — cite these; don't re-derive.
- Mathlib's open composition item, for surface comparisons:
  `proof_wanted TM2ComputableInPolyTime.comp` at
  `Mathlib/Computability/TuringMachine/Computable.lean:284` — over `FinTM2` with three
  `FinEncoding`s and a `Polynomial ℕ` clock, concluding `Nonempty (…)`.
  `MachinePolyEC.comp` is an analogue, not that statement; neither implies the other.

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
- `Function.update`-shaped phase lemmas fail to `rw` at a bundled machine's `Stack M.K`
  (instance mismatch: ambient `DecidableEq` vs `Machine.decEqK`). Use the pointwise
  `_val` forms (`xfer_run_val`, `dup_run_val`, and round-1's `emitTagged_run_val`/
  `pushOne_run_val`); do not introduce new update-shaped statements. (R1-F19)
- Pop-a-stack-to-empty is `pump src (fun _ => .nop) (fun _ => .nop)` — 3 steps/symbol,
  same induction shape as `xfer_run`.
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
  25 s; `lake build LogicalInduction.Construction.Machine` warm 8 s; full `lake build`
  incl. `AxiomAudit` from seeded cache 45 s at `LAKE_JOBS=2`. The full gate is cheap —
  run it rather than the module target alone.
- Doc comments on `example` are legal in this toolchain (a corrected wrong belief —
  don't refactor away from them on the assumption they error).
