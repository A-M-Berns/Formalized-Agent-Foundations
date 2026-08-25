import Lake
open Lake DSL

package agentFoundations where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib ModalAgents where
  srcDir := "."

@[default_target]
lean_lib LogicalInduction where
  srcDir := "."

@[default_target]
lean_lib CartesianFrames where
  srcDir := "."

@[default_target]
lean_lib FiniteFactoredSets where
  srcDir := "."

-- Condensation (Eisenstat, 2025), stated over the shared Shannon-information layer.
-- Globbed because the formalization is split across files that the aggregator
-- `Condensation.lean` re-exports; see `Condensation/notes/roadmap.md`.
@[default_target]
lean_lib Condensation where
  srcDir := "."
  -- `.andSubmodules`, not `.submodules`: the latter excludes the root module itself, which
  -- would leave the aggregator `Condensation.lean` (and its `dd:` glossary) unbuilt.
  globs := #[.andSubmodules `Condensation]

@[default_target]
lean_lib FactoredSpaces where
  srcDir := "."

-- Vendored Shannon-information substrate: the entropy import closure of
-- teorth/pfr @ 01c9b666945eaf73b3f7d8b20ffe003f8640e630 (Apache-2.0), 25 modules, kept at
-- upstream module paths so diffs against upstream stay readable. Two compatibility
-- patches, both recorded as diffs; no mathematics altered. This is dependency code, not a
-- paper this project formalizes — see `ShannonInformation/vendor/PROVENANCE.md`.
-- Do not edit these files: re-vendor with `ShannonInformation/vendor/vendor-pfr.sh`.
@[default_target]
lean_lib PFR where
  srcDir := "."
  globs := #[.submodules `PFR]

-- The FAF-facing consumer surface over that substrate. Paper-agnostic shared
-- infrastructure; downstream formalizations import `ShannonInformation.API` and should
-- never need to name a `PFR.*` module. See `ShannonInformation/README.md`.
@[default_target]
lean_lib ShannonInformation where
  srcDir := "."
  globs := #[.submodules `ShannonInformation]

-- Consumer-style smoke tests. Each paper test imports only its supported API module.
@[default_target]
lean_lib APITests where
  srcDir := "."

-- Checked axiom/endpoint audit over the public surface (see README "Axioms").
-- A default target so `lake build` always runs it, but not part of the library.
@[default_target]
lean_lib AxiomAudit where
  srcDir := "."

-- The counted-step machine (Stage 1) and the executable description bridge (Stage 3) of
-- the efficiency-model program. A default target so CI compiles it, but deliberately *not*
-- imported by `LogicalInduction.lean`: nothing here carries a paper node, and no strength
-- claim depends on it. `DescExec` is the only module in this repository that names a
-- `Complexity.*` declaration; its import surface is `…UTM.Internal.Interp`, a 5-file /
-- ~2.2k-line closure of the pinned fork, not the whole library.
@[default_target]
lean_lib MachineExec where
  srcDir := "."
  roots := #[`LogicalInduction.Construction.Machine]

-- Scratch verification of the Mathlib + Foundation substrate (not part of the
-- formalization proper; see Scratchpad.lean). Excluded from the default target.
lean_lib Scratchpad where
  srcDir := "."

-- Upstream Foundation, pinned by commit. The Matrix-rename patch this project once
-- carried on a fork (PR #835: `vecMap`/`vecForall_iff`/`vecExists_iff`, avoiding Mathlib
-- name clashes that blocked co-importing matrix/analysis theory) is included upstream
-- as of v4.31; the fork is retired.
--
-- The pin is the last upstream commit that still contains `Foundation.Modal` (removed
-- upstream in #852 in favor of the separate FormalizedFormalLogic/ModalLogic repo).
-- It sits in the four-day window (2026-07-18 → 2026-07-22) that has *both* the Matrix
-- rename (#835, merged 07-18 — without it Foundation cannot co-import with Mathlib's
-- matrix/analysis theory) *and* `Foundation.Modal`. `ModalAgents` is stated over
-- `Foundation.Modal`, so moving past this pin means migrating it onto the ModalLogic
-- repo — a scoped follow-up, not part of routine bumping. Mathlib and all other pins
-- are transitive through Foundation's manifest; keep `lean-toolchain` matched to
-- Foundation's.
-- Pinned Lean-4.31 compatibility fork of SamuelSchlesinger/complexitylib (Apache-2.0),
-- the complexity-theory substrate for the machine-efficiency recalibration of `dd:fuel`
-- (see `LogicalInduction/notes/complexitylib-adoption.md`).
--
-- A *compatibility pin*, not a conceptual fork. `faf/v4.31` is upstream `b673821` plus
-- ten commits, every one of them either a mechanical port or purely additive; no
-- mathematical statement, definition or proof of upstream's is altered:
--
--   * a 36-line port to this project's Lean/Mathlib pin (upstream is on 4.30), plus a
--     later port of `Subroutines/Counter` in the same style;
--   * `utmTM_simulates_computer` and `TM.exists_singleTape_computesInTime`, which expose
--     *arbitrary function output* rather than only a decision cell — strictly weaker
--     projections of theorems upstream already proves;
--   * `exists_desc_computesInTime_polynomial`, a finite description for every
--     polynomial-time function;
--   * generic unary-register arithmetic and control flow: `subIntoTM`, `flagNonzeroTM`,
--     `guardTM`, `ltFlagTM`, and exact machine implementations of `Nat.pair` /
--     `Nat.unpair` with correctness and polynomial runtime bounds.
--
-- Nothing carries a FAF-specific or `Nat.Partrec.Code` name; all of it is upstreamable and
-- meant to be upstreamed. The fork retires into a plain upstream `require` once upstream
-- reaches this toolchain.
--
-- Required rather than vendored: the useful upstream slice is ~35k lines — 3.4× this
-- repository's largest vendored body — while the port is 36 mechanical lines that a
-- rebase carries forward. Vendoring would re-pay that port inside FAF on every toolchain
-- bump and degrade the diff-against-upstream story each time. See the adoption note §5.
--
-- FAF's own import surface is far narrower than the fork. Exactly two modules may name a
-- `Complexity.*` declaration, both under `Construction/Machine/`:
--   * `DescExec` imports `…UTM.Internal.Interp` (a 5-file / ~2.2k-line closure);
--   * `EvalnCompiler` imports `…Registers.Pairing`, the unary-register arithmetic layer.
-- Nothing else in this repository may, and neither is imported by `LogicalInduction.lean`
-- — the same containment discipline `PFR/` ↔ `ShannonInformation.API` follows.
require complexitylib from git
  "https://github.com/A-M-Berns/complexitylib" @ "6c6a06138038032135df207415205c896d63867a"

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "41d20b5158e9331e9b8dd86e16dbf488cc688bdb"

-- Vendored subset of FormalizedFormalLogic/ProvabilityLogic @ 7ed4a427 (2026-07-27,
-- the last upstream commit in CI lockstep with the Foundation pin above): the
-- sequent-calculus + Solovay development supplying the GL fixed-point theorem
-- (`ModalAgents/FixedPoint.lean` bridge) and the arithmetical soundness of GL
-- (`ModalAgents/Cooperation.lean`). Vendored rather than required as a package for one
-- reason: upstream declares its `Formula` connective notations globally at precedences
-- that capture the parse of Foundation's modal notation wherever the two are
-- co-imported (upstream never co-imports them; we must). The patch class is exactly
-- that: the clashing notation declarations are made `scoped` plus matching
-- `open scoped Formula` lines — no mathematical divergence. Diff against the upstream
-- commit to audit.
lean_lib ProvabilityLogic where
  srcDir := "."
  globs := #[.submodules `ProvabilityLogic]
  leanOptions := #[⟨`autoImplicit, true⟩]
