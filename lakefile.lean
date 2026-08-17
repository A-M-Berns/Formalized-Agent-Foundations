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
