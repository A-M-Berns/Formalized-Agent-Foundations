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

-- Safe Pareto Improvements for Delegated Game Playing (Oesterheld–Conitzer 2022). Globbed
-- like `Condensation`; the aggregator `SafeParetoImprovements.lean` carries the `dd:`
-- glossary. See `SafeParetoImprovements/notes/scoping.md`.
@[default_target]
lean_lib SafeParetoImprovements where
  srcDir := "."
  globs := #[.andSubmodules `SafeParetoImprovements]

-- Vendored Shannon-information substrate: the entropy import closure of
-- teorth/pfr @ 65691129be2d8ca3e164c0822d95a456b88ee259 (Apache-2.0), 27 modules, kept at
-- upstream module paths so diffs against upstream stay readable. Byte-identical to upstream:
-- no compatibility patches are carried. This is dependency code, not a paper this project
-- formalizes — see `ShannonInformation/vendor/PROVENANCE.md`.
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

-- Pinned Lean-4.34 compatibility branch of SamuelSchlesinger/complexitylib (Apache-2.0), the
-- complexity substrate for the machine reading of `def:ec`.
--
-- A *compatibility pin*, not a conceptual fork. `faf/v4.34` is upstream `175f412` plus a
-- two-file port to this toolchain and twelve purely additive commits, none of which alters a
-- mathematical statement, definition or proof of upstream's:
--
--   * `utmTM_simulates_computer` and `TM.exists_singleTape_computesInTime`, which expose
--     *arbitrary function output* rather than only a decision cell — strictly weaker
--     projections of theorems upstream already proves;
--   * `exists_desc_computesInTime_polynomial`, a finite description for every
--     polynomial-time function;
--   * generic unary-register arithmetic and control flow: `subIntoTM`, `flagNonzeroTM`,
--     `guardTM`, `ltFlagTM`, and exact machine implementations of `Nat.pair` /
--     `Nat.unpair` with correctness and polynomial runtime bounds;
--   * register-tuple plumbing — `regsWork` sub-windows (`regsWork_restrict`,
--     `regsWork_window`) and offset sub-tuples (`shiftEmb`), which let a machine written
--     against a small fixed tuple run at any offset of a larger register file.
--
-- Nothing carries a FAF-specific or `Nat.Partrec.Code` name; all of it is upstreamable and
-- meant to be upstreamed. The branch retires into a plain upstream `require` once the additive
-- commits land there. `scripts/pin_bump.py` tracks the branch head rather than upstream `dev`
-- for exactly this reason.
--
-- Required rather than vendored: the useful upstream slice is ~35k lines, while the port is a
-- handful of mechanical lines that a rebase carries forward. Vendoring would re-pay that port
-- inside FAF on every toolchain bump and degrade the diff-against-upstream story each time.
--
-- FAF's own import surface is far narrower than the branch. `Complexity.FP` is the
-- paper-facing reading of `def:ec` and so is named at the criterion itself
-- (`Framework/Criterion.lean`); the *deep* imports are exactly two:
--   * `Construction/Descriptions` imports `…UTM.Internal.Interp` (a 5-file /
--     ~2.2k-line closure);
--   * `Framework/Machine/EvalnCompiler` imports `…Registers.Pairing`, the unary-register
--     arithmetic layer.
-- Everything else naming a `Complexity.*` declaration reaches only `Classes/P/Defs` and
-- its immediate neighbours. The same containment discipline `PFR/` ↔
-- `ShannonInformation.API` follows.
require complexitylib from git
  "https://github.com/A-M-Berns/complexitylib" @ "d3013c36bd416cf62f68d1e411519bc158f6bfba"

-- Upstream Foundation, pinned by commit. The Matrix-rename patch this project once
-- carried on a fork (PR #835: `vecMap`/`vecForall_iff`/`vecExists_iff`, avoiding Mathlib
-- name clashes that blocked co-importing matrix/analysis theory) is included upstream
-- as of v4.31; the fork is retired.
--
-- The pin is tied to the ProvabilityLogic pin below, not chosen on its own: it is the
-- Foundation commit that ProvabilityLogic's own `lake-manifest.json` records at *its* pinned
-- commit, i.e. the Foundation that development was last tested against. Foundation's `master`
-- moves its syntax and bootstrapping namespaces between releases, and ProvabilityLogic follows
-- a few days later; pinning Foundation independently (at head) has broken the GL development
-- in exactly that window. So a bump moves ProvabilityLogic first and reads the Foundation rev
-- off its manifest — `scripts/pin_bump.py` does this. Keep `lean-toolchain` matched to
-- Foundation's.
require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "abd0cb9044dedc6bb1755871ee30724b8f3c1d12"

-- Upstream Gödel–Löb provability logic (FormalizedFormalLogic/ProvabilityLogic), pinned by
-- commit: `Formula`, `LogicGL` with finite Kripke completeness, the de Jongh–Sambin fixed-point
-- theorem (`LogicGL.fixpointTheorem`) and the arithmetical soundness of GL
-- (`LogicGL.arithmetical_soundness'`). `ModalAgents` is stated directly over its `LogicGL`,
-- so this is the substrate of that formalization the way Foundation is of LogicInduction's.
-- Only the modules ModalAgents imports are built (about forty of ninety-five). The package
-- also requires `Forgive`, the FFL axiom auditor, at the toolchain tag — the same pin
-- Foundation already carries, so it adds no dependency.
require ProvabilityLogic from git
  "https://github.com/FormalizedFormalLogic/ProvabilityLogic" @ "60c41f4e6b1914b5f24f498d47c2cb8c003160f6"

-- Game-theory substrate for `SafeParetoImprovements` (Oesterheld–Conitzer 2022):
-- `StrategicGame`, strict dominance, best response, Nash equilibrium, mixed strategies
-- and expected payoff, simultaneous-round IESDS. Pinned to a commit because the library
-- is young and its API moves; a bump is a deliberate act. Upstream pins an older Mathlib
-- than this repository — Lake takes the root's Mathlib, and the imported strategic-game
-- modules compile unmodified against it (probe of 2026-09-04, recorded in
-- `SafeParetoImprovements/notes/scoping.md` §2). Only the modules FAF imports are built.
-- The paper's set-based `Game` maps to `StrategicGame` through one bridge
-- (`SafeParetoImprovements/Game.lean`); paper-facing statements never name an EconCSLib
-- internal directly.
require EconCSLib from git
  "https://github.com/gametheoryinlean/EconCSLib" @ "cef01c709a7d238f076b45818f2ff2629518efe3"

-- Mathlib, pinned at the root and placed LAST on purpose. With no root `require mathlib`, Lake
-- inherits whichever Mathlib the first dependency above pins — EconCSLib's older one — and
-- `lake exe cache get` then refuses ("mismatched dependencies"). A root pin that comes last
-- makes Mathlib's own dependency versions take precedence over those inherited from the
-- packages above (Lake's documented rule), so the whole workspace resolves to one Mathlib: the
-- release tag matching `lean-toolchain`, which is also what Foundation and ProvabilityLogic pin.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5ed2965256430c3649e86755f9576b54eca72435"
