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

-- Checked axiom/endpoint audit over the public surface (see README "Axioms").
-- A default target so `lake build` always runs it, but not part of the library.
@[default_target]
lean_lib AxiomAudit where
  srcDir := "."

-- Scratch verification of the Mathlib + Foundation substrate (not part of the
-- formalization proper; see Scratchpad.lean). Excluded from the default target.
lean_lib Scratchpad where
  srcDir := "."

-- Autoformalized (Harmonic Aristotle) sequent-calculus development of the GL fixed-point
-- theorem, discharging the former `glFixedPoint_thm42` axiom in `ModalAgents/FixedPoint.lean`.
-- Kernel-gated like the Brouwer construction: its interior has not had a human line-by-line
-- read-through. Its `Formula`-level notations are `scoped` so they do not collide with
-- Foundation's modal notation in `ModalAgents`.
lean_lib ProvabilityLogic where
  srcDir := "."
  globs := #[.submodules `ProvabilityLogic]
  leanOptions := #[⟨`autoImplicit, true⟩]

-- Fork of FormalizedFormalLogic/Foundation @ 83d98a36 with one patch class: three
-- `Matrix.*` decls that shadow Mathlib names (`map`, `forall_iff`, `exists_iff`) renamed
-- (`vecMap`, `vecForall_iff`, `vecExists_iff`) so Foundation co-imports with Mathlib
-- matrix/analysis theory (Bochner integration; EuclideanSpace via InnerProductSpace.PiL2,
-- needed by the Brouwer construction). The patch is **merged upstream**
-- (FormalizedFormalLogic/Foundation PR #835), so this fork carries no divergent
-- mathematics — it exists only to hold that rename on a base compatible with this
-- project's Lean toolchain (v4.28.0-rc1). Every upstream commit containing the rename is
-- on v4.31+, so switching to upstream is a Lean/Mathlib upgrade, not a dependency swap;
-- it is queued as its own project (see notes/consolidation.md).
require Foundation from git
  "https://github.com/A-M-Berns/Foundation" @ "aada66ef517064ce4fe025bb6c9072dacdf83991"
