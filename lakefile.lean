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

-- Fork of FormalizedFormalLogic/Foundation @ 83d98a36 with one patch class: three
-- `Matrix.*` decls that shadow Mathlib names (`map`, `forall_iff`, `exists_iff`) renamed
-- (`vecMap`, `vecForall_iff`, `vecExists_iff`) so Foundation co-imports with Mathlib
-- matrix/analysis theory (Bochner integration; EuclideanSpace via InnerProductSpace.PiL2,
-- needed by the Brouwer construction). Upstreamed as PR #835; see notes/next-session.md for current status.
require Foundation from git
  "https://github.com/A-M-Berns/Foundation" @ "aada66ef517064ce4fe025bb6c9072dacdf83991"
