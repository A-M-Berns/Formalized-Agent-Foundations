import Lake
open Lake DSL

package agentFoundations where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Barasz where
  srcDir := "."

@[default_target]
lean_lib LogicalInduction where
  srcDir := "."

-- Scratch verification of the Mathlib + Foundation substrate (not part of the
-- formalization proper; see Scratchpad.lean). Excluded from the default target.
lean_lib Scratchpad where
  srcDir := "."

-- Fork of FormalizedFormalLogic/Foundation @ 83d98a36 with one patch: `Matrix.map`
-- renamed to `Matrix.vecMap` so Foundation co-imports with Mathlib matrix/analysis
-- theory (Bochner integration, finite-dim analysis). See PROGRESS.md, OPEN RISK 1.
require Foundation from git
  "https://github.com/A-M-Berns/Foundation" @ "0939b51dd9d57b40b1f4048271e5cf7736a9e8de"
