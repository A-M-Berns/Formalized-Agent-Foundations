import Lake
open Lake DSL

package agentFoundations where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Barasz where
  srcDir := "."

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "83d98a36091ffd9e7220ffa0033b1fc9097f5ab9"
