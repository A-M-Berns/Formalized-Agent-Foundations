import Lake
open Lake DSL

package agentFoundations where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Barasz where
  srcDir := "."

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "master"
