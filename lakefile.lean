import Lake
open Lake DSL

package agentFoundations where
  leanOptions := #[⟨`autoImplicit, false⟩]

lean_lib Barasz where
  srcDir := "."

lean_lib Critch where
  srcDir := "."

lean_lib AxiomAudit where
  srcDir := "."

@[default_target]
lean_lib AgentFoundations where
  srcDir := "."

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "c28942b7d9d0df41ee5b736602c3f27b8643532c"
