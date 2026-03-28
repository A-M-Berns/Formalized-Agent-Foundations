import Lake
open Lake DSL

package modalAgents where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib ModalAgents where
  srcDir := "."

require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "master"
