/-
  Main cooperation theorems from Barasz et al. 2014.

  Key results to formalize:
  - FairBot cooperates with FairBot  (via Löb's theorem)
  - FairBot cooperates with PrudentBot
  - PrudentBot cooperates with PrudentBot
  - PrudentBot defects against DefectBot (unlike FairBot, which loops)

  The proofs use the Löb axiom □(□φ → φ) → □φ and fixed-point reasoning
  within GL.
-/

import ModalAgents.Agent.Agents
