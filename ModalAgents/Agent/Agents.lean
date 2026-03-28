/-
  Concrete modal agents from Barasz et al. 2014.

  - CooperateBot: always cooperates (⊤)
  - DefectBot:    always defects (⊥)
  - FairBot:      cooperates iff it can prove the opponent cooperates (□p)
  - PrudentBot:   cooperates iff it can prove the opponent cooperates
                  AND cannot prove the opponent defects (□p ⋏ ∼□∼p)

  Each agent is a Formula ℕ in the sense of LO.Modal.Formula.
-/

import ModalAgents.Agent.Basic
