import ModalAgents.API

namespace APITests.ModalAgents

open LO LO.Modal
open scoped ModalAgent

/-- A client-defined rank-zero agent that asks for two nested proofs of cooperation. -/
def cautiousBot : ModalAgent :=
  ModalAgent.mkRank0 (□□(.atom 0 : Modal.Formula ℕ))

example : cautiousBot.formula = □□(.atom 0 : Modal.Formula ℕ) := by simp [cautiousBot]
example : cautiousBot.arity = 0 := by simp [cautiousBot]
example : cautiousBot.rank = 0 := by simp [cautiousBot]

/-- PrudentBot's supported theorem composes into the usual no-exploitation statement. -/
example (Y : ModalAgent) : ¬ (Cooperates prudentBot Y ∧ Defects Y prudentBot) := by
  rintro ⟨hCoop, hDefect⟩
  exact hDefect (prudentBot_unexploitable Y hCoop)

example (Y : ModalAgent) : Defects defectBot Y :=
  (defectBot_provably_defects Y).defects

/-- Behavioral equivalences compose and transport every advertised behavior predicate. -/
example {X X' X'' Y Y' : ModalAgent} (h₁ : X ≈ X') (h₂ : X' ≈ X'')
    (hY : Y ≈ Y') : Cooperates X Y ↔ Cooperates X'' Y' :=
  (h₁.trans h₂).cooperates_iff hY

example {X X' Y Y' : ModalAgent} (hX : X ≈ X') (hY : Y ≈ Y') :
    Defects X Y ↔ Defects X' Y' :=
  hX.defects_iff hY

example {X X' Y Y' : ModalAgent} (hX : X ≈ X') (hY : Y ≈ Y') :
    ProvablyDefects X Y ↔ ProvablyDefects X' Y' :=
  hX.provablyDefects_iff hY

end APITests.ModalAgents
