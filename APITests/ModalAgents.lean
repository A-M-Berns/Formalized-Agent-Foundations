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

/-! ## The arithmetic layer (§4)

Client-side use of the agents-as-`PA`-formulas surface: the theory is a parameter, so a
client supplies it, and every result below is obtained by composing exported statements
rather than restating one. -/

section Arithmetic

open LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] [𝗣𝗔 ⪯ T]

/-- A client transports a behavioral-equivalence hypothesis through an arbitrary modal
agent — Theorem 4.8 used as the transport rule it is. -/
example {k : ℕ} {X Y Z : Agent} (hX : IsModalAgentOfRank T k X)
    (hYZ : BehaviorallyEquivalent T Y Z) : T ⊢ X.app Y 🡘 X.app Z :=
  modalAgent_isBehavioral hX Y Z hYZ

/-- CooperateBot is behavioral: the non-vacuity witness composed with Theorem 4.8. -/
example : IsBehavioral T (⊤ : Agent) :=
  modalAgent_isBehavioral cooperateBot_isModalAgentOfRank_zero

/-- A fact neither paper endpoint states on its own: no modal agent *is* CliqueBot. -/
example [Entailment.Consistent T] {k : ℕ} {X : Agent}
    (hX : IsModalAgentOfRank T k X) : X ≠ cliqueBot := by
  rintro rfl
  exact cliqueBot_not_modalAgent ⟨k, hX⟩

end Arithmetic

end APITests.ModalAgents
