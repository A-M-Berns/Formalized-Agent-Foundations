import FactoredSpaces.Probability

/-!
# Soundness of structural independence for events (Lemma 6.3, §C.1)

If `H(A | C) ∩ H(B | C) = ∅` then `A ⊥^P B | C` for every `P` factorizing over `Ω`.
The set-theoretic half is `inter_eq_splice`; the measure half is Lemma C.15 applied
through `Factorizes.eq_outerCompl`.
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]

/-- **Soundness for events.** If `H(A | C) ∩ H(B | C) = ∅` then `A ⊥^P B | C` holds
for all `P ∈ Δ^F(Ω)`.

Paper node: Lemma 6.3 (§6.1). -/
theorem condIndep_of_disjoint_eventHistory {A B C : Set (Pt Ω)}
    (h : Disjoint (eventHistory A C) (eventHistory B C)) : CondIndepAll A B C := by
  sorry

end FactoredSpaces
