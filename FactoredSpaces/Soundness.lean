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
  set J := eventHistory A C
  have hgen : Generates J (indic A) C := generates_history (indic A) C
  have hd : Disintegrates J C := hgen.2
  have hA : A ∩ C = splice J (A ∩ C) C := (generates_indic_iff_splice hd).mp hgen
  have hsub : eventHistory B C ⊆ Jᶜ := fun i hi =>
    Finset.mem_compl.mpr (Finset.disjoint_right.mp h hi)
  have hgenB : Generates Jᶜ (indic B) C :=
    (generates_iff_history_subset hd.compl).mpr hsub
  have hB : B ∩ C = splice J C (B ∩ C) := by
    have := (generates_indic_iff_splice hd.compl).mp hgenB
    rwa [splice_compl] at this
  have hAB : A ∩ B ∩ C = splice J (A ∩ C) (B ∩ C) := inter_eq_splice hA hB
  have hC : C = splice J C C := by
    have h' := hd
    rwa [Disintegrates, prodSplit_eq_splice] at h'
  intro P hPf
  have hOC := hPf.eq_outerCompl J
  have e1 : P.prob (A ∩ C) =
      (P.marg J).prob (projSet J (A ∩ C)) * (P.marg Jᶜ).prob (projSet Jᶜ C) := by
    conv_lhs => rw [hA, splice_eq_cyl_inter]
    exact Dist.prob_cyl_inter_cyl hOC _ _
  have e2 : P.prob (B ∩ C) =
      (P.marg J).prob (projSet J C) * (P.marg Jᶜ).prob (projSet Jᶜ (B ∩ C)) := by
    conv_lhs => rw [hB, splice_eq_cyl_inter]
    exact Dist.prob_cyl_inter_cyl hOC _ _
  have e3 : P.prob (A ∩ B ∩ C) =
      (P.marg J).prob (projSet J (A ∩ C)) * (P.marg Jᶜ).prob (projSet Jᶜ (B ∩ C)) := by
    conv_lhs => rw [hAB, splice_eq_cyl_inter]
    exact Dist.prob_cyl_inter_cyl hOC _ _
  have e4 : P.prob C =
      (P.marg J).prob (projSet J C) * (P.marg Jᶜ).prob (projSet Jᶜ C) := by
    conv_lhs => rw [hC, splice_eq_cyl_inter]
    exact Dist.prob_cyl_inter_cyl hOC _ _
  show P.prob (A ∩ C) * P.prob (B ∩ C) = P.prob (A ∩ B ∩ C) * P.prob C
  rw [e1, e2, e3, e4]; ring

end FactoredSpaces
