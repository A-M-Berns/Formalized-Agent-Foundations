import FactoredSpaces.Soundness
import FactoredSpaces.LocalToGlobal

/-!
# Completeness of structural independence for events (Lemma 6.4, §C.3)

The paper's most technical contribution: if `A ⊥^P B | C` for every factorizing `P`,
then `H(A | C) ∩ H(B | C) = ∅`.  The route is through the *cohistory* — the set of
factors irrelevant to `A` given `C` (Definition C.6): mutual exclusion (Lemma C.9) is
strengthened by interpolation to `Cohistory(A|C) ∪ Cohistory(B|C) = I` (Lemma C.7), and
the cohistory is shown to be exactly the complement of the history (Lemma C.8) via the
progressive-replacement lemma (C.12), the independence properties of the cohistory
(C.18, C.19) and its disintegration of `C` (C.20).
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]

/-! ## Definition C.6: irrelevant factors and the cohistory -/

/-- The paper's `Δ^F_{C,i}(Ω)`: pairs `(P, Q)` of factorizing distributions with
`P(C) > 0`, `Q(C) > 0` that agree in every factor other than `i` (§C.3). -/
def pairsDifferingAt (C : Set (Pt Ω)) (i : I) : Set (Dist (Pt Ω) × Dist (Pt Ω)) :=
  {PQ | PQ.1 ∈ factorizingPos C ∧ PQ.2 ∈ factorizingPos C ∧
    ∀ j, j ≠ i → PQ.1.margAt j = PQ.2.margAt j}

/-- **`(P, Q)`-irrelevance.** For `(P, Q) ∈ Δ^F_{C,i}`, the factor `i` is
`(P, Q)`-irrelevant to `A` given `C` if `P(A | C) = Q(A | C)`.

Paper node: Definition C.6 (§C.3). -/
def PQIrrelevant (P Q : Dist (Pt Ω)) (A C : Set (Pt Ω)) : Prop :=
  P.condProb A C = Q.condProb A C

/-- **(Global) irrelevance.** The factor `i` is irrelevant to `A` given `C` if it is
`(P, Q)`-irrelevant for every `(P, Q) ∈ Δ^F_{C,i}(Ω)`.

Paper node: Definition C.6 (§C.3). -/
def Irrelevant (i : I) (A C : Set (Pt Ω)) : Prop :=
  ∀ P Q : Dist (Pt Ω), (P, Q) ∈ pairsDifferingAt C i → PQIrrelevant P Q A C

/-- **Cohistory.** `Cohistory(A | C)` is the set of factors irrelevant to `A` given `C`.

Paper node: Definition C.6 (§C.3). -/
noncomputable def cohistory (A C : Set (Pt Ω)) : Finset I := by
  classical
  exact Finset.univ.filter fun i => Irrelevant i A C

lemma mem_cohistory_iff {i : I} {A C : Set (Pt Ω)} : i ∈ cohistory A C ↔ Irrelevant i A C := by
  classical
  simp [cohistory]

/-! ## Lemma C.9: mutual exclusion -/

/-- **Mutual exclusion principle.** If `A ⊥^⊗ B | C` and `(P, Q) ∈ Δ^F_{C,i}`, then `i`
cannot be `(P, Q)`-relevant to both `A` and `B` given `C`.

Paper node: Lemma C.9 (§C.3). -/
theorem pqIrrelevant_or_of_condIndepAll {A B C : Set (Pt Ω)} (h : CondIndepAll A B C) {i : I}
    {P Q : Dist (Pt Ω)} (hPQ : (P, Q) ∈ pairsDifferingAt C i) :
    PQIrrelevant P Q A C ∨ PQIrrelevant P Q B C := by
  sorry

/-! ## Lemma C.7: the cohistories cover `I` -/

/-- **Completeness through the cohistory.** If `A ⊥^⊗ B | C` then
`Cohistory(A | C) ∪ Cohistory(B | C) = I`.

Paper node: Lemma C.7 (§C.3). -/
theorem cohistory_union_eq_univ_of_condIndepAll {A B C : Set (Pt Ω)} (h : CondIndepAll A B C) :
    cohistory A C ∪ cohistory B C = Finset.univ := by
  sorry

/-! ## Lemma C.12: progressive replacement of irrelevant factors -/

/-- **Progressive application of irrelevance.** If `P, Q ∈ Δ^F_C(Ω)` agree in every
factor relevant to `A` given `C`, then `P(A | C) = Q(A | C)`.

Paper node: Lemma C.12 (§C.3). -/
theorem condProb_eq_of_agree_on_relevant {A C : Set (Pt Ω)} {P Q : Dist (Pt Ω)}
    (hP : P ∈ factorizingPos C) (hQ : Q ∈ factorizingPos C)
    (h : ∀ j, ¬ Irrelevant j A C → P.margAt j = Q.margAt j) :
    P.condProb A C = Q.condProb A C := by
  sorry

/-! ## Lemmas C.18, C.19: independence properties of the cohistory -/

/-- **`A ⊥^⊗ U_J | C` for `J = Cohistory(A | C)`.**

Paper node: Lemma C.18 (§C.3). -/
theorem condIndepEventVar_proj_cohistory (A C : Set (Pt Ω)) (P : Dist (Pt Ω))
    (hP : Factorizes P) : CondIndepEventVar P A (proj (cohistory A C)) C := by
  sorry

/-- **`U_J ⊥^⊗ U_{I∖J} | C` for `J = Cohistory(A | C)`.**

Paper node: Lemma C.19 (§C.3). -/
theorem condIndepVarEvent_proj_cohistory (A C : Set (Pt Ω)) (P : Dist (Pt Ω))
    (hP : Factorizes P) :
    CondIndepVarEvent P (proj (cohistory A C)) (proj (cohistory A C)ᶜ) C := by
  sorry

/-! ## Lemma C.20: the cohistory disintegrates `C` -/

/-- **The cohistory disintegrates `C`.**  Needs a point of `Ω` — the paper takes "any
strictly positive distribution", which exists only when `Ω ≠ ∅` — but not more: when
`Ω = ∅` every `J` disintegrates every `C` trivially, so the statement is unconditional.

Paper node: Lemma C.20 (§C.3). -/
theorem disintegrates_cohistory (A C : Set (Pt Ω)) : Disintegrates (cohistory A C) C := by
  sorry

/-! ## Lemma C.8: the cohistory is the complement of the history -/

/-- **`Cohistory(A | C) = I ∖ H(A | C)`.**

Paper node: Lemma C.8 (§C.3). -/
theorem cohistory_eq_compl_eventHistory (A C : Set (Pt Ω)) :
    cohistory A C = (eventHistory A C)ᶜ := by
  sorry

/-! ## Lemma 6.4: completeness for events -/

/-- **Completeness for events.** If `A ⊥^P B | C` for all `P ∈ Δ^F(Ω)`, then
`H(A | C) ∩ H(B | C) = ∅`.

Paper node: Lemma 6.4 (§6.1). -/
theorem disjoint_eventHistory_of_condIndepAll {A B C : Set (Pt Ω)} (h : CondIndepAll A B C) :
    Disjoint (eventHistory A C) (eventHistory B C) := by
  sorry

end FactoredSpaces
