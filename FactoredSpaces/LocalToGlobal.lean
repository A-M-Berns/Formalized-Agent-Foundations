import FactoredSpaces.Probability
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The local-to-global principle (Lemma 6.5, Lemmas C.5 and C.10)

Interpolating two factorizing distributions factorwise, `R^λ = ⨂_i ((1−λ)Q_i + λP_i)`,
makes every event probability a polynomial in `λ` (Lemma C.5); positivity of `P(C)` is
preserved along the interpolation (Lemma C.10); and a conditional independence holding
on a Euclidean ε-ball of factorizing distributions holds on all of them (Lemma 6.5).
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]

/-- The interpolation `R^λ = ⨂_{i∈I} R^λ_i`, `R^λ_i = (1−λ)Q_i + λP_i`, between the
factorwise families `Q` and `P` (Lemmas C.5, C.10, 6.5, C.7). -/
noncomputable def interp (Q P : ∀ i, Dist (Ω i)) (t : unitInterval) : Dist (Pt Ω) :=
  Dist.prod fun i => Dist.mix t (Q i) (P i)

lemma interp_zero (Q P : ∀ i, Dist (Ω i)) : interp Q P 0 = Dist.prod Q := by
  simp [interp, Dist.mix_zero]

lemma interp_one (Q P : ∀ i, Dist (Ω i)) : interp Q P 1 = Dist.prod P := by
  simp [interp, Dist.mix_one]

lemma factorizes_interp (Q P : ∀ i, Dist (Ω i)) (t : unitInterval) : Factorizes (interp Q P t) :=
  factorizes_prod _

/-- **The interpolated probability is a polynomial.** For factorwise families `Q`, `P` and
an event `A`, `λ ↦ R^λ(A)` is (the restriction to `[0, 1]` of) a polynomial of degree at
most `|I|`.

Paper node: Lemma C.5 (§C.2). -/
theorem exists_polynomial_interp_prob (Q P : ∀ i, Dist (Ω i)) (A : Set (Pt Ω)) :
    ∃ f : Polynomial ℝ, f.natDegree ≤ Fintype.card I ∧
      ∀ t : unitInterval, f.eval (t : ℝ) = (interp Q P t).prob A := by
  sorry

/-- **Positivity of `P(C)` is preserved by interpolation.** If `⨂P` and `⨂P'` both give
`C` positive probability, so does every `⨂((1−λ)P + λP')`.

Paper node: Lemma C.10 (§C.3). -/
theorem interp_prob_pos (P P' : ∀ i, Dist (Ω i)) {C : Set (Pt Ω)}
    (hP : 0 < (Dist.prod P).prob C) (hP' : 0 < (Dist.prod P').prob C) (t : unitInterval) :
    0 < (interp P P' t).prob C := by
  sorry

/-- **From local to global conditional independence.** If `X ⊥^{Q'} Y | Z` holds for every
factorizing `Q'` within Euclidean distance `ε` of a factorizing `Q`, then it holds for
every `P ∈ Δ^F(Ω)`.

Paper node: Lemma 6.5 (§6.2). -/
theorem condIndepVar_of_local {α β γ : Type*} {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ}
    {Q : Dist (Pt Ω)} (hQ : Factorizes Q) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ Q' : Dist (Pt Ω), Factorizes Q' → Dist.euclDist Q Q' < ε → CondIndepVar Q' X Y Z) :
    ∀ P : Dist (Pt Ω), Factorizes P → CondIndepVar P X Y Z := by
  sorry

end FactoredSpaces
