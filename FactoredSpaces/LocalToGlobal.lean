import FactoredSpaces.Probability
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Set.Infinite

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
noncomputable def interp (Q P : ∀ i, Distr (Ω i)) (t : unitInterval) : Distr (Pt Ω) :=
  Distr.prod fun i => Distr.mix t (Q i) (P i)

lemma interp_zero (Q P : ∀ i, Distr (Ω i)) : interp Q P 0 = Distr.prod Q := by
  simp [interp, Distr.mix_zero]

lemma interp_one (Q P : ∀ i, Distr (Ω i)) : interp Q P 1 = Distr.prod P := by
  simp [interp, Distr.mix_one]

lemma factorizes_interp (Q P : ∀ i, Distr (Ω i)) (t : unitInterval) : Factorizes (interp Q P t) :=
  factorizes_prod _

/-- **The interpolated probability is a polynomial.** For factorwise families `Q`, `P` and
an event `A`, `λ ↦ R^λ(A)` is (the restriction to `[0, 1]` of) a polynomial of degree at
most `|I|`.

Paper node: Lemma C.5 (§C.2). -/
theorem exists_polynomial_interp_prob (Q P : ∀ i, Distr (Ω i)) (A : Set (Pt Ω)) :
    ∃ f : Polynomial ℝ, f.natDegree ≤ Fintype.card I ∧
      ∀ t : unitInterval, f.eval (t : ℝ) = (interp Q P t).prob A := by
  classical
  refine ⟨∑ ω ∈ Finset.univ.filter (· ∈ A), ∏ i : I,
      (Polynomial.C ((Q i).mass (ω i)) +
        Polynomial.C ((P i).mass (ω i) - (Q i).mass (ω i)) * Polynomial.X), ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun ω _ => ?_
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have hle : ∀ i : I, (Polynomial.C ((Q i).mass (ω i)) +
        Polynomial.C ((P i).mass (ω i) - (Q i).mass (ω i)) * Polynomial.X).natDegree ≤ 1 := by
      intro i
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      simp only [Polynomial.natDegree_C, max_le_iff]
      exact ⟨Nat.zero_le _, (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le⟩
    calc ∑ i : I, _ ≤ ∑ _i : I, 1 := Finset.sum_le_sum fun i _ => hle i
      _ = Fintype.card I := by simp
  · intro t
    rw [Distr.prob_eq_sum_filter, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Polynomial.eval_prod]
    simp only [interp, Distr.prod_mass, Distr.mix, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    exact Finset.prod_congr rfl fun i _ => by ring

/-- **Positivity of `P(C)` is preserved by interpolation.** If `⨂P` and `⨂P'` both give
`C` positive probability, so does every `⨂((1−λ)P + λP')`.

Paper node: Lemma C.10 (§C.3). -/
theorem interp_prob_pos (P P' : ∀ i, Distr (Ω i)) {C : Set (Pt Ω)}
    (hP : 0 < (Distr.prod P).prob C) (hP' : 0 < (Distr.prod P').prob C) (t : unitInterval) :
    0 < (interp P P' t).prob C := by
  classical
  rcases eq_or_lt_of_le t.2.1 with ht | ht
  · have h0 : t = 0 := Subtype.ext ht.symm
    rw [h0, interp_zero]
    exact hP
  -- For `λ > 0` the factorwise bound `λ P'_i(ω_i) ≤ (1−λ)P_i(ω_i) + λ P'_i(ω_i)` already
  -- gives `R^λ(C) ≥ λ^{|I|} P'(C) > 0`; the paper's full expansion is not needed.
  · have key : (t : ℝ) ^ Fintype.card I * (Distr.prod P').prob C ≤ (interp P P' t).prob C := by
      rw [Distr.prob_eq_sum_filter (Distr.prod P') C, Distr.prob_eq_sum_filter (interp P P' t) C,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun ω _ => ?_
      have hrw : (t : ℝ) ^ Fintype.card I * (Distr.prod P').mass ω
          = ∏ i, (t : ℝ) * (P' i).mass (ω i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Distr.prod_mass]
      rw [hrw]
      simp only [interp, Distr.prod_mass, Distr.mix]
      refine Finset.prod_le_prod (fun i _ => mul_nonneg ht.le ((P' i).nonneg _))
        fun i _ => ?_
      have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [t.2.2]
      nlinarith [(P i).nonneg (ω i)]
    have hpos : 0 < (t : ℝ) ^ Fintype.card I * (Distr.prod P').prob C := by positivity
    linarith

/-- Continuity of `λ ↦ R^λ` at `λ = 0`, in the explicit `ε`-`δ` form Lemma 6.5 consumes:
every Euclidean ball around `⨂Q` contains `R^λ` for all small enough `λ`. -/
private lemma exists_delta_euclDist_interp (Q P : ∀ i, Distr (Ω i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t : unitInterval, (t : ℝ) < δ →
      Distr.euclDist (Distr.prod Q) (interp Q P t) < ε := by
  classical
  have hcont : Continuous fun s : ℝ => ∑ ω : Pt Ω,
      ((Distr.prod Q).mass ω - ∏ i, ((1 - s) * (Q i).mass (ω i) + s * (P i).mass (ω i))) ^ 2 := by
    fun_prop
  obtain ⟨δ, hδ, hδ'⟩ :=
    Metric.continuousAt_iff.mp (hcont.continuousAt (x := (0 : ℝ))) (ε ^ 2) (by positivity)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hd : dist (t : ℝ) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]; exact ht
  have hzero : (∑ ω : Pt Ω,
      ((Distr.prod Q).mass ω - ∏ i, ((1 - (0 : ℝ)) * (Q i).mass (ω i)
        + (0 : ℝ) * (P i).mass (ω i))) ^ 2) = 0 := by
    simp [Distr.prod_mass]
  have hlt := hδ' hd
  rw [hzero, Real.dist_eq, sub_zero] at hlt
  rw [Distr.euclDist, Real.sqrt_lt' hε]
  refine lt_of_le_of_lt (le_abs_self _) ?_
  simpa only [interp, Distr.prod_mass, Distr.mix] using hlt

/-- **From local to global conditional independence.** If `X ⊥^{Q'} Y | Z` holds for every
factorizing `Q'` within Euclidean distance `ε` of a factorizing `Q`, then it holds for
every `P ∈ Δ^F(Ω)`.

Paper node: Lemma 6.5 (§6.2). -/
theorem condIndepVar_of_local {α β γ : Type*} {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ}
    {Q : Distr (Pt Ω)} (hQ : Factorizes Q) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ Q' : Distr (Pt Ω), Factorizes Q' → Distr.euclDist Q Q' < ε → CondIndepVar Q' X Y Z) :
    ∀ P : Distr (Pt Ω), Factorizes P → CondIndepVar P X Y Z := by
  classical
  intro P hP x y z
  obtain ⟨q, rfl⟩ := (factorizes_iff_exists_prod Q).mp hQ
  obtain ⟨p, rfl⟩ := (factorizes_iff_exists_prod P).mp hP
  obtain ⟨f₁, -, hf₁⟩ := exists_polynomial_interp_prob q p (fiber X x ∩ fiber Z z)
  obtain ⟨f₂, -, hf₂⟩ := exists_polynomial_interp_prob q p (fiber Y y ∩ fiber Z z)
  obtain ⟨f₃, -, hf₃⟩ := exists_polynomial_interp_prob q p (fiber X x ∩ fiber Y y ∩ fiber Z z)
  obtain ⟨f₄, -, hf₄⟩ := exists_polynomial_interp_prob q p (fiber Z z)
  obtain ⟨δ, hδ, hδ'⟩ := exists_delta_euclDist_interp q p hε
  -- `f₁f₂ − f₃f₄` vanishes on all of `(0, min δ 1)`, an infinite set of roots.
  have hroot : Set.Ioo (0 : ℝ) (min δ 1) ⊆ {s | (f₁ * f₂ - f₃ * f₄).IsRoot s} := by
    rintro s ⟨hs0, hs1⟩
    have hmem : s ∈ unitInterval := ⟨hs0.le, (hs1.trans_le (min_le_right _ _)).le⟩
    have hci := h (interp q p ⟨s, hmem⟩) (factorizes_interp q p _)
      (hδ' ⟨s, hmem⟩ (hs1.trans_le (min_le_left _ _))) x y z
    have e₁ : f₁.eval s = (interp q p ⟨s, hmem⟩).prob (fiber X x ∩ fiber Z z) := hf₁ ⟨s, hmem⟩
    have e₂ : f₂.eval s = (interp q p ⟨s, hmem⟩).prob (fiber Y y ∩ fiber Z z) := hf₂ ⟨s, hmem⟩
    have e₃ : f₃.eval s =
      (interp q p ⟨s, hmem⟩).prob (fiber X x ∩ fiber Y y ∩ fiber Z z) := hf₃ ⟨s, hmem⟩
    have e₄ : f₄.eval s = (interp q p ⟨s, hmem⟩).prob (fiber Z z) := hf₄ ⟨s, hmem⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
      e₁, e₂, e₃, e₄]
    exact sub_eq_zero_of_eq hci
  have hF : f₁ * f₂ - f₃ * f₄ = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.Ioo_infinite (lt_min hδ one_pos)).mono hroot)
  -- evaluating at `λ = 1`, where `R¹ = ⨂P`
  have e₁ : f₁.eval (1 : ℝ) = (Distr.prod p).prob (fiber X x ∩ fiber Z z) := by
    have := hf₁ 1; rwa [interp_one] at this
  have e₂ : f₂.eval (1 : ℝ) = (Distr.prod p).prob (fiber Y y ∩ fiber Z z) := by
    have := hf₂ 1; rwa [interp_one] at this
  have e₃ : f₃.eval (1 : ℝ) =
      (Distr.prod p).prob (fiber X x ∩ fiber Y y ∩ fiber Z z) := by
    have := hf₃ 1; rwa [interp_one] at this
  have e₄ : f₄.eval (1 : ℝ) = (Distr.prod p).prob (fiber Z z) := by
    have := hf₄ 1; rwa [interp_one] at this
  have hone := congrArg (fun g : Polynomial ℝ => g.eval (1 : ℝ)) hF
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_zero,
    e₁, e₂, e₃, e₄] at hone
  show (Distr.prod p).prob (fiber X x ∩ fiber Z z) *
      (Distr.prod p).prob (fiber Y y ∩ fiber Z z) =
    (Distr.prod p).prob (fiber X x ∩ fiber Y y ∩ fiber Z z) * (Distr.prod p).prob (fiber Z z)
  linarith

end FactoredSpaces
