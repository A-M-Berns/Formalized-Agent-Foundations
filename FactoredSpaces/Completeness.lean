import FactoredSpaces.Soundness
import FactoredSpaces.LocalToGlobal
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.BigOperators.Field

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

universe u v w

/-! ## Local probability infrastructure

Facts about `Dist` that Appendix C.3 needs beyond the §C.0–C.1 interface of
`Probability.lean`: a carrier of a distribution is inhabited, the mass of an outer
product is positive exactly when every factor is, a delta distribution on a product is
the outer product of the factorwise deltas, mixing two distributions mixes their event
probabilities, and the conditional distribution `P(· | C)` of Lemma C.20. -/

/-- A distribution witnesses that its carrier is inhabited: an empty type carries none,
because the empty sum is `0 ≠ 1`. -/
lemma Dist.nonempty_carrier {S : Type w} [Fintype S] (P : Dist S) : Nonempty S := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 := P.sum_eq_one
  simp at h1

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]

/-- Every factor of a factored space carrying a distribution is inhabited. -/
lemma nonempty_factor (P : Dist (Pt Ω)) (i : I) : Nonempty (Ω i) :=
  ⟨P.nonempty_carrier.some i⟩

/-- A point has positive mass under an outer product exactly when each of its
coordinates has positive mass under the corresponding factor. -/
lemma Dist.prod_mass_pos_iff (p : ∀ i, Dist (Ω i)) (ω : Pt Ω) :
    0 < (Dist.prod p).mass ω ↔ ∀ i, 0 < (p i).mass (ω i) := by
  rw [Dist.prod_mass]
  constructor
  · intro h i
    rcases lt_or_eq_of_le ((p i).nonneg (ω i)) with h' | h'
    · exact h'
    · rw [Finset.prod_eq_zero (Finset.mem_univ i) h'.symm] at h
      exact absurd h (lt_irrefl 0)
  · exact fun h => Finset.prod_pos fun i _ => h i

/-- The delta distribution at `ω` is the outer product of the factorwise deltas
(the paper's `δ_α = ⨂_{i∈J} δ_{α_i}`, eq. (delta_factorizes)). -/
lemma Dist.delta_eq_prod (ω : Pt Ω) :
    Dist.delta ω = Dist.prod fun i => Dist.delta (ω i) := by
  classical
  ext ω'
  rw [Dist.prod_mass]
  simp only [Dist.delta_mass]
  by_cases h : ω' = ω
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ω' i ≠ ω i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

lemma factorizes_delta (ω : Pt Ω) : Factorizes (Dist.delta ω) := by
  rw [Dist.delta_eq_prod]
  exact factorizes_prod _

/-- If `R` is the pointwise midpoint of `P` and `Q` then so are all its event
probabilities (used for the distribution `R` of Lemma C.9). -/
lemma Dist.prob_of_mass_midpoint {S : Type w} [Fintype S] {R P Q : Dist S}
    (h : ∀ s, R.mass s = (P.mass s + Q.mass s) / 2) (D : Set S) :
    R.prob D = (P.prob D + Q.prob D) / 2 := by
  simp only [Dist.prob]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s ∈ D <;> simp [hs, h s]

/-- The conditional distribution `P(· | C)`, for `P(C) > 0` (Lemma C.20). -/
noncomputable def condDist {S : Type w} [Fintype S] (P : Dist S) (C : Set S)
    (h : 0 < P.prob C) : Dist S where
  mass s := C.indicator P.mass s / P.prob C
  nonneg s := div_nonneg (Set.indicator_nonneg (fun t _ => P.nonneg t) s) h.le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self h.ne'

lemma condDist_mass {S : Type w} [Fintype S] (P : Dist S) (C : Set S) (h : 0 < P.prob C)
    (s : S) : (condDist P C h).mass s = C.indicator P.mass s / P.prob C := rfl

lemma condDist_prob {S : Type w} [Fintype S] (P : Dist S) (C : Set S) (h : 0 < P.prob C)
    (D : Set S) : (condDist P C h).prob D = P.prob (D ∩ C) / P.prob C := by
  simp only [Dist.prob]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hD : s ∈ D <;> by_cases hC : s ∈ C <;>
    simp [hD, hC, condDist_mass, Dist.prob]

/-- The paper's `δ_α ⊗ P_{I∖J}` read as an outer product over all of `I`: the factors are
the deltas `δ_{α_i}` on `J` and the marginals `P_i` off `J`.  This is what makes it
visibly a member of `Δ^F(Ω)` and pins down its one-factor marginals (Lemma C.18). -/
lemma outerCompl_delta_eq_prod {J : Finset I} {P : Dist (Pt Ω)} (hP : Factorizes P)
    (α : PtOn Ω J) :
    Dist.outerCompl (Dist.delta α) (P.marg Jᶜ) =
      Dist.prod fun i => if h : i ∈ J then Dist.delta (α ⟨i, h⟩) else P.margAt i := by
  classical
  ext ω
  rw [Dist.outerCompl_mass, Dist.prod_mass, ← Finset.prod_mul_prod_compl J]
  congr 1
  · rw [← Finset.prod_coe_sort J]
    rw [Dist.delta_eq_prod (Ω := fun i : J => Ω i) α, Dist.prod_mass]
    exact Finset.prod_congr rfl fun i _ => by
      rw [dif_pos i.2]
      congr 1
  · rw [hP.marg_mass Jᶜ, ← Finset.prod_coe_sort Jᶜ]
    exact (Finset.prod_congr rfl fun i _ => by
      rw [dif_neg (Finset.mem_compl.mp i.2)]; rfl).symm

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
  obtain ⟨⟨hPf, hPC⟩, ⟨hQf, hQC⟩, hagree⟩ := hPQ
  -- The paper's `R(ω) = (P(ω) + Q(ω))/2`, presented as an outer product: it agrees with
  -- `P` and `Q` off `i` and mixes their `i`-th factors evenly.
  set r : ∀ j, Dist (Ω j) :=
    Function.update (fun j => P.margAt j) i
      (Dist.mix ⟨1 / 2, by norm_num, by norm_num⟩ (P.margAt i) (Q.margAt i)) with hr
  set R : Dist (Pt Ω) := Dist.prod r with hRdef
  have hmass : ∀ ω : Pt Ω, R.mass ω = (P.mass ω + Q.mass ω) / 2 := by
    intro ω
    have hpeel : ∀ s : ∀ j, Dist (Ω j),
        (Dist.prod s).mass ω =
          (s i).mass (ω i) * ∏ j ∈ Finset.univ.erase i, (s j).mass (ω j) := fun s => by
      rw [Dist.prod_mass, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hPm : P.mass ω =
        (P.margAt i).mass (ω i) * ∏ j ∈ Finset.univ.erase i, (P.margAt j).mass (ω j) := by
      rw [hPf ω, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hQm : Q.mass ω =
        (Q.margAt i).mass (ω i) * ∏ j ∈ Finset.univ.erase i, (P.margAt j).mass (ω j) := by
      rw [hQf ω, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      exact congrArg _ (Finset.prod_congr rfl fun j hj => by
        rw [hagree j (Finset.ne_of_mem_erase hj)])
    have hRm : R.mass ω =
        (r i).mass (ω i) * ∏ j ∈ Finset.univ.erase i, (P.margAt j).mass (ω j) := by
      rw [hRdef, hpeel r]
      exact congrArg _ (Finset.prod_congr rfl fun j hj => by
        rw [hr, Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hri : (r i).mass (ω i) =
        ((P.margAt i).mass (ω i) + (Q.margAt i).mass (ω i)) / 2 := by
      rw [hr, Function.update_self]
      show (1 - (1 / 2 : ℝ)) * _ + (1 / 2 : ℝ) * _ = _
      ring
    rw [hRm, hPm, hQm, hri]
    ring
  have hRprob := Dist.prob_of_mass_midpoint hmass
  have h1 := h P hPf
  have h2 := h Q hQf
  have h3 := h R (hRdef ▸ factorizes_prod r)
  simp only [CondIndep] at h1 h2 h3
  rw [hRprob, hRprob, hRprob, hRprob] at h3
  -- Clearing the halves in `A ⊥^R B | C` and cancelling the `P`- and `Q`-independencies
  -- leaves the paper's cross-term identity.
  have e3 : (P.prob (A ∩ C) + Q.prob (A ∩ C)) * (P.prob (B ∩ C) + Q.prob (B ∩ C)) =
      (P.prob (A ∩ B ∩ C) + Q.prob (A ∩ B ∩ C)) * (P.prob C + Q.prob C) := by
    linarith [h3]
  have hmid : P.prob (A ∩ C) * Q.prob (B ∩ C) + Q.prob (A ∩ C) * P.prob (B ∩ C) =
      P.prob (A ∩ B ∩ C) * Q.prob C + Q.prob (A ∩ B ∩ C) * P.prob C := by
    linarith [e3, h1, h2]
  -- The algebraic core: `(P(A∩C)Q(C) − Q(A∩C)P(C)) · (Q(B∩C)P(C) − P(B∩C)Q(C)) = 0`.
  have key : (P.prob (A ∩ C) * Q.prob C - Q.prob (A ∩ C) * P.prob C) *
      (Q.prob (B ∩ C) * P.prob C - P.prob (B ∩ C) * Q.prob C) = 0 := by
    have hexp : (P.prob (A ∩ C) * Q.prob C - Q.prob (A ∩ C) * P.prob C) *
        (Q.prob (B ∩ C) * P.prob C - P.prob (B ∩ C) * Q.prob C) =
        P.prob C * Q.prob C *
            (P.prob (A ∩ C) * Q.prob (B ∩ C) + Q.prob (A ∩ C) * P.prob (B ∩ C)) -
          Q.prob C ^ 2 * (P.prob (A ∩ C) * P.prob (B ∩ C)) -
          P.prob C ^ 2 * (Q.prob (A ∩ C) * Q.prob (B ∩ C)) := by ring
    rw [hexp, hmid, h1, h2]
    ring
  rcases mul_eq_zero.mp key with hk | hk
  · left
    show P.prob (A ∩ C) / P.prob C = Q.prob (A ∩ C) / Q.prob C
    rw [div_eq_div_iff hPC.ne' hQC.ne']
    linarith
  · right
    show P.prob (B ∩ C) / P.prob C = Q.prob (B ∩ C) / Q.prob C
    rw [div_eq_div_iff hPC.ne' hQC.ne']
    linarith

/-! ## Lemma C.7: the cohistories cover `I` -/

/-- **Completeness through the cohistory.** If `A ⊥^⊗ B | C` then
`Cohistory(A | C) ∪ Cohistory(B | C) = I`.

Paper node: Lemma C.7 (§C.3). -/
theorem cohistory_union_eq_univ_of_condIndepAll {A B C : Set (Pt Ω)} (h : CondIndepAll A B C) :
    cohistory A C ∪ cohistory B C = Finset.univ := by
  classical
  refine Finset.eq_univ_iff_forall.mpr fun i => Finset.mem_union.mpr ?_
  rw [mem_cohistory_iff, mem_cohistory_iff]
  by_cases hA : Irrelevant i A C
  · exact Or.inl hA
  right
  -- `P(A | C) = Q(A | C)` iff the cross-multiplied form vanishes, for `P(C), Q(C) > 0`.
  have bridge : ∀ (X Y : Dist (Pt Ω)) (D : Set (Pt Ω)), 0 < X.prob C → 0 < Y.prob C →
      (X.condProb D C = Y.condProb D C ↔
        X.prob (D ∩ C) * Y.prob C - Y.prob (D ∩ C) * X.prob C = 0) := by
    intro X Y D hX hY
    rw [Dist.condProb, Dist.condProb, div_eq_div_iff hX.ne' hY.ne', sub_eq_zero]
  -- A pair witnessing that `i` is relevant to `A` given `C`.
  obtain ⟨P, Q, hPQ, hne⟩ : ∃ P Q : Dist (Pt Ω), (P, Q) ∈ pairsDifferingAt C i ∧
      P.condProb A C ≠ Q.condProb A C := by
    by_contra hc
    refine hA fun P Q hPQ => ?_
    by_contra hne
    exact hc ⟨P, Q, hPQ, hne⟩
  have hPC : 0 < P.prob C := hPQ.1.2
  have hQC : 0 < Q.prob C := hPQ.2.1.2
  have hag : ∀ j, j ≠ i → P.margAt j = Q.margAt j := hPQ.2.2
  obtain ⟨p, rfl⟩ := (factorizes_iff_exists_prod P).mp hPQ.1.1
  obtain ⟨q, rfl⟩ := (factorizes_iff_exists_prod Q).mp hPQ.2.1.1
  simp only [Dist.margAt_prod] at hag
  intro P' Q' hPQ'
  have hP'C : 0 < P'.prob C := hPQ'.1.2
  have hQ'C : 0 < Q'.prob C := hPQ'.2.1.2
  have hag' : ∀ j, j ≠ i → P'.margAt j = Q'.margAt j := hPQ'.2.2
  obtain ⟨p', rfl⟩ := (factorizes_iff_exists_prod P').mp hPQ'.1.1
  obtain ⟨q', rfl⟩ := (factorizes_iff_exists_prod Q').mp hPQ'.2.1.1
  simp only [Dist.margAt_prod] at hag'
  -- The interpolated pairs `(P^λ, Q^λ)` stay in `Δ^F_{C,i}(Ω)`, so Lemma C.9 applies.
  have hPtC : ∀ t : unitInterval, 0 < (interp p p' t).prob C := interp_prob_pos p p' hPC hP'C
  have hQtC : ∀ t : unitInterval, 0 < (interp q q' t).prob C := interp_prob_pos q q' hQC hQ'C
  have hmem : ∀ t : unitInterval, (interp p p' t, interp q q' t) ∈ pairsDifferingAt C i := by
    intro t
    refine ⟨⟨factorizes_interp p p' t, hPtC t⟩, ⟨factorizes_interp q q' t, hQtC t⟩, fun j hj => ?_⟩
    simp only [interp, Dist.margAt_prod, hag j hj, hag' j hj]
  have hdisj : ∀ t : unitInterval,
      (interp p p' t).condProb A C = (interp q q' t).condProb A C ∨
        (interp p p' t).condProb B C = (interp q q' t).condProb B C :=
    fun t => pqIrrelevant_or_of_condIndepAll h (hmem t)
  -- Lemma C.5: each interpolated probability is a polynomial in `λ`.
  obtain ⟨gA, -, hgA⟩ := exists_polynomial_interp_prob p p' (A ∩ C)
  obtain ⟨gB, -, hgB⟩ := exists_polynomial_interp_prob p p' (B ∩ C)
  obtain ⟨gC, -, hgC⟩ := exists_polynomial_interp_prob p p' C
  obtain ⟨kA, -, hkA⟩ := exists_polynomial_interp_prob q q' (A ∩ C)
  obtain ⟨kB, -, hkB⟩ := exists_polynomial_interp_prob q q' (B ∩ C)
  obtain ⟨kC, -, hkC⟩ := exists_polynomial_interp_prob q q' C
  set Gp : Polynomial ℝ := gA * kC - kA * gC with hGp
  set Fp : Polynomial ℝ := gB * kC - kB * gC with hFp
  have hGeval : ∀ t : unitInterval, Gp.eval (t : ℝ) =
      (interp p p' t).prob (A ∩ C) * (interp q q' t).prob C -
        (interp q q' t).prob (A ∩ C) * (interp p p' t).prob C := fun t => by
    simp only [hGp, Polynomial.eval_sub, Polynomial.eval_mul, hgA t, hkC t, hkA t, hgC t]
  have hFeval : ∀ t : unitInterval, Fp.eval (t : ℝ) =
      (interp p p' t).prob (B ∩ C) * (interp q q' t).prob C -
        (interp q q' t).prob (B ∩ C) * (interp p p' t).prob C := fun t => by
    simp only [hFp, Polynomial.eval_sub, Polynomial.eval_mul, hgB t, hkC t, hkB t, hgC t]
  -- `G` is not the zero polynomial: at `λ = 0` it records `P(A | C) ≠ Q(A | C)`.
  have hGne : Gp ≠ 0 := by
    intro hz
    refine hne ((bridge _ _ A hPC hQC).mpr ?_)
    have h0 := hGeval 0
    rw [Set.Icc.coe_zero, interp_zero, interp_zero, hz, Polynomial.eval_zero] at h0
    exact h0.symm
  -- Off the finitely many roots of `G`, Lemma C.9 forces the `B`-disjunct, so `F` vanishes.
  have hroots : Set.Icc (0 : ℝ) 1 \ {x : ℝ | Gp.IsRoot x} ⊆ {x : ℝ | Fp.IsRoot x} := by
    rintro x ⟨hx, hxG⟩
    set t : unitInterval := ⟨x, hx⟩
    have hcoe : ((t : unitInterval) : ℝ) = x := rfl
    rcases hdisj t with hL | hR
    · refine absurd (show Gp.IsRoot x from ?_) hxG
      rw [Polynomial.IsRoot, ← hcoe, hGeval t]
      exact (bridge _ _ A (hPtC t) (hQtC t)).mp hL
    · show Fp.IsRoot x
      rw [Polynomial.IsRoot, ← hcoe, hFeval t]
      exact (bridge _ _ B (hPtC t) (hQtC t)).mp hR
  have hinf : (Set.Icc (0 : ℝ) 1 \ {x : ℝ | Gp.IsRoot x}).Infinite :=
    (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).sdiff (Polynomial.finite_setOf_isRoot hGne)
  have hF0 : Fp = 0 := Polynomial.eq_zero_of_infinite_isRoot Fp (hinf.mono hroots)
  -- Evaluating the zero polynomial at `λ = 1` returns the arbitrary pair `(P', Q')`.
  have h1 := hFeval 1
  rw [Set.Icc.coe_one, interp_one, interp_one, hF0, Polynomial.eval_zero] at h1
  exact (bridge _ _ B hP'C hQ'C).mpr h1.symm

/-! ## Lemma C.12: progressive replacement of irrelevant factors -/

/-- The strictly-positive special case of Lemma C.12.  Replacing the factors of `⨂ p`
indexed by `Cohistory(A | C)` one at a time by those of `⨂ q` leaves `P(A | C)`
unchanged: each single-factor replacement is a pair in `Δ^F_{C,j}(Ω)`, so irrelevance of
`j` applies.  Strict positivity of the new factors on the cohistory is what keeps
`P(C) > 0` along the induction (via Lemma C.11 part 1). -/
private lemma condProb_eq_of_replace {A C : Set (Pt Ω)} (p q : ∀ i, Dist (Ω i))
    (hp : 0 < (Dist.prod p).prob C)
    (hstrict : ∀ j, Irrelevant j A C → (q j).StrictlyPositive)
    (hagree : ∀ j, ¬ Irrelevant j A C → p j = q j) :
    (Dist.prod p).condProb A C = (Dist.prod q).condProb A C := by
  classical
  -- `S` records which factors have already been replaced.
  have key : ∀ S : Finset I, S ⊆ cohistory A C →
      0 < (Dist.prod fun j => if j ∈ S then q j else p j).prob C ∧
      (Dist.prod fun j => if j ∈ S then q j else p j).condProb A C
        = (Dist.prod p).condProb A C := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        have he : (fun j => if j ∈ (∅ : Finset I) then q j else p j) = p := by
          funext j; simp
        rw [he]
        exact ⟨hp, rfl⟩
    | insert j₀ S hj₀ ih =>
        intro hsub
        have hj₀J : j₀ ∈ cohistory A C := hsub (Finset.mem_insert_self _ _)
        obtain ⟨hSpos, hSeq⟩ := ih fun j hj => hsub (Finset.mem_insert_of_mem hj)
        -- the replaced factor `q j₀` is strictly positive, so the support only grows
        have hsupp : (Dist.prod fun j => if j ∈ S then q j else p j).support ⊆
            (Dist.prod fun j => if j ∈ insert j₀ S then q j else p j).support := by
          intro ω hω
          rw [Dist.mem_support_iff, Dist.prod_mass_pos_iff] at hω ⊢
          intro i
          by_cases hi : i = j₀
          · subst hi
            simpa using hstrict i (mem_cohistory_iff.mp hj₀J) (ω i)
          · simpa [Finset.mem_insert, hi] using hω i
        have hIpos : 0 < (Dist.prod fun j => if j ∈ insert j₀ S then q j else p j).prob C :=
          Dist.prob_pos_of_support_subset hsupp hSpos
        -- the two products differ only in the factor `j₀`, which is irrelevant to `A`
        have hpair : ((Dist.prod fun j => if j ∈ S then q j else p j),
            (Dist.prod fun j => if j ∈ insert j₀ S then q j else p j))
            ∈ pairsDifferingAt C j₀ := by
          refine ⟨⟨factorizes_prod _, hSpos⟩, ⟨factorizes_prod _, hIpos⟩, fun j hj => ?_⟩
          rw [Dist.margAt_prod, Dist.margAt_prod]
          simp [Finset.mem_insert, hj]
        have hirr : (Dist.prod fun j => if j ∈ S then q j else p j).condProb A C
            = (Dist.prod fun j => if j ∈ insert j₀ S then q j else p j).condProb A C :=
          mem_cohistory_iff.mp hj₀J _ _ hpair
        exact ⟨hIpos, hirr.symm.trans hSeq⟩
  have hfull : (fun j => if j ∈ cohistory A C then q j else p j) = q := by
    funext j
    by_cases hj : j ∈ cohistory A C
    · rw [if_pos hj]
    · rw [if_neg hj]
      exact hagree j fun hc => hj (mem_cohistory_iff.mpr hc)
  have := (key (cohistory A C) Finset.Subset.rfl).2
  rw [hfull] at this
  exact this.symm

/-- **Progressive application of irrelevance.** If `P, Q ∈ Δ^F_C(Ω)` agree in every
factor relevant to `A` given `C`, then `P(A | C) = Q(A | C)`.

Paper node: Lemma C.12 (§C.3). -/
theorem condProb_eq_of_agree_on_relevant {A C : Set (Pt Ω)} {P Q : Dist (Pt Ω)}
    (hP : P ∈ factorizingPos C) (hQ : Q ∈ factorizingPos C)
    (h : ∀ j, ¬ Irrelevant j A C → P.margAt j = Q.margAt j) :
    P.condProb A C = Q.condProb A C := by
  classical
  haveI : ∀ j, Nonempty (Ω j) := fun j => nonempty_factor P j
  obtain ⟨hPf, hPpos⟩ := hP
  obtain ⟨hQf, hQpos⟩ := hQ
  have hPe : P = Dist.prod fun i => P.margAt i := hPf.eq_prod_margAt
  have hQe : Q = Dist.prod fun i => Q.margAt i := hQf.eq_prod_margAt
  -- The interpolant of the paper's proof: uniform (hence strictly positive) on the
  -- cohistory, and `P`'s own factors off it.
  set q' : ∀ i, Dist (Ω i) :=
    fun i => if i ∈ cohistory A C then Dist.uniform else P.margAt i with hq'
  have hstrict : ∀ j, Irrelevant j A C → (q' j).StrictlyPositive := by
    intro j hj
    simp only [hq', if_pos (mem_cohistory_iff.mpr hj)]
    exact Dist.uniform_strictlyPositive
  have hPq' : ∀ j, ¬ Irrelevant j A C → P.margAt j = q' j := by
    intro j hj
    simp only [hq', if_neg fun hc => hj (mem_cohistory_iff.mp hc)]
  have h1 : (Dist.prod fun i => P.margAt i).condProb A C = (Dist.prod q').condProb A C :=
    condProb_eq_of_replace _ q' (by rw [← hPe]; exact hPpos) hstrict hPq'
  have h2 : (Dist.prod fun i => Q.margAt i).condProb A C = (Dist.prod q').condProb A C := by
    refine condProb_eq_of_replace _ q' (by rw [← hQe]; exact hQpos) hstrict fun j hj => ?_
    rw [← hPq' j hj]
    exact (h j hj).symm
  rw [hPe, hQe, h1, h2]

/-! ## Lemmas C.18, C.19: independence properties of the cohistory -/

/-- **`A ⊥^⊗ U_J | C` for `J = Cohistory(A | C)`.**

Paper node: Lemma C.18 (§C.3). -/
theorem condIndepEventVar_proj_cohistory (A C : Set (Pt Ω)) (P : Dist (Pt Ω))
    (hP : Factorizes P) : CondIndepEventVar P A (proj (cohistory A C)) C := by
  classical
  set J := cohistory A C with hJ
  intro α
  set B := fiber (proj J) α with hB
  have hBC : B ∩ C = sliceAt J α C := Set.inter_comm _ _
  have hABC : A ∩ B ∩ C = sliceAt J α (A ∩ C) := by
    ext ω; simp only [sliceAt, hB, fiber, Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
  simp only [CondIndep]
  rcases (P.prob_nonneg (B ∩ C)).lt_or_eq with hpos | hzero
  swap
  · -- `P(B ∩ C) = 0`: both sides of the product identity vanish
    have h1 : P.prob (A ∩ B ∩ C) = 0 :=
      le_antisymm (hzero ▸ P.prob_mono fun ω hω => ⟨hω.1.2, hω.2⟩) (P.prob_nonneg _)
    rw [h1, ← hzero, mul_zero, zero_mul]
  -- `P(B ∩ C) > 0`
  have hPC : 0 < P.prob C := lt_of_lt_of_le hpos (P.prob_mono fun _ hω => hω.2)
  have hBCval : P.prob (B ∩ C) =
      (P.marg J).mass α * (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α C)) := by
    rw [hBC]; exact hP.prob_sliceAt J α C
  have hABCval : P.prob (A ∩ B ∩ C) =
      (P.marg J).mass α * (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α (A ∩ C))) := by
    rw [hABC]; exact hP.prob_sliceAt J α (A ∩ C)
  have hsC : 0 < (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α C)) := by
    by_contra hc
    push Not at hc
    rw [hBCval, le_antisymm hc ((P.marg Jᶜ).prob_nonneg _), mul_zero] at hpos
    exact lt_irrefl 0 hpos
  set mJ := (P.marg J).mass α with hmJ
  set sC := (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α C)) with hsCdef
  set sAC := (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α (A ∩ C))) with hsACdef
  -- the auxiliary distribution `δ_α ⊗ P_{I∖J}` and its membership in `Δ^F_C(Ω)`
  set R := Dist.outerCompl (Dist.delta α) (P.marg Jᶜ) with hR
  have hRprod : R = Dist.prod fun i =>
      if h : i ∈ J then Dist.delta (α ⟨i, h⟩) else P.margAt i := outerCompl_delta_eq_prod hP α
  have hRfact : Factorizes R := by rw [hRprod]; exact factorizes_prod _
  have hRC : R.prob C = sC := Dist.prob_outerCompl_delta P J α C
  have hRAC : R.prob (A ∩ C) = sAC := Dist.prob_outerCompl_delta P J α (A ∩ C)
  have hRmarg : ∀ j, ¬ Irrelevant j A C → P.margAt j = R.margAt j := by
    intro j hj
    have hjJ : j ∉ J := fun hc => hj (mem_cohistory_iff.mp (hJ ▸ hc))
    rw [hRprod, Dist.margAt_prod, dif_neg hjJ]
  -- Lemma C.12 identifies the two conditional probabilities
  have hkey : P.condProb A C = R.condProb A C :=
    condProb_eq_of_agree_on_relevant ⟨hP, hPC⟩ ⟨hRfact, by rw [hRC]; exact hsC⟩ hRmarg
  simp only [Dist.condProb, hRC, hRAC] at hkey
  rw [div_eq_div_iff hPC.ne' hsC.ne'] at hkey
  rw [hBCval, hABCval]
  calc P.prob (A ∩ C) * (mJ * sC) = P.prob (A ∩ C) * sC * mJ := by ring
    _ = sAC * P.prob C * mJ := by rw [hkey]
    _ = mJ * sAC * P.prob C := by ring

/-- **`U_J ⊥^⊗ U_{I∖J} | C` for `J = Cohistory(A | C)`.**

Paper node: Lemma C.19 (§C.3). -/
theorem condIndepVarEvent_proj_cohistory (A C : Set (Pt Ω)) (P : Dist (Pt Ω))
    (hP : Factorizes P) :
    CondIndepVarEvent P (proj (cohistory A C)) (proj (cohistory A C)ᶜ) C := by
  intro α β
  -- `A ⊥^⊗ U_J | C` by Lemma C.18, so in particular `A ⊥^⊗ B | C` for `B = {U_J = α}`
  have hAB : CondIndepAll A (fiber (proj (cohistory A C)) α) C :=
    fun P' hP' => condIndepEventVar_proj_cohistory A C P' hP' α
  -- Lemma C.7 then puts `I ∖ J` inside the cohistory of `B`
  have hsub : (cohistory A C)ᶜ ⊆ cohistory (fiber (proj (cohistory A C)) α) C := by
    intro i hi
    have hmem : i ∈ cohistory A C ∪ cohistory (fiber (proj (cohistory A C)) α) C := by
      rw [cohistory_union_eq_univ_of_condIndepAll hAB]; exact Finset.mem_univ i
    rcases Finset.mem_union.mp hmem with h' | h'
    · exact absurd h' (Finset.mem_compl.mp hi)
    · exact h'
  exact CondIndepEventVar.of_proj_subset hsub
    (condIndepEventVar_proj_cohistory (fiber (proj (cohistory A C)) α) C P hP) β

/-! ## Lemma C.20: the cohistory disintegrates `C` -/

/-- **The cohistory disintegrates `C`.**  Needs a point of `Ω` — the paper takes "any
strictly positive distribution", which exists only when `Ω ≠ ∅` — but not more: when
`Ω = ∅` every `J` disintegrates every `C` trivially, so the statement is unconditional.

Paper node: Lemma C.20 (§C.3). -/
theorem disintegrates_cohistory (A C : Set (Pt Ω)) : Disintegrates (cohistory A C) C := by
  classical
  set J := cohistory A C with hJ
  -- the two degenerate cases: no points at all, or `C` empty
  rcases isEmpty_or_nonempty (Pt Ω) with hE | hNE
  · exact (disintegrates_iff_splice J C).mpr fun a _ _ _ => (IsEmpty.false a).elim
  rcases Set.eq_empty_or_nonempty C with rfl | hCne
  · exact (disintegrates_iff_splice J ∅).mpr fun a ha => absurd ha (Set.notMem_empty a)
  haveI : ∀ i, Nonempty (Ω i) := fun i => ⟨hNE.some i⟩
  -- the paper's strictly positive `P` and the conditional `Q = P(· | C)`
  set P : Dist (Pt Ω) := Dist.prod fun _ => Dist.uniform with hPdef
  have hPfact : Factorizes P := factorizes_prod _
  have hPpos : P.StrictlyPositive := fun ω =>
    (Dist.prod_mass_pos_iff _ ω).mpr fun _ => Dist.uniform_strictlyPositive _
  have hPsupp : P.support = Set.univ := Set.eq_univ_of_forall fun ω => hPpos ω
  have hPC : 0 < P.prob C := by
    rw [P.prob_pos_iff, hPsupp, Set.inter_univ]; exact hCne
  set Q := condDist P C hPC with hQdef
  have hQsupp : Q.support = C := by
    ext ω
    simp only [Dist.mem_support_iff, hQdef, condDist_mass, Set.indicator_apply]
    constructor
    · intro hω; by_contra hc; rw [if_neg hc, zero_div] at hω; exact lt_irrefl 0 hω
    · intro hω; rw [if_pos hω]; exact div_pos (hPpos ω) hPC
  -- `Q` splits as `Q_J ⊗ Q_{I∖J}`, by Lemma C.19 for `P`
  have hQfactor : Q = Dist.outerCompl (Q.marg J) (Q.marg Jᶜ) := by
    ext ω
    rw [Dist.outerCompl_mass]
    have hsingle : fiber (proj J) (proj J ω) ∩ fiber (proj Jᶜ) (proj Jᶜ ω) = {ω} := by
      ext ω'
      simp only [Set.mem_inter_iff, fiber, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        funext i
        by_cases hi : i ∈ J
        · exact congrFun h1 ⟨i, hi⟩
        · exact congrFun h2 ⟨i, Finset.mem_compl.mpr hi⟩
      · rintro rfl; exact ⟨rfl, rfl⟩
    have hCI : P.prob (fiber (proj J) (proj J ω) ∩ C) *
        P.prob (fiber (proj Jᶜ) (proj Jᶜ ω) ∩ C) =
        P.prob (fiber (proj J) (proj J ω) ∩ fiber (proj Jᶜ) (proj Jᶜ ω) ∩ C) * P.prob C :=
      condIndepVarEvent_proj_cohistory A C P hPfact (proj J ω) (proj Jᶜ ω)
    have hlhs : (Q.marg J).mass (proj J ω) * (Q.marg Jᶜ).mass (proj Jᶜ ω) =
        Q.prob (fiber (proj J) (proj J ω)) * Q.prob (fiber (proj Jᶜ) (proj Jᶜ ω)) := rfl
    rw [hlhs, hQdef, condDist_prob, condDist_prob]
    rw [div_mul_div_comm, ← Dist.prob_singleton Q ω, hQdef, ← hsingle, condDist_prob]
    rw [hCI]
    field_simp
  -- the supports of the two halves are the two projections of `C`
  have hmargsupp : ∀ K : Finset I, (Q.marg K).support = projSet K C := by
    intro K
    ext α
    rw [Dist.mem_support_iff, Dist.marg_mass, Dist.prob_pos_iff, hQsupp]
    constructor
    · rintro ⟨ω, hω1, hω2⟩; exact ⟨ω, hω2, hω1⟩
    · rintro ⟨ω, hω, rfl⟩; exact ⟨ω, rfl, hω⟩
  have hsplit := Dist.support_outerCompl (Q.marg J) (Q.marg Jᶜ)
  rw [← hQfactor, hQsupp, hmargsupp J, hmargsupp Jᶜ] at hsplit
  exact hsplit

/-! ## Lemma C.8: the cohistory is the complement of the history -/

/-- **`Cohistory(A | C) = I ∖ H(A | C)`.**

Paper node: Lemma C.8 (§C.3). -/
theorem cohistory_eq_compl_eventHistory (A C : Set (Pt Ω)) :
    cohistory A C = (eventHistory A C)ᶜ := by
  classical
  have hcancel : ∀ x y z : ℝ, z ≠ 0 → x * z / (y * z) = x / y := by
    intro x y z hz
    rw [mul_comm x z, mul_comm y z, mul_div_mul_left _ _ hz]
  have hposr : ∀ x y : ℝ, 0 ≤ y → 0 < x * y → 0 < y := by
    intro x y hy hxy
    rcases hy.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hxy; exact absurd hxy (lt_irrefl 0)
  obtain ⟨⟨hdis, hsplice⟩, hmin⟩ := eventHistory_minimal_splice A C
  apply Finset.Subset.antisymm
  · -- `Cohistory(A | C) ⊆ (H(A | C))ᶜ`: the complement of the cohistory has the two
    -- properties that characterise the history (Lemma C.4), so it contains it
    have hdisK : Disintegrates (cohistory A C)ᶜ C := (disintegrates_cohistory A C).compl
    have hspliceK : A ∩ C = splice (cohistory A C)ᶜ (A ∩ C) C := by
      apply Set.Subset.antisymm
      · exact fun ω hω => ⟨ω, hω, ω, hω.2, (piecewise_self _ ω).symm⟩
      · rintro ω ⟨a, haAC, b, hbC, rfl⟩
        have hcC : ((cohistory A C)ᶜ).piecewise a b ∈ C := hdisK.splice_mem haAC.2 hbC
        refine ⟨?_, hcC⟩
        by_contra hnotA
        have hcnot : ((cohistory A C)ᶜ).piecewise a b ∉ A ∩ C := fun hh => hnotA hh.1
        have hdaC : 0 < (Dist.delta a).prob C := by
          rw [Dist.delta_prob, if_pos haAC.2]; norm_num
        have hdcC : 0 < (Dist.delta (((cohistory A C)ᶜ).piecewise a b)).prob C := by
          rw [Dist.delta_prob, if_pos hcC]; norm_num
        -- the two deltas agree in every factor relevant to `A` given `C`
        have hagree : ∀ j, ¬ Irrelevant j A C →
            (Dist.delta a).margAt j =
              (Dist.delta (((cohistory A C)ᶜ).piecewise a b)).margAt j := by
          intro j hj
          have hjK : j ∈ (cohistory A C)ᶜ :=
            Finset.mem_compl.mpr fun hc => hj (mem_cohistory_iff.mp hc)
          rw [Dist.delta_eq_prod a, Dist.delta_eq_prod (((cohistory A C)ᶜ).piecewise a b),
            Dist.margAt_prod, Dist.margAt_prod]
          simp [Finset.piecewise, hjK]
        have hkey := condProb_eq_of_agree_on_relevant
          ⟨factorizes_delta a, hdaC⟩ ⟨factorizes_delta _, hdcC⟩ hagree
        simp only [Dist.condProb, Dist.delta_prob] at hkey
        rw [if_pos haAC, if_pos haAC.2, if_neg hcnot, if_pos hcC] at hkey
        norm_num at hkey
    intro i hi
    rw [Finset.mem_compl]
    exact fun hcon => (Finset.mem_compl.mp (hmin _ hdisK hspliceK hcon)) hi
  · -- `(H(A | C))ᶜ ⊆ Cohistory(A | C)`: Lemma C.15 computes `P(A | C)` from `P_H` alone
    intro i hi
    rw [Finset.mem_compl] at hi
    rw [mem_cohistory_iff]
    rintro P Q ⟨⟨hPf, hPC⟩, ⟨hQf, hQC⟩, hagree⟩
    have hmargH : P.marg (eventHistory A C) = Q.marg (eventHistory A C) := by
      ext α
      rw [hPf.marg_mass, hQf.marg_mass]
      exact Finset.prod_congr rfl fun j _ => by
        rw [hagree j fun hji => hi (hji ▸ j.2)]
    have hCeq : C = cyl (eventHistory A C) (projSet (eventHistory A C) C) ∩
        cyl (eventHistory A C)ᶜ (projSet (eventHistory A C)ᶜ C) := by
      rw [← splice_eq_cyl_inter, ← prodSplit_eq_splice]; exact hdis
    have hACeq : A ∩ C = cyl (eventHistory A C) (projSet (eventHistory A C) (A ∩ C)) ∩
        cyl (eventHistory A C)ᶜ (projSet (eventHistory A C)ᶜ C) := by
      rw [← splice_eq_cyl_inter]; exact hsplice
    have hPAC : P.prob (A ∩ C) =
        (P.marg (eventHistory A C)).prob (projSet (eventHistory A C) (A ∩ C)) *
          (P.marg (eventHistory A C)ᶜ).prob (projSet (eventHistory A C)ᶜ C) := by
      conv_lhs => rw [hACeq]
      exact Dist.prob_cyl_inter_cyl (hPf.eq_outerCompl _) _ _
    have hPCv : P.prob C =
        (P.marg (eventHistory A C)).prob (projSet (eventHistory A C) C) *
          (P.marg (eventHistory A C)ᶜ).prob (projSet (eventHistory A C)ᶜ C) := by
      conv_lhs => rw [hCeq]
      exact Dist.prob_cyl_inter_cyl (hPf.eq_outerCompl _) _ _
    have hQAC : Q.prob (A ∩ C) =
        (Q.marg (eventHistory A C)).prob (projSet (eventHistory A C) (A ∩ C)) *
          (Q.marg (eventHistory A C)ᶜ).prob (projSet (eventHistory A C)ᶜ C) := by
      conv_lhs => rw [hACeq]
      exact Dist.prob_cyl_inter_cyl (hQf.eq_outerCompl _) _ _
    have hQCv : Q.prob C =
        (Q.marg (eventHistory A C)).prob (projSet (eventHistory A C) C) *
          (Q.marg (eventHistory A C)ᶜ).prob (projSet (eventHistory A C)ᶜ C) := by
      conv_lhs => rw [hCeq]
      exact Dist.prob_cyl_inter_cyl (hQf.eq_outerCompl _) _ _
    have heP : 0 < (P.marg (eventHistory A C)ᶜ).prob (projSet (eventHistory A C)ᶜ C) :=
      hposr _ _ ((P.marg _).prob_nonneg _) (hPCv ▸ hPC)
    have heQ : 0 < (Q.marg (eventHistory A C)ᶜ).prob (projSet (eventHistory A C)ᶜ C) :=
      hposr _ _ ((Q.marg _).prob_nonneg _) (hQCv ▸ hQC)
    show P.condProb A C = Q.condProb A C
    rw [Dist.condProb, Dist.condProb, hPAC, hPCv, hQAC, hQCv,
      hcancel _ _ _ heP.ne', hcancel _ _ _ heQ.ne', hmargH]

/-! ## Lemma 6.4: completeness for events -/

/-- **Completeness for events.** If `A ⊥^P B | C` for all `P ∈ Δ^F(Ω)`, then
`H(A | C) ∩ H(B | C) = ∅`.

Paper node: Lemma 6.4 (§6.1). -/
theorem disjoint_eventHistory_of_condIndepAll {A B C : Set (Pt Ω)} (h : CondIndepAll A B C) :
    Disjoint (eventHistory A C) (eventHistory B C) := by
  classical
  have hu := cohistory_union_eq_univ_of_condIndepAll h
  rw [cohistory_eq_compl_eventHistory, cohistory_eq_compl_eventHistory,
    ← Finset.compl_inter, Finset.compl_eq_univ_iff] at hu
  exact Finset.disjoint_iff_inter_eq_empty.mpr hu

end FactoredSpaces
