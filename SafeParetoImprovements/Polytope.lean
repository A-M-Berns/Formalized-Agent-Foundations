import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Polytopes: convex hulls of finitely many points, and their half-space sections

Mathlib has no Weyl–Minkowski theorem, so "the intersection of a polytope with a
half-space is a polytope" — which Corollary 14's *polytope* clause needs (RULING 12) — is
proved here directly, for polytopes presented as convex hulls of finite sets:

> `convexHull V ∩ {y | t ≤ ℓ y} = convexHull ((V ∩ H) ∪ {crossing points of the edges
> from `V \ H` to `V ∩ H`})`.

The inclusion `⊆` is the content.  Given `x = ∑ λᵥ v` in the half-space, split `V` into
`A` (on or above the hyperplane, surplus `sᵥ = ℓ v − t ≥ 0`) and `B` (below it, deficit
`d_w = t − ℓ w > 0`), and set `S = ∑_A λᵥ sᵥ`, `D = ∑_B λ_w d_w`, so `ℓ x ≥ t` reads
`D ≤ S`.  Route the mass of each `w ∈ B` through the crossing points
`c(w, v) = (sᵥ w + d_w v) / (sᵥ + d_w)`: with weights `λᵥ (1 − D/S)` on `v ∈ A` and
`λ_w λᵥ (sᵥ + d_w) / S` on `c(w, v)`, the combination is convex and equals `x`.

Nothing here is specific to games; it is Mathlib-shaped material kept in this
formalization's directory because the repository has no shared extension library.
-/

open Finset Set
open scoped Pointwise

namespace SafeParetoImprovements

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A **polytope**: the convex hull of finitely many points. -/
def IsPolytope (s : Set E) : Prop := ∃ V : Set E, V.Finite ∧ s = convexHull ℝ V

namespace IsPolytope

lemma of_finite {s : Set E} (hs : s.Finite) : IsPolytope (convexHull ℝ s) := ⟨s, hs, rfl⟩

lemma singleton (x : E) : IsPolytope ({x} : Set E) :=
  ⟨{x}, finite_singleton x, (convexHull_singleton x).symm⟩

lemma zero : IsPolytope (0 : Set E) := by
  rw [← Set.singleton_zero]; exact singleton 0

lemma smul {s : Set E} (hs : IsPolytope s) (c : ℝ) : IsPolytope (c • s) := by
  obtain ⟨V, hV, rfl⟩ := hs
  exact ⟨c • V, hV.smul_set, (convexHull_smul c V).symm⟩

lemma add {s t : Set E} (hs : IsPolytope s) (ht : IsPolytope t) : IsPolytope (s + t) := by
  obtain ⟨V, hV, rfl⟩ := hs
  obtain ⟨W, hW, rfl⟩ := ht
  exact ⟨V + W, hV.add hW, (convexHull_add V W).symm⟩

lemma finsetSum {ι : Type*} (I : Finset ι) {f : ι → Set E} (hf : ∀ i ∈ I, IsPolytope (f i)) :
    IsPolytope (∑ i ∈ I, f i) :=
  Finset.sum_induction _ IsPolytope (fun _ _ => add) zero hf

lemma convex {s : Set E} (hs : IsPolytope s) : Convex ℝ s := by
  obtain ⟨V, -, rfl⟩ := hs; exact convex_convexHull ℝ _

end IsPolytope

/-! ### Half-space sections -/

section halfspace

variable (ℓ : E →ₗ[ℝ] ℝ) (t : ℝ)

/-- The crossing point of the segment from `w` (below the hyperplane `ℓ = t`) to `v`
(on or above it). -/
noncomputable def crossing (w v : E) : E :=
  ((ℓ v - t) + (t - ℓ w))⁻¹ • ((ℓ v - t) • w + (t - ℓ w) • v)

variable {ℓ t}

lemma crossing_mem_segment {w v : E} (hw : ℓ w < t) (hv : t ≤ ℓ v) {s : Set E}
    (hs : Convex ℝ s) (hws : w ∈ s) (hvs : v ∈ s) : crossing ℓ t w v ∈ s := by
  have hpos : 0 < (ℓ v - t) + (t - ℓ w) := by linarith
  have := hs hws hvs (a := (ℓ v - t) / ((ℓ v - t) + (t - ℓ w)))
    (b := (t - ℓ w) / ((ℓ v - t) + (t - ℓ w))) (div_nonneg (by linarith) hpos.le)
    (div_nonneg (by linarith) hpos.le) (by field_simp)
  unfold crossing
  rw [smul_add, smul_smul, smul_smul]
  convert this using 2 <;> rw [div_eq_inv_mul]

lemma apply_crossing {w v : E} (hw : ℓ w < t) (hv : t ≤ ℓ v) : ℓ (crossing ℓ t w v) = t := by
  have hpos : 0 < (ℓ v - t) + (t - ℓ w) := by linarith
  unfold crossing
  rw [map_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- **A polytope cut by a half-space is a polytope.**  The section of `convexHull V` by
`{y | t ≤ ℓ y}` is the convex hull of the vertices on or above the hyperplane together
with the crossing points of the edges from the vertices below it to those above it. -/
lemma _root_.SafeParetoImprovements.IsPolytope.inter_halfspace {s : Set E} (hs : IsPolytope s)
    (ℓ : E →ₗ[ℝ] ℝ) (t : ℝ) : IsPolytope (s ∩ {y | t ≤ ℓ y}) := by
  classical
  obtain ⟨V₀, hV₀, rfl⟩ := hs
  set V : Finset E := hV₀.toFinset with hVdef
  have hVcoe : (V : Set E) = V₀ := hV₀.coe_toFinset
  set A : Finset E := V.filter fun v => t ≤ ℓ v with hAdef
  set B : Finset E := V.filter fun w => ℓ w < t with hBdef
  set cr : E × E → E := fun p => crossing ℓ t p.1 p.2 with hcr
  set W : Set E := (A : Set E) ∪ cr '' ((B ×ˢ A : Finset (E × E)) : Set (E × E)) with hWdef
  have hAW : ∀ v ∈ A, v ∈ convexHull ℝ W := fun v hv => subset_convexHull ℝ W (Or.inl hv)
  have hcrW : ∀ p ∈ B ×ˢ A, cr p ∈ convexHull ℝ W := fun p hp =>
    subset_convexHull ℝ W (Or.inr ⟨p, Finset.mem_coe.2 hp, rfl⟩)
  have hAV : ∀ v ∈ A, v ∈ V := fun v hv => (Finset.mem_filter.1 hv).1
  have hBV : ∀ w ∈ B, w ∈ V := fun w hw => (Finset.mem_filter.1 hw).1
  have hAt : ∀ v ∈ A, t ≤ ℓ v := fun v hv => (Finset.mem_filter.1 hv).2
  have hBt : ∀ w ∈ B, ℓ w < t := fun w hw => (Finset.mem_filter.1 hw).2
  refine ⟨W, (A.finite_toSet).union ((B ×ˢ A).finite_toSet.image _), Subset.antisymm ?_ ?_⟩
  · -- ⊆ : route the mass below the hyperplane through the crossing points
    rintro x ⟨hx, hxt⟩
    rw [← hVcoe, Finset.mem_convexHull'] at hx
    obtain ⟨lam, hlam0, hlam1, hlamx⟩ := hx
    simp only [mem_setOf_eq] at hxt
    -- the split of `V` into `A` and `B`
    have hsplit : ∀ f : E → ℝ, ∑ y ∈ V, f y = ∑ v ∈ A, f v + ∑ w ∈ B, f w := by
      intro f
      rw [hAdef, hBdef, ← Finset.sum_filter_add_sum_filter_not V (fun v => t ≤ ℓ v)]
      congr 1
      exact Finset.sum_congr (Finset.filter_congr fun _ _ => not_le) fun _ _ => rfl
    have hsplitE : ∀ f : E → E, ∑ y ∈ V, f y = ∑ v ∈ A, f v + ∑ w ∈ B, f w := by
      intro f
      rw [hAdef, hBdef, ← Finset.sum_filter_add_sum_filter_not V (fun v => t ≤ ℓ v)]
      congr 1
      exact Finset.sum_congr (Finset.filter_congr fun _ _ => not_le) fun _ _ => rfl
    set S : ℝ := ∑ v ∈ A, lam v * (ℓ v - t) with hSdef
    set D : ℝ := ∑ w ∈ B, lam w * (t - ℓ w) with hDdef
    set ΛA : ℝ := ∑ v ∈ A, lam v with hΛA
    set XA : E := ∑ v ∈ A, lam v • v with hXA
    set XB : E := ∑ w ∈ B, lam w • w with hXB
    have hx : x = XA + XB := by rw [← hlamx, hsplitE]
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun v hv =>
      mul_nonneg (hlam0 v (hAV v hv)) (sub_nonneg.2 (hAt v hv))
    have hD0 : 0 ≤ D := Finset.sum_nonneg fun w hw =>
      mul_nonneg (hlam0 w (hBV w hw)) (sub_nonneg.2 (hBt w hw).le)
    -- `ℓ x ≥ t` says `D ≤ S`
    have hDS : D ≤ S := by
      have hℓx : ℓ x = t + S - D := by
        rw [← hlamx, map_sum, hsplit (fun y => ℓ (lam y • y))]
        simp only [map_smul, smul_eq_mul, hSdef, hDdef]
        have h1 : ∑ v ∈ A, lam v * ℓ v = ∑ v ∈ A, (lam v * t + lam v * (ℓ v - t)) :=
          Finset.sum_congr rfl fun v _ => by ring
        have h2 : ∑ w ∈ B, lam w * ℓ w = ∑ w ∈ B, (lam w * t - lam w * (t - ℓ w)) :=
          Finset.sum_congr rfl fun w _ => by ring
        rw [h1, h2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.sum_mul]
        have h3 : ∑ v ∈ A, lam v + ∑ w ∈ B, lam w = 1 := by rw [← hsplit, hlam1]
        linear_combination (t : ℝ) * h3
      linarith
    by_cases hD : D = 0
    · -- no mass below the hyperplane: every `w ∈ B` has weight `0`
      have hB0 : ∀ w ∈ B, lam w = 0 := by
        intro w hw
        have := (Finset.sum_eq_zero_iff_of_nonneg fun w hw =>
          mul_nonneg (hlam0 w (hBV w hw)) (sub_nonneg.2 (hBt w hw).le)).1 hD w hw
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h (sub_ne_zero.2 (hBt w hw).ne')
      have hXB0 : XB = 0 := Finset.sum_eq_zero fun w hw => by rw [hB0 w hw, zero_smul]
      have hΛA1 : ΛA = 1 := by
        have h3 : ∑ v ∈ A, lam v + ∑ w ∈ B, lam w = 1 := by rw [← hsplit, hlam1]
        rw [Finset.sum_eq_zero hB0, add_zero] at h3
        exact h3
      rw [hx, hXB0, add_zero]
      exact (convex_convexHull ℝ W).sum_mem (fun v hv => hlam0 v (hAV v hv)) hΛA1 hAW
    · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hD)
      have hSpos : 0 < S := lt_of_lt_of_le hDpos hDS
      set ρ : ℝ := D / S with hρ
      have hρ0 : 0 ≤ ρ := div_nonneg hD0 hS0
      have hρ1 : ρ ≤ 1 := (div_le_one hSpos).2 hDS
      -- the routed combination
      set wt : E ⊕ (E × E) → ℝ :=
        Sum.elim (fun v => lam v * (1 - ρ)) (fun p => lam p.1 * lam p.2 * ((ℓ p.2 - t) + (t - ℓ p.1)) / S)
      set pt : E ⊕ (E × E) → E := Sum.elim id cr
      have key : ∑ i ∈ A.disjSum (B ×ˢ A), wt i • pt i = x := by
        rw [Finset.sum_disjSum]
        simp only [wt, pt, Sum.elim_inl, Sum.elim_inr, id]
        -- the pair sum routes each `w ∈ B` to `w` plus a share of `XA`
        have hpair : ∑ p ∈ B ×ˢ A, (lam p.1 * lam p.2 * ((ℓ p.2 - t) + (t - ℓ p.1)) / S) • cr p =
            XB + ρ • XA := by
          rw [Finset.sum_product]
          have hinner : ∀ w ∈ B, ∑ v ∈ A, (lam w * lam v * ((ℓ v - t) + (t - ℓ w)) / S) • cr (w, v) =
              lam w • w + (lam w * (t - ℓ w) / S) • XA := by
            intro w hw
            have hterm : ∀ v ∈ A, (lam w * lam v * ((ℓ v - t) + (t - ℓ w)) / S) • cr (w, v) =
                (lam w / S * (lam v * (ℓ v - t))) • w +
                  (lam w * (t - ℓ w) / S) • (lam v • v) := by
              intro v hv
              have hpos : (ℓ v - t) + (t - ℓ w) ≠ 0 := by linarith [hAt v hv, hBt w hw]
              simp only [hcr, crossing, smul_add, smul_smul]
              congr 2
              · field_simp
              · field_simp
            rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_smul,
              ← Finset.smul_sum, ← hXA, ← Finset.mul_sum, ← hSdef, div_mul_cancel₀ _ hSpos.ne']
          rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← hXB, ← Finset.sum_smul,
            ← Finset.sum_div, ← hDdef]
        rw [hpair, hx]
        -- `∑_A λᵥ (1 − ρ) • v = (1 − ρ) • XA`
        have hA' : ∑ v ∈ A, (lam v * (1 - ρ)) • v = (1 - ρ) • XA := by
          rw [hXA, Finset.smul_sum]
          exact Finset.sum_congr rfl fun v _ => by rw [smul_smul, mul_comm]
        rw [hA', sub_smul, one_smul]
        abel
      rw [← key]
      refine (convex_convexHull ℝ W).sum_mem ?_ ?_ ?_
      · intro i hi
        rcases i with v | p
        · simp only [wt, Sum.elim_inl]
          exact mul_nonneg (hlam0 v (hAV v (Finset.mem_disjSum.1 hi |> fun h => by
            rcases h with ⟨_, hv, hh⟩ | ⟨_, _, hh⟩ <;> cases hh; exact hv))) (sub_nonneg.2 hρ1)
        · simp only [wt, Sum.elim_inr]
          obtain ⟨hp1, hp2⟩ : p.1 ∈ B ∧ p.2 ∈ A := by
            rcases Finset.mem_disjSum.1 hi with ⟨_, _, hh⟩ | ⟨q, hq, hh⟩
            · cases hh
            · cases hh; exact Finset.mem_product.1 hq
          have h1 : 0 ≤ (ℓ p.2 - t) + (t - ℓ p.1) := by linarith [hAt _ hp2, hBt _ hp1]
          exact div_nonneg (mul_nonneg (mul_nonneg (hlam0 _ (hBV _ hp1)) (hlam0 _ (hAV _ hp2))) h1)
            hS0
      · -- the weights sum to `1`
        rw [Finset.sum_disjSum]
        simp only [wt, Sum.elim_inl, Sum.elim_inr]
        have hpairw : ∑ p ∈ B ×ˢ A, lam p.1 * lam p.2 * ((ℓ p.2 - t) + (t - ℓ p.1)) / S =
            (∑ w ∈ B, lam w) + ρ * ΛA := by
          rw [Finset.sum_product]
          have hinner : ∀ w ∈ B, ∑ v ∈ A, lam w * lam v * ((ℓ v - t) + (t - ℓ w)) / S =
              lam w + lam w * (t - ℓ w) / S * ΛA := by
            intro w _
            have hterm : ∀ v ∈ A, lam w * lam v * ((ℓ v - t) + (t - ℓ w)) / S =
                lam w / S * (lam v * (ℓ v - t)) + lam w * (t - ℓ w) / S * lam v := by
              intro v _; field_simp
            rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← hSdef, ← hΛA, div_mul_cancel₀ _ hSpos.ne']
          rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.sum_mul,
            ← Finset.sum_div, ← hDdef]
        rw [hpairw, ← Finset.sum_mul, ← hΛA]
        have h3 : ΛA + ∑ w ∈ B, lam w = 1 := by rw [hΛA, ← hsplit, hlam1]
        linear_combination h3
      · intro i hi
        rcases i with v | p
        · simp only [pt, Sum.elim_inl, id]
          exact hAW v (by
            rcases Finset.mem_disjSum.1 hi with ⟨_, hv, hh⟩ | ⟨_, _, hh⟩ <;> cases hh; exact hv)
        · simp only [pt, Sum.elim_inr]
          exact hcrW p (by
            rcases Finset.mem_disjSum.1 hi with ⟨_, _, hh⟩ | ⟨q, hq, hh⟩ <;> cases hh; exact hq)
  · -- ⊇ : the generators lie in the section, which is convex
    refine convexHull_min ?_ ((convex_convexHull ℝ _).inter (convex_halfSpace_ge ℓ.isLinear t))
    rintro y (hy | ⟨p, hp, rfl⟩)
    · exact ⟨subset_convexHull ℝ _ (by rw [← hVcoe]; exact Finset.mem_coe.2 (hAV y hy)),
        hAt y hy⟩
    · have hp' := Finset.mem_product.1 (Finset.mem_coe.1 hp)
      refine ⟨crossing_mem_segment (hBt _ hp'.1) (hAt _ hp'.2) (convex_convexHull ℝ _) ?_ ?_,
        (apply_crossing (hBt _ hp'.1) (hAt _ hp'.2)).ge⟩
      · exact subset_convexHull ℝ _ (by rw [← hVcoe]; exact Finset.mem_coe.2 (hBV _ hp'.1))
      · exact subset_convexHull ℝ _ (by rw [← hVcoe]; exact Finset.mem_coe.2 (hAV _ hp'.2))

end halfspace

/-- A polytope in a finite product of lines cut by an orthant `{y | c ≤ y}` is a polytope:
iterate the half-space section over the coordinates. -/
lemma IsPolytope.inter_Ici {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)} (hs : IsPolytope s)
    (c : ι → ℝ) : IsPolytope (s ∩ Ici c) := by
  classical
  have key : ∀ T : Finset ι, IsPolytope (s ∩ {y | ∀ i ∈ T, c i ≤ y i}) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using hs
    | insert i T hi ih =>
      have : s ∩ {y | ∀ j ∈ insert i T, c j ≤ y j} =
          (s ∩ {y | ∀ j ∈ T, c j ≤ y j}) ∩ {y | c i ≤ LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i y} := by
        ext y
        simp only [mem_inter_iff, mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp,
          LinearMap.proj_apply]
        tauto
      rw [this]
      exact ih.inter_halfspace _ _
  have : Ici c = {y | ∀ i ∈ (Finset.univ : Finset ι), c i ≤ y i} := by
    ext y; simp [Pi.le_def]
  rw [this]
  exact key _

end SafeParetoImprovements
