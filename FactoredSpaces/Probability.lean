import FactoredSpaces.Independence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.BigOperators.Field

/-!
# The finite-probability substrate (§4.1, §6, Appendix C.0–C.1)

Distributions on a finite type are elementary mass functions (`Distr`, `dd:dist`);
distributions that factorize over the factored space (Definition 4.3), factored space
models (Definition 4.4), conditional independence in the paper's product form
(Definition 6.1), outer products and marginals (Definitions C.1, C.2), supports, delta
distributions, and the interpolation `R^λ = ⨂ ((1−λ)Q_i + λP_i)` used by Lemmas C.5,
C.10 and 6.5.  The Appendix-C bookkeeping lemmas that involve no history — C.11, C.13,
C.14, C.15, C.16, C.17 — live here too.
-/

namespace FactoredSpaces

open Finset

universe u v w w' w''

/-! ## Distributions on a finite type -/

/-- A probability distribution on a finite type `S`, as its mass function
(`dd:dist`).  `prob P A = ∑_{s ∈ A} P(s)` is the probability of an event. -/
@[ext]
structure Distr (S : Type w) [Fintype S] where
  /-- The mass `P(s)` of a point. -/
  mass : S → ℝ
  nonneg : ∀ s, 0 ≤ mass s
  sum_eq_one : ∑ s, mass s = 1

namespace Distr

variable {S : Type w} {T : Type w'} [Fintype S] [Fintype T]

/-- The probability `P(A) = ∑_{s ∈ A} P(s)` of an event `A ⊆ S`. -/
noncomputable def prob (P : Distr S) (A : Set S) : ℝ := ∑ s, A.indicator P.mass s

/-- The distributions on `S` — the paper's `Δ(S)`. -/
abbrev all (S : Type w) [Fintype S] : Set (Distr S) := Set.univ

instance [Nonempty S] : Nonempty (Distr S) := by
  classical
  obtain ⟨s⟩ := ‹Nonempty S›
  exact ⟨⟨fun t => if t = s then 1 else 0, fun t => by split_ifs <;> norm_num, by simp⟩⟩

lemma prob_nonneg (P : Distr S) (A : Set S) : 0 ≤ P.prob A :=
  Finset.sum_nonneg fun s _ => Set.indicator_nonneg (fun t _ => P.nonneg t) s

lemma prob_univ (P : Distr S) : P.prob Set.univ = 1 := by
  simp [prob, P.sum_eq_one]

lemma prob_empty (P : Distr S) : P.prob ∅ = 0 := by simp [prob]

lemma prob_mono (P : Distr S) {A B : Set S} (h : A ⊆ B) : P.prob A ≤ P.prob B :=
  Finset.sum_le_sum fun s _ => Set.indicator_le_indicator_of_subset h (P.nonneg) s

lemma prob_le_one (P : Distr S) (A : Set S) : P.prob A ≤ 1 :=
  P.prob_univ ▸ P.prob_mono (Set.subset_univ A)

lemma prob_union_of_disjoint (P : Distr S) {A B : Set S} (h : Disjoint A B) :
    P.prob (A ∪ B) = P.prob A + P.prob B := by
  simp only [prob, Set.indicator_union_of_disjoint h, Finset.sum_add_distrib]

lemma prob_singleton (P : Distr S) (s : S) : P.prob {s} = P.mass s := by
  classical
  simp [prob, Set.indicator_apply, Finset.sum_ite_eq']

lemma prob_eq_sum_filter (P : Distr S) (A : Set S) [DecidablePred (· ∈ A)] :
    P.prob A = ∑ s ∈ Finset.univ.filter (· ∈ A), P.mass s := by
  simp only [prob, Set.indicator_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero]

lemma prob_eq_sum_subtype (P : Distr S) (A : Set S) [Fintype A] :
    P.prob A = ∑ s : A, P.mass s := by
  classical
  rw [prob_eq_sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The support `supp(P) = {s | P(s) > 0}` (§C.3). -/
def support (P : Distr S) : Set S := {s | 0 < P.mass s}

lemma mem_support_iff (P : Distr S) (s : S) : s ∈ P.support ↔ 0 < P.mass s := Iff.rfl

lemma prob_pos_iff (P : Distr S) (A : Set S) : 0 < P.prob A ↔ (A ∩ P.support).Nonempty := by
  classical
  constructor
  · intro h
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hzero : ∀ s ∈ (Finset.univ : Finset S), A.indicator P.mass s = 0 := by
      intro s _
      by_cases hs : s ∈ A
      · have hns : s ∉ P.support := fun hsp => by
          simpa [hne] using (Set.mem_inter hs hsp)
        have hle : P.mass s ≤ 0 := not_lt.mp hns
        simp [hs, le_antisymm hle (P.nonneg s)]
      · simp [hs]
    rw [prob, Finset.sum_congr rfl hzero, Finset.sum_const_zero] at h
    exact lt_irrefl 0 h
  · rintro ⟨s, hsA, hsp⟩
    refine Finset.sum_pos' (fun t _ => Set.indicator_nonneg (fun u _ => P.nonneg u) t)
      ⟨s, Finset.mem_univ s, ?_⟩
    rw [Set.indicator_of_mem hsA]
    exact hsp

lemma prob_eq_zero_iff (P : Distr S) (A : Set S) : P.prob A = 0 ↔ Disjoint A P.support := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty, ← prob_pos_iff,
    not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h (P.prob_nonneg A)⟩

lemma prob_support (P : Distr S) : P.prob P.support = 1 := by
  classical
  rw [prob, ← P.sum_eq_one]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s ∈ P.support
  · simp [hs]
  · have hle : P.mass s ≤ 0 := not_lt.mp hs
    simp [hs, le_antisymm hle (P.nonneg s)]

/-- The conditional probability `P(A | C) = P(A ∩ C) / P(C)` (`0` when `P(C) = 0`,
by Lean's convention for division; the paper only uses it when `P(C) > 0`). -/
noncomputable def condProb (P : Distr S) (A C : Set S) : ℝ := P.prob (A ∩ C) / P.prob C

/-- `P` is strictly positive: every point has positive mass. -/
def StrictlyPositive (P : Distr S) : Prop := ∀ s, 0 < P.mass s

/-- The pushforward `P ∘ f⁻¹` of `P` along `f : S → T`. -/
noncomputable def map (f : S → T) (P : Distr S) : Distr T where
  mass t := P.prob (f ⁻¹' {t})
  nonneg t := P.prob_nonneg _
  sum_eq_one := by
    classical
    simp only [prob, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_comm]
    simpa using P.sum_eq_one

lemma map_mass (f : S → T) (P : Distr S) (t : T) : (P.map f).mass t = P.prob (f ⁻¹' {t}) := rfl

lemma map_prob (f : S → T) (P : Distr S) (B : Set T) : (P.map f).prob B = P.prob (f ⁻¹' B) := by
  classical
  simp only [prob, map, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  have h : ∀ t : T, (if t ∈ B then (∑ s, if f s = t then P.mass s else 0) else 0)
      = ∑ s, (if f s = t then (if f s ∈ B then P.mass s else 0) else 0) := by
    intro t
    by_cases ht : t ∈ B
    · simp only [ht, if_true]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : f s = t <;> simp [hs, ht]
    · simp only [ht, if_false]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      by_cases hs : f s = t <;> simp [hs, ht]
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_comm]
  simp

lemma map_map {U : Type w''} [Fintype U] (f : S → T) (g : T → U) (P : Distr S) :
    (P.map f).map g = P.map (g ∘ f) := by
  ext u
  simp [map_mass, map_prob, Set.preimage_comp]

/-- Pushing forward along a bijection just relabels the mass. -/
lemma map_equiv_mass (e : S ≃ T) (P : Distr S) (t : T) : (P.map e).mass t = P.mass (e.symm t) := by
  rw [map_mass]
  have h : (e : S → T) ⁻¹' {t} = {e.symm t} := by
    ext s; simp [Equiv.eq_symm_apply]
  rw [h, prob_singleton]

open scoped Classical in
/-- The delta distribution `δ_s` at a point (§C.3). -/
noncomputable def delta (s : S) : Distr S where
  mass t := if t = s then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  sum_eq_one := by simp

open scoped Classical in
lemma delta_mass (s t : S) : (delta s).mass t = if t = s then 1 else 0 := rfl

open scoped Classical in
lemma delta_prob (s : S) (A : Set S) : (delta s).prob A = if s ∈ A then 1 else 0 := by
  classical
  simp only [prob, Set.indicator_apply, delta_mass]
  rw [Finset.sum_congr rfl (g := fun t => if t = s then (if s ∈ A then (1 : ℝ) else 0) else 0)
    fun t _ => by by_cases ht : t = s <;> simp [ht]]
  simp

lemma support_delta (s : S) : (delta s).support = {s} := by
  classical
  ext t
  simp only [support, Set.mem_setOf_eq, delta_mass, Set.mem_singleton_iff]
  by_cases ht : t = s <;> simp [ht]

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform [Nonempty S] : Distr S where
  mass _ := (Fintype.card S : ℝ)⁻¹
  nonneg _ := by positivity
  sum_eq_one := by
    simp [Finset.sum_const, Finset.card_univ]

lemma uniform_strictlyPositive [Nonempty S] : (uniform : Distr S).StrictlyPositive := fun _ =>
  inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

/-- The convex combination `(1 − t)·P + t·Q` for `t ∈ [0, 1]` — the paper's
`R^λ_i = (1−λ)Q_i + λP_i` is `mix λ Q_i P_i`. -/
noncomputable def mix (t : unitInterval) (P Q : Distr S) : Distr S where
  mass s := (1 - (t : ℝ)) * P.mass s + (t : ℝ) * Q.mass s
  nonneg s := by
    have h0 := t.2.1; have h1 := t.2.2
    have := P.nonneg s; have := Q.nonneg s
    nlinarith
  sum_eq_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, P.sum_eq_one, Q.sum_eq_one]
    ring

lemma mix_zero (P Q : Distr S) : mix 0 P Q = P := by
  ext s; simp [mix]

lemma mix_one (P Q : Distr S) : mix 1 P Q = Q := by
  ext s; simp [mix]

/-- The Euclidean distance between two distributions, viewing `Δ(S) ⊆ ℝ^S` (§6.2). -/
noncomputable def euclDist (P Q : Distr S) : ℝ := √(∑ s, (P.mass s - Q.mass s) ^ 2)

end Distr

/-! ## Distributions on a factored space -/

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]

/-- The product `⨂_{i∈I} p_i` of one distribution per factor: `ω ↦ ∏_i p_i(ω_i)`. -/
noncomputable def Distr.prod (p : ∀ i, Distr (Ω i)) : Distr (Pt Ω) where
  mass ω := ∏ i, (p i).mass (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (p i).nonneg _
  sum_eq_one := by
    rw [← Fintype.prod_sum]
    simp [Distr.sum_eq_one]

lemma Distr.prod_mass (p : ∀ i, Distr (Ω i)) (ω : Pt Ω) :
    (Distr.prod p).mass ω = ∏ i, (p i).mass (ω i) := rfl

/-- The paper's `P(ω_i) := P(π_i⁻¹(ω_i))`: the marginal of `P` on the `i`-th factor,
`P_i = P ∘ U_i⁻¹` (Definition C.2 at `J = {i}`). -/
noncomputable abbrev Distr.margAt (P : Distr (Pt Ω)) (i : I) : Distr (Ω i) := P.map (bg i)

/-- **Factorizing distribution.** `P` factorizes over `Ω` if `P(ω) = ∏_{i∈I} P(ω_i)`
for all `ω`, where `P(ω_i) = P(π_i⁻¹(ω_i))`.

Paper node: Definition 4.3 (§4.1). -/
def Factorizes (P : Distr (Pt Ω)) : Prop :=
  ∀ ω : Pt Ω, P.mass ω = ∏ i, (P.margAt i).mass (ω i)

/-- The set `Δ^F(Ω)` of distributions that factorize over `Ω`. -/
def factorizing (Ω : I → Type v) [∀ i, Fintype (Ω i)] : Set (Distr (Pt Ω)) :=
  {P | Factorizes P}

lemma mem_factorizing {P : Distr (Pt Ω)} : P ∈ factorizing Ω ↔ Factorizes P := Iff.rfl

omit [∀ i, Fintype (Ω i)] in
/-- A product over `I` splits off the factor at `i`. -/
private lemma prod_split_at (i : I) (f : ∀ j, Ω j → ℝ) (ω : Pt Ω) :
    ∏ j, f j (ω j) = f i (ω i) * ∏ j : {j : I // j ≠ i}, f j (ω j) := by
  classical
  rw [← Finset.prod_subtype (Finset.univ.erase i) (fun j => by simp) fun j => f j (ω j)]
  exact (Finset.mul_prod_erase Finset.univ (fun j => f j (ω j)) (Finset.mem_univ i)).symm

/-- The marginal on factor `i` of a product is the `i`-th component. -/
lemma Distr.margAt_prod (p : ∀ i, Distr (Ω i)) (i : I) : (Distr.prod p).margAt i = p i := by
  classical
  ext x
  have h0 : ((Distr.prod p).margAt i).mass x
      = ∑ ω : Pt Ω, (if ω i = x then ∏ j, (p j).mass (ω j) else 0) := by
    simp only [Distr.margAt, Distr.map_mass, Distr.prob, Set.indicator_apply, Set.mem_preimage,
      Set.mem_singleton_iff, Distr.prod_mass, bg]
  have hone : ∑ g : (∀ j : {j : I // j ≠ i}, Ω j), ∏ j : {j : I // j ≠ i}, (p j).mass (g j)
      = 1 := by
    rw [← Fintype.prod_sum]
    simp [Distr.sum_eq_one]
  have hstep := Fintype.sum_equiv (Equiv.piSplitAt i Ω)
    (fun ω : Pt Ω => if ω i = x then ∏ j, (p j).mass (ω j) else 0)
    (fun q : Ω i × (∀ j : {j : I // j ≠ i}, Ω j) =>
      if q.1 = x then (p i).mass q.1 * ∏ j : {j : I // j ≠ i}, (p j).mass (q.2 j) else 0)
    (fun ω => by
      show (if ω i = x then ∏ j, (p j).mass (ω j) else 0)
          = (if ω i = x then
              (p i).mass (ω i) * ∏ j : {j : I // j ≠ i}, (p j).mass (ω j) else 0)
      rw [prod_split_at i (fun j => (p j).mass) ω])
  rw [h0, hstep, Fintype.sum_prod_type]
  have hinner : ∀ a : Ω i,
      (∑ g : (∀ j : {j : I // j ≠ i}, Ω j),
        if a = x then (p i).mass a * ∏ j : {j : I // j ≠ i}, (p j).mass (g j) else 0)
        = if a = x then (p i).mass a else 0 := by
    intro a
    by_cases ha : a = x
    · rw [if_pos ha]
      calc (∑ g : (∀ j : {j : I // j ≠ i}, Ω j),
              if a = x then (p i).mass a * ∏ j : {j : I // j ≠ i}, (p j).mass (g j) else 0)
          = ∑ g : (∀ j : {j : I // j ≠ i}, Ω j),
              (p i).mass a * ∏ j : {j : I // j ≠ i}, (p j).mass (g j) := by simp [ha]
        _ = (p i).mass a := by rw [← Finset.mul_sum, hone, mul_one]
    · simp [ha]
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  simp

lemma factorizes_prod (p : ∀ i, Distr (Ω i)) : Factorizes (Distr.prod p) := by
  intro ω
  simp only [Distr.margAt_prod, Distr.prod_mass]

lemma Factorizes.eq_prod_margAt {P : Distr (Pt Ω)} (h : Factorizes P) :
    P = Distr.prod fun i => P.margAt i := by
  ext ω
  exact h ω

/-- The remark after Definition C.2: `P` factorizes iff it is the outer product of its
one-factor marginals, `P = ⨂_{i∈I} P_i`. -/
lemma factorizes_iff_exists_prod (P : Distr (Pt Ω)) :
    Factorizes P ↔ ∃ p : ∀ i, Distr (Ω i), P = Distr.prod p := by
  constructor
  · exact fun h => ⟨_, h.eq_prod_margAt⟩
  · rintro ⟨p, rfl⟩
    exact factorizes_prod p

/-- The set `Δ^F_C(Ω)` of factorizing distributions with `P(C) > 0` (§C.3). -/
def factorizingPos (C : Set (Pt Ω)) : Set (Distr (Pt Ω)) :=
  {P | Factorizes P ∧ 0 < P.prob C}

/-- **Factored space model.** `(Ω, O)` is a factored space model for a distribution `P`
on the observation space `Obs` if some distribution `P^Ω` factorizing over `Ω` has
`P^Ω(O = o) = P(o)` for all `o ∈ Obs`.  The model is the pair of the ambient factored
space `(I, Ω)` and the observation variable `O` (`dd:pi-space`).

Paper node: Definition 4.4 (§4.1). -/
def IsFactoredSpaceModel {Obs : Type w} [Fintype Obs] (O : Pt Ω → Obs) (P : Distr Obs) : Prop :=
  ∃ PΩ : Distr (Pt Ω), Factorizes PΩ ∧ ∀ o : Obs, PΩ.prob (fiber O o) = P.mass o

/-! ## Marginals, cylinders and outer products (Definitions C.1, C.2) -/

/-- **Marginal distribution.** `P_J = P ∘ U_J⁻¹`, a distribution on `Ω_J`.

Paper node: Definition C.2 (§C). -/
noncomputable def Distr.marg (P : Distr (Pt Ω)) (J : Finset I) : Distr (PtOn Ω J) := P.map (proj J)

lemma Distr.marg_mass (P : Distr (Pt Ω)) (J : Finset I) (α : PtOn Ω J) :
    (P.marg J).mass α = P.prob (proj J ⁻¹' {α}) := rfl

/-- Restriction of a family over `K` to a subset `J ⊆ K`. -/
def restrict {J K : Finset I} (h : J ⊆ K) (α : PtOn Ω K) : PtOn Ω J := fun i => α ⟨i, h i.2⟩

/-- The bridge between the two encodings of `Ω = Ω_J × Ω_{I∖J}` (`dd:splice`). -/
def splitEquiv (J : Finset I) : Pt Ω ≃ PtOn Ω J × PtOn Ω Jᶜ where
  toFun ω := (proj J ω, proj Jᶜ ω)
  invFun p i := if h : i ∈ J then p.1 ⟨i, h⟩ else p.2 ⟨i, Finset.mem_compl.mpr h⟩
  left_inv ω := by
    funext i
    by_cases h : i ∈ J <;> simp [proj, h]
  right_inv p := by
    ext ⟨i, hi⟩
    · simp [proj, hi]
    · simp [proj, Finset.mem_compl.mp hi]

omit [∀ i, Fintype (Ω i)] in
@[simp] lemma proj_splitEquiv_symm (J : Finset I) (α : PtOn Ω J) (β : PtOn Ω Jᶜ) :
    proj J ((splitEquiv J).symm (α, β)) = α :=
  congrArg Prod.fst ((splitEquiv J).apply_symm_apply (α, β))

omit [∀ i, Fintype (Ω i)] in
@[simp] lemma proj_compl_splitEquiv_symm (J : Finset I) (α : PtOn Ω J) (β : PtOn Ω Jᶜ) :
    proj Jᶜ ((splitEquiv J).symm (α, β)) = β :=
  congrArg Prod.snd ((splitEquiv J).apply_symm_apply (α, β))

omit [∀ i, Fintype (Ω i)] in
lemma splitEquiv_symm_proj (J : Finset I) (ω : Pt Ω) :
    (splitEquiv J).symm (proj J ω, proj Jᶜ ω) = ω :=
  (splitEquiv J).symm_apply_apply ω

/-- `Ω_{J ∪ K} = Ω_J × Ω_K` for disjoint `J`, `K`: the dependent-subtype transport behind
Definition C.1. -/
def unionEquiv {J K : Finset I} (h : Disjoint J K) :
    PtOn Ω (J ∪ K) ≃ PtOn Ω J × PtOn Ω K where
  toFun α := (restrict Finset.subset_union_left α, restrict Finset.subset_union_right α)
  invFun q i := if hi : (i : I) ∈ J then q.1 ⟨i, hi⟩
    else q.2 ⟨i, (Finset.mem_union.mp i.2).resolve_left hi⟩
  left_inv α := by
    funext i
    by_cases hi : (i : I) ∈ J <;> simp [restrict, hi]
  right_inv q := by
    ext ⟨i, hi⟩
    · simp [restrict, hi]
    · have hnJ : i ∉ J := fun hc => Finset.disjoint_left.mp h hc hi
      simp [restrict, hnJ]

/-- Summing over `Ω` is summing over `Ω_J × Ω_{I∖J}` (`dd:splice`). -/
private lemma sum_eq_sum_split (J : Finset I) (F : Pt Ω → ℝ) :
    ∑ ω : Pt Ω, F ω
      = ∑ α : PtOn Ω J, ∑ β : PtOn Ω Jᶜ, F ((splitEquiv J).symm (α, β)) :=
  calc ∑ ω : Pt Ω, F ω
      = ∑ q : PtOn Ω J × PtOn Ω Jᶜ, F ((splitEquiv J).symm q) :=
        Fintype.sum_equiv (splitEquiv J) _ _ fun ω => by rw [Equiv.symm_apply_apply]
    _ = _ := Fintype.sum_prod_type _

omit [∀ i, Fintype (Ω i)] in
/-- A product over `I` splits as a product over `J` times a product over `I ∖ J`. -/
private lemma prod_split (J : Finset I) (f : ∀ i, Ω i → ℝ) (α : PtOn Ω J) (β : PtOn Ω Jᶜ) :
    ∏ i, f i ((splitEquiv J).symm (α, β) i)
      = (∏ i : J, f i (α i)) * ∏ i : (Jᶜ : Finset I), f i (β i) := by
  classical
  rw [← Finset.prod_mul_prod_compl J fun i => f i ((splitEquiv J).symm (α, β) i)]
  congr 1
  · rw [← Finset.prod_coe_sort J]
    exact Finset.prod_congr rfl fun i _ => by simp [splitEquiv, i.2]
  · rw [← Finset.prod_coe_sort Jᶜ]
    exact Finset.prod_congr rfl fun i _ => by
      simp [splitEquiv, Finset.mem_compl.mp i.2]

lemma Distr.prob_eq_sum_split (P : Distr (Pt Ω)) (J : Finset I) (A : Set (Pt Ω)) :
    P.prob A = ∑ α : PtOn Ω J, ∑ β : PtOn Ω Jᶜ,
      A.indicator P.mass ((splitEquiv J).symm (α, β)) :=
  sum_eq_sum_split J _

lemma Distr.marg_mass_eq_sum (P : Distr (Pt Ω)) (J : Finset I) (α : PtOn Ω J) :
    (P.marg J).mass α = ∑ β : PtOn Ω Jᶜ, P.mass ((splitEquiv J).symm (α, β)) := by
  classical
  rw [marg_mass, prob_eq_sum_split P J]
  have key : ∀ α' : PtOn Ω J,
      (∑ β : PtOn Ω Jᶜ, (proj J ⁻¹' {α}).indicator P.mass ((splitEquiv J).symm (α', β)))
        = if α' = α then ∑ β : PtOn Ω Jᶜ, P.mass ((splitEquiv J).symm (α', β)) else 0 := by
    intro α'
    by_cases h : α' = α
    · subst h
      rw [if_pos rfl]
      exact Finset.sum_congr rfl fun β _ => Set.indicator_of_mem (by simp) _
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun β _ => Set.indicator_of_notMem (by simp [h]) _
  rw [Finset.sum_congr rfl fun α' _ => key α']
  simp

/-- **Outer product.** For disjoint `J`, `K` and distributions `P_J`, `P_K` on `Ω_J`,
`Ω_K`, the distribution `P_J ⊗ P_K` on `Ω_{J ∪ K}` with
`(P_J ⊗ P_K)(α) = P_J(α_J) · P_K(α_K)`.

Paper node: Definition C.1 (§C). -/
noncomputable def Distr.outer {J K : Finset I} (h : Disjoint J K) (PJ : Distr (PtOn Ω J))
    (PK : Distr (PtOn Ω K)) : Distr (PtOn Ω (J ∪ K)) where
  mass α := PJ.mass (restrict Finset.subset_union_left α) *
    PK.mass (restrict Finset.subset_union_right α)
  nonneg α := mul_nonneg (PJ.nonneg _) (PK.nonneg _)
  sum_eq_one := by
    have hsplit := Fintype.sum_equiv (unionEquiv h)
      (fun α : PtOn Ω (J ∪ K) => PJ.mass (restrict Finset.subset_union_left α) *
        PK.mass (restrict Finset.subset_union_right α))
      (fun q : PtOn Ω J × PtOn Ω K => PJ.mass q.1 * PK.mass q.2) fun _ => rfl
    rw [hsplit, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, PK.sum_eq_one, mul_one, PJ.sum_eq_one]

/-- `Ω_{J ∪ (I∖J)} = Ω`. -/
def unionComplEquiv (J : Finset I) : PtOn Ω (J ∪ Jᶜ) ≃ Pt Ω where
  toFun α i := α ⟨i, by simp⟩
  invFun ω i := ω i
  left_inv α := by funext i; rfl
  right_inv ω := by funext i; rfl

/-- The paper's `P_J ⊗ P_{I∖J}`, read as a distribution on `Ω` itself:
`ω ↦ P_J(ω_J) · P_{I∖J}(ω_{I∖J})` (`outerCompl_mass`).  This is the form every use of
Definition C.1 in the paper takes. -/
noncomputable def Distr.outerCompl {J : Finset I} (PJ : Distr (PtOn Ω J)) (PK : Distr (PtOn Ω Jᶜ)) :
    Distr (Pt Ω) :=
  (Distr.outer disjoint_compl_right PJ PK).map (unionComplEquiv J)

lemma Distr.outerCompl_mass {J : Finset I} (PJ : Distr (PtOn Ω J)) (PK : Distr (PtOn Ω Jᶜ))
    (ω : Pt Ω) : (Distr.outerCompl PJ PK).mass ω = PJ.mass (proj J ω) * PK.mass (proj Jᶜ ω) := by
  rw [Distr.outerCompl, Distr.map_equiv_mass]
  rfl

/-- The cylinder over a set of `J`-families: `π_J⁻¹(A)`.  The paper's `A_J × B_{I∖J}` for
`A ⊆ Ω_J`, `B ⊆ Ω_{I∖J}` is `cyl J A ∩ cyl Jᶜ B`. -/
def cyl (J : Finset I) (A : Set (PtOn Ω J)) : Set (Pt Ω) := proj J ⁻¹' A

omit [∀ i, Fintype (Ω i)] in
lemma splice_eq_cyl_inter (J : Finset I) (S T : Set (Pt Ω)) :
    splice J S T = cyl J (projSet J S) ∩ cyl Jᶜ (projSet Jᶜ T) := by
  ext ω
  rw [mem_splice_iff]
  simp only [cyl, projSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨⟨a, ha, hJa⟩, ⟨b, hb, hJb⟩⟩
    exact ⟨⟨a, ha, proj_eq_iff.mpr fun i hi => (hJa i hi).symm⟩,
      ⟨b, hb, proj_eq_iff.mpr fun i hi => (hJb i (Finset.mem_compl.mp hi)).symm⟩⟩
  · rintro ⟨⟨a, ha, hJa⟩, ⟨b, hb, hJb⟩⟩
    exact ⟨⟨a, ha, fun i hi => (congrFun hJa ⟨i, hi⟩).symm⟩,
      ⟨b, hb, fun i hi => (congrFun hJb ⟨i, Finset.mem_compl.mpr hi⟩).symm⟩⟩

omit [DecidableEq I] [Fintype I] [∀ i, Fintype (Ω i)] in
/-- Two cylinders over the same index set intersect as a cylinder. -/
lemma cyl_inter (J : Finset I) (S T : Set (PtOn Ω J)) :
    cyl J S ∩ cyl J T = cyl J (S ∩ T) := Set.preimage_inter.symm

/-- The marginal of a factorizing distribution factorizes over `Ω_J` in the same sense:
`P_J = ⨂_{i∈J} P_i` (remark after Definition C.2), stated pointwise. -/
lemma Factorizes.marg_mass {P : Distr (Pt Ω)} (h : Factorizes P) (J : Finset I) (α : PtOn Ω J) :
    (P.marg J).mass α = ∏ i : J, (P.margAt i).mass (α i) := by
  classical
  rw [Distr.marg_mass_eq_sum]
  have hterm : ∀ β : PtOn Ω Jᶜ, P.mass ((splitEquiv J).symm (α, β))
      = (∏ i : J, (P.margAt i).mass (α i)) *
        ∏ i : (Jᶜ : Finset I), (P.margAt i).mass (β i) := by
    intro β
    rw [h ((splitEquiv J).symm (α, β))]
    exact prod_split J (fun i => (P.margAt i).mass) α β
  rw [Finset.sum_congr rfl fun β _ => hterm β, ← Finset.mul_sum]
  have hone : ∑ β : PtOn Ω Jᶜ, ∏ i : (Jᶜ : Finset I), (P.margAt i).mass (β i) = 1 := by
    rw [← Fintype.prod_sum]
    simp [Distr.sum_eq_one]
  rw [hone, mul_one]

/-- If `P` factorizes over `Ω` then `P = P_J ⊗ P_{I∖J}` for every `J`
(the remark after Definition C.2). -/
lemma Factorizes.eq_outerCompl {P : Distr (Pt Ω)} (h : Factorizes P) (J : Finset I) :
    P = Distr.outerCompl (P.marg J) (P.marg Jᶜ) := by
  ext ω
  rw [Distr.outerCompl_mass, h.marg_mass J (proj J ω), h.marg_mass Jᶜ (proj Jᶜ ω), h ω]
  have hp := prod_split J (fun i => (P.margAt i).mass) (proj J ω) (proj Jᶜ ω)
  rw [splitEquiv_symm_proj] at hp
  exact hp

/-! ## Lemma C.11: supports -/

/-- **Support statements (1).** If `supp(P) ⊆ supp(Q)` and `P(C) > 0` then `Q(C) > 0`.

Paper node: Lemma C.11 (§C.3). -/
theorem Distr.prob_pos_of_support_subset {P Q : Distr (Pt Ω)} (h : P.support ⊆ Q.support)
    {C : Set (Pt Ω)} (hC : 0 < P.prob C) : 0 < Q.prob C := by
  rw [Distr.prob_pos_iff] at hC ⊢
  obtain ⟨ω, hωC, hωP⟩ := hC
  exact ⟨ω, hωC, h hωP⟩

/-- **Support statements (2).** If `P = P_J ⊗ P_{I∖J}` then
`supp(P) = supp(P_J) × supp(P_{I∖J})`.

Paper node: Lemma C.11 (§C.3). -/
theorem Distr.support_outerCompl {J : Finset I} (PJ : Distr (PtOn Ω J)) (PK : Distr (PtOn Ω Jᶜ)) :
    (Distr.outerCompl PJ PK).support = cyl J PJ.support ∩ cyl Jᶜ PK.support := by
  ext ω
  simp only [Distr.mem_support_iff, cyl, Set.mem_inter_iff, Set.mem_preimage,
    Distr.outerCompl_mass]
  constructor
  · intro hpos
    rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact ⟨h1, h2⟩
    · exact absurd h1 (not_lt.mpr (PJ.nonneg _))
  · rintro ⟨h1, h2⟩
    exact mul_pos h1 h2

/-- **Support statements (3).** If `P = P_J ⊗ P_{I∖J}`, `Q = Q_J ⊗ Q_{I∖J}`,
`supp(P_J) ⊆ supp(Q_J)`, `supp(P_{I∖J}) ⊆ supp(Q_{I∖J})` and `P(C) > 0`, then `Q(C) > 0`.

The paper states this with only `supp(P_J) ⊆ supp(Q_J)`, which is false (take `P = δ_ω`,
`Q = δ_{ω_J} ⊗ δ_β` with `β ≠ ω_{I∖J}`, `C = {ω}`); its proof, and its only use
(Lemma C.12), take `Q_{I∖J} = P_{I∖J}`, which the second support inclusion covers.  See
`notes/paper-errata.md`.

Paper node: Lemma C.11 (§C.3). -/
theorem Distr.prob_pos_of_marg_support_subset {J : Finset I} {P Q : Distr (Pt Ω)}
    (hP : P = Distr.outerCompl (P.marg J) (P.marg Jᶜ))
    (hQ : Q = Distr.outerCompl (Q.marg J) (Q.marg Jᶜ))
    (h₁ : (P.marg J).support ⊆ (Q.marg J).support)
    (h₂ : (P.marg Jᶜ).support ⊆ (Q.marg Jᶜ).support)
    {C : Set (Pt Ω)} (hC : 0 < P.prob C) : 0 < Q.prob C := by
  have hPs : P.support = cyl J (P.marg J).support ∩ cyl Jᶜ (P.marg Jᶜ).support := by
    conv_lhs => rw [hP]
    exact Distr.support_outerCompl _ _
  have hQs : Q.support = cyl J (Q.marg J).support ∩ cyl Jᶜ (Q.marg Jᶜ).support := by
    conv_lhs => rw [hQ]
    exact Distr.support_outerCompl _ _
  refine Distr.prob_pos_of_support_subset ?_ hC
  rw [hPs, hQs]
  exact Set.inter_subset_inter (Set.preimage_mono h₁) (Set.preimage_mono h₂)

/-! ## Definition 6.1: conditional independence -/

/-- **Conditional independence of events**, in the paper's product form:
`A ⊥^P B | C` iff `P(A ∩ C)·P(B ∩ C) = P(A ∩ B ∩ C)·P(C)`.  When `P(C) = 0` this holds
trivially — the paper's convention, and it is load-bearing (it is what makes the
intersection axiom fail); never restate it in the conditional form.

Paper node: Definition 6.1 (§6). -/
def CondIndep (P : Distr (Pt Ω)) (A B C : Set (Pt Ω)) : Prop :=
  P.prob (A ∩ C) * P.prob (B ∩ C) = P.prob (A ∩ B ∩ C) * P.prob C

/-- **Conditional independence of random variables**: `X ⊥^P Y | Z` iff
`x ⊥^P y | z` for all values `x, y, z`, where `x` is the event `{X = x}`.

Paper node: Definition 6.1 (§6). -/
def CondIndepVar {α β γ : Type*} (P : Distr (Pt Ω)) (X : Pt Ω → α) (Y : Pt Ω → β)
    (Z : Pt Ω → γ) : Prop :=
  ∀ (x : α) (y : β) (z : γ), CondIndep P (fiber X x) (fiber Y y) (fiber Z z)

/-- The paper's mixed notation `B ⊥^P Y | C` (an event, a variable, an event): `B ⊥^P y | C`
for all values `y` (§C.3, "Further notation for conditional independence"). -/
def CondIndepEventVar {β : Type*} (P : Distr (Pt Ω)) (B : Set (Pt Ω)) (Y : Pt Ω → β)
    (C : Set (Pt Ω)) : Prop :=
  ∀ y : β, CondIndep P B (fiber Y y) C

/-- The paper's mixed notation `X ⊥^P Y | C` (two variables, an event). -/
def CondIndepVarEvent {α β : Type*} (P : Distr (Pt Ω)) (X : Pt Ω → α) (Y : Pt Ω → β)
    (C : Set (Pt Ω)) : Prop :=
  ∀ (x : α) (y : β), CondIndep P (fiber X x) (fiber Y y) C

lemma CondIndep.symm {P : Distr (Pt Ω)} {A B C : Set (Pt Ω)} (h : CondIndep P A B C) :
    CondIndep P B A C := by
  unfold CondIndep at *
  rw [mul_comm, h]
  congr 2
  ext ω; simp only [Set.mem_inter_iff]; tauto

lemma CondIndep.of_prob_eq_zero {P : Distr (Pt Ω)} {A B C : Set (Pt Ω)} (h : P.prob C = 0) :
    CondIndep P A B C := by
  have hz : ∀ D : Set (Pt Ω), P.prob (D ∩ C) = 0 := fun D =>
    le_antisymm (h ▸ P.prob_mono Set.inter_subset_right) (P.prob_nonneg _)
  simp [CondIndep, hz A, hz B, h]

/-- The paper's `A ⊥^⊗ B | C`: independence in every factorizing distribution (§C.3). -/
def CondIndepAll (A B C : Set (Pt Ω)) : Prop :=
  ∀ P : Distr (Pt Ω), Factorizes P → CondIndep P A B C

/-- Regrouping an event along the fibres of a variable: if `T` contains every attained
value of `Z`, then `P(D) = ∑_{z ∈ T} P(D ∩ {Z = z})`.  Stated with an explicit `Finset`
of values because `Val(Z)` carries no `Fintype` instance (`dd:variable`); take
`T := Finset.univ` for a finite value type. -/
lemma Distr.prob_eq_sum_fiber {S : Type w} [Fintype S] {κ : Type*} (P : Distr S)
    (D : Set S) (Z : S → κ) (T : Finset κ) (hT : ∀ s, Z s ∈ T) :
    P.prob D = ∑ z ∈ T, P.prob (D ∩ Z ⁻¹' {z}) := by
  classical
  have key : ∀ s : S, ∑ z ∈ T, (D ∩ Z ⁻¹' {z}).indicator P.mass s = D.indicator P.mass s := by
    intro s
    rw [Finset.sum_eq_single (Z s)]
    · by_cases hs : s ∈ D
      · rw [Set.indicator_of_mem (show s ∈ D ∩ Z ⁻¹' {Z s} from ⟨hs, rfl⟩),
          Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem (fun h => hs h.1), Set.indicator_of_notMem hs]
    · intro z _ hz
      exact Set.indicator_of_notMem (fun h => hz h.2.symm) _
    · intro h
      exact absurd (hT s) h
  simp only [Distr.prob]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => (key s).symm

/-! ## Lemmas C.13, C.14: decomposition of mixed independence -/

/-- **Decomposition of mixed independence.** `B ⊥^P (Y, Z) | C` implies `B ⊥^P Y | C`.

Paper node: Lemma C.13 (§C.3). -/
theorem CondIndepEventVar.of_pair {β γ : Type*} {P : Distr (Pt Ω)} {B C : Set (Pt Ω)}
    {Y : Pt Ω → β} {Z : Pt Ω → γ} (h : CondIndepEventVar P B (pair Y Z) C) :
    CondIndepEventVar P B Y C := by
  classical
  intro y
  have hT : ∀ ω : Pt Ω, Z ω ∈ Finset.univ.image Z := fun ω =>
    Finset.mem_image_of_mem Z (Finset.mem_univ ω)
  have h₁ : ∀ z : γ, fiber Y y ∩ C ∩ Z ⁻¹' {z} = fiber (pair Y Z) (y, z) ∩ C := by
    intro z
    ext ω
    simp only [fiber, pair, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_singleton_iff, Prod.ext_iff]
    tauto
  have h₂ : ∀ z : γ, B ∩ fiber Y y ∩ C ∩ Z ⁻¹' {z} = B ∩ fiber (pair Y Z) (y, z) ∩ C := by
    intro z
    ext ω
    simp only [fiber, pair, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_singleton_iff, Prod.ext_iff]
    tauto
  have e₁ : P.prob (fiber Y y ∩ C)
      = ∑ z ∈ Finset.univ.image Z, P.prob (fiber (pair Y Z) (y, z) ∩ C) :=
    (P.prob_eq_sum_fiber _ Z _ hT).trans
      (Finset.sum_congr rfl fun z _ => by rw [h₁ z])
  have e₂ : P.prob (B ∩ fiber Y y ∩ C)
      = ∑ z ∈ Finset.univ.image Z, P.prob (B ∩ fiber (pair Y Z) (y, z) ∩ C) :=
    (P.prob_eq_sum_fiber _ Z _ hT).trans
      (Finset.sum_congr rfl fun z _ => by rw [h₂ z])
  unfold CondIndep
  rw [e₁, e₂, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun z _ => h (y, z)

/-- **Corollary of decomposition.** For `J' ⊆ J`, `B ⊥^P U_J | C` implies `B ⊥^P U_{J'} | C`.

Paper node: Corollary C.14 (§C.3). -/
theorem CondIndepEventVar.of_proj_subset {P : Distr (Pt Ω)} {B C : Set (Pt Ω)} {J' J : Finset I}
    (hJ : J' ⊆ J) (h : CondIndepEventVar P B (proj J) C) : CondIndepEventVar P B (proj J') C := by
  classical
  intro α'
  have key : ∀ (D : Set (Pt Ω)) (α : PtOn Ω J),
      D ∩ fiber (proj J') α' ∩ C ∩ proj J ⁻¹' {α} =
        if restrict hJ α = α' then D ∩ fiber (proj J) α ∩ C else ∅ := by
    intro D α
    by_cases hα : restrict hJ α = α'
    · rw [if_pos hα]
      ext ω
      simp only [fiber, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨⟨hD, _⟩, hC⟩, hp⟩
        exact ⟨⟨hD, hp⟩, hC⟩
      · rintro ⟨⟨hD, hp⟩, hC⟩
        refine ⟨⟨⟨hD, ?_⟩, hC⟩, hp⟩
        rw [← hα]
        exact congrArg (restrict hJ) hp
    · rw [if_neg hα]
      ext ω
      simp only [fiber, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨⟨_, hp'⟩, _⟩, hp⟩
      exact hα (by rw [← hp]; exact hp')
  have e : ∀ D : Set (Pt Ω), P.prob (D ∩ fiber (proj J') α' ∩ C) =
      ∑ α : PtOn Ω J, if restrict hJ α = α' then P.prob (D ∩ fiber (proj J) α ∩ C) else 0 := by
    intro D
    refine (P.prob_eq_sum_fiber _ (proj J) Finset.univ (fun _ => Finset.mem_univ _)).trans
      (Finset.sum_congr rfl fun α _ => ?_)
    rw [key D α]
    split_ifs
    · rfl
    · exact P.prob_empty
  have eC : P.prob (fiber (proj J') α' ∩ C) =
      ∑ α : PtOn Ω J, if restrict hJ α = α' then P.prob (fiber (proj J) α ∩ C) else 0 := by
    simpa only [Set.univ_inter] using e Set.univ
  unfold CondIndep
  rw [eC, e B, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with hα
  · exact h α
  · ring

/-! ## Lemma C.15: probability of a product event -/

/-- **Probability of a product event.** If `P = P_J ⊗ P_{I∖J}` then
`P(A_J × A_{I∖J}) = P_J(A_J) · P_{I∖J}(A_{I∖J})`.

Paper node: Lemma C.15 (§C.3). -/
theorem Distr.prob_cyl_inter_cyl {J : Finset I} {P : Distr (Pt Ω)}
    (hP : P = Distr.outerCompl (P.marg J) (P.marg Jᶜ)) (A : Set (PtOn Ω J)) (B : Set (PtOn Ω Jᶜ)) :
    P.prob (cyl J A ∩ cyl Jᶜ B) = (P.marg J).prob A * (P.marg Jᶜ).prob B := by
  classical
  have hmass : ∀ (α : PtOn Ω J) (β : PtOn Ω Jᶜ),
      P.mass ((splitEquiv J).symm (α, β)) = (P.marg J).mass α * (P.marg Jᶜ).mass β := by
    intro α β
    conv_lhs => rw [hP]
    rw [Distr.outerCompl_mass, proj_splitEquiv_symm, proj_compl_splitEquiv_symm]
  have hterm : ∀ (α : PtOn Ω J) (β : PtOn Ω Jᶜ),
      (cyl J A ∩ cyl Jᶜ B).indicator P.mass ((splitEquiv J).symm (α, β))
        = A.indicator (P.marg J).mass α * B.indicator (P.marg Jᶜ).mass β := by
    intro α β
    by_cases hA : α ∈ A
    · by_cases hB : β ∈ B
      · rw [Set.indicator_of_mem (by simp [cyl, hA, hB]), Set.indicator_of_mem hA,
          Set.indicator_of_mem hB, hmass]
      · rw [Set.indicator_of_notMem (by simp [cyl, hB]), Set.indicator_of_notMem hB, mul_zero]
    · rw [Set.indicator_of_notMem (by simp [cyl, hA]), Set.indicator_of_notMem hA, zero_mul]
  rw [Distr.prob_eq_sum_split P J,
    Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => hterm α β]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

/-! ## Lemma C.16: slicing at a `J`-value -/

/-- The paper's `D^α = {ω ∈ D | ω_J = α} = D ∩ U_J⁻¹(α)` (§C.3, eq. (D_alpha)). -/
def sliceAt (J : Finset I) (α : PtOn Ω J) (D : Set (Pt Ω)) : Set (Pt Ω) :=
  D ∩ fiber (proj J) α

omit [∀ i, Fintype (Ω i)] in
/-- The `I∖J`-parts of the slice `D^α` are exactly the `β` with `α · β ∈ D`. -/
lemma mem_projSet_compl_sliceAt (J : Finset I) (α : PtOn Ω J) (D : Set (Pt Ω))
    (β : PtOn Ω Jᶜ) : β ∈ projSet Jᶜ (sliceAt J α D) ↔ (splitEquiv J).symm (α, β) ∈ D := by
  constructor
  · rintro ⟨ω, ⟨hωD, hωα⟩, rfl⟩
    rw [show α = proj J ω from (hωα : proj J ω = α).symm, splitEquiv_symm_proj]
    exact hωD
  · intro hD
    exact ⟨(splitEquiv J).symm (α, β), ⟨hD, by simp [fiber]⟩, by simp⟩

open scoped Classical in
/-- `P_{I∖J}(D^α_{I∖J})` written as a sum over the `I∖J`-coordinates. -/
private lemma prob_projSet_sliceAt (J : Finset I) (α : PtOn Ω J) (D : Set (Pt Ω))
    (Q : Distr (PtOn Ω Jᶜ)) :
    Q.prob (projSet Jᶜ (sliceAt J α D))
      = ∑ β : PtOn Ω Jᶜ, (if (splitEquiv J).symm (α, β) ∈ D then Q.mass β else 0) := by
  rw [Distr.prob]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases hβ : (splitEquiv J).symm (α, β) ∈ D
  · rw [Set.indicator_of_mem ((mem_projSet_compl_sliceAt J α D β).mpr hβ), if_pos hβ]
  · rw [Set.indicator_of_notMem fun hc => hβ ((mem_projSet_compl_sliceAt J α D β).mp hc),
      if_neg hβ]

/-- **Slicing (1).** For factorizing `P`: `P(D^α) = P_J(α) · P_{I∖J}(D^α_{I∖J})`.

Paper node: Lemma C.16 (§C.3). -/
theorem Factorizes.prob_sliceAt {P : Distr (Pt Ω)} (hP : Factorizes P) (J : Finset I)
    (α : PtOn Ω J) (D : Set (Pt Ω)) :
    P.prob (sliceAt J α D) = (P.marg J).mass α * (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α D)) := by
  classical
  have hmass : ∀ (α' : PtOn Ω J) (β : PtOn Ω Jᶜ),
      P.mass ((splitEquiv J).symm (α', β)) = (P.marg J).mass α' * (P.marg Jᶜ).mass β := by
    intro α' β
    conv_lhs => rw [hP.eq_outerCompl J]
    rw [Distr.outerCompl_mass, proj_splitEquiv_symm, proj_compl_splitEquiv_symm]
  have hterm : ∀ α' : PtOn Ω J,
      (∑ β : PtOn Ω Jᶜ, (sliceAt J α D).indicator P.mass ((splitEquiv J).symm (α', β)))
        = if α' = α then
            ∑ β : PtOn Ω Jᶜ, (P.marg J).mass α *
              (if (splitEquiv J).symm (α, β) ∈ D then (P.marg Jᶜ).mass β else 0)
          else 0 := by
    intro α'
    by_cases hα : α' = α
    · subst hα
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun β _ => ?_
      by_cases hD : (splitEquiv J).symm (α', β) ∈ D
      · rw [Set.indicator_of_mem (show (splitEquiv J).symm (α', β) ∈ sliceAt J α' D from
          ⟨hD, by simp [fiber]⟩), if_pos hD, hmass]
      · rw [Set.indicator_of_notMem fun hc => hD hc.1, if_neg hD, mul_zero]
    · rw [if_neg hα]
      refine Finset.sum_eq_zero fun β _ => ?_
      refine Set.indicator_of_notMem (fun hc => hα ?_) _
      simpa [fiber] using hc.2
  rw [Distr.prob_eq_sum_split P J, prob_projSet_sliceAt J α D (P.marg Jᶜ), Finset.mul_sum,
    Finset.sum_congr rfl fun α' _ => hterm α']
  simp

/-- **Slicing (2).** `(δ_α ⊗ P_{I∖J})(D) = P_{I∖J}(D^α_{I∖J})`.  (The paper assumes `P`
factorizes here; the identity needs no such hypothesis.)

Paper node: Lemma C.16 (§C.3). -/
theorem Distr.prob_outerCompl_delta (P : Distr (Pt Ω)) (J : Finset I) (α : PtOn Ω J)
    (D : Set (Pt Ω)) :
    (Distr.outerCompl (Distr.delta α) (P.marg Jᶜ)).prob D =
      (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α D)) := by
  classical
  have hterm : ∀ α' : PtOn Ω J,
      (∑ β : PtOn Ω Jᶜ, D.indicator (Distr.outerCompl (Distr.delta α) (P.marg Jᶜ)).mass
          ((splitEquiv J).symm (α', β)))
        = if α' = α then
            ∑ β : PtOn Ω Jᶜ, (if (splitEquiv J).symm (α, β) ∈ D then (P.marg Jᶜ).mass β else 0)
          else 0 := by
    intro α'
    by_cases hα : α' = α
    · subst hα
      rw [if_pos rfl]
      have hm : ∀ β : PtOn Ω Jᶜ,
          (Distr.outerCompl (Distr.delta α') (P.marg Jᶜ)).mass ((splitEquiv J).symm (α', β))
            = (P.marg Jᶜ).mass β := by
        intro β
        rw [Distr.outerCompl_mass, proj_splitEquiv_symm, proj_compl_splitEquiv_symm,
          Distr.delta_mass, if_pos rfl, one_mul]
      refine Finset.sum_congr rfl fun β _ => ?_
      by_cases hD : (splitEquiv J).symm (α', β) ∈ D
      · rw [Set.indicator_of_mem hD, if_pos hD, hm β]
      · rw [Set.indicator_of_notMem hD, if_neg hD]
    · rw [if_neg hα]
      have hm : ∀ β : PtOn Ω Jᶜ,
          (Distr.outerCompl (Distr.delta α) (P.marg Jᶜ)).mass ((splitEquiv J).symm (α', β)) = 0 := by
        intro β
        rw [Distr.outerCompl_mass, proj_splitEquiv_symm, proj_compl_splitEquiv_symm,
          Distr.delta_mass, if_neg hα, zero_mul]
      refine Finset.sum_eq_zero fun β _ => ?_
      by_cases hD : (splitEquiv J).symm (α', β) ∈ D
      · rw [Set.indicator_of_mem hD, hm β]
      · rw [Set.indicator_of_notMem hD]
  rw [Distr.prob_eq_sum_split _ J, prob_projSet_sliceAt J α D (P.marg Jᶜ),
    Finset.sum_congr rfl fun α' _ => hterm α']
  simp

/-! ## Lemma C.17: the history's factors are independent of the rest -/

/-- The content of Lemma C.17: whenever `J` disintegrates `C`, the `J`-coordinates and the
`(I∖J)`-coordinates are conditionally independent given `C` in every factorizing `P`.  The
paper states it only for `J = H(A | C)`, where the disintegration comes from Lemma 4.7. -/
lemma condIndepVarEvent_proj_of_disintegrates {J : Finset I} {C : Set (Pt Ω)}
    (hd : Disintegrates J C) {P : Distr (Pt Ω)} (hP : Factorizes P) :
    CondIndepVarEvent P (proj J) (proj Jᶜ) C := by
  classical
  intro x y
  -- `J` disintegrates `C`, so `C = C_J × C_{I∖J}`
  have hCsplit : C = cyl J (projSet J C) ∩ cyl Jᶜ (projSet Jᶜ C) :=
    (hd.trans (prodSplit_eq_splice J C)).trans (splice_eq_cyl_inter J C C)
  have hC15 : ∀ (S : Set (PtOn Ω J)) (T : Set (PtOn Ω Jᶜ)),
      P.prob (cyl J S ∩ cyl Jᶜ T) = (P.marg J).prob S * (P.marg Jᶜ).prob T :=
    fun S T => Distr.prob_cyl_inter_cyl (hP.eq_outerCompl J) S T
  have e1 : fiber (proj J) x ∩ C = cyl J ({x} ∩ projSet J C) ∩ cyl Jᶜ (projSet Jᶜ C) := by
    conv_lhs => rw [hCsplit]
    ext ω
    simp only [fiber, cyl, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    tauto
  have e2 : fiber (proj Jᶜ) y ∩ C = cyl J (projSet J C) ∩ cyl Jᶜ ({y} ∩ projSet Jᶜ C) := by
    conv_lhs => rw [hCsplit]
    ext ω
    simp only [fiber, cyl, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    tauto
  have e3 : fiber (proj J) x ∩ fiber (proj Jᶜ) y ∩ C
      = cyl J ({x} ∩ projSet J C) ∩ cyl Jᶜ ({y} ∩ projSet Jᶜ C) := by
    conv_lhs => rw [hCsplit]
    ext ω
    simp only [fiber, cyl, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    tauto
  have eC : P.prob C = (P.marg J).prob (projSet J C) * (P.marg Jᶜ).prob (projSet Jᶜ C) := by
    conv_lhs => rw [hCsplit]
    exact hC15 _ _
  unfold CondIndep
  rw [e1, e2, e3, eC, hC15, hC15, hC15]
  ring

/-- **`U_J ⊥^⊗ U_{I∖J} | C` for `J = H(A | C)`.**

Paper node: Lemma C.17 (§C.3). -/
theorem condIndepVarEvent_proj_history (A C : Set (Pt Ω)) (P : Distr (Pt Ω)) (hP : Factorizes P) :
    CondIndepVarEvent P (proj (eventHistory A C)) (proj (eventHistory A C)ᶜ) C :=
  condIndepVarEvent_proj_of_disintegrates (generates_history (indic A) C).2 hP


lemma Distr.prob_eq_zero_of_subset {S : Type w} [Fintype S] {A B : Set S} (P : Distr S) (hAB : A ⊆ B)
    (h : P.prob B = 0) : P.prob A = 0 :=
  le_antisymm (h ▸ P.prob_mono hAB) (P.prob_nonneg _)

/-! ## Further `Distr` facts used by Appendix C.3

A carrier of a distribution is inhabited, the mass of an outer
product is positive exactly when every factor is, a delta distribution on a product is
the outer product of the factorwise deltas, mixing two distributions mixes their event
probabilities, and the conditional distribution `P(· | C)` of Lemma C.20. -/

/-- A distribution witnesses that its carrier is inhabited: an empty type carries none,
because the empty sum is `0 ≠ 1`. -/
lemma Distr.nonempty_carrier {S : Type w} [Fintype S] (P : Distr S) : Nonempty S := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 := P.sum_eq_one
  simp at h1

/-- Every factor of a factored space carrying a distribution is inhabited. -/
lemma nonempty_factor (P : Distr (Pt Ω)) (i : I) : Nonempty (Ω i) :=
  ⟨P.nonempty_carrier.some i⟩

/-- A point has positive mass under an outer product exactly when each of its
coordinates has positive mass under the corresponding factor. -/
lemma Distr.prod_mass_pos_iff (p : ∀ i, Distr (Ω i)) (ω : Pt Ω) :
    0 < (Distr.prod p).mass ω ↔ ∀ i, 0 < (p i).mass (ω i) := by
  rw [Distr.prod_mass]
  constructor
  · intro h i
    rcases lt_or_eq_of_le ((p i).nonneg (ω i)) with h' | h'
    · exact h'
    · rw [Finset.prod_eq_zero (Finset.mem_univ i) h'.symm] at h
      exact absurd h (lt_irrefl 0)
  · exact fun h => Finset.prod_pos fun i _ => h i

/-- The delta distribution at `ω` is the outer product of the factorwise deltas
(the paper's `δ_α = ⨂_{i∈J} δ_{α_i}`, eq. (delta_factorizes)). -/
lemma Distr.delta_eq_prod (ω : Pt Ω) :
    Distr.delta ω = Distr.prod fun i => Distr.delta (ω i) := by
  classical
  ext ω'
  rw [Distr.prod_mass]
  simp only [Distr.delta_mass]
  by_cases h : ω' = ω
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ω' i ≠ ω i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

lemma factorizes_delta (ω : Pt Ω) : Factorizes (Distr.delta ω) := by
  rw [Distr.delta_eq_prod]
  exact factorizes_prod _

/-- If `R` is the pointwise midpoint of `P` and `Q` then so are all its event
probabilities (used for the distribution `R` of Lemma C.9). -/
lemma Distr.prob_of_mass_midpoint {S : Type w} [Fintype S] {R P Q : Distr S}
    (h : ∀ s, R.mass s = (P.mass s + Q.mass s) / 2) (D : Set S) :
    R.prob D = (P.prob D + Q.prob D) / 2 := by
  simp only [Distr.prob]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s ∈ D <;> simp [hs, h s]

/-- The conditional distribution `P(· | C)`, for `P(C) > 0` (Lemma C.20). -/
noncomputable def condDist {S : Type w} [Fintype S] (P : Distr S) (C : Set S)
    (h : 0 < P.prob C) : Distr S where
  mass s := C.indicator P.mass s / P.prob C
  nonneg s := div_nonneg (Set.indicator_nonneg (fun t _ => P.nonneg t) s) h.le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self h.ne'

lemma condDist_mass {S : Type w} [Fintype S] (P : Distr S) (C : Set S) (h : 0 < P.prob C)
    (s : S) : (condDist P C h).mass s = C.indicator P.mass s / P.prob C := rfl

lemma condDist_prob {S : Type w} [Fintype S] (P : Distr S) (C : Set S) (h : 0 < P.prob C)
    (D : Set S) : (condDist P C h).prob D = P.prob (D ∩ C) / P.prob C := by
  simp only [Distr.prob]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hD : s ∈ D <;> by_cases hC : s ∈ C <;>
    simp [hD, hC, condDist_mass, Distr.prob]

/-- The paper's `δ_α ⊗ P_{I∖J}` read as an outer product over all of `I`: the factors are
the deltas `δ_{α_i}` on `J` and the marginals `P_i` off `J`.  This is what makes it
visibly a member of `Δ^F(Ω)` and pins down its one-factor marginals (Lemma C.18). -/
lemma outerCompl_delta_eq_prod {J : Finset I} {P : Distr (Pt Ω)} (hP : Factorizes P)
    (α : PtOn Ω J) :
    Distr.outerCompl (Distr.delta α) (P.marg Jᶜ) =
      Distr.prod fun i => if h : i ∈ J then Distr.delta (α ⟨i, h⟩) else P.margAt i := by
  classical
  ext ω
  rw [Distr.outerCompl_mass, Distr.prod_mass, ← Finset.prod_mul_prod_compl J]
  congr 1
  · rw [← Finset.prod_coe_sort J]
    rw [Distr.delta_eq_prod (Ω := fun i : J => Ω i) α, Distr.prod_mass]
    exact Finset.prod_congr rfl fun i _ => by
      rw [dif_pos i.2]
      congr 1
  · rw [hP.marg_mass Jᶜ, ← Finset.prod_coe_sort Jᶜ]
    exact (Finset.prod_congr rfl fun i _ => by
      rw [dif_neg (Finset.mem_compl.mp i.2)]; rfl).symm

/-! ## Product distributions and single coordinates -/

/-- Under a product distribution, the probability that `ω` agrees with a fixed point `f`
on a finite set `S` of coordinates is the product of the corresponding masses. -/
lemma Distr.prob_prod_agree_on (p : ∀ i, Distr (Ω i)) (S : Finset I) (f : Pt Ω) :
    (Distr.prod p).prob {ω | ∀ i ∈ S, ω i = f i} = ∏ i ∈ S, (p i).mass (f i) := by
  classical
  have hset : Finset.univ.filter (fun ω : Pt Ω => ω ∈ {ω : Pt Ω | ∀ i ∈ S, ω i = f i})
      = Fintype.piFinset (fun j => if j ∈ S then ({f j} : Finset (Ω j)) else Finset.univ) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j ∈ S
      · simp [hj, h j hj]
      · simp [hj]
    · intro h j hj
      have := h j
      simpa [hj] using this
  rw [Distr.prob_eq_sum_filter, hset]
  simp only [Distr.prod_mass]
  rw [← Finset.prod_univ_sum]
  have hsum : ∀ j : I, (∑ b ∈ (if j ∈ S then ({f j} : Finset (Ω j)) else Finset.univ),
      (p j).mass b) = if j ∈ S then (p j).mass (f j) else 1 := by
    intro j
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj, (p j).sum_eq_one]
  simp only [hsum]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- Under a product distribution, an event invariant under changing the `i`-th coordinate
is independent of that coordinate. -/
lemma Distr.prob_prod_inter_bg (p : ∀ i, Distr (Ω i)) (i : I) (a : Ω i) {E : Set (Pt Ω)}
    (hE : ∀ (ω : Pt Ω) (b : Ω i), ω ∈ E → Function.update ω i b ∈ E) :
    (Distr.prod p).prob (E ∩ {ω | ω i = a}) = (p i).mass a * (Distr.prod p).prob E := by
  classical
  have hupd : ∀ (ω : Pt Ω) (b : Ω i),
      ∏ j ∈ Finset.univ.erase i, (p j).mass (Function.update ω i b j)
        = ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := fun ω b =>
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj) b ω]
  have hmass : ∀ ω : Pt Ω, (Distr.prod p).mass ω
      = (p i).mass (ω i) * ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := fun ω =>
    (Finset.mul_prod_erase Finset.univ (fun j => (p j).mass (ω j)) (Finset.mem_univ i)).symm
  have hmem : ∀ (ω : Pt Ω) (b : Ω i), Function.update ω i b ∈ E ↔ ω ∈ E := by
    intro ω b
    refine ⟨fun h => ?_, fun h => hE ω b h⟩
    have := hE _ (ω i) h
    rwa [Function.update_idem, Function.update_eq_self] at this
  have hGsum : ∀ b : Ω i,
      (∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = b),
        ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j))
      = ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = a),
        ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := by
    intro b
    refine Finset.sum_nbij' (fun ω => Function.update ω i a) (fun ω => Function.update ω i b)
      ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨(hmem ω a).mpr hω.1, Function.update_self _ _ _⟩
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨(hmem ω b).mpr hω.1, Function.update_self _ _ _⟩
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      rw [Function.update_idem, ← hω.2, Function.update_eq_self]
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      rw [Function.update_idem, ← hω.2, Function.update_eq_self]
    · intro ω _
      exact (hupd ω a).symm
  have hkey : ∀ b : Ω i,
      (∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = b), (Distr.prod p).mass ω)
      = (p i).mass b * ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = a),
          ∏ j ∈ Finset.univ.erase i, (p j).mass (ω j) := by
    intro b
    rw [← hGsum b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [hmass ω, hω.2]
  have hLHS : (Distr.prod p).prob (E ∩ {ω | ω i = a})
      = ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = a), (Distr.prod p).mass ω := by
    rw [Distr.prob_eq_sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext ω
    simp [Set.mem_inter_iff]
  have hRHS : (Distr.prod p).prob E
      = ∑ b : Ω i, ∑ ω ∈ Finset.univ.filter (fun ω : Pt Ω => ω ∈ E ∧ ω i = b),
          (Distr.prod p).mass ω := by
    rw [Distr.prob_eq_sum_filter,
      ← Finset.sum_fiberwise (Finset.univ.filter (fun ω : Pt Ω => ω ∈ E)) (fun ω : Pt Ω => ω i)
        (Distr.prod p).mass]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    rw [Finset.filter_filter]
  rw [hLHS, hRHS, hkey a]
  simp only [hkey]
  rw [← Finset.sum_mul, (p i).sum_eq_one, one_mul]

end FactoredSpaces
