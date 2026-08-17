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

/-!
# The finite-probability substrate (§4.1, §6, Appendix C.0–C.1)

Distributions on a finite type are elementary mass functions (`Dist`, `dd:dist`);
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
structure Dist (S : Type w) [Fintype S] where
  /-- The mass `P(s)` of a point. -/
  mass : S → ℝ
  nonneg : ∀ s, 0 ≤ mass s
  sum_eq_one : ∑ s, mass s = 1

namespace Dist

variable {S : Type w} {T : Type w'} [Fintype S] [Fintype T]

/-- The probability `P(A) = ∑_{s ∈ A} P(s)` of an event `A ⊆ S`. -/
noncomputable def prob (P : Dist S) (A : Set S) : ℝ := ∑ s, A.indicator P.mass s

/-- The distributions on `S` — the paper's `Δ(S)`. -/
abbrev all (S : Type w) [Fintype S] : Set (Dist S) := Set.univ

instance [Nonempty S] : Nonempty (Dist S) := by
  classical
  obtain ⟨s⟩ := ‹Nonempty S›
  exact ⟨⟨fun t => if t = s then 1 else 0, fun t => by split_ifs <;> norm_num, by simp⟩⟩

lemma prob_nonneg (P : Dist S) (A : Set S) : 0 ≤ P.prob A :=
  Finset.sum_nonneg fun s _ => Set.indicator_nonneg (fun t _ => P.nonneg t) s

lemma prob_univ (P : Dist S) : P.prob Set.univ = 1 := by
  simp [prob, P.sum_eq_one]

lemma prob_empty (P : Dist S) : P.prob ∅ = 0 := by simp [prob]

lemma prob_mono (P : Dist S) {A B : Set S} (h : A ⊆ B) : P.prob A ≤ P.prob B :=
  Finset.sum_le_sum fun s _ => Set.indicator_le_indicator_of_subset h (P.nonneg) s

lemma prob_le_one (P : Dist S) (A : Set S) : P.prob A ≤ 1 :=
  P.prob_univ ▸ P.prob_mono (Set.subset_univ A)

lemma prob_union_of_disjoint (P : Dist S) {A B : Set S} (h : Disjoint A B) :
    P.prob (A ∪ B) = P.prob A + P.prob B := by
  simp only [prob, Set.indicator_union_of_disjoint h, Finset.sum_add_distrib]

lemma prob_singleton (P : Dist S) (s : S) : P.prob {s} = P.mass s := by
  classical
  simp [prob, Set.indicator_apply, Finset.sum_ite_eq']

lemma prob_eq_sum_filter (P : Dist S) (A : Set S) [DecidablePred (· ∈ A)] :
    P.prob A = ∑ s ∈ Finset.univ.filter (· ∈ A), P.mass s := by
  simp only [prob, Set.indicator_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero]

lemma prob_eq_sum_subtype (P : Dist S) (A : Set S) [Fintype A] :
    P.prob A = ∑ s : A, P.mass s := by
  sorry

/-- The support `supp(P) = {s | P(s) > 0}` (§C.3). -/
def support (P : Dist S) : Set S := {s | 0 < P.mass s}

lemma mem_support_iff (P : Dist S) (s : S) : s ∈ P.support ↔ 0 < P.mass s := Iff.rfl

lemma prob_pos_iff (P : Dist S) (A : Set S) : 0 < P.prob A ↔ (A ∩ P.support).Nonempty := by
  sorry

lemma prob_eq_zero_iff (P : Dist S) (A : Set S) : P.prob A = 0 ↔ Disjoint A P.support := by
  sorry

lemma prob_support (P : Dist S) : P.prob P.support = 1 := by
  sorry

/-- The conditional probability `P(A | C) = P(A ∩ C) / P(C)` (`0` when `P(C) = 0`,
by Lean's convention for division; the paper only uses it when `P(C) > 0`). -/
noncomputable def condProb (P : Dist S) (A C : Set S) : ℝ := P.prob (A ∩ C) / P.prob C

/-- `P` is strictly positive: every point has positive mass. -/
def StrictlyPositive (P : Dist S) : Prop := ∀ s, 0 < P.mass s

/-- The pushforward `P ∘ f⁻¹` of `P` along `f : S → T`. -/
noncomputable def map (f : S → T) (P : Dist S) : Dist T where
  mass t := P.prob (f ⁻¹' {t})
  nonneg t := P.prob_nonneg _
  sum_eq_one := by
    sorry

lemma map_mass (f : S → T) (P : Dist S) (t : T) : (P.map f).mass t = P.prob (f ⁻¹' {t}) := rfl

lemma map_prob (f : S → T) (P : Dist S) (B : Set T) : (P.map f).prob B = P.prob (f ⁻¹' B) := by
  sorry

lemma map_map {U : Type w''} [Fintype U] (f : S → T) (g : T → U) (P : Dist S) :
    (P.map f).map g = P.map (g ∘ f) := by
  sorry

open scoped Classical in
/-- The delta distribution `δ_s` at a point (§C.3). -/
noncomputable def delta (s : S) : Dist S where
  mass t := if t = s then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  sum_eq_one := by simp

open scoped Classical in
lemma delta_mass (s t : S) : (delta s).mass t = if t = s then 1 else 0 := rfl

open scoped Classical in
lemma delta_prob (s : S) (A : Set S) : (delta s).prob A = if s ∈ A then 1 else 0 := by
  sorry

lemma support_delta (s : S) : (delta s).support = {s} := by
  sorry

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform [Nonempty S] : Dist S where
  mass _ := (Fintype.card S : ℝ)⁻¹
  nonneg _ := by positivity
  sum_eq_one := by
    simp [Finset.sum_const, Finset.card_univ]

lemma uniform_strictlyPositive [Nonempty S] : (uniform : Dist S).StrictlyPositive := fun _ =>
  inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

/-- The convex combination `(1 − t)·P + t·Q` for `t ∈ [0, 1]` — the paper's
`R^λ_i = (1−λ)Q_i + λP_i` is `mix λ Q_i P_i`. -/
noncomputable def mix (t : unitInterval) (P Q : Dist S) : Dist S where
  mass s := (1 - (t : ℝ)) * P.mass s + (t : ℝ) * Q.mass s
  nonneg s := by
    have h0 := t.2.1; have h1 := t.2.2
    have := P.nonneg s; have := Q.nonneg s
    nlinarith
  sum_eq_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, P.sum_eq_one, Q.sum_eq_one]
    ring

lemma mix_zero (P Q : Dist S) : mix 0 P Q = P := by
  ext s; simp [mix]

lemma mix_one (P Q : Dist S) : mix 1 P Q = Q := by
  ext s; simp [mix]

/-- The Euclidean distance between two distributions, viewing `Δ(S) ⊆ ℝ^S` (§6.2). -/
noncomputable def euclDist (P Q : Dist S) : ℝ := √(∑ s, (P.mass s - Q.mass s) ^ 2)

end Dist

/-! ## Distributions on a factored space -/

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]

/-- The product `⨂_{i∈I} p_i` of one distribution per factor: `ω ↦ ∏_i p_i(ω_i)`. -/
noncomputable def Dist.prod (p : ∀ i, Dist (Ω i)) : Dist (Pt Ω) where
  mass ω := ∏ i, (p i).mass (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (p i).nonneg _
  sum_eq_one := by
    rw [← Fintype.prod_sum]
    simp [Dist.sum_eq_one]

lemma Dist.prod_mass (p : ∀ i, Dist (Ω i)) (ω : Pt Ω) :
    (Dist.prod p).mass ω = ∏ i, (p i).mass (ω i) := rfl

/-- The paper's `P(ω_i) := P(π_i⁻¹(ω_i))`: the marginal of `P` on the `i`-th factor,
`P_i = P ∘ U_i⁻¹` (Definition C.2 at `J = {i}`). -/
noncomputable abbrev Dist.margAt (P : Dist (Pt Ω)) (i : I) : Dist (Ω i) := P.map (bg i)

/-- **Factorizing distribution.** `P` factorizes over `Ω` if `P(ω) = ∏_{i∈I} P(ω_i)`
for all `ω`, where `P(ω_i) = P(π_i⁻¹(ω_i))`.

Paper node: Definition 4.3 (§4.1). -/
def Factorizes (P : Dist (Pt Ω)) : Prop :=
  ∀ ω : Pt Ω, P.mass ω = ∏ i, (P.margAt i).mass (ω i)

/-- The set `Δ^F(Ω)` of distributions that factorize over `Ω`. -/
def factorizing (Ω : I → Type v) [∀ i, Fintype (Ω i)] : Set (Dist (Pt Ω)) :=
  {P | Factorizes P}

lemma mem_factorizing {P : Dist (Pt Ω)} : P ∈ factorizing Ω ↔ Factorizes P := Iff.rfl

/-- The marginal on factor `i` of a product is the `i`-th component. -/
lemma Dist.margAt_prod (p : ∀ i, Dist (Ω i)) (i : I) : (Dist.prod p).margAt i = p i := by
  sorry

lemma factorizes_prod (p : ∀ i, Dist (Ω i)) : Factorizes (Dist.prod p) := by
  sorry

/-- The remark after Definition C.2: `P` factorizes iff it is the outer product of its
one-factor marginals, `P = ⨂_{i∈I} P_i`. -/
lemma factorizes_iff_exists_prod (P : Dist (Pt Ω)) :
    Factorizes P ↔ ∃ p : ∀ i, Dist (Ω i), P = Dist.prod p := by
  sorry

lemma Factorizes.eq_prod_margAt {P : Dist (Pt Ω)} (h : Factorizes P) :
    P = Dist.prod fun i => P.margAt i := by
  sorry

/-- The set `Δ^F_C(Ω)` of factorizing distributions with `P(C) > 0` (§C.3). -/
def factorizingPos (C : Set (Pt Ω)) : Set (Dist (Pt Ω)) :=
  {P | Factorizes P ∧ 0 < P.prob C}

/-- **Factored space model.** `(Ω, O)` is a factored space model for a distribution `P`
on the observation space `Obs` if some distribution `P^Ω` factorizing over `Ω` has
`P^Ω(O = o) = P(o)` for all `o ∈ Obs`.  The model is the pair of the ambient factored
space `(I, Ω)` and the observation variable `O` (`dd:pi-space`).

Paper node: Definition 4.4 (§4.1). -/
def IsFactoredSpaceModel {Obs : Type w} [Fintype Obs] (O : Pt Ω → Obs) (P : Dist Obs) : Prop :=
  ∃ PΩ : Dist (Pt Ω), Factorizes PΩ ∧ ∀ o : Obs, PΩ.prob (fiber O o) = P.mass o

/-! ## Marginals, cylinders and outer products (Definitions C.1, C.2) -/

/-- **Marginal distribution.** `P_J = P ∘ U_J⁻¹`, a distribution on `Ω_J`.

Paper node: Definition C.2 (§C). -/
noncomputable def Dist.marg (P : Dist (Pt Ω)) (J : Finset I) : Dist (PtOn Ω J) := P.map (proj J)

lemma Dist.marg_mass (P : Dist (Pt Ω)) (J : Finset I) (α : PtOn Ω J) :
    (P.marg J).mass α = P.prob (proj J ⁻¹' {α}) := rfl

/-- Restriction of a family over `K` to a subset `J ⊆ K`. -/
def restrict {J K : Finset I} (h : J ⊆ K) (α : PtOn Ω K) : PtOn Ω J := fun i => α ⟨i, h i.2⟩

/-- **Outer product.** For disjoint `J`, `K` and distributions `P_J`, `P_K` on `Ω_J`,
`Ω_K`, the distribution `P_J ⊗ P_K` on `Ω_{J ∪ K}` with
`(P_J ⊗ P_K)(α) = P_J(α_J) · P_K(α_K)`.

Paper node: Definition C.1 (§C). -/
noncomputable def Dist.outer {J K : Finset I} (h : Disjoint J K) (PJ : Dist (PtOn Ω J))
    (PK : Dist (PtOn Ω K)) : Dist (PtOn Ω (J ∪ K)) where
  mass α := PJ.mass (restrict Finset.subset_union_left α) *
    PK.mass (restrict Finset.subset_union_right α)
  nonneg α := mul_nonneg (PJ.nonneg _) (PK.nonneg _)
  sum_eq_one := by
    sorry

/-- `Ω_{J ∪ (I∖J)} = Ω`. -/
def unionComplEquiv (J : Finset I) : PtOn Ω (J ∪ Jᶜ) ≃ Pt Ω where
  toFun α i := α ⟨i, by simp⟩
  invFun ω i := ω i
  left_inv α := by funext i; rfl
  right_inv ω := by funext i; rfl

/-- The paper's `P_J ⊗ P_{I∖J}`, read as a distribution on `Ω` itself:
`ω ↦ P_J(ω_J) · P_{I∖J}(ω_{I∖J})` (`outerCompl_mass`).  This is the form every use of
Definition C.1 in the paper takes. -/
noncomputable def Dist.outerCompl {J : Finset I} (PJ : Dist (PtOn Ω J)) (PK : Dist (PtOn Ω Jᶜ)) :
    Dist (Pt Ω) :=
  (Dist.outer disjoint_compl_right PJ PK).map (unionComplEquiv J)

lemma Dist.outerCompl_mass {J : Finset I} (PJ : Dist (PtOn Ω J)) (PK : Dist (PtOn Ω Jᶜ))
    (ω : Pt Ω) : (Dist.outerCompl PJ PK).mass ω = PJ.mass (proj J ω) * PK.mass (proj Jᶜ ω) := by
  sorry

/-- The cylinder over a set of `J`-families: `π_J⁻¹(A)`.  The paper's `A_J × B_{I∖J}` for
`A ⊆ Ω_J`, `B ⊆ Ω_{I∖J}` is `cyl J A ∩ cyl Jᶜ B`. -/
def cyl (J : Finset I) (A : Set (PtOn Ω J)) : Set (Pt Ω) := proj J ⁻¹' A

lemma splice_eq_cyl_inter (J : Finset I) (S T : Set (Pt Ω)) :
    splice J S T = cyl J (projSet J S) ∩ cyl Jᶜ (projSet Jᶜ T) := by
  sorry

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

/-- If `P` factorizes over `Ω` then `P = P_J ⊗ P_{I∖J}` for every `J`
(the remark after Definition C.2). -/
lemma Factorizes.eq_outerCompl {P : Dist (Pt Ω)} (h : Factorizes P) (J : Finset I) :
    P = Dist.outerCompl (P.marg J) (P.marg Jᶜ) := by
  sorry

/-- The marginal of a factorizing distribution factorizes over `Ω_J` in the same sense:
`P_J = ⨂_{i∈J} P_i` (remark after Definition C.2), stated pointwise. -/
lemma Factorizes.marg_mass {P : Dist (Pt Ω)} (h : Factorizes P) (J : Finset I) (α : PtOn Ω J) :
    (P.marg J).mass α = ∏ i : J, (P.margAt i).mass (α i) := by
  sorry

/-! ## Lemma C.11: supports -/

/-- **Support statements (1).** If `supp(P) ⊆ supp(Q)` and `P(C) > 0` then `Q(C) > 0`.

Paper node: Lemma C.11 (§C.3). -/
theorem Dist.prob_pos_of_support_subset {P Q : Dist (Pt Ω)} (h : P.support ⊆ Q.support)
    {C : Set (Pt Ω)} (hC : 0 < P.prob C) : 0 < Q.prob C := by
  sorry

/-- **Support statements (2).** If `P = P_J ⊗ P_{I∖J}` then
`supp(P) = supp(P_J) × supp(P_{I∖J})`.

Paper node: Lemma C.11 (§C.3). -/
theorem Dist.support_outerCompl {J : Finset I} (PJ : Dist (PtOn Ω J)) (PK : Dist (PtOn Ω Jᶜ)) :
    (Dist.outerCompl PJ PK).support = cyl J PJ.support ∩ cyl Jᶜ PK.support := by
  sorry

/-- **Support statements (3).** If `P = P_J ⊗ P_{I∖J}`, `Q = Q_J ⊗ Q_{I∖J}`,
`supp(P_J) ⊆ supp(Q_J)`, `supp(P_{I∖J}) ⊆ supp(Q_{I∖J})` and `P(C) > 0`, then `Q(C) > 0`.

The paper states this with only `supp(P_J) ⊆ supp(Q_J)`, which is false (take `P = δ_ω`,
`Q = δ_{ω_J} ⊗ δ_β` with `β ≠ ω_{I∖J}`, `C = {ω}`); its proof, and its only use
(Lemma C.12), take `Q_{I∖J} = P_{I∖J}`, which the second support inclusion covers.  See
`notes/paper-errata.md`.

Paper node: Lemma C.11 (§C.3). -/
theorem Dist.prob_pos_of_marg_support_subset {J : Finset I} {P Q : Dist (Pt Ω)}
    (hP : P = Dist.outerCompl (P.marg J) (P.marg Jᶜ))
    (hQ : Q = Dist.outerCompl (Q.marg J) (Q.marg Jᶜ))
    (h₁ : (P.marg J).support ⊆ (Q.marg J).support)
    (h₂ : (P.marg Jᶜ).support ⊆ (Q.marg Jᶜ).support)
    {C : Set (Pt Ω)} (hC : 0 < P.prob C) : 0 < Q.prob C := by
  sorry

/-! ## Definition 6.1: conditional independence -/

/-- **Conditional independence of events**, in the paper's product form:
`A ⊥^P B | C` iff `P(A ∩ C)·P(B ∩ C) = P(A ∩ B ∩ C)·P(C)`.  When `P(C) = 0` this holds
trivially — the paper's convention, and it is load-bearing (it is what makes the
intersection axiom fail); never restate it in the conditional form.

Paper node: Definition 6.1 (§6). -/
def CondIndep (P : Dist (Pt Ω)) (A B C : Set (Pt Ω)) : Prop :=
  P.prob (A ∩ C) * P.prob (B ∩ C) = P.prob (A ∩ B ∩ C) * P.prob C

/-- **Conditional independence of random variables**: `X ⊥^P Y | Z` iff
`x ⊥^P y | z` for all values `x, y, z`, where `x` is the event `{X = x}`.

Paper node: Definition 6.1 (§6). -/
def CondIndepVar {α β γ : Type*} (P : Dist (Pt Ω)) (X : Pt Ω → α) (Y : Pt Ω → β)
    (Z : Pt Ω → γ) : Prop :=
  ∀ (x : α) (y : β) (z : γ), CondIndep P (fiber X x) (fiber Y y) (fiber Z z)

/-- The paper's mixed notation `B ⊥^P Y | C` (an event, a variable, an event): `B ⊥^P y | C`
for all values `y` (§C.3, "Further notation for conditional independence"). -/
def CondIndepEventVar {β : Type*} (P : Dist (Pt Ω)) (B : Set (Pt Ω)) (Y : Pt Ω → β)
    (C : Set (Pt Ω)) : Prop :=
  ∀ y : β, CondIndep P B (fiber Y y) C

/-- The paper's mixed notation `X ⊥^P Y | C` (two variables, an event). -/
def CondIndepVarEvent {α β : Type*} (P : Dist (Pt Ω)) (X : Pt Ω → α) (Y : Pt Ω → β)
    (C : Set (Pt Ω)) : Prop :=
  ∀ (x : α) (y : β), CondIndep P (fiber X x) (fiber Y y) C

lemma CondIndep.symm {P : Dist (Pt Ω)} {A B C : Set (Pt Ω)} (h : CondIndep P A B C) :
    CondIndep P B A C := by
  unfold CondIndep at *
  rw [mul_comm, h]
  congr 2
  ext ω; simp only [Set.mem_inter_iff]; tauto

lemma CondIndep.of_prob_eq_zero {P : Dist (Pt Ω)} {A B C : Set (Pt Ω)} (h : P.prob C = 0) :
    CondIndep P A B C := by
  sorry

/-- The paper's `A ⊥^⊗ B | C`: independence in every factorizing distribution (§C.3). -/
def CondIndepAll (A B C : Set (Pt Ω)) : Prop :=
  ∀ P : Dist (Pt Ω), Factorizes P → CondIndep P A B C

/-! ## Lemmas C.13, C.14: decomposition of mixed independence -/

/-- **Decomposition of mixed independence.** `B ⊥^P (Y, Z) | C` implies `B ⊥^P Y | C`.

Paper node: Lemma C.13 (§C.3). -/
theorem CondIndepEventVar.of_pair {β γ : Type*} [Fintype γ] {P : Dist (Pt Ω)} {B C : Set (Pt Ω)}
    {Y : Pt Ω → β} {Z : Pt Ω → γ} (h : CondIndepEventVar P B (pair Y Z) C) :
    CondIndepEventVar P B Y C := by
  sorry

/-- **Corollary of decomposition.** For `J' ⊆ J`, `B ⊥^P U_J | C` implies `B ⊥^P U_{J'} | C`.

Paper node: Corollary C.14 (§C.3). -/
theorem CondIndepEventVar.of_proj_subset {P : Dist (Pt Ω)} {B C : Set (Pt Ω)} {J' J : Finset I}
    (hJ : J' ⊆ J) (h : CondIndepEventVar P B (proj J) C) : CondIndepEventVar P B (proj J') C := by
  sorry

/-! ## Lemma C.15: probability of a product event -/

/-- **Probability of a product event.** If `P = P_J ⊗ P_{I∖J}` then
`P(A_J × A_{I∖J}) = P_J(A_J) · P_{I∖J}(A_{I∖J})`.

Paper node: Lemma C.15 (§C.3). -/
theorem Dist.prob_cyl_inter_cyl {J : Finset I} {P : Dist (Pt Ω)}
    (hP : P = Dist.outerCompl (P.marg J) (P.marg Jᶜ)) (A : Set (PtOn Ω J)) (B : Set (PtOn Ω Jᶜ)) :
    P.prob (cyl J A ∩ cyl Jᶜ B) = (P.marg J).prob A * (P.marg Jᶜ).prob B := by
  sorry

/-! ## Lemma C.16: slicing at a `J`-value -/

/-- The paper's `D^α = {ω ∈ D | ω_J = α} = D ∩ U_J⁻¹(α)` (§C.3, eq. (D_alpha)). -/
def sliceAt (J : Finset I) (α : PtOn Ω J) (D : Set (Pt Ω)) : Set (Pt Ω) :=
  D ∩ fiber (proj J) α

/-- **Slicing (1).** For factorizing `P`: `P(D^α) = P_J(α) · P_{I∖J}(D^α_{I∖J})`.

Paper node: Lemma C.16 (§C.3). -/
theorem Factorizes.prob_sliceAt {P : Dist (Pt Ω)} (hP : Factorizes P) (J : Finset I)
    (α : PtOn Ω J) (D : Set (Pt Ω)) :
    P.prob (sliceAt J α D) = (P.marg J).mass α * (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α D)) := by
  sorry

/-- **Slicing (2).** `(δ_α ⊗ P_{I∖J})(D) = P_{I∖J}(D^α_{I∖J})`.  (The paper assumes `P`
factorizes here; the identity needs no such hypothesis.)

Paper node: Lemma C.16 (§C.3). -/
theorem Dist.prob_outerCompl_delta (P : Dist (Pt Ω)) (J : Finset I) (α : PtOn Ω J)
    (D : Set (Pt Ω)) :
    (Dist.outerCompl (Dist.delta α) (P.marg Jᶜ)).prob D =
      (P.marg Jᶜ).prob (projSet Jᶜ (sliceAt J α D)) := by
  sorry

/-! ## Lemma C.17: the history's factors are independent of the rest -/

/-- **`U_J ⊥^⊗ U_{I∖J} | C` for `J = H(A | C)`.**

Paper node: Lemma C.17 (§C.3). -/
theorem condIndepVarEvent_proj_history (A C : Set (Pt Ω)) (P : Dist (Pt Ω)) (hP : Factorizes P) :
    CondIndepVarEvent P (proj (eventHistory A C)) (proj (eventHistory A C)ᶜ) C := by
  sorry

end FactoredSpaces
