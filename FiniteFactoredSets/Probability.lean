import FiniteFactoredSets.CharacteristicOrthogonality
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-!
# Probability distributions and the fundamental theorem

This file is §5.4–§5.5 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): probability distributions on a set and on a factored set
(Definitions 36–37), their characterization by evaluation of characteristic polynomials
(Proposition 32), and the **fundamental theorem of finite factored sets** (Theorem 3):
conditional orthogonality is exactly conditional independence in every distribution on `F`.

## Modeling decision — `dd:probability`

The paper defines a probability distribution *elementarily* — a function
`P : 𝒫(S) → ℝ` that is nonnegative, `0` on `∅`, `1` on `S`, and finitely additive — and
states the fundamental theorem division-free (`P(x∩z)·P(y∩z) = P(x∩y∩z)·P(z)`).  The
formalization follows the paper verbatim: `ProbDist S` is that structure, with no
measure theory and no substitution.  A distribution *on `F`* (Definition 37) is the
predicate `FactoredSet.IsDistribution` on a `ProbDist S`.  Evaluation `Q^F_E(P)` is
`MvPolynomial.eval P.P (F.Q E)` (Definition 29).  A bridge to Mathlib's probability
vocabulary would be extra credit and must remain a separate lemma, never a stand-in.
`[Finite S]` is carried as the paper's "finite" hypothesis where used.
-/

universe u

open MvPolynomial

namespace FiniteFactoredSets

variable {S : Type u}

/-! ## §5.4 Probability distributions -/

/-- Definition 36: a probability distribution on `S` — `P : 𝒫(S) → ℝ`, nonnegative, `0` on
`∅`, `1` on `S`, and additive on disjoint sets.  (`dd:probability`; the paper says "finite
set `S`", and finiteness is carried by the statements, not the definition.)

Paper node: Definition 36 (§5.4). -/
structure ProbDist (S : Type u) where
  P : Set S → ℝ
  nonneg : ∀ E : Set S, 0 ≤ P E
  empty : P ∅ = 0
  univ : P Set.univ = 1
  additive : ∀ E₀ E₁ : Set S, Disjoint E₀ E₁ → P (E₀ ∪ E₁) = P E₀ + P E₁

namespace ProbDist

instance : CoeFun (ProbDist S) (fun _ => Set S → ℝ) := ⟨ProbDist.P⟩

/-- Definition 36's additivity, iterated: a probability distribution is the sum of its
singleton probabilities over any finite set.  Stated over a `Finset` so that the induction
is Mathlib's `Finset.induction_on`; `eq_sum_singleton_of_finite` is the `Set` form the
paper's Proposition 32 actually quotes ("`P(E) = ∑_{s ∈ E} …`"). -/
lemma eq_sum_singleton (P : ProbDist S) (T : Finset S) : P ↑T = ∑ s ∈ T, P {s} := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.coe_empty, P.empty, Finset.sum_empty]
  | @insert a T ha ih =>
      rw [Finset.coe_insert, Set.insert_eq,
        P.additive _ _ (Set.disjoint_singleton_left.2 (by simpa using ha)), ih,
        Finset.sum_insert ha]

lemma eq_sum_singleton_of_finite (P : ProbDist S) {E : Set S} (hE : E.Finite) :
    P E = ∑ s ∈ hE.toFinset, P {s} := by
  rw [← P.eq_sum_singleton hE.toFinset, hE.coe_toFinset]

end ProbDist

/-! ### Evaluating `mono`, `poly` and `Q` at a weight function

Definition 29's evaluation is `MvPolynomial.eval`, so these are all instances of `map_sum`
/ `map_prod` over the descriptions §5.1 already provides.  They are `private`: the paper
has no node for them, and every §5.4–§5.5 statement is phrased in `eval` directly. -/

section Eval

open scoped Classical

variable {S : Type u}

/-- `mono^F_C(s)` evaluates to the product of the weights of the blocks `[s]_b`, `b ∈ C`. -/
private lemma eval_mono (f : Set S → ℝ) {C : Set (Setoid S)} (hC : C.Finite) (s : S) :
    eval f (mono C s) = ∏ᶠ b ∈ C, f (part b s) := by
  rw [mono_eq_prod hC, map_prod, finprod_mem_eq_finite_toFinset_prod _ hC]
  simp

/-- A monomial evaluates positively at a strictly positive weight function. -/
private lemma eval_mono_pos {f : Set S → ℝ} (hf : ∀ v, 0 < f v) {C : Set (Setoid S)}
    (hC : C.Finite) (s : S) : 0 < eval f (mono C s) := by
  rw [mono_eq_prod hC, map_prod]
  exact Finset.prod_pos fun b _ => by simpa using hf (part b s)

/-- The paper's "a nonempty sum of products of positive real numbers, and thus positive". -/
private lemma eval_poly_pos [Finite S] {f : Set S → ℝ} (hf : ∀ v, 0 < f v)
    (C : Set (Setoid S)) {E : Set S} (hE : E.Nonempty) : 0 < eval f (poly C E) := by
  classical
  rw [poly_eq_sum_image, map_sum]
  refine Finset.sum_pos (fun m hm => ?_) ?_
  · obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hm
    exact eval_mono_pos hf (Set.toFinite C) s
  · obtain ⟨s, hs⟩ := hE
    exact ⟨mono C s, Finset.mem_image.2 ⟨s, (Set.Finite.mem_toFinset _).2 hs, rfl⟩⟩

/-- `poly^F_{b}([s]_b)` is the single variable `[s]_b`: every element of the block has the
same `b`-block, and `monos` is an image, so the sum collapses. -/
private lemma poly_singleton_part (b : Setoid S) (s : S) :
    poly {b} (part b s) = X (part b s) := by
  have hmono : ∀ t : S, mono ({b} : Set (Setoid S)) t = X (part b t) := fun _ =>
    finprod_mem_singleton
  have hm : monos ({b} : Set (Setoid S)) (part b s) = {X (part b s)} := by
    ext m
    simp only [monos, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hmono t, part_eq_iff.2 ht]
    · rintro rfl
      exact ⟨s, Setoid.refl' b s, (hmono s).trans rfl⟩
  rw [poly, hm, finsum_mem_singleton]

/-- The analytic step of Theorem 3: a real polynomial vanishing at every strictly positive
assignment is the zero polynomial.  The paper says "`q` is a polynomial that is zero on an
open subset of inputs, so `q` is the zero polynomial"; in Mathlib that is
`MvPolynomial.funext_set` at the box `∏ᵢ (0, ∞)`, whose sides are infinite. -/
private lemma eq_zero_of_eval_pos_eq_zero {σ : Type*} {p : MvPolynomial σ ℝ}
    (h : ∀ f : σ → ℝ, (∀ v, 0 < f v) → eval f p = 0) : p = 0 :=
  MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite 0)
    fun x hx => by rw [map_zero]; exact h x fun v => hx v (Set.mem_univ v)

end Eval

namespace FactoredSet

open scoped Classical

variable (F : FactoredSet S)

/-! ### Characteristic polynomials as a measure

`Q^F` is finitely additive in `E` and vanishes at `∅`; that plus positivity of its
evaluations is exactly Definition 36's checklist for the paper's `P_f`. -/

private lemma Q_empty : F.Q (∅ : Set S) = 0 := finsum_mem_empty

/-- `Q^F_{E₀ ∪ E₁} = Q^F_{E₀} + Q^F_{E₁}` for disjoint `E₀, E₁` — the additivity clause of
the paper's `P_f`, before dividing by `Q^F_S`. -/
private lemma Q_union_of_disjoint [Finite S] {E₀ E₁ : Set S} (hd : Disjoint E₀ E₁) :
    F.Q (E₀ ∪ E₁) = F.Q E₀ + F.Q E₁ :=
  finsum_mem_union hd (Set.toFinite E₀) (Set.toFinite E₁)

private lemma eval_Q_pos [Finite S] {f : Set S → ℝ} (hf : ∀ v, 0 < f v) {E : Set S}
    (hE : E.Nonempty) : 0 < eval f (F.Q E) := by
  rw [F.Q_eq_poly]
  exact eval_poly_pos hf _ hE

private lemma eval_Q_nonneg [Finite S] {f : Set S → ℝ} (hf : ∀ v, 0 < f v) (E : Set S) :
    0 ≤ eval f (F.Q E) := by
  rcases E.eq_empty_or_nonempty with rfl | hE
  · rw [F.Q_empty, map_zero]
  · exact (F.eval_Q_pos hf hE).le

/-! ### The two instances of Proposition 27 that Theorem 3 uses

The paper's proof of Theorem 3 applies Proposition 27 (`factor1`) at `C = {b}` twice, using
`χ^F_{b}([s]_b, S) = [s]_b` and `χ^F_{b}(S,S) = S`. -/

private lemma chimeraImage_univ_univ (C : Set (Setoid S)) :
    F.chimeraImage C Set.univ Set.univ = (Set.univ : Set S) :=
  Set.eq_univ_of_forall fun u => ⟨u, Set.mem_univ u, u, Set.mem_univ u, F.chimera_self C u⟩

private lemma chimeraImage_singleton_part {b : Setoid S} (hb : b ∈ F.B) (s : S) :
    F.chimeraImage {b} (part b s) Set.univ = part b s := by
  ext u
  constructor
  · rintro ⟨t, ht, r, -, rfl⟩
    exact b.trans' (F.chimera_rel_of_mem t r hb (Set.mem_singleton b)) ht
  · intro hu
    exact ⟨u, hu, u, Set.mem_univ u, F.chimera_self _ u⟩

private lemma singleton_union_sdiff {b : Setoid S} (hb : b ∈ F.B) :
    ({b} : Set (Setoid S)) ∪ (F.B \ {b}) = F.B :=
  Set.union_sdiff_cancel (Set.singleton_subset_iff.2 hb)

/-- Proposition 27 at `C₀ = {b}`, `C₁ = B ∖ {b}`, `E₀ = [s]_b`, `E₁ = S`. -/
private lemma Q_part_eq [Finite S] {b : Setoid S} (hb : b ∈ F.B) (s : S) :
    F.Q (part b s) = X (part b s) * poly (F.B \ {b}) (Set.univ : Set S) := by
  have h27 := F.poly_union_chimeraImage (Set.singleton_subset_iff.2 hb) (fun _ hc => hc.1)
    Set.disjoint_sdiff_right (part b s) Set.univ
  rw [F.chimeraImage_singleton_part hb s, F.singleton_union_sdiff hb] at h27
  rw [F.Q_eq_poly, h27, poly_singleton_part]

/-- Proposition 27 at `C₀ = {b}`, `C₁ = B ∖ {b}`, `E₀ = E₁ = S`. -/
private lemma Q_univ_eq [Finite S] {b : Setoid S} (hb : b ∈ F.B) :
    F.Q (Set.univ : Set S)
      = poly {b} (Set.univ : Set S) * poly (F.B \ {b}) (Set.univ : Set S) := by
  have h27 := F.poly_union_chimeraImage (Set.singleton_subset_iff.2 hb) (fun _ hc => hc.1)
    Set.disjoint_sdiff_right (Set.univ : Set S) Set.univ
  rw [F.chimeraImage_univ_univ, F.singleton_union_sdiff hb] at h27
  rw [F.Q_eq_poly, h27]

/-- Proposition 27 iterated over a subset of the basis at `E = S`: `poly^F_C(S)` is the
product of the one-factor polynomials `poly^F_{b}(S)`, `b ∈ C`.  This is what turns the
paper's per-factor computation of `P_f([s]_b)` into the product formula for `P_f({s})`. -/
private lemma poly_univ_finprod [Finite S] [Nonempty S] :
    ∀ {C : Set (Setoid S)}, C ⊆ F.B →
      poly C (Set.univ : Set S) = ∏ᶠ b ∈ C, poly {b} (Set.univ : Set S) := by
  intro C
  have hCfin : C.Finite := Set.toFinite C
  induction C, hCfin using Set.Finite.induction_on with
  | empty => intro _; rw [poly_empty Set.univ_nonempty, finprod_mem_empty]
  | @insert b C hbC hfin ih =>
      intro hsub
      have hbB : b ∈ F.B := hsub (Set.mem_insert _ _)
      have hCB : C ⊆ F.B := fun c hc => hsub (Set.mem_insert_of_mem _ hc)
      have h27 := F.poly_union_chimeraImage (Set.singleton_subset_iff.2 hbB) hCB
        (Set.disjoint_singleton_left.2 hbC) (Set.univ : Set S) Set.univ
      rw [F.chimeraImage_univ_univ] at h27
      rw [finprod_mem_insert _ hbC hfin, Set.insert_eq, h27, ih hCB]

/-! ## §5.4 Distributions on a factored set -/

/-- Definition 37: a probability distribution on the factored set `F` — a distribution on
`S` whose singleton probabilities factor through the factors: `P {s} = ∏_{b ∈ B} P [s]_b`.

Paper node: Definition 37 (§5.4). -/
def IsDistribution (P : ProbDist S) : Prop :=
  ∀ s : S, P {s} = ∏ᶠ b ∈ F.B, P (part b s)

/-- **Proposition 32** — a distribution on `S` is a distribution on `F` iff `P E = Q^F_E(P)`
for every `E ⊆ S` (Definition 29's evaluation).

Paper node: Proposition 32 (§5.4). -/
theorem isDistribution_iff [Finite S] (P : ProbDist S) :
    F.IsDistribution P ↔ ∀ E : Set S, P E = eval P.P (F.Q E) := by
  classical
  have hQs : ∀ s : S, F.Q {s} = mono F.B s := fun s => by
    rw [F.Q_eq_finsum_mono]; exact finsum_mem_singleton
  constructor
  · -- `P(E) = ∑_{s ∈ E} P({s}) = ∑_{s ∈ E} ∏_{b ∈ B} P([s]_b) = Q^F_E(P)`.
    intro h E
    rw [P.eq_sum_singleton_of_finite (Set.toFinite E), F.Q_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun s _ => by
      rw [h s, eval_mono P.P (Set.toFinite F.B) s]
  · -- The converse is the hypothesis at the singletons `E = {s}`.
    intro h s
    have hs := h {s}
    rwa [hQs s, eval_mono P.P (Set.toFinite F.B) s] at hs

/-! ### The paper's `P_f`

For a strictly positive weight function `f : 𝒫(S) → ℝ^{>0}`, the paper normalizes the
characteristic polynomials into a distribution `P_f(E) = Q^F_E(f)/Q^F_S(f)` and shows it is
a distribution on `F`.  `Nonempty S` is what makes the denominator positive. -/

private noncomputable def normalized [Finite S] [Nonempty S] (f : Set S → ℝ)
    (hf : ∀ v, 0 < f v) : ProbDist S where
  P E := eval f (F.Q E) / eval f (F.Q (Set.univ : Set S))
  nonneg E := div_nonneg (F.eval_Q_nonneg hf E) (F.eval_Q_pos hf Set.univ_nonempty).le
  empty := by rw [F.Q_empty, map_zero, zero_div]
  univ := div_self (ne_of_gt (F.eval_Q_pos hf Set.univ_nonempty))
  additive _ _ hd := by rw [F.Q_union_of_disjoint hd, map_add, add_div]

private lemma normalized_apply [Finite S] [Nonempty S] (f : Set S → ℝ) (hf : ∀ v, 0 < f v)
    (E : Set S) :
    (F.normalized f hf) E = eval f (F.Q E) / eval f (F.Q (Set.univ : Set S)) := rfl

private lemma isDistribution_normalized [Finite S] [Nonempty S] (f : Set S → ℝ)
    (hf : ∀ v, 0 < f v) : F.IsDistribution (F.normalized f hf) := by
  classical
  intro s
  -- `Q^F_S(f) = ∏_{b ∈ B} poly^F_{b}(S)(f)`.
  have hDprod : eval f (F.Q (Set.univ : Set S))
      = ∏ b ∈ (Set.toFinite F.B).toFinset, eval f (poly {b} (Set.univ : Set S)) := by
    rw [F.Q_eq_poly, F.poly_univ_finprod (subset_refl F.B),
      finprod_mem_eq_finite_toFinset_prod _ (Set.toFinite F.B), map_prod]
  -- `P_f([s]_b) = f([s]_b)/poly^F_{b}(S)(f)`, the paper's marginal computation.
  have hmarg : ∀ b ∈ F.B, (F.normalized f hf) (part b s)
      = f (part b s) / eval f (poly {b} (Set.univ : Set S)) := by
    intro b hb
    have hDb : eval f (poly (F.B \ {b}) (Set.univ : Set S)) ≠ 0 :=
      ne_of_gt (eval_poly_pos hf _ Set.univ_nonempty)
    rw [F.normalized_apply, F.Q_part_eq hb s, F.Q_univ_eq hb, map_mul, map_mul, eval_X,
      mul_div_mul_right _ _ hDb]
  have hRHS : (∏ᶠ b ∈ F.B, (F.normalized f hf) (part b s))
      = (∏ b ∈ (Set.toFinite F.B).toFinset, f (part b s))
        / ∏ b ∈ (Set.toFinite F.B).toFinset, eval f (poly {b} (Set.univ : Set S)) := by
    rw [finprod_mem_eq_finite_toFinset_prod _ (Set.toFinite F.B), ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun b hb => hmarg b ((Set.Finite.mem_toFinset _).1 hb)
  rw [hRHS, ← hDprod, F.normalized_apply]
  congr 1
  rw [show F.Q {s} = mono F.B s from by rw [F.Q_eq_finsum_mono]; exact finsum_mem_singleton,
    mono_eq_prod (Set.toFinite F.B), map_prod]
  exact Finset.prod_congr rfl fun b _ => by simp

/-! ## §5.5 The fundamental theorem of finite factored sets -/

/-- **Theorem 3** — the fundamental theorem of finite factored sets: `X ⊥^F Y | Z` iff for
every distribution `P` on `F` and all blocks `x ∈ X`, `y ∈ Y`, `z ∈ Z`,
`P(x∩z) · P(y∩z) = P(x∩y∩z) · P(z)`.

The forward direction is Lemma 3 (`Q_mul_Q_eq_of_orthogonalGiven`) evaluated through
Proposition 32.  The converse follows the paper: normalize an arbitrary strictly positive
weight function into a distribution `P_f` on `F`, deduce that the polynomial
`q = Q^F_{x∩z}·Q^F_{y∩z} - Q^F_{x∩y∩z}·Q^F_z` vanishes at every positive assignment, hence
is zero, hence clause 3 of Lemma 3 holds.  The paper opens the converse with a case split on
`S` being empty; here that case is absorbed rather than split, because a block `x ∈ X` comes
with an element of `S` and so supplies `Nonempty S` directly — over an empty `S` the goal is
vacuous, which is the same observation the paper's "`{}` is the unique partition" branch
makes.

Paper node: Theorem 3 (§5.5). -/
theorem orthogonalGiven_iff_forall_isDistribution [Finite S] (X Y Z : Setoid S) :
    F.OrthogonalGiven X Y Z ↔
      ∀ P : ProbDist S, F.IsDistribution P →
        ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
          P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z := by
  classical
  constructor
  · intro h P hP x hx y hy z hz
    have hQ := congrArg (eval P.P) (F.Q_mul_Q_eq_of_orthogonalGiven h hx hy hz)
    rw [map_mul, map_mul] at hQ
    have hE := (F.isDistribution_iff P).1 hP
    rw [hE (x ∩ z), hE (y ∩ z), hE (x ∩ y ∩ z), hE z,
      mul_comm (eval P.P (F.Q (x ∩ y ∩ z)))]
    exact hQ.symm
  · intro h
    refine F.orthogonalGiven_of_Q_mul_Q_eq ?_
    intro x hx y hy z hz
    haveI : Nonempty S := by obtain ⟨s₀, -⟩ := hx; exact ⟨s₀⟩
    have hq : F.Q (x ∩ z) * F.Q (y ∩ z) - F.Q (x ∩ y ∩ z) * F.Q z = 0 := by
      refine eq_zero_of_eval_pos_eq_zero fun f hf => ?_
      have hDne : eval f (F.Q (Set.univ : Set S)) ≠ 0 :=
        ne_of_gt (F.eval_Q_pos hf Set.univ_nonempty)
      have hDD : eval f (F.Q (Set.univ : Set S)) * eval f (F.Q (Set.univ : Set S)) ≠ 0 :=
        mul_ne_zero hDne hDne
      have key := h (F.normalized f hf) (F.isDistribution_normalized f hf) x hx y hy z hz
      rw [F.normalized_apply, F.normalized_apply, F.normalized_apply, F.normalized_apply,
        div_mul_div_comm, div_mul_div_comm, div_eq_div_iff hDD hDD] at key
      rw [map_sub, map_mul, map_mul, mul_right_cancel₀ hDD key, sub_self]
    rw [mul_comm (F.Q z)]
    exact (sub_eq_zero.1 hq).symm

end FactoredSet

/-! ## Client-style uses of the §5.4–§5.5 surface

Each endpoint applied the way a downstream consumer would apply it, so that a signature
that is inventoried and axiom-clean is also known to be *usable*. -/

section Clients

variable {S : Type u} [Finite S] (F : FactoredSet S) (P : ProbDist S)

/-- Definition 36 used as a measure: finite additivity gives the two-block decomposition a
client writes by hand. -/
example (E : Set S) : P E + P Eᶜ = 1 := by
  rw [← P.additive E Eᶜ disjoint_compl_right, Set.union_compl_self, P.univ]

/-- Proposition 32, forward: a distribution on `F` evaluates its own characteristic
polynomials. -/
example (hP : F.IsDistribution P) (E : Set S) : P E = eval P.P (F.Q E) :=
  (F.isDistribution_iff P).1 hP E

/-- Proposition 32, converse: the evaluation identity forces Definition 37's product
formula at every point. -/
example (h : ∀ E : Set S, P E = eval P.P (F.Q E)) (s : S) :
    P {s} = ∏ᶠ b ∈ F.B, P (part b s) :=
  (F.isDistribution_iff P).2 h s

/-- Theorem 3, forward: conditional orthogonality gives conditional independence in every
distribution on `F`. -/
example (X Y Z : Setoid S) (h : F.OrthogonalGiven X Y Z) (hP : F.IsDistribution P)
    {x y z : Set S} (hx : x ∈ X.classes) (hy : y ∈ Y.classes) (hz : z ∈ Z.classes) :
    P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z :=
  (F.orthogonalGiven_iff_forall_isDistribution X Y Z).1 h P hP x hx y hy z hz

/-- Theorem 3, converse, composed with Proposition 24: unconditional independence in every
distribution on `F` is unconditional orthogonality. -/
example (X Y : Setoid S)
    (h : ∀ P : ProbDist S, F.IsDistribution P → ∀ x ∈ X.classes, ∀ y ∈ Y.classes,
      ∀ z ∈ (⊤ : Setoid S).classes, P (x ∩ z) * P (y ∩ z) = P (x ∩ y ∩ z) * P z) :
    F.Orthogonal X Y :=
  (F.orthogonal_iff_orthogonalGiven_top X Y).2
    ((F.orthogonalGiven_iff_forall_isDistribution X Y ⊤).2 h)

end Clients

end FiniteFactoredSets
