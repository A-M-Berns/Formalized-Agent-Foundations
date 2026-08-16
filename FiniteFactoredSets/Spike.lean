/-
# FFS spike — NOT a formalization, a measurement.

Purpose: find out what it actually costs to prove the load-bearing lemma of
Garrabrant, *Temporal Inference with Finite Factored Sets* (arXiv:2109.11513) §5.1,
Proposition 20 ("if `p` divides `Q^F_E` then `p = r * poly^F_C(E)`"), against the
Mathlib pinned in this repo.  Everything downstream of that proposition — the `Irr`
factorization, Lemma CPO, and the Fundamental Theorem — routes through it, so it is
the one place where a hypothesis-shaped stub would formalize nothing.

Built with `lake env lean FiniteFactoredSets/Spike.lean`, which does NOT pick up the
lakefile's `autoImplicit := false`; set it here (recorded gotcha).
-/
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false

namespace FFSSpike

open MvPolynomial Finset

variable {σ R : Type*} [CommRing R]

/-! ## Stage A — products with variable-disjoint factors

The paper's phrase is "there can be no combining like terms, then, in the product
`pq`".  In Lean that is the statement that when `p` and `q` use disjoint variable
sets, the addition map `p.support × q.support → (p*q).support` is injective and
coefficient-multiplicative.  This is the reusable core; nothing about it is
FFS-specific.
-/

/-- A monomial exponent vector living entirely inside the variable set `V`. -/
private lemma filter_self_of_mem {V : σ → Prop} [DecidablePred V] {f : σ →₀ ℕ}
    (h : ∀ i, f i ≠ 0 → V i) : f.filter V = f :=
  (Finsupp.filter_eq_self_iff _ _).2 h

private lemma filter_zero_of_notMem {V : σ → Prop} [DecidablePred V] {f : σ →₀ ℕ}
    (h : ∀ i, f i ≠ 0 → ¬ V i) : f.filter V = 0 :=
  (Finsupp.filter_eq_zero_iff _ _).2 fun i hi => by
    by_contra hf; exact h i hf hi

/-- If every monomial of `p` is supported inside `V` and every monomial of `q` is
supported outside `V`, then the coefficient of `d + e` in `p * q` is just the product
of the coefficients — no other antidiagonal pair contributes.

This is the paper's "there can be no combining like terms, then, in the product `pq`". -/
theorem coeff_add_mul_of_split [DecidableEq σ] {p q : MvPolynomial σ R}
    (V : σ → Prop) [DecidablePred V]
    (hp : ∀ a ∈ p.support, ∀ i, a i ≠ 0 → V i)
    (hq : ∀ b ∈ q.support, ∀ i, b i ≠ 0 → ¬ V i)
    {d e : σ →₀ ℕ} (hd : ∀ i, d i ≠ 0 → V i) (he : ∀ i, e i ≠ 0 → ¬ V i) :
    coeff (d + e) (p * q) = coeff d p * coeff e q := by
  rw [coeff_mul]
  refine Finset.sum_eq_single (d, e) ?_ ?_
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    rcases eq_or_ne (coeff a p) 0 with h | hca
    · rw [h, zero_mul]
    rcases eq_or_ne (coeff b q) 0 with h | hcb
    · rw [h, mul_zero]
    exfalso
    have ha : ∀ i, a i ≠ 0 → V i := hp a (mem_support_iff.2 hca)
    have hb : ∀ i, b i ≠ 0 → ¬ V i := hq b (mem_support_iff.2 hcb)
    have key : a = d := by
      have h2 := congrArg (Finsupp.filter V) hab
      rwa [Finsupp.filter_add, Finsupp.filter_add, filter_self_of_mem ha,
        filter_zero_of_notMem hb, filter_self_of_mem hd, filter_zero_of_notMem he,
        add_zero, add_zero] at h2
    subst key
    have : b = e := add_left_cancel hab
    subst this
    exact hne rfl
  · intro h
    -- GOTCHA: `exact absurd (Finset.mem_antidiagonal.2 rfl) h` loops in `whnf` on the
    -- `Finsupp` antidiagonal instance; going through `simp only` is instant.
    simp only [Finset.mem_antidiagonal] at h
    exact absurd trivial h

/-! ## Stage B — the modeling decision

The FFS analogue of Cartesian Frames' `dd:universe`.  The paper's `F = (S,B)` has `B` a
*set of partitions* of `S`, not an indexed family — and that matters downstream, because
§5.2's `Irr^F(E)` is a partition *of `B` itself*.  So `B : Finset (Setoid S)`, and the
factorization condition is bijectivity of the map into the dependent product of the
quotients.

Variables of `Poly^F` range over `𝒫(S)`; rendered as `Finset S`, which for `Fintype S`
is equivalent to `Set S` and gives `DecidableEq` on variables for free.
-/

open scoped Classical in
/-- A finite factored set: `S` finite, together with a finite set `B` of partitions
whose joint-coordinate map is a bijection.

**The `nontrivial` field is load-bearing and easy to miss.**  The paper builds it into
the definition of factorization (Theorem 2, §2.3: "a set `B` of *nontrivial* partitions
of `S`"), and the spike found that dropping it is not harmless: without it, the
indiscrete partition of a singleton `S` is a legal factor, so both `{}` and `{Ind}`
factor a one-element set — which falsifies Proposition 6's *uniqueness* of the trivial
factorization, and removes the hypothesis Corollary 1 (`basisdisjoint`) is proved from.

Paper node: Definition 12 (§2.5). -/
structure FFS (S : Type*) [Fintype S] where
  B : Finset (Setoid S)
  bij : Function.Bijective (fun (s : S) (b : B) => Quotient.mk (b : Setoid S) s)
  nontrivial : ∀ b ∈ B, ∃ s t : S, ¬ b s t

namespace FFS

open scoped Classical

variable {S : Type*} [Fintype S]

/-- The part of the partition `b` containing `s` — the paper's `[s]_b`, an element of
`𝒫(S)` and hence a polynomial variable. -/
noncomputable def part (b : Setoid S) (s : S) : Finset S :=
  Finset.univ.filter (fun t => b t s)

lemma mem_part {b : Setoid S} {s t : S} : t ∈ part b s ↔ b t s := by
  simp [part]

lemma self_mem_part (b : Setoid S) (s : S) : s ∈ part b s :=
  mem_part.2 (b.refl' s)

/-- Distinct parts of the same partition are disjoint — the fact the paper leans on to
separate the supports of distinct monomials. -/
lemma part_eq_of_mem {b : Setoid S} {s t : S} (h : t ∈ part b s) : part b t = part b s := by
  ext u
  simp only [mem_part] at *
  exact ⟨fun hu => b.trans' hu h, fun hu => b.trans' hu (b.symm' h)⟩

lemma part_eq_iff {b : Setoid S} {s t : S} : part b s = part b t ↔ b s t := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hs : s ∈ part b t := h ▸ self_mem_part b s
    exact mem_part.1 hs
  · exact (part_eq_of_mem (mem_part.2 (b.symm' h))).symm

/-- The coordinate equivalence supplied by the factorization condition. -/
noncomputable def coord (F : FFS S) : S ≃ ((b : F.B) → Quotient (b : Setoid S)) :=
  Equiv.ofBijective _ F.bij

/-- The chimera function `χ^F_C(s,t)`: agree with `s` on the factors in `C`, with `t`
off it.

Paper node: Definition 9 (§2.3). -/
noncomputable def chimera (F : FFS S) (C : Finset (Setoid S)) (s t : S) : S :=
  F.coord.symm fun b => if (b : Setoid S) ∈ C then F.coord s b else F.coord t b

lemma coord_apply (F : FFS S) (s : S) (b : F.B) :
    F.coord s b = Quotient.mk (b : Setoid S) s := rfl

lemma coord_chimera (F : FFS S) (C : Finset (Setoid S)) (s t : S) (b : F.B) :
    F.coord (F.chimera C s t) b
      = if (b : Setoid S) ∈ C then F.coord s b else F.coord t b := by
  rw [chimera, F.coord.apply_symm_apply]

/-- `χ^F_C(s,t) ∼_b s` for `b ∈ C`.

Paper node: Proposition 4.1 (§2.3). -/
lemma chimera_rel_of_mem (F : FFS S) {C : Finset (Setoid S)} (s t : S) {b : Setoid S}
    (hb : b ∈ F.B) (hbC : b ∈ C) : b (F.chimera C s t) s := by
  have h := F.coord_chimera C s t ⟨b, hb⟩
  rw [if_pos hbC] at h
  exact Quotient.exact h

/-- `χ^F_C(s,t) ∼_b t` for `b ∉ C`.

Paper node: Proposition 4.2 (§2.3). -/
lemma chimera_rel_of_notMem (F : FFS S) {C : Finset (Setoid S)} (s t : S) {b : Setoid S}
    (hb : b ∈ F.B) (hbC : b ∉ C) : b (F.chimera C s t) t := by
  have h := F.coord_chimera C s t ⟨b, hb⟩
  rw [if_neg hbC] at h
  exact Quotient.exact h

/-- **Corollary 1 (`basisdisjoint`)** — distinct factors share no part.  This is the
squarefreeness input for the whole §5 polynomial development: it is exactly what makes
`b ↦ [s]_b` injective, hence `mono^F_B(s)` a squarefree monomial.

Paper node: Corollary 1 (§2.3). -/
lemma eq_of_part_eq (F : FFS S) {b₀ b₁ : Setoid S} (h₀ : b₀ ∈ F.B) (h₁ : b₁ ∈ F.B)
    {s t : S} (h : part b₀ s = part b₁ t) : b₀ = b₁ := by
  by_contra hne
  -- `b₀` is nontrivial, so some `u` sits in a different `b₀`-part from `s`.
  obtain ⟨x, y, hxy⟩ := F.nontrivial b₀ h₀
  have hu : ∃ u : S, ¬ b₀ u s := by
    by_contra hall
    have hall' : ∀ u, b₀ u s := fun u => not_not.1 fun h => hall ⟨u, h⟩
    exact hxy (b₀.trans' (hall' x) (b₀.symm' (hall' y)))
  obtain ⟨u, hus⟩ := hu
  -- Fuse: agree with `u` on `b₀`, with `t` on every other factor (in particular `b₁`).
  set r := F.chimera {b₀} u t with hr
  have hr0 : b₀ r u := F.chimera_rel_of_mem u t h₀ (Finset.mem_singleton_self b₀)
  have hr1 : b₁ r t := F.chimera_rel_of_notMem u t h₁ (by simpa using Ne.symm hne)
  -- `r` is in `[t]_{b₁} = [s]_{b₀}`, so `r ∼_{b₀} s` — but `r ∼_{b₀} u ≁_{b₀} s`.
  have hmem : r ∈ part b₁ t := mem_part.2 hr1
  rw [← h] at hmem
  exact hus (b₀.trans' (b₀.symm' hr0) (mem_part.1 hmem))

/-! ## Stage C — characteristic polynomials -/

/-- `mono^F_C(s) = ∏_{b ∈ C} [s]_b`. -/
noncomputable def mono (C : Finset (Setoid S)) (s : S) : MvPolynomial (Finset S) ℝ :=
  ∏ b ∈ C, MvPolynomial.X (part b s)

/-- The characteristic polynomial `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b`.

Paper node: Definition 33 (§5.1). -/
noncomputable def Q (F : FFS S) (E : Finset S) : MvPolynomial (Finset S) ℝ :=
  ∑ s ∈ E, mono F.B s

/-- Two elements of `S` agreeing on every factor are equal — the factorization
condition, in the form the monomial-injectivity argument uses.

Paper node: Proposition 8 (§2.2). -/
lemma eq_of_forall_part_eq (F : FFS S) {s t : S} (h : ∀ b ∈ F.B, part b s = part b t) :
    s = t := by
  refine F.bij.1 ?_
  funext b
  have hb := h b b.2
  refine Quotient.sound ?_
  have : s ∈ part b t := hb ▸ self_mem_part (b : Setoid S) s
  exact mem_part.1 this

/-! ## Stage D — the `factor2` measurement

`factor2` (Proposition 20) is the load-bearing proposition: every divisor of `Q^F_E` is
`r * poly^F_C(E)`.  Its first step — "if there were some `T ∈ supp(p) ∩ supp(q)`, then
the degree of `T` in `Q^F_E` would be at least 2, contradicting the definition of
`Q^F_E` and Corollary 1" — is what the rest of the argument stands on, and is proved
here in full.
-/

/-- The degree of a variable in `mono^F_C(s)` counts the factors whose part is that
variable — and by Corollary 1 there is at most one of them. -/
lemma degreeOf_mono {C : Finset (Setoid S)} (s : S) (v : Finset S) :
    (mono C s).degreeOf v = (C.filter fun b => v = part b s).card := by
  rw [mono, degreeOf_prod_eq _ _ fun b _ => X_ne_zero _, Finset.card_filter]
  exact Finset.sum_congr rfl fun b _ => by rw [degreeOf_X]

/-- `Q^F_E` is multilinear: no variable occurs squared.  This is precisely where
Corollary 1 (`eq_of_part_eq`) does its work. -/
lemma degreeOf_mono_le (F : FFS S) {C : Finset (Setoid S)} (hC : C ⊆ F.B) (s : S)
    (v : Finset S) : (mono C s).degreeOf v ≤ 1 := by
  rw [degreeOf_mono s v]
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  simp only [Finset.mem_filter] at ha hb
  exact F.eq_of_part_eq (hC ha.1) (hC hb.1) (ha.2.symm.trans hb.2)

lemma degreeOf_sum_mono_le (F : FFS S) {C : Finset (Setoid S)} (hC : C ⊆ F.B)
    (E : Finset S) (v : Finset S) : (∑ s ∈ E, mono C s).degreeOf v ≤ 1 := by
  classical
  induction E using Finset.induction_on with
  | empty => simp
  | insert a E ha ih =>
      rw [Finset.sum_insert ha]
      exact le_trans (degreeOf_add_le _ _ _) (max_le (F.degreeOf_mono_le hC a v) ih)

lemma degreeOf_Q_le (F : FFS S) (E : Finset S) (v : Finset S) : (Q F E).degreeOf v ≤ 1 :=
  F.degreeOf_sum_mono_le (subset_refl _) E v

lemma Q_ne_zero (F : FFS S) {E : Finset S} (hE : E.Nonempty) : Q F E ≠ 0 := by
  intro h
  have hev : MvPolynomial.eval (fun _ => (1 : ℝ)) (Q F E) = (E.card : ℝ) := by
    simp [Q, mono]
  rw [h, map_zero] at hev
  exact absurd hev.symm (by exact_mod_cast hE.card_pos.ne')

/-- **`factor2`, step (i).**  In any factorization `p * q = Q^F_E` of a characteristic
polynomial, the two factors share no variable.

Paper node: Proposition 20 (§5.1), first paragraph. -/
theorem vars_disjoint_of_mul_eq_Q (F : FFS S) {E : Finset S} (hE : E.Nonempty)
    {p q : MvPolynomial (Finset S) ℝ} (h : p * q = Q F E) :
    Disjoint p.vars q.vars := by
  classical
  have hQ : Q F E ≠ 0 := F.Q_ne_zero hE
  have hp : p ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hQ h.symm
  have hq : q ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hQ h.symm
  rw [Finset.disjoint_left]
  intro v hvp hvq
  have h2 : 2 ≤ (Q F E).degreeOf v := by
    rw [← h, degreeOf_mul_eq hp hq]
    have := mem_vars_iff_degreeOf_ne_zero.1 hvp
    have := mem_vars_iff_degreeOf_ne_zero.1 hvq
    omega
  exact absurd (F.degreeOf_Q_le E v) (by omega)

/-! ## Stage F — non-vacuity by construction

The repo standard wants the hypotheses of `FFS` witnessed by a real object, not
asserted.  The discrete factorization of `Bool` is the smallest one that exercises
every field, including the `nontrivial` one added above. -/

open scoped Classical in
noncomputable def boolFFS : FFS Bool where
  B := {⊥}
  bij := by
    constructor
    · intro s t h
      exact Quotient.exact (congrFun h ⟨⊥, Finset.mem_singleton_self _⟩)
    · intro g
      refine ⟨Quotient.out (g ⟨⊥, Finset.mem_singleton_self _⟩), ?_⟩
      funext b
      obtain ⟨b, hb⟩ := b
      rw [Finset.mem_singleton] at hb
      subst hb
      exact Quotient.out_eq _
  nontrivial := by
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨true, false, by simp⟩

example : (boolFFS.B).card = 1 := rfl

end FFS

/-! ## Stage E — the Fundamental Theorem's analytic step

The proof of Theorem 3 ends: "`q` is a polynomial that is zero on an open subset of
inputs, so `q` is the zero polynomial."  That reads like the hard part of the paper and
is in fact a direct instance of `MvPolynomial.funext_set` at `Set.Ioi 0`. -/
theorem eq_zero_of_eval_pos_eq_zero {σ : Type*} {p : MvPolynomial σ ℝ}
    (h : ∀ f : σ → ℝ, (∀ v, 0 < f v) → MvPolynomial.eval f p = 0) : p = 0 :=
  MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ)) (fun _ => Set.Ioi_infinite 0)
    fun x hx => by rw [map_zero]; exact h x fun v => hx v (Set.mem_univ v)

end FFSSpike

-- Axiom check on the results this spike actually measures.
#print axioms FFSSpike.coeff_add_mul_of_split
#print axioms FFSSpike.FFS.eq_of_part_eq
#print axioms FFSSpike.FFS.vars_disjoint_of_mul_eq_Q
#print axioms FFSSpike.eq_zero_of_eval_pos_eq_zero
#print axioms FFSSpike.FFS.boolFFS
