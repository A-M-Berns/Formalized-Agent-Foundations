import FiniteFactoredSets.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Real.Basic

/-!
# Characteristic polynomials

This file is §5.1 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): the polynomial ring `Poly^F`, the characteristic polynomial `Q^F_E` of
a subset, the monomials `mono^F_C(s)`, `monos^F_C(E)`, `poly^F_C(E)`, and the two
factoring propositions the rest of §5 rests on — Proposition 27 (`factor1`) and
Proposition 28 (`factor2`, the load-bearing lemma of the paper).

It also carries the monomial-level description of `poly^F_C(E)` that §5.2 consumes:
`mono^F_C(s)` is a monic monomial, so for `C ⊆ B` (where Corollary 1 makes it
*squarefree*) the coefficients, support, variables and degrees of `poly^F_C(E)` are all
read off the single exponent vector `monoExp C s`.

## Modeling decision — `dd:poly`

* `Poly^F` is `MvPolynomial (Set S) ℝ`: the paper's variables are the subsets `𝒫(S)`
  themselves, and under `dd:partition` a block `[s]_b` *is* the set `part b s`, so it is a
  variable verbatim (`MvPolynomial.X (part b s)`).  Definition 28 depends on `S` only, and
  is stated that way (`Poly S`).
* Definition 29's evaluation `p(f)` is `MvPolynomial.eval f p`, and Definition 30's
  support `supp(p)` is `MvPolynomial.vars p` — both rendered by Mathlib vocabulary with no
  declaration of ours, so neither is inventoried; they belong in the README's table of
  Mathlib-rendered nodes, whose §5 rows land with this stage's README update.
* Sums and products over *sets* (`∑_{s ∈ E}`, `∏_{b ∈ B}`) are `finsum`/`finprod`, so the
  definitions carry no finiteness hypothesis, and each statement carries the weakest
  finiteness its own proof consumes (`dd:finiteness-minimal`).  This is the section where
  `Finite S` genuinely enters — for infinite `S` a `finsum` over an infinite `E` is `0`,
  and nothing below is claimed about that junk value — but it does not enter uniformly:
  `mono_eq_iff`, Proposition 26 (`Q_eq_poly`) and `degreeOf_Q_le` need only `Finite F.B`,
  and `degreeOf_poly_le` needs no finiteness at all.  The exact carrier list is maintained
  in the "Finiteness" section of `API.lean`.
* Irreducibility (Proposition 31, next file) is Mathlib's `Irreducible` in this ring; over
  the field `ℝ` its units are the nonzero constants, so it coincides with the paper's
  "no factorization into two polynomials of nonempty support".
-/

universe u

open MvPolynomial

namespace FiniteFactoredSets

variable {S : Type u}

/-- Definition 28: the ring of polynomials with real coefficients and variables in `𝒫(S)`
(the paper's `Poly^F`, which depends only on `S`).

Paper node: Definition 28 (§5.1). -/
abbrev Poly (S : Type u) := MvPolynomial (Set S) ℝ

section Split

variable {σ : Type*}

private lemma filter_self_of_mem {V : σ → Prop} [DecidablePred V] {f : σ →₀ ℕ}
    (h : ∀ i, f i ≠ 0 → V i) : f.filter V = f :=
  (Finsupp.filter_eq_self_iff _ _).2 h

private lemma filter_zero_of_notMem {V : σ → Prop} [DecidablePred V] {f : σ →₀ ℕ}
    (h : ∀ i, f i ≠ 0 → ¬ V i) : f.filter V = 0 :=
  (Finsupp.filter_eq_zero_iff _ _).2 fun i hi => by
    by_contra hf; exact h i hf hi

/-- **`coeff_add_mul_of_split`** — when two polynomials have disjoint variable sets there is
no combining of like terms in their product: the coefficient of `a + b` in `p * q`, for
`a` supported in `p`'s variables and `b` in `q`'s, is `coeff a p * coeff b q`.  This is the
generic fact behind Proposition 28's "there can be no combining like terms"; it is not
FFS-specific and is upstreamable. -/
lemma coeff_add_mul_of_split {σ : Type*} {p q : MvPolynomial σ ℝ}
    (hpq : Disjoint p.vars q.vars) {a b : σ →₀ ℕ}
    (ha : ∀ i ∈ a.support, i ∈ p.vars) (hb : ∀ i ∈ b.support, i ∈ q.vars) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  classical
  have hp : ∀ c ∈ p.support, ∀ i, c i ≠ 0 → i ∈ p.vars := fun c hc i hi =>
    support_subset_vars_of_mem_support hc (Finsupp.mem_support_iff.2 hi)
  have hq : ∀ c ∈ q.support, ∀ i, c i ≠ 0 → i ∉ p.vars := fun c hc i hi =>
    Finset.disjoint_right.1 hpq
      (support_subset_vars_of_mem_support hc (Finsupp.mem_support_iff.2 hi))
  have hda : ∀ i, a i ≠ 0 → i ∈ p.vars := fun i hi => ha i (Finsupp.mem_support_iff.2 hi)
  have hdb : ∀ i, b i ≠ 0 → i ∉ p.vars := fun i hi =>
    Finset.disjoint_right.1 hpq (hb i (Finsupp.mem_support_iff.2 hi))
  rw [coeff_mul]
  refine Finset.sum_eq_single (a, b) ?_ ?_
  · rintro ⟨c, d⟩ hcd hne
    rw [Finset.mem_antidiagonal] at hcd
    rcases eq_or_ne (coeff c p) 0 with h | hcp
    · rw [h, zero_mul]
    rcases eq_or_ne (coeff d q) 0 with h | hdq
    · rw [h, mul_zero]
    exfalso
    have hc : ∀ i, c i ≠ 0 → i ∈ p.vars := hp c (mem_support_iff.2 hcp)
    have hd : ∀ i, d i ≠ 0 → i ∉ p.vars := hq d (mem_support_iff.2 hdq)
    have key : c = a := by
      have h2 := congrArg (Finsupp.filter (· ∈ p.vars)) hcd
      rwa [Finsupp.filter_add, Finsupp.filter_add, filter_self_of_mem hc,
        filter_zero_of_notMem hd, filter_self_of_mem hda, filter_zero_of_notMem hdb,
        add_zero, add_zero] at h2
    subst key
    have : d = b := add_left_cancel hcd
    subst this
    exact hne rfl
  · intro h
    -- `exact absurd (Finset.mem_antidiagonal.2 rfl) h` loops in `whnf` on the `Finsupp`
    -- antidiagonal instance; going through `simp only` is instant.
    simp only [Finset.mem_antidiagonal] at h
    exact absurd trivial h

end Split

/-- Definition 32: the monomial `mono^F_C(s) = ∏_{b ∈ C} [s]_b`.  The paper's superscript
`F` is notational — the monomial depends on `C` and `s` only — so, unlike `Q`, this is not
a `FactoredSet` operation (compare `size`, whose `F` argument is likewise vestigial).

Paper node: Definition 32 (§5.1). -/
noncomputable def mono (C : Set (Setoid S)) (s : S) : Poly S :=
  ∏ᶠ b ∈ C, X (part b s)

/-- Definition 33: `monos^F_C(E) = {mono^F_C(s) | s ∈ E}`.

Paper node: Definition 33 (§5.1). -/
def monos (C : Set (Setoid S)) (E : Set S) : Set (Poly S) := mono C '' E

/-- Definition 34: `poly^F_C(E) = ∑_{m ∈ monos^F_C(E)} m`.

Paper node: Definition 34 (§5.1). -/
noncomputable def poly (C : Set (Setoid S)) (E : Set S) : Poly S :=
  ∑ᶠ m ∈ monos C E, m

/-- `poly^F_∅(E) = 1` for nonempty `E`: the empty product is `1`, and `monos` being an
*image* collapses the constant family to the single monomial `1`.  This degenerate corner
of Definitions 32–34 is what makes an empty factor set in Proposition 28 produce a *unit*
(hence Proposition 31's case split), and what makes Proposition 27 at `C₁ = ∅` an
invariance rather than a factorization.  No finiteness is needed. -/
lemma poly_empty {E : Set S} (hE : E.Nonempty) : poly (∅ : Set (Setoid S)) E = 1 := by
  have hmono : ∀ s : S, mono (∅ : Set (Setoid S)) s = 1 := fun _ => finprod_mem_empty
  rw [poly, monos, show (mono (∅ : Set (Setoid S))) '' E = {1} by
    rw [show (mono (∅ : Set (Setoid S))) = fun _ => (1 : Poly S) from funext hmono]
    exact hE.image_const 1]
  exact finsum_mem_singleton

/-! ### Elementary rewriting of `mono` and `poly` -/

lemma mono_eq_prod {C : Set (Setoid S)} (hC : C.Finite) (s : S) :
    mono C s = ∏ b ∈ hC.toFinset, X (part b s) :=
  finprod_mem_eq_finite_toFinset_prod _ hC

lemma mono_congr {C : Set (Setoid S)} {s t : S} (h : ∀ b ∈ C, part b s = part b t) :
    mono C s = mono C t :=
  finprod_mem_congr rfl fun b hb => by rw [h b hb]

lemma mono_union {C D : Set (Setoid S)} (hd : Disjoint C D) (hC : C.Finite) (hD : D.Finite)
    (s : S) : mono (C ∪ D) s = mono C s * mono D s :=
  finprod_mem_union hd hC hD

private lemma X_ne_one (v : Set S) : (X v : Poly S) ≠ 1 := fun h => by
  simpa using congrArg (eval fun _ => (0 : ℝ)) h

/-- The junk value of Definition 32 at an infinite factor set: `∏ᶠ` collapses to `1`.  No
`C ⊆ B` is needed — no variable `X v` is `1`, so the multiplicative support is all of `C`. -/
private lemma mono_eq_one_of_infinite {C : Set (Setoid S)} (hC : ¬ C.Finite) (s : S) :
    mono C s = 1 :=
  finprod_mem_eq_one_of_infinite <| by
    rw [Set.inter_eq_self_of_subset_left
      fun b _ => Function.mem_mulSupport.2 (X_ne_one (part b s))]
    exact hC

/-- A `finsum` of polynomials whose members all have `v`-degree at most `n` has `v`-degree
at most `n`, junk value included: an infinite support gives `0`.  This is what lets the
squarefreeness of `poly^F_C(E)` be stated with no finiteness hypothesis at all. -/
private lemma degreeOf_finsum_mem_le {ι : Type*} {f : ι → Poly S} {t : Set ι} {v : Set S}
    {n : ℕ} (h : ∀ i ∈ t, (f i).degreeOf v ≤ n) : (∑ᶠ i ∈ t, f i).degreeOf v ≤ n := by
  by_cases hfin : (t ∩ Function.support f).Finite
  · rw [finsum_mem_eq_sum f hfin]
    exact (degreeOf_sum_le v _ f).trans
      (Finset.sup_le fun i hi => h i (hfin.mem_toFinset.1 hi).1)
  · rw [finsum_mem_eq_zero_of_infinite hfin, degreeOf_zero]
    exact Nat.zero_le _

lemma poly_eq_sum_image [Finite S] (C : Set (Setoid S)) (E : Set S) :
    poly C E = ∑ m ∈ (Set.toFinite E).toFinset.image (mono C), m := by
  have h : monos C E = ↑((Set.toFinite E).toFinset.image (mono C)) := by
    rw [monos, Finset.coe_image, Set.Finite.coe_toFinset]
  rw [poly, h, finsum_mem_coe_finset]

/-! ### The monomial layer

`mono^F_C(s)` is a product of variables, hence the monic monomial `monomial (monoExp C s) 1`
for the exponent vector `monoExp C s = ∑_{b ∈ C} δ_{[s]_b}`.  That one description carries
every fact §5 needs about the coefficients, support, variables and degrees of `poly^F_C(E)`.
The exponent vector itself is an implementation detail and stays private; the statements it
proves are phrased in the paper's own vocabulary (`mono`, `monos`, `poly`).

For `C ⊆ B` the vector is `0`/`1`-valued — that is Corollary 1 (`eq_of_part_eq`) at work,
and it is why the squarefreeness facts below are stated inside the `FactoredSet` namespace
with a `C ⊆ B` hypothesis. -/

open scoped Classical

private lemma prod_X_eq_monomial {ι : Type*} (t : Finset ι) (f : ι → Set S) :
    (∏ i ∈ t, (X (f i) : Poly S)) = monomial (∑ i ∈ t, Finsupp.single (f i) 1) 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← pow_one (X (f a)),
        X_pow_eq_monomial, monomial_mul, mul_one]

/-- The exponent vector of the monomial `mono^F_C(s)`. -/
private noncomputable def monoExp (C : Set (Setoid S)) (s : S) : (Set S) →₀ ℕ :=
  ∑ᶠ b ∈ C, Finsupp.single (part b s) 1

private lemma monoExp_eq_sum {C : Set (Setoid S)} (hC : C.Finite) (s : S) :
    monoExp C s = ∑ b ∈ hC.toFinset, Finsupp.single (part b s) 1 := by
  rw [monoExp, ← finsum_mem_coe_finset, Set.Finite.coe_toFinset]

private lemma mono_eq_monomial {C : Set (Setoid S)} (hC : C.Finite) (s : S) :
    mono C s = monomial (monoExp C s) 1 := by
  rw [mono_eq_prod hC, monoExp_eq_sum hC, prod_X_eq_monomial]

private lemma poly_eq_finsum_monomial {C : Set (Setoid S)} (hC : C.Finite) (E : Set S) :
    poly C E = ∑ᶠ d ∈ monoExp C '' E, monomial d 1 := by
  have hm : mono C = fun s => (monomial (monoExp C s) 1 : Poly S) :=
    funext (mono_eq_monomial hC)
  rw [poly, monos, hm, ← Set.image_image (fun d => (monomial d 1 : Poly S)) (monoExp C),
    finsum_mem_image (Function.Injective.injOn (monomial_left_injective one_ne_zero))]

private lemma coeff_poly_monoExp [Finite S] (C : Set (Setoid S)) (E : Set S)
    (d : (Set S) →₀ ℕ) :
    coeff d (poly C E) = if d ∈ monoExp C '' E then 1 else 0 := by
  have hfin : (monoExp C '' E).Finite := (Set.toFinite E).image _
  rw [poly_eq_finsum_monomial (Set.toFinite C), ← hfin.coe_toFinset, finsum_mem_coe_finset,
    coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' hfin.toFinset d (fun _ => (1 : ℝ))]
  simp

private lemma mem_support_poly_monoExp [Finite S] (C : Set (Setoid S)) (E : Set S)
    {d : (Set S) →₀ ℕ} : d ∈ (poly C E).support ↔ d ∈ monoExp C '' E := by
  rw [mem_support_iff, coeff_poly_monoExp]
  split_ifs with h <;> simp [h]

private lemma monomial_mem_monos_iff [Finite S] (C : Set (Setoid S)) (E : Set S)
    (d : (Set S) →₀ ℕ) :
    (monomial d (1 : ℝ) : Poly S) ∈ monos C E ↔ d ∈ monoExp C '' E := by
  rw [monos, Set.mem_image, Set.mem_image]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [mono_eq_monomial (Set.toFinite C)]
  exact ⟨fun h => monomial_left_injective one_ne_zero h, fun h => by rw [h]⟩

/-- Every coefficient of `poly^F_C(E)` is `0` or `1`, and it is `1` exactly on the monomials
of `monos^F_C(E)`.  (Definition 33 is an *image*, so a monomial occurring for several points
of `E` still occurs once.) -/
lemma coeff_poly [Finite S] (C : Set (Setoid S)) (E : Set S) (d : (Set S) →₀ ℕ) :
    coeff d (poly C E) = if (monomial d (1 : ℝ) : Poly S) ∈ monos C E then 1 else 0 := by
  rw [coeff_poly_monoExp C E d]
  exact if_congr (monomial_mem_monos_iff C E d).symm rfl rfl

/-- The *coefficient* support of `poly^F_C(E)` read as Definition 33: an exponent vector
occurs iff its monic monomial is one of the `C`-monomials of `E`.  This is Mathlib's
`MvPolynomial.support` — the finset of exponent vectors with nonzero coefficient — and not
the paper's `supp` of Definition 30, which is `MvPolynomial.vars` (see `mem_vars_poly`). -/
lemma mem_support_poly [Finite S] (C : Set (Setoid S)) (E : Set S) {d : (Set S) →₀ ℕ} :
    d ∈ (poly C E).support ↔ (monomial d (1 : ℝ) : Poly S) ∈ monos C E := by
  rw [mem_support_poly_monoExp, monomial_mem_monos_iff]

/-- `poly^F_C(E)` is nonzero for nonempty `E` — its monomials all have coefficient `1`, so
none of them cancels. -/
lemma poly_ne_zero [Finite S] (C : Set (Setoid S)) {E : Set S} (hE : E.Nonempty) :
    poly C E ≠ 0 := by
  obtain ⟨s, hs⟩ := hE
  intro h
  have hco := coeff_poly_monoExp C E (monoExp C s)
  rw [h, if_pos ⟨s, hs, rfl⟩] at hco
  simp at hco

private lemma monos_eq_image_support [Finite S] (C : Set (Setoid S)) (E : Set S) :
    monos C E = (fun d => (monomial d (1 : ℝ) : Poly S)) '' ↑(poly C E).support := by
  have hsupp : ↑(poly C E).support = monoExp C '' E := by
    ext d; rw [Finset.mem_coe]; exact mem_support_poly_monoExp C E
  have hm : mono C = fun s => (monomial (monoExp C s) 1 : Poly S) :=
    funext (mono_eq_monomial (Set.toFinite C))
  rw [monos, hm, hsupp, Set.image_image]

/-- `poly^F_C(E)` determines `monos^F_C(E)`: the monomial set is the image of the
coefficient support, so two `C`-polynomials with the same coefficient support have the same
monomials.  "Support" here is Mathlib's `MvPolynomial.support`, the set of exponent vectors
with nonzero coefficient — *not* the paper's `supp` of Definition 30, which is
`MvPolynomial.vars`, the set of occurring variables.  Proposition 31 uses this to recover a
point of `E` from an equality of polynomials up to a nonzero constant. -/
lemma monos_eq_of_support_eq [Finite S] {C : Set (Setoid S)} {E E' : Set S}
    (h : (poly C E).support = (poly C E').support) : monos C E = monos C E' := by
  rw [monos_eq_image_support, monos_eq_image_support, h]

namespace FactoredSet

variable (F : FactoredSet S)

/-! ## §5.1 Characteristic polynomials -/

/-- Definition 31: the characteristic polynomial `Q^F_E = ∑_{s ∈ E} ∏_{b ∈ B} [s]_b`.

Paper node: Definition 31 (§5.1). -/
noncomputable def Q (E : Set S) : Poly S :=
  ∑ᶠ s ∈ E, ∏ᶠ b ∈ F.B, X (part b s)

/-- `Q^F_E` is the sum of `mono^F_B` over `E`. -/
lemma Q_eq_finsum_mono (E : Set S) : F.Q E = ∑ᶠ s ∈ E, mono F.B s := rfl

lemma Q_eq_sum [Finite S] (E : Set S) :
    F.Q E = ∑ s ∈ (Set.toFinite E).toFinset, mono F.B s :=
  finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite E)

/-- The exponent of a variable in `mono^F_C(s)` is `1` if the variable is one of the blocks
`[s]_b`, `b ∈ C`, and `0` otherwise.  Corollary 1 (`eq_of_part_eq`) is what rules out two
factors of `C` contributing the same variable, which is why `C ⊆ B` is needed.  The
finiteness of `C` is a hypothesis rather than an instance on `F.B`, so that the squarefree
facts below can be stated for an arbitrary basis. -/
private lemma monoExp_apply {C : Set (Setoid S)} (hCfin : C.Finite) (hC : C ⊆ F.B) (s : S)
    (v : Set S) : monoExp C s v = if ∃ b ∈ C, part b s = v then 1 else 0 := by
  rw [monoExp_eq_sum hCfin, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  split_ifs with h
  · obtain ⟨b₀, hb₀C, hb₀⟩ := h
    rw [Finset.sum_eq_single b₀]
    · rw [if_pos hb₀]
    · intro b hb hne
      rw [if_neg]
      intro hbv
      exact hne (F.eq_of_part_eq (hC (by simpa using hb)) (hC hb₀C) (hbv.trans hb₀.symm))
    · intro hb₀f
      exact absurd (by simpa using hb₀C) hb₀f
  · exact Finset.sum_eq_zero fun b hb => if_neg fun hbv => h ⟨b, by simpa using hb, hbv⟩

private lemma monoExp_ne_zero_iff [Finite F.B] {C : Set (Setoid S)} (hC : C ⊆ F.B) (s : S)
    (v : Set S) : monoExp C s v ≠ 0 ↔ ∃ b ∈ C, part b s = v := by
  rw [F.monoExp_apply ((Set.toFinite F.B).subset hC) hC]
  split_ifs with h <;> simp [h]

/-- Two `C`-monomials agree exactly when their arguments agree on every factor in `C`
(for `C ⊆ B`).  This is Corollary 1 in the form Propositions 26, 27 and 31 use it: only the
*dimension* has to be finite. -/
lemma mono_eq_iff [Finite F.B] {C : Set (Setoid S)} (hC : C ⊆ F.B) {s t : S} :
    mono C s = mono C t ↔ ∀ b ∈ C, part b s = part b t := by
  have hCfin : C.Finite := (Set.toFinite F.B).subset hC
  refine ⟨fun h b hb => ?_, mono_congr⟩
  rw [mono_eq_monomial hCfin, mono_eq_monomial hCfin] at h
  have hexp : monoExp C s = monoExp C t := monomial_left_injective one_ne_zero h
  have hv : monoExp C s (part b s) = monoExp C t (part b s) := by rw [hexp]
  rw [F.monoExp_apply hCfin hC s, F.monoExp_apply hCfin hC t, if_pos ⟨b, hb, rfl⟩] at hv
  by_cases hex : ∃ b' ∈ C, part b' t = part b s
  · obtain ⟨b', hb'C, hb'⟩ := hex
    have hbb : b' = b := F.eq_of_part_eq (hC hb'C) (hC hb) hb'
    rw [hbb] at hb'
    exact hb'.symm
  · rw [if_neg hex] at hv
    exact absurd hv one_ne_zero

/-- Every variable has degree at most one in `mono^F_C(s)` for `C ⊆ B` — Corollary 1 says
the factors of `C` contribute pairwise distinct variables, so the monomial is squarefree.
No finiteness: for an infinite `C` the `finprod` takes its junk value `1`. -/
private lemma degreeOf_mono_le {C : Set (Setoid S)} (hC : C ⊆ F.B) (s : S) (v : Set S) :
    (mono C s).degreeOf v ≤ 1 := by
  by_cases hCfin : C.Finite
  · rw [mono_eq_monomial hCfin, degreeOf_monomial_eq _ _ (one_ne_zero (α := ℝ)),
      F.monoExp_apply hCfin hC]
    split_ifs <;> simp
  · rw [mono_eq_one_of_infinite hCfin, degreeOf_one]
    exact Nat.zero_le _

/-- Every variable has degree at most one in `poly^F_C(E)` for `C ⊆ B`: the monomials of a
factorization are squarefree, which is exactly where Corollary 1 does its work.  No
finiteness is needed anywhere — `poly^F_C(E)` is a `finsum` of squarefree monomials, and
both of its junk values (`1` for an infinite `C`, `0` for an infinite monomial set) satisfy
the bound. -/
lemma degreeOf_poly_le {C : Set (Setoid S)} (hC : C ⊆ F.B) (E : Set S)
    (v : Set S) : (poly C E).degreeOf v ≤ 1 := by
  rw [poly]
  refine degreeOf_finsum_mem_le fun m hm => ?_
  obtain ⟨s, -, rfl⟩ := hm
  exact F.degreeOf_mono_le hC s v

/-- The variables of `poly^F_C(E)` are exactly the blocks `[s]_b` for `b ∈ C`, `s ∈ E`
(for `C ⊆ B`). -/
lemma mem_vars_poly [Finite S] {C : Set (Setoid S)} (hC : C ⊆ F.B) (E : Set S) {v : Set S} :
    v ∈ (poly C E).vars ↔ ∃ b ∈ C, ∃ s ∈ E, part b s = v := by
  rw [mem_vars_iff_mem_support]
  constructor
  · rintro ⟨d, hd, hv⟩
    obtain ⟨s, hs, rfl⟩ := (mem_support_poly_monoExp C E).1 hd
    rw [Finsupp.mem_support_iff, F.monoExp_ne_zero_iff hC] at hv
    obtain ⟨b, hb, hbv⟩ := hv
    exact ⟨b, hb, s, hs, hbv⟩
  · rintro ⟨b, hb, s, hs, rfl⟩
    refine ⟨monoExp C s, (mem_support_poly_monoExp C E).2 ⟨s, hs, rfl⟩, ?_⟩
    rw [Finsupp.mem_support_iff, F.monoExp_ne_zero_iff hC]
    exact ⟨b, hb, rfl⟩

/-- The paper's first paragraph in Proposition 26: distinct elements of `S` have distinct
`B`-monomials.  Proposition 3 supplies a factor separating them, Corollary 1 keeps that
factor's block out of the other monomial. -/
lemma mono_basis_injective [Finite F.B] : Function.Injective (mono F.B) := fun _ _ h =>
  F.eq_of_forall_rel fun b hb => part_eq_iff.1 ((F.mono_eq_iff le_rfl).1 h b hb)

/-- **Proposition 26** — `Q^F_E = poly^F_B(E)`: distinct elements have distinct
`B`-monomials (Proposition 3), so summing over `monos^F_B(E)` is summing over `E`.

Only the *dimension* has to be finite (`dd:finiteness-minimal`): the argument is
`finsum_mem_image` applied to `mono_basis_injective`, and injectivity of `mono^F_B` needs
`Finite F.B` alone.  The extra content this buys over the paper's `[Finite S]` form is
degenerate and is not oversold: for an infinite `E` both sides are the `finsum` junk value
`0` — `Q^F_E` sums a family of nonzero monomials over an infinite set, and so does
`poly^F_B(E)`, `mono^F_B` being injective — so the statement is `0 = 0` there.

Paper node: Proposition 26 (§5.1). -/
theorem Q_eq_poly [Finite F.B] (E : Set S) : F.Q E = poly F.B E := by
  rw [Q_eq_finsum_mono, poly, monos]
  exact (finsum_mem_image (f := fun m : Poly S => m)
    (fun s _ t _ h => F.mono_basis_injective h)).symm

/-- Every variable has degree at most one in `Q^F_E` — Proposition 26 followed by
`degreeOf_poly_le` at `C = B`.  Both of those now need at most `[Finite F.B]`, so this does
too; as with Proposition 26, the extra content over `[Finite S]` is degenerate, an infinite
`E` giving `Q^F_E = 0` and degree `0`. -/
lemma degreeOf_Q_le [Finite F.B] (E : Set S) (v : Set S) : (F.Q E).degreeOf v ≤ 1 := by
  rw [F.Q_eq_poly E]
  exact F.degreeOf_poly_le le_rfl E v

lemma Q_ne_zero [Finite S] {E : Set S} (hE : E.Nonempty) : F.Q E ≠ 0 := by
  rw [F.Q_eq_poly E]
  exact poly_ne_zero F.B hE

/-! ### The coefficients of `Q^F_E`

`Q^F_E` is a sum of pairwise distinct squarefree monic monomials, so each of its
coefficients is `0` or `1`.  Proposition 28 runs entirely on these two lemmas. -/

private lemma coeff_Q_monoExp [Finite S] {E : Set S} {s : S} (hs : s ∈ E) :
    (F.Q E).coeff (monoExp F.B s) = 1 := by
  rw [F.Q_eq_poly E, coeff_poly_monoExp, if_pos ⟨s, hs, rfl⟩]

private lemma exists_of_coeff_Q_ne_zero [Finite S] {E : Set S} {a : (Set S) →₀ ℕ}
    (h : (F.Q E).coeff a ≠ 0) : ∃ s ∈ E, monoExp F.B s = a := by
  rw [F.Q_eq_poly E, coeff_poly_monoExp] at h
  split_ifs at h with hmem
  · obtain ⟨s, hs, hsa⟩ := hmem
    exact ⟨s, hs, hsa⟩
  · exact absurd rfl h

private lemma part_chimera_of_mem {C : Set (Setoid S)} (s t : S) {b : Setoid S}
    (hb : b ∈ F.B) (hbC : b ∈ C) : part b (F.chimera C s t) = part b s :=
  part_eq_iff.2 (F.chimera_rel_of_mem s t hb hbC)

private lemma part_chimera_of_notMem {C : Set (Setoid S)} (s t : S) {b : Setoid S}
    (hb : b ∈ F.B) (hbC : b ∉ C) : part b (F.chimera C s t) = part b t :=
  part_eq_iff.2 (F.chimera_rel_of_notMem s t hb hbC)

/-- The monomial half of Proposition 27: on disjoint sets of factors the chimera splices two
elements so that its `C₀ ∪ C₁`-monomial is the product of their separate monomials. -/
private lemma mono_mul_chimera [Finite S] {C₀ C₁ : Set (Setoid S)} (h₀ : C₀ ⊆ F.B)
    (h₁ : C₁ ⊆ F.B) (hd : Disjoint C₀ C₁) (s₀ s₁ : S) :
    mono C₀ s₀ * mono C₁ s₁ = mono (C₀ ∪ C₁) (F.chimera C₀ s₀ s₁) := by
  rw [mono_union hd (Set.toFinite _) (Set.toFinite _)]
  congr 1
  · exact mono_congr fun b hb => (F.part_chimera_of_mem s₀ s₁ (h₀ hb) hb).symm
  · exact mono_congr fun b hb =>
      (F.part_chimera_of_notMem s₀ s₁ (h₁ hb) (Set.disjoint_right.1 hd hb)).symm

/-- **Proposition 27** (`factor1`) — for disjoint `C₀, C₁ ⊆ B` and
`E₂ = χ^F_{C₀}(E₀, E₁)`, `poly^F_{C₀ ∪ C₁}(E₂) = poly^F_{C₀}(E₀) · poly^F_{C₁}(E₁)`.

The paper separates the two factors of a product monomial by intersecting supports; the
proof below instead reads the separation off Corollary 1 through `mono_eq_iff` at
`C₀ ∪ C₁`.  Same ingredient, shorter route — a proof change, not a statement change.

Paper node: Proposition 27 (§5.1). -/
theorem poly_union_chimeraImage [Finite S] {C₀ C₁ : Set (Setoid S)} (h₀ : C₀ ⊆ F.B)
    (h₁ : C₁ ⊆ F.B) (hd : Disjoint C₀ C₁) (E₀ E₁ : Set S) :
    poly (C₀ ∪ C₁) (F.chimeraImage C₀ E₀ E₁) = poly C₀ E₀ * poly C₁ E₁ := by
  rw [poly_eq_sum_image, poly_eq_sum_image, poly_eq_sum_image, Finset.sum_mul_sum,
    ← Finset.sum_product']
  refine (Finset.sum_nbij (fun x : Poly S × Poly S => x.1 * x.2) ?_ ?_ ?_ fun _ _ => rfl).symm
  · rintro ⟨m₀, m₁⟩ hm
    simp only [Finset.mem_product, Finset.mem_image, Set.Finite.mem_toFinset] at hm
    obtain ⟨⟨s₀, hs₀, rfl⟩, s₁, hs₁, rfl⟩ := hm
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨F.chimera C₀ s₀ s₁, F.mem_chimeraImage.2 ⟨s₀, hs₀, s₁, hs₁, rfl⟩,
      (F.mono_mul_chimera h₀ h₁ hd s₀ s₁).symm⟩
  · rintro ⟨m₀, m₁⟩ hm ⟨m₀', m₁'⟩ hm' heq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_image,
      Set.Finite.mem_toFinset] at hm hm'
    obtain ⟨⟨s₀, hs₀, rfl⟩, s₁, hs₁, rfl⟩ := hm
    obtain ⟨⟨s₀', hs₀', rfl⟩, s₁', hs₁', rfl⟩ := hm'
    replace heq : mono C₀ s₀ * mono C₁ s₁ = mono C₀ s₀' * mono C₁ s₁' := heq
    rw [F.mono_mul_chimera h₀ h₁ hd, F.mono_mul_chimera h₀ h₁ hd] at heq
    have key := (F.mono_eq_iff (Set.union_subset h₀ h₁)).1 heq
    have e₀ : mono C₀ s₀ = mono C₀ s₀' := mono_congr fun b hb => by
      have h := key b (Or.inl hb)
      rwa [F.part_chimera_of_mem s₀ s₁ (h₀ hb) hb,
        F.part_chimera_of_mem s₀' s₁' (h₀ hb) hb] at h
    have e₁ : mono C₁ s₁ = mono C₁ s₁' := mono_congr fun b hb => by
      have h := key b (Or.inr hb)
      have hb' : b ∉ C₀ := Set.disjoint_right.1 hd hb
      rwa [F.part_chimera_of_notMem s₀ s₁ (h₁ hb) hb',
        F.part_chimera_of_notMem s₀' s₁' (h₁ hb) hb'] at h
    simp only [Prod.mk.injEq]
    exact ⟨e₀, e₁⟩
  · rintro m₂ hm₂
    simp only [Finset.mem_coe, Finset.mem_image, Set.Finite.mem_toFinset] at hm₂
    obtain ⟨u, hu, rfl⟩ := hm₂
    obtain ⟨t, ht, r, hr, rfl⟩ := F.mem_chimeraImage.1 hu
    refine ⟨(mono C₀ t, mono C₁ r), ?_, F.mono_mul_chimera h₀ h₁ hd t r⟩
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨⟨t, ht, rfl⟩, r, hr, rfl⟩

/-- The two factors of `Q^F_E` share no variable (the first step of the paper's proof of
Proposition 28). -/
lemma vars_disjoint_of_mul_eq_Q [Finite S] {E : Set S} (hE : E.Nonempty) {p q : Poly S}
    (h : p * q = F.Q E) : Disjoint p.vars q.vars := by
  have hQ : F.Q E ≠ 0 := F.Q_ne_zero hE
  have hp : p ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hQ h.symm
  have hq : q ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact hQ h.symm
  rw [Finset.disjoint_left]
  intro v hvp hvq
  have h2 : 2 ≤ (F.Q E).degreeOf v := by
    rw [← h, degreeOf_mul_eq hp hq]
    have h3 := mem_vars_iff_degreeOf_ne_zero.1 hvp
    have h4 := mem_vars_iff_degreeOf_ne_zero.1 hvq
    omega
  exact absurd (F.degreeOf_Q_le E v) (by omega)

/-- **Proposition 28** (`factor2`) — the load-bearing lemma: for nonempty `E`, every divisor
of `Q^F_E` is a real multiple of some `poly^F_C(E)` with `C ⊆ B`.

Paper node: Proposition 28 (§5.1). -/
theorem eq_C_mul_poly_of_dvd_Q [Finite S] {E : Set S} (hE : E.Nonempty) {p : Poly S}
    (hp : p ∣ F.Q E) : ∃ (r : ℝ) (C : Set (Setoid S)), C ⊆ F.B ∧ p = MvPolynomial.C r * poly C E := by
  obtain ⟨q, hq⟩ := hp
  have hBfin : (F.B : Set (Setoid S)).Finite := Set.toFinite _
  have hQ0 : F.Q E ≠ 0 := F.Q_ne_zero hE
  have hp0 : p ≠ 0 := fun h => hQ0 (by rw [hq, h, zero_mul])
  have hq0 : q ≠ 0 := fun h => hQ0 (by rw [hq, h, mul_zero])
  have hdisj : Disjoint p.vars q.vars := F.vars_disjoint_of_mul_eq_Q hE hq.symm
  have hpv : ∀ a ∈ p.support, ∀ i ∈ a.support, i ∈ p.vars := fun _ ha _ hi =>
    support_subset_vars_of_mem_support ha hi
  have hqv : ∀ b ∈ q.support, ∀ i ∈ b.support, i ∈ q.vars := fun _ hb _ hi =>
    support_subset_vars_of_mem_support hb hi
  -- (A) every `p`-term times every `q`-term is a term of `Q^F_E`, of coefficient one.
  have hA : ∀ a ∈ p.support, ∀ b ∈ q.support, ∃ s ∈ E, monoExp F.B s = a + b := by
    intro a ha b hb
    refine F.exists_of_coeff_Q_ne_zero ?_
    rw [hq, coeff_add_mul_of_split hdisj (hpv a ha) (hqv b hb)]
    exact mul_ne_zero (mem_support_iff.1 ha) (mem_support_iff.1 hb)
  have hA1 : ∀ a ∈ p.support, ∀ b ∈ q.support, coeff a p * coeff b q = 1 := by
    intro a ha b hb
    obtain ⟨s, hs, hsa⟩ := hA a ha b hb
    have h1 : (F.Q E).coeff (a + b) = 1 := by rw [← hsa]; exact F.coeff_Q_monoExp hs
    rwa [hq, coeff_add_mul_of_split hdisj (hpv a ha) (hqv b hb)] at h1
  -- Splitting an exponent vector along `supp p`.
  have hfil : ∀ a ∈ p.support, ∀ b ∈ q.support,
      (a + b).filter (· ∈ p.vars) = a ∧ (a + b).filter (fun v => v ∉ p.vars) = b := by
    intro a ha b hb
    have hda : ∀ i, a i ≠ 0 → i ∈ p.vars := fun i hi => hpv a ha i (Finsupp.mem_support_iff.2 hi)
    have hdb : ∀ i, b i ≠ 0 → i ∉ p.vars := fun i hi =>
      Finset.disjoint_right.1 hdisj (hqv b hb i (Finsupp.mem_support_iff.2 hi))
    refine ⟨?_, ?_⟩
    · rw [Finsupp.filter_add, filter_self_of_mem hda, filter_zero_of_notMem hdb, add_zero]
    · rw [Finsupp.filter_add, filter_zero_of_notMem (fun i hi h => h (hda i hi)),
        filter_self_of_mem hdb, zero_add]
  -- (C) each term of `Q^F_E` splits across the two factors.
  have hCsplit : ∀ s ∈ E, (monoExp F.B s).filter (· ∈ p.vars) ∈ p.support ∧
      (monoExp F.B s).filter (fun v => v ∉ p.vars) ∈ q.support := by
    intro s hs
    have hmem : monoExp F.B s ∈ (F.Q E).support :=
      mem_support_iff.2 (by rw [F.coeff_Q_monoExp hs]; exact one_ne_zero)
    rw [hq] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.1 (support_mul p q hmem)
    obtain ⟨h1, h2⟩ := hfil a ha b hb
    rw [hab] at h1 h2
    exact ⟨by rw [h1]; exact ha, by rw [h2]; exact hb⟩
  -- Corollary 1: a variable of `mono^F_B(u)` of the form `[x]_c` is `[u]_c`.
  have hkey : ∀ (c : Setoid S) (x u : S), c ∈ F.B → monoExp F.B u (part c x) ≠ 0 →
      part c x = part c u := by
    intro c x u hc hne
    obtain ⟨b', hb', hb'eq⟩ := (F.monoExp_ne_zero_iff le_rfl u (part c x)).1 hne
    have hb'c : b' = c := F.eq_of_part_eq hb' hc hb'eq
    rw [hb'c] at hb'eq
    exact hb'eq.symm
  -- (D) which factors contribute variables to `p` does not depend on the point.
  have hD : ∀ b ∈ F.B, ∀ s ∈ E, ∀ t ∈ E, part b s ∈ p.vars → part b t ∈ p.vars := by
    intro b hbB s hs t ht hbs
    by_contra hbt
    obtain ⟨u, hu, hueq⟩ := hA _ (hCsplit s hs).1 _ (hCsplit t ht).2
    have hes : monoExp F.B s (part b s) = 1 := by
      rw [F.monoExp_apply hBfin le_rfl, if_pos ⟨b, hbB, rfl⟩]
    have het : monoExp F.B t (part b t) = 1 := by
      rw [F.monoExp_apply hBfin le_rfl, if_pos ⟨b, hbB, rfl⟩]
    have hvs : ((monoExp F.B s).filter (· ∈ p.vars)) (part b s) = 1 := by
      rw [Finsupp.filter_apply]; simp [hbs, hes]
    have hvt : ((monoExp F.B t).filter (fun v => v ∉ p.vars)) (part b t) = 1 := by
      rw [Finsupp.filter_apply]; simp [hbt, het]
    have hus : part b s = part b u := by
      refine hkey b s u hbB ?_
      rw [hueq, Finsupp.add_apply, hvs]; omega
    have hut : part b t = part b u := by
      refine hkey b t u hbB ?_
      rw [hueq, Finsupp.add_apply, hvt]; omega
    exact hbt (by rw [hut, ← hus]; exact hbs)
  -- (E) the set of factors: those whose block at some (hence every) point of `E` is a
  -- variable of `p`.
  obtain ⟨s₀, hs₀⟩ := hE
  obtain ⟨C, hCdef⟩ : ∃ C : Set (Setoid S), C = {b | b ∈ F.B ∧ part b s₀ ∈ p.vars} := ⟨_, rfl⟩
  have hCmemiff : ∀ b, b ∈ C ↔ (b ∈ F.B ∧ part b s₀ ∈ p.vars) := by
    intro b; rw [hCdef]; exact Iff.rfl
  have hCsub : C ⊆ F.B := fun b hb => ((hCmemiff b).1 hb).1
  have hmemC : ∀ b ∈ F.B, ∀ s ∈ E, (part b s ∈ p.vars ↔ b ∈ C) := by
    intro b hbB s hs
    rw [hCmemiff b]
    exact ⟨fun h => ⟨hbB, hD b hbB s hs s₀ hs₀ h⟩, fun h => hD b hbB s₀ hs₀ s hs h.2⟩
  have hev : ∀ s ∈ E, (monoExp F.B s).filter (· ∈ p.vars) = monoExp C s := by
    intro s hs
    refine Finsupp.ext fun v => ?_
    rw [Finsupp.filter_apply, F.monoExp_apply hBfin le_rfl,
      F.monoExp_apply (hBfin.subset hCsub) hCsub]
    by_cases hv : v ∈ p.vars
    · rw [if_pos hv]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨b, hbB, hbv⟩
        exact ⟨b, (hmemC b hbB s hs).1 (hbv ▸ hv), hbv⟩
      · rintro ⟨b, hbC, hbv⟩
        exact ⟨b, hCsub hbC, hbv⟩
    · have hnot : ¬ ∃ b ∈ C, part b s = v := by
        rintro ⟨b, hbC, rfl⟩
        exact hv ((hmemC b (hCsub hbC) s hs).2 hbC)
      rw [if_neg hv, if_neg hnot]
  -- (B) all coefficients of `p` are the same real.
  obtain ⟨a₀, ha₀⟩ := support_nonempty.2 hp0
  obtain ⟨b₀, hb₀⟩ := support_nonempty.2 hq0
  have hconst : ∀ a ∈ p.support, coeff a p = coeff a₀ p := by
    intro a ha
    refine mul_right_cancel₀ (mem_support_iff.1 hb₀) ?_
    rw [hA1 a ha b₀ hb₀, hA1 a₀ ha₀ b₀ hb₀]
  -- (F) the support of `p` is exactly the `C`-monomial support of `E`.
  have hsupp : p.support = (Set.toFinite E).toFinset.image (fun s => monoExp C s) := by
    ext a
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    constructor
    · intro ha
      obtain ⟨s, hs, hsa⟩ := hA a ha b₀ hb₀
      refine ⟨s, hs, ?_⟩
      have h1 := (hfil a ha b₀ hb₀).1
      rw [← hsa] at h1
      rw [← hev s hs]; exact h1
    · rintro ⟨s, hs, rfl⟩
      rw [← hev s hs]
      exact (hCsplit s hs).1
  -- (G) assemble.
  have himg : (Set.toFinite E).toFinset.image (mono C)
      = ((Set.toFinite E).toFinset.image (fun s => monoExp C s)).image
          (fun d => (monomial d (1 : ℝ) : Poly S)) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun s _ => mono_eq_monomial (Set.toFinite C) s
  have hpolyC : poly C E
      = ∑ d ∈ (Set.toFinite E).toFinset.image (fun s => monoExp C s),
          (monomial d (1 : ℝ) : Poly S) := by
    rw [poly_eq_sum_image, himg]
    exact Finset.sum_image fun d _ d' _ h => monomial_left_injective one_ne_zero h
  refine ⟨coeff a₀ p, C, hCsub, ?_⟩
  rw [hpolyC, Finset.mul_sum]
  calc p = ∑ d ∈ p.support, monomial d (coeff d p) := (support_sum_monomial_coeff p).symm
    _ = ∑ d ∈ p.support, monomial d (coeff a₀ p) :=
        Finset.sum_congr rfl fun d hd => by rw [hconst d hd]
    _ = ∑ d ∈ (Set.toFinite E).toFinset.image (fun s => monoExp C s),
          (monomial d (coeff a₀ p) : Poly S) := by rw [hsupp]
    _ = _ := Finset.sum_congr rfl fun d _ => by rw [C_mul_monomial, mul_one]

/-! ### Client-style uses of the §5.1 surface -/

/-- Definitions 32–34 read off each other: at a singleton, `poly^F_C({s})` is the single
monomial `mono^F_C(s)`. -/
example (C : Set (Setoid S)) (s : S) : poly C {s} = mono C s := by
  rw [poly, monos, Set.image_singleton, finsum_mem_singleton]

/-- Definition 33 as membership: every point of `E` contributes its `B`-monomial to the set
`monos^F_B(E)` that Proposition 26 sums over. -/
example (F : FactoredSet S) (E : Set S) {s : S} (hs : s ∈ E) : mono F.B s ∈ monos F.B E :=
  ⟨s, hs, rfl⟩

/-- Definition 28 used as a ring: `Poly^F` is a commutative ring, so §5's divisibility is
Mathlib's `∣` in it and needs no bespoke notion of division. -/
example (F : FactoredSet S) (E : Set S) (p q : Poly S) (h : p * q = F.Q E) : p ∣ F.Q E :=
  ⟨q, h.symm⟩

/-- Proposition 26 as a transport: Proposition 28 stated over `poly^F_B(E)` rather than over
`Q^F_E`.  This is the form §5.2 uses when it factors `poly^F_B(E)` into irreducibles. -/
example (F : FactoredSet S) [Finite S] {E : Set S} (hE : E.Nonempty) {p : Poly S}
    (hp : p ∣ poly F.B E) :
    ∃ (r : ℝ) (C : Set (Setoid S)), C ⊆ F.B ∧ p = MvPolynomial.C r * poly C E :=
  F.eq_C_mul_poly_of_dvd_Q hE (by rwa [F.Q_eq_poly E])

/-- Proposition 27 in the shape Proposition 30's induction needs it: when `C₀` fixes `E`
(`χ^F_{C₀}(E,E) = E`), splitting off a disjoint `C₀` factors `poly^F_{C₀ ∪ C₁}(E)`. -/
example (F : FactoredSet S) [Finite S] {C₀ C₁ : Set (Setoid S)} (h₀ : C₀ ⊆ F.B)
    (h₁ : C₁ ⊆ F.B) (hd : Disjoint C₀ C₁) {E : Set S} (hE : F.chimeraImage C₀ E E = E) :
    poly (C₀ ∪ C₁) E = poly C₀ E * poly C₁ E := by
  have h := F.poly_union_chimeraImage h₀ h₁ hd E E
  rwa [hE] at h

/-- Definition 31 through Proposition 26: a nonempty `E` has a nonzero characteristic
polynomial, so `poly^F_B(E)` is a legitimate object to factor. -/
example (F : FactoredSet S) [Finite S] {E : Set S} (hE : E.Nonempty) : poly F.B E ≠ 0 := by
  rw [← F.Q_eq_poly E]
  exact F.Q_ne_zero hE

end FactoredSet

end FiniteFactoredSets
