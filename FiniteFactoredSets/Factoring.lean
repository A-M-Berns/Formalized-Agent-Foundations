import FiniteFactoredSets.Polynomial
import FiniteFactoredSets.Subpartition

/-!
# Factoring characteristic polynomials

This file is §5.2 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): the irreducible-factor structure `Irr^F(E)` on `B` (Definition 35),
the fact that it partitions `B` (Proposition 29), and the factorization of `Q^F_E` into
irreducibles (Propositions 30 and 31).  `dd:poly` fixes the polynomial ring; Mathlib's
`Irreducible` renders the paper's irreducibility (over `ℝ` the units are the nonzero
constants).  `[Finite S]` is carried where the paper's "finite factored set" is used.

The first section below is not §5.2 material: it is the monomial-level description of
`poly^F_C(E)` — under `[Finite S]` it is the sum of the distinct squarefree monomials
`mono^F_C(s)`, `s ∈ E`, each with coefficient `1` — which Propositions 30 and 31 consume
and which `Polynomial.lean` does not state.  It belongs with §5.1 and is a candidate for
moving upstream.
-/

universe u

open MvPolynomial

namespace FiniteFactoredSets

variable {S : Type u}

open scoped Classical

/-! ## The monomial structure of `poly^F_C(E)`

Corollary 1 makes `b ↦ [s]_b` injective on `B`, so `mono^F_C(s)` is a *squarefree*
monomial with coefficient `1`, and `poly^F_C(E)` is the sum of the distinct such monomials
over `s ∈ E`.  Everything §5.2 needs about supports, variables and degrees follows from
that one description. -/

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

private lemma monoExp_eq_sum [Finite S] (C : Set (Setoid S)) (s : S) :
    monoExp C s = ∑ b ∈ (Set.toFinite C).toFinset, Finsupp.single (part b s) 1 := by
  rw [monoExp, ← finsum_mem_coe_finset, Set.Finite.coe_toFinset]

private lemma mono_eq_monomial [Finite S] (C : Set (Setoid S)) (s : S) :
    mono C s = monomial (monoExp C s) 1 := by
  have h1 : mono C s = ∏ b ∈ (Set.toFinite C).toFinset, X (part b s) := by
    rw [mono, ← finprod_mem_coe_finset, Set.Finite.coe_toFinset]
  rw [h1, monoExp_eq_sum, prod_X_eq_monomial]

private lemma monoExp_empty (s : S) : monoExp (∅ : Set (Setoid S)) s = 0 := by
  rw [monoExp, finsum_mem_empty]

private lemma poly_eq_finsum_monomial [Finite S] (C : Set (Setoid S)) (E : Set S) :
    poly C E = ∑ᶠ d ∈ monoExp C '' E, monomial d 1 := by
  have hm : mono C = fun s => (monomial (monoExp C s) 1 : Poly S) :=
    funext (mono_eq_monomial C)
  rw [poly, monos, hm, ← Set.image_image (fun d => (monomial d 1 : Poly S)) (monoExp C),
    finsum_mem_image (Function.Injective.injOn (monomial_left_injective one_ne_zero))]

private lemma coeff_poly [Finite S] (C : Set (Setoid S)) (E : Set S) (d : (Set S) →₀ ℕ) :
    coeff d (poly C E) = if d ∈ monoExp C '' E then 1 else 0 := by
  have hfin : (monoExp C '' E).Finite := (Set.toFinite E).image _
  rw [poly_eq_finsum_monomial, ← hfin.coe_toFinset, finsum_mem_coe_finset, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' hfin.toFinset d (fun _ => (1 : ℝ))]
  simp

private lemma mem_support_poly [Finite S] (C : Set (Setoid S)) (E : Set S)
    {d : (Set S) →₀ ℕ} : d ∈ (poly C E).support ↔ d ∈ monoExp C '' E := by
  rw [mem_support_iff, coeff_poly]
  split_ifs with h <;> simp [h]

/-- `poly^F_C(E)` is nonzero for nonempty `E` — its monomials all have coefficient `1`, so
none of them cancels. -/
lemma poly_ne_zero [Finite S] (C : Set (Setoid S)) {E : Set S} (hE : E.Nonempty) :
    poly C E ≠ 0 := by
  obtain ⟨s, hs⟩ := hE
  intro h
  have hco := coeff_poly C E (monoExp C s)
  rw [h, if_pos ⟨s, hs, rfl⟩] at hco
  simp at hco


/-- A unit of `Poly^F` has empty support: `ℝ` has no zero divisors, so degrees add. -/
private lemma vars_eq_empty_of_isUnit {p : Poly S} (h : IsUnit p) : p.vars = ∅ := by
  obtain ⟨u, rfl⟩ := h
  have h1 : (u : Poly S) * (↑u⁻¹ : Poly S) = 1 := u.mul_inv
  have hu : (u : Poly S) ≠ 0 := u.ne_zero
  have hv : (↑u⁻¹ : Poly S) ≠ 0 := u⁻¹.ne_zero
  ext v
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_vars_iff_degreeOf_ne_zero]
  intro hne
  have hd := degreeOf_mul_eq (n := v) hu hv
  rw [h1] at hd
  simp only [degreeOf_one] at hd
  omega

namespace FactoredSet

variable (F : FactoredSet S)

/-- The exponent of a variable in `mono^F_C(s)` is `1` if the variable is one of the blocks
`[s]_b`, `b ∈ C`, and `0` otherwise.  Corollary 1 (`eq_of_part_eq`) is what rules out two
factors of `C` contributing the same variable, which is why `C ⊆ B` is needed. -/
private lemma monoExp_apply [Finite S] {C : Set (Setoid S)} (hC : C ⊆ F.B) (s : S) (v : Set S) :
    monoExp C s v = if ∃ b ∈ C, part b s = v then 1 else 0 := by
  rw [monoExp_eq_sum, Finsupp.finsetSum_apply]
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

/-- Two elements have the same `C`-monomial exactly when they agree on every factor of `C`
(for `C ⊆ B`).  This is the step Proposition 31 uses to pull an element of `E` back out of
an equality of monomial sets. -/
lemma mono_eq_iff [Finite S] {C : Set (Setoid S)} (hC : C ⊆ F.B) {s t : S} :
    mono C s = mono C t ↔ ∀ b ∈ C, part b s = part b t := by
  rw [mono_eq_monomial, mono_eq_monomial]
  constructor
  · intro h b hb
    have hexp : monoExp C s = monoExp C t := monomial_left_injective one_ne_zero h
    have hv : monoExp C s (part b s) = monoExp C t (part b s) := by rw [hexp]
    rw [F.monoExp_apply hC s, F.monoExp_apply hC t, if_pos ⟨b, hb, rfl⟩] at hv
    by_cases hex : ∃ b' ∈ C, part b' t = part b s
    · obtain ⟨b', hb'C, hb'⟩ := hex
      have hbb : b' = b := F.eq_of_part_eq (hC hb'C) (hC hb) hb'
      rw [hbb] at hb'
      exact hb'.symm
    · rw [if_neg hex] at hv
      exact absurd hv one_ne_zero
  · intro h
    have hexp : monoExp C s = monoExp C t := by
      ext v
      rw [F.monoExp_apply hC s, F.monoExp_apply hC t]
      congr 1
      exact propext ⟨fun ⟨b, hb, he⟩ => ⟨b, hb, (h b hb) ▸ he⟩,
        fun ⟨b, hb, he⟩ => ⟨b, hb, (h b hb).symm ▸ he⟩⟩
    rw [hexp]

/-- Every variable has degree at most one in `poly^F_C(E)` for `C ⊆ B` — the `poly` analogue
of `degreeOf_Q_le`, and the fact that forces the two factors in Proposition 31 to use
disjoint sets of factors. -/
lemma degreeOf_poly_le [Finite S] {C : Set (Setoid S)} (hC : C ⊆ F.B) (E : Set S) (v : Set S) :
    (poly C E).degreeOf v ≤ 1 := by
  rw [degreeOf_le_iff]
  intro d hd
  obtain ⟨s, -, rfl⟩ := (mem_support_poly C E).1 hd
  rw [F.monoExp_apply hC s]
  split_ifs <;> simp

/-- The support of `poly^F_C(E)` is exactly `{[s]_b | b ∈ C, s ∈ E}` (for `C ⊆ B`). -/
lemma mem_vars_poly [Finite S] {C : Set (Setoid S)} (hC : C ⊆ F.B) (E : Set S) {v : Set S} :
    v ∈ (poly C E).vars ↔ ∃ b ∈ C, ∃ s ∈ E, part b s = v := by
  rw [mem_vars_iff_mem_support]
  constructor
  · rintro ⟨d, hd, hv⟩
    obtain ⟨s, hs, rfl⟩ := (mem_support_poly C E).1 hd
    rw [Finsupp.mem_support_iff, F.monoExp_apply hC s] at hv
    by_cases hex : ∃ b ∈ C, part b s = v
    · obtain ⟨b, hb, hbv⟩ := hex
      exact ⟨b, hb, s, hs, hbv⟩
    · rw [if_neg hex] at hv
      exact absurd rfl hv
  · rintro ⟨b, hb, s, hs, rfl⟩
    refine ⟨monoExp C s, (mem_support_poly C E).2 ⟨s, hs, rfl⟩, ?_⟩
    rw [Finsupp.mem_support_iff, F.monoExp_apply hC s, if_pos ⟨b, hb, rfl⟩]
    exact one_ne_zero

/-- Reading a factor set off the support of its polynomial: for `b ∈ B` and any `s ∈ E`,
`b ∈ C` iff `[s]_b` is a variable of `poly^F_C(E)`.  This is the paper's "`b ∈ C` if and
only if `[s]_b ∈ supp(poly^F_C(E))`" step in Proposition 31. -/
private lemma mem_iff_part_mem_vars [Finite S] {C : Set (Setoid S)} (hC : C ⊆ F.B)
    {E : Set S} {s : S} (hs : s ∈ E) {b : Setoid S} (hb : b ∈ F.B) :
    b ∈ C ↔ part b s ∈ (poly C E).vars := by
  constructor
  · intro hbC
    exact (F.mem_vars_poly hC E).2 ⟨b, hbC, s, hs, rfl⟩
  · intro hv
    obtain ⟨b', hb', s', hs', heq⟩ := (F.mem_vars_poly hC E).1 hv
    exact F.eq_of_part_eq (hC hb') hb heq ▸ hb'

/-! ## §5.2 Factoring characteristic polynomials

The paper's proof of Proposition 29 runs on three facts about the sets `C` with
`χ^F_C(E,E) = E`: they contain `B`, they are closed under intersection, and they are closed
under complementation in `B`.  These are the three lemmas below; none of them needs `E`
nonempty. -/

private lemma subset_chimeraImage_self (C : Set (Setoid S)) (E : Set S) :
    E ⊆ F.chimeraImage C E E :=
  fun u hu => F.mem_chimeraImage.2 ⟨u, hu, u, hu, F.chimera_self C u⟩

private lemma chimeraImage_inter_eq {C D : Set (Setoid S)} {E : Set S}
    (hC : F.chimeraImage C E E = E) (hD : F.chimeraImage D E E = E) :
    F.chimeraImage (C ∩ D) E E = E := by
  refine Set.Subset.antisymm ?_ (F.subset_chimeraImage_self _ _)
  rintro u ⟨s, hs, t, ht, rfl⟩
  rw [F.chimera_inter]
  have h1 : F.chimera D s t ∈ E := by
    rw [← hD]; exact F.mem_chimeraImage.2 ⟨s, hs, t, ht, rfl⟩
  rw [← hC]
  exact F.mem_chimeraImage.2 ⟨_, h1, t, ht, rfl⟩

private lemma chimeraImage_basis_eq (E : Set S) : F.chimeraImage F.B E E = E := by
  refine Set.Subset.antisymm ?_ (F.subset_chimeraImage_self _ _)
  rintro u ⟨s, hs, t, -, rfl⟩
  rw [F.chimera_basis]
  exact hs

private lemma chimeraImage_sdiff_eq {D : Set (Setoid S)} {E : Set S}
    (hD : F.chimeraImage D E E = E) : F.chimeraImage (F.B \ D) E E = E := by
  refine Set.Subset.antisymm ?_ (F.subset_chimeraImage_self _ _)
  rintro u ⟨s, hs, t, ht, rfl⟩
  rw [F.chimera_sdiff, ← hD]
  exact F.mem_chimeraImage.2 ⟨t, ht, s, hs, rfl⟩

/-- Definition 35: `Irr^F(E)` — the nonempty subsets `C ⊆ B` with `χ^F_C(E,E) = E` that
are minimal for that property among nonempty subsets.  (The paper takes `E` nonempty; the
definition itself needs no such hypothesis, and the propositions carry it.)

Paper node: Definition 35 (§5.2). -/
def irr (E : Set S) : Set (Set (Setoid S)) :=
  {C | C.Nonempty ∧ C ⊆ F.B ∧ F.chimeraImage C E E = E ∧
    ∀ D ⊂ C, D.Nonempty → F.chimeraImage D E E ≠ E}

lemma mem_irr {E : Set S} {C : Set (Setoid S)} :
    C ∈ F.irr E ↔ C.Nonempty ∧ C ⊆ F.B ∧ F.chimeraImage C E E = E ∧
      ∀ D ⊂ C, D.Nonempty → F.chimeraImage D E E ≠ E := Iff.rfl

set_option linter.unusedVariables false in
/-- **Proposition 29** — `Irr^F(E)` is a partition of `B` (for nonempty `E`): its members
are nonempty, pairwise disjoint, and cover `B`.  Under `dd:partition` a partition of the
*set* `B` is exactly this triple; `irr_isPartition` restates it as a `Subpartition` of
`Setoid S` with domain `B` whose blocks are the members of `Irr^F(E)`.

The paper's `E.Nonempty` is kept for faithfulness but is not consumed: `χ^F_C(∅,∅) = ∅` for
every `C`, so `Irr^F(∅) = {{b} | b ∈ B}`, which is still a partition of `B`.  The linter is
silenced on that one binder rather than renaming it, so the statement reads as the paper
states it.

Paper node: Proposition 29 (§5.2). -/
theorem irr_partition [Finite S] {E : Set S} (hE : E.Nonempty) :
    (∀ C ∈ F.irr E, C.Nonempty) ∧ (F.irr E).PairwiseDisjoint id ∧ ⋃₀ F.irr E = F.B := by
  haveI : Finite F.B := F.finite_basis_of_finite
  have hBfin : F.B.Finite := Set.toFinite _
  refine ⟨fun C hC => hC.1, ?_, ?_⟩
  · intro C₀ h₀ C₁ h₁ hCne
    show Disjoint C₀ C₁
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hemp
    have hinter : F.chimeraImage (C₀ ∩ C₁) E E = E :=
      F.chimeraImage_inter_eq h₀.2.2.1 h₁.2.2.1
    have hIne : (C₀ ∩ C₁).Nonempty := Set.nonempty_iff_ne_empty.2 hemp
    have hsplit : C₀ ∩ C₁ ≠ C₀ ∨ C₀ ∩ C₁ ≠ C₁ := by
      by_cases h : C₀ ∩ C₁ = C₀
      · exact Or.inr fun h' => hCne (h.symm.trans h')
      · exact Or.inl h
    rcases hsplit with h | h
    · exact h₀.2.2.2 (C₀ ∩ C₁) (Set.ssubset_iff_subset_ne.2 ⟨Set.inter_subset_left, h⟩)
        hIne hinter
    · exact h₁.2.2.2 (C₀ ∩ C₁) (Set.ssubset_iff_subset_ne.2 ⟨Set.inter_subset_right, h⟩)
        hIne hinter
  · refine Set.Subset.antisymm ?_ ?_
    · rintro b ⟨C, hC, hbC⟩
      exact hC.2.1 hbC
    · intro b hb
      obtain ⟨Cb, hCb⟩ :=
        Set.Finite.exists_minimal
          (s := {C : Set (Setoid S) | C ⊆ F.B ∧ b ∈ C ∧ F.chimeraImage C E E = E})
          (hBfin.finite_subsets.subset fun C hC => hC.1)
          ⟨F.B, subset_rfl, hb, F.chimeraImage_basis_eq E⟩
      have hmem : Cb ⊆ F.B ∧ b ∈ Cb ∧ F.chimeraImage Cb E E = E := hCb.1
      refine ⟨Cb, ⟨⟨b, hmem.2.1⟩, hmem.1, hmem.2.2, ?_⟩, hmem.2.1⟩
      intro D hD hDne hDE
      obtain ⟨hDsub, hDneq⟩ := Set.ssubset_iff_subset_ne.1 hD
      by_cases hbD : b ∈ D
      · exact hDneq (hCb.eq_of_subset ⟨hDsub.trans hmem.1, hbD, hDE⟩ hDsub)
      · have h1 : F.chimeraImage (F.B \ D) E E = E := F.chimeraImage_sdiff_eq hDE
        have h2 : F.chimeraImage (Cb ∩ (F.B \ D)) E E = E :=
          F.chimeraImage_inter_eq hmem.2.2 h1
        have heq : Cb ∩ (F.B \ D) = Cb \ D := by
          ext c
          simp only [Set.mem_inter_iff, Set.mem_sdiff]
          exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmem.1 h.1, h.2⟩⟩
        rw [heq] at h2
        have h4 : Cb \ D = Cb :=
          hCb.eq_of_subset ⟨Set.sdiff_subset.trans hmem.1, ⟨hmem.2.1, hbD⟩, h2⟩
            Set.sdiff_subset
        obtain ⟨d, hd⟩ := hDne
        have hdmem : d ∈ Cb \ D := by rw [h4]; exact hDsub hd
        exact hdmem.2 hd

/-- Proposition 29 in the vocabulary of §4: `Irr^F(E)` is the block set of a subpartition of
`Setoid S` with domain `B`. -/
lemma irr_isPartition [Finite S] {E : Set S} (hE : E.Nonempty) :
    ∃ P : Subpartition (Setoid S), P.dom = F.B ∧ P.classes = F.irr E := by
  obtain ⟨hne, hdisj, hcover⟩ := F.irr_partition hE
  have huniq : ∀ C ∈ F.irr E, ∀ C' ∈ F.irr E, ∀ b, b ∈ C → b ∈ C' → C = C' := by
    intro C hC C' hC' b hb hb'
    by_contra hcon
    exact Set.disjoint_left.1 (hdisj hC hC' hcon) hb hb'
  obtain ⟨P, hPr⟩ : ∃ P : Subpartition (Setoid S),
      ∀ b₀ b₁, P b₀ b₁ ↔ ∃ C ∈ F.irr E, b₀ ∈ C ∧ b₁ ∈ C := by
    refine ⟨⟨fun b₀ b₁ => ∃ C ∈ F.irr E, b₀ ∈ C ∧ b₁ ∈ C, ?_, ?_⟩, fun _ _ => Iff.rfl⟩
    · rintro s t ⟨C, hC, hs, ht⟩
      exact ⟨C, hC, ht, hs⟩
    · rintro s t u ⟨C, hC, hs, ht⟩ ⟨C', hC', ht', hu⟩
      obtain rfl := huniq C hC C' hC' t ht ht'
      exact ⟨C, hC, hs, hu⟩
  have hpart : ∀ C ∈ F.irr E, ∀ b ∈ C, P.part b = C := by
    intro C hC b hb
    ext b'
    simp only [Subpartition.mem_part, hPr]
    constructor
    · rintro ⟨C', hC', hb'C', hbC'⟩
      obtain rfl := huniq C' hC' C hC b hbC' hb
      exact hb'C'
    · intro hb'
      exact ⟨C, hC, hb', hb⟩
  refine ⟨P, ?_, ?_⟩
  · rw [← hcover]
    ext b
    simp only [Subpartition.dom, Set.mem_setOf_eq, hPr, Set.mem_sUnion]
    exact ⟨fun ⟨C, hC, hb, _⟩ => ⟨C, hC, hb⟩, fun ⟨C, hC, hb⟩ => ⟨C, hC, hb, hb⟩⟩
  · ext x
    simp only [Subpartition.classes, Set.mem_setOf_eq]
    constructor
    · rintro ⟨b, hbdom, rfl⟩
      obtain ⟨C, hC, hbC, -⟩ := (hPr b b).1 hbdom
      rw [hpart C hC b hbC]
      exact hC
    · intro hx
      obtain ⟨b, hb⟩ := hne x hx
      exact ⟨b, (hPr b b).2 ⟨x, hx, hb, hb⟩, (hpart x hx b hb).symm⟩

/-- The induction step of Proposition 30, over an arbitrary subfamily: Proposition 27
applied repeatedly, with `χ^F_{C}(E,E) = E` supplying the paper's `E₂ = E`. -/
private lemma finprod_poly_sUnion [Finite S] {E : Set S} (hE : E.Nonempty)
    (𝒦 : Set (Set (Setoid S))) :
    𝒦 ⊆ F.irr E → ∏ᶠ C ∈ 𝒦, poly C E = poly (⋃₀ 𝒦) E := by
  induction 𝒦, (Set.toFinite 𝒦) using Set.Finite.induction_on with
  | empty => intro _; rw [finprod_mem_empty, Set.sUnion_empty, poly_empty hE]
  | @insert C 𝒦' hCn h𝒦' ih =>
      intro hsub
      have hCirr : C ∈ F.irr E := hsub (Set.mem_insert _ _)
      have hsub' : 𝒦' ⊆ F.irr E := fun D hD => hsub (Set.mem_insert_of_mem _ hD)
      have hUB : ⋃₀ 𝒦' ⊆ F.B := by
        rintro b ⟨D, hD, hbD⟩
        exact (hsub' hD).2.1 hbD
      have hdisj : Disjoint C (⋃₀ 𝒦') := by
        rw [Set.disjoint_sUnion_right]
        intro D hD
        have hne : C ≠ D := by rintro rfl; exact hCn hD
        exact (F.irr_partition hE).2.1 hCirr (hsub' hD) hne
      rw [finprod_mem_insert _ hCn h𝒦', ih hsub', Set.sUnion_insert]
      have hst := F.poly_union_chimeraImage hCirr.2.1 hUB hdisj E E
      rw [hCirr.2.2.1] at hst
      exact hst.symm

/-- **Proposition 30** — `Q^F_E = ∏_{C ∈ Irr^F(E)} poly^F_C(E)` for nonempty `E`.

Paper node: Proposition 30 (§5.2). -/
theorem Q_eq_finprod_poly_irr [Finite S] {E : Set S} (hE : E.Nonempty) :
    F.Q E = ∏ᶠ C ∈ F.irr E, poly C E := by
  rw [F.finprod_poly_sUnion hE (F.irr E) subset_rfl, (F.irr_partition hE).2.2, ← F.Q_eq_poly E]

/-- Each irreducible factor divides the characteristic polynomial — Proposition 30 read as a
divisibility, which is how Proposition 31 gets to apply Proposition 28. -/
lemma poly_dvd_Q [Finite S] {E : Set S} (hE : E.Nonempty) {C : Set (Setoid S)}
    (hC : C ∈ F.irr E) : poly C E ∣ F.Q E := by
  have hfin : (F.irr E).Finite := Set.toFinite _
  rw [F.Q_eq_finprod_poly_irr hE, ← hfin.coe_toFinset, finprod_mem_coe_finset]
  exact Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hC)

/-- **Proposition 31** — each `poly^F_C(E)`, `C ∈ Irr^F(E)`, is irreducible (`E` nonempty).

Paper node: Proposition 31 (§5.2). -/
theorem irreducible_poly_of_mem_irr [Finite S] {E : Set S} (hE : E.Nonempty)
    {C : Set (Setoid S)} (hC : C ∈ F.irr E) : Irreducible (poly C E) := by
  obtain ⟨s, hs⟩ : ∃ s, s ∈ E := id hE
  obtain ⟨hCne, hCB, hCfix, hCmin⟩ := hC
  have hCirr : C ∈ F.irr E := ⟨hCne, hCB, hCfix, hCmin⟩
  constructor
  · -- `poly^F_C(E)` is not a unit: `C` and `E` are nonempty, so it has a variable.
    intro hu
    obtain ⟨b, hb⟩ := hCne
    have hmem : part b s ∈ (poly C E).vars :=
      (F.mem_vars_poly hCB E).2 ⟨b, hb, s, hs, rfl⟩
    rw [vars_eq_empty_of_isUnit hu] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · intro p₀ p₁ hprod
    have hpolyne : poly C E ≠ 0 := poly_ne_zero C hE
    have hp₀ne : p₀ ≠ 0 := by rintro rfl; rw [zero_mul] at hprod; exact hpolyne hprod
    have hp₁ne : p₁ ≠ 0 := by rintro rfl; rw [mul_zero] at hprod; exact hpolyne hprod
    -- Both factors divide `Q^F_E`, so Proposition 28 puts them in the form `r · poly_{Cᵢ}(E)`.
    have hdvdQ := F.poly_dvd_Q hE hCirr
    have hd₀ : p₀ ∣ F.Q E := dvd_trans ⟨p₁, hprod⟩ hdvdQ
    have hd₁ : p₁ ∣ F.Q E := dvd_trans ⟨p₀, by rw [hprod, mul_comm]⟩ hdvdQ
    obtain ⟨r₀, C₀, hC₀B, hp₀⟩ := F.eq_C_mul_poly_of_dvd_Q hE hd₀
    obtain ⟨r₁, C₁, hC₁B, hp₁⟩ := F.eq_C_mul_poly_of_dvd_Q hE hd₁
    have hr₀ : r₀ ≠ 0 := by rintro rfl; rw [map_zero, zero_mul] at hp₀; exact hp₀ne hp₀
    have hr₁ : r₁ ≠ 0 := by rintro rfl; rw [map_zero, zero_mul] at hp₁; exact hp₁ne hp₁
    -- A factor with an empty factor set is a nonzero constant, hence a unit.
    rcases Set.eq_empty_or_nonempty C₀ with hC₀e | hC₀ne
    · left
      rw [hp₀, hC₀e, poly_empty hE, mul_one]
      exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.2 hr₀)
    rcases Set.eq_empty_or_nonempty C₁ with hC₁e | hC₁ne
    · right
      rw [hp₁, hC₁e, poly_empty hE, mul_one]
      exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.2 hr₁)
    exfalso
    have hv₀ : p₀.vars = (poly C₀ E).vars := by rw [hp₀, vars_C_mul r₀ hr₀]
    have hv₁ : p₁.vars = (poly C₁ E).vars := by rw [hp₁, vars_C_mul r₁ hr₁]
    -- `C₀` and `C₁` are disjoint: a shared factor would give a variable of degree two.
    have hdisj : Disjoint C₀ C₁ := by
      rw [Set.disjoint_left]
      intro b hb0 hb1
      have h0 : part b s ∈ p₀.vars := by
        rw [hv₀]; exact (F.mem_iff_part_mem_vars hC₀B hs (hC₀B hb0)).1 hb0
      have h1 : part b s ∈ p₁.vars := by
        rw [hv₁]; exact (F.mem_iff_part_mem_vars hC₁B hs (hC₁B hb1)).1 hb1
      rw [mem_vars_iff_degreeOf_ne_zero] at h0 h1
      have hdeg : (poly C E).degreeOf (part b s)
          = p₀.degreeOf (part b s) + p₁.degreeOf (part b s) := by
        rw [hprod]; exact degreeOf_mul_eq hp₀ne hp₁ne
      have hle := F.degreeOf_poly_le hCB E (part b s)
      omega
    -- and their union is `C`, read off the supports.
    have hvarsC : (poly C E).vars = (poly C₀ E).vars ∪ (poly C₁ E).vars := by
      rw [hprod]
      refine Finset.Subset.antisymm ?_ ?_
      · rw [← hv₀, ← hv₁]; exact vars_mul p₀ p₁
      · intro v hv
        rw [Finset.mem_union] at hv
        rw [mem_vars_iff_degreeOf_ne_zero, degreeOf_mul_eq hp₀ne hp₁ne]
        rcases hv with h | h
        · rw [← hv₀, mem_vars_iff_degreeOf_ne_zero] at h; omega
        · rw [← hv₁, mem_vars_iff_degreeOf_ne_zero] at h; omega
    have hunion : C₀ ∪ C₁ = C := by
      ext b
      by_cases hbB : b ∈ F.B
      · rw [Set.mem_union, F.mem_iff_part_mem_vars hC₀B hs hbB,
          F.mem_iff_part_mem_vars hC₁B hs hbB, F.mem_iff_part_mem_vars hCB hs hbB,
          hvarsC, Finset.mem_union]
      · constructor
        · rintro (h | h)
          · exact absurd (hC₀B h) hbB
          · exact absurd (hC₁B h) hbB
        · intro h; exact absurd (hCB h) hbB
    have hC₀sub : C₀ ⊆ C := by rw [← hunion]; exact Set.subset_union_left
    have hC₀neC : C₀ ≠ C := by
      intro h
      obtain ⟨b, hb⟩ := hC₁ne
      have hbC : b ∈ C := by rw [← hunion]; exact Set.mem_union_right _ hb
      rw [← h] at hbC
      exact (Set.disjoint_left.1 hdisj hbC) hb
    -- So `C₀` is a nonempty strict subset of `C`; it remains to contradict minimality by
    -- showing `χ^F_{C₀}(E,E) = E`.
    refine hCmin C₀ (Set.ssubset_iff_subset_ne.2 ⟨hC₀sub, hC₀neC⟩) hC₀ne ?_
    have hfac : poly C (F.chimeraImage C₀ E E) = poly C₀ E * poly C₁ E := by
      have h := F.poly_union_chimeraImage hC₀B hC₁B hdisj E E
      rw [hunion] at h
      exact h
    have hrel : poly C E
        = MvPolynomial.C (r₀ * r₁) * poly C (F.chimeraImage C₀ E E) := by
      rw [hfac, hprod, hp₀, hp₁, map_mul]; ring
    -- `monos^F_C(E) = monos^F_C(χ^F_{C₀}(E,E))`, in the form of an equality of supports.
    have hsupp : monoExp C '' E = monoExp C '' (F.chimeraImage C₀ E E) := by
      ext d
      rw [← mem_support_poly C E, ← mem_support_poly C (F.chimeraImage C₀ E E),
        mem_support_iff, mem_support_iff, hrel, coeff_C_mul]
      simp [hr₀, hr₁]
    refine Set.Subset.antisymm ?_ (F.subset_chimeraImage_self C₀ E)
    rintro u ⟨s₀, hs₀, s₁, hs₁, rfl⟩
    have hu' : monoExp C (F.chimera C₀ s₀ s₁) ∈ monoExp C '' E := by
      rw [hsupp]
      exact ⟨_, ⟨s₀, hs₀, s₁, hs₁, rfl⟩, rfl⟩
    obtain ⟨s₃, hs₃, heq⟩ := hu'
    have hmono : mono C s₃ = mono C (F.chimera C₀ s₀ s₁) := by
      rw [mono_eq_monomial, mono_eq_monomial, heq]
    have hagree : ∀ b ∈ C, part b s₃ = part b (F.chimera C₀ s₀ s₁) :=
      (F.mono_eq_iff hCB).1 hmono
    have hueq : F.chimera C₀ s₀ s₁ = F.chimera C s₃ s₁ := by
      refine F.eq_of_forall_rel fun b hbB => ?_
      by_cases hbC : b ∈ C
      · have h1 : b (F.chimera C s₃ s₁) s₃ := F.chimera_rel_of_mem s₃ s₁ hbB hbC
        have h2 : b s₃ (F.chimera C₀ s₀ s₁) := part_eq_iff.1 (hagree b hbC)
        exact b.symm' (b.trans' h1 h2)
      · have h1 : b (F.chimera C s₃ s₁) s₁ := F.chimera_rel_of_notMem s₃ s₁ hbB hbC
        have h2 : b (F.chimera C₀ s₀ s₁) s₁ :=
          F.chimera_rel_of_notMem s₀ s₁ hbB fun hc => hbC (hC₀sub hc)
        exact b.trans' h2 (b.symm' h1)
    have hmem : F.chimera C s₃ s₁ ∈ F.chimeraImage C E E := ⟨s₃, hs₃, s₁, hs₁, rfl⟩
    rw [hCfix] at hmem
    rw [hueq]
    exact hmem

/-! ### Client-style uses of the §5.2 endpoints -/

/-- A client reading Proposition 29 as "every factor lies in exactly one irreducible
block". -/
example [Finite S] (F : FactoredSet S) {E : Set S} (hE : E.Nonempty) {b : Setoid S}
    (hb : b ∈ F.B) : ∃! C, C ∈ F.irr E ∧ b ∈ C := by
  obtain ⟨-, hdisj, hcover⟩ := F.irr_partition hE
  rw [← hcover] at hb
  obtain ⟨C, hC, hbC⟩ := hb
  refine ⟨C, ⟨hC, hbC⟩, ?_⟩
  rintro C' ⟨hC', hbC'⟩
  by_contra hne
  exact Set.disjoint_left.1 (hdisj hC' hC hne) hbC' hbC

/-- A client reading Proposition 29 as pairwise disjointness. -/
example [Finite S] (F : FactoredSet S) {E : Set S} (hE : E.Nonempty)
    {C₀ C₁ : Set (Setoid S)} (h₀ : C₀ ∈ F.irr E) (h₁ : C₁ ∈ F.irr E) (hne : C₀ ≠ C₁)
    {b : Setoid S} (hb : b ∈ C₀) : b ∉ C₁ :=
  Set.disjoint_left.1 ((F.irr_partition hE).2.1 h₀ h₁ hne) hb

/-- Propositions 30 and 31 composed: `Q^F_E` is the product of a family of irreducibles. -/
example [Finite S] (F : FactoredSet S) {E : Set S} (hE : E.Nonempty) :
    F.Q E = ∏ᶠ C ∈ F.irr E, poly C E ∧ ∀ C ∈ F.irr E, Irreducible (poly C E) :=
  ⟨F.Q_eq_finprod_poly_irr hE, fun _ hC => F.irreducible_poly_of_mem_irr hE hC⟩

/-- A client extracting an irreducible *divisor* of the characteristic polynomial. -/
example [Finite S] (F : FactoredSet S) {E : Set S} (hE : E.Nonempty)
    {C : Set (Setoid S)} (hC : C ∈ F.irr E) : ∃ p, Irreducible p ∧ p ∣ F.Q E :=
  ⟨poly C E, F.irreducible_poly_of_mem_irr hE hC, F.poly_dvd_Q hE hC⟩

end FactoredSet

end FiniteFactoredSets
