import FiniteFactoredSets.Factoring
import FiniteFactoredSets.ConditionalOrthogonality
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Characteristic polynomials and orthogonality

This file is §5.3 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): Lemma 3 (`CPO`), the characterization of conditional orthogonality
by divisibility of characteristic polynomials.  It is the bridge from the combinatorics
of §4 to the probability of §5.4–§5.5.

`dd:poly` fixes the ring; the blocks `x ∈ X` of a partition of `S` are `Setoid.classes`
(as in Definitions 16 and 27), and `X ⊥^F Y | Z` is `OrthogonalGiven` (Definition 27).
`[Finite S]` is carried as the paper's "finite factored set" — the polynomial side needs it.

## How the two directions run

The paper proves `1 → 3` and `2 → 1`, `3 → 2` being immediate.

* `1 → 3` is four applications of Proposition 27 (`poly_union_chimeraImage`) along the
  split `B = C ∪ (B ∖ C)` at `C = h^F(X|z)`.  What makes the split work is that `C`
  generates `X|z` and `B ∖ C` generates `Y|z`; the latter is the public
  `generatesSub_iff_historySub_subset` applied to `B ∖ C`, whose two conjuncts are exactly
  the paper's `h^F(Y|z) ⊆ B ∖ C` and `χ^F_{B∖C}(z,z) = z`.
* `2 → 1` is the contradiction argument.  `Poly^F` is a `UniqueFactorizationMonoid`
  (`MvPolynomial.uniqueFactorizationMonoid`, which holds for an arbitrary variable type),
  so Proposition 31's irreducible `p = poly^F_C(z)` is prime and the divisibility of a
  product splits.  The rest recovers `Q^F_{x∩z} = poly^F_C(z) · poly^F_{B∖C}(x∩z)` from
  Proposition 28 and then reads `x ∩ z = χ^F_{B∖C}(x∩z, z)` off the injectivity of
  `E ↦ Q^F_E`.

The paper's `x ∩ z = {}` case has no counterpart here: the blocks of `X|z` are the
*nonempty* traces `x ∩ z` (`Subpartition.classes_restrict`), which is all that
`GeneratesSub` quantifies over.
-/

universe u

open MvPolynomial

namespace FiniteFactoredSets

variable {S : Type u}

/-- Blocks of a partition are closed under the relation: this is `Setoid.classes`
unfolded, and it is what turns "`χ^F_C(s,t) ∼_X s`" into "`χ^F_C(s,t) ∈ x`". -/
private lemma mem_classes_of_rel {X : Setoid S} {x : Set S} (hx : x ∈ X.classes) {u v : S}
    (hv : v ∈ x) (h : X u v) : u ∈ x := by
  obtain ⟨w, rfl⟩ := hx
  exact X.trans' h hv

private lemma nonempty_of_mem_classes {X : Setoid S} {x : Set S} (hx : x ∈ X.classes) :
    x.Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h => Setoid.empty_notMem_classes (h ▸ hx)

namespace FactoredSet

open scoped Classical

variable (F : FactoredSet S)

/-! ### Local glue

Four private facts §5.3 runs on.  `mem_chimeraImage_self` and `mem_iff_part_mem_vars`
restate §5.2's own `private` helpers (`Factoring.lean`'s `subset_chimeraImage_self`,
generalized to two sets, and its `mem_iff_part_mem_vars` verbatim); `private` is
module-scoped, and they are restated rather than promoted so that this section changes no
part of the §5.1–§5.2 surface.  `chimeraImage_sdiff` is the setwise form of Proposition 4
clause 4, and `eq_of_Q_eq` is the injectivity of `E ↦ Q^F_E`, whose one ingredient beyond
Proposition 26 — injectivity of `mono^F_B` — is the public `mono_eq_iff` at `C = B`. -/

private lemma mem_chimeraImage_self (C : Set (Setoid S)) {T R : Set S} {u : S}
    (hT : u ∈ T) (hR : u ∈ R) : u ∈ F.chimeraImage C T R :=
  ⟨u, hT, u, hR, F.chimera_self C u⟩

/-- Proposition 4 clause 4 setwise: `χ^F_{B∖C}(T,R) = χ^F_C(R,T)`. -/
private lemma chimeraImage_sdiff (C : Set (Setoid S)) (T R : Set S) :
    F.chimeraImage (F.B \ C) T R = F.chimeraImage C R T := by
  ext u
  constructor
  · rintro ⟨t, ht, r, hr, rfl⟩
    exact ⟨r, hr, t, ht, (F.chimera_sdiff C t r).symm⟩
  · rintro ⟨r, hr, t, ht, rfl⟩
    exact ⟨t, ht, r, hr, F.chimera_sdiff C t r⟩

/-- Reading a factor set off the variables of its polynomial (Proposition 31's opening
step): for `b ∈ B` and any `s ∈ E`, `b ∈ C` iff `[s]_b ∈ supp(poly^F_C(E))`. -/
private lemma mem_iff_part_mem_vars [Finite S] {C : Set (Setoid S)} (hC : C ⊆ F.B)
    {E : Set S} {s : S} (hs : s ∈ E) {b : Setoid S} (hb : b ∈ F.B) :
    b ∈ C ↔ part b s ∈ (poly C E).vars := by
  refine ⟨fun hbC => (F.mem_vars_poly hC E).2 ⟨b, hbC, s, hs, rfl⟩, fun hv => ?_⟩
  obtain ⟨b', hb', s', hs', heq⟩ := (F.mem_vars_poly hC E).1 hv
  exact F.eq_of_part_eq (hC hb') hb heq ▸ hb'

/-- `E ↦ Q^F_E` is injective: `mono^F_B` is injective (Proposition 3 with Corollary 1) and
`Q^F_E` is the sum over its image (Proposition 26), so the monomial set recovers `E`. -/
private lemma eq_of_Q_eq [Finite S] {E E' : Set S} (h : F.Q E = F.Q E') : E = E' := by
  have hinj : ∀ s t : S, mono F.B s = mono F.B t → s = t := fun _ _ hst =>
    F.eq_of_forall_rel fun b hb => part_eq_iff.1 ((F.mono_eq_iff le_rfl).1 hst b hb)
  rw [F.Q_eq_poly, F.Q_eq_poly] at h
  have hmonos : monos F.B E = monos F.B E' := monos_eq_of_support_eq (by rw [h])
  have himg : ∀ E₁ E₂ : Set S, monos F.B E₁ = monos F.B E₂ → E₁ ⊆ E₂ := by
    intro E₁ E₂ hm u hu
    have hmem : mono F.B u ∈ monos F.B E₂ := by rw [← hm]; exact ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hvu⟩ := hmem
    rwa [hinj v u hvu] at hv
  exact Set.Subset.antisymm (himg E E' hmonos) (himg E' E hmonos.symm)

/-! ## §5.3 Characteristic polynomials and orthogonality -/

/-! ### The `1 → 3` direction, one block of `Z` at a time -/

/-- The paper's proof of `1 → 3`, at a single block `z`: with `C = h^F(X|z)`, the four
chimera images `χ^F_C(z,z)`, `χ^F_C(x∩z, z)`, `χ^F_C(z, y∩z)` and `χ^F_C(x∩z, y∩z)` are
`z`, `x∩z`, `y∩z` and `x∩y∩z`, so Proposition 27 factors all four characteristic
polynomials over the split `B = C ∪ (B ∖ C)`. -/
private lemma Q_mul_Q_eq_of_orthogonalGivenSet [Finite S] {X Y : Setoid S} {z : Set S}
    (h : F.OrthogonalGivenSet X Y z) {x y : Set S} (hx : x ∈ X.classes) (hy : y ∈ Y.classes) :
    F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z) := by
  set C : Set (Setoid S) := F.historySub ((Subpartition.ofSetoid X).restrict z) with hCdef
  have hCB : C ⊆ F.B := F.historySub_subset _
  -- `C ⊢^F X|z`, in the relational form of Proposition 20 clause 5.
  have hXrel : ∀ s ∈ z, ∀ t ∈ z, F.chimera C s t ∈ z ∧ X (F.chimera C s t) s := by
    have hgen := (F.generatesSub_iff_rel C ((Subpartition.ofSetoid X).restrict z)).1
      (F.generatesSub_historySub _)
    intro s hs t ht
    have hsd : s ∈ ((Subpartition.ofSetoid X).restrict z).dom := by
      rw [Subpartition.dom_restrict_ofSetoid]; exact hs
    have htd : t ∈ ((Subpartition.ofSetoid X).restrict z).dom := by
      rw [Subpartition.dom_restrict_ofSetoid]; exact ht
    obtain ⟨h1, -, h3⟩ := hgen s hsd t htd
    exact ⟨h1, h3⟩
  -- `B ∖ C ⊢^F Y|z`: it contains `h^F(Y|z)` by orthogonality, and it fixes `z` because
  -- `χ^F_{B∖C}(s,t) = χ^F_C(t,s)`.
  have hDgen : F.GeneratesSub (F.B \ C) ((Subpartition.ofSetoid Y).restrict z) := by
    refine (F.generatesSub_iff_historySub_subset Set.sdiff_subset _).2 ⟨?_, ?_⟩
    · intro b hb
      refine ⟨F.historySub_subset _ hb, fun hbC => ?_⟩
      have hmem : b ∈ C ∩ F.historySub ((Subpartition.ofSetoid Y).restrict z) := ⟨hbC, hb⟩
      rw [hCdef, (F.orthogonalGivenSet_def X Y z).1 h] at hmem
      exact hmem
    · intro s hs t ht
      rw [Subpartition.dom_restrict_ofSetoid] at hs ht ⊢
      rw [F.chimera_sdiff]
      exact (hXrel t ht s hs).1
  have hYrel : ∀ s ∈ z, ∀ t ∈ z, Y (F.chimera C s t) t := by
    have hgen := (F.generatesSub_iff_rel (F.B \ C)
      ((Subpartition.ofSetoid Y).restrict z)).1 hDgen
    intro s hs t ht
    have hsd : s ∈ ((Subpartition.ofSetoid Y).restrict z).dom := by
      rw [Subpartition.dom_restrict_ofSetoid]; exact hs
    have htd : t ∈ ((Subpartition.ofSetoid Y).restrict z).dom := by
      rw [Subpartition.dom_restrict_ofSetoid]; exact ht
    obtain ⟨-, -, h3⟩ := hgen t htd s hsd
    rw [F.chimera_sdiff] at h3
    exact h3
  -- The four chimera images.
  have hZZ : F.chimeraImage C z z = z := by
    refine Set.Subset.antisymm ?_ fun u hu => F.mem_chimeraImage_self C hu hu
    rintro u ⟨s, hs, t, ht, rfl⟩
    exact (hXrel s hs t ht).1
  have hXZ : F.chimeraImage C (x ∩ z) z = x ∩ z := by
    refine Set.Subset.antisymm ?_ fun u hu => F.mem_chimeraImage_self C hu hu.2
    rintro u ⟨s, ⟨hsx, hsz⟩, t, ht, rfl⟩
    exact ⟨mem_classes_of_rel hx hsx (hXrel s hsz t ht).2, (hXrel s hsz t ht).1⟩
  have hZY : F.chimeraImage C z (y ∩ z) = y ∩ z := by
    refine Set.Subset.antisymm ?_ fun u hu => F.mem_chimeraImage_self C hu.2 hu
    rintro u ⟨s, hsz, t, ⟨hty, htz⟩, rfl⟩
    exact ⟨mem_classes_of_rel hy hty (hYrel s hsz t htz), (hXrel s hsz t htz).1⟩
  have hXY : F.chimeraImage C (x ∩ z) (y ∩ z) = x ∩ y ∩ z := by
    refine Set.Subset.antisymm ?_ fun u hu =>
      F.mem_chimeraImage_self C ⟨hu.1.1, hu.2⟩ ⟨hu.1.2, hu.2⟩
    rintro u ⟨s, ⟨hsx, hsz⟩, t, ⟨hty, htz⟩, rfl⟩
    exact ⟨⟨mem_classes_of_rel hx hsx (hXrel s hsz t htz).2,
      mem_classes_of_rel hy hty (hYrel s hsz t htz)⟩, (hXrel s hsz t htz).1⟩
  -- Proposition 27 along `B = C ∪ (B ∖ C)`.
  have hdisj : Disjoint C (F.B \ C) := Set.disjoint_left.2 fun b hb hb' => hb'.2 hb
  have key : ∀ E₀ E₁ : Set S,
      poly F.B (F.chimeraImage C E₀ E₁) = poly C E₀ * poly (F.B \ C) E₁ := by
    intro E₀ E₁
    have hp := F.poly_union_chimeraImage hCB Set.sdiff_subset hdisj E₀ E₁
    rwa [Set.union_sdiff_cancel hCB] at hp
  have e1 : F.Q z = poly C z * poly (F.B \ C) z := by
    rw [F.Q_eq_poly, ← key z z, hZZ]
  have e2 : F.Q (x ∩ z) = poly C (x ∩ z) * poly (F.B \ C) z := by
    rw [F.Q_eq_poly, ← key (x ∩ z) z, hXZ]
  have e3 : F.Q (y ∩ z) = poly C z * poly (F.B \ C) (y ∩ z) := by
    rw [F.Q_eq_poly, ← key z (y ∩ z), hZY]
  have e4 : F.Q (x ∩ y ∩ z) = poly C (x ∩ z) * poly (F.B \ C) (y ∩ z) := by
    rw [F.Q_eq_poly, ← key (x ∩ z) (y ∩ z), hXY]
  rw [e1, e2, e3, e4]
  ring

/-! ### The `2 → 1` direction

The engine is `generatesSub_sdiff_of_dvd`: an irreducible factor `poly^F_C(z)` of `Q^F_z`
that divides `Q^F_{w∩z}` for *every* block `w` of `W` forces `B ∖ C` to generate `W|z`,
hence `h^F(W|z) ⊆ B ∖ C`.  Applied to `X` and to `Y` it contradicts a common factor of
`h^F(X|z)` and `h^F(Y|z)`. -/

private lemma generatesSub_sdiff_of_dvd [Finite S] {W : Setoid S} {z : Set S}
    (hz : z.Nonempty) {C : Set (Setoid S)} (hCirr : C ∈ F.irr z)
    (hdvd : ∀ w ∈ W.classes, poly C z ∣ F.Q (w ∩ z)) :
    F.GeneratesSub (F.B \ C) ((Subpartition.ofSetoid W).restrict z) := by
  have hCB : C ⊆ F.B := hCirr.2.1
  intro v hv
  rw [Subpartition.classes_restrict] at hv
  obtain ⟨w, hw, rfl, hne⟩ := hv
  rw [Subpartition.classes_ofSetoid] at hw
  rw [Subpartition.dom_restrict_ofSetoid, F.chimeraImage_sdiff]
  -- `p = poly^F_C(z)` divides `Q^F_{w∩z}`; write the quotient and factor both sides.
  obtain ⟨q, hq⟩ := hdvd w hw
  obtain ⟨s, hs⟩ := hne
  have hsz : s ∈ z := hs.2
  have hpne : poly C z ≠ 0 := poly_ne_zero C hz
  have hQne : F.Q (w ∩ z) ≠ 0 := F.Q_ne_zero ⟨s, hs⟩
  have hqne : q ≠ 0 := fun h => hQne (by rw [hq, h, mul_zero])
  obtain ⟨r₀, C₀, hC₀B, hp₀⟩ :=
    F.eq_C_mul_poly_of_dvd_Q (E := w ∩ z) ⟨s, hs⟩ ⟨q, hq⟩
  obtain ⟨r₁, C₁, hC₁B, hp₁⟩ :=
    F.eq_C_mul_poly_of_dvd_Q (E := w ∩ z) ⟨s, hs⟩ ⟨poly C z, by rw [hq, mul_comm]⟩
  have hr₀ : r₀ ≠ 0 := by rintro rfl; rw [map_zero, zero_mul] at hp₀; exact hpne hp₀
  have hr₁ : r₁ ≠ 0 := by rintro rfl; rw [map_zero, zero_mul] at hp₁; exact hqne hp₁
  -- `C₀ = C`: the variables of `p` are the blocks at `s` of the factors of `C`.
  have hv₀ : (poly C z).vars = (poly C₀ (w ∩ z)).vars := by rw [hp₀, vars_C_mul r₀ hr₀]
  have hC₀ : C₀ = C := by
    ext b
    constructor
    · intro hb
      rw [F.mem_iff_part_mem_vars hCB hsz (hC₀B hb), hv₀]
      exact (F.mem_iff_part_mem_vars hC₀B hs (hC₀B hb)).1 hb
    · intro hb
      rw [F.mem_iff_part_mem_vars hC₀B hs (hCB hb), ← hv₀]
      exact (F.mem_iff_part_mem_vars hCB hsz (hCB hb)).1 hb
  rw [hC₀] at hp₀
  -- `r₀ = 1`: both `poly^F_C(z)` and `poly^F_C(w∩z)` have all coefficients `0` or `1`.
  obtain ⟨d, hd⟩ := support_nonempty.2 (poly_ne_zero C (⟨s, hs⟩ : (w ∩ z).Nonempty))
  have hcd : coeff d (poly C (w ∩ z)) = 1 := by
    rw [coeff_poly, if_pos ((mem_support_poly C (w ∩ z)).1 hd)]
  have hcz : coeff d (poly C z) = r₀ := by rw [hp₀, coeff_C_mul, hcd, mul_one]
  have hdz : d ∈ (poly C z).support := mem_support_iff.2 (by rw [hcz]; exact hr₀)
  have hcz1 : coeff d (poly C z) = 1 := by
    rw [coeff_poly, if_pos ((mem_support_poly C z).1 hdz)]
  have hr₀1 : r₀ = 1 := by rw [← hcz, hcz1]
  rw [hr₀1, map_one, one_mul] at hp₀
  -- `C₁ = B ∖ C`, read off the disjointness of the two factors' variables.
  have hdisjv : Disjoint (poly C z).vars q.vars := F.vars_disjoint_of_mul_eq_Q ⟨s, hs⟩ hq.symm
  have hv₁ : q.vars = (poly C₁ (w ∩ z)).vars := by rw [hp₁, vars_C_mul r₁ hr₁]
  have hC₁ : C₁ = F.B \ C := by
    ext b
    constructor
    · intro hb
      refine ⟨hC₁B hb, fun hbC => ?_⟩
      have h1 : part b s ∈ q.vars := by
        rw [hv₁]; exact (F.mem_iff_part_mem_vars hC₁B hs (hC₁B hb)).1 hb
      have h2 : part b s ∈ (poly C z).vars :=
        (F.mem_iff_part_mem_vars hCB hsz (hCB hbC)).1 hbC
      exact Finset.disjoint_left.1 hdisjv h2 h1
    · rintro ⟨hbB, hbC⟩
      have h3 : part b s ∈ (F.Q (w ∩ z)).vars := by
        rw [F.Q_eq_poly]
        exact (F.mem_vars_poly le_rfl (w ∩ z)).2 ⟨b, hbB, s, hs, rfl⟩
      rw [hq] at h3
      rcases Finset.mem_union.1 (vars_mul _ _ h3) with h4 | h4
      · exact absurd ((F.mem_iff_part_mem_vars hCB hsz hbB).2 h4) hbC
      · rw [hv₁] at h4
        exact (F.mem_iff_part_mem_vars hC₁B hs hbB).2 h4
  rw [hC₁] at hp₁
  -- `r₁ = 1`: the coefficients of `Q^F_{w∩z}` are `0` or `1`, and the two factors have
  -- disjoint variables, so no like terms combine.
  obtain ⟨e, he⟩ := support_nonempty.2 (poly_ne_zero (F.B \ C) (⟨s, hs⟩ : (w ∩ z).Nonempty))
  have hce : coeff e (poly (F.B \ C) (w ∩ z)) = 1 := by
    rw [coeff_poly, if_pos ((mem_support_poly (F.B \ C) (w ∩ z)).1 he)]
  have hceq : coeff e q = r₁ := by rw [hp₁, coeff_C_mul, hce, mul_one]
  have heq' : e ∈ q.support := mem_support_iff.2 (by rw [hceq]; exact hr₁)
  have hsplit : coeff (d + e) (F.Q (w ∩ z)) = r₁ := by
    rw [hq, coeff_add_mul_of_split hdisjv
      (fun i hi => support_subset_vars_of_mem_support hdz hi)
      (fun i hi => support_subset_vars_of_mem_support heq' hi), hcz1, hceq, one_mul]
  have hQ1 : coeff (d + e) (F.Q (w ∩ z)) = 1 := by
    have hne' : coeff (d + e) (F.Q (w ∩ z)) ≠ 0 := by rw [hsplit]; exact hr₁
    rw [F.Q_eq_poly] at hne' ⊢
    rw [coeff_poly, if_pos ((mem_support_poly F.B (w ∩ z)).1 (mem_support_iff.2 hne'))]
  have hr₁1 : r₁ = 1 := by rw [← hsplit, hQ1]
  rw [hr₁1, map_one, one_mul] at hp₁
  -- `Q^F_{w∩z} = poly^F_C(z) · poly^F_{B∖C}(w∩z)`, which Proposition 27 reads as
  -- `Q^F_{χ^F_C(z, w∩z)}`; injectivity of `E ↦ Q^F_E` finishes.
  refine F.eq_of_Q_eq ?_
  have hdisjC : Disjoint C (F.B \ C) := Set.disjoint_left.2 fun b hb hb' => hb'.2 hb
  have hfac := F.poly_union_chimeraImage hCB Set.sdiff_subset hdisjC z (w ∩ z)
  rw [Set.union_sdiff_cancel hCB] at hfac
  rw [F.Q_eq_poly (F.chimeraImage C z (w ∩ z)), hfac, ← hp₁, ← hq]

/-- Clause `2 → 1` of Lemma 3.  If `X ⊥^F Y | Z` fails, some block `z` has a factor `b` in
both `h^F(X|z)` and `h^F(Y|z)`; the irreducible block `C ∈ Irr^F(z)` containing `b` gives a
prime `p = poly^F_C(z)` dividing `Q^F_z`, hence dividing every `Q^F_{x∩z}` or every
`Q^F_{y∩z}`, and either way `B ∖ C` generates the corresponding restriction — which `b`
contradicts. -/
private lemma orthogonalGiven_of_Q_dvd [Finite S] {X Y Z : Setoid S}
    (h : ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
      F.Q z ∣ F.Q (x ∩ z) * F.Q (y ∩ z)) : F.OrthogonalGiven X Y Z := by
  intro z hz
  rw [F.orthogonalGivenSet_def]
  by_contra hne
  obtain ⟨b, hbX, hbY⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hzne : z.Nonempty := nonempty_of_mem_classes hz
  have hbB : b ∈ F.B := F.historySub_subset _ hbX
  obtain ⟨C, hCirr, hbC⟩ : ∃ C ∈ F.irr z, b ∈ C := by
    rw [← (F.irr_partition hzne).2.2] at hbB
    exact hbB
  have hprime : Prime (poly C z) := (F.irreducible_poly_of_mem_irr hzne hCirr).prime
  have hdich : (∀ x ∈ X.classes, poly C z ∣ F.Q (x ∩ z)) ∨
      (∀ y ∈ Y.classes, poly C z ∣ F.Q (y ∩ z)) := by
    rcases Classical.em (∀ x ∈ X.classes, poly C z ∣ F.Q (x ∩ z)) with hall | hall
    · exact Or.inl hall
    refine Or.inr fun y hy => ?_
    by_contra hny
    obtain ⟨x, hx, hnx⟩ : ∃ x ∈ X.classes, ¬ poly C z ∣ F.Q (x ∩ z) :=
      Classical.byContradiction fun hno =>
        hall fun x hx => Classical.byContradiction fun hn => hno ⟨x, hx, hn⟩
    rcases hprime.2.2 _ _
      (dvd_trans (F.poly_dvd_Q hzne hCirr) (h x hx y hy z hz)) with hd | hd
    · exact hnx hd
    · exact hny hd
  rcases hdich with hX | hY
  · exact (F.historySub_subset_of_generatesSub Set.sdiff_subset
      (F.generatesSub_sdiff_of_dvd hzne hCirr hX) hbX).2 hbC
  · exact (F.historySub_subset_of_generatesSub Set.sdiff_subset
      (F.generatesSub_sdiff_of_dvd hzne hCirr hY) hbY).2 hbC

/-- **Lemma 3** (`CPO`) — for partitions `X, Y, Z` of `S`, the following are equivalent:
(1) `X ⊥^F Y | Z`; (2) `Q^F_z ∣ Q^F_{x∩z} · Q^F_{y∩z}` for all blocks `x ∈ X`, `y ∈ Y`,
`z ∈ Z`; (3) `Q^F_z · Q^F_{x∩y∩z} = Q^F_{x∩z} · Q^F_{y∩z}` for all such blocks.

Paper node: Lemma 3 (§5.3). -/
theorem orthogonalGiven_tfae [Finite S] (X Y Z : Setoid S) :
    [F.OrthogonalGiven X Y Z,
     ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
       F.Q z ∣ F.Q (x ∩ z) * F.Q (y ∩ z),
     ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
       F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z)].TFAE := by
  -- 1 → 3: the paper's four applications of Proposition 27 at `C = h^F(X|z)`.
  tfae_have 1 → 3 := fun h x hx y hy z hz =>
    F.Q_mul_Q_eq_of_orthogonalGivenSet (h z hz) hx hy
  -- 3 → 2: "clearly condition 3 implies condition 2" — the cofactor is `Q^F_{x∩y∩z}`.
  tfae_have 3 → 2 := fun h x hx y hy z hz => ⟨F.Q (x ∩ y ∩ z), (h x hx y hy z hz).symm⟩
  -- 2 → 1: the contradiction argument, through primality of `poly^F_C(z)`.
  tfae_have 2 → 1 := F.orthogonalGiven_of_Q_dvd
  tfae_finish

/-- Lemma 3, clause 1 → clause 3, isolated: the direction the fundamental theorem's easy
half uses. -/
lemma Q_mul_Q_eq_of_orthogonalGiven [Finite S] {X Y Z : Setoid S}
    (h : F.OrthogonalGiven X Y Z) {x y z : Set S} (hx : x ∈ X.classes) (hy : y ∈ Y.classes)
    (hz : z ∈ Z.classes) : F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z) := by
  have h3 : ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
      F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z) :=
    ((F.orthogonalGiven_tfae X Y Z).out 0 2).1 h
  exact h3 x hx y hy z hz

/-- Lemma 3, clause 3 → clause 1, isolated: the direction the fundamental theorem's hard
half uses. -/
lemma orthogonalGiven_of_Q_mul_Q_eq [Finite S] {X Y Z : Setoid S}
    (h : ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
      F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z)) : F.OrthogonalGiven X Y Z :=
  ((F.orthogonalGiven_tfae X Y Z).out 2 0).1 h

/-! ### Client-style uses of Lemma 3

These `example`s consume the §5.3 endpoints the way §5.5 and a downstream file will —
through the `TFAE` projections and the two isolated directions, never by unfolding
`OrthogonalGiven`, `historySub` or `poly`. -/

/-- Clause 2 projected out of the `TFAE`: conditional orthogonality is a divisibility
statement about characteristic polynomials.  `List.TFAE.out` has autoparam arguments, so
the projected clause is bound by an explicitly typed `have` before being applied. -/
example (F : FactoredSet S) [Finite S] (X Y Z : Setoid S) (h : F.OrthogonalGiven X Y Z)
    {x y z : Set S} (hx : x ∈ X.classes) (hy : y ∈ Y.classes) (hz : z ∈ Z.classes) :
    F.Q z ∣ F.Q (x ∩ z) * F.Q (y ∩ z) := by
  have h2 : ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
      F.Q z ∣ F.Q (x ∩ z) * F.Q (y ∩ z) := ((F.orthogonalGiven_tfae X Y Z).out 0 1).1 h
  exact h2 x hx y hy z hz

/-- Lemma 3 composed with Proposition 25 (§4.3): `X ⊥^F X | Z` holds exactly when `Z ≤ X`,
so a refinement hypothesis alone yields the polynomial identity. -/
example (F : FactoredSet S) [Finite S] (X Z : Setoid S) (hZX : Z ≤ X) {x z : Set S}
    (hx : x ∈ X.classes) (hz : z ∈ Z.classes) :
    F.Q z * F.Q (x ∩ x ∩ z) = F.Q (x ∩ z) * F.Q (x ∩ z) :=
  F.Q_mul_Q_eq_of_orthogonalGiven ((F.orthogonalGiven_self_iff X Z).2 hZX) hx hx hz

/-- The hard direction used as a *certificate*: a client who has checked the polynomial
identity block by block gets conditional orthogonality, and hence — through Theorem 2's
symmetry — the same statement with the two partitions swapped. -/
example (F : FactoredSet S) [Finite S] (X Y Z : Setoid S)
    (h : ∀ x ∈ X.classes, ∀ y ∈ Y.classes, ∀ z ∈ Z.classes,
      F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z)) :
    F.OrthogonalGiven Y X Z :=
  (F.orthogonalGiven_semigraphoid X Y Z Z).1 (F.orthogonalGiven_of_Q_mul_Q_eq h)

/-- Lemma 3 and Proposition 24 together: unconditional orthogonality (Definition 18) is the
`Z = Ind_S` case, so it too is a statement about characteristic polynomials. -/
example (F : FactoredSet S) [Finite S] (X Y : Setoid S) (h : F.Orthogonal X Y)
    {x y z : Set S} (hx : x ∈ X.classes) (hy : y ∈ Y.classes) (hz : z ∈ (⊤ : Setoid S).classes) :
    F.Q z * F.Q (x ∩ y ∩ z) = F.Q (x ∩ z) * F.Q (y ∩ z) :=
  F.Q_mul_Q_eq_of_orthogonalGiven ((F.orthogonal_iff_orthogonalGiven_top X Y).1 h) hx hy hz

end FactoredSet

end FiniteFactoredSets
