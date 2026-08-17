import FactoredSpaces.MainTheorem

/-!
# Graphoid and semigraphoid axioms (§5.1, Definition 5.1, Proposition 5.2)

Structural independence is a compositional semigraphoid.  As in the paper, axioms 1–4 are
derived from Theorem 6.2 together with the semigraphoid axioms of probabilistic
conditional independence — which are *proved* here for Definition 6.1's product form
(the paper cites Pearl for them), so no citation boundary remains — and composition is
Lemma B.1.
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v}

/-- A ternary independence relation on the random variables of `Ω` — a "set of triplets
`(X, Y, Z)`, usually denoted `X ⊥ Y | Z`" (Definition 5.1) — with the value spaces ranging
over `Type v`, the factors' universe, and inhabited (`dd:variable`). -/
abbrev IndepRel (Ω : I → Type v) : Type (max u (v + 1)) :=
  ∀ {α β γ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ],
    (Pt Ω → α) → (Pt Ω → β) → (Pt Ω → γ) → Prop

/-- **Semigraphoid.** A set of triplets satisfying the symmetry, decomposition, weak
union and contraction axioms (Table 1, axioms 1–4).

Paper node: Definition 5.1 (§5.1). -/
structure IsSemigraphoid (R : IndepRel Ω) : Prop where
  symm : ∀ {α β δ : Type v} [Nonempty α] [Nonempty β] [Nonempty δ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (W : Pt Ω → δ), R X Y W → R Y X W
  decomposition : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ), R X (pair Y Z) W → R X Y W
  weakUnion : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X (pair Y Z) W → R X Z (pair Y W)
  contraction : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X Y W → R X Z (pair Y W) → R X (pair Y Z) W

/-- **Graphoid.** A semigraphoid that also satisfies the intersection axiom (Table 1,
axiom 5): `(X ⊥ Y | Z, W) ∧ (X ⊥ Z | Y, W) ∧ Y ≠ Z ⟹ X ⊥ (Y, Z) | W`.  (`Y ≠ Z` is
stated for variables of one value type; the paper does not say what it means across
types.)

Paper node: Definition 5.1 (§5.1). -/
structure IsGraphoid (R : IndepRel Ω) : Prop extends IsSemigraphoid R where
  intersection : ∀ {α β δ : Type v} [Nonempty α] [Nonempty β] [Nonempty δ]
    (X : Pt Ω → α) (Y Z : Pt Ω → β) (W : Pt Ω → δ),
    R X Y (pair Z W) → R X Z (pair Y W) → Y ≠ Z → R X (pair Y Z) W

/-- **Compositional semigraphoid.** A semigraphoid that also satisfies the composition
axiom (Table 1, axiom 6): `(X ⊥ Y | W) ∧ (X ⊥ Z | W) ⟹ X ⊥ (Y, Z) | W`.

Paper node: Definition 5.1 (§5.1). -/
structure IsCompositionalSemigraphoid (R : IndepRel Ω) : Prop extends IsSemigraphoid R where
  composition : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X Y W → R X Z W → R X (pair Y Z) W

/-- Structural independence given a variable, as an `IndepRel`. -/
def structIndepRel (Ω : I → Type v) : IndepRel Ω :=
  fun X Y Z => StructIndepGiven X Y Z

section Probabilistic

variable [∀ i, Fintype (Ω i)]

/-- Probabilistic conditional independence in `P`, as an `IndepRel`. -/
def condIndepRel (P : Dist (Pt Ω)) : IndepRel Ω := fun X Y Z => CondIndepVar P X Y Z

omit [DecidableEq I] [Fintype I] [∀ i, Fintype (Ω i)] in
/-- The fibre of a joint variable is the intersection of the fibres. -/
private lemma fiber_pair {β κ : Type*} (Y : Pt Ω → β) (Z : Pt Ω → κ) (y : β) (z : κ) :
    fiber (pair Y Z) (y, z) = fiber Y y ∩ fiber Z z := by
  ext ω; simp [fiber, pair, Prod.ext_iff, Set.mem_inter_iff]

private lemma prob_eq_zero_of_subset {S T : Set (Pt Ω)} (P : Dist (Pt Ω)) (hst : S ⊆ T)
    (h : P.prob T = 0) : P.prob S = 0 :=
  le_antisymm (h ▸ P.prob_mono hst) (P.prob_nonneg _)

/-- Regrouping an event along the fibres of a variable: if `T` contains every attained
value of `Z`, then `P(D) = ∑_{z ∈ T} P(D ∩ {Z = z})`.  Stated with an explicit `Finset`
of values because `Val(Z)` carries no `Fintype` instance (`dd:variable`). -/
private lemma prob_eq_sum_fiber {κ : Type*} [DecidableEq κ] (P : Dist (Pt Ω)) (D : Set (Pt Ω))
    (Z : Pt Ω → κ) (T : Finset κ) (hT : ∀ ω, Z ω ∈ T) :
    P.prob D = ∑ z ∈ T, P.prob (D ∩ fiber Z z) := by
  classical
  have key : ∀ ω : Pt Ω, ∑ z ∈ T, (D ∩ fiber Z z).indicator P.mass ω
      = D.indicator P.mass ω := by
    intro ω
    rw [Finset.sum_eq_single (Z ω)]
    · by_cases hω : ω ∈ D
      · rw [Set.indicator_of_mem (show ω ∈ D ∩ fiber Z (Z ω) from ⟨hω, rfl⟩),
          Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem (fun h => hω h.1), Set.indicator_of_notMem hω]
    · intro z _ hz
      exact Set.indicator_of_notMem (fun h => hz h.2.symm) _
    · intro h
      exact absurd (hT ω) h
  simp only [Dist.prob]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ => (key ω).symm

/-- The decomposition axiom for probabilistic conditional independence. -/
private lemma condIndepVar_decomposition {α β κ δ : Type*} (P : Dist (Pt Ω)) {X : Pt Ω → α}
    {Y : Pt Ω → β} {Z : Pt Ω → κ} {W : Pt Ω → δ} (h : CondIndepVar P X (pair Y Z) W) :
    CondIndepVar P X Y W := by
  classical
  intro x y w
  have hT : ∀ ω, Z ω ∈ (Finset.univ.image Z) := fun ω =>
    Finset.mem_image_of_mem Z (Finset.mem_univ ω)
  have hsum1 : P.prob (fiber Y y ∩ fiber W w)
      = ∑ z ∈ Finset.univ.image Z, P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) := by
    rw [prob_eq_sum_fiber P (fiber Y y ∩ fiber W w) Z _ hT]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have hsum2 : P.prob (fiber X x ∩ fiber Y y ∩ fiber W w)
      = ∑ z ∈ Finset.univ.image Z,
        P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) := by
    rw [prob_eq_sum_fiber P (fiber X x ∩ fiber Y y ∩ fiber W w) Z _ hT]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    ext ω; simp only [Set.mem_inter_iff]; tauto
  show P.prob (fiber X x ∩ fiber W w) * P.prob (fiber Y y ∩ fiber W w)
      = P.prob (fiber X x ∩ fiber Y y ∩ fiber W w) * P.prob (fiber W w)
  rw [hsum1, hsum2, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz := h x (y, z) w
  rw [fiber_pair] at hz
  exact hz

/-- The weak union axiom for probabilistic conditional independence. -/
private lemma condIndepVar_weakUnion {α β κ δ : Type*} (P : Dist (Pt Ω)) {X : Pt Ω → α}
    {Y : Pt Ω → β} {Z : Pt Ω → κ} {W : Pt Ω → δ} (h : CondIndepVar P X (pair Y Z) W) :
    CondIndepVar P X Z (pair Y W) := by
  rintro x z ⟨y, w⟩
  have hd := condIndepVar_decomposition P h x y w
  have h2 := h x (y, z) w
  rw [fiber_pair] at h2
  have e1 : fiber X x ∩ (fiber Y y ∩ fiber W w) = fiber X x ∩ fiber Y y ∩ fiber W w := by
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have e2 : fiber Z z ∩ (fiber Y y ∩ fiber W w) = fiber Y y ∩ fiber Z z ∩ fiber W w := by
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have e3 : fiber X x ∩ fiber Z z ∩ (fiber Y y ∩ fiber W w)
      = fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w := by
    ext ω; simp only [Set.mem_inter_iff]; tauto
  show P.prob (fiber X x ∩ fiber (pair Y W) (y, w)) * P.prob (fiber Z z ∩ fiber (pair Y W) (y, w))
      = P.prob (fiber X x ∩ fiber Z z ∩ fiber (pair Y W) (y, w)) * P.prob (fiber (pair Y W) (y, w))
  rw [fiber_pair, e1, e2, e3]
  by_cases hq : P.prob (fiber Y y ∩ fiber W w) = 0
  · have hu : P.prob (fiber X x ∩ fiber Y y ∩ fiber W w) = 0 :=
      prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.2, hω.2⟩) hq
    have hs : P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) = 0 :=
      prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.2.1, hω.2⟩) hq
    rw [hu, hs, hq, zero_mul, zero_mul]
  · have hqpos : 0 < P.prob (fiber Y y ∩ fiber W w) :=
      lt_of_le_of_ne (P.prob_nonneg _) (Ne.symm hq)
    have hcpos : 0 < P.prob (fiber W w) :=
      lt_of_lt_of_le hqpos (P.prob_mono (by intro ω hω; exact hω.2))
    refine mul_right_cancel₀ (ne_of_gt hcpos) ?_
    calc P.prob (fiber X x ∩ fiber Y y ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) * P.prob (fiber W w)
        = P.prob (fiber X x ∩ fiber Y y ∩ fiber W w) * P.prob (fiber W w)
            * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) := by ring
      _ = P.prob (fiber X x ∩ fiber W w) * P.prob (fiber Y y ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) := by rw [hd]
      _ = P.prob (fiber X x ∩ fiber W w) * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber W w) := by ring
      _ = P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) * P.prob (fiber W w)
            * P.prob (fiber Y y ∩ fiber W w) := by rw [h2]
      _ = P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber W w) * P.prob (fiber W w) := by ring

/-- The contraction axiom for probabilistic conditional independence. -/
private lemma condIndepVar_contraction {α β κ δ : Type*} (P : Dist (Pt Ω)) {X : Pt Ω → α}
    {Y : Pt Ω → β} {Z : Pt Ω → κ} {W : Pt Ω → δ} (h₁ : CondIndepVar P X Y W)
    (h₂ : CondIndepVar P X Z (pair Y W)) : CondIndepVar P X (pair Y Z) W := by
  rintro x ⟨y, z⟩ w
  have hA := h₁ x y w
  have e1 : fiber X x ∩ (fiber Y y ∩ fiber W w) = fiber X x ∩ fiber Y y ∩ fiber W w := by
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have e2 : fiber Z z ∩ (fiber Y y ∩ fiber W w) = fiber Y y ∩ fiber Z z ∩ fiber W w := by
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have e3 : fiber X x ∩ fiber Z z ∩ (fiber Y y ∩ fiber W w)
      = fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w := by
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have hB : P.prob (fiber X x ∩ fiber Y y ∩ fiber W w)
        * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w)
      = P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w)
        * P.prob (fiber Y y ∩ fiber W w) := by
    have hB₀ := h₂ x z (y, w)
    rw [show fiber (pair Y W) (y, w) = fiber Y y ∩ fiber W w from fiber_pair Y W y w] at hB₀
    have hB₁ : P.prob (fiber X x ∩ (fiber Y y ∩ fiber W w))
          * P.prob (fiber Z z ∩ (fiber Y y ∩ fiber W w))
        = P.prob (fiber X x ∩ fiber Z z ∩ (fiber Y y ∩ fiber W w))
          * P.prob (fiber Y y ∩ fiber W w) := hB₀
    rwa [e1, e2, e3] at hB₁
  show P.prob (fiber X x ∩ fiber W w) * P.prob (fiber (pair Y Z) (y, z) ∩ fiber W w)
      = P.prob (fiber X x ∩ fiber (pair Y Z) (y, z) ∩ fiber W w) * P.prob (fiber W w)
  rw [fiber_pair]
  by_cases hq : P.prob (fiber Y y ∩ fiber W w) = 0
  · have hv : P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) = 0 :=
      prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.1, hω.2⟩) hq
    have hs : P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) = 0 :=
      prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.2.1, hω.2⟩) hq
    rw [hv, hs, mul_zero, zero_mul]
  · have hqpos : 0 < P.prob (fiber Y y ∩ fiber W w) :=
      lt_of_le_of_ne (P.prob_nonneg _) (Ne.symm hq)
    refine mul_right_cancel₀ (ne_of_gt hqpos) ?_
    calc P.prob (fiber X x ∩ fiber W w) * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber W w)
        = P.prob (fiber X x ∩ fiber W w) * P.prob (fiber Y y ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) := by ring
      _ = P.prob (fiber X x ∩ fiber Y y ∩ fiber W w) * P.prob (fiber W w)
            * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) := by rw [hA]
      _ = P.prob (fiber X x ∩ fiber Y y ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) * P.prob (fiber W w) := by ring
      _ = P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w)
            * P.prob (fiber Y y ∩ fiber W w) * P.prob (fiber W w) := by rw [hB]
      _ = P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) * P.prob (fiber W w)
            * P.prob (fiber Y y ∩ fiber W w) := by ring

/-- Probabilistic conditional independence (Definition 6.1) is a semigraphoid — the fact
the paper cites from Pearl (1988) in the proof of Proposition 5.2, proved here for the
product-form definition with its `P(C) = 0` convention. -/
lemma isSemigraphoid_condIndepRel (P : Dist (Pt Ω)) : IsSemigraphoid (condIndepRel P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β δ _ _ _ X Y W h y x w
    exact (h x y w).symm
  · intro α β κ δ _ _ _ _ X Y Z W h
    exact condIndepVar_decomposition P h
  · intro α β κ δ _ _ _ _ X Y Z W h
    exact condIndepVar_weakUnion P h
  · intro α β κ δ _ _ _ _ X Y Z W h₁ h₂
    exact condIndepVar_contraction P h₁ h₂

end Probabilistic

/-- **Structural independence is a compositional semigraphoid.**

Paper node: Proposition 5.2 (§5.1). -/
theorem isCompositionalSemigraphoid_structIndepRel [∀ i, Fintype (Ω i)] :
    IsCompositionalSemigraphoid (structIndepRel Ω) := by
  have hsemi : IsSemigraphoid (structIndepRel Ω) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro α β δ _ _ _ X Y W h
      exact h.symm
    · intro α β κ δ _ _ _ _ X Y Z W h
      refine structIndepGiven_of_forall_condIndepVar fun P hP => ?_
      exact (isSemigraphoid_condIndepRel P).decomposition X Y Z W
        (condIndepVar_of_structIndepGiven h P hP)
    · intro α β κ δ _ _ _ _ X Y Z W h
      refine structIndepGiven_of_forall_condIndepVar fun P hP => ?_
      exact (isSemigraphoid_condIndepRel P).weakUnion X Y Z W
        (condIndepVar_of_structIndepGiven h P hP)
    · intro α β κ δ _ _ _ _ X Y Z W h₁ h₂
      refine structIndepGiven_of_forall_condIndepVar fun P hP => ?_
      exact (isSemigraphoid_condIndepRel P).contraction X Y Z W
        (condIndepVar_of_structIndepGiven h₁ P hP) (condIndepVar_of_structIndepGiven h₂ P hP)
  refine ⟨hsemi, ?_⟩
  intro α β κ δ _ _ _ _ X Y Z W hY hZ
  exact structIndepGiven_pair hY hZ

end FactoredSpaces
