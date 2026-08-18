import FactoredSpaces.MainTheorem

/-!
# Graphoid and semigraphoid axioms (§5.1, Definition 5.1, Proposition 5.2)

Structural independence is a compositional semigraphoid.  Symmetry (axiom 1) is immediate
from Definition 4.10 — it is `StructIndepGiven.symm`, *not* routed through Theorem 6.2 —
and composition (axiom 6) is Lemma B.1; axioms 2–4 are derived, as in the paper, from
Theorem 6.2 together with the semigraphoid axioms of probabilistic conditional
independence, which are *proved* here for Definition 6.1's product form (the paper cites
Pearl for them), so no citation boundary remains.

Structural independence is *not* a graphoid: `not_isGraphoid_structIndepRel` is the
negative claim of Table 1 that §5.1 singles out as an important property — the
intersection axiom fails.
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v}

/-- A ternary independence relation on the random variables of `Ω` — a "set of triplets
`(X, Y, Z)`, usually denoted `X ⊥ Y | Z`" (Definition 5.1) — with the value spaces ranging
over `Type v`, the factors' universe (`dd:variable`).

The paper puts no nonemptiness condition on any of the three slots.  `[Nonempty]` is kept
on the two independent slots only, where Theorem 6.2 (via Lemma C.3) genuinely needs it;
the conditioning slot carries none. -/
abbrev IndepRel (Ω : I → Type v) : Type (max u (v + 1)) :=
  ∀ {α β γ : Type v} [Nonempty α] [Nonempty β],
    (Pt Ω → α) → (Pt Ω → β) → (Pt Ω → γ) → Prop

/-- **Semigraphoid.** A set of triplets satisfying the symmetry, decomposition, weak
union and contraction axioms (Table 1, axioms 1–4).

Paper node: Definition 5.1 (§5.1). -/
structure IsSemigraphoid (R : IndepRel Ω) : Prop where
  symm : ∀ {α β δ : Type v} [Nonempty α] [Nonempty β]
    (X : Pt Ω → α) (Y : Pt Ω → β) (W : Pt Ω → δ), R X Y W → R Y X W
  decomposition : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ), R X (pair Y Z) W → R X Y W
  weakUnion : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X (pair Y Z) W → R X Z (pair Y W)
  contraction : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X Y W → R X Z (pair Y W) → R X (pair Y Z) W

/-- **Graphoid.** A semigraphoid that also satisfies the intersection axiom (Table 1,
axiom 5): `(X ⊥ Y | Z, W) ∧ (X ⊥ Z | Y, W) ∧ Y ≠ Z ⟹ X ⊥ (Y, Z) | W`.

As in every other axiom, `Y` and `Z` may have different value spaces.  The paper's side
condition `Y ≠ Z` is then read heterogeneously, as `β = γ → ¬ HEq Y Z`: for two variables
sharing a value space it *is* `Y ≠ Z` (`heq_eq_eq`), and variables whose value spaces
differ are distinct with nothing to exclude.

Paper node: Definition 5.1 (§5.1). -/
structure IsGraphoid (R : IndepRel Ω) : Prop extends IsSemigraphoid R where
  intersection : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X Y (pair Z W) → R X Z (pair Y W) → (β = γ → ¬ HEq Y Z) → R X (pair Y Z) W

/-- **Compositional semigraphoid.** A semigraphoid that also satisfies the composition
axiom (Table 1, axiom 6): `(X ⊥ Y | W) ∧ (X ⊥ Z | W) ⟹ X ⊥ (Y, Z) | W`.

Paper node: Definition 5.1 (§5.1). -/
structure IsCompositionalSemigraphoid (R : IndepRel Ω) : Prop extends IsSemigraphoid R where
  composition : ∀ {α β γ δ : Type v} [Nonempty α] [Nonempty β] [Nonempty γ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X Y W → R X Z W → R X (pair Y Z) W

/-- Structural independence given a variable, as an `IndepRel`. -/
def structIndepRel (Ω : I → Type v) : IndepRel Ω :=
  fun X Y Z => StructIndepGiven X Y Z

section Probabilistic

variable [∀ i, Fintype (Ω i)]

/-- Probabilistic conditional independence in `P`, as an `IndepRel`. -/
def condIndepRel (P : Distr (Pt Ω)) : IndepRel Ω := fun X Y Z => CondIndepVar P X Y Z

/-- The decomposition axiom for probabilistic conditional independence. -/
private lemma condIndepVar_decomposition {α β κ δ : Type*} (P : Distr (Pt Ω)) {X : Pt Ω → α}
    {Y : Pt Ω → β} {Z : Pt Ω → κ} {W : Pt Ω → δ} (h : CondIndepVar P X (pair Y Z) W) :
    CondIndepVar P X Y W := by
  classical
  intro x y w
  have hT : ∀ ω, Z ω ∈ (Finset.univ.image Z) := fun ω =>
    Finset.mem_image_of_mem Z (Finset.mem_univ ω)
  have hsum1 : P.prob (fiber Y y ∩ fiber W w)
      = ∑ z ∈ Finset.univ.image Z, P.prob (fiber Y y ∩ fiber Z z ∩ fiber W w) := by
    rw [Distr.prob_eq_sum_fiber P (fiber Y y ∩ fiber W w) Z _ hT]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have hsum2 : P.prob (fiber X x ∩ fiber Y y ∩ fiber W w)
      = ∑ z ∈ Finset.univ.image Z,
        P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) := by
    rw [Distr.prob_eq_sum_fiber P (fiber X x ∩ fiber Y y ∩ fiber W w) Z _ hT]
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
private lemma condIndepVar_weakUnion {α β κ δ : Type*} (P : Distr (Pt Ω)) {X : Pt Ω → α}
    {Y : Pt Ω → β} {Z : Pt Ω → κ} {W : Pt Ω → δ} (h : CondIndepVar P X (pair Y Z) W) :
    CondIndepVar P X Z (pair Y W) := by
  rintro x z ⟨y, w⟩
  have hd := condIndepVar_decomposition P h x y w
  have h2 := h x (y, z) w
  rw [fiber_pair] at h2
  have e1 : fiber X x ∩ (fiber Y y ∩ fiber W w) = fiber X x ∩ fiber Y y ∩ fiber W w :=
    (Set.inter_assoc _ _ _).symm
  have e2 : fiber Z z ∩ (fiber Y y ∩ fiber W w) = fiber Y y ∩ fiber Z z ∩ fiber W w :=
    (Set.inter_left_comm _ _ _).trans (Set.inter_assoc _ _ _).symm
  have e3 : fiber X x ∩ fiber Z z ∩ (fiber Y y ∩ fiber W w)
      = fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w := by
    simp only [Set.inter_assoc, Set.inter_left_comm]
  show P.prob (fiber X x ∩ fiber (pair Y W) (y, w)) * P.prob (fiber Z z ∩ fiber (pair Y W) (y, w))
      = P.prob (fiber X x ∩ fiber Z z ∩ fiber (pair Y W) (y, w)) * P.prob (fiber (pair Y W) (y, w))
  rw [fiber_pair, e1, e2, e3]
  by_cases hq : P.prob (fiber Y y ∩ fiber W w) = 0
  · have hu : P.prob (fiber X x ∩ fiber Y y ∩ fiber W w) = 0 :=
      Distr.prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.2, hω.2⟩) hq
    have hs : P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) = 0 :=
      Distr.prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.2.1, hω.2⟩) hq
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
private lemma condIndepVar_contraction {α β κ δ : Type*} (P : Distr (Pt Ω)) {X : Pt Ω → α}
    {Y : Pt Ω → β} {Z : Pt Ω → κ} {W : Pt Ω → δ} (h₁ : CondIndepVar P X Y W)
    (h₂ : CondIndepVar P X Z (pair Y W)) : CondIndepVar P X (pair Y Z) W := by
  rintro x ⟨y, z⟩ w
  have hA := h₁ x y w
  have e1 : fiber X x ∩ (fiber Y y ∩ fiber W w) = fiber X x ∩ fiber Y y ∩ fiber W w :=
    (Set.inter_assoc _ _ _).symm
  have e2 : fiber Z z ∩ (fiber Y y ∩ fiber W w) = fiber Y y ∩ fiber Z z ∩ fiber W w :=
    (Set.inter_left_comm _ _ _).trans (Set.inter_assoc _ _ _).symm
  have e3 : fiber X x ∩ fiber Z z ∩ (fiber Y y ∩ fiber W w)
      = fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w := by
    simp only [Set.inter_assoc, Set.inter_left_comm]
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
      Distr.prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.1, hω.2⟩) hq
    have hs : P.prob (fiber X x ∩ (fiber Y y ∩ fiber Z z) ∩ fiber W w) = 0 :=
      Distr.prob_eq_zero_of_subset P (by intro ω hω; exact ⟨hω.1.2.1, hω.2⟩) hq
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
lemma isSemigraphoid_condIndepRel (P : Distr (Pt Ω)) : IsSemigraphoid (condIndepRel P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β δ _ _ X Y W h y x w
    exact (h x y w).symm
  · intro α β κ δ _ _ _ X Y Z W h
    exact condIndepVar_decomposition P h
  · intro α β κ δ _ _ _ X Y Z W h
    exact condIndepVar_weakUnion P h
  · intro α β κ δ _ _ _ X Y Z W h₁ h₂
    exact condIndepVar_contraction P h₁ h₂

end Probabilistic

/-- **Structural independence is a compositional semigraphoid.**

Paper node: Proposition 5.2 (§5.1). -/
theorem isCompositionalSemigraphoid_structIndepRel [∀ i, Fintype (Ω i)] :
    IsCompositionalSemigraphoid (structIndepRel Ω) := by
  have hsemi : IsSemigraphoid (structIndepRel Ω) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro α β δ _ _ X Y W h
      exact h.symm
    · intro α β κ δ _ _ _ X Y Z W h
      refine structIndepGiven_of_forall_condIndepVar fun P hP => ?_
      exact (isSemigraphoid_condIndepRel P).decomposition X Y Z W
        (condIndepVar_of_structIndepGiven h P hP)
    · intro α β κ δ _ _ _ X Y Z W h
      refine structIndepGiven_of_forall_condIndepVar fun P hP => ?_
      exact (isSemigraphoid_condIndepRel P).weakUnion X Y Z W
        (condIndepVar_of_structIndepGiven h P hP)
    · intro α β κ δ _ _ _ X Y Z W h₁ h₂
      refine structIndepGiven_of_forall_condIndepVar fun P hP => ?_
      exact (isSemigraphoid_condIndepRel P).contraction X Y Z W
        (condIndepVar_of_structIndepGiven h₁ P hP) (condIndepVar_of_structIndepGiven h₂ P hP)
  refine ⟨hsemi, ?_⟩
  intro α β κ δ _ _ _ X Y Z W hY hZ
  exact structIndepGiven_pair hY hZ


/-- **Structural independence is not a graphoid**: it fails the intersection axiom.  This
is the negative claim of Table 1 that §5.1 calls an important property of structural
independence.  On its own the statement `¬ IsGraphoid` only says *some* graphoid axiom
fails; it pins the failure on axiom 5 (intersection) only together with Proposition 5.2
(`isCompositionalSemigraphoid_structIndepRel`), which supplies axioms 1–4 — the proof below
does refute intersection directly, but the theorem statement does not expose that.

The witness is the one-factor space `Ω = {0, 1}` with `X = Y = U`, `Z = ¬U` and `W`
constant.  Conditioning on `(Z, W)` or on `(Y, W)` pins the single factor down to one
point, so every conditional history there is empty and both premises hold; but
`H(X) = H((Y, Z)) = {*}`, so the conclusion `X ⊥ (Y, Z) | W` fails. -/
lemma not_isGraphoid_structIndepRel :
    ¬ IsGraphoid (structIndepRel fun _ : Unit => Bool) := by
  intro hG
  -- Conditioning on an event that fixes the only factor leaves every history empty.
  have hfix : ∀ {α : Type} (V : Pt (fun _ : Unit => Bool) → α)
      (C : Set (Pt (fun _ : Unit => Bool))) (b : Bool), (∀ ω ∈ C, ω () = b) →
      history V C = ∅ := by
    intro α V C b hC
    refine Finset.subset_empty.mp (history_subset_of_generates
      ⟨⟨fun _ => V fun _ => b, fun ω hω => ?_⟩, disintegrates_empty C⟩)
    have hω' : ω = fun _ => b := funext fun i => by cases i; exact hC ω hω
    rw [hω']
  -- `X ⊥ Y | (Z, W)`: the fibre of `(Z, W)` fixes the factor.
  have h₁ : StructIndepGiven (fun ω : Pt (fun _ : Unit => Bool) => ω ())
      (fun ω : Pt (fun _ : Unit => Bool) => ω ())
      (pair (fun ω : Pt (fun _ : Unit => Bool) => !ω ())
        (fun _ : Pt (fun _ : Unit => Bool) => ())) := by
    rintro ⟨b, u⟩
    have hpt : ∀ ω ∈ fiber (pair (fun ω : Pt (fun _ : Unit => Bool) => !ω ())
        (fun _ : Pt (fun _ : Unit => Bool) => ())) (b, u), ω () = !b := by
      intro ω hω
      have hω' : (!ω ()) = b := congrArg Prod.fst hω
      rw [← hω', Bool.not_not]
    rw [hfix _ _ _ hpt]
    exact Finset.disjoint_empty_left _
  -- `X ⊥ Z | (Y, W)`: the fibre of `(Y, W)` fixes the factor.
  have h₂ : StructIndepGiven (fun ω : Pt (fun _ : Unit => Bool) => ω ())
      (fun ω : Pt (fun _ : Unit => Bool) => !ω ())
      (pair (fun ω : Pt (fun _ : Unit => Bool) => ω ())
        (fun _ : Pt (fun _ : Unit => Bool) => ())) := by
    rintro ⟨b, u⟩
    have hpt : ∀ ω ∈ fiber (pair (fun ω : Pt (fun _ : Unit => Bool) => ω ())
        (fun _ : Pt (fun _ : Unit => Bool) => ())) (b, u), ω () = b :=
      fun ω hω => congrArg Prod.fst hω
    rw [hfix _ _ _ hpt, hfix _ _ _ hpt]
    exact Finset.disjoint_empty_left _
  -- `Y ≠ Z`, in the heterogeneous form the axiom asks for.
  have hne : (Bool = Bool) → ¬ HEq (fun ω : Pt (fun _ : Unit => Bool) => ω ())
      (fun ω : Pt (fun _ : Unit => Bool) => !ω ()) := by
    intro _ hh
    have := congrFun (eq_of_heq hh) (fun _ => true)
    simp at this
  have key := hG.intersection (fun ω : Pt (fun _ : Unit => Bool) => ω ())
    (fun ω : Pt (fun _ : Unit => Bool) => ω ())
    (fun ω : Pt (fun _ : Unit => Bool) => !ω ())
    (fun _ : Pt (fun _ : Unit => Bool) => ()) h₁ h₂ hne ()
  -- but the single factor is in both `H(X | W = *)` and `H((Y, Z) | W = *)`
  have hagree : ∀ j : Unit, j ≠ () →
      (fun _ : Unit => true) j = (fun _ : Unit => false) j :=
    fun j hj => absurd (Subsingleton.elim j ()) hj
  have hX : () ∈ history (fun ω : Pt (fun _ : Unit => Bool) => ω ())
      (fiber (fun _ : Pt (fun _ : Unit => Bool) => ()) ()) :=
    mem_history_of_sep (a := fun _ => true) (b := fun _ => false) rfl rfl hagree (by simp)
  have hYZ : () ∈ history (pair (fun ω : Pt (fun _ : Unit => Bool) => ω ())
        (fun ω : Pt (fun _ : Unit => Bool) => !ω ()))
      (fiber (fun _ : Pt (fun _ : Unit => Bool) => ()) ()) :=
    mem_history_of_sep (a := fun _ => true) (b := fun _ => false) rfl rfl hagree (by simp [pair])
  exact Finset.disjoint_left.mp key hX hYZ

end FactoredSpaces
