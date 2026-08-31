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
intersection axiom fails.  `not_intersection_structIndepRel` states that failure
directly, naming the axiom, so the negative claim can be read without Proposition 5.2.
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v}

/-- A ternary independence relation on the random variables of `Ω` — a "set of triplets
`(X, Y, Z)`, usually denoted `X ⊥ Y | Z`" (Definition 5.1).

As in the paper, no slot carries a nonemptiness condition: the axioms below are asserted
for *every* triple of variables, including those whose value spaces are empty.

The value spaces range over `Type v`, the factors' own universe (where the background
variables `U_i` live), rather than over all universes.  That restriction is a Lean
limitation and no part of the paper's statement: a structure field cannot quantify over
universes, so the axioms of `IsSemigraphoid` / `IsGraphoid` /
`IsCompositionalSemigraphoid` have to fix one.  The results stated outside this structure
layer stay universe-polymorphic in the value spaces — Theorem 6.2
(`structIndepGiven_iff_forall_condIndepVar`), Proposition 6.6 (`structIndepGiven_of_open`)
and Lemma B.1 (`structIndepGiven_pair`). -/
abbrev IndepRel (Ω : I → Type v) : Type (max u (v + 1)) :=
  ∀ {α β γ : Type v}, (Pt Ω → α) → (Pt Ω → β) → (Pt Ω → γ) → Prop

/-- **Semigraphoid.** A set of triplets satisfying the symmetry, decomposition, weak
union and contraction axioms (Table 1, axioms 1–4).

Paper node: Definition 5.1 (§5.1). -/
structure IsSemigraphoid (R : IndepRel Ω) : Prop where
  symm : ∀ {α β δ : Type v}
    (X : Pt Ω → α) (Y : Pt Ω → β) (W : Pt Ω → δ), R X Y W → R Y X W
  decomposition : ∀ {α β γ δ : Type v}
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ), R X (pair Y Z) W → R X Y W
  weakUnion : ∀ {α β γ δ : Type v}
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X (pair Y Z) W → R X Z (pair Y W)
  contraction : ∀ {α β γ δ : Type v}
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
  intersection : ∀ {α β γ δ : Type v}
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) (W : Pt Ω → δ),
    R X Y (pair Z W) → R X Z (pair Y W) → (β = γ → ¬ HEq Y Z) → R X (pair Y Z) W

/-- **Compositional semigraphoid.** A semigraphoid that also satisfies the composition
axiom (Table 1, axiom 6): `(X ⊥ Y | W) ∧ (X ⊥ Z | W) ⟹ X ⊥ (Y, Z) | W`.

Paper node: Definition 5.1 (§5.1). -/
structure IsCompositionalSemigraphoid (R : IndepRel Ω) : Prop extends IsSemigraphoid R where
  composition : ∀ {α β γ δ : Type v}
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
  -- Definition 6.1 is stated over an arbitrary sample space, so its events are written as
  -- set-builders; the ascription re-reads them as the factored space's `fiber`s.
  have hz : CondIndep P (fiber X x) (fiber (pair Y Z) (y, z)) (fiber W w) := h x (y, z) w
  rw [fiber_pair] at hz
  exact hz

/-- The weak union axiom for probabilistic conditional independence. -/
private lemma condIndepVar_weakUnion {α β κ δ : Type*} (P : Distr (Pt Ω)) {X : Pt Ω → α}
    {Y : Pt Ω → β} {Z : Pt Ω → κ} {W : Pt Ω → δ} (h : CondIndepVar P X (pair Y Z) W) :
    CondIndepVar P X Z (pair Y W) := by
  rintro x z ⟨y, w⟩
  have hd : CondIndep P (fiber X x) (fiber Y y) (fiber W w) :=
    condIndepVar_decomposition P h x y w
  have h2 : CondIndep P (fiber X x) (fiber (pair Y Z) (y, z)) (fiber W w) := h x (y, z) w
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
  have hA : CondIndep P (fiber X x) (fiber Y y) (fiber W w) := h₁ x y w
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
    have hB₀ : CondIndep P (fiber X x) (fiber Z z) (fiber (pair Y W) (y, w)) := h₂ x z (y, w)
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
  · intro α β δ X Y W h y x w
    exact (h x y w).symm
  · intro α β κ δ X Y Z W h
    exact condIndepVar_decomposition P h
  · intro α β κ δ X Y Z W h
    exact condIndepVar_weakUnion P h
  · intro α β κ δ X Y Z W h₁ h₂
    exact condIndepVar_contraction P h₁ h₂

end Probabilistic

/-! ### The degenerate case: a factored space with no points

Definition 5.1 puts no nonemptiness condition on any of the three slots, so Proposition
5.2 asserts its axioms also for variables with empty value spaces.  Such a variable exists
only when `Ω` itself has no points, and then conditioning is vacuous: every event is `∅`
and the history of a variable does not depend on which event it is conditioned on.  That
one observation reduces every axiom to a set-theoretic triviality about `Finset` unions
(`history_pair` is itself hypothesis-free, so `H((Y, Z) | C) = H(Y | C) ∪ H(Z | C)` is
available there). -/

/-- With no points in `Ω` the history of a variable is independent of the conditioning
event: with an inhabited value space it is `∅`, and with an empty one it is the history
shared by all empty-valued variables (`{i₀}` for a unique empty factor `Ω_{i₀}`, and `∅`
if there are two or more). -/
private lemma history_indep_of_isEmpty_pt [IsEmpty (Pt Ω)] {α : Type*} (X : Pt Ω → α)
    (C D : Set (Pt Ω)) : history X C = history X D := by
  have hemp : ∀ E : Set (Pt Ω), E = ∅ := fun E =>
    Set.eq_empty_of_subset_empty fun ω _ => isEmptyElim ω
  rcases isEmpty_or_nonempty α with hα | hα
  · haveI := hα
    exact history_eq_of_isEmpty X X C D
  · haveI := hα
    rw [history_eq_empty_of_eq_empty X (hemp C), history_eq_empty_of_eq_empty X (hemp D)]

/-- **Structural independence is a compositional semigraphoid.**

Paper node: Proposition 5.2 (§5.1). -/
theorem isCompositionalSemigraphoid_structIndepRel [∀ i, Fintype (Ω i)] :
    IsCompositionalSemigraphoid (structIndepRel Ω) := by
  have hsemi : IsSemigraphoid (structIndepRel Ω) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro α β δ X Y W h
      exact h.symm
    · -- Decomposition: `H((Y, Z) | w) = H(Y | w) ∪ H(Z | w)` already gives this one, but
      -- we follow the paper and route it through Theorem 6.2 wherever that is available.
      intro α β κ δ X Y Z W h
      rcases isEmpty_or_nonempty (Pt Ω) with hΩ | hΩ
      · haveI := hΩ
        intro w
        have hw := h w
        rw [history_pair] at hw
        exact (Finset.disjoint_union_right.mp hw).1
      · haveI := hΩ
        haveI : Nonempty α := ⟨X (Classical.arbitrary _)⟩
        haveI : Nonempty β := ⟨Y (Classical.arbitrary _)⟩
        refine structIndepGiven_of_forall_condIndepVar (Or.inl ‹_›) fun P hP => ?_
        exact (isSemigraphoid_condIndepRel P).decomposition X Y Z W
          (condIndepVar_of_structIndepGiven h P hP)
    · intro α β κ δ X Y Z W h
      rcases isEmpty_or_nonempty (Pt Ω) with hΩ | hΩ
      · haveI := hΩ
        rintro ⟨y, w⟩
        have hw := h w
        rw [history_pair] at hw
        rw [history_indep_of_isEmpty_pt X (fiber (pair Y W) (y, w)) (fiber W w),
          history_indep_of_isEmpty_pt Z (fiber (pair Y W) (y, w)) (fiber W w)]
        exact (Finset.disjoint_union_right.mp hw).2
      · haveI := hΩ
        haveI : Nonempty α := ⟨X (Classical.arbitrary _)⟩
        haveI : Nonempty κ := ⟨Z (Classical.arbitrary _)⟩
        refine structIndepGiven_of_forall_condIndepVar (Or.inl ‹_›) fun P hP => ?_
        exact (isSemigraphoid_condIndepRel P).weakUnion X Y Z W
          (condIndepVar_of_structIndepGiven h P hP)
    · intro α β κ δ X Y Z W h₁ h₂
      rcases isEmpty_or_nonempty (Pt Ω) with hΩ | hΩ
      · haveI := hΩ
        intro w
        rw [history_pair]
        refine Finset.disjoint_union_right.mpr ⟨h₁ w, ?_⟩
        rcases isEmpty_or_nonempty β with hβ | hβ
        · -- No value of `Y` to condition on, so `h₂` is unusable; but then `X` and `Y`
          -- either share the empty-value history — which `h₁` forces to be `∅` — or
          -- `H(X | w) = ∅` outright.
          haveI := hβ
          have hX : history X (fiber W w) = ∅ := by
            rcases isEmpty_or_nonempty α with hα | hα
            · haveI := hα
              have hXY : history X (fiber W w) = history Y (fiber W w) :=
                history_eq_of_isEmpty X Y _ _
              have hd := h₁ w
              rw [hXY] at hd
              rw [hXY]
              exact Finset.eq_empty_of_forall_notMem fun i hi => Finset.disjoint_left.mp hd hi hi
            · haveI := hα
              exact history_eq_empty_of_eq_empty X
                (Set.eq_empty_of_subset_empty fun ω _ => isEmptyElim ω)
          rw [hX]
          exact Finset.disjoint_empty_left _
        · haveI := hβ
          have h2 := h₂ (Classical.arbitrary β, w)
          rwa [history_indep_of_isEmpty_pt X (fiber (pair Y W) (Classical.arbitrary β, w))
              (fiber W w),
            history_indep_of_isEmpty_pt Z (fiber (pair Y W) (Classical.arbitrary β, w))
              (fiber W w)] at h2
      · haveI := hΩ
        haveI : Nonempty α := ⟨X (Classical.arbitrary _)⟩
        haveI : Nonempty β := ⟨Y (Classical.arbitrary _)⟩
        haveI : Nonempty κ := ⟨Z (Classical.arbitrary _)⟩
        refine structIndepGiven_of_forall_condIndepVar (Or.inl ‹_›) fun P hP => ?_
        exact (isSemigraphoid_condIndepRel P).contraction X Y Z W
          (condIndepVar_of_structIndepGiven h₁ P hP) (condIndepVar_of_structIndepGiven h₂ P hP)
  refine ⟨hsemi, ?_⟩
  intro α β κ δ X Y Z W hY hZ
  exact structIndepGiven_pair hY hZ


/-- **Structural independence fails the intersection axiom** (Table 1, row
"Intersection", the negative claim §5.1 calls an important property of structural
independence), stated directly as the existence of a counterexample to axiom 5 rather
than as the negation of `IsGraphoid`.  Reading `¬ IsGraphoid` as "intersection fails"
needs Proposition 5.2 alongside it; this statement needs nothing.

The witness is the one-factor space `Ω = {0, 1, 2}` with the *pairwise distinct*
variables `X = U`, `Y = U + 1`, `Z = U + 2` and `W` constant — distinct as Pearl's
convention requires, so the refutation does not turn on a degenerate repetition of a
variable.  Conditioning on a value of `Z` (or of `Y`) pins the single factor down to one
point, so every conditional history there is empty and both premises hold; but the single
factor lies in `H(X)` and in `H((Y, Z))`, so the conclusion `X ⊥ (Y, Z) | W` fails.
Pairwise distinctness of `X`, `Y`, `Z` is part of the statement, so no reading of the
premises can make the counterexample degenerate. -/
lemma not_intersection_structIndepRel :
    ∃ (X Y Z : Pt (fun _ : Unit => Fin 3) → Fin 3) (W : Pt (fun _ : Unit => Fin 3) → Unit),
      StructIndepGiven X Y (pair Z W) ∧ StructIndepGiven X Z (pair Y W) ∧
        X ≠ Y ∧ X ≠ Z ∧ Y ≠ Z ∧ ¬ StructIndepGiven X (pair Y Z) W := by
  -- Conditioning on an event that fixes the only factor leaves every history empty.
  have hfix : ∀ {α : Type} (V : Pt (fun _ : Unit => Fin 3) → α)
      (C : Set (Pt (fun _ : Unit => Fin 3))) (b : Fin 3), (∀ ω ∈ C, ω () = b) →
      history V C = ∅ := by
    intro α V C b hC
    refine Finset.subset_empty.mp (history_subset_of_generates
      ⟨⟨fun _ => V fun _ => b, fun ω hω => ?_⟩, disintegrates_empty C⟩)
    have hω' : ω = fun _ => b := funext fun i => by cases i; exact hC ω hω
    rw [hω']
  refine ⟨fun ω => ω (), fun ω => ω () + 1, fun ω => ω () + 2, fun _ => (),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `X ⊥ Y | (Z, W)`: the fibre of `(Z, W)` fixes the factor.
    rintro ⟨c, u⟩
    have hpt : ∀ ω ∈ fiber (pair (fun ω : Pt (fun _ : Unit => Fin 3) => ω () + 2)
        (fun _ : Pt (fun _ : Unit => Fin 3) => ())) (c, u), ω () = c - 2 := by
      intro ω hω
      exact eq_sub_of_add_eq (congrArg Prod.fst hω)
    rw [hfix _ _ _ hpt]
    exact Finset.disjoint_empty_left _
  · -- `X ⊥ Z | (Y, W)`: the fibre of `(Y, W)` fixes the factor.
    rintro ⟨c, u⟩
    have hpt : ∀ ω ∈ fiber (pair (fun ω : Pt (fun _ : Unit => Fin 3) => ω () + 1)
        (fun _ : Pt (fun _ : Unit => Fin 3) => ())) (c, u), ω () = c - 1 := by
      intro ω hω
      exact eq_sub_of_add_eq (congrArg Prod.fst hω)
    rw [hfix _ _ _ hpt]
    exact Finset.disjoint_empty_left _
  · -- `X ≠ Y`
    intro hXY
    exact absurd (congrFun hXY (fun _ => (0 : Fin 3))) (by decide)
  · -- `X ≠ Z`
    intro hXZ
    exact absurd (congrFun hXZ (fun _ => (0 : Fin 3))) (by decide)
  · -- `Y ≠ Z`
    intro hYZ
    exact absurd (congrFun hYZ (fun _ => (0 : Fin 3))) (by decide)
  · -- but the single factor is in both `H(X | W = *)` and `H((Y, Z) | W = *)`
    intro hcon
    have hagree : ∀ j : Unit, j ≠ () →
        (fun _ : Unit => (0 : Fin 3)) j = (fun _ : Unit => (1 : Fin 3)) j :=
      fun j hj => absurd (Subsingleton.elim j ()) hj
    have hX : () ∈ history (fun ω : Pt (fun _ : Unit => Fin 3) => ω ())
        (fiber (fun _ : Pt (fun _ : Unit => Fin 3) => ()) ()) :=
      mem_history_of_sep (a := fun _ => 0) (b := fun _ => 1) rfl rfl hagree (by decide)
    have hYZ : () ∈ history (pair (fun ω : Pt (fun _ : Unit => Fin 3) => ω () + 1)
          (fun ω : Pt (fun _ : Unit => Fin 3) => ω () + 2))
        (fiber (fun _ : Pt (fun _ : Unit => Fin 3) => ()) ()) :=
      mem_history_of_sep (a := fun _ => 0) (b := fun _ => 1) rfl rfl hagree (by decide)
    exact Finset.disjoint_left.mp (hcon ()) hX hYZ

/-- **Structural independence is not a graphoid**: it fails the intersection axiom.  This
is the negative claim of Table 1 that §5.1 calls an important property of structural
independence.  On its own the statement `¬ IsGraphoid` only says *some* graphoid axiom
fails; `not_intersection_structIndepRel` above is the same refutation with the failing
axiom written out, and is the statement to read if the point is *which* axiom fails.

The witness is `not_intersection_structIndepRel`'s: the one-factor space `Ω = {0, 1, 2}`
with the pairwise distinct variables `X = U`, `Y = U + 1`, `Z = U + 2` and `W`
constant. -/
lemma not_isGraphoid_structIndepRel :
    ¬ IsGraphoid (structIndepRel fun _ : Unit => Fin 3) := by
  intro hG
  obtain ⟨X, Y, Z, W, h₁, h₂, -, -, hne, hcon⟩ := not_intersection_structIndepRel
  exact hcon (hG.intersection X Y Z W h₁ h₂ fun _ hh => hne (eq_of_heq hh))

end FactoredSpaces
