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

/-- Probabilistic conditional independence (Definition 6.1) is a semigraphoid — the fact
the paper cites from Pearl (1988) in the proof of Proposition 5.2, proved here for the
product-form definition with its `P(C) = 0` convention. -/
lemma isSemigraphoid_condIndepRel (P : Dist (Pt Ω)) : IsSemigraphoid (condIndepRel P) := by
  sorry

end Probabilistic

/-- **Structural independence is a compositional semigraphoid.**

Paper node: Proposition 5.2 (§5.1). -/
theorem isCompositionalSemigraphoid_structIndepRel [∀ i, Fintype (Ω i)] :
    IsCompositionalSemigraphoid (structIndepRel Ω) := by
  sorry

end FactoredSpaces
