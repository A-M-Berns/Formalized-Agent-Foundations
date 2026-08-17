import FactoredSpaces.Completeness

/-!
# Soundness and completeness of structural independence (Theorem 6.2, Proposition 6.6)

`X ⊥_Ω Y | Z` iff `X ⊥^P Y | Z` for every `P ∈ Δ^F(Ω)`; and it suffices to have the
probabilistic independence on a nonempty open subset of `Δ^F(Ω)`.
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]
variable {α β γ : Type*}

/-- **Soundness and completeness of structural independence.** For random variables
`X, Y, Z` on the factored space `Ω`: `X ⊥_Ω Y | Z` iff `X ⊥^P Y | Z` holds for all
probability distributions `P` that factorize over `Ω`.

Paper node: Theorem 6.2 (§6.1). -/
theorem structIndepGiven_iff_forall_condIndepVar [Nonempty α] [Nonempty β] [Nonempty γ]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) :
    StructIndepGiven X Y Z ↔ ∀ P : Dist (Pt Ω), Factorizes P → CondIndepVar P X Y Z := by
  sorry

/-- The soundness direction of Theorem 6.2 on its own. -/
lemma condIndepVar_of_structIndepGiven [Nonempty α] [Nonempty β] [Nonempty γ]
    {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ} (h : StructIndepGiven X Y Z)
    (P : Dist (Pt Ω)) (hP : Factorizes P) : CondIndepVar P X Y Z :=
  (structIndepGiven_iff_forall_condIndepVar X Y Z).mp h P hP

/-- The completeness direction of Theorem 6.2 on its own. -/
lemma structIndepGiven_of_forall_condIndepVar [Nonempty α] [Nonempty β] [Nonempty γ]
    {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ}
    (h : ∀ P : Dist (Pt Ω), Factorizes P → CondIndepVar P X Y Z) : StructIndepGiven X Y Z :=
  (structIndepGiven_iff_forall_condIndepVar X Y Z).mpr h

/-- **Strong completeness.** If there is a nonempty open set `S ⊆ Δ^F(Ω)` with
`X ⊥^P Y | Z` for all `P ∈ S`, then `X ⊥_Ω Y | Z`.  Openness of `S` in `Δ^F(Ω)` — a
subspace of `ℝ^Ω` with the Euclidean topology — is stated as the metric-ball criterion
(`dd:open-ball`): every `Q ∈ S` has an `ε`-ball in `Δ^F(Ω)` inside `S`.

Paper node: Proposition 6.6 (§6.2). -/
theorem structIndepGiven_of_open [Nonempty α] [Nonempty β] [Nonempty γ]
    {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ} (S : Set (Dist (Pt Ω)))
    (hS : S ⊆ factorizing Ω) (hne : S.Nonempty)
    (hopen : ∀ Q ∈ S, ∃ ε > (0 : ℝ), ∀ Q' ∈ factorizing Ω, Dist.euclDist Q Q' < ε → Q' ∈ S)
    (h : ∀ P ∈ S, CondIndepVar P X Y Z) : StructIndepGiven X Y Z := by
  sorry

end FactoredSpaces
