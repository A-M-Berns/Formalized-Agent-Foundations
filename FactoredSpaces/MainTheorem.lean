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
  -- Lemma 4.9 turns the histories of `X` and `Y` into unions over their events, so
  -- disjointness of the histories is disjointness of every pair of event histories
  have hkey : ∀ D : Set (Pt Ω), Disjoint (history X D) (history Y D) ↔
      ∀ (x : α) (y : β), Disjoint (eventHistory (fiber X x) D) (eventHistory (fiber Y y) D) := by
    intro D
    constructor
    · intro hd x y
      exact Disjoint.mono (history_mono_of_derived (DerivedOn.comp_left fun v : α => v = x))
        (history_mono_of_derived (DerivedOn.comp_left fun v : β => v = y)) hd
    · intro hev
      rw [Finset.disjoint_left]
      intro i hiX hiY
      have h1 : i ∈ ⋃ x : α, (eventHistory (fiber X x) D : Set I) := by
        rw [← history_eq_iUnion_fibers]; exact hiX
      have h2 : i ∈ ⋃ y : β, (eventHistory (fiber Y y) D : Set I) := by
        rw [← history_eq_iUnion_fibers]; exact hiY
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h1
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp h2
      exact Finset.disjoint_left.mp (hev x y) hx hy
  constructor
  · intro h P hP x y z
    exact condIndep_of_disjoint_eventHistory ((hkey (fiber Z z)).mp (h z) x y) P hP
  · intro h z
    exact (hkey (fiber Z z)).mpr fun x y =>
      disjoint_eventHistory_of_condIndepAll fun P hP => h P hP x y z

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
  obtain ⟨Q, hQS⟩ := hne
  obtain ⟨ε, hε, hball⟩ := hopen Q hQS
  exact structIndepGiven_of_forall_condIndepVar
    (condIndepVar_of_local (hS hQS) hε fun Q' hQ'f hd => h Q' (hball Q' hQ'f hd))

end FactoredSpaces
