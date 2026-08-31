import FactoredSpaces.Completeness

/-!
# Soundness and completeness of structural independence (Theorem 6.2, Proposition 6.6)

`X ⊥_Ω Y | Z` iff `X ⊥^P Y | Z` for every `P ∈ Δ^⊗(Ω)`; and it suffices to have the
probabilistic independence on a nonempty open subset of `Δ^⊗(Ω)`.
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v} [∀ i, Fintype (Ω i)]
variable {α β γ : Type*}

/-- Theorem 6.2 with both value spaces inhabited — the case that carries the mathematics;
the paper-node statement above reduces to it whenever `Ω` is inhabited. -/
lemma structIndepGiven_iff_forall_condIndepVar_of_nonempty [Nonempty α] [Nonempty β]
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) :
    StructIndepGiven X Y Z ↔ ∀ P : Distr (Pt Ω), Factorizes P → CondIndepVar P X Y Z := by
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

/-- **Soundness and completeness of structural independence.** For random variables
`X, Y, Z` on the factored space `Ω`: `X ⊥_Ω Y | Z` iff `X ⊥^P Y | Z` holds for all
probability distributions `P` that factorize over `Ω`.

The hypothesis `Nonempty α ∨ Nonempty β` — at least one of `Val(X)`, `Val(Y)` inhabited —
is **added** by the formalization: the theorem as printed quantifies over arbitrary random
variables and is false exactly when both value spaces are empty (`notes/paper-errata.md`,
E14 — then some factor `Ω_i` is empty, there is no distribution at all, so the right-hand
side is vacuously true while `H(X | z)` is a nonempty set of indices).  The disjunction is
the weakest correction: with exactly one value space empty, `Ω` is empty, so the right-hand
side is again vacuous but now the inhabited side's history of the empty event is `∅` and
the left-hand side holds too.  Nothing is assumed about `Val(Z)`.  See `dd:variable` in
the glossary for where value-space inhabitation enters this development.

Paper node: Theorem 6.2 (§6.1). -/
theorem structIndepGiven_iff_forall_condIndepVar (hne : Nonempty α ∨ Nonempty β)
    (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) :
    StructIndepGiven X Y Z ↔ ∀ P : Distr (Pt Ω), Factorizes P → CondIndepVar P X Y Z := by
  by_cases hΩ : Nonempty (Pt Ω)
  · haveI := hΩ
    haveI : Nonempty α := ⟨X (Classical.arbitrary _)⟩
    haveI : Nonempty β := ⟨Y (Classical.arbitrary _)⟩
    exact structIndepGiven_iff_forall_condIndepVar_of_nonempty X Y Z
  · rw [not_nonempty_iff] at hΩ
    constructor
    · intro _ P _
      exact absurd P.nonempty_carrier (not_nonempty_iff.mpr hΩ)
    · intro _ z
      have hfib : fiber Z z = ∅ := Set.eq_empty_of_isEmpty _
      rcases hne with hα | hβ
      · rw [history_eq_empty_of_eq_empty X hfib]; exact Finset.disjoint_empty_left _
      · rw [history_eq_empty_of_eq_empty Y hfib]; exact Finset.disjoint_empty_right _

/-- The soundness direction of Theorem 6.2 on its own. -/
lemma condIndepVar_of_structIndepGiven
    {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ} (h : StructIndepGiven X Y Z)
    (P : Distr (Pt Ω)) (hP : Factorizes P) : CondIndepVar P X Y Z := by
  haveI : Nonempty (Pt Ω) := P.nonempty_carrier
  haveI : Nonempty α := ⟨X (Classical.arbitrary _)⟩
  exact (structIndepGiven_iff_forall_condIndepVar (Or.inl ‹_›) X Y Z).mp h P hP

/-- The completeness direction of Theorem 6.2 on its own, under the same
`Nonempty α ∨ Nonempty β` hypothesis as the theorem. -/
lemma structIndepGiven_of_forall_condIndepVar (hne : Nonempty α ∨ Nonempty β)
    {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ}
    (h : ∀ P : Distr (Pt Ω), Factorizes P → CondIndepVar P X Y Z) : StructIndepGiven X Y Z :=
  (structIndepGiven_iff_forall_condIndepVar hne X Y Z).mpr h

/-- **Strong completeness.** If there is a nonempty open set `S ⊆ Δ^⊗(Ω)` with
`X ⊥^P Y | Z` for all `P ∈ S`, then `X ⊥_Ω Y | Z`.  Openness of `S` in `Δ^⊗(Ω)` — a
subspace of `ℝ^Ω` with the Euclidean topology — is stated as the metric-ball criterion
(`dd:open-ball`): every `Q ∈ S` has an `ε`-ball in `Δ^⊗(Ω)` inside `S`.

Paper node: Proposition 6.6 (§6.2). -/
theorem structIndepGiven_of_open
    {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ} (S : Set (Distr (Pt Ω)))
    (hS : S ⊆ factorizing Ω) (hne : S.Nonempty)
    (hopen : ∀ Q ∈ S, ∃ ε > (0 : ℝ), ∀ Q' ∈ factorizing Ω, Distr.euclDist Q Q' < ε → Q' ∈ S)
    (h : ∀ P ∈ S, CondIndepVar P X Y Z) : StructIndepGiven X Y Z := by
  obtain ⟨Q, hQS⟩ := hne
  -- a distribution on `Ω` exists, so `Ω` and hence the value spaces of `X`, `Y` are inhabited
  haveI : Nonempty (Pt Ω) := Q.nonempty_carrier
  haveI : Nonempty α := ⟨X (Classical.arbitrary _)⟩
  haveI : Nonempty β := ⟨Y (Classical.arbitrary _)⟩
  obtain ⟨ε, hε, hball⟩ := hopen Q hQS
  exact structIndepGiven_of_forall_condIndepVar (Or.inl ‹_›)
    (condIndepVar_of_local (hS hQS) hε fun Q' hQ'f hd => h Q' (hball Q' hQ'f hd))

end FactoredSpaces
