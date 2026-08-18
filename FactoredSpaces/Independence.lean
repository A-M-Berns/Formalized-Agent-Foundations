import FactoredSpaces.History

/-!
# Structural independence and structural time (§4.3–§4.4, Lemma B.1)
-/

namespace FactoredSpaces

universe u v

variable {I : Type u} [DecidableEq I] [Fintype I] {Ω : I → Type v}
variable {α β γ δ : Type*}

/-- **Structural independence.** `X ⊥_Ω Y` iff `H(X) ∩ H(Y) = ∅`.

Paper node: Definition 4.10 (§4.3). -/
def StructIndep (X : Pt Ω → α) (Y : Pt Ω → β) : Prop :=
  Disjoint (history X (Set.univ : Set (Pt Ω))) (history Y Set.univ)

/-- **Conditional structural independence.** `X ⊥_Ω Y | Z` iff `H(X | z) ∩ H(Y | z) = ∅`
for every value `z ∈ Val(Z)`, where `H(X | z)` conditions on the event `{Z = z}`.

Paper node: Definition 4.10 (§4.3). -/
def StructIndepGiven (X : Pt Ω → α) (Y : Pt Ω → β) (Z : Pt Ω → γ) : Prop :=
  ∀ z : γ, Disjoint (history X (fiber Z z)) (history Y (fiber Z z))

/-- **Structural time.** `X ≤_Ω Y` ("`X` is before `Y`") iff `H(X) ⊆ H(Y)`.

Paper node: Definition 4.11 (§4.4). -/
def Before (X : Pt Ω → α) (Y : Pt Ω → β) : Prop :=
  history X (Set.univ : Set (Pt Ω)) ⊆ history Y Set.univ

/-- **Strict structural time.** `X <_Ω Y` iff `H(X) ⊊ H(Y)`.

Paper node: Definition 4.11 (§4.4). -/
def StrictlyBefore (X : Pt Ω → α) (Y : Pt Ω → β) : Prop :=
  history X (Set.univ : Set (Pt Ω)) ⊂ history Y Set.univ

lemma StructIndep.symm {X : Pt Ω → α} {Y : Pt Ω → β} (h : StructIndep X Y) : StructIndep Y X :=
  Disjoint.symm h

lemma StructIndepGiven.symm {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ}
    (h : StructIndepGiven X Y Z) : StructIndepGiven Y X Z :=
  fun z => (h z).symm

/-- `H(U_i) ⊆ {i}`. -/
lemma history_bg_subset (i : I) (C : Set (Pt Ω)) (hC : Disintegrates {i} C) :
    history (bg (Ω := Ω) i) C ⊆ {i} :=
  history_subset_of_generates ⟨⟨fun a => a ⟨i, Finset.mem_singleton_self i⟩, fun _ _ => rfl⟩, hC⟩

/-- If `i ∈ H(X)` then the factor `Ω_i` genuinely varies: two points agreeing off `i`
and differing at `i` exist.  The weaker form of `mem_history_iff_exists_ne`, whose
separating pair must already differ at `i`. -/
lemma exists_ne_of_mem_history [Nonempty α] {X : Pt Ω → α} {i : I}
    (hi : i ∈ history X (Set.univ : Set (Pt Ω))) :
    ∃ a b : Pt Ω, (∀ j, j ≠ i → a j = b j) ∧ a i ≠ b i := by
  obtain ⟨a, b, hab, hne⟩ := (mem_history_iff_exists_ne X i).mp hi
  refine ⟨a, b, hab, fun h => hne (congrArg X (funext fun j => ?_))⟩
  by_cases hj : j = i
  · exact hj ▸ h
  · exact hab j hj

/-- If `i ∈ H(X)` then `i ∈ H(U_i)` (and so `H(U_i) = {i}` by `history_bg_subset`). -/
lemma mem_history_bg_of_mem_history [Nonempty α] {X : Pt Ω → α} {i : I}
    (hi : i ∈ history X (Set.univ : Set (Pt Ω))) :
    i ∈ history (bg (Ω := Ω) i) (Set.univ : Set (Pt Ω)) := by
  obtain ⟨a, b, hab, hne⟩ := exists_ne_of_mem_history hi
  by_contra hnot
  haveI : Nonempty (Ω i) := ⟨a i⟩
  have hgen := generates_history (bg (Ω := Ω) i) (Set.univ : Set (Pt Ω))
  rw [generates_iff] at hgen
  refine hne (hgen.2 a (Set.mem_univ _) b (Set.mem_univ _) fun j hj => ?_)
  exact hab j (fun h => hnot (h ▸ hj))

/-- **Structural time and structural independence**, the direction "`X ≤ Y` implies
`Y ⊥ Z ⟹ X ⊥ Z` for every variable `Z`" (universe-polymorphic in `Val(Z)`).

Paper node: Lemma 4.12 (§4.4). -/
theorem structIndep_of_before {X : Pt Ω → α} {Y : Pt Ω → β} (h : Before X Y)
    (Z : Pt Ω → γ) (hYZ : StructIndep Y Z) : StructIndep X Z :=
  Finset.disjoint_left.mpr fun _ hi hiZ => (Finset.disjoint_left.mp hYZ) (h hi) hiZ

/-- **Structural time and structural independence**, the direction "if `Y ⊥ Z ⟹ X ⊥ Z`
for every variable `Z`, then `X ≤ Y`".  Only the background variables `U_i` are needed
as witnesses, so the hypothesis is stated for them.

No hypothesis on `Val(X)`: if it is empty then `Ω` has no points and `H(X)` is either
`∅` (nothing to prove) or the singleton `{i}` of the unique empty factor, in which case
`H(U_i) = H(X)` and the hypothesis at `i` is already contradictory
(`history_eq_singleton_of_mem`, `history_eq_of_isEmpty`).

Paper node: Lemma 4.12 (§4.4). -/
theorem before_of_forall_bg {X : Pt Ω → α} {Y : Pt Ω → β}
    (h : ∀ i : I, StructIndep Y (bg (Ω := Ω) i) → StructIndep X (bg i)) : Before X Y := by
  rcases isEmpty_or_nonempty α with hα | hα
  · haveI := hα
    intro i hi
    obtain ⟨hΩi, hHX⟩ := history_eq_singleton_of_mem hi
    haveI := hΩi
    have hbg : history (bg (Ω := Ω) i) (Set.univ : Set (Pt Ω))
        = history X (Set.univ : Set (Pt Ω)) := history_eq_of_isEmpty _ _ _ _
    have hibg : i ∈ history (bg (Ω := Ω) i) (Set.univ : Set (Pt Ω)) := by rw [hbg]; exact hi
    have hnX : ¬ StructIndep X (bg (Ω := Ω) i) := fun hd =>
      Finset.disjoint_left.mp hd hi hibg
    have hnY : ¬ Disjoint (history Y (Set.univ : Set (Pt Ω)))
        (history (bg (Ω := Ω) i) (Set.univ : Set (Pt Ω))) := fun hY => hnX (h i hY)
    rw [hbg, hHX, Finset.disjoint_singleton_right, not_not] at hnY
    exact hnY
  · haveI := hα
    intro i hi
    by_contra hiY
    have hYU : StructIndep Y (bg (Ω := Ω) i) := by
      refine Finset.disjoint_left.mpr fun j hjY hjU => ?_
      have := history_bg_subset i _ (disintegrates_univ_set {i}) hjU
      rw [Finset.mem_singleton] at this
      exact hiY (this ▸ hjY)
    exact Finset.disjoint_left.mp (h i hYU) hi (mem_history_bg_of_mem_history hi)

/-- **Structural time and structural independence.** `X ≤_Ω Y` iff
`Y ⊥_Ω Z ⟹ X ⊥_Ω Z` for all variables `Z` on `Ω` (with `Val(Z)` ranging over the
factors' universe, which is where the witnesses `U_i` live).

Paper node: Lemma 4.12 (§4.4). -/
theorem before_iff_forall_structIndep (X : Pt Ω → α) (Y : Pt Ω → β) :
    Before X Y ↔ ∀ (γ : Type v) (Z : Pt Ω → γ), StructIndep Y Z → StructIndep X Z :=
  ⟨fun h _ Z hYZ => structIndep_of_before h Z hYZ,
   fun h => before_of_forall_bg fun i => h (Ω i) (bg i)⟩

/-- **Composition axiom** for structural independence:
`X ⊥ Y | W` and `X ⊥ Z | W` imply `X ⊥ (Y, Z) | W`.

Paper node: Lemma B.1 (§B.1). -/
theorem structIndepGiven_pair {X : Pt Ω → α} {Y : Pt Ω → β}
    {Z : Pt Ω → γ} {W : Pt Ω → δ} (hY : StructIndepGiven X Y W) (hZ : StructIndepGiven X Z W) :
    StructIndepGiven X (pair Y Z) W := by
  intro w
  rw [history_pair]
  exact Finset.disjoint_union_right.mpr ⟨hY w, hZ w⟩

end FactoredSpaces
