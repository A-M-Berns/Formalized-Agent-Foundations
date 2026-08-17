import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Disjoint

/-!
# Factored spaces: points, projections, derived variables (§4, Definitions 4.1–4.2)

The paper's factored space `Ω = ×_{i∈I} Ω_i` is the dependent function type `Pt Ω`
(`dd:pi-space`); its projections `π_J`, merges `a · b` and background variables `U_J` are
`proj`, `Finset.piecewise` and `proj` again (`dd:splice`).  See `FactoredSpaces.lean` for
the glossary of `dd:` tags.
-/

/-! ## Generic `Finset.piecewise` algebra

Two lemmas about `Finset.piecewise` over a union and an intersection of index sets.  They
carry no factored-space content — they hold for an arbitrary family `π : ι → Sort*` — and
Mathlib has no counterpart, so they are stated in the root `Finset` namespace. -/

namespace Finset

variable {ι : Type*} {π : ι → Sort*} [DecidableEq ι]

/-- Splicing at a union splices twice: `(s ∪ t).piecewise f g` takes `f` on `s` and
`t.piecewise f g` off `s`. -/
lemma piecewise_union (s t : Finset ι) (f g : ∀ i, π i) [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] [∀ i, Decidable (i ∈ s ∪ t)] :
    (s ∪ t).piecewise f g = s.piecewise f (t.piecewise f g) := by
  funext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [Finset.piecewise, hs, ht]

/-- Splicing at an intersection splices twice: `(s ∩ t).piecewise f g` takes
`t.piecewise f g` on `s` and `g` off `s`. -/
lemma piecewise_inter (s t : Finset ι) (f g : ∀ i, π i) [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] [∀ i, Decidable (i ∈ s ∩ t)] :
    (s ∩ t).piecewise f g = s.piecewise (t.piecewise f g) g := by
  funext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [Finset.piecewise, hs, ht]

end Finset

namespace FactoredSpaces

universe u v

variable {I : Type u} {Ω : I → Type v}

/-- The point set of the factored space `Ω = ×_{i∈I} Ω_i`: the indexed families
`ω = (ω_i)_{i∈I}` with `ω_i ∈ Ω_i` (`dd:pi-space`).  The data `(I, Ω)` — an index type
and a family of factors — is the factored space itself; Definition 4.2's finiteness
requirements (`I` finite, every `Ω_i` finite) are carried as instance hypotheses on the
statements that use them (`dd:finiteness-minimal`), and the background variables `U_i`
are `bg`.

Paper node: Definition 4.2 (§4.1). -/
abbrev Pt (Ω : I → Type v) : Type max u v := ∀ i, Ω i

/-- The paper's `Ω_J = ×_{i∈J} Ω_i`: families indexed by the members of `J`. -/
abbrev PtOn (Ω : I → Type v) (J : Finset I) : Type max u v := ∀ i : J, Ω i

/-- The projection `π_J : Ω → Ω_J`, `π_J(ω) = (ω_j)_{j∈J}`; as a random variable this is
the paper's background variable `U_J` (Definition 4.2). -/
def proj (J : Finset I) (ω : Pt Ω) : PtOn Ω J := fun i => ω i

/-- The background variable `U_i : Ω → Ω_i`, `U_i(ω) = π_i(ω)`.

Paper node: Definition 4.2 (§4.1). -/
def bg (i : I) : Pt Ω → Ω i := fun ω => ω i

/-- The paper's projection of a set, `A_J = π_J(A) = {π_J(a) | a ∈ A}`. -/
def projSet (J : Finset I) (A : Set (Pt Ω)) : Set (PtOn Ω J) := proj J '' A

@[simp] lemma proj_apply (J : Finset I) (ω : Pt Ω) (i : J) : proj J ω i = ω i := rfl

lemma proj_eq_iff {J : Finset I} {a b : Pt Ω} :
    proj J a = proj J b ↔ ∀ i ∈ J, a i = b i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext ⟨i, hi⟩
    exact h i hi

section Derived

variable {α β γ : Type*}

/-- **Derived variable.** `Y` is derived from `X` on the event `C`, written `X ▷_C Y`: there
is `f : Val(X) → Val(Y)` with `Y(ω) = f(X(ω))` for all `ω ∈ C`.  A random variable
`X : Ω → Val(X)` is any function out of `Pt Ω` and `Val(X)` is its codomain
(`dd:variable`).  The unconditional `X ▷ Y` is `DerivedOn Set.univ X Y`.

Paper node: Definition 4.1 (§4). -/
def DerivedOn (C : Set (Pt Ω)) (X : Pt Ω → α) (Y : Pt Ω → β) : Prop :=
  ∃ f : α → β, ∀ ω ∈ C, Y ω = f (X ω)

/-- **Alternative characterization of derived variables.** `X ▷_C Y` iff `X` separates
`Y` on `C`: whenever two members of `C` agree under `X` they agree under `Y`.

The paper's proof of (ii) ⟹ (i) says "let `f(x)` be arbitrary" for values `x` not
attained on `C`, which silently needs `Val(Y)` inhabited: with `C = ∅`, `Val(X)`
nonempty and `Val(Y)` empty, (ii) holds vacuously but no `f : Val(X) → Val(Y)` exists.
The `[Nonempty β]` hypothesis is that implicit assumption made explicit (recorded in
`FactoredSpaces/KNOWLEDGE.md`, paper errata).

Paper node: Lemma C.3 (§C.1). -/
theorem derivedOn_iff [Nonempty β] {C : Set (Pt Ω)} (X : Pt Ω → α) (Y : Pt Ω → β) :
    DerivedOn C X Y ↔ ∀ ω ∈ C, ∀ ω' ∈ C, X ω = X ω' → Y ω = Y ω' := by
  classical
  constructor
  · rintro ⟨f, hf⟩ ω hω ω' hω' hx
    rw [hf ω hω, hf ω' hω', hx]
  · intro h
    refine ⟨fun x => if hx : ∃ ω ∈ C, X ω = x then Y hx.choose else Classical.arbitrary β, ?_⟩
    intro ω hω
    have hx : ∃ ω' ∈ C, X ω' = X ω := ⟨ω, hω, rfl⟩
    show Y ω = if hx : ∃ ω' ∈ C, X ω' = X ω then Y hx.choose else Classical.arbitrary β
    rw [dif_pos hx]
    obtain ⟨hmem, heq⟩ := hx.choose_spec
    exact (h _ hmem _ hω heq).symm

lemma DerivedOn.mono {C D : Set (Pt Ω)} {X : Pt Ω → α} {Y : Pt Ω → β}
    (h : DerivedOn D X Y) (hCD : C ⊆ D) : DerivedOn C X Y :=
  h.imp fun _ hf ω hω => hf ω (hCD hω)

lemma DerivedOn.trans {C : Set (Pt Ω)} {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ}
    (hXY : DerivedOn C X Y) (hYZ : DerivedOn C Y Z) : DerivedOn C X Z := by
  obtain ⟨f, hf⟩ := hXY
  obtain ⟨g, hg⟩ := hYZ
  exact ⟨g ∘ f, fun ω hω => by simp [hg ω hω, hf ω hω]⟩

lemma DerivedOn.refl (C : Set (Pt Ω)) (X : Pt Ω → α) : DerivedOn C X X :=
  ⟨id, fun _ _ => rfl⟩

lemma DerivedOn.comp_left {C : Set (Pt Ω)} {X : Pt Ω → α} (f : α → β) :
    DerivedOn C X (f ∘ X) :=
  ⟨f, fun _ _ => rfl⟩

/-- The joint variable `(X, Y) : Ω → Val(X) × Val(Y)` (§4, after Definition 4.1). -/
def pair (X : Pt Ω → α) (Y : Pt Ω → β) : Pt Ω → α × β := fun ω => (X ω, Y ω)

lemma DerivedOn.pair {C : Set (Pt Ω)} {X : Pt Ω → α} {Y : Pt Ω → β} {Z : Pt Ω → γ}
    (hY : DerivedOn C X Y) (hZ : DerivedOn C X Z) : DerivedOn C X (FactoredSpaces.pair Y Z) := by
  obtain ⟨f, hf⟩ := hY
  obtain ⟨g, hg⟩ := hZ
  exact ⟨fun x => (f x, g x), fun ω hω => by simp [FactoredSpaces.pair, hf ω hω, hg ω hω]⟩

end Derived

/-- The event `{X = x}`: the paper's shorthand `x` for the event `{ω ∈ Ω | X(ω) = x}`
(§4.2, "Shorthand notation for the history"). -/
def fiber {α : Type*} (X : Pt Ω → α) (x : α) : Set (Pt Ω) := {ω | X ω = x}

/-- The indicator variable `1_A : Ω → {0, 1}` of an event `A`, valued in `Prop`
(`dd:event-indicator`); the history of an event `A` is the history of `1_A`. -/
def indic (A : Set (Pt Ω)) : Pt Ω → Prop := fun ω => ω ∈ A

/-- The fibre of a joint variable is the intersection of the fibres. -/
lemma fiber_pair {α β : Type*} (X : Pt Ω → α) (Y : Pt Ω → β) (x : α) (y : β) :
    fiber (pair X Y) (x, y) = fiber X x ∩ fiber Y y := by
  ext ω; simp [fiber, pair, Prod.ext_iff, Set.mem_inter_iff]

end FactoredSpaces
