import FiniteFactoredSets.History

/-!
# Orthogonality and time

This file is §3.3–§3.4 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): orthogonality of partitions (disjoint histories) and the temporal
order (inclusion of histories), together with their characterizations that avoid
mentioning history at all (Propositions 14, 16, 17).

## Finiteness

The *definitions* here — `Orthogonal`, `Entangled`, `Before`, `StrictlyBefore` — carry no
finiteness hypothesis at all: they read off `history`, which is defined for a factored set
of any dimension.  The *theorems* carry `[Finite F.B]`, finite dimension and never finite
`S` (`dd:finiteness-minimal`), because every one of them needs the history to actually
generate, and for infinite `F.B` it need not — see the counterexample in `History.lean`'s
module doc.  So an unrestricted `F.Orthogonal X Y` is a well-formed statement; it is just
not one Propositions 14–19 say anything about.

## Orientation

Orientation is Mathlib's throughout
(`dd:order-flip`): the paper's `X ≤_S Y` is `Y ≤ X`, `X ∨_S Y` is `X ⊓ Y`, `⋁_S(C)` is
`sInf C`, and `Ind_S` is `⊤`.
-/

universe u

namespace FiniteFactoredSets

variable {S : Type u}

namespace FactoredSet

open scoped Classical

variable (F : FactoredSet S)

/-! ## §3.3 Orthogonality -/

/-- Definition 18, first sentence: `X` is orthogonal to `Y` (in `F`), written `X ⊥^F Y`,
when their histories are disjoint.

Paper node: Definition 18 (§3.3). -/
def Orthogonal (X Y : Setoid S) : Prop := F.history X ∩ F.history Y = ∅

lemma orthogonal_def (X Y : Setoid S) :
    F.Orthogonal X Y ↔ F.history X ∩ F.history Y = ∅ := Iff.rfl

/-- Definition 18, second sentence: `X` is *entangled* with `Y` (in `F`) when it is not
orthogonal to it.  The paper names this in the same definition as `⊥^F`, so the node has
two carriers, as Definition 19 does.

Paper node: Definition 18 (§3.3). -/
def Entangled (X Y : Setoid S) : Prop := ¬ F.Orthogonal X Y

lemma entangled_iff (X Y : Setoid S) :
    F.Entangled X Y ↔ ¬ F.Orthogonal X Y := Iff.rfl

/-- Orthogonality element-wise: no factor lies in both histories.  Pure glue — the content
is Mathlib's `Set.disjoint_left`, reached by recognizing the definition as `Disjoint`. -/
lemma orthogonal_iff_forall_notMem (X Y : Setoid S) :
    F.Orthogonal X Y ↔ ∀ b ∈ F.history X, b ∉ F.history Y :=
  Set.disjoint_iff_inter_eq_empty.symm.trans Set.disjoint_left

/-- **Proposition 14** — orthogonality unpacked without history: `X ⊥^F Y` iff some
`C ⊆ B` has `X ≤_S ⋁_S(C)` and `Y ≤_S ⋁_S(B \ C)`, i.e. (in Mathlib's order)
`sInf C ≤ X` and `sInf (B \ C) ≤ Y`.

Paper node: Proposition 14 (§3.3). -/
theorem orthogonal_iff_exists [Finite F.B] (X Y : Setoid S) :
    F.Orthogonal X Y ↔
      ∃ C ⊆ F.B, commonRefinement C ≤ X ∧ commonRefinement (F.B \ C) ≤ Y := by
  constructor
  · -- Take `C = h^F(X)`.  Then `C ⊢^F X`, and `B \ C ⊇ h^F(Y)` by disjointness.
    intro h
    refine ⟨F.history X, F.history_subset X, F.commonRefinement_history_le X, ?_⟩
    refine (F.le_iff_history_subset Set.sdiff_subset Y).2 fun b hb => ?_
    exact ⟨F.history_subset Y hb, fun hbX => (F.orthogonal_iff_forall_notMem X Y).1 h b hbX hb⟩
  · -- `C ⊢^F X` and `B \ C ⊢^F Y`, so the two histories sit inside disjoint sets.
    rintro ⟨C, hC, hX, hY⟩
    have h₁ : F.history X ⊆ C := (F.le_iff_history_subset hC X).1 hX
    have h₂ : F.history Y ⊆ F.B \ C := (F.le_iff_history_subset Set.sdiff_subset Y).1 hY
    exact (F.orthogonal_iff_forall_notMem X Y).2 fun b hbX hbY => (h₂ hbY).2 (h₁ hbX)

/-- **Proposition 15** — the basic properties of orthogonality.  Clause 2's `Y ≤_S X` is
Mathlib's `X ≤ Y` and clause 3's `X ∨_S Y` is `X ⊓ Y` (`dd:order-flip`).

Paper node: Proposition 15 (§3.3). -/
theorem orthogonal_spec [Finite F.B] (X Y Z : Setoid S) :
    (F.Orthogonal X Y → F.Orthogonal Y X) ∧
    (F.Orthogonal X Z → X ≤ Y → F.Orthogonal Y Z) ∧
    (F.Orthogonal X Z → F.Orthogonal Y Z → F.Orthogonal (X ⊓ Y) Z) ∧
    (F.Orthogonal X X ↔ X = ⊤) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1: the definition is symmetric in `X` and `Y`.
    intro h
    rw [orthogonal_def, Set.inter_comm]
    exact h
  · -- 2: Proposition 13 clause 1 puts `h^F(Y)` inside `h^F(X)`.
    intro h hXY
    have hsub : F.history Y ⊆ F.history X := (F.history_spec Y X).1 hXY
    exact (F.orthogonal_iff_forall_notMem Y Z).2 fun b hbY =>
      (F.orthogonal_iff_forall_notMem X Z).1 h b (hsub hbY)
  · -- 3: Proposition 13 clause 2 splits `h^F(X ⊓ Y)` as a union.
    intro hXZ hYZ
    rw [orthogonal_def, (F.history_spec X Y).2.1, Set.union_inter_distrib_right,
      show F.history X ∩ F.history Z = ∅ from hXZ,
      show F.history Y ∩ F.history Z = ∅ from hYZ, Set.union_empty]
  · -- 4: Proposition 13 clause 3, after `s ∩ s = s`.
    rw [orthogonal_def, Set.inter_self]
    exact (F.history_spec X X).2.2.1

/-! ## §3.4 Time -/

/-- Definition 19, first half: `X` is before `Y` (in `F`), written `X ≤^F Y`, when
`h^F(X) ⊆ h^F(Y)`.

Paper node: Definition 19 (§3.4). -/
def Before (X Y : Setoid S) : Prop := F.history X ⊆ F.history Y

/-- Definition 19, second half: `X` is strictly before `Y`, written `X <^F Y`, when
`h^F(X) ⊂ h^F(Y)`.

Paper node: Definition 19 (§3.4). -/
def StrictlyBefore (X Y : Setoid S) : Prop := F.history X ⊂ F.history Y

lemma before_def (X Y : Setoid S) : F.Before X Y ↔ F.history X ⊆ F.history Y := Iff.rfl

lemma strictlyBefore_def (X Y : Setoid S) :
    F.StrictlyBefore X Y ↔ F.history X ⊂ F.history Y := Iff.rfl

/-- Strictly before implies before — the paper's `<^F` refines `≤^F`. -/
lemma StrictlyBefore.before {X Y : Setoid S} (h : F.StrictlyBefore X Y) : F.Before X Y :=
  h.subset

/-- **Proposition 16** — time unpacked without history: `X ≤^F Y` iff every `C ⊆ B` with
`Y ≤_S ⋁_S(C)` also has `X ≤_S ⋁_S(C)` (Mathlib's order: `sInf C ≤ Y → sInf C ≤ X`).

Paper node: Proposition 16 (§3.4). -/
theorem before_iff_forall_sInf [Finite F.B] (X Y : Setoid S) :
    F.Before X Y ↔ ∀ C ⊆ F.B, commonRefinement C ≤ Y → commonRefinement C ≤ X := by
  constructor
  · intro h C hC hCY
    exact (F.le_iff_history_subset hC X).2 (h.trans ((F.le_iff_history_subset hC Y).1 hCY))
  · -- The witness is `C = h^F(Y)`, which does satisfy `Y ≤_S ⋁_S(C)`.
    intro h
    exact (F.le_iff_history_subset (F.history_subset Y) X).1
      (h _ (F.history_subset Y) (F.commonRefinement_history_le Y))

/-- **Proposition 17** — time as a closure property of orthogonality: `X ≤^F Y` iff every
`Z` orthogonal to `Y` is orthogonal to `X`.  The paper's proof splits on whether `S` is
empty; the statement does not.

Paper node: Proposition 17 (§3.4). -/
theorem before_iff_forall_orthogonal [Finite F.B] (X Y : Setoid S) :
    F.Before X Y ↔ ∀ Z : Setoid S, F.Orthogonal Y Z → F.Orthogonal X Z := by
  constructor
  · -- Shrinking the left side of a disjointness preserves it; needs neither `Finite F.B`
    -- nor `Nonempty S`.
    intro h Z hYZ
    exact (F.orthogonal_iff_forall_notMem X Z).2 fun b hbX =>
      (F.orthogonal_iff_forall_notMem Y Z).1 hYZ b (h hbX)
  · intro h
    rcases isEmpty_or_nonempty S with hS | hS
    · -- Over the empty type every setoid has the empty relation, so `X = Y`.
      have hXY : X = Y := Setoid.ext fun a _ => (IsEmpty.false a).elim
      subst hXY
      exact subset_rfl
    · -- Otherwise a factor `b ∈ h^F(X) \ h^F(Y)` is itself the counterexample `Z := b`,
      -- because `h^F(b) = {b}` (Proposition 13 clause 4).
      by_contra hn
      obtain ⟨b, hbX, hbY⟩ :=
        Set.not_subset.1 (show ¬ (F.history X ⊆ F.history Y) from hn)
      have hhb : F.history b = {b} := (F.history_spec X Y).2.2.2 hS b (F.history_subset X hbX)
      have hbb : b ∈ F.history b := by rw [hhb]; exact Set.mem_singleton_iff.2 rfl
      have hYb : F.Orthogonal Y b := by
        refine (F.orthogonal_iff_forall_notMem Y b).2 fun c hcY hcb => hbY ?_
        rw [hhb, Set.mem_singleton_iff] at hcb
        subst hcb
        exact hcY
      exact (F.orthogonal_iff_forall_notMem X b).1 (h b hYb) b hbX hbb

/-- **Proposition 18** — the basic properties of time.  Clause 3's `X ≤_S Y` is Mathlib's
`Y ≤ X` and clause 4's `X ∨_S Y` is `X ⊓ Y` (`dd:order-flip`).

Paper node: Proposition 18 (§3.4). -/
theorem before_spec [Finite F.B] (X Y Z : Setoid S) :
    F.Before X X ∧
    (F.Before X Y → F.Before Y Z → F.Before X Z) ∧
    (Y ≤ X → F.Before X Y) ∧
    (F.Before X Z → F.Before Y Z → F.Before (X ⊓ Y) Z) := by
  refine ⟨subset_rfl, fun h₁ h₂ => h₁.trans h₂, (F.history_spec X Y).1, fun h₁ h₂ => ?_⟩
  -- Clause 4 is Proposition 13 clause 2 plus `Set.union_subset`.
  rw [before_def, (F.history_spec X Y).2.1]
  exact Set.union_subset h₁ h₂

/-- **Proposition 19** — history recovered from time, for nonempty `S`:
`h^F(X) = {b ∈ B | b ≤^F X}`.

Paper node: Proposition 19 (§3.4). -/
theorem history_eq_setOf_before [Finite F.B] [Nonempty S] (X : Setoid S) :
    F.history X = {b ∈ F.B | F.Before b X} := by
  ext b
  rw [Set.mem_sep_iff]
  constructor
  · intro hb
    have hbB : b ∈ F.B := F.history_subset X hb
    refine ⟨hbB, ?_⟩
    rw [before_def, (F.history_spec X X).2.2.2 ‹Nonempty S› b hbB]
    exact Set.singleton_subset_iff.2 hb
  · rintro ⟨hbB, hbX⟩
    rw [before_def, (F.history_spec X X).2.2.2 ‹Nonempty S› b hbB,
      Set.singleton_subset_iff] at hbX
    exact hbX

/-! ## Client-side sanity checks

These `example`s use the endpoints above the way a downstream file will: through the
annotated paper statements, never by unfolding `Orthogonal` or `Before`. -/

/-- Anything before `Y` inherits `Y`'s orthogonalities (Propositions 17 and 15). -/
example (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S)
    (hXY : F.Before X Y) (hYZ : F.Orthogonal Y Z) : F.Orthogonal Z X :=
  (F.orthogonal_spec X Z Z).1 ((F.before_iff_forall_orthogonal X Y).1 hXY Z hYZ)

/-- `Ind_S` (Mathlib's `⊤`) is before everything (Proposition 18 clause 3), so it is
orthogonal to whatever anything is orthogonal to (Proposition 17). -/
example (F : FactoredSet S) [Finite F.B] (Y Z : Setoid S) (h : F.Orthogonal Y Z) :
    F.Orthogonal ⊤ Z :=
  (F.before_iff_forall_orthogonal ⊤ Y).1 ((F.before_spec ⊤ Y Y).2.2.1 le_top) Z h

/-- Proposition 14 read as a client would: a witnessing split of the basis certifies
orthogonality, with no history in sight. -/
example (F : FactoredSet S) [Finite F.B] (X Y : Setoid S) (C : Set (Setoid S))
    (hC : C ⊆ F.B) (hX : commonRefinement C ≤ X) (hY : commonRefinement (F.B \ C) ≤ Y) :
    F.Orthogonal X Y :=
  (F.orthogonal_iff_exists X Y).2 ⟨C, hC, hX, hY⟩

/-- Entanglement runs forward in time: Proposition 17 contraposed says whatever `X` is
entangled with, everything `X` is before is entangled with too. -/
example (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S) (hXY : F.Before X Y)
    (h : F.Entangled X Z) : F.Entangled Y Z :=
  fun hYZ => h ((F.before_iff_forall_orthogonal X Y).1 hXY Z hYZ)

/-- `StrictlyBefore` used as a client would: it is `Before` with a witness of properness,
so every consequence of `≤^F` is available from `<^F`. -/
example (F : FactoredSet S) [Finite F.B] (X Y Z : Setoid S) (h : F.StrictlyBefore X Y)
    (hYZ : F.Orthogonal Y Z) : F.Orthogonal X Z :=
  (F.before_iff_forall_orthogonal X Y).1 h.before Z hYZ

/-- Proposition 16 read as a client would: a set of factors computing `Y` computes
everything before `Y`, with no history in sight. -/
example (F : FactoredSet S) [Finite F.B] (X Y : Setoid S) (C : Set (Setoid S))
    (hC : C ⊆ F.B) (hXY : F.Before X Y) (hY : commonRefinement C ≤ Y) :
    commonRefinement C ≤ X :=
  (F.before_iff_forall_sInf X Y).1 hXY C hC hY

/-- Proposition 19 read as a client would: a factor before `X` is a factor *of* `X`. -/
example (F : FactoredSet S) [Finite F.B] [Nonempty S] (X : Setoid S) {b : Setoid S}
    (hb : b ∈ F.B) (h : F.Before b X) : b ∈ F.history X := by
  rw [F.history_eq_setOf_before X]
  exact ⟨hb, h⟩

end FactoredSet

end FiniteFactoredSets
