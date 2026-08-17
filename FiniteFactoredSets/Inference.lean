import FiniteFactoredSets.ConditionalOrthogonality

/-!
# Inferring time: factored set models

This file is §6.1 of Garrabrant, *Temporal Inference with Finite Factored Sets*
(arXiv:2109.11513): factored set models of a sample space, orthogonality databases, what it
means for a model to model a database, consistency and completeness, and the inferred
temporal order `X <_D Y`.

## Modeling decision — `dd:model`

* Definition 38's model `M = (F, f)` is `structure Model (Ω)` bundling the carrier `S`, a
  `FactoredSet S`, the map `f : S → Ω`, and — because the paper's definition says *finite*
  factored set — a `Finite S` field.  The finiteness is part of the definition (it is what
  Definition 45 quantifies over), not a hypothesis on statements.
* Definition 39's preimages: `f⁻¹(ω)` and `f⁻¹(E)` are `Set.preimage`; `f⁻¹(X)` for a
  partition `X` of `Ω` is `Setoid.comap f X`, whose blocks are exactly the nonempty
  preimages of blocks of `X` — the paper's `{f⁻¹(x) | x ∈ X, f⁻¹(x) ≠ ∅}` verbatim.  All
  three are Mathlib-rendered (README table); `Model.pullback` names the third for
  legibility.
* Definition 40's database `D = (O, N)` is `structure OrthDatabase (Ω)` with two sets of
  triples of partitions; Definition 41's `X ⊥_D Y | Z` / `¬(X ⊥_D Y | Z)` are membership in
  `O` / `N` (`OrthDatabase.Orth`, `OrthDatabase.NotOrth`).
-/

universe u

namespace FiniteFactoredSets

/-! ## §3 working forms of Definition 17

Temporal inference argues about an *arbitrary* factored set through its histories, so it
needs Proposition 12's minimality in both directions pointwise: a factor lies in `h^F(X)`
exactly when some pair of points agrees on every *other* factor without being `X`-related.
These are the pointwise faces of `le_iff_history_subset` and belong to §3; they live here
because §6.2 is the first consumer. -/

namespace FactoredSet

variable {S : Type u} (F : FactoredSet S)

/-- Points agreeing on every factor of `h^F(X)` are `X`-related — the pointwise form of
`h^F(X) ⊢^F X` (Proposition 12 through Proposition 10 clause 7). -/
lemma rel_of_forall_mem_history [Finite F.B] {X : Setoid S} {s t : S}
    (h : ∀ b ∈ F.history X, b s t) : X s t :=
  ((F.le_iff_history_subset (F.history_subset X) X).2 subset_rfl)
    (commonRefinement_iff.2 h : commonRefinement (F.history X) s t)

/-- Minimality of `h^F(X)` in contrapositive form: a factor of the history is witnessed by
a pair of points that agree on every other factor while failing to be `X`-related. -/
lemma exists_not_rel_of_mem_history [Finite F.B] {X b : Setoid S} (hb : b ∈ F.history X) :
    ∃ s t : S, (∀ c ∈ F.B, c ≠ b → c s t) ∧ ¬ X s t := by
  by_contra hcon
  have hle : commonRefinement (F.B \ {b}) ≤ X := by
    intro s t hst
    by_contra hX
    exact hcon ⟨s, t, fun c hc hcb => commonRefinement_iff.1 hst c ⟨hc, hcb⟩, hX⟩
  exact ((F.le_iff_history_subset Set.sdiff_subset X).1 hle hb).2 rfl

/-- The converse of `exists_not_rel_of_mem_history`: such a pair puts `b` in `h^F(X)`.
No `b ∈ B` hypothesis is needed — off the basis the hypothesis forces `s = t`. -/
lemma mem_history_of_not_rel [Finite F.B] {X b : Setoid S} {s t : S}
    (hst : ∀ c ∈ F.B, c ≠ b → c s t) (hX : ¬ X s t) : b ∈ F.history X := by
  by_contra hbX
  have hsub : F.history X ⊆ F.B \ {b} := fun c hc =>
    ⟨F.history_subset X hc, fun hcb => hbX (by rw [← hcb]; exact hc)⟩
  have hle := (F.le_iff_history_subset Set.sdiff_subset X).2 hsub
  exact hX (hle (commonRefinement_iff.2 fun c hc => hst c hc.1 hc.2) : X s t)

/-- If `s` already agrees with `t` on every factor of `C`, splicing changes nothing:
`χ^F_C(s,t) = t`. -/
lemma chimera_eq_right {C : Set (Setoid S)} {s t : S} (h : ∀ b ∈ C, b ∈ F.B → b s t) :
    F.chimera C s t = t := by
  refine F.eq_of_forall_rel fun b hb => ?_
  by_cases hbC : b ∈ C
  · exact b.trans' (F.chimera_rel_of_mem s t hb hbC) (h b hbC hb)
  · exact F.chimera_rel_of_notMem s t hb hbC

end FactoredSet

/-! ## §6.1 Factored set models -/

/-- Definition 38: a model of `Ω` — a finite factored set `F` together with a map from its
underlying set to `Ω`.

Paper node: Definition 38 (§6.1). -/
structure Model (Ω : Type u) where
  {S : Type u}
  F : FactoredSet S
  f : S → Ω
  [finite : Finite S]

namespace Model

variable {Ω : Type u}

attribute [instance] Model.finite

/-- Definition 39's `f⁻¹(X)` for a partition `X` of `Ω`: the partition of `S` by
`Setoid.comap f X`, whose blocks are the nonempty preimages of blocks of `X`.  (Definition
39's `f⁻¹(ω)` and `f⁻¹(E)` are `Set.preimage`; see the README's Mathlib-rendered table.) -/
def pullback (M : Model Ω) (X : Setoid Ω) : Setoid M.S := Setoid.comap M.f X

@[simp] lemma pullback_apply (M : Model Ω) (X : Setoid Ω) (s t : M.S) :
    M.pullback X s t ↔ X (M.f s) (M.f t) := Iff.rfl

/-- The pullback of `Ind_Ω` is `Ind_S`: `f⁻¹({Ω}) = {S}`.  Every use of Proposition 24
inside a `Models` obligation goes through this. -/
@[simp] lemma pullback_top (M : Model Ω) : M.pullback (⊤ : Setoid Ω) = ⊤ := rfl

/-- The pullback along a model whose map is the identity is the partition itself. -/
@[simp] lemma pullback_id {S : Type u} [Finite S] (F : FactoredSet S) (X : Setoid S) :
    Model.pullback ⟨F, id⟩ X = X := rfl

end Model

/-- Definition 40: an orthogonality database on `Ω` — two sets `O`, `N` of triples of
partitions of `Ω` (the triples asserted orthogonal, resp. asserted not orthogonal).

Paper node: Definition 40 (§6.1). -/
structure OrthDatabase (Ω : Type u) where
  O : Set (Setoid Ω × Setoid Ω × Setoid Ω)
  N : Set (Setoid Ω × Setoid Ω × Setoid Ω)

namespace OrthDatabase

variable {Ω : Type u}

/-- Definition 41, first half: `X ⊥_D Y | Z` — the triple is asserted orthogonal by `D`.

Paper node: Definition 41 (§6.1). -/
def Orth (D : OrthDatabase Ω) (X Y Z : Setoid Ω) : Prop := (X, Y, Z) ∈ D.O

/-- Definition 41, second half: `¬(X ⊥_D Y | Z)` — the triple is asserted *not* orthogonal
by `D`.  (This is a positive assertion of `D`, not the negation of `Orth`.)

Paper node: Definition 41 (§6.1). -/
def NotOrth (D : OrthDatabase Ω) (X Y Z : Setoid Ω) : Prop := (X, Y, Z) ∈ D.N

/-- Definition 42: the model `M` models `D` when every orthogonality `D` asserts holds in `M`
under pullback, and every non-orthogonality `D` asserts fails in `M`.

Paper node: Definition 42 (§6.1). -/
def Models (M : Model Ω) (D : OrthDatabase Ω) : Prop :=
  ∀ X Y Z : Setoid Ω,
    (D.Orth X Y Z → M.F.OrthogonalGiven (M.pullback X) (M.pullback Y) (M.pullback Z)) ∧
    (D.NotOrth X Y Z → ¬ M.F.OrthogonalGiven (M.pullback X) (M.pullback Y) (M.pullback Z))

/-- Definition 43: `D` is consistent when some model of `Ω` models it.

Paper node: Definition 43 (§6.1). -/
def Consistent (D : OrthDatabase Ω) : Prop := ∃ M : Model Ω, Models M D

/-- Definition 44: `D` is complete when every triple is asserted one way or the other.

Paper node: Definition 44 (§6.1). -/
def Complete (D : OrthDatabase Ω) : Prop :=
  ∀ X Y Z : Setoid Ω, D.Orth X Y Z ∨ D.NotOrth X Y Z

/-- Definition 45: `X <_D Y` — in every model of `Ω` that models `D`, the pullback of `X` is
strictly before the pullback of `Y`.

Paper node: Definition 45 (§6.1). -/
def Before (D : OrthDatabase Ω) (X Y : Setoid Ω) : Prop :=
  ∀ M : Model Ω, Models M D → M.F.StrictlyBefore (M.pullback X) (M.pullback Y)

end OrthDatabase

end FiniteFactoredSets
