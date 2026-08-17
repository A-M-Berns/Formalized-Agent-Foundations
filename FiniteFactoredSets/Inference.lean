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

/-- The pullback of `Ind_Ω` is `Ind_S`: `f⁻¹({Ω}) = {S}`.  This is the rewrite that turns a
`Models` obligation at `Z = {Ω}` into an unconditional orthogonality, which is the shape
Proposition 24 (`orthogonal_iff_orthogonalGiven_top`) consumes. -/
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

/-- Definition 45: `X <_D Y` — `X` is *strictly before* `Y` according to `D`: in every model
of `Ω` that models `D`, the pullback of `X` is strictly before the pullback of `Y`.

The paper gives the relation no word, only the glyph `<_D`; the name says `Strictly` because
Definition 45 unfolds to `<^F` (`FactoredSet.StrictlyBefore`), *not* to Definition 19's
non-strict `≤^F` (`FactoredSet.Before`), and both base names occur in §6 expressions.

Paper node: Definition 45 (§6.1). -/
def StrictlyBefore (D : OrthDatabase Ω) (X Y : Setoid Ω) : Prop :=
  ∀ M : Model Ω, Models M D → M.F.StrictlyBefore (M.pullback X) (M.pullback Y)

/-! ### Reading Definition 45

Definition 45 quantifies over the models of `D`, so its content depends entirely on there
being any: irreflexive where `D` is consistent, vacuously total where it is not.  Both
sides are one-liners, and both are what a client needs before treating `X <_D Y` as an
inference. -/

/-- **Definition 45 is irreflexive on every consistent database.**  A model of `D` supplies
a factored set on which `<^F` is a *strict* inclusion of histories, which no partition
bears to itself.  So `X <_D Y` is not the total relation. -/
lemma not_strictlyBefore_self_of_consistent {D : OrthDatabase Ω} (hD : D.Consistent)
    (X : Setoid Ω) :
    ¬ D.StrictlyBefore X X := by
  obtain ⟨M, hM⟩ := hD
  exact fun h => lt_irrefl _ (h M hM)

/-- The other side of the same coin, and the trap worth recording: on an **inconsistent**
database Definition 45 is vacuously *total*, because it quantifies over models that do not
exist.  `X <_D Y` is therefore an inference only once `D` is known consistent — which is
why Propositions 33 and 35 come before Propositions 34 and 36 in the paper. -/
lemma strictlyBefore_of_not_consistent {D : OrthDatabase Ω} (hD : ¬ D.Consistent)
    (X Y : Setoid Ω) :
    D.StrictlyBefore X Y := fun M hM => absurd ⟨M, hM⟩ hD

/-- Client's-eye use of the first: against a consistent database an inferred order
separates its two partitions. -/
example {D : OrthDatabase Ω} (hD : D.Consistent) {X Y : Setoid Ω} (h : D.StrictlyBefore X Y) :
    X ≠ Y := by
  rintro rfl
  exact not_strictlyBefore_self_of_consistent hD X h

/-- …and of the second: against an inconsistent one it separates nothing, inferring every
pair in both directions. -/
example {D : OrthDatabase Ω} (hD : ¬ D.Consistent) (X Y : Setoid Ω) :
    D.StrictlyBefore X Y ∧ D.StrictlyBefore Y X :=
  ⟨strictlyBefore_of_not_consistent hD X Y, strictlyBefore_of_not_consistent hD Y X⟩

end OrthDatabase

end FiniteFactoredSets
