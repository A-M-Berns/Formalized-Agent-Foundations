import FiniteFactoredSets.ConditionalOrthogonality

/-!
# Embedded agency: observations, counterfactability, conditional time

This file is the in-scope part of §7.3 of Garrabrant, *Temporal Inference with Finite
Factored Sets* (arXiv:2109.11513): Definitions 46–50 — an agent observing an event or a
partition with respect to a world model, counterfactability (absolute and relative), and
conditional time.  §7 states no theorem about them, so this file carries definitions only,
each with the paper's phrasing rendered through the §3–§4 vocabulary.

## Modeling decisions

* Definition 46's `X_E` (`eventPartition E`) is `Setoid.comap (· ∈ E) ⊥`: two points are
  related iff they agree on membership in `E`.  Its blocks (`Setoid.classes`) are the
  nonempty ones among `E` and `S \ E`, so the paper's case split — `{S}` when `E = ∅` or
  `E = S`, `{E, S \ E}` otherwise — is absorbed rather than written out.
* Definition 47 lists `X = {x₀, …, xₙ₋₁}` and indexes the sub-agents `Aᵢ` by `i`; here the
  family is indexed by the blocks themselves, `As : X.classes → Setoid S`, and the paper's
  `⋁_S {Aᵢ}` is `sInf (Set.range As)` (`dd:order-flip`).  Indexing by blocks rather than by
  a numbering of them changes nothing and needs no finiteness.
* Definition 50's `h^F(X | E)` is `historySub ((ofSetoid X).restrict E)`, as in
  Definition 26.
* Per `dd:finiteness-minimal`, none of the five definitions carries a finiteness
  hypothesis: each is a formula in `history`/`historySub`/`Orthogonal`/`OrthogonalGiven`,
  all of which are defined for every factored set.
-/

universe u

namespace FiniteFactoredSets

variable {S : Type u}

namespace FactoredSet

open Subpartition

variable (F : FactoredSet S)

/-! ## §7.3.1 Embedded observations -/

/-- Definition 46's auxiliary partition `X_E`: `{S}` if `E` is empty or all of `S`, and
`{E, S \ E}` otherwise — rendered as the partition by membership in `E`, whose blocks are
the nonempty ones among `E` and `S \ E`. -/
def eventPartition (E : Set S) : Setoid S := Setoid.comap (· ∈ E) ⊥

/-- Definition 46: `A` observes the event `E` with respect to `W` (in `F`) — `A ⊥^F X_E`
and `A ⊥^F W | S \ E`.

Paper node: Definition 46 (§7.3). -/
def Observes (A W : Setoid S) (E : Set S) : Prop :=
  F.Orthogonal A (eventPartition E) ∧ F.OrthogonalGivenSet A W Eᶜ

/-- Definition 47: `A` observes the partition `X` with respect to `W` (in `F`) — `A ⊥^F X`,
and `A` splits as the common refinement of a family `Aₓ` (one per block `x ∈ X`) with
`Aₓ ⊥^F W | S \ x` for each.

Paper node: Definition 47 (§7.3). -/
def ObservesPartition (A W X : Setoid S) : Prop :=
  F.Orthogonal A X ∧
    ∃ As : X.classes → Setoid S,
      A = sInf (Set.range As) ∧ ∀ x : X.classes, F.OrthogonalGivenSet (As x) W (↑x)ᶜ

/-! ## §7.3.2 Counterfactability -/

/-- Definition 48: `X` is counterfactable (in `F`) if `X = ⋁_S(h^F(X))`.

Paper node: Definition 48 (§7.3). -/
def Counterfactable (X : Setoid S) : Prop := X = commonRefinement (F.history X)

/-- Definition 49: `X` is counterfactable relative to `W` (in `F`) if
`⋁_S(h^F(X)) ⊥^F W | X`.

Paper node: Definition 49 (§7.3). -/
def CounterfactableRel (X W : Setoid S) : Prop :=
  F.OrthogonalGiven (commonRefinement (F.history X)) W X

/-! ## §7.3.6 Conditional time -/

/-- Definition 50: `X` is before `Y` given `E` (in `F`), `X ≤^F Y | E`, if
`h^F(X | E) ⊆ h^F(Y | E)`.

Paper node: Definition 50 (§7.3). -/
def BeforeGivenSet (X Y : Setoid S) (E : Set S) : Prop :=
  F.historySub ((ofSetoid X).restrict E) ⊆ F.historySub ((ofSetoid Y).restrict E)

end FactoredSet

end FiniteFactoredSets
