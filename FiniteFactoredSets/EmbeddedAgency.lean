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

  Read that as a statement about *well-formedness*, not about meaning.  Definitions 46-50
  all begin "let `F = (S, B)` be a finite factored set", and past finite **dimension** the
  vocabulary they are built from stops meaning what the paper means by it: `history X` is
  the intersection of all generating subsets of `B`, and Proposition 12 — that this
  intersection itself generates — is exactly what fails there (`History.lean`'s module doc
  gives the mechanism).  So on an infinite-dimensional `F` these five are well-formed and
  say something else: `Counterfactable X` degenerates to `X = ⊤` wherever `history X = ∅`,
  and an `Observes`/`BeforeGivenSet` claim is not one Definitions 46-50 speak to.  The same
  caveat is carried at `Orthogonality.lean` and `History.lean` for §3.
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

/-! ## §7.3.5 Conditional time -/

/-- Definition 50: `X` is before `Y` given `E` (in `F`), `X ≤^F Y | E`, if
`h^F(X | E) ⊆ h^F(Y | E)`.

Paper node: Definition 50 (§7.3). -/
def BeforeGivenSet (X Y : Setoid S) (E : Set S) : Prop :=
  F.historySub ((ofSetoid X).restrict E) ⊆ F.historySub ((ofSetoid Y).restrict E)

/-! ## Reductions

§7 states no theorem about Definitions 46-50, so what a consumer of this file needs is not
endpoints but *reductions*: the facts that say when one of these five is silently a §3 or
§4 statement.  Four of them are general enough to belong here rather than beside a witness,
and an auditor meeting a §7.3 hypothesis should apply them first. -/

/-- **Definition 48 implies Definition 49, for every `W`.**  A counterfactable `X` *is*
`⋁_S(h^F(X))`, so the screening-off Definition 49 asks for degenerates to `X ⊥^F W | X`,
which holds for every `W` (`orthogonalGiven_given_self`). -/
lemma counterfactableRel_of_counterfactable [Finite F.B] {X : Setoid S}
    (h : F.Counterfactable X) (W : Setoid S) : F.CounterfactableRel X W := by
  show F.OrthogonalGiven (commonRefinement (F.history X)) W X
  rw [← h]
  exact F.orthogonalGiven_given_self X W

/-- The degenerate corner of Definition 49, recorded so it is not mistaken for content:
*every* partition is counterfactable relative to `Ind_S`, counterfactable or not.  So a
`CounterfactableRel X ⊤` witness certifies nothing about `X`. -/
lemma counterfactableRel_top [Finite F.B] (X : Setoid S) :
    F.CounterfactableRel X (⊤ : Setoid S) :=
  fun z _ => F.orthogonalGivenSet_top_right (commonRefinement (F.history X)) z

/-- **Definition 50 at `E = S` is Definition 19**, since `X|S = X` and `historySub_ofSetoid`
identifies the two histories.  This is the reduction that keeps a conditional-time claim
from being read as new content when its event is everything.  It carries no finiteness: the
identification is definitional, and only Proposition 22's *least*-element sentence needs
`[Finite F.B]`. -/
lemma beforeGivenSet_univ_iff (X Y : Setoid S) :
    F.BeforeGivenSet X Y Set.univ ↔ F.Before X Y := by
  show F.historySub ((ofSetoid X).restrict Set.univ)
      ⊆ F.historySub ((ofSetoid Y).restrict Set.univ) ↔ _
  rw [restrict_univ, restrict_univ, F.historySub_ofSetoid X, F.historySub_ofSetoid Y]
  exact Iff.rfl

/-- The other degenerate corner: given the impossible event, everything is before
everything.  Definition 27 never conditions on `∅` (a block is never empty), but
Definition 50 takes a bare subset, so a client should know. -/
lemma beforeGivenSet_empty [Finite F.B] (X Y : Setoid S) : F.BeforeGivenSet X Y ∅ := by
  show F.historySub ((ofSetoid X).restrict (∅ : Set S)) ⊆ _
  rw [F.historySub_restrict_empty]
  exact Set.empty_subset _

/-- Client's-eye use of the first reduction: a counterfactable partition screens its own
history off from *every* world model at once, so Definition 49 adds nothing on top of
Definition 48. -/
example [Finite F.B] {X : Setoid S} (h : F.Counterfactable X) :
    ∀ W : Setoid S, F.CounterfactableRel X W :=
  F.counterfactableRel_of_counterfactable h

/-- …and of the third: Definition 50 read at `E = S` composes with Proposition 18's
transitivity, so a chain of conditional-time facts at the total event is a chain in `≤^F`. -/
example (X Y : Setoid S) (h : F.BeforeGivenSet X Y Set.univ) :
    F.history X ⊆ F.history Y :=
  (F.beforeGivenSet_univ_iff X Y).1 h

end FactoredSet

end FiniteFactoredSets
