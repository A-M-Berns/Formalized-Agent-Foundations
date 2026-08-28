import Mathlib.Data.Set.Basic

/-!
# The Decomposition Theorem for Cartesian frames

This challenge states Theorem 24 of Scott Garrabrant, Daniel Herrmann and Rob
Lopez-Wild, *Cartesian Frames* (arXiv:2109.10996v1) — the paper's Decomposition
Theorem, which factors the subagent relation into a multiplicative step followed by an
additive one.

## What the theorem says

A **Cartesian frame** over a set `W` of possible worlds is a pair of sets together with
a map into `W`: the agent's available choices, the environment's available states, and
the world that results when one of each is selected. The paper's central relation is
**subagency**, `C₀ ◁ C₁`, read "`C₀` is a subagent of `C₁`" — informally, `C₀` is an
agent that `C₁` could be composed of, or delegate to.

The paper then splits subagency into two special cases. `C₀ ◁ₓ C₁` (*multiplicative*)
holds when `C₀` is one of several agents acting simultaneously, the others having been
absorbed into `C₀`'s environment. `C₀ ◁₊ C₁` (*additive*) holds when `C₀` is `C₁`
restricted to a subset of its choices — the same agent with fewer options. Theorem 24
says these two generate the whole relation:

> `C₀ ◁ C₁` if and only if there is a frame `C₂` with `C₀ ◁ₓ C₂` and `C₂ ◁₊ C₁`.

That is: every way of being a subagent factors as *take a subset of the choices*, then
*act alongside others*, in that order and with nothing left over.

All three relations are stated up to **biextensional equivalence** (Definition 7): two
frames are identified when their *collapses* — the results of deleting duplicate rows
and duplicate columns — are isomorphic. This matters, because a frame that offers the
same agent choice twice under different names should not count as a different agent.

## What a reader should check

Everything below is defined from scratch over Lean core and Mathlib, so the statement
can be audited without trusting any development. The definitions are, in order:
`Frame` (Definition 1), `Hom` with its identity and composition (Definition 2),
frame isomorphism, the two relations `∼` of Definition 5 and the collapse `Ĉ` of
Definition 6, biextensional equivalence (Definition 7), the frame `⊥` (Definition 12),
subagency (Definition 13), and the additive and multiplicative relations
(Definitions 18 and 19).

Two points of care, both places where a reader should confirm nothing has been
weakened:

* Subagency is stated in the paper's **primary** categorical form (Definition 13):
  every morphism from `C` to `⊥` factors through `D`. The paper proves this equivalent
  to a currying form (Definition 14) and a covering form (Definition 50); those are
  *not* used here, so no equivalence is being assumed.
* The additive and multiplicative relations are the paper's Definitions 18 and 19 —
  the direct forms in terms of a shared outcome function, not the currying variants of
  Definitions 20 and 21.

The quantifier `∃ C₂` in the conclusion ranges over frames in the same universe as
`C₀` and `C₁`; no cardinality restriction is imposed anywhere, matching the paper,
which works with arbitrary sets.

## Provenance

Formalized by Anson Berns from the arXiv v1 text. The proof supplied in the companion
Solution module is a transport of the development in the Formalized Agent Foundations
repository, which formalizes all sixty numbered nodes of this paper; the accompanying
`formalization.yaml` records the details.
-/

universe u

namespace Palomar.CartesianFrames

/-- A **Cartesian frame** over possible worlds `W` (Definition 1): a set of agent
choices, a set of environment states, and the world jointly selected by one of each.

The paper presents a frame as a matrix whose rows are indexed by agent choices, whose
columns are indexed by environment states, and whose entries are worlds. -/
@[ext]
structure Frame (W : Type u) where
  /-- The agent's available choices — the rows of the paper's matrix. -/
  Agent : Type u
  /-- The environment's available states — the columns of the paper's matrix. -/
  Env : Type u
  /-- The world selected by a given agent choice and environment state. -/
  outcome : Agent → Env → W

namespace Frame

variable {W : Type u}

/-- A **morphism of Cartesian frames** (Definition 2): covariant on agent choices,
contravariant on environment states, subject to the paper's adjointness condition.

Reading `adjoint`: pushing an agent choice forward along `agent` and pulling an
environment state back along `env` select the same world. -/
@[ext]
structure Hom (C D : Frame W) where
  /-- The covariant component, on agent choices. -/
  agent : C.Agent → D.Agent
  /-- The contravariant component, on environment states. -/
  env : D.Env → C.Env
  /-- The adjointness condition of Definition 2. -/
  adjoint : ∀ a e, C.outcome a (env e) = D.outcome (agent a) e

/-- The identity morphism on a frame. -/
protected def Hom.id (C : Frame W) : Hom C C where
  agent := id
  env := id
  adjoint _ _ := rfl

/-- Composition of frame morphisms (Definition 2). The environment components compose
in the reverse order, as they must, being contravariant. -/
def Hom.comp {C D E : Frame W} (g : Hom D E) (f : Hom C D) : Hom C E where
  agent := g.agent ∘ f.agent
  env := f.env ∘ g.env
  adjoint a e := (f.adjoint a (g.env e)).trans (g.adjoint (f.agent a) e)

/-- An **isomorphism of Cartesian frames**: morphisms both ways whose composites are
the identities. This is isomorphism in the category the paper calls `Chu(W)`. -/
structure Iso (C D : Frame W) where
  /-- The forward morphism. -/
  hom : Hom C D
  /-- The backward morphism. -/
  inv : Hom D C
  /-- The backward morphism is a left inverse. -/
  hom_inv : Hom.comp inv hom = Hom.id C
  /-- The backward morphism is a right inverse. -/
  inv_hom : Hom.comp hom inv = Hom.id D

/-- Definition 5's relation `∼` on agent choices: two choices are related when they
select the same world against every environment state — that is, when they index
identical rows of the paper's matrix. -/
def agentSetoid (C : Frame W) : Setoid C.Agent where
  r a₀ a₁ := ∀ e, C.outcome a₀ e = C.outcome a₁ e
  iseqv := ⟨fun _ _ => rfl, fun h e => (h e).symm, fun h₀ h₁ e => (h₀ e).trans (h₁ e)⟩

/-- Definition 5's relation `∼` on environment states: two states are related when
they select the same world against every agent choice — identical columns. -/
def envSetoid (C : Frame W) : Setoid C.Env where
  r e₀ e₁ := ∀ a, C.outcome a e₀ = C.outcome a e₁
  iseqv := ⟨fun _ _ => rfl, fun h a => (h a).symm, fun h₀ h₁ a => (h₀ a).trans (h₁ a)⟩

/-- The **biextensional collapse** `Ĉ` (Definition 6): quotient both carriers by
Definition 5's relations. The outcome map descends because related choices and states
were, by definition, indistinguishable. -/
def collapse (C : Frame W) : Frame W where
  Agent := Quotient C.agentSetoid
  Env := Quotient C.envSetoid
  outcome := Quotient.lift₂ C.outcome fun _ e₀ a₁ _ ha he => (ha e₀).trans (he a₁)

/-- **Biextensional equivalence** (Definition 7): the collapses are isomorphic.

This is the paper's working notion of sameness for frames. Two frames are
biextensionally equivalent exactly when they differ only by duplicated rows and
columns. -/
def BiextEquiv (C D : Frame W) : Prop := Nonempty (Iso C.collapse D.collapse)

/-- The frame `⊥` of Definition 12: the agent selects a world outright and the
environment has a single state. Morphisms into `⊥` are what subagency quantifies
over. -/
def bot (W : Type u) : Frame W where
  Agent := W
  Env := PUnit
  outcome w _ := w

/-- **Subagency** (Definition 13), the paper's primary definition: `C` is a subagent
of `D` when every morphism from `C` to `⊥` factors through `D`.

This is the categorical form. The paper's equivalent currying (Definition 14) and
covering (Definition 50) forms are deliberately not used here. -/
def Subagent (C D : Frame W) : Prop :=
  ∀ φ : Hom C (bot W), ∃ (φ₀ : Hom C D) (φ₁ : Hom D (bot W)), φ = Hom.comp φ₁ φ₀

/-- The **additive** subagent relation (Definition 18): `C` is `D` with its agent
choices cut down to a subset, the environment untouched.

Concretely: there is an outcome function `f : Y → Z → W` presenting `D`, and a subset
`X ⊆ Y` presenting `C`, both up to biextensional equivalence. -/
def AddSubagent (C D : Frame W) : Prop :=
  ∃ (Y Z : Type u) (X : Set Y) (f : Y → Z → W),
    BiextEquiv C { Agent := X, Env := Z, outcome := fun x z => f x.val z } ∧
    BiextEquiv D { Agent := Y, Env := Z, outcome := f }

/-- The **multiplicative** subagent relation (Definition 19): `C` is one factor of a
joint agent, the other factor having moved into `C`'s environment.

Concretely: there is a three-place outcome function `f : X → Y → Z → W` whose middle
argument sits on `C`'s environment side and on `D`'s agent side, presenting both frames
up to biextensional equivalence. -/
def MultSubagent (C D : Frame W) : Prop :=
  ∃ (X Y Z : Type u) (f : X → Y → Z → W),
    BiextEquiv C { Agent := X, Env := Y × Z, outcome := fun x p => f x p.1 p.2 } ∧
    BiextEquiv D { Agent := X × Y, Env := Z, outcome := fun p z => f p.1 p.2 z }

/-- **The Decomposition Theorem** (Theorem 24). Subagency is exactly a multiplicative
step followed by an additive one: `C₀ ◁ C₁` holds if and only if some frame `C₂` sits
between them with `C₀ ◁ₓ C₂` and `C₂ ◁₊ C₁`.

The forward direction is the substantive one; the reverse says only that both special
relations imply subagency and that subagency composes. -/
theorem subagent_iff_exists_multSubagent_addSubagent {C₀ C₁ : Frame W} :
    Subagent C₀ C₁ ↔ ∃ C₂, MultSubagent C₀ C₂ ∧ AddSubagent C₂ C₁ := by
  sorry

end Frame

end Palomar.CartesianFrames
