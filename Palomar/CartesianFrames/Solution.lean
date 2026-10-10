import Mathlib.Data.Set.Basic
import CartesianFrames.API

/-!
# Solution — the Decomposition Theorem for Cartesian frames

Discharges the single `sorry` in `Palomar.CartesianFrames.Challenge`.

The definitions in the first half of this file are character-for-character those of the
challenge module, as Comparator requires: the two modules must declare the same
constants with the same types, so the shared vocabulary is repeated here rather than
imported.

The proof is a **transport**. The Formalized Agent Foundations repository
(`CartesianFrames.API`) formalizes all sixty numbered nodes of the paper, including
Theorem 24 as `CartesianFrames.Frame.subagent_iff_exists_multSubagent_addSubagent`. Its
`Frame` structure has exactly the fields of the one declared here, so the two are
carried back and forth by a definitional bijection, and each of the three relations
`◁`, `◁₊`, `◁ₓ` is shown to agree across it. Nothing mathematical happens in the
bridge; the content is upstream.

The bridge is deliberately built out of explicit `Iff` lemmas rather than a blanket
`simp` normalization, so that a reader can check each relation's correspondence in
isolation.
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

/-! ## The bridge to `CartesianFrames`

Everything below is plumbing. `toLib`/`ofLib` are mutually inverse by structure eta,
and every relation above is shown to match its upstream counterpart. -/

open CategoryTheory

/-- Carry a frame to the upstream `CartesianFrames.Frame`. -/
private def toLib (C : Frame W) : _root_.CartesianFrames.Frame W :=
  ⟨C.Agent, C.Env, C.outcome⟩

/-- Carry a frame back from the upstream `CartesianFrames.Frame`. -/
private def ofLib (C : _root_.CartesianFrames.Frame W) : Frame W :=
  ⟨C.Agent, C.Env, C.outcome⟩

@[simp] private lemma toLib_ofLib (C : _root_.CartesianFrames.Frame W) :
    toLib (ofLib C) = C := rfl

@[simp] private lemma ofLib_toLib (C : Frame W) : ofLib (toLib C) = C := rfl

/-- Morphisms correspond: the two `Hom` structures have the same fields. -/
private def homToLib {C D : Frame W} (f : Hom C D) : toLib C ⟶ toLib D :=
  ⟨f.agent, f.env, f.adjoint⟩

/-- The inverse correspondence on morphisms. -/
private def homOfLib {C D : Frame W} (f : toLib C ⟶ toLib D) : Hom C D :=
  ⟨f.agent, f.env, f.adjoint⟩

@[simp] private lemma homOfLib_homToLib {C D : Frame W} (f : Hom C D) :
    homOfLib (homToLib f) = f := rfl

@[simp] private lemma homToLib_homOfLib {C D : Frame W} (f : toLib C ⟶ toLib D) :
    homToLib (homOfLib f) = f := rfl

private lemma homToLib_injective {C D : Frame W} {f g : Hom C D}
    (h : homToLib f = homToLib g) : f = g := by
  have := congrArg homOfLib h; simpa using this

@[simp] private lemma homToLib_id (C : Frame W) :
    homToLib (Hom.id C) = 𝟙 (toLib C) := rfl

@[simp] private lemma homToLib_comp {C D E : Frame W} (g : Hom D E) (f : Hom C D) :
    homToLib (Hom.comp g f) = homToLib f ≫ homToLib g := rfl

/-- Isomorphisms correspond. -/
private def isoToLib {C D : Frame W} (i : Iso C D) : toLib C ≅ toLib D where
  hom := homToLib i.hom
  inv := homToLib i.inv
  hom_inv_id := by rw [← homToLib_comp, i.hom_inv, homToLib_id]
  inv_hom_id := by rw [← homToLib_comp, i.inv_hom, homToLib_id]

/-- The inverse correspondence on isomorphisms. -/
private def isoOfLib {C D : Frame W} (i : toLib C ≅ toLib D) : Iso C D where
  hom := homOfLib i.hom
  inv := homOfLib i.inv
  hom_inv := homToLib_injective (by simp [i.hom_inv_id])
  inv_hom := homToLib_injective (by simp [i.inv_hom_id])

/-- The collapse commutes with the bridge, definitionally. -/
@[simp] private lemma toLib_collapse (C : Frame W) :
    toLib C.collapse = (toLib C).collapse := rfl

/-- `⊥` corresponds to `⊥`, definitionally. -/
@[simp] private lemma toLib_bot : toLib (bot W) = (⊥ : _root_.CartesianFrames.Frame W) :=
  rfl

private lemma biextEquiv_iff {C D : Frame W} :
    BiextEquiv C D ↔ _root_.CartesianFrames.Frame.BiextEquiv (toLib C) (toLib D) := by
  constructor
  · rintro ⟨i⟩; exact ⟨isoToLib i⟩
  · rintro ⟨i⟩; exact ⟨isoOfLib i⟩

private lemma subagent_iff {C D : Frame W} :
    Subagent C D ↔ _root_.CartesianFrames.Frame.Subagent (toLib C) (toLib D) := by
  constructor
  · intro h φ
    obtain ⟨φ₀, φ₁, hφ⟩ := h (homOfLib φ)
    refine ⟨homToLib φ₀, homToLib φ₁, ?_⟩
    show φ = homToLib φ₀ ≫ homToLib φ₁
    rw [← homToLib_comp, ← hφ, homToLib_homOfLib]
  · intro h φ
    obtain ⟨φ₀, φ₁, hφ⟩ := h (homToLib φ)
    refine ⟨homOfLib φ₀, homOfLib φ₁, homToLib_injective ?_⟩
    show homToLib φ = homToLib (Hom.comp (homOfLib φ₁) (homOfLib φ₀))
    rw [homToLib_comp, homToLib_homOfLib, homToLib_homOfLib]
    exact hφ

private lemma addSubagent_iff {C D : Frame W} :
    AddSubagent C D ↔ _root_.CartesianFrames.Frame.AddSubagent (toLib C) (toLib D) := by
  constructor
  · rintro ⟨Y, Z, X, f, h₀, h₁⟩
    exact ⟨Y, Z, X, f, biextEquiv_iff.mp h₀, biextEquiv_iff.mp h₁⟩
  · rintro ⟨Y, Z, X, f, h₀, h₁⟩
    exact ⟨Y, Z, X, f, biextEquiv_iff.mpr h₀, biextEquiv_iff.mpr h₁⟩

private lemma multSubagent_iff {C D : Frame W} :
    MultSubagent C D ↔ _root_.CartesianFrames.Frame.MultSubagent (toLib C) (toLib D) := by
  constructor
  · rintro ⟨X, Y, Z, f, h₀, h₁⟩
    exact ⟨X, Y, Z, f, biextEquiv_iff.mp h₀, biextEquiv_iff.mp h₁⟩
  · rintro ⟨X, Y, Z, f, h₀, h₁⟩
    exact ⟨X, Y, Z, f, biextEquiv_iff.mpr h₀, biextEquiv_iff.mpr h₁⟩

/-- **The Decomposition Theorem** (Theorem 24). Subagency is exactly a multiplicative
step followed by an additive one: `C₀ ◁ C₁` holds if and only if some frame `C₂` sits
between them with `C₀ ◁ₓ C₂` and `C₂ ◁₊ C₁`.

The forward direction is the substantive one; the reverse says only that both special
relations imply subagency and that subagency composes. -/
theorem subagent_iff_exists_multSubagent_addSubagent {C₀ C₁ : Frame W} :
    Subagent C₀ C₁ ↔ ∃ C₂, MultSubagent C₀ C₂ ∧ AddSubagent C₂ C₁ := by
  rw [subagent_iff, _root_.CartesianFrames.Frame.subagent_iff_exists_multSubagent_addSubagent]
  constructor
  · rintro ⟨C₂, hx, ha⟩
    refine ⟨ofLib C₂, ?_, ?_⟩
    · exact multSubagent_iff.mpr (by simpa using hx)
    · exact addSubagent_iff.mpr (by simpa using ha)
  · rintro ⟨C₂, hx, ha⟩
    exact ⟨toLib C₂, multSubagent_iff.mp hx, addSubagent_iff.mp ha⟩

end Frame

end Palomar.CartesianFrames
