import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

/-!
# Cartesian frames and their structural operations

This file begins §2 of Garrabrant, Herrmann, and Lopez-Wild, *Cartesian Frames*.
It formalizes the paper's basic frame and morphism calculus together with the
object-level operations needed by the later account of subagency.

The paper works with sets without cardinality restrictions.  Here a set is represented
by a Lean type.  See `dd:universe` in `CartesianFrames.lean` for the sole universe
convention in this initial layer.
-/

universe u

namespace CartesianFrames

/-- A Cartesian frame over possible worlds `W`: agent choices, environment states,
and the world jointly selected by one of each.

Paper node: Definition 1 (§2.1). -/
@[ext]
structure Frame (W : Type u) where
  Agent : Type u
  Env : Type u
  outcome : Agent → Env → W

namespace Frame

variable {W V : Type u}

/-- The possible worlds realized by some agent choice and environment state.  This is
the `Image(C)` notation introduced immediately after Definition 1.

Paper node: Definition 1 (§2.1). -/
def image (C : Frame W) : Set W :=
  {w | ∃ a e, C.outcome a e = w}

/-- A morphism of Cartesian frames.  Its environment component is contravariant, and
`adjoint` is the paper's adjointness condition.

Paper node: Definition 2 (§2.1). -/
structure Hom (C D : Frame W) where
  agent : C.Agent → D.Agent
  env : D.Env → C.Env
  adjoint : ∀ a e, C.outcome a (env e) = D.outcome (agent a) e

namespace Hom

variable {C D F : Frame W}

/-- The identity frame morphism. -/
def id (C : Frame W) : Hom C C where
  agent := _root_.id
  env := _root_.id
  adjoint := by simp

/-- Composition of frame morphisms.  The environment maps compose in the reverse
order, exactly as in Definition 2.

Paper node: Definition 2 (§2.1). -/
def comp (g : Hom D F) (f : Hom C D) : Hom C F where
  agent := g.agent ∘ f.agent
  env := f.env ∘ g.env
  adjoint := by
    intro a e
    change C.outcome a (f.env (g.env e)) = F.outcome (g.agent (f.agent a)) e
    rw [f.adjoint, g.adjoint]

@[ext]
lemma ext {f g : Hom C D} (ha : f.agent = g.agent) (he : f.env = g.env) : f = g := by
  cases f
  cases g
  simp_all

@[simp] lemma id_agent (C : Frame W) : (id C).agent = _root_.id := rfl

@[simp] lemma id_env (C : Frame W) : (id C).env = _root_.id := rfl

@[simp] lemma comp_agent (g : Hom D F) (f : Hom C D) :
    (comp g f).agent = g.agent ∘ f.agent := rfl

@[simp] lemma comp_env (g : Hom D F) (f : Hom C D) :
    (comp g f).env = f.env ∘ g.env := rfl

@[simp] lemma id_comp (f : Hom C D) : comp (id D) f = f := by
  ext <;> rfl

@[simp] lemma comp_id (f : Hom C D) : comp f (id C) = f := by
  ext <;> rfl

lemma comp_assoc {G : Frame W} (h : Hom F G) (g : Hom D F) (f : Hom C D) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> rfl

end Hom

/-- The paper's notion of frame isomorphism: a morphism whose two component functions
are bijections.

Paper node: Definition 3 (§2.2). -/
def Isomorphic (C D : Frame W) : Prop :=
  ∃ f : Hom C D, Function.Bijective f.agent ∧ Function.Bijective f.env

@[inherit_doc] infix:50 " ≅ᶜ " => Isomorphic

lemma isomorphic_refl (C : Frame W) : C ≅ᶜ C := by
  exact ⟨Hom.id C, Function.bijective_id, Function.bijective_id⟩

/-- A frame is biextensional when equal outcome rows determine equal agent choices and
equal outcome columns determine equal environment states.

Paper node: Definition 4 (§2.2). -/
def Biextensional (C : Frame W) : Prop :=
  (∀ a₀ a₁, (∀ e, C.outcome a₀ e = C.outcome a₁ e) → a₀ = a₁) ∧
  (∀ e₀ e₁, (∀ a, C.outcome a e₀ = C.outcome a e₁) → e₀ = e₁)

/-- Transpose a frame, exchanging the roles of agent and environment.

Paper node: Definition 9 (§2.2). -/
def dual (C : Frame W) : Frame W where
  Agent := C.Env
  Env := C.Agent
  outcome e a := C.outcome a e

@[simp] lemma dual_dual (C : Frame W) : C.dual.dual = C := by
  cases C
  rfl

/-- Apply a map of possible worlds pointwise to a frame.

Paper node: Definition 10 (§2.3). -/
def mapWorlds (p : W → V) (C : Frame W) : Frame V where
  Agent := C.Agent
  Env := C.Env
  outcome a e := p (C.outcome a e)

/-- A frame whose possible worlds are the agent choices of `D` can be curried into a
frame over `W`; its environment remembers both environment components.

Paper node: Definition 11 (§2.3). -/
def curry (D : Frame W) (M : Frame D.Agent) : Frame W where
  Agent := M.Agent
  Env := M.Env × D.Env
  outcome b fe := D.outcome (M.outcome b fe.1) fe.2

/-- The frame `⊥_S`: the agent freely selects an element of `S`, while the environment
has exactly one state.

Paper node: Definition 12 (§2.4). -/
def bottom (S : Set W) : Frame W where
  Agent := S
  Env := PUnit
  outcome s _ := s.1

end Frame

end CartesianFrames
