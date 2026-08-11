import Mathlib.CategoryTheory.Opposites

/-!
# Cartesian frames, morphisms, and the category `Chu W`

This file opens §2.1 of Garrabrant, Herrmann, and Lopez-Wild, *Cartesian Frames*
(arXiv:2109.10996): frames over a set of possible worlds, frame morphisms with their
adjointness condition, the category `Chu(W)` they form, and the dual (transpose)
functor of Definition 9.

The paper works with sets without cardinality restriction; here a set is a Lean type
and all three carriers share one universe (`dd:universe`).  The paper states its
Definitions 9–11 as functors, so the `Category` instance is main-body specification,
not an appendix nicety, and lives here (`dd:cat`).  Both tags are defined in
`CartesianFrames.lean`.
-/

universe u

namespace CartesianFrames

open CategoryTheory

/-- A Cartesian frame over possible worlds `W`: agent choices, environment states,
and the world jointly selected by one of each.

Paper node: Definition 1 (§2.1). -/
@[ext]
structure Frame (W : Type u) where
  Agent : Type u
  Env : Type u
  outcome : Agent → Env → W

namespace Frame

variable {W : Type u}

/-- The possible worlds realized by some agent choice and environment state.  This is
the `Image(C)` notation introduced immediately after Definition 1.

Paper node: Definition 1 (§2.1). -/
def image (C : Frame W) : Set W :=
  {w | ∃ a e, C.outcome a e = w}

/-- A morphism of Cartesian frames: covariant on agents, contravariant on
environments, and `adjoint` is the paper's adjointness condition.

Paper node: Definition 2 (§2.1). -/
@[ext]
structure Hom (C D : Frame W) where
  agent : C.Agent → D.Agent
  env : D.Env → C.Env
  adjoint : ∀ a e, C.outcome a (env e) = D.outcome (agent a) e

/-- The identity frame morphism. -/
protected def Hom.id (C : Frame W) : Hom C C where
  agent := _root_.id
  env := _root_.id
  adjoint := fun _ _ => rfl

/-- Composition of frame morphisms.  The environment maps compose in the reverse
order, exactly as in Definition 2.

Paper node: Definition 2 (§2.1). -/
def Hom.comp {C D E : Frame W} (g : Hom D E) (f : Hom C D) : Hom C E where
  agent := g.agent ∘ f.agent
  env := f.env ∘ g.env
  adjoint := fun a e => (f.adjoint a (g.env e)).trans (g.adjoint (f.agent a) e)

/-- Frames over `W` with Definition 2's morphisms form the category the paper calls
`Chu(W)`; the category axioms are the ones checked in Appendix B (`dd:cat`).

Paper node: Definition 2 (§2.1). -/
instance : LargeCategory (Frame W) where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] lemma id_agent (C : Frame W) : Hom.agent (𝟙 C) = _root_.id := rfl

@[simp] lemma id_env (C : Frame W) : Hom.env (𝟙 C) = _root_.id := rfl

@[simp] lemma comp_agent {C D E : Frame W} (f : C ⟶ D) (g : D ⟶ E) :
    (f ≫ g).agent = g.agent ∘ f.agent := rfl

@[simp] lemma comp_env {C D E : Frame W} (f : C ⟶ D) (g : D ⟶ E) :
    (f ≫ g).env = f.env ∘ g.env := rfl

/-- The dual (matrix transpose) of a frame: agent and environment swap roles.  This
is Definition 9's action on objects.

Paper node: Definition 9 (§2.2). -/
def dual (C : Frame W) : Frame W where
  Agent := C.Env
  Env := C.Agent
  outcome := fun e a => C.outcome a e

/-- The paper's `(C*)* = C`, which here holds definitionally. -/
@[simp] lemma dual_dual (C : Frame W) : C.dual.dual = C := rfl

/-- The dual of a morphism: the two component maps swap roles.  This is
Definition 9's action on arrows.

Paper node: Definition 9 (§2.2). -/
def Hom.dual {C D : Frame W} (f : C ⟶ D) : D.dual ⟶ C.dual where
  agent := f.env
  env := f.agent
  adjoint := fun e a => (f.adjoint a e).symm

@[simp] lemma Hom.dual_agent {C D : Frame W} (f : C ⟶ D) : f.dual.agent = f.env := rfl

@[simp] lemma Hom.dual_env {C D : Frame W} (f : C ⟶ D) : f.dual.env = f.agent := rfl

@[simp] lemma Hom.dual_dual {C D : Frame W} (f : C ⟶ D) : f.dual.dual = f := rfl

/-- Definition 9's transpose functor `-* : Chu(W) ⥤ Chu(W)ᵒᵖ`.  Appendix B's
Claim 46 upgrades it to an equivalence of categories.

Paper node: Definition 9 (§2.2). -/
def dualFunctor (W : Type u) : Frame W ⥤ (Frame W)ᵒᵖ where
  obj C := Opposite.op C.dual
  map f := (Hom.dual f).op
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma dualFunctor_obj (C : Frame W) :
    (dualFunctor W).obj C = Opposite.op C.dual := rfl

@[simp] lemma dualFunctor_map {C D : Frame W} (f : C ⟶ D) :
    (dualFunctor W).map f = (Hom.dual f).op := rfl

section RegressionExamples

/- Client-side exercises of the endpoints above (endpoint-usability rule): the
category structure composes, the transpose functor acts on arrows, and duality is
an involution on both layers. -/

example {C D E : Frame W} (f : C ⟶ D) (g : D ⟶ E) (a : C.Agent) (e : E.Env) :
    C.outcome a ((f ≫ g).env e) = E.outcome ((f ≫ g).agent a) e :=
  (f ≫ g).adjoint a e

example {C D : Frame W} (f : C ⟶ D) : (𝟙 C ≫ f ≫ 𝟙 D).dual = f.dual := by simp

example {C D : Frame W} (f : C ⟶ D) :
    (dualFunctor W).map (𝟙 C ≫ f) = ((dualFunctor W).map f : _) := by simp

example (C : Frame W) (w : W) (h : w ∈ C.image) : ∃ a e, C.outcome a e = w := h

end RegressionExamples

end Frame

end CartesianFrames
