import CartesianFrames.Biextensional

/-!
# Coarse and refined worlds

§2.3 of the paper: moving frames between levels of description.  Definition 10
turns a function of possible worlds `p : W → V` into a functor
`Chu(W) ⥤ Chu(V)`; Definition 11 turns a frame `C` over `W` into a "currying"
functor `Chu(Agent C) ⥤ Chu(W)`, in which the environment supplies both a state of
`C`'s environment and a state of the argument frame's environment.

Definition 10's TeX display names the image frame's carriers `B` and `F`, but the
functor leaves the agent and environment carriers unchanged — only outcomes are
mapped through `p` (see `KNOWLEDGE.md`, pitfalls).
-/

universe u

namespace CartesianFrames

namespace Frame

open CategoryTheory

variable {W V : Type u}

/-- Definition 10's functor `p° : Chu(W) ⥤ Chu(V)` induced by a map of possible
worlds `p : W → V`: outcomes are pushed through `p`; carriers and morphisms are
unchanged.

Paper node: Definition 10 (§2.3). -/
def mapWorlds (p : W → V) : Frame W ⥤ Frame V where
  obj C :=
    { Agent := C.Agent
      Env := C.Env
      outcome := fun a e => p (C.outcome a e) }
  map f :=
    { agent := f.agent
      env := f.env
      adjoint := fun a e => congrArg p (f.adjoint a e) }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma mapWorlds_obj_outcome (p : W → V) (C : Frame W)
    (a : C.Agent) (e : C.Env) :
    ((mapWorlds p).obj C).outcome a e = p (C.outcome a e) := rfl

@[simp] lemma mapWorlds_map_agent (p : W → V) {C D : Frame W} (f : C ⟶ D) :
    ((mapWorlds p).map f).agent = f.agent := rfl

@[simp] lemma mapWorlds_map_env (p : W → V) {C D : Frame W} (f : C ⟶ D) :
    ((mapWorlds p).map f).env = f.env := rfl

/-- `p°` sends homotopic morphisms to homotopic morphisms: the mixed-pair
adjointness condition is preserved by pushing outcomes through `p`. -/
lemma Homotopic.mapWorlds (p : W → V) {C D : Frame W} {f g : C ⟶ D}
    (h : Homotopic f g) :
    Homotopic ((Frame.mapWorlds p).map f) ((Frame.mapWorlds p).map g) :=
  fun a e => congrArg p (h a e)

/-- `p°` preserves homotopy equivalence. -/
lemma HomotopyEquiv.mapWorlds (p : W → V) {C D : Frame W}
    (h : HomotopyEquiv C D) :
    HomotopyEquiv ((Frame.mapWorlds p).obj C) ((Frame.mapWorlds p).obj D) := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := h
  exact ⟨(Frame.mapWorlds p).map φ, (Frame.mapWorlds p).map ψ,
    by simpa [← Functor.map_comp] using hφψ.mapWorlds p,
    by simpa [← Functor.map_comp] using hψφ.mapWorlds p⟩

/-- `p°` preserves biextensional equivalence — the footnote to Definition 10.

Paper node: Definition 10 (§2.3). -/
lemma BiextEquiv.mapWorlds (p : W → V) {C D : Frame W} (h : C ≃ᵇ D) :
    (Frame.mapWorlds p).obj C ≃ᵇ (Frame.mapWorlds p).obj D :=
  biextEquiv_iff_homotopyEquiv.mpr
    ((biextEquiv_iff_homotopyEquiv.mp h).mapWorlds p)

/-- Definition 11's currying functor `C° : Chu(Agent C) ⥤ Chu(W)` attached to a
frame `C` over `W`: on a frame `Z` over `C`'s agent, the agent carrier is kept and
the environment carrier becomes `Env Z × Env C`, with outcome
`(C's outcome of (Z's outcome)) applied to the second component`.  On morphisms the
environment map acts on the first component only.

Paper node: Definition 11 (§2.3). -/
def curry (C : Frame W) : Frame C.Agent ⥤ Frame W where
  obj Z :=
    { Agent := Z.Agent
      Env := Z.Env × C.Env
      outcome := fun b fe => C.outcome (Z.outcome b fe.1) fe.2 }
  map g :=
    { agent := g.agent
      env := fun fe => (g.env fe.1, fe.2)
      adjoint := fun b fe => congrArg (C.outcome · fe.2) (g.adjoint b fe.1) }
  map_id _ := rfl
  map_comp _ _ := rfl

lemma curry_obj_agent (C : Frame W) (Z : Frame C.Agent) :
    ((C.curry).obj Z).Agent = Z.Agent := rfl

lemma curry_obj_env (C : Frame W) (Z : Frame C.Agent) :
    ((C.curry).obj Z).Env = (Z.Env × C.Env) := rfl

@[simp] lemma curry_obj_outcome (C : Frame W) (Z : Frame C.Agent)
    (b : Z.Agent) (f : Z.Env) (e : C.Env) :
    ((C.curry).obj Z).outcome b (f, e) = C.outcome (Z.outcome b f) e := rfl

/-- `C°` sends homotopic morphisms to homotopic morphisms. -/
lemma Homotopic.curryMap (C : Frame W) {Z₀ Z₁ : Frame C.Agent} {g g' : Z₀ ⟶ Z₁}
    (h : Homotopic g g') :
    Homotopic (C.curry.map g) (C.curry.map g') :=
  fun b p => congrArg (C.outcome · p.2) (h b p.1)

/-- `C°` preserves homotopy equivalence. -/
lemma HomotopyEquiv.curryObj (C : Frame W) {Z₀ Z₁ : Frame C.Agent}
    (h : HomotopyEquiv Z₀ Z₁) :
    HomotopyEquiv (C.curry.obj Z₀) (C.curry.obj Z₁) := by
  obtain ⟨φ, ψ, hφψ, hψφ⟩ := h
  exact ⟨C.curry.map φ, C.curry.map ψ,
    by simpa [← Functor.map_comp] using hφψ.curryMap C,
    by simpa [← Functor.map_comp] using hψφ.curryMap C⟩

/-- `C°` preserves biextensional equivalence — used silently by the paper's proof
of Claim 42 when replacing `M` by `⊥_{Image M}` under `D°`. -/
lemma BiextEquiv.curryObj (C : Frame W) {Z₀ Z₁ : Frame C.Agent} (h : Z₀ ≃ᵇ Z₁) :
    C.curry.obj Z₀ ≃ᵇ C.curry.obj Z₁ :=
  biextEquiv_iff_homotopyEquiv.mpr
    ((biextEquiv_iff_homotopyEquiv.mp h).curryObj C)

section RegressionExamples

/- Client-side exercises of the endpoints above (endpoint-usability rule). -/

example (p : W → V) {C D : Frame W} (i : C ≅ D) :
    (mapWorlds p).obj C ≃ᵇ (mapWorlds p).obj D :=
  BiextEquiv.mapWorlds p (biextEquiv_of_nonempty_iso ⟨i⟩)

example (p : W → V) {C D E : Frame W} (f : C ⟶ D) (g : D ⟶ E) :
    (mapWorlds p).map (f ≫ g) = (mapWorlds p).map f ≫ (mapWorlds p).map g :=
  Functor.map_comp _ _ _

example (C : Frame W) {Z₀ Z₁ : Frame C.Agent} (g : Z₀ ⟶ Z₁)
    (b : Z₀.Agent) (f : Z₁.Env) (e : C.Env) :
    ((C.curry).obj Z₀).outcome b ((C.curry.map g).env (f, e)) =
      ((C.curry).obj Z₁).outcome ((C.curry.map g).agent b) (f, e) :=
  (C.curry.map g).adjoint b (f, e)

end RegressionExamples

end Frame

end CartesianFrames
