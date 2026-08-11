import CartesianFrames.Worlds

/-!
# Subagents: the categorical relation and its equivalent presentations

§2.4 of the paper through Claim 17, together with the covering definition and the
equivalence chain the paper defers to Appendix B: Definition 12 (`⊥_S`, `⊥`),
Definition 13 (categorical subagent — the primary definition, owning `◁`),
Definition 14 (currying variant), Definition 50 (covering variant), and Claims 15,
16, 17, 51, 52, 53.

Per the settled convention (`KNOWLEDGE.md`), the paper's first-presented definition
owns the plain name: `Subagent` is Definition 13, and the currying and covering
presentations are `SubagentCurry`/`SubagentCovering` with the equivalences proved as
the paper's numbered claims.  Proofs may route through whichever presentation is
convenient; the statement surface is unaffected.

**Paper erratum (Claim 53).** The printed proof's final display verifies only the
*agent* components of `φ_e = φ_e ∘ τ ∘ σ`; the environment components (`e` versus
`σ.env (τ.env e)`) agree only up to duplicate columns, while Definition 13 demands
morphism equality.  The proof of `SubagentCurry.subagent` below instead redirects
the factoring morphism's environment map at the single relevant point — the exact
construction of the paper's commented-out "currying implies covering" proof
(TeX source lines 1334–1377).  The claim itself is true as stated.
-/

universe u

namespace CartesianFrames

namespace Frame

open CategoryTheory

variable {W : Type u}

/-! ## The bottom frames (Definition 12) -/

/-- Definition 12's frame `⊥_S` for `S ⊆ W`: the agent picks a world from `S`
directly; the environment is trivial.

Paper node: Definition 12 (§2.4). -/
def botOf (S : Set W) : Frame W where
  Agent := S
  Env := PUnit
  outcome := fun s _ => s.val

/-- The paper's `⊥`, i.e. `⊥_W`, as a `Bot` instance.  Rendered with agent carrier
`W` itself rather than the subtype `↥(Set.univ)`; `botOfUnivIsoBot` supplies the
canonical isomorphism (`dd:eq-to-iso`).

Paper node: Definition 12 (§2.4). -/
instance instBot : Bot (Frame W) :=
  ⟨{ Agent := W, Env := PUnit, outcome := fun w _ => w }⟩

@[simp] lemma bot_outcome (w : W) (u : (⊥ : Frame W).Env) :
    (⊥ : Frame W).outcome w u = w := rfl

/-- The paper writes `⊥ = ⊥_W`; across the subtype boundary this is the canonical
isomorphism (`dd:eq-to-iso`). -/
def botOfUnivIsoBot : botOf (Set.univ : Set W) ≅ (⊥ : Frame W) where
  hom := { agent := fun s => s.val, env := fun u => u, adjoint := fun _ _ => rfl }
  inv := { agent := fun w => ⟨w, trivial⟩, env := fun u => u, adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Morphisms into `⊥` correspond exactly to environment states — the observation
the paper makes directly after Definition 13 and leans on throughout Appendix B. -/
def homBotEquiv (C : Frame W) : (C ⟶ (⊥ : Frame W)) ≃ C.Env where
  toFun φ := φ.env PUnit.unit
  invFun e :=
    { agent := fun a => C.outcome a e
      env := fun _ => e
      adjoint := fun _ _ => rfl }
  left_inv φ := by
    refine Hom.ext (funext fun a => ?_) (funext fun u => ?_)
    · exact φ.adjoint a PUnit.unit
    · rfl
  right_inv e := rfl

@[simp] lemma homBotEquiv_symm_env (C : Frame W) (e : C.Env) (u : PUnit) :
    ((C.homBotEquiv.symm e : C ⟶ (⊥ : Frame W))).env u = e := rfl

@[simp] lemma homBotEquiv_symm_agent (C : Frame W) (e : C.Env) (a : C.Agent) :
    ((C.homBotEquiv.symm e : C ⟶ (⊥ : Frame W))).agent a = C.outcome a e := rfl

/-! ## Subagent: the categorical definition and its variants -/

variable (C D : Frame W)

/-- Definition 13, the categorical definition of subagent — the primary rendering
of `C ◁ D`: every morphism `C ⟶ ⊥` factors through `D`.

Paper node: Definition 13 (§2.4). -/
def Subagent : Prop :=
  ∀ φ : C ⟶ (⊥ : Frame W), ∃ (φ₀ : C ⟶ D) (φ₁ : D ⟶ (⊥ : Frame W)), φ = φ₀ ≫ φ₁

@[inherit_doc] scoped infixl:50 " ◁ " => Subagent

/-- Definition 14, the currying definition of subagent: `C` is biextensionally
equivalent to `D°(Z)` for some frame `Z` over `D`'s agent.

Paper node: Definition 14 (§2.4). -/
def SubagentCurry : Prop :=
  ∃ Z : Frame D.Agent, C ≃ᵇ D.curry.obj Z

/-- Definition 50, the covering definition of subagent: every environment state of
`C` is hit by the environment component of some morphism `C ⟶ D`.

Paper node: Definition 50 (App. B). -/
def SubagentCovering : Prop :=
  ∀ e : C.Env, ∃ (f : C ⟶ D) (x : D.Env), f.env x = e

variable {C D}

/-! ## The equivalence chain (Claims 51, 52, 53, 15) -/

/-- The covering and categorical definitions of subagent are equivalent.

Paper node: Claim 51 (App. B). -/
theorem subagent_iff_subagentCovering : C ◁ D ↔ SubagentCovering C D := by
  constructor
  · intro h e
    obtain ⟨φ₀, φ₁, hfac⟩ := h (C.homBotEquiv.symm e)
    exact ⟨φ₀, φ₁.env PUnit.unit,
      (congrArg (fun ψ : C ⟶ (⊥ : Frame W) => ψ.env PUnit.unit) hfac).symm⟩
  · intro h φ
    obtain ⟨f, x, hfx⟩ := h (φ.env PUnit.unit)
    refine ⟨f, D.homBotEquiv.symm x, ?_⟩
    refine Hom.ext (funext fun a => ?_) (funext fun u => ?_)
    · calc φ.agent a
          = C.outcome a (φ.env PUnit.unit) := (φ.adjoint a PUnit.unit).symm
        _ = C.outcome a (f.env x) := by rw [hfx]
        _ = D.outcome (f.agent a) x := f.adjoint a x
    · exact hfx.symm

/-- The covering definition of subagent implies the currying definition, via the
frame `Z = (Agent C, hom(C, D), ⋄)` over `D`'s agent, with `a ⋄ f = f.agent a`.

Paper node: Claim 52 (App. B). -/
theorem SubagentCovering.subagentCurry (h : SubagentCovering C D) :
    SubagentCurry C D := by
  classical
  choose cov covEnv covSpec using h
  refine ⟨{ Agent := C.Agent, Env := C ⟶ D, outcome := fun a f => f.agent a }, ?_⟩
  rw [biextEquiv_iff_homotopyEquiv]
  exact ⟨{ agent := fun a => a
           env := fun p => (p.1).env p.2
           adjoint := fun a p => (p.1).adjoint a p.2 },
    { agent := fun a => a
      env := fun e => (cov e, covEnv e)
      adjoint := fun a e =>
        ((cov e).adjoint a (covEnv e)).symm.trans
          (congrArg (C.outcome a) (covSpec e)) },
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- The currying definition of subagent implies the categorical definition.

Paper node: Claim 53 (App. B). -/
theorem SubagentCurry.subagent (h : SubagentCurry C D) : C ◁ D := by
  classical
  obtain ⟨Z, hZ⟩ := h
  rw [biextEquiv_iff_homotopyEquiv] at hZ
  obtain ⟨σ, τ, hστ, hτσ⟩ := hZ
  intro φ
  set e : C.Env := φ.env PUnit.unit with he
  set y : Z.Env := (τ.env e).1 with hy
  set x : D.Env := (τ.env e).2 with hx
  -- The key computation: `C.outcome a e = D.outcome (Z.outcome (σ.agent a) y) x`,
  -- by `τ`'s adjointness at `e` and the homotopy `σ ≫ τ ∼ 𝟙 C`.
  have key : ∀ a : C.Agent,
      C.outcome a e = D.outcome (Z.outcome (σ.agent a) y) x := fun a =>
    (hστ a e).trans (τ.adjoint (σ.agent a) e).symm
  -- The factoring morphism `ξ : C ⟶ D`: agent `a ↦ Z.outcome (σ.agent a) y`, and
  -- `σ`'s environment map with the fibre over `x` redirected to `e` (the paper's
  -- commented-out construction; see the module docstring erratum note).
  refine ⟨{ agent := fun a => Z.outcome (σ.agent a) y
            env := fun f' => if f' = x then e else σ.env (y, f')
            adjoint := fun a f' => ?_ },
    D.homBotEquiv.symm x, ?_⟩
  · by_cases hf : f' = x
    · subst hf
      simpa using key a
    · simpa [hf] using σ.adjoint a (y, f')
  · refine Hom.ext (funext fun a => ?_) (funext fun u => ?_)
    · show φ.agent a = D.outcome (Z.outcome (σ.agent a) y) x
      exact (φ.adjoint a PUnit.unit).symm.trans (key a)
    · show φ.env u = if x = x then e else σ.env (y, x)
      rw [if_pos rfl, he]
      cases u
      rfl

/-- The categorical and currying definitions of subagency are equivalent.

Paper node: Claim 15 (§2.4). -/
theorem subagent_iff_subagentCurry : C ◁ D ↔ SubagentCurry C D :=
  ⟨fun h => (subagent_iff_subagentCovering.mp h).subagentCurry,
    fun h => h.subagent⟩

/-! ## Basic properties (Claims 16, 17) -/

/-- `◁` is transitive.

Paper node: Claim 16 (§2.4). -/
theorem Subagent.trans {C₀ C₁ C₂ : Frame W} (h₀ : C₀ ◁ C₁) (h₁ : C₁ ◁ C₂) :
    C₀ ◁ C₂ := by
  intro φ
  obtain ⟨φ₀, φ₁, hfac₀⟩ := h₀ φ
  obtain ⟨ψ₀, ψ₁, hfac₁⟩ := h₁ φ₁
  exact ⟨φ₀ ≫ ψ₀, ψ₁, by rw [hfac₀, hfac₁, Category.assoc]⟩

/-- Biextensionally equivalent frames are subagents of one another — the second
half of Claim 17.

Paper node: Claim 17 (§2.4). -/
theorem Subagent.of_biextEquiv (h : C ≃ᵇ D) : C ◁ D := by
  refine SubagentCurry.subagent
    ⟨{ Agent := D.Agent, Env := PUnit, outcome := fun b _ => b }, ?_⟩
  refine h.trans (biextEquiv_of_nonempty_iso ⟨?_⟩)
  -- `D ≅ D°(Z)` for `Z = (Agent D, {x}, ⋄)`, inserting the trivial factor.
  exact
    { hom :=
        { agent := fun b => b
          env := fun p => p.2
          adjoint := fun _ _ => rfl }
      inv :=
        { agent := fun b => b
          env := fun e => (PUnit.unit, e)
          adjoint := fun _ _ => rfl }
      hom_inv_id := rfl
      inv_hom_id := rfl }

/-- `◁` is reflexive — the first half of Claim 17.

Paper node: Claim 17 (§2.4). -/
theorem Subagent.refl (C : Frame W) : C ◁ C :=
  Subagent.of_biextEquiv (BiextEquiv.refl C)

section RegressionExamples

/- Client-side exercises of the endpoints above (endpoint-usability rule). -/

example {C D : Frame W} (i : C ≅ D) : C ◁ D :=
  Subagent.of_biextEquiv (biextEquiv_of_nonempty_iso ⟨i⟩)

example {C D : Frame W} (h : C ◁ D) (e : C.Env) :
    ∃ (f : C ⟶ D) (x : D.Env), f.env x = e :=
  subagent_iff_subagentCovering.mp h e

example {C₀ C₁ C₂ : Frame W} (h₀ : SubagentCurry C₀ C₁) (h₁ : C₁ ◁ C₂) :
    C₀ ◁ C₂ :=
  (h₀.subagent).trans h₁

end RegressionExamples

end Frame

end CartesianFrames
