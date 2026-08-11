import CartesianFrames.Operations
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The categorical framework (Appendix B)

Appendix B of Garrabrant, Herrmann, and Lopez-Wild, *Cartesian Frames*
(arXiv:2109.10996): the self-duality of `Chu(W)` (Claim 46, together with the two
strict composites behind it), its initial and terminal objects (Definition 47,
Claim 48), the frames `1_S` and `1` (Definition 49), and the three alternative
definitions of subagency the appendix contributes — categorical additive
(Definition 54), categorical multiplicative (Definition 57), and sub-environment
multiplicative (Definition 58) — each tied back to a main-body definition by
Claims 55–56 (additive) and Claims 59–60 (multiplicative).

The category structure itself is not proved here: `dd:cat` puts it in
`CartesianFrames/Basic.lean`, since the paper's main body already states
Definitions 9–11 as functors.  Appendix B's opening proof (composition is
well-defined, associative, and unital) is exactly the content of
`Frame.instChuCategory`, whose laws hold by `rfl`.

`dd:cat` also governs Claim 46.  The paper says `-*` is an *isomorphism* between
`Chu(W)` and `Chu(W)ᵒᵖ`; Mathlib has no strict isomorphism of categories, so the
claim is rendered as an `Equivalence` (`dualEquivalence`, whose unit and counit are
both the identity natural isomorphism) together with the strict involution
`Frame.dual_dual : (C*)* = C`, which holds by `rfl`.  Nothing is lost: the two
composites are *literally* the identity functors
(`dualEquivalence_functor_comp_inverse`, `dualEquivalence_inverse_comp_functor`,
both `rfl`), which is exactly the paper's "compose to the identity in both orders";
only the name of the ambient concept is unavailable in Mathlib.

Definition 47's `0` and `⊤` are given as `Zero`/`Top` instances with the concrete
carriers `PEmpty`/`PUnit`.  The paper notes that `0` and `⊤` are only well defined
up to isomorphism (any singleton will do); Mathlib's `Limits.IsInitial` and
`Limits.IsTerminal` are the honest carriers of that content, and `Limits.IsInitial`
is *data*, so each of Claims 48's two halves is stated as the `Nonempty` of the
corresponding witness type, with the constructive witness available separately as
`zeroIsInitial` / `topIsTerminal`.
-/

universe u

namespace CartesianFrames

namespace Frame

open CategoryTheory

variable {W : Type u}

/-! ## `Chu(W)` is self-dual (Claim 46) -/

/-- The transpose functor packaged as an equivalence `Chu(W) ≌ Chu(W)ᵒᵖ`: the
inverse is the same construction read out of the opposite category, and both the
unit and the counit are the identity natural isomorphism, because `(C*)* = C` and
`(f*)* = f` hold definitionally.  This is the constructive carrier behind
`dualFunctor_isEquivalence`, which states Claim 46 (App. B). -/
def dualEquivalence (W : Type u) : Frame W ≌ (Frame W)ᵒᵖ where
  functor := dualFunctor W
  inverse :=
    { obj := fun C => (Opposite.unop C).dual
      map := fun f => Hom.dual f.unop
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  functor_unitIso_comp := fun _ => rfl

/-- The paper's "`-*` and `-*` compose to the identity in both orders", first
order: strict equality of functors, not merely a natural isomorphism.  Together
with `dualEquivalence_inverse_comp_functor` this is the full content of the
paper's word *isomorphism*; `dd:cat` routes the headline statement through
`Equivalence` only because Mathlib has no type of category isomorphisms to name.

Paper node: Claim 46 (App. B). -/
theorem dualEquivalence_functor_comp_inverse (W : Type u) :
    (dualEquivalence W).functor ⋙ (dualEquivalence W).inverse = 𝟭 (Frame W) := rfl

/-- The other order of `dualEquivalence_functor_comp_inverse`: the composite is
again literally the identity functor.

Paper node: Claim 46 (App. B). -/
theorem dualEquivalence_inverse_comp_functor (W : Type u) :
    (dualEquivalence W).inverse ⋙ (dualEquivalence W).functor = 𝟭 ((Frame W)ᵒᵖ) := rfl

/-- The transpose functor is an equivalence `Chu(W) ≌ Chu(W)ᵒᵖ` — the paper's
"`-*` is an isomorphism of categories", rendered per `dd:cat`: Mathlib has no
strict isomorphism of categories, so the claim is stated as an equivalence,
with the strict involution `(C*)* = C` holding definitionally (`dual_dual`).
The equivalence is not merely essentially surjective and fully faithful: its unit
and counit are the *identity* natural isomorphism, and the two composites are
literally the identity functors (`dualEquivalence_functor_comp_inverse`,
`dualEquivalence_inverse_comp_functor`), so no strength is lost to the rendering.

Paper node: Claim 46 (App. B). -/
theorem dualFunctor_isEquivalence (W : Type u) : (dualFunctor W).IsEquivalence :=
  (dualEquivalence W).isEquivalence_functor

/-! ## The initial and terminal frames (Definition 47, Claim 48) -/

/-- Definition 47's initial frame `0`: empty agent, one environment state.

Paper node: Definition 47 (App. B). -/
instance instZero : Zero (Frame W) :=
  ⟨{ Agent := PEmpty, Env := PUnit, outcome := fun x _ => x.elim }⟩

/-- Definition 47's terminal frame `⊤`: one agent choice, empty environment.

Paper node: Definition 47 (App. B). -/
instance instTop : Top (Frame W) :=
  ⟨{ Agent := PUnit, Env := PEmpty, outcome := fun _ e => e.elim }⟩

/-- The unique morphism out of `0`, witnessing initiality: `PEmpty` is initial and
`PUnit` is terminal in `Type u`, and the adjointness condition is vacuous. -/
private def zeroHom (C : Frame W) : (0 : Frame W) ⟶ C where
  agent a := a.elim
  env _ := PUnit.unit
  adjoint a _ := a.elim

/-- The unique morphism into `⊤`, witnessing terminality. -/
private def topHom (C : Frame W) : C ⟶ (⊤ : Frame W) where
  agent _ := PUnit.unit
  env e := e.elim
  adjoint _ e := e.elim

/-- The constructive witness that `0` is initial in `Chu(W)`, packaged for
`nonempty_isInitial_zero`, which states Claim 48's initial half (App. B). -/
def zeroIsInitial : Limits.IsInitial (0 : Frame W) :=
  Limits.IsInitial.ofUniqueHom zeroHom fun _ _ =>
    Hom.ext (funext fun a => a.elim) (funext fun _ => rfl)

/-- The constructive witness that `⊤` is terminal in `Chu(W)`, packaged for
`nonempty_isTerminal_top`, which states Claim 48's terminal half (App. B). -/
def topIsTerminal : Limits.IsTerminal (⊤ : Frame W) :=
  Limits.IsTerminal.ofUniqueHom topHom fun _ _ =>
    Hom.ext (funext fun _ => rfl) (funext fun e => e.elim)

/-- `0` is initial in `Chu(W)` — Claim 48, initial half.  The witness is
constructive (`IsInitial` is data), so the carrier is a `def`; this `theorem`
asserts the paper's propositional content.

Paper node: Claim 48 (App. B). -/
theorem nonempty_isInitial_zero (W : Type u) :
    Nonempty (Limits.IsInitial (0 : Frame W)) :=
  ⟨zeroIsInitial⟩

/-- `⊤` is terminal in `Chu(W)` — Claim 48, terminal half.

Paper node: Claim 48 (App. B). -/
theorem nonempty_isTerminal_top (W : Type u) :
    Nonempty (Limits.IsTerminal (⊤ : Frame W)) :=
  ⟨topIsTerminal⟩

/-! ## The frames `1_S` and `1` (Definition 49) -/

/-- Definition 49's frame `1_S`: one agent choice, environments the worlds of `S`.
The paper's remark `(⊥_S)* = 1_S` holds definitionally here.

Paper node: Definition 49 (App. B). -/
def oneOf (S : Set W) : Frame W := (botOf S).dual

/-- Definition 49's `1 = 1_W`, rendered like `⊥` with carrier `W` itself
(`dd:eq-to-iso`; `(⊥)* = 1` is definitional).

Paper node: Definition 49 (App. B). -/
instance instOne : One (Frame W) := ⟨(⊥ : Frame W).dual⟩

/-- The paper writes `1 = 1_W`; across the subtype boundary this is the canonical
isomorphism (`dd:eq-to-iso`), the transpose of `botOfUnivIsoBot`.

Paper node: Definition 49 (App. B). -/
def oneOfUnivIsoOne : oneOf (Set.univ : Set W) ≅ (1 : Frame W) where
  hom := { agent := fun a => a, env := fun w => ⟨w, trivial⟩, adjoint := fun _ _ => rfl }
  inv := { agent := fun a => a, env := fun s => s.val, adjoint := fun _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The companion remark to Definition 49, `(1_S)* = ⊥_S`, an instance of
`dual_dual`. -/
@[simp] lemma oneOf_dual (S : Set W) : (oneOf S).dual = botOf S := rfl

/-! ## The categorical definition of additive subagent (Definition 54) -/

/-- Definition 54, the categorical definition of additive subagent: a single
morphism `φ₀ : C ⟶ D` through which every `C ⟶ ⊥` factors up to homotopy.

Paper node: Definition 54 (App. B). -/
def AddSubagentCategorical (C D : Frame W) : Prop :=
  ∃ φ₀ : C ⟶ D, ∀ φ : C ⟶ (⊥ : Frame W),
    ∃ φ₁ : D ⟶ (⊥ : Frame W), Homotopic φ (φ₀ ≫ φ₁)

/-- The inclusion `(X, Z, ⋄) ⟶ (Y, Z, •)` of a restricted-agent frame into its
ambient frame over a shared environment — the paper's `X ↪ Y` inside the proof of
Claim 56 (App. B). -/
private def subsetInclusion {Y Z : Type u} (X : Set Y) (f : Y → Z → W) :
    ({ Agent := X, Env := Z, outcome := fun x z => f x.val z } : Frame W) ⟶
      { Agent := Y, Env := Z, outcome := f } where
  agent x := x.val
  env z := z
  adjoint _ _ := rfl

/-- The categorical definition of additive subagent implies the committing
definition.

Paper node: Claim 55 (App. B). -/
theorem AddSubagentCategorical.addSubagent {C D : Frame W}
    (h : AddSubagentCategorical C D) : C ◁₊ D := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := h
  -- The paper's `X = {g₀(a) : a ∈ A}`, with `(X, F, ⋄)` the restriction of `D`.
  refine ⟨D.Agent, D.Env, Set.range φ₀.agent, D.outcome, ?_, BiextEquiv.refl D⟩
  -- `g₂`: a right inverse to the surjection `A → X`.
  have hsurj : ∀ x : (Set.range φ₀.agent : Set D.Agent), ∃ a : C.Agent,
      φ₀.agent a = x.val := fun x => x.property
  choose g₂ hg₂ using hsurj
  -- `h₂`: morphisms `C ⟶ ⊥` are environment states, and the hypothesis factors each
  -- of them through `φ₀` up to homotopy; `h₂ e` is the resulting `h'_e(j)`.
  have hfac : ∀ e : C.Env, ∃ z : D.Env,
      ∀ a : C.Agent, C.outcome a (φ₀.env z) = C.outcome a e := by
    intro e
    obtain ⟨φ₁, hφ₁⟩ := hφ₀ (C.homBotEquiv.symm e)
    exact ⟨φ₁.env PUnit.unit, fun a => hφ₁ a PUnit.unit⟩
  choose h₂ hh₂ using hfac
  -- The paper's first display: `(g₂, h₂)` satisfies adjointness.
  have key : ∀ (x : (Set.range φ₀.agent : Set D.Agent)) (e : C.Env),
      D.outcome x.val (h₂ e) = C.outcome (g₂ x) e := by
    intro x e
    calc D.outcome x.val (h₂ e)
        = D.outcome (φ₀.agent (g₂ x)) (h₂ e) := by rw [hg₂ x]
      _ = C.outcome (g₂ x) (φ₀.env (h₂ e)) := (φ₀.adjoint (g₂ x) (h₂ e)).symm
      _ = C.outcome (g₂ x) e := hh₂ e (g₂ x)
  refine biextEquiv_iff_homotopyEquiv.mpr
    ⟨{ agent := fun a => ⟨φ₀.agent a, a, rfl⟩
       env := φ₀.env
       adjoint := φ₀.adjoint },
     { agent := g₂
       env := h₂
       adjoint := key },
     ?_, ?_⟩
  · -- The paper's second display: `g₂(g₁(a)) · e = a · e`.
    intro a e
    exact (((φ₀.adjoint a (h₂ e)).symm.trans (hh₂ e a)).symm).trans
      (key ⟨φ₀.agent a, a, rfl⟩ e)
  · -- `g₁ ∘ g₂ = id_X`, so the other composite is the identity on the nose.
    intro x z
    exact congrArg (fun b => D.outcome b z) (hg₂ x).symm

/-- The committing definition of additive subagent implies the categorical
definition.

Paper node: Claim 56 (App. B). -/
theorem AddSubagent.addSubagentCategorical {C D : Frame W}
    (h : C ◁₊ D) : AddSubagentCategorical C D := by
  obtain ⟨Y, Z, X, f, hC, hD⟩ := h
  obtain ⟨α, β, hαβ, hβα⟩ := biextEquiv_iff_homotopyEquiv.mp hC
  obtain ⟨γ, δ, hγδ, hδγ⟩ := biextEquiv_iff_homotopyEquiv.mp hD
  -- The paper's `φ = (g₄, h₄) ∘ (g₀, h₀) ∘ (g₁, h₁)`.
  refine ⟨α ≫ subsetInclusion X f ≫ δ, fun φ => ?_⟩
  -- The paper's `h' = h₃ ∘ h₂ ∘ h`, as the environment state naming `φ₁`.
  refine ⟨D.homBotEquiv.symm (γ.env (β.env (φ.env PUnit.unit))), fun a u => ?_⟩
  -- The paper's final display, read from `⊥` back to `C`.
  calc C.outcome a (α.env (δ.env (γ.env (β.env (φ.env PUnit.unit)))))
      = f (α.agent a).val (δ.env (γ.env (β.env (φ.env PUnit.unit)))) :=
        α.adjoint a (δ.env (γ.env (β.env (φ.env PUnit.unit))))
    _ = f (α.agent a).val (β.env (φ.env PUnit.unit)) :=
        hδγ.symm (α.agent a).val (β.env (φ.env PUnit.unit))
    _ = C.outcome a (α.env (β.env (φ.env PUnit.unit))) :=
        (α.adjoint a (β.env (φ.env PUnit.unit))).symm
    _ = C.outcome a (φ.env PUnit.unit) := hαβ.symm a (φ.env PUnit.unit)
    _ = φ.agent a := φ.adjoint a PUnit.unit

/-- The categorical and committing definitions of additive subagent are
equivalent — Claims 55 and 56 combined. -/
lemma addSubagent_iff_addSubagentCategorical {C D : Frame W} :
    C ◁₊ D ↔ AddSubagentCategorical C D :=
  ⟨AddSubagent.addSubagentCategorical, AddSubagentCategorical.addSubagent⟩

/-! ## The categorical definition of multiplicative subagent (Definition 57) -/

/-- Definition 57, the categorical definition of multiplicative subagent: every
`C ⟶ ⊥` factors through `D` exactly, and every `1 ⟶ D` factors through `C`
exactly.

Paper node: Definition 57 (App. B). -/
def MultSubagentCategorical (C D : Frame W) : Prop :=
  (∀ φ : C ⟶ (⊥ : Frame W), ∃ (φ₀ : C ⟶ D) (φ₁ : D ⟶ (⊥ : Frame W)), φ = φ₀ ≫ φ₁) ∧
  (∀ ψ : (1 : Frame W) ⟶ D, ∃ (ψ₀ : (1 : Frame W) ⟶ C) (ψ₁ : C ⟶ D), ψ = ψ₀ ≫ ψ₁)

section RegressionExamples

/- Client-side exercises of the endpoints above (endpoint-usability rule). -/

example (C : Frame W) : (0 : Frame W) ⟶ C := zeroIsInitial.to C

example (C : Frame W) : C ⟶ (⊤ : Frame W) := topIsTerminal.from C

example {C D : Frame W} (h : AddSubagentCategorical C D) : C ◁ D :=
  h.addSubagent.subagent

example (C : Frame W) : AddSubagentCategorical C C :=
  (AddSubagent.refl C).addSubagentCategorical

example (S : Set W) : (oneOf S).Agent = PUnit := rfl

example (W : Type u) : ((dualFunctor W).obj (0 : Frame W)).unop = (⊤ : Frame W) := rfl

end RegressionExamples

/-! ## The sub-environment definition of multiplicative subagent
(Definition 58, Claims 59–60) -/

variable {C D : Frame W}

/-- Definition 58, the sub-environment definition of multiplicative subagent:
`C` is both a subagent and a sub-environment of `D`.

Paper node: Definition 58 (App. B). -/
def MultSubagentSubEnv (C D : Frame W) : Prop := (C ◁ D) ∧ (C ◁* D)

/-- The categorical definition of multiplicative subagent is equivalent to the
sub-environment definition: the `1 ⟶ D` factorization clause dualizes exactly to
the categorical subagent condition for the duals.

Paper node: Claim 59 (App. B). -/
theorem multSubagentCategorical_iff_multSubagentSubEnv :
    MultSubagentCategorical C D ↔ MultSubagentSubEnv C D := by
  refine and_congr Iff.rfl ?_
  constructor
  · intro h φ
    obtain ⟨ψ₀, ψ₁, hfac⟩ := h φ.dual
    exact ⟨ψ₁.dual, ψ₀.dual, congrArg Hom.dual hfac⟩
  · intro h ψ
    obtain ⟨φ₀, φ₁, hfac⟩ := h ψ.dual
    exact ⟨φ₁.dual, φ₀.dual, congrArg Hom.dual hfac⟩

/-- The sub-environment definition of multiplicative subagent is equivalent to the
externalizing definition.

Paper node: Claim 60 (App. B). -/
theorem multSubagentSubEnv_iff_multSubagent :
    MultSubagentSubEnv C D ↔ C ◁ₓ D := by
  constructor
  · rintro ⟨hsub, hsubenv⟩
    classical
    -- Covering data on both sides: environments of `C` and agents of `D` are both
    -- reached by morphisms `C ⟶ D`, exactly as in the paper's proof.
    choose covHom covEnv covSpec using subagent_iff_subagentCovering.mp hsub
    have hagent : ∀ b : D.Agent, ∃ p : C.Agent × (C ⟶ D), p.2.agent p.1 = b := by
      intro b
      obtain ⟨f, a, hfa⟩ := subagent_iff_subagentCovering.mp hsubenv b
      exact ⟨(a, f.dual), hfa⟩
    choose pick pickSpec using hagent
    refine ⟨C.Agent, C ⟶ D, D.Env, fun a g z => D.outcome (g.agent a) z, ?_, ?_⟩
    · -- `C ≃ᵇ (Agent C, hom(C,D) × Env D, ⋄)`, agents the identity.
      rw [biextEquiv_iff_homotopyEquiv]
      exact ⟨{ agent := fun a => a
               env := fun p => (p.1).env p.2
               adjoint := fun a p => (p.1).adjoint a p.2 },
        { agent := fun a => a
          env := fun e => (covHom e, covEnv e)
          adjoint := fun a e =>
            ((covHom e).adjoint a (covEnv e)).symm.trans
              (congrArg (C.outcome a) (covSpec e)) },
        fun _ _ => rfl, fun _ _ => rfl⟩
    · -- `D ≃ᵇ (Agent C × hom(C,D), Env D, •)`, environments the identity.
      rw [biextEquiv_iff_homotopyEquiv]
      refine ⟨{ agent := pick
                env := fun z => z
                adjoint := fun b z => by
                  show D.outcome b z = D.outcome ((pick b).2.agent (pick b).1) z
                  rw [pickSpec b] },
        { agent := fun p => p.2.agent p.1
          env := fun z => z
          adjoint := fun p z => rfl },
        fun b z => ?_, fun p z => ?_⟩
      · show D.outcome b z = D.outcome ((pick b).2.agent (pick b).1) z
        rw [pickSpec b]
      · exact (congrArg (fun b => D.outcome b z) (pickSpec ((p.2).agent p.1))).symm
  · intro h
    exact ⟨h.subagent, (multSubagent_iff_multSubEnv.mp h).subagent⟩

end Frame

end CartesianFrames

