import CartesianFrames.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Logic.Equiv.Basic

/-!
# Biextensional equivalence and homotopy equivalence

§2.2 of the paper (Definitions 3–7, Claim 8) together with the homotopy machinery of
Appendix A (Definitions 36–37, Claims 38–40).  The two live in one file because the
paper's own proof of Claim 8's second half routes through Appendix A: isomorphism
gives homotopy equivalence (Claim 40 via Definition 37), and homotopy equivalence
coincides with biextensional equivalence (Claim 39).

The paper writes `≃` both for biextensional equivalence (main text) and for homotopy
equivalence (Appendix A), justified by Claim 39.  Here the two keep distinct names —
`BiextEquiv` (with the scoped notation `≃ᵇ`) and `HomotopyEquiv` — and Claim 39 is
the bridge.
-/

universe u

namespace CartesianFrames

namespace Frame

open CategoryTheory

variable {W : Type u} {C D E : Frame W}

/-! ## Isomorphism (Definition 3) -/

/-- Definition 3's isomorphisms: a frame morphism both of whose component maps are
bijections.  `isIsomorphism_iff_isIso` identifies this with categorical
isomorphism, so the paper's relation `C ≅ D` is Mathlib's.

Paper node: Definition 3 (§2.2). -/
def Hom.IsIsomorphism (f : C ⟶ D) : Prop :=
  Function.Bijective f.agent ∧ Function.Bijective f.env

/-- The inverse frame morphism of a morphism with bijective components. -/
noncomputable def Hom.invOfBijective (f : C ⟶ D) (h : f.IsIsomorphism) : D ⟶ C where
  agent := (Equiv.ofBijective f.agent h.1).symm
  env := (Equiv.ofBijective f.env h.2).symm
  adjoint := fun b e => by
    have hb : f.agent ((Equiv.ofBijective f.agent h.1).symm b) = b :=
      (Equiv.ofBijective f.agent h.1).apply_symm_apply b
    have he : f.env ((Equiv.ofBijective f.env h.2).symm e) = e :=
      (Equiv.ofBijective f.env h.2).apply_symm_apply e
    calc D.outcome b ((Equiv.ofBijective f.env h.2).symm e)
        = D.outcome (f.agent ((Equiv.ofBijective f.agent h.1).symm b))
            ((Equiv.ofBijective f.env h.2).symm e) := by rw [hb]
      _ = C.outcome ((Equiv.ofBijective f.agent h.1).symm b)
            (f.env ((Equiv.ofBijective f.env h.2).symm e)) :=
          (f.adjoint _ _).symm
      _ = C.outcome ((Equiv.ofBijective f.agent h.1).symm b) e := by rw [he]

lemma Hom.IsIsomorphism.isIso {f : C ⟶ D} (h : f.IsIsomorphism) : IsIso f := by
  refine ⟨f.invOfBijective h, ?_, ?_⟩
  · refine Hom.ext (funext fun a => ?_) (funext fun e => ?_)
    · exact (Equiv.ofBijective f.agent h.1).symm_apply_apply a
    · exact (Equiv.ofBijective f.env h.2).apply_symm_apply e
  · refine Hom.ext (funext fun b => ?_) (funext fun e => ?_)
    · exact (Equiv.ofBijective f.agent h.1).apply_symm_apply b
    · exact (Equiv.ofBijective f.env h.2).symm_apply_apply e

lemma Hom.isIsomorphism_of_isIso (f : C ⟶ D) [IsIso f] : f.IsIsomorphism := by
  constructor
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨(inv f).agent,
        fun a => congrFun (congrArg Hom.agent (IsIso.hom_inv_id f)) a,
        fun b => congrFun (congrArg Hom.agent (IsIso.inv_hom_id f)) b⟩
  · exact Function.bijective_iff_has_inverse.mpr
      ⟨(inv f).env,
        fun e => congrFun (congrArg Hom.env (IsIso.inv_hom_id f)) e,
        fun e => congrFun (congrArg Hom.env (IsIso.hom_inv_id f)) e⟩

/-- Definition 3's bijective-components condition is categorical isomorphism. -/
lemma Hom.isIsomorphism_iff_isIso {f : C ⟶ D} : f.IsIsomorphism ↔ IsIso f :=
  ⟨Hom.IsIsomorphism.isIso, fun _ => f.isIsomorphism_of_isIso⟩

/-- The paper's relation `C ≅ D` — "there is an isomorphism between `C` and `D`" —
in terms of Definition 3's bijective-components condition.

Paper node: Definition 3 (§2.2). -/
lemma nonempty_iso_iff_exists_isIsomorphism :
    Nonempty (C ≅ D) ↔ ∃ f : C ⟶ D, f.IsIsomorphism := by
  constructor
  · rintro ⟨i⟩
    have : IsIso i.hom := ⟨i.inv, i.hom_inv_id, i.inv_hom_id⟩
    exact ⟨i.hom, i.hom.isIsomorphism_of_isIso⟩
  · rintro ⟨f, hf⟩
    have := hf.isIso
    exact ⟨asIso f⟩

/-! ## Biextensionality and the collapse (Definitions 4–6) -/

/-- A frame is biextensional when it has no duplicate rows or columns: agent choices
with identical outcome rows coincide, and dually for environment states.

Paper node: Definition 4 (§2.2). -/
structure Biextensional (C : Frame W) : Prop where
  agent_ext : ∀ ⦃a₀ a₁ : C.Agent⦄, (∀ e, C.outcome a₀ e = C.outcome a₁ e) → a₀ = a₁
  env_ext : ∀ ⦃e₀ e₁ : C.Env⦄, (∀ a, C.outcome a e₀ = C.outcome a e₁) → e₀ = e₁

/-- Definition 5's relation `∼` on agent choices: identical outcome rows.

Paper node: Definition 5 (§2.2). -/
def agentSetoid (C : Frame W) : Setoid C.Agent where
  r a₀ a₁ := ∀ e, C.outcome a₀ e = C.outcome a₁ e
  iseqv := ⟨fun _ _ => rfl, fun h e => (h e).symm, fun h₀ h₁ e => (h₀ e).trans (h₁ e)⟩

/-- Definition 5's relation `∼` on environment states: identical outcome columns.

Paper node: Definition 5 (§2.2). -/
def envSetoid (C : Frame W) : Setoid C.Env where
  r e₀ e₁ := ∀ a, C.outcome a e₀ = C.outcome a e₁
  iseqv := ⟨fun _ _ => rfl, fun h a => (h a).symm, fun h₀ h₁ a => (h₀ a).trans (h₁ a)⟩

/-- The biextensional collapse `Ĉ`: quotient the agent and environment carriers by
Definition 5's relations; the outcome map descends.

Paper node: Definition 6 (§2.2). -/
def collapse (C : Frame W) : Frame W where
  Agent := Quotient C.agentSetoid
  Env := Quotient C.envSetoid
  outcome := Quotient.lift₂ C.outcome fun _ e₀ a₁ _ ha he => (ha e₀).trans (he a₁)

@[simp] lemma collapse_outcome (a : C.Agent) (e : C.Env) :
    C.collapse.outcome (Quotient.mk C.agentSetoid a) (Quotient.mk C.envSetoid e) =
      C.outcome a e := rfl

/-- The collapse deletes every duplicate row and column: `Ĉ` is biextensional.
Implicit in Definition 6's description of `Ĉ` as "the corresponding biextensional
frame". -/
lemma collapse_biextensional (C : Frame W) : C.collapse.Biextensional := by
  constructor
  · refine fun a₀ a₁ => Quotient.inductionOn₂ a₀ a₁ fun a₀ a₁ h => ?_
    exact Quotient.sound fun e => h (Quotient.mk C.envSetoid e)
  · refine fun e₀ e₁ => Quotient.inductionOn₂ e₀ e₁ fun e₀ e₁ h => ?_
    exact Quotient.sound fun a => h (Quotient.mk C.agentSetoid a)

/-! ## Biextensional equivalence (Definition 7) -/

/-- Biextensional equivalence: the collapses are isomorphic.

Paper node: Definition 7 (§2.2). -/
def BiextEquiv (C D : Frame W) : Prop := Nonempty (C.collapse ≅ D.collapse)

@[inherit_doc] scoped infixl:25 " ≃ᵇ " => BiextEquiv

lemma BiextEquiv.refl (C : Frame W) : C ≃ᵇ C := ⟨Iso.refl _⟩

lemma BiextEquiv.symm (h : C ≃ᵇ D) : D ≃ᵇ C := ⟨h.some.symm⟩

lemma BiextEquiv.trans (h₀ : C ≃ᵇ D) (h₁ : D ≃ᵇ E) : C ≃ᵇ E :=
  ⟨h₀.some.trans h₁.some⟩

/-! ## Homotopy (Definitions 36–37) -/

/-- Two parallel morphisms `(g₀, h₀), (g₁, h₁) : C ⟶ D` are homotopic when the mixed
pair `(g₀, h₁)` is itself a morphism, i.e. satisfies the adjointness condition.

Paper node: Definition 36 (App. A). -/
def Homotopic (f g : C ⟶ D) : Prop :=
  ∀ a e, C.outcome a (g.env e) = D.outcome (f.agent a) e

namespace Homotopic

lemma refl (f : C ⟶ D) : Homotopic f f := f.adjoint

lemma of_eq {f g : C ⟶ D} (h : f = g) : Homotopic f g := h ▸ refl f

/-- Homotopy is symmetric: if the mixed pair `(g₀, h₁)` is a morphism, so is
`(g₁, h₀)`.  The paper's Definition 36 only demands one of the two. -/
lemma symm {f g : C ⟶ D} (h : Homotopic f g) : Homotopic g f :=
  fun a e => (f.adjoint a e).trans ((h a e).symm.trans (g.adjoint a e))

lemma trans {f g k : C ⟶ D} (h₀ : Homotopic f g) (h₁ : Homotopic g k) :
    Homotopic f k :=
  fun a e => (h₁ a e).trans ((g.adjoint a e).symm.trans (h₀ a e))

/-- Homotopy is a congruence for post-composition. -/
lemma comp_right {f g : C ⟶ D} (h : Homotopic f g) (k : D ⟶ E) :
    Homotopic (f ≫ k) (g ≫ k) :=
  fun a e => (h a (k.env e)).trans (k.adjoint (f.agent a) e)

/-- Homotopy is a congruence for pre-composition. -/
lemma comp_left (k : E ⟶ C) {f g : C ⟶ D} (h : Homotopic f g) :
    Homotopic (k ≫ f) (k ≫ g) :=
  fun a e => (k.adjoint a (g.env e)).trans (h (k.agent a) e)

end Homotopic

/-- Homotopy equivalence: morphisms in both directions whose composites are
homotopic to the identities.

Paper node: Definition 37 (App. A). -/
def HomotopyEquiv (C D : Frame W) : Prop :=
  ∃ (φ : C ⟶ D) (ψ : D ⟶ C), Homotopic (φ ≫ ψ) (𝟙 C) ∧ Homotopic (ψ ≫ φ) (𝟙 D)

namespace HomotopyEquiv

lemma refl (C : Frame W) : HomotopyEquiv C C :=
  ⟨𝟙 C, 𝟙 C, Homotopic.of_eq (Category.comp_id _), Homotopic.of_eq (Category.comp_id _)⟩

lemma symm (h : HomotopyEquiv C D) : HomotopyEquiv D C :=
  let ⟨φ, ψ, hφψ, hψφ⟩ := h
  ⟨ψ, φ, hψφ, hφψ⟩

lemma trans (h₀ : HomotopyEquiv C D) (h₁ : HomotopyEquiv D E) :
    HomotopyEquiv C E := by
  obtain ⟨φ₀, ψ₀, hφψ₀, hψφ₀⟩ := h₀
  obtain ⟨φ₁, ψ₁, hφψ₁, hψφ₁⟩ := h₁
  refine ⟨φ₀ ≫ φ₁, ψ₁ ≫ ψ₀, ?_, ?_⟩
  · have step : Homotopic ((φ₀ ≫ (φ₁ ≫ ψ₁)) ≫ ψ₀) ((φ₀ ≫ 𝟙 D) ≫ ψ₀) :=
      (hφψ₁.comp_left φ₀).comp_right ψ₀
    exact Homotopic.trans step (Homotopic.of_eq (by simp) |>.trans hφψ₀)
  · have step : Homotopic ((ψ₁ ≫ (ψ₀ ≫ φ₀)) ≫ φ₁) ((ψ₁ ≫ 𝟙 D) ≫ φ₁) :=
      (hψφ₀.comp_left ψ₁).comp_right φ₁
    exact Homotopic.trans step (Homotopic.of_eq (by simp) |>.trans hψφ₁)

/-- Isomorphic frames are homotopy equivalent: the inverse pair composes to the
identities on the nose.

This is the *argument* the paper gives for Claim 40 (isomorphism implies homotopy
equivalence, hence biextensional equivalence via Claim 39).  The annotated Claim 40
statement is `biextEquiv_of_nonempty_iso` below; this lemma is the internal step it
composes, so it carries no node annotation of its own. -/
lemma ofIso (i : C ≅ D) : HomotopyEquiv C D :=
  ⟨i.hom, i.inv, Homotopic.of_eq i.hom_inv_id, Homotopic.of_eq i.inv_hom_id⟩

end HomotopyEquiv

/-- Every frame is homotopy equivalent to its biextensional collapse, by the
representative-selection argument inside the paper's proof of Claim 39. -/
lemma homotopyEquiv_collapse (C : Frame W) : HomotopyEquiv C C.collapse := by
  refine ⟨⟨fun a => Quotient.mk C.agentSetoid a, fun ê => ê.out, ?_⟩,
    ⟨fun â => â.out, fun e => Quotient.mk C.envSetoid e, ?_⟩, ?_, ?_⟩
  · refine fun a ê => Quotient.inductionOn ê fun e => ?_
    exact Quotient.exact ((Quotient.mk C.envSetoid e).out_eq) a
  · refine fun â e => Quotient.inductionOn â fun a => ?_
    exact (Quotient.exact ((Quotient.mk C.agentSetoid a).out_eq) e).symm
  · intro a e
    exact (Quotient.exact ((Quotient.mk C.agentSetoid a).out_eq) e).symm
  · intro â ê
    show C.collapse.outcome â ê =
      C.collapse.outcome (Quotient.mk C.agentSetoid â.out) ê
    rw [Quotient.out_eq]

/-! ## Claims 38–40 and Claim 8 -/

/-- For biextensional frames, homotopy equivalence and isomorphism coincide.

Paper node: Claim 38 (App. A). -/
theorem homotopyEquiv_iff_nonempty_iso_of_biextensional
    (hC : C.Biextensional) (hD : D.Biextensional) :
    HomotopyEquiv C D ↔ Nonempty (C ≅ D) := by
  constructor
  · rintro ⟨φ, ψ, hφψ, hψφ⟩
    -- The composites' agent maps fix every row, so the agent components invert
    -- each other on the nose.
    have hagentC : ∀ a, ψ.agent (φ.agent a) = a := fun a =>
      hC.agent_ext fun e => ((hφψ a e).symm : C.outcome (ψ.agent (φ.agent a)) e = _)
    have hagentD : ∀ b, φ.agent (ψ.agent b) = b := fun b =>
      hD.agent_ext fun e => ((hψφ b e).symm : D.outcome (φ.agent (ψ.agent b)) e = _)
    have hφagent : Function.Bijective φ.agent :=
      Function.bijective_iff_has_inverse.mpr ⟨ψ.agent, hagentC, hagentD⟩
    -- `φ.env` is injective because `D` has no duplicate columns…
    have hinj : Function.Injective φ.env := by
      intro f₁ f₂ hf
      refine hD.env_ext fun b => ?_
      obtain ⟨a, rfl⟩ := hφagent.surjective b
      calc D.outcome (φ.agent a) f₁ = C.outcome a (φ.env f₁) := (φ.adjoint a f₁).symm
        _ = C.outcome a (φ.env f₂) := by rw [hf]
        _ = D.outcome (φ.agent a) f₂ := φ.adjoint a f₂
    -- …and surjective because `C` has no duplicate columns.
    have hsurj : Function.Surjective φ.env := by
      intro e₀
      refine ⟨ψ.env e₀, hC.env_ext fun a => ?_⟩
      calc C.outcome a (φ.env (ψ.env e₀))
          = C.outcome ((φ ≫ ψ).agent a) e₀ := (φ ≫ ψ).adjoint a e₀
        _ = C.outcome (ψ.agent (φ.agent a)) e₀ := rfl
        _ = C.outcome a e₀ := by rw [hagentC]
    have : IsIso φ := Hom.IsIsomorphism.isIso ⟨hφagent, ⟨hinj, hsurj⟩⟩
    exact ⟨asIso φ⟩
  · rintro ⟨i⟩
    exact HomotopyEquiv.ofIso i

/-- A biextensional frame is isomorphic to its own collapse: with no duplicate rows
or columns there is nothing for the collapse to delete.  Unnumbered in the paper —
it is Claim 38 applied to `homotopyEquiv_collapse`, and is the step the paper uses
silently whenever it replaces a biextensional frame by its collapse. -/
lemma Biextensional.nonempty_iso_collapse (h : C.Biextensional) :
    Nonempty (C ≅ C.collapse) :=
  (homotopyEquiv_iff_nonempty_iso_of_biextensional h (collapse_biextensional C)).mp
    (homotopyEquiv_collapse C)

/-- Biextensional equivalence coincides with homotopy equivalence.

Paper node: Claim 39 (App. A). -/
theorem biextEquiv_iff_homotopyEquiv : C ≃ᵇ D ↔ HomotopyEquiv C D := by
  constructor
  · rintro ⟨i⟩
    exact ((homotopyEquiv_collapse C).trans (HomotopyEquiv.ofIso i)).trans
      (homotopyEquiv_collapse D).symm
  · intro h
    have : HomotopyEquiv C.collapse D.collapse :=
      ((homotopyEquiv_collapse C).symm.trans h).trans (homotopyEquiv_collapse D)
    exact (homotopyEquiv_iff_nonempty_iso_of_biextensional
      (collapse_biextensional C) (collapse_biextensional D)).mp this

/-- Isomorphic frames are biextensionally equivalent — the second half of Claim 8,
restated and proved as Claim 40.

Paper node: Claim 8 (§2.2), Claim 40 (App. A). -/
theorem biextEquiv_of_nonempty_iso (h : Nonempty (C ≅ D)) : C ≃ᵇ D :=
  biextEquiv_iff_homotopyEquiv.mpr (HomotopyEquiv.ofIso h.some)

/-- Equal frames are isomorphic — the first half of Claim 8.

Paper node: Claim 8 (§2.2). -/
theorem nonempty_iso_of_eq (h : C = D) : Nonempty (C ≅ D) := ⟨eqToIso h⟩

section RegressionExamples

/- Client-side exercises of the endpoints above (endpoint-usability rule). -/

example (C : Frame W) : C ≃ᵇ C.collapse :=
  biextEquiv_iff_homotopyEquiv.mpr (homotopyEquiv_collapse C)

example (h : C ≃ᵇ D) (h' : D ≃ᵇ E) : C ≃ᵇ E := h.trans h'

example (i : C ≅ D) : C ≃ᵇ D := biextEquiv_of_nonempty_iso ⟨i⟩

example (f : C ⟶ D) (hf : f.IsIsomorphism) : C ≃ᵇ D :=
  biextEquiv_of_nonempty_iso (nonempty_iso_iff_exists_isIsomorphism.mpr ⟨f, hf⟩)

end RegressionExamples

end Frame

end CartesianFrames
