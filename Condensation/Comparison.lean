import Condensation.Amalgamation
import Condensation.Perfect

/-!
# Condensation §4 — comparison of perfect condensations

Lemma 4.14 and Theorem 4.15 of Eisenstat, *Condensation: A Theory of Concepts*:

* Lemma 4.14 — a **conditional-independence rigidity lemma**: if `X` is a.e. a function of
  `(C, Y₁)` and of `(C, Y₂)`, and `Y₁ ⟂ Y₂ | C`, then `X` is a.e. a function of `C` alone;
* Theorem 4.15 — the **comparison theorem**: any two perfect condensations of the same
  random variable model determine each other, in the sense that inside an amalgamation
  the latent `Y_A` of one is a.e. a function of the family `Z_⊇A` of the other.

## Modeling decisions

* Lemma 4.14 is stated over **bare random variables**, not over a model: the paper states
  it for "random variables on some countable discrete probability space", and it is used
  inside Theorem 4.15's induction at variables (`Z_F`, `Z_G`, `Z_{F∩G}`) that are joints
  over *set-indexed* subfamilies rather than model variables.  Its binders are the paper's:
  the countable discrete probability space is `Ω`, and the only *range* carrying a
  countability hypothesis is `C`'s — the `[Countable U] [MeasurableSingletonClass U]` pair
  is what makes the witnessing function automatically measurable (the last line of the
  printed proof).  The ranges of `X`, `Y₁` and `Y₂` carry nothing beyond a measurable-space
  structure, and no finiteness hypothesis of any kind appears: the printed argument is
  measure-theoretic and uses no entropy.  (Before 2026-08-17 the statement carried
  `FiniteRange` binders on all four ranges; Phase 4b swapped them for
  `ShannonInformation.FiniteEntropyOf` binders, and round 2 established that neither
  belonged here in the first place — R2-F01/F23.)

  **As printed, the lemma is false** — nothing in the printed binders makes `X`'s range
  separate points, and when it does not, `CondIndepFun Y₁ Y₂ C μ` can be vacuous while the
  conclusion is a real constraint: `Ω = Bool` uniform, `U = Unit` (so `C` is constant),
  `S = T₁ = T₂` the two-point set carrying the *trivial* σ-algebra `⊥`, and
  `X = Y₁ = Y₂ = id` satisfies every hypothesis (any map into a `⊥`-space is measurable,
  `comap Yₖ ⊥ = ⊥` makes the independence automatic, and `Prod.snd` witnesses both
  functional dependences) while the conclusion would force `X` to be a.e. constant
  (machine-checked, M2-B1; `notes/paper-errata.md` entry 15).  The Lean statement therefore
  carries `[MeasurableSingletonClass S]` on `X`'s range — free at every call site here (`X`
  is always a model's variable, and `RVModel` carries `singR`) and licensed by the paper's
  standing convention that "our probability spaces are countable and discrete" (§2, just
  before Definition 2.4).  `T₁`, `T₂` genuinely need only a measurable-space structure.
  Orchestrator ruling 2026-08-18: round 2's binder strip (R2-F01/F23) had gone one range
  too far; the binder is restored and the lemma is proved.
* Theorem 4.15 quantifies over an arbitrary `LatentAmalgamation L₁ L₂`, not over the
  canonical one of Lemma 4.13.  The paper says "let `L̃₁` and `L̃₂` be the latent variable
  models **in an** amalgamation of `L₁` and `L₂`".  The hypothesis is not vacuous: the
  paper's own general existence claim, `Condensation.nonempty_latentAmalgamation`
  (Lemma 4.13), is proved, and `Condensation.LatentAmalgamation.diagonal` — a latent
  variable model amalgamated with itself along the identity — is a second, far cheaper
  witness that does not depend on Lemma 4.13's measure construction at all.  Prefer
  `diagonal` when all that is wanted is an inhabitant; it was added precisely because at
  the time Lemma 4.13 was still `sorry` and nothing axiom-clean witnessed the hypothesis
  (R2-F19).
* The two conclusions are stated on `Λ₀` with the single measure `P₀`, which is exactly why
  `LatentAmalgamation` was designed with `Λ₀` primary: `Am.lat₁` and `Am.lat₂` are honest
  `LatentModel M`s whose underlying spaces are `Λ₀` *definitionally*, so `Am.lat₂.jointAbove`
  and `Am.lat₁.Y` are variables on one and the same space and `AEFunctionOf` relates them
  without transport.
* Erratum (already logged in `notes/paper-errata.md`): the printed proof of Theorem 4.15
  uses an undefined `F_i`; it is `{B : i ∈ B}`, i.e. `Condensation.contribIdx i`, and
  (4.62) `⋂_{i ∈ A} F_i = {B : B ⊇ A}` is `Condensation.iInter_contribIdx_eq_above` below.
-/

universe u v w u₀ u₁ v₁ u₂ v₂

namespace Condensation

open MeasureTheory ProbabilityTheory

/-! ## An index-family identity used by Theorem 4.15

Equation (4.62).  The paper writes `F_i` without defining it; it is `contribIdx i`. -/

/-- **Equation (4.62)**: `⋂_{i ∈ A} {B : i ∈ B} = {B : A ⊆ B}`, for every `A : Finset I`.

The paper writes (4.62) inside an argument where `A` is nonempty, but nonemptiness is not
needed: at `A = ∅` the left side is the empty intersection, `Set.univ`, and the right side
is `above ∅ = Set.univ` too.  So the identity is stated without a nonemptiness
hypothesis. -/
lemma iInter_contribIdx_eq_above {I : Type*} (A : Finset I) :
    ⋂ i ∈ A, contribIdx i = above A := by
  ext B
  simp only [Set.mem_iInter, mem_contribIdx, mem_above, PPlus.mem_iff]
  exact ⟨fun h => fun i hi => h i hi, fun h i hi => h hi⟩

/-! ## Lemma 4.14 -/

/-- **Lemma 4.14.**  On a countable discrete probability space, if `Y₁` and `Y₂` are
conditionally independent given `C`, and `X` is almost everywhere a function of `(C, Y₁)`
and also almost everywhere a function of `(C, Y₂)`, then `X` is almost everywhere a
function of `C` alone.

Recall the argument order of `Condensation.AEFunctionOf`: `AEFunctionOf V W μ` says that
`W` is a.e. a function of `V`, so the hypotheses read "`X` is a function of `⟨C, Y₁⟩`" and
the conclusion "`X` is a function of `C`".

Recall also `ProbabilityTheory.CondIndepFun f g h μ`: `f` and `g` are conditionally
independent **given** `h` (`PFR/ForMathlib/ConditionalIndependence.lean`), so the
hypothesis below is the paper's "`Y₁` and `Y₂` are conditionally independent given `C`".

The binders are the paper's own and no more.  The countable discrete probability space is
`Ω`; among the *ranges*, only `C`'s carries `[Countable] [MeasurableSingletonClass]`,
because that is what the printed proof uses — it defines the witnessing function
pointwise on the (countable, discrete) range of `C` and appeals to
`measurable_of_countable`.  The ranges of `X`, `Y₁` and `Y₂` need only a measurable-space
structure, and no finiteness hypothesis appears at all: the argument is measure-theoretic
and never forms an entropy.

**Binder ruling (M2, 2026-08-18).** `[MeasurableSingletonClass S]` on `X`'s range is required:
without it the statement is *false* — with `S` carrying the trivial σ-algebra the
conditional-independence hypothesis is vacuous while the conclusion is not (machine-checked
refutation recorded in `notes/paper-errata.md`, entry 15). It is licensed by the paper's
standing convention (§2: "our probability spaces are countable and discrete") and is free
at every call site. `T₁`, `T₂` genuinely need only `MeasurableSpace`. The measurability
hypotheses on `X`, `Y₁`, `Y₂` are the paper's "random variables" and are not used by the
proof (only `C`'s is).

Paper node: `Lemma 4.14` -/
theorem aeFunctionOf_of_condIndepFun {Ω S T₁ T₂ U : Type*} [MeasurableSpace Ω] [Countable Ω]
    [_hΩsing : MeasurableSingletonClass Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace T₁] [MeasurableSpace T₂]
    [MeasurableSpace U] [Countable U] [MeasurableSingletonClass U]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S}
    {Y₁ : Ω → T₁} {Y₂ : Ω → T₂} {C : Ω → U} (_hX : Measurable X) (_hY₁ : Measurable Y₁)
    (_hY₂ : Measurable Y₂) (hC : Measurable C) (hindep : CondIndepFun Y₁ Y₂ C μ)
    (h₁ : AEFunctionOf (⟨C, Y₁⟩ : Ω → U × T₁) X μ)
    (h₂ : AEFunctionOf (⟨C, Y₂⟩ : Ω → U × T₂) X μ) :
    AEFunctionOf C X μ := by
  classical
  obtain ⟨f₁, hf₁, hae₁⟩ := h₁
  obtain ⟨f₂, hf₂, hae₂⟩ := h₂
  rw [ae_iff_of_countable] at hae₁ hae₂
  -- `⟨C, Y₁⟩ ω` does not beta-reduce on its own; a type ascription is the cheapest way in.
  have hae₁' : ∀ x : Ω, μ {x} ≠ 0 → X x = f₁ (C x, Y₁ x) := hae₁
  have hae₂' : ∀ x : Ω, μ {x} ≠ 0 → X x = f₂ (C x, Y₂ x) := hae₂
  -- Independence holds on every fibre of `C` of positive mass.
  have hind : ∀ c : U, μ (C ⁻¹' {c}) ≠ 0 → IndepFun Y₁ Y₂ (μ[|C ⁻¹' {c}]) := by
    have h := hindep
    rw [condIndepFun_iff, ae_iff_of_countable] at h
    intro c hc
    refine h c ?_
    rwa [Measure.map_apply hC (measurableSet_singleton c)]
  -- (4.58)–(4.61): `X` is constant on each positive-mass fibre of `C`.
  have key : ∀ ω ω₀ : Ω, μ {ω} ≠ 0 → μ {ω₀} ≠ 0 → C ω = C ω₀ → X ω = X ω₀ := by
    intro ω ω₀ hω hω₀ hCeq
    have hfibmeas : MeasurableSet (C ⁻¹' {C ω₀}) := hC (measurableSet_singleton _)
    have hmem₀ : ω₀ ∈ C ⁻¹' {C ω₀} := rfl
    have hfib : μ (C ⁻¹' {C ω₀}) ≠ 0 := fun h0 =>
      hω₀ (measure_mono_null (Set.singleton_subset_iff.mpr hmem₀) h0)
    have hfibtop : μ (C ⁻¹' {C ω₀}) ≠ ⊤ := measure_ne_top _ _
    -- transfer between `μ`-atoms of the fibre and `Pc`-atoms
    have hatom : ∀ x : Ω, μ {x} ≠ 0 → C x = C ω₀ → (μ[|C ⁻¹' {C ω₀}]) {x} ≠ 0 := by
      intro x hx hCx
      rw [ProbabilityTheory.cond_apply hfibmeas]
      have : C ⁻¹' {C ω₀} ∩ {x} = {x} :=
        Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hCx)
      rw [this]
      exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hfibtop) hx
    have hatom' : ∀ x : Ω, (μ[|C ⁻¹' {C ω₀}]) {x} ≠ 0 → μ {x} ≠ 0 ∧ C x = C ω₀ := by
      intro x hx
      rw [ProbabilityTheory.cond_apply hfibmeas] at hx
      have hx' : μ (C ⁻¹' {C ω₀} ∩ {x}) ≠ 0 := fun h0 => hx (by rw [h0, mul_zero])
      have hne : (C ⁻¹' {C ω₀} ∩ {x}).Nonempty := by
        rcases Set.eq_empty_or_nonempty (C ⁻¹' {C ω₀} ∩ {x}) with h | h
        · exact absurd (by rw [h, measure_empty]) hx'
        · exact h
      obtain ⟨y, hy₁, hy₂⟩ := hne
      rw [Set.mem_singleton_iff] at hy₂
      subst hy₂
      exact ⟨fun h0 => hx' (measure_mono_null Set.inter_subset_right h0), hy₁⟩
    -- the two saturated events of (4.60)
    set s₁ : Set T₁ := (fun t => f₁ (C ω₀, t)) ⁻¹' {X ω₀} with hs₁def
    set s₂ : Set T₂ := (fun t => f₂ (C ω₀, t)) ⁻¹' {X ω} with hs₂def
    have hs₁ : MeasurableSet s₁ :=
      (hf₁.comp (measurable_const.prodMk measurable_id)) (measurableSet_singleton _)
    have hs₂ : MeasurableSet s₂ :=
      (hf₂.comp (measurable_const.prodMk measurable_id)) (measurableSet_singleton _)
    have hmem₁ : ω₀ ∈ Y₁ ⁻¹' s₁ := by
      simp only [hs₁def, Set.mem_preimage, Set.mem_singleton_iff]
      exact (hae₁ ω₀ hω₀).symm
    have hmem₂ : ω ∈ Y₂ ⁻¹' s₂ := by
      simp only [hs₂def, Set.mem_preimage, Set.mem_singleton_iff]
      rw [← hCeq]
      exact (hae₂ ω hω).symm
    -- (4.61): the intersection has positive conditional mass, so it carries an atom
    have hpos₁ : (μ[|C ⁻¹' {C ω₀}]) (Y₁ ⁻¹' s₁) ≠ 0 := fun h0 =>
      hatom ω₀ hω₀ rfl (measure_mono_null (Set.singleton_subset_iff.mpr hmem₁) h0)
    have hpos₂ : (μ[|C ⁻¹' {C ω₀}]) (Y₂ ⁻¹' s₂) ≠ 0 := fun h0 =>
      hatom ω hω hCeq (measure_mono_null (Set.singleton_subset_iff.mpr hmem₂) h0)
    have hprod : (μ[|C ⁻¹' {C ω₀}]) (Y₁ ⁻¹' s₁ ∩ Y₂ ⁻¹' s₂) ≠ 0 := by
      rw [(hind (C ω₀) hfib).measure_inter_preimage_eq_mul s₁ s₂ hs₁ hs₂]
      exact mul_ne_zero hpos₁ hpos₂
    obtain ⟨υ, hυmem, hυ⟩ :
        ∃ υ ∈ Y₁ ⁻¹' s₁ ∩ Y₂ ⁻¹' s₂, (μ[|C ⁻¹' {C ω₀}]) {υ} ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hprod ((measure_null_iff_singleton (Set.to_countable _)).mpr hcon)
    obtain ⟨hυμ, hυC⟩ := hatom' υ hυ
    have e₁ : X υ = X ω₀ := by
      rw [hae₁' υ hυμ, hυC]
      exact hυmem.1
    have e₂ : X υ = X ω := by
      rw [hae₂' υ hυμ, hυC]
      exact hυmem.2
    rw [← e₂, e₁]
  -- the witnessing function: pick an atom in each fibre (`R_C` discrete, so `g` is
  -- automatically measurable — the last line of the printed proof)
  have hΩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hSne : Nonempty S := ⟨X (Classical.arbitrary Ω)⟩
  refine ⟨fun c => if h : ∃ ω, μ {ω} ≠ 0 ∧ C ω = c then X h.choose else Classical.arbitrary S,
    measurable_of_countable _, ?_⟩
  rw [ae_iff_of_countable]
  intro ω hω
  have hex : ∃ ω', μ {ω'} ≠ 0 ∧ C ω' = C ω := ⟨ω, hω, rfl⟩
  have hgc : (fun c => if h : ∃ ω, μ {ω} ≠ 0 ∧ C ω = c then X h.choose
      else Classical.arbitrary S) (C ω) = X hex.choose := dif_pos hex
  rw [hgc]
  exact key ω hex.choose hω hex.choose_spec.1 hex.choose_spec.2.symm


/-! ## Theorem 4.15 — comparison of perfect condensations -/

section Comparison

variable {I : Type w} [Finite I] {M : RVModel.{u, v, w} I}
  {L₁ : LatentModel.{u, v, w, u₁, v₁} M} {L₂ : LatentModel.{u, v, w, u₂, v₂} M}

/-- Perfect condensation transfers from `L₁` to `L̃₁`. -/
lemma _root_.Condensation.LatentAmalgamation.perfectlyCondenses_lat₁
    (Am : LatentAmalgamation.{u, v, w, u₀, u₁, v₁, u₂, v₂} L₁ L₂) (h : L₁.PerfectlyCondenses) :
    Am.lat₁.PerfectlyCondenses := fun A => (Am.condScore_lat₁ A).trans (h A)

/-- Perfect condensation transfers from `L₂` to `L̃₂`. -/
lemma _root_.Condensation.LatentAmalgamation.perfectlyCondenses_lat₂
    (Am : LatentAmalgamation.{u, v, w, u₀, u₁, v₁, u₂, v₂} L₁ L₂) (h : L₂.PerfectlyCondenses) :
    Am.lat₂.PerfectlyCondenses := fun A => (Am.condScore_lat₂ A).trans (h A)

/-! ### The one direction of Theorem 4.15 -/

/-- One direction of **Theorem 4.15**, from which the theorem follows by
`LatentAmalgamation.symm`.  This is the paper's proof: at each `i ∈ A` the latent `Y_A` is
a.e. a function of `X_i` (Corollary 4.6 applied to `L̃₁`) and `X_i` is a.e. a function of
`Z_∋i` (Definition 3.2 for `L̃₂`), the two being composable because `π̃₁ =ᵐ π̃₂`
(`LatentAmalgamation.comm`); then Lemma 4.14 is applied along an induction over `i ∈ A`,
whose conditional-independence side condition comes from Proposition 4.10 applied to `L̃₂`
(Theorem 4.9 (B1 ⇒ B2) makes `L̃₂`'s latents ordered Markov).  The families being
intersected stay upward closed, and (4.62) closes the induction at `Z_⊇A`. -/
private lemma aeFunctionOf_jointAbove_aux (h₁ : L₁.PerfectlyCondenses)
    (h₂ : L₂.PerfectlyCondenses)
    (Am : LatentAmalgamation.{u, v, w, u₀, u₁, v₁, u₂, v₂} L₁ L₂) (A : PPlus I) :
    AEFunctionOf (Am.lat₂.jointAbove A.toFinset) (Am.lat₁.Y A) Am.P₀ := by
  haveI : Countable Am.lat₂.Λ := Am.countΛ₀
  haveI : MeasurableSingletonClass Am.lat₂.Λ := Am.singΛ₀
  -- `Y_A` is a.e. a function of `Z_∋i`, for every `i ∈ A`
  have hbase : ∀ i ∈ A.toFinset,
      AEFunctionOf (Am.lat₂.jointOn (contribIdx i)) (Am.lat₁.Y A) Am.P₀ := by
    intro i hi
    have hYA : AEFunctionOf (M.X i ∘ Am.π₁) (Am.lat₁.Y A) Am.P₀ :=
      Am.lat₁.aeFunctionOf_of_perfectlyCondenses (Am.perfectlyCondenses_lat₁ h₁) i A hi
    have hcomm : (M.X i ∘ Am.π₁) =ᵐ[Am.P₀] (M.X i ∘ Am.π₂) := by
      filter_upwards [Am.comm] with l hl using by simp only [Function.comp_apply, hl]
    exact (Am.contributes₂ i).trans (hYA.congr_left hcomm)
  -- Proposition 4.10 for `L̃₂`, via Theorem 4.9 (B1 ⇒ B2)
  have hCI : ∀ F G : Set (PPlus I), IsUpperSet F → IsUpperSet G →
      CondIndepFun (Am.lat₂.jointOn F) (Am.lat₂.jointOn G) (Am.lat₂.jointOn (F ∩ G)) Am.P₀ :=
    Am.lat₂.L.orderedMarkov_iff.mp
      (Am.lat₂.perfect_tfae_B.mp (Am.perfectlyCondenses_lat₂ h₂)).2
  -- the induction of (4.62), over a nonempty `T ⊆ A`
  have hind : ∀ (T : Finset I) (hT : T.Nonempty), T ⊆ A.toFinset →
      AEFunctionOf (Am.lat₂.jointOn (⋂ i ∈ T, contribIdx i)) (Am.lat₁.Y A) Am.P₀ := by
    intro T hT
    induction hT using Finset.Nonempty.cons_induction with
    | singleton i =>
        intro hsub
        have hset : (⋂ j ∈ ({i} : Finset I), contribIdx j) = contribIdx i :=
          Finset.set_biInter_singleton i _
        exact (Am.lat₂.L.aeFunctionOf_jointOn_mono hset.symm.subset Am.P₀).trans
          (hbase i (hsub (Finset.mem_singleton_self i)))
    | cons j T hj hT ih =>
        intro hsub
        have hjA : j ∈ A.toFinset := hsub (by simp)
        have hTsub : T ⊆ A.toFinset := fun x hx => hsub (by simp [hx])
        have hupj : IsUpperSet (contribIdx j) := by
          rw [contribIdx_eq_contrib_singleton]
          exact isUpperSet_contrib _
        have hres : AEFunctionOf (Am.lat₂.jointOn (contribIdx j ∩ ⋂ i ∈ T, contribIdx i))
            (Am.lat₁.Y A) Am.P₀ :=
          aeFunctionOf_of_condIndepFun
            (_hΩsing := Am.singΛ₀) (Am.lat₁.L.measurable_X A)
            (Am.lat₂.L.measurable_jointOn _) (Am.lat₂.L.measurable_jointOn _)
            (Am.lat₂.L.measurable_jointOn _)
            (hCI (contribIdx j) (⋂ i ∈ T, contribIdx i) hupj (isUpperSet_iInter_contribIdx T))
            ((aeFunctionOf_comp measurable_snd).trans (hbase j hjA))
            ((aeFunctionOf_comp measurable_snd).trans (ih hTsub))
        have hset : (⋂ i ∈ Finset.cons j T hj, contribIdx i)
            = contribIdx j ∩ ⋂ i ∈ T, contribIdx i := by
          ext B
          simp [Set.mem_iInter, Finset.mem_cons]
        exact (Am.lat₂.L.aeFunctionOf_jointOn_mono hset.symm.subset Am.P₀).trans hres
  have hset : (⋂ i ∈ A.toFinset, contribIdx i) = above A.toFinset :=
    iInter_contribIdx_eq_above _
  exact (Am.lat₂.L.aeFunctionOf_jointOn_mono hset.subset Am.P₀).trans
    (hind A.toFinset A.nonempty (Finset.Subset.refl _))

/-- **Theorem 4.15** (comparison of perfect condensations).  If `L₁` and `L₂` are both
perfect condensations of `M`, then inside any amalgamation of them the latent variables
correspond: `Y_A` is almost everywhere a function of `Z_⊇A`, and reciprocally `Z_A` is
almost everywhere a function of `Y_⊇A`.

Here `(Y_A)` are the latents of `L̃₁ = Am.lat₁` and `(Z_A)` those of `L̃₂ = Am.lat₂`, both
living on the amalgamating space `Λ₀` with measure `P₀`; `Z_⊇A` is
`Am.lat₂.jointAbove A.toFinset`, the joint variable of (3.6).

The amalgamation hypothesis is not vacuous, twice over: the paper's own existence claim
`Condensation.nonempty_latentAmalgamation` (Lemma 4.13) is proved, and
`Condensation.LatentAmalgamation.diagonal` constructs one directly — a latent variable
model amalgamated with itself along the identity — independently of that construction.

Paper node: `Theorem 4.15` -/
theorem aeFunctionOf_jointAbove_of_perfectlyCondenses
    (h₁ : L₁.PerfectlyCondenses) (h₂ : L₂.PerfectlyCondenses)
    (Am : LatentAmalgamation.{u, v, w, u₀, u₁, v₁, u₂, v₂} L₁ L₂) (A : PPlus I) :
    AEFunctionOf (Am.lat₂.jointAbove A.toFinset) (Am.lat₁.Y A) Am.P₀ ∧
      AEFunctionOf (Am.lat₁.jointAbove A.toFinset) (Am.lat₂.Y A) Am.P₀ :=
  ⟨aeFunctionOf_jointAbove_aux h₁ h₂ Am A, aeFunctionOf_jointAbove_aux h₂ h₁ Am.symm A⟩

end Comparison

end Condensation
