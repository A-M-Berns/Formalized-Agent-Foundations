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
  over *set-indexed* subfamilies rather than model variables.  Each carries the paper's own finiteness
  hypothesis, `ShannonInformation.FiniteEntropyOf`; the "`C` has discrete range" hypothesis is the
  `[Countable U] [MeasurableSingletonClass U]` pair, which is what makes the witnessing
  function automatically measurable (the last line of the printed proof).
* Theorem 4.15 quantifies over an arbitrary `LatentAmalgamation L₁ L₂`, not over the
  canonical one of Lemma 4.13.  The paper says "let `L̃₁` and `L̃₂` be the latent variable
  models **in an** amalgamation of `L₁` and `L₂`", and `Condensation.nonempty_latentAmalgamation`
  is what makes the hypothesis non-vacuous.
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

/-- **Equation (4.62)**: `⋂_{i ∈ A} {B : i ∈ B} = {B : A ⊆ B}`, for a *nonempty* `A`.

Nonemptiness matters: at `A = ∅` the left side is the empty intersection, `Set.univ`, and
the right side is `above ∅ = Set.univ` too — so in fact the identity holds for every
`A : Finset I`, and it is stated that way. -/
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

Paper node: `Lemma 4.14` -/
theorem aeFunctionOf_of_condIndepFun {Ω S T₁ T₂ U : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace T₁] [Countable T₁]
    [MeasurableSingletonClass T₁] [MeasurableSpace T₂] [Countable T₂]
    [MeasurableSingletonClass T₂] [MeasurableSpace U] [Countable U]
    [MeasurableSingletonClass U] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S}
    {Y₁ : Ω → T₁} {Y₂ : Ω → T₂} {C : Ω → U} (hX : Measurable X) (hY₁ : Measurable Y₁)
    (hY₂ : Measurable Y₂) (hC : Measurable C) [ShannonInformation.FiniteEntropyOf X μ]
    [ShannonInformation.FiniteEntropyOf Y₁ μ] [ShannonInformation.FiniteEntropyOf Y₂ μ]
    [ShannonInformation.FiniteEntropyOf C μ] (hindep : CondIndepFun Y₁ Y₂ C μ)
    (h₁ : AEFunctionOf (⟨C, Y₁⟩ : Ω → U × T₁) X μ)
    (h₂ : AEFunctionOf (⟨C, Y₂⟩ : Ω → U × T₂) X μ) :
    AEFunctionOf C X μ := by
  sorry

/-! ## Theorem 4.15 — comparison of perfect condensations -/

section Comparison

variable {I : Type w} [Finite I] {M : RVModel.{u, v, w} I}
  {L₁ : LatentModel.{u, v, w, u₁, v₁} M} {L₂ : LatentModel.{u, v, w, u₂, v₂} M}

/-- **Theorem 4.15** (comparison of perfect condensations).  If `L₁` and `L₂` are both
perfect condensations of `M`, then inside any amalgamation of them the latent variables
correspond: `Y_A` is almost everywhere a function of `Z_⊇A`, and reciprocally `Z_A` is
almost everywhere a function of `Y_⊇A`.

Here `(Y_A)` are the latents of `L̃₁ = Am.lat₁` and `(Z_A)` those of `L̃₂ = Am.lat₂`, both
living on the amalgamating space `Λ₀` with measure `P₀`; `Z_⊇A` is
`Am.lat₂.jointAbove A.toFinset`, the joint variable of (3.6).

Such an amalgamation always exists (`Condensation.nonempty_latentAmalgamation`), so the
hypothesis is not vacuous.

Paper node: `Theorem 4.15` -/
theorem aeFunctionOf_jointAbove_of_perfectlyCondenses
    (h₁ : L₁.PerfectlyCondenses) (h₂ : L₂.PerfectlyCondenses)
    (Am : LatentAmalgamation.{u, v, w, u₀, u₁, v₁, u₂, v₂} L₁ L₂) (A : PPlus I) :
    AEFunctionOf (Am.lat₂.jointAbove A.toFinset) (Am.lat₁.Y A) Am.P₀ ∧
      AEFunctionOf (Am.lat₁.jointAbove A.toFinset) (Am.lat₂.Y A) Am.P₀ := by
  sorry

end Comparison

end Condensation
