import SafeParetoImprovements.PerfectCoordination
import SafeParetoImprovements.Polytope
import Mathlib.Probability.ConditionalProbability
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Characterizing perfect-coordination SPIs (§5.3): Lemma 13 and Corollary 14

Both nodes are about the *expected* payoffs of perfect-coordination SPIs, so they live at
the `Representatives` level, with the expectation the Bochner integral of the
`(N → ℝ)`-valued payoff of the token play and the conditional expectation
`E[· | Π(Γ) = a]` the integral against Mathlib's conditional measure
`ProbabilityTheory.cond` on the fiber `{Π(Γ) = a}`.  On the support of `Π(Γ)` those fibers
have positive probability and the conditional measure is a probability measure; off the
support the paper's conditional expectations are undefined (erratum D7) and the nodes are
stated on the support.

* **Lemma 13** (`Representatives.exists_reassignment_condExp_eq`): under Assumptions 1–2
  with room, every perfect-coordination SPI `Γ′` can be replaced by a token copy of the
  reduced game — `TokenGame.reassign`, with `uᵉ` defined *along the isomorphism Assumption 2
  supplies* (erratum D6, RULING 10) — that is again a perfect-coordination SPI and has the
  same conditional expected payoff on every supported outcome, hence the same expected
  payoff.  The copy is of `reduce Γ`, not of `Γ`: Assumption 2 speaks only about reduced
  games, so the paper's "(Â, û) is isomorphic to Γ, thus by Assumption 2 …" needs
  Assumption 1 to first move the play into the reduction (RULING 11).  The relabeling is
  *exact* — the paper prints `û(â) = u(a)` — so the isomorphism is exposed with scale `1`
  and shift `0` (`Game.ExactCopy`), not merely as `Game.Isomorphic` (R5-F01/F07).
* **Corollary 14** (`Representatives.achievable_eq_improvementSum`, `convex_achievable`,
  `isCompact_achievable`, `isPolytope_achievable`): the set of expected payoffs safely
  achievable with perfect coordination is the weighted Minkowski sum
  `∑ₐ P(Π(Γ) = a) • {y ∈ C(Γ) | y ≥ u(a)}` over the outcomes of `Γ` (erratum D7: the
  paper's "convex polygon" is its `n = 2` wording; the polytope substrate is
  `Polytope.lean`), a convex compact polytope.

## What `condExp` is, and what it is in the in-tree models

`Representatives.condExp` is a genuine Bochner integral against the conditional measure.
In every *book* model of this development it nevertheless collapses to a point evaluation:
a `Book` page is chosen per isomorphism class of the reduced game, so the token play is a
function of `Π(Γ)` and the fiber `{Π(Γ) = a}` carries a single token payoff.  That is a
property of the book construction, not of the definition — `condExp` averaging strictly
between the values it integrates is witnessed by the hand-built family
`Examples.mixPlay` / `Examples.mixToken` of `Examples/CharacterizationWitnesses.lean`,
whose play reads the *size* of the game it is handed, so the token play is not a function
of `Π(Γ)` and the conditional expectation `(½, ½)` is a value the integrand never takes
(R5-F11).
-/

universe u v w

namespace SafeParetoImprovements

open Filter Set MeasureTheory ProbabilityTheory
open scoped Pointwise

variable {N : Type u} {𝒜 : N → Type v}

namespace Representatives

variable (R : Representatives.{u, v, w} N 𝒜)

/-! ### Fibers of the play and the vector-valued integrals -/

/-- The event `Π(Γ) = a`. -/
def fiber (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) : Set R.Ω := {ω | R.play Γ ω = a}

lemma measurableSet_fiber' (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) : MeasurableSet (R.fiber Γ a) :=
  R.measurableSet_fiber Γ a

lemma mem_support_iff (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) : a ∈ R.support Γ ↔ R.μ (R.fiber Γ a) ≠ 0 :=
  Iff.rfl

lemma fiber_disjoint (Γ : Game N 𝒜) {a b : ∀ i, 𝒜 i} (hab : a ≠ b) :
    Disjoint (R.fiber Γ a) (R.fiber Γ b) := by
  rw [Set.disjoint_left]
  intro ω ha hb
  exact hab (ha.symm.trans hb)

/-- The conditional measure on a fiber is finite: total mass `1` on a supported fiber and
`0` off the support. -/
instance isFiniteMeasure_cond_fiber (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) :
    IsFiniteMeasure (R.μ[|R.fiber Γ a]) := by
  refine ⟨?_⟩
  rw [cond_apply (R.measurableSet_fiber' Γ a), Set.inter_univ]
  by_cases h : R.μ (R.fiber Γ a) = 0
  · simp [h]
  · rw [ENNReal.inv_mul_cancel h (measure_ne_top _ _)]
    exact ENNReal.one_lt_top

lemma condExp_isProbabilityMeasure (Γ : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ R.support Γ) :
    IsProbabilityMeasure (R.μ[|R.fiber Γ a]) :=
  cond_isProbabilityMeasure ha

/-- On the fiber, the conditional measure sees `Π(Γ) = a` almost everywhere. -/
lemma ae_play_eq_cond (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) :
    ∀ᵐ ω ∂(R.μ[|R.fiber Γ a]), R.play Γ ω = a :=
  Measure.ae_smul_measure (ae_restrict_mem (R.measurableSet_fiber' Γ a)) _

/-- Almost-everywhere statements for `R.μ` hold almost everywhere for the conditional
measures. -/
lemma ae_cond_of_ae (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) {P : R.Ω → Prop} (h : ∀ᵐ ω ∂R.μ, P ω) :
    ∀ᵐ ω ∂(R.μ[|R.fiber Γ a]), P ω :=
  Measure.ae_smul_measure (ae_restrict_of_ae h) _

variable [Fintype N]

/-- Any `(N → ℝ)`-valued function of `Π(Γ)` is measurable. -/
lemma measurable_comp_play_pi (Γ : Game N 𝒜) (g : (∀ i, 𝒜 i) → N → ℝ) :
    Measurable fun ω => g (R.play Γ ω) :=
  measurable_pi_iff.2 fun i => R.measurable_comp_play Γ fun a => g a i

/-- Any `(N → ℝ)`-valued function of `Π(Γ)` is integrable against any finite measure on the
sample space (it takes finitely many values). -/
lemma integrable_comp_play_pi (Γ : Game N 𝒜) (g : (∀ i, 𝒜 i) → N → ℝ) (ν : Measure R.Ω)
    [IsFiniteMeasure ν] : Integrable (fun ω => g (R.play Γ ω)) ν := by
  classical
  refine Integrable.of_bound (R.measurable_comp_play_pi Γ g).aestronglyMeasurable
    (∑ a ∈ Γ.profilesFinset, ‖g a‖) (ae_of_all _ fun ω => ?_)
  exact Finset.single_le_sum (f := fun a => ‖g a‖) (fun a _ => norm_nonneg _)
    (Γ.mem_profilesFinset.2 (R.toPlay.mem Γ ω))

/-- The **expected payoff of a token game to the original players**, `E[uᵉ(Π(Aˢ, uˢ))]`. -/
noncomputable def tokenValue [DecidableEq N] (Γ : Game N 𝒜) (T : TokenGame Γ) : N → ℝ :=
  ∫ ω, T.ue (R.play T.game ω) ∂R.μ

/-- The **conditional expectation** `E[g | Π(Γ) = a]`, as the integral against the
conditional measure on the fiber.  Meaningful on the support of `Π(Γ)` (erratum D7).

This is a genuine average, but it collapses to a point evaluation in every *book* model of
this development: a `Book` page is chosen per isomorphism class of the reduced game, so the
token play is a function of `Π(Γ)` and the fiber `{Π(Γ) = a}` carries a single token payoff
(`condExp_comp_play` is then all one ever needs).  That is a property of the book
construction, not of this definition: `Examples.condExp_genuine_average` exhibits a play
family for which `E[uᵉ(Π(Aˢ,uˢ)) | Π(Γ) = a] = (½, ½)` while the integrand takes only the
values `(0,0)` and `(1,1)` (R5-F11). -/
noncomputable def condExp (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) (g : R.Ω → N → ℝ) : N → ℝ :=
  ∫ ω, g ω ∂(R.μ[|R.fiber Γ a])

/-- The conditional expectation of a function of `Π(Γ)` on a supported fiber is its value
there. -/
lemma condExp_comp_play (Γ : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ R.support Γ)
    (g : (∀ i, 𝒜 i) → N → ℝ) : R.condExp Γ a (fun ω => g (R.play Γ ω)) = g a := by
  haveI := R.condExp_isProbabilityMeasure Γ ha
  unfold condExp
  rw [integral_congr_ae ((R.ae_play_eq_cond Γ a).mono fun ω hω => by rw [hω]), integral_const,
    probReal_univ, one_smul]

/-- Conditional expectation respects almost-everywhere order on the fiber.

A coordinate of a vector-valued integral is the integral of the coordinate: that is
Mathlib's `MeasureTheory.eval_integral` (`Mathlib/MeasureTheory/SpecificCodomains/Pi.lean`),
not a lemma of this development (R5-F05). -/
lemma condExp_mono (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) {g₁ g₂ : R.Ω → N → ℝ}
    (h₁ : Integrable g₁ (R.μ[|R.fiber Γ a])) (h₂ : Integrable g₂ (R.μ[|R.fiber Γ a]))
    (h : ∀ᵐ ω ∂(R.μ[|R.fiber Γ a]), g₁ ω ≤ g₂ ω) :
    R.condExp Γ a g₁ ≤ R.condExp Γ a g₂ := by
  intro i
  unfold condExp
  rw [eval_integral (fun j => h₁.eval j) i, eval_integral (fun j => h₂.eval j) i]
  refine integral_mono_ae ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => ℝ) i).integrable_comp h₁)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => ℝ) i).integrable_comp h₂) ?_
  exact h.mono fun ω hω => hω i

/-! ### The law of total expectation over the fibers -/

/-- `E[g] = ∑ₐ P(Π(Γ) = a) · E[g | Π(Γ) = a]`, the sum over the outcomes of `Γ`. -/
lemma integral_eq_sum_condExp [DecidableEq N] (Γ : Game N 𝒜) (g : R.Ω → N → ℝ)
    (hg : Integrable g R.μ) :
    ∫ ω, g ω ∂R.μ = ∑ a ∈ Γ.profilesFinset, R.μ.real (R.fiber Γ a) • R.condExp Γ a g := by
  classical
  have hcover : (⋃ a ∈ Γ.profilesFinset, R.fiber Γ a) = univ := by
    ext ω
    simp only [mem_iUnion, mem_univ, iff_true, exists_prop]
    exact ⟨R.play Γ ω, Γ.mem_profilesFinset.2 (R.toPlay.mem Γ ω), rfl⟩
  have hsplit : ∫ ω, g ω ∂R.μ = ∑ a ∈ Γ.profilesFinset, ∫ ω in R.fiber Γ a, g ω ∂R.μ := by
    rw [← integral_biUnion_finset _ (fun a _ => R.measurableSet_fiber' Γ a)
      (fun a _ b _ hab => R.fiber_disjoint Γ hab) (fun a _ => hg.integrableOn), hcover,
      Measure.restrict_univ]
  rw [hsplit]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold condExp ProbabilityTheory.cond
  rw [integral_smul_measure, smul_smul]
  by_cases h : R.μ (R.fiber Γ a) = 0
  · rw [h, Measure.real, h, ENNReal.toReal_zero, zero_mul, zero_smul,
      Measure.restrict_eq_zero.2 h, integral_zero_measure]
  · rw [Measure.real, ← ENNReal.toReal_mul, ENNReal.mul_inv_cancel h (measure_ne_top _ _),
      ENNReal.toReal_one, one_smul]

/-! ### Lemma 13 -/

variable [DecidableEq N] [∀ i, DecidableEq (𝒜 i)]

omit [∀ i, DecidableEq (𝒜 i)] in
/-- The conditional expectation of a feasible-valued payoff on a supported fiber is
feasible: `C(Γ)` is closed and convex. -/
lemma condExp_mem_feasible (Γ : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ R.support Γ)
    {Γ' : Game N 𝒜} {g : (∀ i, 𝒜 i) → N → ℝ} (hg : ∀ b ∈ Γ'.profiles, g b ∈ Γ.feasible) :
    R.condExp Γ a (fun ω => g (R.play Γ' ω)) ∈ Γ.feasible := by
  haveI := R.condExp_isProbabilityMeasure Γ ha
  exact Γ.convex_feasible.integral_mem Γ.isClosed_feasible
    (ae_of_all _ fun ω => hg _ (R.toPlay.mem Γ' ω)) (R.integrable_comp_play_pi Γ' g _)

omit [∀ i, DecidableEq (𝒜 i)] in
/-- On a supported fiber, the conditional expected token payoff of a perfect-coordination
SPI is at least the base payoff there. -/
lemma le_condExp_of_isSPI (Γ : Game N 𝒜) {a : ∀ i, 𝒜 i} (ha : a ∈ R.support Γ)
    {T : TokenGame Γ} (hT : T.IsSPI R.toPlay R.certainty) :
    Γ.u a ≤ R.condExp Γ a (fun ω => T.ue (R.play T.game ω)) := by
  haveI := R.condExp_isProbabilityMeasure Γ ha
  have hconst : R.condExp Γ a (fun _ => Γ.u a) = Γ.u a := by
    unfold condExp; rw [integral_const, probReal_univ, one_smul]
  rw [← hconst]
  refine R.condExp_mono Γ a (integrable_const _) (R.integrable_comp_play_pi T.game T.ue _) ?_
  filter_upwards [R.ae_play_eq_cond Γ a, R.ae_cond_of_ae Γ a hT] with ω hωa hωT
  rw [← hωa]; exact hωT

/-- **Lemma 13** (RULINGS 10, 11; errata D6, D7): under Assumptions 1 and 2, with room for
tokens, every perfect-coordination SPI `Γ′` on `Γ` can be replaced by a token copy of the
reduced game — a `TokenGame.reassign`, whose `uᵉ` is defined along the isomorphism
Assumption 2 supplies — that is again a perfect-coordination SPI, has the same conditional
expected payoff on every outcome in the support of `Π(Γ)`, and hence the same expected
payoff.  Off the support the paper's conditional expectations are undefined (D7), and the
reassignment there is `u` itself.

The copy is exposed as a `Game.ExactCopy` — an isomorphism with scale `1` and shift `0`,
i.e. the paper's `û(â) = u(a)` — and not merely as `Game.Isomorphic`: the witness the proof
builds is the token relabeling `Game.tokenCopy` along `Game.tokenIso` (R5-F01/F07).  What
is *not* exposed is which relabeling: the token map is chosen from the room hypothesis, and
`uᵉ` is defined along whichever isomorphism Assumption 2 supplies (D6, RULING 10).

Paper node: `Lemma 13` -/
theorem exists_reassignment_condExp_eq (Γ : Game N 𝒜)
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty)
    (h : Γ.reduce.HasRoomOutside Γ.S) {T' : TokenGame Γ} (hT' : T'.IsSPI R.toPlay R.certainty) :
    ∃ T : TokenGame Γ, Γ.reduce.ExactCopy T.game ∧ T.IsSPI R.toPlay R.certainty ∧
      (∀ a ∈ R.support Γ, R.condExp Γ a (fun ω => T.ue (R.play T.game ω)) =
        R.condExp Γ a (fun ω => T'.ue (R.play T'.game ω))) ∧
      R.tokenValue Γ T = R.tokenValue Γ T' := by
  classical
  set g' : R.Ω → N → ℝ := fun ω => T'.ue (R.play T'.game ω) with hg'
  set f : (∀ i, 𝒜 i) → N → ℝ :=
    fun a => if a ∈ R.support Γ then R.condExp Γ a g' else Γ.u a with hfdef
  have hf : ∀ a ∈ Γ.reduce.profiles, f a ∈ Γ.feasible := by
    intro a ha
    by_cases hs : a ∈ R.support Γ
    · simp only [hfdef, if_pos hs]
      exact R.condExp_mem_feasible Γ hs fun b hb => T'.ue_mem b hb
    · simp only [hfdef, if_neg hs]
      exact Γ.u_mem_feasible (Γ.reduce_isSubsetGameOf.profiles_subset ha)
  have hge : ∀ a, Γ.u a ≤ f a := by
    intro a
    by_cases hs : a ∈ R.support Γ
    · simp only [hfdef, if_pos hs]
      exact R.le_condExp_of_isSPI Γ hs hT'
    · simp [hfdef, hs]
  obtain ⟨T, hiso, hT⟩ := Play.exists_tokenGame_ue_eq hA1 hA2 Γ h f hf
  have hcond : ∀ a ∈ R.support Γ,
      R.condExp Γ a (fun ω => T.ue (R.play T.game ω)) = R.condExp Γ a g' := by
    intro a ha
    have h₁ : R.condExp Γ a (fun ω => T.ue (R.play T.game ω)) =
        R.condExp Γ a (fun ω => f (R.play Γ ω)) :=
      integral_congr_ae (R.ae_cond_of_ae Γ a hT)
    rw [h₁, R.condExp_comp_play Γ ha]
    simp only [hfdef, if_pos ha]
  refine ⟨T, hiso, ?_, hcond, ?_⟩
  · filter_upwards [hT] with ω hω
    rw [hω]; exact hge _
  · unfold tokenValue
    rw [R.integral_eq_sum_condExp Γ _ (R.integrable_comp_play_pi T.game T.ue _),
      R.integral_eq_sum_condExp Γ _ (R.integrable_comp_play_pi T'.game T'.ue _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hs : a ∈ R.support Γ
    · rw [hcond a hs]
    · have h0 : R.μ.real (R.fiber Γ a) = 0 := by
        have : R.μ (R.fiber Γ a) = 0 := not_not.1 ((R.mem_support_iff Γ a).not.1 hs)
        rw [Measure.real, this, ENNReal.toReal_zero]
      rw [h0, zero_smul, zero_smul]

/-! ### Corollary 14 -/

omit [∀ i, DecidableEq (𝒜 i)] in
/-- **The safely achievable expected payoffs**: the expected payoffs `E[uᵉ(Π(Aˢ, uˢ))]` of
the perfect-coordination SPIs on `Γ` for these representatives. -/
def achievable (Γ : Game N 𝒜) : Set (N → ℝ) :=
  {y | ∃ T : TokenGame Γ, T.IsSPI R.toPlay R.certainty ∧ R.tokenValue Γ T = y}

omit [∀ i, DecidableEq (𝒜 i)] in
/-- `{y ∈ C(Γ) | y ≥ u(a)}`: the feasible payoff vectors that weakly Pareto-improve on the
outcome `a`. -/
def _root_.SafeParetoImprovements.Game.improvementSet (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) :
    Set (N → ℝ) := Γ.feasible ∩ Ici (Γ.u a)

omit [∀ i, DecidableEq (𝒜 i)] in
lemma _root_.SafeParetoImprovements.Game.u_mem_improvementSet (Γ : Game N 𝒜) {a : ∀ i, 𝒜 i}
    (ha : a ∈ Γ.profiles) : Γ.u a ∈ Γ.improvementSet a :=
  ⟨Γ.u_mem_feasible ha, Set.self_mem_Ici⟩

omit [∀ i, DecidableEq (𝒜 i)] in
lemma _root_.SafeParetoImprovements.Game.convex_improvementSet (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) :
    Convex ℝ (Γ.improvementSet a) :=
  Γ.convex_feasible.inter (convex_Ici _)

omit [∀ i, DecidableEq (𝒜 i)] in
lemma _root_.SafeParetoImprovements.Game.isCompact_improvementSet (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) :
    IsCompact (Γ.improvementSet a) :=
  Γ.isCompact_feasible.inter_right isClosed_Ici

omit [∀ i, DecidableEq (𝒜 i)] in
/-- The weighted Minkowski sum `∑ₐ P(Π(Γ) = a) • {y ∈ C(Γ) | y ≥ u(a)}` over the outcomes of
`Γ`; outcomes outside the support contribute the singleton `{0}`. -/
def improvementSum (Γ : Game N 𝒜) : Set (N → ℝ) :=
  ∑ a ∈ Γ.profilesFinset, R.μ.real (R.fiber Γ a) • Γ.improvementSet a

/-- **Corollary 14, the formula** (RULINGS 10, 11; erratum D7): under Assumptions 1 and 2,
with room for tokens, the safely achievable expected payoffs are exactly the weighted
Minkowski sum `∑ₐ P(Π(Γ) = a) • {y ∈ C(Γ) | y ≥ u(a)}`.  "⊆" is Lemma 13's conditional
expectations; "⊇" is the reassignment of each outcome to its chosen improvement.

Paper node: `Corollary 14` -/
theorem achievable_eq_improvementSum (Γ : Game N 𝒜)
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty)
    (h : Γ.reduce.HasRoomOutside Γ.S) : R.achievable Γ = R.improvementSum Γ := by
  classical
  ext y
  constructor
  · rintro ⟨T, hT, rfl⟩
    unfold tokenValue
    rw [R.integral_eq_sum_condExp Γ _ (R.integrable_comp_play_pi T.game T.ue _)]
    refine Set.finsetSum_mem_finsetSum _ _ _ fun a ha => ?_
    by_cases hs : a ∈ R.support Γ
    · exact Set.smul_mem_smul_set ⟨R.condExp_mem_feasible Γ hs fun b hb => T.ue_mem b hb,
        R.le_condExp_of_isSPI Γ hs hT⟩
    · have h0 : R.μ.real (R.fiber Γ a) = 0 := by
        have : R.μ (R.fiber Γ a) = 0 := not_not.1 ((R.mem_support_iff Γ a).not.1 hs)
        rw [Measure.real, this, ENNReal.toReal_zero]
      rw [h0, zero_smul]
      have := Set.smul_mem_smul_set (a := (0 : ℝ))
        (Γ.u_mem_improvementSet (Γ.mem_profilesFinset.1 ha))
      rwa [zero_smul] at this
  · intro hy
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).1 hy
    choose k hk hgk using fun a (ha : a ∈ Γ.profilesFinset) => Set.mem_smul_set.1 (hg ha)
    set f : (∀ i, 𝒜 i) → N → ℝ := fun a =>
      if ha : a ∈ Γ.profilesFinset then k a ha else Γ.u a with hfdef
    have hf : ∀ a ∈ Γ.reduce.profiles, f a ∈ Γ.feasible := by
      intro a ha
      have ha' : a ∈ Γ.profilesFinset :=
        Γ.mem_profilesFinset.2 (Γ.reduce_isSubsetGameOf.profiles_subset ha)
      simp only [hfdef, dif_pos ha']
      exact (hk a ha').1
    have hge : ∀ a, Γ.u a ≤ f a := by
      intro a
      by_cases ha : a ∈ Γ.profilesFinset
      · simp only [hfdef, dif_pos ha]; exact (hk a ha).2
      · simp only [hfdef, dif_neg ha]; exact le_rfl
    obtain ⟨T, -, hT⟩ := Play.exists_tokenGame_ue_eq hA1 hA2 Γ h f hf
    refine ⟨T, ?_, ?_⟩
    · filter_upwards [hT] with ω hω
      rw [hω]; exact hge _
    · unfold tokenValue
      rw [R.integral_eq_sum_condExp Γ _ (R.integrable_comp_play_pi T.game T.ue _)]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [← hgk a ha]
      by_cases hs : a ∈ R.support Γ
      · have e : R.condExp Γ a (fun ω => T.ue (R.play T.game ω)) =
            R.condExp Γ a (fun ω => f (R.play Γ ω)) :=
          integral_congr_ae (R.ae_cond_of_ae Γ a hT)
        rw [e, R.condExp_comp_play Γ hs]
        simp only [hfdef, dif_pos ha]
      · have h0 : R.μ.real (R.fiber Γ a) = 0 := by
          have : R.μ (R.fiber Γ a) = 0 := not_not.1 ((R.mem_support_iff Γ a).not.1 hs)
          rw [Measure.real, this, ENNReal.toReal_zero]
        rw [h0, zero_smul, zero_smul]

/-- **Corollary 14, convexity**: the safely achievable set is convex.

Paper node: `Corollary 14` -/
theorem convex_achievable (Γ : Game N 𝒜)
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty)
    (h : Γ.reduce.HasRoomOutside Γ.S) : Convex ℝ (R.achievable Γ) := by
  rw [R.achievable_eq_improvementSum Γ hA1 hA2 h]
  unfold improvementSum
  refine Finset.sum_induction _ (fun s => Convex ℝ s) (fun s t hs ht => hs.add ht) ?_
    fun a _ => (Γ.convex_improvementSet a).smul _
  rw [← Set.singleton_zero]; exact convex_singleton 0

/-- The safely achievable set is compact. -/
lemma isCompact_achievable (Γ : Game N 𝒜)
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty)
    (h : Γ.reduce.HasRoomOutside Γ.S) : IsCompact (R.achievable Γ) := by
  rw [R.achievable_eq_improvementSum Γ hA1 hA2 h]
  unfold improvementSum
  refine Finset.sum_induction _ (fun s => IsCompact s) (fun s t hs ht => hs.add ht) ?_
    fun a _ => (Γ.isCompact_improvementSet a).smul _
  rw [← Set.singleton_zero]; exact isCompact_singleton

omit [∀ i, DecidableEq (𝒜 i)] in
/-- `C(Γ)` is a polytope. -/
lemma _root_.SafeParetoImprovements.Game.isPolytope_feasible (Γ : Game N 𝒜) : IsPolytope Γ.feasible := by
  rw [Game.feasible_eq_convexHull]
  exact IsPolytope.of_finite ((Set.Finite.ofFinset Γ.profilesFinset fun _ => Γ.mem_profilesFinset).image Γ.u)

omit [∀ i, DecidableEq (𝒜 i)] in
/-- `{y ∈ C(Γ) | y ≥ u(a)}` is a polytope: a polytope cut by an orthant. -/
lemma _root_.SafeParetoImprovements.Game.isPolytope_improvementSet (Γ : Game N 𝒜) (a : ∀ i, 𝒜 i) :
    IsPolytope (Γ.improvementSet a) :=
  Γ.isPolytope_feasible.inter_Ici (Γ.u a)

/-- **Corollary 14, the polytope clause** (RULING 12): the safely achievable set is the convex
hull of finitely many points — the paper's "convex polygon", for any number of players.
Each summand `{y ∈ C(Γ) | y ≥ u(a)}` is a polytope cut by an orthant
(`IsPolytope.inter_Ici`), and polytopes are closed under scaling and Minkowski sums.

Paper node: `Corollary 14` -/
theorem isPolytope_achievable (Γ : Game N 𝒜)
    (hA1 : R.toPlay.SatisfiesA1 R.certainty) (hA2 : R.toPlay.SatisfiesA2 R.certainty)
    (h : Γ.reduce.HasRoomOutside Γ.S) : IsPolytope (R.achievable Γ) := by
  rw [R.achievable_eq_improvementSum Γ hA1 hA2 h]
  exact IsPolytope.finsetSum _ fun a _ => (Γ.isPolytope_improvementSet a).smul _

end Representatives

end SafeParetoImprovements
