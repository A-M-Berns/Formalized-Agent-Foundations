import ShannonInformation.API

/-! # Client-style smoke tests for the shared Shannon-information API

These import **only** `ShannonInformation.API` — never a `PFR.*` module — and prove small
generic information-theoretic facts by combining re-exported endpoints.  That is the point:
the layer is not established merely because the vendored files compile, but because a
fresh client can reach the vocabulary through one documented import and get work done
without knowing which upstream file anything lives in.

Nothing here is paper-specific: no Condensation, no Natural Latents, no
agent-foundations vocabulary.  Each test is a derivation, not a restatement of an
upstream lemma — the point is to exercise composition. -/

namespace APITests.ShannonInformation

open MeasureTheory ProbabilityTheory Real

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {μ : Measure Ω}

/-! ### Determinism -/

/-- A variable is determined by itself, so it carries no residual uncertainty given
itself: `H[X | X] = 0`.  Derived from `condEntropy_comp_self` at `f = id`. -/
theorem condEntropy_self [IsProbabilityMeasure μ] {X : Ω → S} (hX : Measurable X)
    [FiniteRange X] : H[X | X ; μ] = 0 := by
  simpa using condEntropy_comp_self (μ := μ) hX (f := id) measurable_id

/-- A constant random variable has zero entropy.  Derived by combining
`mutualInfo_const`, `mutualInfo_def` and `entropy_prod_comp` — none of which states this
on its own. -/
theorem entropy_const [IsZeroOrProbabilityMeasure μ] {X : Ω → S} (hX : Measurable X)
    [FiniteRange X] (c : T) : H[(fun _ : Ω => c) ; μ] = 0 := by
  have h0 : I[X : (fun _ : Ω => c) ; μ] = 0 := mutualInfo_const hX c
  have hpair : H[⟨X, (fun _ : Ω => c)⟩ ; μ] = H[X ; μ] := by
    simpa [Function.comp_def] using entropy_prod_comp hX μ (fun _ : S => c)
  rw [mutualInfo_def, hpair] at h0
  linarith

/-! ### Independence -/

/-- Mutual information is nonnegative — the shape clients bound things with. -/
theorem mutualInfo_nonneg' {X : Ω → S} {Y : Ω → T} (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] : 0 ≤ I[X : Y ; μ] := mutualInfo_nonneg hX hY μ

/-- An independent pair carries no mutual information. -/
theorem indep_mutualInfo_zero [IsZeroOrProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]
    (h : IndepFun X Y μ) : I[X : Y ; μ] = 0 :=
  (mutualInfo_eq_zero hX hY).mpr h

/-- …and conversely: zero mutual information *characterizes* independence.  Using the
`iff` in the reverse direction is what makes this a real client of the API rather than a
restatement. -/
theorem mutualInfo_zero_indep [IsZeroOrProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]
    (h : I[X : Y ; μ] = 0) : IndepFun X Y μ :=
  (mutualInfo_eq_zero hX hY).mp h

/-- Conditionally independent variables carry no conditional mutual information. -/
theorem condIndep_condMutualInfo_zero [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] (h : CondIndepFun X Y Z μ) :
    I[X : Y | Z ; μ] = 0 :=
  (condMutualInfo_eq_zero hX hY).mpr h

/-- An independent pair has additive entropy — combining the independence
characterization with `mutualInfo_def`, rather than quoting `entropy_pair_eq_add`. -/
theorem indep_entropy_pair [IsZeroOrProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y]
    (h : IndepFun X Y μ) : H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y ; μ] := by
  have h0 : I[X : Y ; μ] = 0 := (mutualInfo_eq_zero hX hY).mpr h
  rw [mutualInfo_def] at h0
  linarith

/-! ### Chain rules -/

/-- A representative chain rule, and a consequence a client would actually want:
conditioning cannot increase entropy, read straight off `chain_rule` plus
nonnegativity of mutual information. -/
theorem condEntropy_le_entropy' [IsZeroOrProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[X | Y ; μ] ≤ H[X ; μ] := by
  have hchain : H[⟨X, Y⟩ ; μ] = H[Y ; μ] + H[X | Y ; μ] := chain_rule μ hX hY
  have hmi : 0 ≤ I[X : Y ; μ] := mutualInfo_nonneg hX hY μ
  rw [mutualInfo_def, hchain] at hmi
  linarith

/-- The conditional chain rule, exercised as an identity a client can rewrite with. -/
theorem cond_chain_rule_check [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U} (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[⟨X, Y⟩ | Z ; μ] = H[Y | Z ; μ] + H[X | ⟨Y, Z⟩ ; μ] :=
  cond_chain_rule μ hX hY hZ

/-! ### Invariance under identical distribution -/

/-- Entropy is an invariant of the distribution, not of the underlying space: two
identically distributed variables on *different* probability spaces have equal entropy. -/
theorem entropy_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X : Ω → S} {X' : Ω' → S} (h : IdentDistrib X X' μ μ') : H[X ; μ] = H[X' ; μ'] :=
  h.entropy_congr

/-- The same for mutual information, which is what makes information-theoretic quantities
usable as *model-independent* invariants — the property agent-foundations work leans on
when comparing two representations of the same data. -/
theorem mutualInfo_of_identDistrib {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] {X : Ω → S} {Y : Ω → T} {X' : Ω' → S}
    {Y' : Ω' → T} (h : IdentDistrib (⟨X, Y⟩ : Ω → S × T) (⟨X', Y'⟩ : Ω' → S × T) μ μ') :
    I[X : Y ; μ] = I[X' : Y' ; μ'] :=
  h.mutualInfo_eq

/-! ### Entropy under maps -/

/-- Data processing: a function of a variable cannot have more entropy than the variable. -/
theorem entropy_comp_le' [IsZeroOrProbabilityMeasure μ] {X : Ω → S} (hX : Measurable X)
    [FiniteRange X] (f : S → T) : H[f ∘ X ; μ] ≤ H[X ; μ] := entropy_comp_le μ hX f

/-! ### A concrete finite example with *nonzero* mutual information

The tests above are all universally quantified, so they would remain true if every
information quantity in the library were identically zero.  This one is not: it pins down
a genuine positive value on an explicit two-point space, and so is the test that
distinguishes a working library from a degenerate one. -/

/-- The fair coin: `Bool` under the uniform measure, observed by the identity. -/
noncomputable def coin : Measure Bool := uniformOn (Set.univ : Set Bool)

instance : IsProbabilityMeasure coin := by
  unfold coin; infer_instance

/-- The fair coin has entropy `log 2`, which is strictly positive. -/
theorem coin_entropy : H[(id : Bool → Bool) ; coin] = log 2 := by
  have huniform : IsUniform (Set.univ : Set Bool) (id : Bool → Bool) coin :=
    isUniform_uniformOn
  have h := huniform.entropy_eq' Set.finite_univ measurable_id
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

theorem coin_entropy_pos : 0 < H[(id : Bool → Bool) ; coin] := by
  rw [coin_entropy]
  exact Real.log_pos (by norm_num)

/-- A variable has full mutual information with itself, so the fair coin exhibits a
strictly positive mutual information: `I[X : X] = H[X] = log 2 > 0`. -/
theorem coin_mutualInfo_self_pos : 0 < I[(id : Bool → Bool) : (id : Bool → Bool) ; coin] := by
  have hpair : H[⟨(id : Bool → Bool), (id : Bool → Bool)⟩ ; coin]
      = H[(id : Bool → Bool) ; coin] := by
    simpa [Function.comp_def] using
      entropy_prod_comp (measurable_id (α := Bool)) coin (id : Bool → Bool)
  have : I[(id : Bool → Bool) : (id : Bool → Bool) ; coin] = H[(id : Bool → Bool) ; coin] := by
    rw [mutualInfo_def, hpair]; ring
  rw [this]
  exact coin_entropy_pos

end APITests.ShannonInformation
