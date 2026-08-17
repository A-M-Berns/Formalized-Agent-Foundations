import ShannonInformation.API
import APITests.ShannonInformationInequalities

/-! # Client-style tests for the derived corpus at `FiniteEntropyOf`

`ShannonInformation/FiniteEntropy/Derived.lean` restates the rest of
`PFR/ForMathlib/Entropy/Basic.lean`'s `FiniteRange`-gated corpus — data processing, entropy
under maps, mutual information as `H[X] - H[X | Y]`, and identically-distributed invariance —
over `FiniteEntropyOf`.  Together with `ChainRule.lean`'s `condMutualInfo_eq` this is Phase 4a
of `Condensation/notes/finite-range-generalization-plan.md`.

The file checks the same two things its siblings do:

* **nothing regressed** — for `Fintype`-valued variables every statement applies with its
  instance arguments discharged by `infer_instance`;
* **something was gained** — the same statements apply to the infinite-range geometric pair
  `geomPair` of `APITests/ShannonInformationInequalities.lean`, which no `FiniteRange`
  instance can reach.

It also pins down the **disambiguation idiom**, which is the one ergonomic cost of having two
parallel surfaces: see the last section. -/

open MeasureTheory ProbabilityTheory Real
open APITests.ShannonInformationInequalities (geomPair triv not_finiteRange_fst)

namespace APITests.ShannonInformationDerived

/-! ### Regression: `Fintype`-valued variables still work with no user input -/

section Finite

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U] [Fintype S] [MeasurableSingletonClass S] [Fintype T]
  [MeasurableSingletonClass T] [Fintype U] [MeasurableSingletonClass U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω} [IsProbabilityMeasure μ]

example (hX : Measurable X) (f : S → U) : H[f ∘ X ; μ] ≤ H[X ; μ] :=
  ShannonInformation.entropy_comp_le μ hX f

example (hX : Measurable X) (hY : Measurable Y) (f : S → T) (g : T → S) (h1 : Y = f ∘ X)
    (h2 : X = g ∘ Y) : H[X ; μ] = H[Y ; μ] :=
  ShannonInformation.entropy_of_comp_eq_of_comp μ hX hY f g h1 h2

example (hX : Measurable X) {f : S → U} (hf : Measurable f) :
    H[X | f ∘ X ; μ] = H[X ; μ] - H[f ∘ X ; μ] :=
  ShannonInformation.condEntropy_comp_self μ hX hf

example (hX : Measurable X) (hY : Measurable Y) (f : T → U) (hf : Function.Injective f)
    (hfY : Measurable (f ∘ Y)) : H[X | f ∘ Y ; μ] = H[X | Y ; μ] :=
  ShannonInformation.condEntropy_of_injective' μ hX hY f hf hfY

example (hX : Measurable X) (hY : Measurable Y) : I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] :=
  ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy hX hY μ

example (hX : Measurable X) (hY : Measurable Y) : I[X : Y ; μ] = H[Y ; μ] - H[Y | X ; μ] :=
  ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy' hX hY μ

example (hX : Measurable X) (hY : Measurable Y) (f : S → U) :
    H[Y | f ∘ X ; μ] ≥ H[Y | X ; μ] :=
  ShannonInformation.condEntropy_comp_ge μ hX hY f

example (hX : Measurable X) (hY : Measurable Y) (f : S → U) :
    I[f ∘ X : Y ; μ] ≤ I[X : Y ; μ] :=
  ShannonInformation.mutual_comp_le μ hX hY f

example (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] = H[X | Z ; μ] + H[Y | Z ; μ] - H[⟨X, Y⟩ | Z ; μ] :=
  ShannonInformation.condMutualInfo_eq hX hY hZ μ

example (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    I[X : Y | Z ; μ] = H[X | Z ; μ] - H[X | ⟨Y, Z⟩ ; μ] :=
  ShannonInformation.condMutualInfo_eq' hX hY hZ μ

example {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X' : Ω' → S} {Y' : Ω' → T} (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (hY' : Measurable Y') (h : IdentDistrib (⟨X, Y⟩) (⟨X', Y'⟩) μ μ') :
    H[X | Y ; μ] = H[X' | Y' ; μ'] :=
  ShannonInformation.IdentDistrib.condEntropy_eq hX hY hX' hY' h

end Finite

/-! ### The gain: the same corpus on an infinite-range witness

`geomPair` is the product of two copies of `Geometric(1/2)` on `ℕ`, with the coordinate
projections as the variables; `not_finiteRange_fst` records that no vendored `FiniteRange`
statement applies to it. -/

section Infinite

/-- The witness really is outside the vendored fragment. -/
example : ¬ FiniteRange (Prod.fst : ℕ × ℕ → ℕ) := not_finiteRange_fst

/-- Data processing at infinite range: coarsening a geometric coordinate to its parity cannot
increase entropy. -/
example : H[(fun n ↦ n % 2) ∘ (Prod.fst : ℕ × ℕ → ℕ) ; geomPair]
    ≤ H[(Prod.fst : ℕ × ℕ → ℕ) ; geomPair] :=
  ShannonInformation.entropy_comp_le geomPair measurable_fst (fun n ↦ n % 2)

example : H[(Prod.fst : ℕ × ℕ → ℕ) | (fun n ↦ n % 2) ∘ (Prod.fst : ℕ × ℕ → ℕ) ; geomPair]
    = H[(Prod.fst : ℕ × ℕ → ℕ) ; geomPair]
      - H[(fun n ↦ n % 2) ∘ (Prod.fst : ℕ × ℕ → ℕ) ; geomPair] :=
  ShannonInformation.condEntropy_comp_self geomPair measurable_fst
    (measurable_of_countable fun n ↦ n % 2)

example : H[(Prod.snd : ℕ × ℕ → ℕ) | (fun n ↦ n % 2) ∘ (Prod.fst : ℕ × ℕ → ℕ) ; geomPair]
    ≥ H[(Prod.snd : ℕ × ℕ → ℕ) | (Prod.fst : ℕ × ℕ → ℕ) ; geomPair] :=
  ShannonInformation.condEntropy_comp_ge geomPair measurable_fst measurable_snd fun n ↦ n % 2

example : I[(fun n ↦ n % 2) ∘ (Prod.fst : ℕ × ℕ → ℕ) : (Prod.snd : ℕ × ℕ → ℕ) ; geomPair]
    ≤ I[(Prod.fst : ℕ × ℕ → ℕ) : (Prod.snd : ℕ × ℕ → ℕ) ; geomPair] :=
  ShannonInformation.mutual_comp_le geomPair measurable_fst measurable_snd fun n ↦ n % 2

/-- `I[X : Y] = H[X] - H[X | Y]` on the infinite-range pair.  Combined with
`APITests.ShannonInformationInequalities.mutualInfo_geomPair` this says the two coordinates
carry no information about each other: `H[X | Y] = H[X]`. -/
example : I[(Prod.fst : ℕ × ℕ → ℕ) : (Prod.snd : ℕ × ℕ → ℕ) ; geomPair]
    = H[(Prod.fst : ℕ × ℕ → ℕ) ; geomPair]
      - H[(Prod.fst : ℕ × ℕ → ℕ) | (Prod.snd : ℕ × ℕ → ℕ) ; geomPair] :=
  ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy measurable_fst measurable_snd
    geomPair

/-- …and here that consequence is actually derived, on a pair no `FiniteRange` theorem can
touch. -/
example : H[(Prod.fst : ℕ × ℕ → ℕ) | (Prod.snd : ℕ × ℕ → ℕ) ; geomPair]
    = H[(Prod.fst : ℕ × ℕ → ℕ) ; geomPair] := by
  have h := ShannonInformation.mutualInfo_eq_entropy_sub_condEntropy measurable_fst
    measurable_snd geomPair
  rw [APITests.ShannonInformationInequalities.mutualInfo_geomPair] at h
  linarith

example : I[(Prod.fst : ℕ × ℕ → ℕ) : (Prod.snd : ℕ × ℕ → ℕ) | triv ; geomPair]
    = H[(Prod.fst : ℕ × ℕ → ℕ) | triv ; geomPair]
      + H[(Prod.snd : ℕ × ℕ → ℕ) | triv ; geomPair]
      - H[⟨(Prod.fst : ℕ × ℕ → ℕ), (Prod.snd : ℕ × ℕ → ℕ)⟩ | triv ; geomPair] :=
  ShannonInformation.condMutualInfo_eq (Z := triv) measurable_fst measurable_snd
    measurable_const geomPair

example : I[(Prod.fst : ℕ × ℕ → ℕ) : (Prod.snd : ℕ × ℕ → ℕ) | triv ; geomPair]
    = H[(Prod.fst : ℕ × ℕ → ℕ) | triv ; geomPair]
      - H[(Prod.fst : ℕ × ℕ → ℕ) | ⟨(Prod.snd : ℕ × ℕ → ℕ), triv⟩ ; geomPair] :=
  ShannonInformation.condMutualInfo_eq' (Z := triv) measurable_fst measurable_snd
    measurable_const geomPair

end Infinite

/-! ### The disambiguation idiom

Every name above shadows a `ProbabilityTheory` declaration of the same name.  A client with
both namespaces open must say which it means — and the failure mode is not a nice error but a
*silent* choice: Lean resolves an ambiguous overload by elaboration success, so a bare name
can pick the `FiniteRange` version and then report a missing `FiniteRange` instance from a
line that never mentioned `FiniteRange`.

The idiom is therefore: **write the namespace in full whenever both surfaces are open.**  The
two examples below sit under `open ProbabilityTheory ShannonInformation` and cite the two
versions of the same fact side by side, with the hypotheses each one actually needs. -/

section Disambiguation

open ProbabilityTheory ShannonInformation

variable {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  [Countable S] [MeasurableSingletonClass S] [Countable U] [MeasurableSingletonClass U]
  {X : Ω → S} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]

/-- The vendored version, at `FiniteRange`. -/
example (hX : Measurable X) [FiniteRange X] (f : S → U) : H[f ∘ X ; μ] ≤ H[X ; μ] :=
  ProbabilityTheory.entropy_comp_le μ hX f

/-- The FAF version, at `FiniteEntropyOf` — strictly weaker, and the one to prefer. -/
example (hX : Measurable X) [ShannonInformation.FiniteEntropyOf X μ] (f : S → U) :
    H[f ∘ X ; μ] ≤ H[X ; μ] :=
  ShannonInformation.entropy_comp_le μ hX f

/-- The bridge that makes "strictly weaker" true rather than merely different: a
`FiniteRange` hypothesis discharges the FAF version's instance argument automatically, so
migrating a call site never loses a proof. -/
example (hX : Measurable X) [FiniteRange X] (f : S → U) : H[f ∘ X ; μ] ≤ H[X ; μ] :=
  ShannonInformation.entropy_comp_le μ hX f

end Disambiguation

end APITests.ShannonInformationDerived
