/-
# Vendoring experiment, part 2: is the ported PFR entropy substrate actually *usable*?

Part 1 established that PFR's entropy closure (25 modules, 6074 lines, taken from PFR
commit `01c9b66`, the last on toolchain v4.31.0) compiles against this repo's pinned
Mathlib after two edits. Compiling is necessary but not sufficient — the question that
decides the Condensation project is whether the library's API is *ergonomic* for this
paper's statements.

This file answers that by proving **Lemma 5.4** of Eisenstat's *Condensation*, the
quantitative core of its §5, directly against the vendored library. It is not a restatement
of a PFR lemma; it is a paper result, and it comes out in a handful of lines.

Build:
  Condensation/spike-build.sh Condensation/VendorSmokeTest.lean
(after `vendor-experiment/.build` has been populated — see SPIKE-REPORT.md §"Reproducing").
-/
module

public import PFR.ForMathlib.Entropy.Basic

public section

namespace CondVendorTest

open MeasureTheory ProbabilityTheory

variable {Ω S T₁ T₂ V : Type*}
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T₁] [MeasurableSpace T₂]
  [MeasurableSpace V]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T₁] [MeasurableSingletonClass T₂]
  [MeasurableSingletonClass V]
  [Countable S] [Countable T₁] [Countable T₂] [Countable V]
  {X : Ω → S} {Y₁ : Ω → T₁} {Y₂ : Ω → T₂} {C : Ω → V}
  {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
  [FiniteRange X] [FiniteRange Y₁] [FiniteRange Y₂] [FiniteRange C]

/-- **Definition 2.3** of *Condensation*, the interaction information
`I(X; Y; Z) = I(X; Y) − I(X; Y | Z)`, in the form §5 uses it: everything additionally
conditioned on `C`. -/
noncomputable def interactionInfo (X : Ω → S) (Y₁ : Ω → T₁) (Y₂ : Ω → T₂) (C : Ω → V)
    (μ : Measure Ω) : ℝ :=
  I[X : Y₁ | C ; μ] - I[X : Y₁ | ⟨Y₂, C⟩ ; μ]

/-- **Lemma 5.4 of *Condensation*, equation (5.6)** — the exact statement:

`H(X | C) = H(X | Y₁, C) + H(X | Y₂, C) − H(X | Y₁, Y₂, C) + I(Y₁; Y₂; X | C)`

The paper calls its own proof "a straightforward if unenlightening calculation". Against
the vendored library it is two rewrites and `ring`. -/
theorem cond_entropy_eq_of_pair
    (hX : Measurable X) (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hC : Measurable C) :
    H[X | C ; μ]
      = H[X | ⟨Y₁, C⟩ ; μ] + H[X | ⟨Y₂, C⟩ ; μ] - H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ]
        + interactionInfo X Y₁ Y₂ C μ := by
  unfold interactionInfo
  rw [condMutualInfo_eq' hX hY₁ hC μ, condMutualInfo_eq' hX hY₁ (hY₂.prodMk hC) μ]
  ring

/-- **Lemma 5.4, equation (5.5)** — the inequality form, in the shape the paper deduces it:
drop `−H(X | Y₁, Y₂, C)` by nonnegativity of conditional entropy. -/
theorem cond_entropy_le_of_pair
    (hX : Measurable X) (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hC : Measurable C) :
    H[X | C ; μ]
      ≤ H[X | ⟨Y₁, C⟩ ; μ] + H[X | ⟨Y₂, C⟩ ; μ] + interactionInfo X Y₁ Y₂ C μ := by
  have h := cond_entropy_eq_of_pair (μ := μ) hX hY₁ hY₂ hC
  have hnn : 0 ≤ H[X | ⟨Y₁, ⟨Y₂, C⟩⟩ ; μ] :=
    condEntropy_nonneg X (⟨Y₁, ⟨Y₂, C⟩⟩) μ
  linarith

/-- Sanity check that the substrate's own nonnegativity facts are reachable at the shapes
§4 of *Condensation* needs (`Proposition 4.2` leans on exactly this). -/
theorem cond_mutual_info_nonneg_check
    (hX : Measurable X) (hY₁ : Measurable Y₁) :
    0 ≤ I[X : Y₁ | C ; μ] :=
  condMutualInfo_nonneg hX hY₁ (Z := C) (μ := μ)

end CondVendorTest

end

section Audit
#print axioms CondVendorTest.cond_entropy_eq_of_pair
#print axioms CondVendorTest.cond_entropy_le_of_pair
end Audit
