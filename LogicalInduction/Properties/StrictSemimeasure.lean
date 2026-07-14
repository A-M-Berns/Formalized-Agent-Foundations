/-
# Strict Domination of the Universal Semimeasure (`thm:strict`)

The market argument is separated from the computability-theory separator construction.
The latter is an explicit M7 representation boundary: it must supply the nested finite
separator prefixes, their efficient repetition, joint realizability, and the theorem that
their universal-semimeasure mass tends to zero.  No market price or strict-domination
conclusion occurs in that boundary.
-/
import LogicalInduction.Properties.UniversalSemimeasure

namespace LogicalInduction

open Filter Topology

/-- Concrete interface to the recursively-inseparable separator class used in the paper's
proof of Strict Domination.  `mass_tendsto_zero` is the precise computability-theory fact
to be instantiated from disjoint c.e. sets with no computable separator; the remaining
fields expose the finite prefix theory and its legal syntax preprocessing. -/
structure StrictSeparatorPresentation
    (M : UniversalContinuousSemimeasure) {DP : DeductiveProcess}
    (B : BitPrefixSentences DP) where
  prefixes : ℕ → List Bool
  nested : ∀ i, ∃ rest, prefixes (i + 1) = prefixes i ++ rest
  length_tendsto_atTop : Tendsto (fun i ↦ (prefixes i).length) atTop atTop
  repetition : EfficientRepeatedEnumeration
    (fun i ↦ B.prefixSentence (prefixes i))
  jointly_possible : ∀ n, ∃ v : PCWorld,
    v.ConsistentWith (DP.D n) ∧
      ∀ i, v.Holds (B.prefixSentence (prefixes i))
  mass_tendsto_zero : Tendsto (fun i ↦ M.mass (prefixes i)) atTop (𝓝 0)

/-- General market half of the strict-domination proof. A uniformly possible prefix
theory whose semimeasure mass vanishes has limiting probability bounded below by Uniform
Non-Dogmatism, hence beats every fixed multiple of that semimeasure somewhere. -/
theorem strict_domination_of_null_prefix_theory
    {DP : DeductiveProcess}
    {M : UniversalContinuousSemimeasure}
    {B : BitPrefixSentences DP}
    (P : History) [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (S : StrictSeparatorPresentation M B) :
    ∀ C : ℝ, 0 < C → ∃ i,
      C * M.mass (S.prefixes i) <
        limitingBelief P (B.prefixSentence (S.prefixes i)) := by
  obtain ⟨ε, hε, hlower⟩ := lic_uniform_nonDogmatism P DP
    (fun i ↦ B.prefixSentence (S.prefixes i)) S.repetition
    S.jointly_possible hP
  intro C hC
  have hscaled : Tendsto (fun i ↦ C * M.mass (S.prefixes i)) atTop (𝓝 0) := by
    simpa using S.mass_tendsto_zero.const_mul C
  have hevent : ∀ᶠ i in atTop, C * M.mass (S.prefixes i) < ε :=
    (tendsto_order.1 hscaled).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  exact ⟨N, (hN N le_rfl).trans_le (hlower N)⟩

/-- **Strict Domination of the Universal Semimeasure** (`thm:strict`). The universal
continuous semimeasure does not dominate the logical inductor's limiting prefix beliefs. -/
theorem lic_strict_domination_universalSemimeasure
    {DP : DeductiveProcess}
    {M : UniversalContinuousSemimeasure}
    {B : BitPrefixSentences DP}
    (P : History) [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (S : StrictSeparatorPresentation M B) :
    ∀ C : ℝ, 0 < C → ∃ σ : List Bool,
      limitingBelief P (B.prefixSentence σ) > C * M.mass σ := by
  intro C hC
  obtain ⟨i, hi⟩ := strict_domination_of_null_prefix_theory P hP S C hC
  exact ⟨S.prefixes i, hi⟩

#print axioms strict_domination_of_null_prefix_theory
#print axioms lic_strict_domination_universalSemimeasure

end LogicalInduction
