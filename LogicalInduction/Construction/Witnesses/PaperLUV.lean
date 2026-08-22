import LogicalInduction.Construction.Witnesses.PaperCutLawDP
import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
# Literal first-order LUV frontend

This module starts the thin frontend for the paper's `def:luv`. A value is represented
inside one-sorted arithmetic by a canonical code for a nonnegative fraction `a / b`:
`pairDef q a b` with `0 < b`. The public propositional ABI remains unchanged.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

/-- An arithmetic object is a code for a nonnegative fraction. -/
def paperRatDef : ArithmeticSemisentence 1 :=
  “q. ∃ a, ∃ b, !pairDef q a b ∧ 0 < b”

/-- A coded nonnegative fraction lies in `[0,1]`. -/
def paperRatUnitDef : ArithmeticSemisentence 1 :=
  “q. ∃ a, ∃ b, !pairDef q a b ∧ 0 < b ∧ a ≤ b”

/-- The coded nonnegative fraction is strictly greater than an external rational.
For a negative threshold, well-formedness itself is the literal order fact. Otherwise
comparison is cross multiplication against the canonical numerator and denominator. -/
def paperRatGtDef (r : ℚ) : ArithmeticSemisentence 1 :=
  if r < 0 then paperRatDef
  else
    let an := Semiterm.Operator.numeral ℒₒᵣ r.num.natAbs
    let bn := Semiterm.Operator.numeral ℒₒᵣ r.den
    “q. ∃ c, ∃ d, !pairDef q c d ∧ 0 < d ∧ !!an * d < c * !!bn”

/-- A literal paper `[0,1]`-LUV: one free value variable, with object-level theory
proofs of unique existence and unit-interval membership. Efficiency belongs to the
separate sequence layer. -/
structure PaperLUV (T : ArithmeticTheory) [T.Δ₁] where
  formula : ArithmeticSemisentence 1
  unique : T ⊢ ∃⁰! formula
  unit : T ⊢ ∀⁰ (formula 🡒 paperRatUnitDef)

namespace PaperLUV

variable {T : ArithmeticTheory} [T.Δ₁]

/-- Literal first-order threshold formula `⌜X > r⌝`: every value satisfying `X`
is greater than the represented external rational. No out-of-range threshold is
replaced by a propositional constant. -/
def thresholdFormula (X : PaperLUV T) (r : ℚ) : ArithmeticSentence :=
  ∀⁰ (X.formula 🡒 paperRatGtDef r)

/-- The corresponding ordinary FAF LUV, obtained only by prime decomposition. -/
def toLUV (X : PaperLUV T) : LUV where
  gt r := paperPrimeDecompose (X.thresholdFormula r)

@[simp] lemma toLUV_gt (X : PaperLUV T) (r : ℚ) :
    X.toLUV.gt r = paperPrimeDecompose (X.thresholdFormula r) := rfl

lemma paperRatDef_eval_nat (q : ℕ) :
    paperRatDef.Evalb ![q] ↔
      ∃ c d : ℕ,
        ((c < d ∧ q = d * d + c) ∨ (d ≤ c ∧ q = c * c + c + d)) ∧ 0 < d := by
  simp [paperRatDef, pairDef]

lemma paperRatUnitDef_eval_nat (q : ℕ) :
    paperRatUnitDef.Evalb ![q] ↔
      ∃ c d : ℕ,
        ((c < d ∧ q = d * d + c) ∨ (d ≤ c ∧ q = c * c + c + d)) ∧
          0 < d ∧ c ≤ d := by
  simp [paperRatUnitDef, pairDef]

/-- The rational representation has the intended standard-model meaning. This is the
first compile-checked boundary test for the frontend. -/
lemma paperRatGtDef_eval_nat (r : ℚ) (q : ℕ) (hr : 0 ≤ r) :
    (paperRatGtDef r).Evalb ![q] ↔
      ∃ c d : ℕ,
        ((c < d ∧ q = d * d + c) ∨ (d ≤ c ∧ q = c * c + c + d)) ∧
          0 < d ∧ r.num.natAbs * d < c * r.den := by
  have hnr : ¬r < 0 := not_lt.mpr hr
  simp [paperRatGtDef, hnr, pairDef]

end PaperLUV

#print axioms PaperLUV.paperRatGtDef_eval_nat

end LogicalInduction
