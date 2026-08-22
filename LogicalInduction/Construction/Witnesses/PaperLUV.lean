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

/-- The coded fraction is strictly greater than the external nonnegative rational `a / b`.
The denominator argument is required to be positive by the caller. -/
def paperRatGtDef (a b : ℕ) : ArithmeticSemisentence 1 :=
  let an := Semiterm.Operator.numeral ℒₒᵣ a
  let bn := Semiterm.Operator.numeral ℒₒᵣ b
  “q. ∃ c, ∃ d, !pairDef q c d ∧ 0 < d ∧ !!an * d < c * !!bn”

/-- A literal paper `[0,1]`-LUV: one free value variable, with object-level theory
proofs of unique existence and unit-interval membership. Efficiency belongs to the
separate sequence layer. -/
structure PaperLUV (T : ArithmeticTheory) [T.Δ₁] where
  formula : ArithmeticSemisentence 1
  unique_provable : Bootstrapping.Provable T (Encodable.encode (∃⁰! formula))
  unit_provable : Bootstrapping.Provable T
    (Encodable.encode (∀⁰ (formula 🡒 paperRatUnitDef)))

namespace PaperLUV

variable {T : ArithmeticTheory} [T.Δ₁]

/-- Literal first-order threshold formula `⌜X > r⌝`. Outside `[0,1]` it uses the
theory-independent constants required by the abstract LUV ABI. -/
def thresholdFormula (X : PaperLUV T) (r : ℚ) : ArithmeticProposition :=
  if r < 0 then ⊤
  else if 1 < r then ⊥
  else ∃⁰ (X.formula ⋏ paperRatGtDef r.num.natAbs r.den)

/-- The corresponding ordinary FAF LUV, obtained only by prime decomposition. -/
def toLUV (X : PaperLUV T) : LUV where
  gt r := paperPrimeDecompose (X.thresholdFormula r)

@[simp] lemma toLUV_gt (X : PaperLUV T) (r : ℚ) :
    X.toLUV.gt r = paperPrimeDecompose (X.thresholdFormula r) := rfl

/-- The rational representation has the intended standard-model meaning. This is the
first compile-checked boundary test for the frontend. -/
lemma paperRatGtDef_eval_nat (a b q : ℕ) :
    (paperRatGtDef a b).Evalb ![q] ↔
      ∃ c d : ℕ,
        ((c < d ∧ q = d * d + c) ∨ (d ≤ c ∧ q = c * c + c + d)) ∧
          0 < d ∧ a * d < c * b := by
  simp [paperRatGtDef, pairDef]

end PaperLUV

#print axioms PaperLUV.paperRatGtDef_eval_nat

end LogicalInduction
