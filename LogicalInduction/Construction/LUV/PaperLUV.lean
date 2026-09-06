import LogicalInduction.Construction.Paper.TheoremDP
import LogicalInduction.Framework.Expectations
import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
# Literal first-order LUV frontend

`def:luv` (tex:1635) as a literal first-order object: the paper's own logically uncertain
variable, rather than the abstract threshold carrier the rest of the development consumes.

Objects defined: `paperRatDef`, `paperRatUnitDef` and `paperRatGtDef r` — the ℒₒᵣ formulas
saying that a coded value is a nonnegative fraction, that it lies in `[0,1]`, and that it
exceeds an external rational — and the structure `PaperLUV T`, whose fields `unique` and
`unit` are object-level `T`-derivations rather than Lean-level side conditions.

The compilation into the carrier is `thresholdFormula` (the literal `⌜X > r⌝`), `toLUV`
(prime decomposition only) and the `@[simp]` `toLUV_gt`.

Main results: `threshold_provable_of_neg`, `threshold_refutable_of_one_lt` and
`threshold_downward_provable` — the three rational-cut obligations, each proved by
completeness over models of `T` — assembled into `rationalCutAt` and hence `source_valued`,
which *derives* the world value rather than assuming it.

The frontend is imported by `Construction/LUV/SourceCodec.lean` and reaches
`Construction/LUV/ArithmeticSource.lean`,
`Construction/Quotation/ExactProduct.lean`, `Construction/Quotation/RepresentedWeight.lean`,
`Construction/Quotation/ExactCCEE.lean` and `Construction/Knowledge/Endpoints.lean` through it.  It
is inhabited at concrete families in the `unitFracPaperLUVSeq` / `dyadicPaperLUVSeq` lane.
`Framework/Expectations.lean` and `Construction/LUV/Arithmetic.lean` are upstream of this
module and refer to it in prose only.

Representation choice, and what it repairs (**PE9**, `notes/paper-errata.md`): the paper
needs a coding of ℚ for `def:luv` and defers it — tex:1633 says Θ must "be capable of
representing rational numbers" and discharges that by assuming Θ can represent computable
functions, which tex:600-606 defines only for `f : ℕ⁺ → ℕ⁺`, naming the value by a numeral
— and then tex:1655 applies `γ_f` to a `[0,1]`-valued `f` regardless. Here the object-level
value is named by a numerator/positive-denominator pair code (`pairDef q a b` with `0 < b`)
rather than by a canonical rational arithmetic inside ℒₒᵣ; `paperRatGtDef_eval_nat` pins
down what that code means in the standard model.
The representation is **ordered-value, not canonical**: distinct codes such as `1/2` and
`2/4` stay distinct object codes, `unique` fixes only which code the formula selects, and
the thresholds determine the external cut.  That is exactly what LUV expectation semantics
consumes — the represented real is recovered through the rational cut, never through
internal normalization — so arithmetic or equality closure *between* LUV values is a scope
boundary of this frontend rather than a gap in `def:luv`.
The `[𝗜𝚺₁ ⪯ T]` binder on the three threshold lemmas is where the rational-cut arithmetic is
indexed, as the README records; efficiency belongs to the separate sequence layer, not here.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder.Arithmetic

/-! ## The rational value code -/

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

/-! ## The literal paper LUV -/

/-- A literal paper `[0,1]`-LUV: one free value variable, with object-level theory
proofs of unique existence and unit-interval membership. Efficiency belongs to the
separate sequence layer.

This is the paper's definition rendered directly: the formula is an actual
`ArithmeticSemisentence 1`, and `unique`/`unit` are derivations in `T`, not Lean-level
side conditions. `toLUV` compiles it into the abstract threshold carrier the rest of the
development consumes, and `source_valued` derives the world value rather than assuming
it. The object-level value is named by a numerator/positive-denominator pair code.
Paper node: `def:luv` -/
structure PaperLUV (T : ArithmeticTheory) [T.Δ₁] where
  formula : ArithmeticSemisentence 1
  unique : T ⊢ ∃⁰! formula
  unit : T ⊢ ∀⁰ (formula 🡒 paperRatUnitDef)

namespace PaperLUV

variable {T : ArithmeticTheory} [T.Δ₁]

/-! ## Threshold formulas and the abstract carrier -/

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

/-- The coded-fraction comparison has the intended meaning in the standard model: `q` codes
`c / d` with `0 < d`, and the comparison is the cross multiplication
`r.num * d < c * r.den`.  This is the adequacy check for the pair-code representation the
module header discloses. -/
lemma paperRatGtDef_eval_nat (r : ℚ) (q : ℕ) (hr : 0 ≤ r) :
    (paperRatGtDef r).Evalb ![q] ↔
      ∃ c d : ℕ,
        ((c < d ∧ q = d * d + c) ∨ (d ≤ c ∧ q = c * c + c + d)) ∧
          0 < d ∧ r.num.natAbs * d < c * r.den := by
  have hnr : ¬r < 0 := not_lt.mpr hr
  simp [paperRatGtDef, hnr, pairDef]

/-- `T` proves `⌜X > r⌝` for every negative `r`: below zero, well-formedness of the value
code is itself the order fact. -/
lemma threshold_provable_of_neg [𝗜𝚺₁ ⪯ T]
    (X : PaperLUV T) (r : ℚ) (hr : r < 0) :
    T ⊢ X.thresholdFormula r := by
  apply LO.FirstOrder.Arithmetic.complete T
  intro (M : Type) _ hM
  letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
  have hunit := models_of_provable hM X.unit
  simp [models_iff, thresholdFormula, paperRatGtDef, hr,
    paperRatUnitDef, paperRatDef] at hunit ⊢
  intro q hX
  obtain ⟨a, b, hpair, hb, hab⟩ := hunit q hX
  exact ⟨a, b, hpair, hb⟩

private lemma den_lt_numNatAbs_of_one_lt {r : ℚ} (hr : 1 < r) :
    r.den < r.num.natAbs := by
  have hnum : 0 ≤ r.num := Rat.num_nonneg.mpr (le_trans zero_le_one hr.le)
  have hcross : (r.den : ℤ) < r.num := by
    simpa [Rat.lt_iff] using hr
  exact_mod_cast (show (r.den : ℤ) < (r.num.natAbs : ℤ) by
    simpa [Int.natAbs_of_nonneg hnum] using hcross)

private lemma rat_cross_lt_of_nonneg {r s : ℚ} (hr : 0 ≤ r) (hrs : r < s) :
    r.num.natAbs * s.den < s.num.natAbs * r.den := by
  have hs : 0 ≤ s := hr.trans hrs.le
  have hrnum : 0 ≤ r.num := Rat.num_nonneg.mpr hr
  have hsnum : 0 ≤ s.num := Rat.num_nonneg.mpr hs
  have hcross : r.num * (s.den : ℤ) < s.num * (r.den : ℤ) := by
    simpa [Rat.lt_iff] using hrs
  exact_mod_cast (show
      (r.num.natAbs : ℤ) * (s.den : ℤ) <
        (s.num.natAbs : ℤ) * (r.den : ℤ) by
    simpa [Int.natAbs_of_nonneg hrnum, Int.natAbs_of_nonneg hsnum] using hcross)

/-- `T` refutes `⌜X > r⌝` for `r > 1`, from the `unit` derivation and cross
multiplication. -/
lemma threshold_refutable_of_one_lt [𝗜𝚺₁ ⪯ T]
    (X : PaperLUV T) (r : ℚ) (hr : 1 < r) :
    T ⊢ ∼X.thresholdFormula r := by
  apply LO.FirstOrder.Arithmetic.complete T
  intro (M : Type) _ hM
  letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
  have hex := models_of_provable hM X.unique
  have hunit := models_of_provable hM X.unit
  simp [models_iff, thresholdFormula] at hex hunit ⊢
  obtain ⟨q, hq, _⟩ := hex
  refine ⟨q, hq, ?_⟩
  obtain ⟨a, b, hpair, hb, hab⟩ := by
    simpa [paperRatUnitDef] using hunit q hq
  intro hgt
  have hnonneg : ¬r < 0 := not_lt.mpr (le_trans zero_le_one hr.le)
  obtain ⟨c, d, hpair', hd, hcd⟩ := by
    simpa [paperRatGtDef, hnonneg] using hgt
  have hac : a = c ∧ b = d :=
    LO.FirstOrder.Arithmetic.pair_ext_iff.mp (hpair.symm.trans hpair')
  rcases hac with ⟨rfl, rfl⟩
  have hden : (r.den : M) < (r.num.natAbs : M) := by
    exact_mod_cast den_lt_numNatAbs_of_one_lt hr
  have hdenmul : (r.den : M) * b < (r.num.natAbs : M) * b :=
    mul_lt_mul_of_pos_right hden hb
  have hamul : a * (r.den : M) ≤ b * (r.den : M) :=
    mul_le_mul_of_nonneg_right hab (by positivity)
  have hirr : (r.num.natAbs : M) * b < (r.num.natAbs : M) * b := calc
    (r.num.natAbs : M) * b < a * (r.den : M) := by
      simpa [LO.FirstOrder.Arithmetic.numeral_eq_natCast] using hcd
    _ ≤ b * (r.den : M) := hamul
    _ = (r.den : M) * b := by ac_rfl
    _ < (r.num.natAbs : M) * b := hdenmul
  exact _root_.lt_irrefl _ hirr

/-- `T` proves `⌜X > s⌝ → ⌜X > r⌝` for `r < s`: the thresholds are downward closed at the
object level. -/
lemma threshold_downward_provable [𝗜𝚺₁ ⪯ T]
    (X : PaperLUV T) (r s : ℚ) (hrs : r < s) :
    T ⊢ (X.thresholdFormula s 🡒 X.thresholdFormula r) := by
  apply LO.FirstOrder.Arithmetic.complete T
  intro (M : Type) _ hM
  letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
    Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
    ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
  have hunit := models_of_provable hM X.unit
  simp [models_iff, thresholdFormula] at hunit ⊢
  intro hs q hq
  by_cases hr : r < 0
  · obtain ⟨a, b, hpair, hb, hab⟩ := by
      simpa [paperRatUnitDef] using hunit q hq
    simpa [paperRatGtDef, hr, paperRatDef] using
      (show ∃ a b, q = LO.FirstOrder.Arithmetic.pair a b ∧ 0 < b from
        ⟨a, b, hpair, hb⟩)
  · have hr0 : 0 ≤ r := le_of_not_gt hr
    have hs0 : ¬s < 0 := not_lt.mpr (hr0.trans hrs.le)
    obtain ⟨c, d, hpair, hd, hsd⟩ := by
      simpa [paperRatGtDef, hs0] using hs q hq
    have hcross :
        (r.num.natAbs : M) * (s.den : M) <
          (s.num.natAbs : M) * (r.den : M) := by
      exact_mod_cast rat_cross_lt_of_nonneg hr0 hrs
    have hrden : (0 : M) < (r.den : M) := by exact_mod_cast r.den_pos
    have hsden : (0 : M) < (s.den : M) := by exact_mod_cast s.den_pos
    have h1 := mul_lt_mul_of_pos_right hcross hd
    have h2 := mul_lt_mul_of_pos_right
      (show (s.num.natAbs : M) * d < c * (s.den : M) by
        simpa [LO.FirstOrder.Arithmetic.numeral_eq_natCast] using hsd)
      hrden
    have hmul :
        ((r.num.natAbs : M) * d) * (s.den : M) <
          (c * (r.den : M)) * (s.den : M) := calc
      ((r.num.natAbs : M) * d) * (s.den : M) =
          ((r.num.natAbs : M) * (s.den : M)) * d := by ac_rfl
      _ < ((s.num.natAbs : M) * (r.den : M)) * d := h1
      _ = ((s.num.natAbs : M) * d) * (r.den : M) := by ac_rfl
      _ < (c * (s.den : M)) * (r.den : M) := h2
      _ = (c * (r.den : M)) * (s.den : M) := by ac_rfl
    have hrd : (r.num.natAbs : M) * d < c * (r.den : M) :=
      lt_of_mul_lt_mul_right hmul hsden.le
    simpa [paperRatGtDef, hr, LO.FirstOrder.Arithmetic.numeral_eq_natCast] using
      (show ∃ c d, q = LO.FirstOrder.Arithmetic.pair c d ∧ 0 < d ∧
          (r.num.natAbs : M) * d < c * (r.den : M) from
        ⟨c, d, hpair, hd, hrd⟩)

/-! ## The rational cut, and the derived world value -/

/-- The three threshold obligations together form a `RationalCutAt` for the compiled LUV, in
every world consistent with `paperTheoryDP T`. -/
lemma rationalCutAt [𝗜𝚺₁ ⪯ T]
    (X : PaperLUV T) (v : PCWorld)
    (hv : v.ConsistentWithTheory (paperTheoryDP T)) :
    v.RationalCutAt X.toLUV := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have hr' : r < 0 := by exact_mod_cast hr
    exact PCWorld.holds_paperPrimeDecompose_of_provable T v hv _
      (X.threshold_provable_of_neg r hr')
  · intro r hr
    have hr' : 1 < r := by exact_mod_cast hr
    have hneg := PCWorld.holds_paperPrimeDecompose_of_provable T v hv _
      (X.threshold_refutable_of_one_lt r hr')
    have hneg' : v.Holds
        (paperPrimeDecompose (∼(X.thresholdFormula r : ArithmeticProposition))) := by
      simpa [LogicalConnective.HomClass.map_neg] using hneg
    exact (v.holds_paperPrimeDecompose_neg _).mp hneg'
  · intro r s hrs hs
    have himp := PCWorld.holds_paperPrimeDecompose_of_provable T v hv _
      (X.threshold_downward_provable r s hrs)
    have himp' : v.Holds (paperPrimeDecompose
        ((X.thresholdFormula s : ArithmeticProposition) 🡒
          (X.thresholdFormula r : ArithmeticProposition))) := by
      simpa [LogicalConnective.HomClass.map_imply] using himp
    exact (v.holds_paperPrimeDecompose_imp _ _).mp himp' hs

/-- Every completed public world of the canonical first-order theorem process assigns a
real value to the abstract LUV compiled from a literal paper LUV.  This is what makes the
frontend's world value *derived* rather than assumed.
Paper node: `def:luv` -/
lemma source_valued [𝗜𝚺₁ ⪯ T]
    (X : PaperLUV T) :
    ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
      ∃ x : ℝ, v.ValuesAt X.toLUV x := by
  intro v hv
  exact (X.rationalCutAt v hv).exists_valuesAt

end PaperLUV

end LogicalInduction
