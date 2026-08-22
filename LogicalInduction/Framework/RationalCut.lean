import LogicalInduction.Framework.Expectations

/-!
# Rational-cut semantics for abstract LUVs

A completed propositional world values an abstract `LUV` whenever its true rational
thresholds form a bounded downward cut.  This module contains only that generic semantic
fact; it is independent of any source-presentation or executable-certificate mechanism.
-/

namespace LogicalInduction

open Set

/-- The completed-world content of a genuine paper `[0,1]` LUV. -/
structure PCWorld.RationalCutAt (v : PCWorld) (X : LUV) : Prop where
  below_zero : ∀ r : ℚ, (r : ℝ) < 0 → v.Holds (X.gt r)
  above_one : ∀ r : ℚ, 1 < (r : ℝ) → ¬v.Holds (X.gt r)
  downward : ∀ r s : ℚ, r < s → v.Holds (X.gt s) → v.Holds (X.gt r)

namespace PCWorld.RationalCutAt

variable {v : PCWorld} {X : LUV}

/-- The real set represented by the true rational thresholds of a cut. -/
def carrier (v : PCWorld) (X : LUV) : Set ℝ :=
  {x | ∃ r : ℚ, (r : ℝ) = x ∧ v.Holds (X.gt r)}

lemma carrier_nonempty (h : v.RationalCutAt X) : (carrier v X).Nonempty := by
  refine ⟨(-1 : ℝ), (-1 : ℚ), by norm_num, ?_⟩
  exact h.below_zero (-1) (by norm_num)

lemma carrier_bddAbove (h : v.RationalCutAt X) : BddAbove (carrier v X) := by
  refine ⟨1, ?_⟩
  rintro x ⟨r, rfl, hr⟩
  exact le_of_not_gt (fun hgt => h.above_one r hgt hr)

/-- A bounded downward rational cut determines a repository LUV value. -/
lemma exists_valuesAt (h : v.RationalCutAt X) : ∃ x : ℝ, v.ValuesAt X x := by
  let S := carrier v X
  have hSne : S.Nonempty := h.carrier_nonempty
  have hSbdd : BddAbove S := h.carrier_bddAbove
  refine ⟨sSup S, ?_, ?_, ?_⟩
  · by_contra hnonneg
    have hsupneg : sSup S < 0 := lt_of_not_ge hnonneg
    obtain ⟨r, hsup_r, hr0⟩ := exists_rat_btwn hsupneg
    have hrS : (r : ℝ) ∈ S := ⟨r, rfl, h.below_zero r hr0⟩
    exact (not_le_of_gt hsup_r) (le_csSup hSbdd hrS)
  · apply csSup_le hSne
    rintro x ⟨r, rfl, hr⟩
    exact le_of_not_gt (fun hgt => h.above_one r hgt hr)
  · intro r
    constructor
    · intro hr
      obtain ⟨y, ⟨s, hs, hsHolds⟩, hry⟩ := exists_lt_of_lt_csSup hSne hr
      subst y
      have hrs : r < s := by exact_mod_cast hry
      exact h.downward r s hrs hsHolds
    · intro hr hHolds
      have hrS : (r : ℝ) ∈ S := ⟨r, rfl, hHolds⟩
      exact (not_le_of_gt hr) (le_csSup hSbdd hrS)

/-- The represented value is canonical, even though truth at a threshold equal to the
value may remain undecided. -/
lemma valuesAt_iff_sSup (h : v.RationalCutAt X) {x : ℝ} :
    v.ValuesAt X x ↔ x = sSup (carrier v X) := by
  have value_eq (z : ℝ) (hz : v.ValuesAt X z) : z = sSup (carrier v X) := by
    apply le_antisymm
    · by_contra hle
      obtain ⟨r, hsup_r, hrz⟩ := exists_rat_btwn (lt_of_not_ge hle)
      have hrHolds := (hz.2.2 r).1 hrz
      exact (not_le_of_gt hsup_r)
        (le_csSup h.carrier_bddAbove ⟨r, rfl, hrHolds⟩)
    · apply csSup_le h.carrier_nonempty
      rintro y ⟨r, rfl, hrHolds⟩
      exact le_of_not_gt (fun hzr => (hz.2.2 r).2 hzr hrHolds)
  constructor
  · exact value_eq x
  · intro hx
    obtain ⟨y, hy⟩ := h.exists_valuesAt
    rw [hx, ← value_eq y hy]
    exact hy

end PCWorld.RationalCutAt

#print axioms PCWorld.RationalCutAt.exists_valuesAt
#print axioms PCWorld.RationalCutAt.valuesAt_iff_sSup

end LogicalInduction
