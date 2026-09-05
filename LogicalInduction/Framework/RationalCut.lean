import LogicalInduction.Framework.Expectations

/-!
# Rational-cut semantics for abstract LUVs (`def:luv`)

The completed-world half of `def:luv` (tex:1635): a plausible world values an abstract `LUV`
exactly when its true rational thresholds form a bounded downward cut.

* `PCWorld.RationalCutAt v X` — the three cut conditions: every threshold below `0` holds,
  none above `1` does, and truth at a threshold is downward closed.
* `carrier`, with `carrier_nonempty` and `carrier_bddAbove` — the set of reals cut out by the
  true thresholds, and why it has a supremum.
* `exists_valuesAt` — a bounded downward cut determines a `PCWorld.ValuesAt` value
  (`Framework/Expectations.lean`), which is the world–value hypothesis every
  `lem:conluvapprox` consumer takes.
* `valuesAt_iff_sSup` — that value is canonical, namely `sSup (carrier v X)`, even though
  truth at a threshold equal to the value may remain undecided.

The cut hypothesis is discharged for the paper's literal first-order LUVs in
`Construction/Witnesses/PaperLUV.lean` (`PaperLUV.source_valued`) and in
`Construction/Witnesses/CertifiedSource.lean` — this module's only importers besides the
`Framework.lean` roll-up.

**Design.**  The module is deliberately presentation-free and certificate-free: nothing here
mentions emission, fuel, or source syntax, and no declaration takes a code or a fuel bound.
It is the purely semantic half of the LUV story, kept apart from the threshold-code
interfaces of `Framework/Expectations.lean` so that a caller reasoning about worlds never
imports the metering vocabulary.
-/

namespace LogicalInduction

open Set

/-! ## The rational cut -/

/-- The completed-world content of a genuine paper `[0,1]` LUV (`def:luv`): the thresholds
`⌜X > r⌝` the world affirms form a downward cut of `ℚ` bounded into `[0,1]`. -/
structure PCWorld.RationalCutAt (v : PCWorld) (X : LUV) : Prop where
  /-- Every threshold below `0` holds. -/
  below_zero : ∀ r : ℚ, (r : ℝ) < 0 → v.Holds (X.gt r)
  /-- No threshold above `1` holds. -/
  above_one : ∀ r : ℚ, 1 < (r : ℝ) → ¬v.Holds (X.gt r)
  /-- Truth at a threshold is downward closed. -/
  downward : ∀ r s : ℚ, r < s → v.Holds (X.gt s) → v.Holds (X.gt r)

namespace PCWorld.RationalCutAt

variable {v : PCWorld} {X : LUV}

/-! ## The represented value -/

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

/-- **Canonicity of the represented value**, the companion to `exists_valuesAt`: the value a
cut determines is not merely *some* real but exactly `sSup (carrier v X)`, and every
`PCWorld.ValuesAt` value of `X` at `v` is that supremum.  This holds even though truth at a
threshold equal to the value may remain undecided, so a client that has produced a value by
any other route may identify it with the supremum without re-deriving the cut. -/
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

end LogicalInduction
