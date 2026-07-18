import LogicalInduction.Construction.M7Witnesses

/-!
# Concrete feedback-trader emission (`M7-FEEDBACK-EMIT`)

The feedback trader is indexed by a deferral function whose program runs in time
polynomial in its *output*, not necessarily in its input.  On day `n` we therefore run
that program only for the polynomial clock justified when its output is exactly `n`.
Successful runs are sound by partial-function uniqueness; unfinished runs emit no trade.

This file turns that bounded schedule into the literal coefficient/sentence streams of
`AffineCombination.feedbackTrader`.  It contains no market or convergence argument.
-/

namespace LogicalInduction
namespace FeedbackEmission

open AffineCombination PrefixPatchCompile

-- Deep products below use `Nat.unpair` through `Primcodable`; keep its square-root
-- implementation opaque during elaboration (the standard `dd:fuel` compiler gotcha).
attribute [local irreducible] Nat.sqrt

/-- Run the deferral program for component `k` with the day-`n` polynomial clock.
Input is `⟨n,k⟩`; output is normalized as `0` for unfinished and `f k + 1` for finished. -/
def scheduledRun (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  deadlineRun f (ecClock a degree z.unpair.1) z.unpair.2

/-- The bounded scheduled run is polynomial in the paired day/component input. -/
theorem scheduledRun_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledRun f a degree) := by
  obtain ⟨csim, hsim⟩ := codeEvalnNat_polyFueled f.code
  obtain ⟨cclock, hclock⟩ := ecClock_polyFueled a degree
  refine ⟨_, (hsim.comp ((hclock.comp PolyFueled.left).pair PolyFueled.right)).of_eq
    (fun z => ?_)⟩
  simp [scheduledRun, deadlineRun]

/-- `1` exactly when the day-bounded run has returned the current day `n`.
The natural-valued flag is the form consumed by the flat stream combinators. -/
def scheduledMatch (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  if scheduledRun f a degree z = z.unpair.1 + 1 then 1 else 0

/-- Equality of the scheduled output and the variable day is polynomially decidable. -/
theorem scheduledMatch_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledMatch f a degree) := by
  obtain ⟨crun, hrun⟩ := scheduledRun_polyFueled f a degree
  have hday : PolyFueled _ (fun z : ℕ => z.unpair.1 + 1) :=
    (PolyFueled.left.succ_comp)
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hleft : PolyFueled _ (fun z =>
      scheduledRun f a degree z - (z.unpair.1 + 1)) :=
    (subc_polyFueled.comp (hrun.pair hday)).of_eq (fun z => by simp)
  have hright : PolyFueled _ (fun z =>
      (z.unpair.1 + 1) - scheduledRun f a degree z) :=
    (subc_polyFueled.comp (hday.pair hrun)).of_eq (fun z => by simp)
  have hgap : PolyFueled _ (fun z =>
      (scheduledRun f a degree z - (z.unpair.1 + 1)) +
        ((z.unpair.1 + 1) - scheduledRun f a degree z)) :=
    (hadd.comp (hleft.pair hright)).of_eq (fun z => by simp)
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 1).pair (PolyFueled.const 0)).pair hgap)).of_eq
      (fun z => ?_)⟩
  simp only [ifzSelFn, Nat.unpair_pair, scheduledMatch]
  by_cases h : scheduledRun f a degree z = z.unpair.1 + 1
  · have hz : (scheduledRun f a degree z - (z.unpair.1 + 1)) +
        ((z.unpair.1 + 1) - scheduledRun f a degree z) = 0 := by omega
    rw [if_pos hz, if_pos h]
  · have hz : (scheduledRun f a degree z - (z.unpair.1 + 1)) +
        ((z.unpair.1 + 1) - scheduledRun f a degree z) ≠ 0 := by omega
    rw [if_neg hz, if_neg h]

/-- A successful match is sound even though the program was run only for the day clock. -/
theorem scheduledMatch_eq_one_iff
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    (n k : ℕ) :
    scheduledMatch f a degree (Nat.pair n k) = 1 ↔ f k = n := by
  constructor
  · intro h
    have hrun : scheduledRun f a degree (Nat.pair n k) = n + 1 := by
      simpa [scheduledMatch] using h
    have hpos : 0 < scheduledRun f a degree (Nat.pair n k) := by omega
    have hsound := deadlineRun_eq f hpos
    simp only [scheduledRun, Nat.unpair_pair] at hsound hrun
    omega
  · intro h
    subst n
    simp [scheduledMatch, scheduledRun, deadlineRun, codeEvalnNat, hspec]

/-- The decoded value of the scheduled run, with the unfinished sentinel normalized to
zero.  Input is again `⟨day,component⟩`. -/
def scheduledValue (f : DeferralFunction) (a degree : ℕ) (z : ℕ) : ℕ :=
  scheduledRun f a degree z - 1

/-- Decoding the bounded run preserves polynomial fuel. -/
theorem scheduledValue_polyFueled (f : DeferralFunction) (a degree : ℕ) :
    ∃ c, PolyFueled c (scheduledValue f a degree) := by
  obtain ⟨crun, hrun⟩ := scheduledRun_polyFueled f a degree
  exact ⟨_, (predc_polyFueled.comp hrun).of_eq (fun z => by
    simp [scheduledValue, Nat.pred_eq_sub_one])⟩

/-- The standard evaluator clock is monotone in its day argument. -/
theorem ecClock_mono (a degree : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ecClock a degree m ≤ ecClock a degree n := by
  simp only [ecClock]
  gcongr

/-- Once the runtime day reaches `f k`, the scheduled value has converged to the true
deferral value.  This is the lookup fact used by every feedback feature emitted on that
day. -/
theorem scheduledValue_eq
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln (ecClock a degree (f k)) f.code k = some (f k))
    {n k : ℕ} (hkn : f k ≤ n) :
    scheduledValue f a degree (Nat.pair n k) = f k := by
  have hbase : deadlineRun f (ecClock a degree (f k)) k = f k + 1 := by
    simp [deadlineRun, codeEvalnNat, hspec]
  have hpos : 0 < deadlineRun f (ecClock a degree (f k)) k := by
    rw [hbase]
    omega
  have hrun := deadlineRun_mono f (ecClock_mono a degree hkn) hpos
  simp only [scheduledValue, scheduledRun, Nat.unpair_pair]
  rw [hrun, hbase]
  omega

end FeedbackEmission
end LogicalInduction
