import LogicalInduction.Framework.Machine.SentenceMachine
import LogicalInduction.Framework.Expectations

/-!
# The threshold interfaces, machine reading

`LUV.BigThresholdCodes` and `LUV.BigThresholdCodeSeq` (`Framework/Expectations.lean`) are
`BigSentenceCodes` at a fixed re-indexing of the paired argument.  The machine readings
stated here are the same re-indexings of `MachineSentenceCodes`, so each is one line, and
each forward bridge is `BigSentenceCodes.toMachine` under it.  Nothing else about them
differs from their twins — same sentences, same index convention, only the meter on the
underlying token stream changes.

## Why this is a module of its own

It is the *only* place in `Framework/Machine/` that needs `Framework/Expectations.lean`, and
it needs it for one reason: `LUV` is declared there.  Isolating that dependency in a leaf is
what lets the rest of `Framework/Machine/` — `SentenceMachine`, `SpliceMachine`,
`Witnesses` — sit *upstream* of `Expectations`, so that `Expectations` can import
`Framework/Machine/SpliceMachine.lean` and use the machine combinators.  That is load-bearing
rather than tidy: `ratCodeFeature_generated` and `PGenerableRat.ofMachineRatCodes` are stated
at `MachineRatCodes` precisely because they reach
`MachineSpliceStream.serialize_const_write`, which they could not do from downstream of the
machine suite.

So the layering is: `WriteOutMachine → SentenceMachine → SpliceMachine → Expectations → `
this file.  Anything in `Framework/Machine/` that mentions `LUV` belongs here; anything that
does not must stay upstream of `Expectations`, or the edge inverts again.

Everything in this file is supporting infrastructure rather than a paper claim, so the
`lemma`s carry no `Paper node` line; the two `def`s are the machine readings of `def:ec`
threshold interfaces and are named in `Framework/Expectations.lean`'s own map.
-/

namespace LogicalInduction

namespace LUV

/-- **Write-out form of the single-LUV threshold interface, machine reading.** A
`Complexity.FP` function of the unary paired index `⟨k,i⟩` emits a block parsing to
`⌜X > i/k⌝`, at exactly the index convention of `LUV.BigThresholdCodes`. Token values are
unrestricted, the word's length is what the polynomial bounds, and no length side condition
is asked of a caller. Fuel-side twin: `LUV.BigThresholdCodes`. -/
def MachineThresholdCodes (X : LUV) : Prop :=
  MachineSentenceCodes (fun m => X.gt ((m.unpair.2 : ℚ) / (m.unpair.1 : ℚ)))

/-- **Write-out form of the threshold sequence interface, machine reading.** A
`Complexity.FP` function of the unary paired index `⟨n,⟨k,i⟩⟩` emits a block parsing to
`⌜X_n > i/k⌝`, at exactly the index convention of `LUV.BigThresholdCodeSeq`. This is the
machine reading of the class the day-indexed expectation surface is stated over. No length
side condition. Fuel-side twin: `LUV.BigThresholdCodeSeq`. -/
def MachineThresholdCodeSeq (X : ℕ → LUV) : Prop :=
  MachineSentenceCodes (fun m => (X m.unpair.1).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))

/-- **The paper's indicator LUV sequence is machine-metered**, from the sentence sequence
alone — no threshold certificate is asked of a caller.  At a threshold index `⟨n,⟨k,i⟩⟩` the
rational is `i/k ≥ 0`, so `LUV.indicatorOf`'s `r < 0` branch is unreachable and the family is
a two-way dispatch: `φ n ⋏ ∼∼(φ n)` when `i/k < 1`, `⊥` otherwise.  The test is the ruler
`((i + 1) - k) * k`, which vanishes exactly when `k = 0` — where `i/k` is `0` — or `i < k`.
The `[0,1)` branch is built from `hφ` by the sentence calculus (`.and`, `.neg`), which is why
`thm:ei`'s unconditional endpoint asks for nothing but the e.c. sentence sequence. -/
lemma indicatorOf_machineThresholdCodeSeq {φ : ℕ → Sentence}
    (hφ : MachineSentenceCodes φ) :
    MachineThresholdCodeSeq (fun n => LUV.indicatorOf (φ n)) := by
  have hk : UnaryRuler (fun m : ℕ => m.unpair.2.unpair.1) :=
    UnaryRuler.unpairFst.comp UnaryRuler.unpairSnd
  have hi : UnaryRuler (fun m : ℕ => m.unpair.2.unpair.2) :=
    UnaryRuler.unpairSnd.comp UnaryRuler.unpairSnd
  have ht : UnaryRuler (fun m : ℕ =>
      (m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1) * m.unpair.2.unpair.1) :=
    (hi.succ.sub hk).mul hk
  have hbase : MachineSentenceCodes (fun m : ℕ => φ m.unpair.1) :=
    hφ.comp UnaryRuler.unpairFst
  show MachineSentenceCodes (fun m => (LUV.indicatorOf (φ m.unpair.1)).gt
    ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)))
  refine MachineSentenceCodes.of_eq
    (MachineSentenceCodes.ifZero (hbase.and hbase.neg.neg)
      (MachineSentenceCodes.const (⊥ : Sentence)) ht) (fun m => ?_)
  have hnn : ¬ ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ) < 0) :=
    not_lt.mpr (div_nonneg (by positivity) (by positivity))
  have hkey : ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ) < 1) ↔
      (m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1) * m.unpair.2.unpair.1 = 0 := by
    rcases Nat.eq_zero_or_pos m.unpair.2.unpair.1 with hk0 | hk0
    · simp [hk0]
    · rw [div_lt_one (by exact_mod_cast hk0)]
      constructor
      · intro h
        have hlt : m.unpair.2.unpair.2 < m.unpair.2.unpair.1 := by exact_mod_cast h
        simp [Nat.sub_eq_zero_of_le hlt]
      · intro h
        have hz : m.unpair.2.unpair.2 + 1 - m.unpair.2.unpair.1 = 0 := by
          rcases Nat.mul_eq_zero.mp h with h' | h'
          · exact h'
          · omega
        have hlt : m.unpair.2.unpair.2 < m.unpair.2.unpair.1 := by omega
        exact_mod_cast hlt
  by_cases hlt : (m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ) < 1
  · rw [if_pos (hkey.mp hlt)]
    simp [LUV.indicatorOf, hnn, hlt]
  · rw [if_neg (fun hc => hlt (hkey.mpr hc))]
    simp [LUV.indicatorOf, hnn, hlt]

/-- **Every fuel-metered single-LUV threshold certificate is machine-metered.**
`BigSentenceCodes.toMachine` under the threshold re-index; stated in this direction only. -/
lemma BigThresholdCodes.toMachine {X : LUV} (h : X.BigThresholdCodes) :
    X.MachineThresholdCodes :=
  BigSentenceCodes.toMachine h

/-- **Every fuel-metered threshold sequence certificate is machine-metered.**
`BigSentenceCodes.toMachine` under the threshold re-index; stated in this direction only. -/
lemma BigThresholdCodeSeq.toMachine {X : ℕ → LUV} (h : BigThresholdCodeSeq X) :
    MachineThresholdCodeSeq X :=
  BigSentenceCodes.toMachine h

end LUV

end LogicalInduction
