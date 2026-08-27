/-
# The efficient sentence-sequence class, machine reading

`RpnSentenceCodes` (`Framework/RpnSplice.lean`) renders the paper's efficiently
computable sentence sequences through the `dd:fuel` device: a `PolySegStream` of
self-delimiting RPN blocks.  `MachineSentenceCodes` states the same notion the way
`MachineEfficientTrader` states `def:ec` — a `Complexity.FP` function of the *unary* day
emits the block, read back three bits per digit.

`RpnSentenceCodes.toMachine` is the inclusion, and it reuses the trader compiler
verbatim: a `PolySegStream` is exactly a poly-fueled length/token code pair, which is the
certificate `traderMachine` compiles, so the same `traderOutput` word carries the sentence
block.  The converse is neither needed nor claimed.
-/
import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnSplice

namespace LogicalInduction

open Nat.Partrec.Code
open LogicalInduction.TraderMachine

/-- **The efficient sentence-sequence class, machine reading.** Some `Complexity.FP`
function of the *unary* day emits a self-delimiting RPN block parsing to `φ d` and nothing
more, read back through the same `bitsToDigits ∘ undigitize` pipeline
`MachineEfficientTrader` uses.  Contrast `RpnSentenceCodes`, which asks for a fuel-clocked
`PolySegStream`; every such sequence certifies here (`RpnSentenceCodes.toMachine`). -/
def MachineSentenceCodes (φ : ℕ → Sentence) : Prop :=
  ∃ B : List Bool → List Bool, B ∈ Complexity.FP ∧
    ∀ d, parseRpn (undigitize (bitsToDigits (B (unaryDay d)))).length
      (undigitize (bitsToDigits (B (unaryDay d)))) = some (φ d, [])

/-- **Every fuel-metered efficient sentence sequence is machine-metered.** The block
stream's digitization is again a `PolySegStream`, hence a clocked code pair, and
`traderMachine` compiles that pair into polynomial time; the emitted word undigitizes back
to the original block, so the parse is unchanged.  The converse is neither needed nor
claimed.

A `lemma`, not a `theorem`: it is supporting infrastructure for the machine reading of
`thm:scon`, not itself a paper claim.  Promote it to a labelled endpoint if and when a
paper-facing theorem is stated directly in terms of it. -/
lemma RpnSentenceCodes.toMachine {φ : ℕ → Sentence} (h : RpnSentenceCodes φ) :
    MachineSentenceCodes φ := by
  obtain ⟨s, hs, hp⟩ := h
  obtain ⟨lc, tc, a, k, hclk⟩ := PolySegStream.clockedTokens_certificate hs.digitizeStream
  refine ⟨traderOutput lc tc a k, traderOutput_mem_FP lc tc a k, fun d => ?_⟩
  have hread : undigitize (bitsToDigits (traderOutput lc tc a k (unaryDay d))) = s d := by
    rw [bitsToDigits_traderOutput, length_unaryDay, undigitize_map_min_four]
    simp only [clockOf]
    rw [hclk d, undigitize_digitize]
  rw [hread]
  exact hp d

#print axioms RpnSentenceCodes.toMachine

end LogicalInduction
