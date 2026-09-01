/-
# The write-out classes, machine reading

`BigTokenStream` (`Framework/WriteOut.lean`) states polynomial write-out through the
`dd:fuel` device: a fuel-clocked digit emitter.  `MachineTokenStream` states the same
notion the way `MachineEfficientTrader` states `def:ec` — a `Complexity.FP` function of
the *unary* day emits the word, and `TokenFold.decodeBits` reads the tokens back.

The bridge is `BigTokenStream.toMachine` with the decoder factored out.  Every
write-out class in this development is "some `BigTokenStream` whose decode satisfies …",
so stating the bridge at the token stream — rather than parameterizing it by a decoder —
gives each class its machine reading by composing with its own decoder, whatever shape
that decoder has (`parseRpn` for sentences, `UnRpnContractsTo` for splice streams).
`MachineSentenceCodes` for a written-out sentence sequence is the worked instance.

The converse is neither needed nor claimed, here or in `RpnSentenceCodes.toMachine`.
-/
import LogicalInduction.Framework.WriteOut
import LogicalInduction.Framework.Machine.SentenceCodes

namespace LogicalInduction

open Nat.Partrec.Code
open LogicalInduction.TraderMachine

/-- **A written-out token stream, machine reading.**  Some `Complexity.FP` function of the
unary day emits a word carrying exactly the tokens of `t d`, read back through the same
`decodeBits = undigitize ∘ bitsToDigits` pipeline `MachineEfficientTrader` uses.  Token
values are unrestricted: the word's *length* is what the polynomial bounds. -/
def MachineTokenStream (t : ℕ → List ℕ) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧
    ∀ d, TokenFold.decodeBits (F (unaryDay d)) = t d

/-- **Every fuel-metered write-out certificate is machine-metered.**  The digit stream
underlying a `BigTokenStream` is a `PolySegStream`, hence a clocked code pair, and
`traderMachine` compiles that pair into polynomial time; the emitted word decodes back to
the same digits, which undigitize to the original tokens.  Nothing here bounds a token's
value, so the exponential tokens the class exists to admit survive the bridge. -/
lemma BigTokenStream.toMachine {t : ℕ → List ℕ} (h : BigTokenStream t) :
    MachineTokenStream t := by
  obtain ⟨ds, hds, -, hu⟩ := h
  obtain ⟨lc, tc, a, k, hclk⟩ := PolySegStream.clockedTokens_certificate hds
  refine ⟨traderOutput lc tc a k, traderOutput_mem_FP lc tc a k, fun d => ?_⟩
  show undigitize (bitsToDigits (traderOutput lc tc a k (unaryDay d))) = t d
  rw [bitsToDigits_traderOutput, length_unaryDay, undigitize_map_min_four]
  simp only [clockOf]
  rw [hclk d]
  exact hu d

/-- **A written-out sentence sequence is machine-metered.**  The `parseRpn` instance of
the bridge, and the write-out counterpart of `RpnSentenceCodes.toMachine`: unlike that
inclusion, this one admits sequences whose Gödel codes grow exponentially in the day. -/
lemma BigSentenceCodes.toMachine {φ : ℕ → Sentence} (h : BigSentenceCodes φ) :
    MachineSentenceCodes φ := by
  obtain ⟨s, hs, hp⟩ := h
  obtain ⟨F, hF, hread⟩ := hs.toMachine
  refine ⟨F, hF, fun d => ?_⟩
  have hd : undigitize (bitsToDigits (F (unaryDay d))) = s d := hread d
  rw [hd]
  exact hp d

#print axioms BigTokenStream.toMachine
#print axioms BigSentenceCodes.toMachine

end LogicalInduction
