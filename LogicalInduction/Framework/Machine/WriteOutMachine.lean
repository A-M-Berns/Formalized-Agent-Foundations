import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnSplice
import LogicalInduction.Framework.WriteOut

/-!
# The write-out classes, machine reading

`BigTokenStream` and `BigSentenceCodes` (`Framework/WriteOut.lean`) state polynomial
write-out through the `dd:fuel` device: a fuel-clocked digit emitter. `MachineTokenStream`
and `MachineSentenceCodes` state the corresponding notion in the shape
`MachineEfficientTrader` has — a `Complexity.FP` function of the *unary* day emits the word,
and `TokenFold.decodeBits` reads the tokens back. Token values are unrestricted: the word's
*length* is what the polynomial bounds.

`MachineEfficientTrader` (`Framework/Criterion.lean`) is the development's rendering of
`def:ec`; the two classes here are the write-out lane's machine readings kept beside it, and
neither is a paper node of its own.

## The shared recipe, and the bridges built from it

`PolySegStream.exists_FP_word` is the one place the certificate recipe is written down: a
polynomial segment stream is a clocked length/token code pair
(`PolySegStream.clockedTokens_certificate`), `traderMachine` compiles that pair into
polynomial time (`Framework/Machine/TraderMachine.lean`), and the emitted word reads back to
the same digits (`bitsToDigits_traderOutput`, `undigitize_map_min_four`). Every bridge below
is one `obtain` from it.

`BigTokenStream.toMachine` states the bridge at the token stream, with the decoder factored
out, so a class defined as "a `BigTokenStream` whose decode satisfies …" gets its machine
reading by composing with its own decoder. That covers `BigSentenceCodes` (decoder
`parseRpn`, the one worked instance below) and `BigSpliceStream` (decoder
`UnRpnContractsTo`, for which no machine reading is constructed). It does *not* cover
`BigDigits` (`Framework/DigitArith.lean`) or the classes over it, `DigitRatCodes` and
`DigitMachineCodes`: those are poly-fueled digit *access* rather than an emitted word, so
they are outside the pattern and have no bridge lemma.

`RpnSentenceCodes.toMachine` is the fuel-metered sentence class's inclusion into its machine
reading, obtained by widening to `BigSentenceCodes` first
(`BigSentenceCodes.ofRpnSentenceCodes`).

## Reach

The converse of these inclusions is calibrated in the fuel model card in
`Framework/Computable.lean`: open at the length-metered target on a named compiler
obstruction, and false at the value-metered one, refuted by `not_polyFueled_two_pow`. The
`dd:fuel` glossary entry records that the converse is open and points at that card.

Neither `MachineTokenStream` nor `MachineSentenceCodes` is a hypothesis anything in the
development takes. They are kept as the machine readings of the write-out classes, stated
beside them so that the fuel/machine calibration recorded in that model card and in
`scripts/coverage-classification.md`'s `def:ec` row is exhibited in Lean rather than only
asserted. `thm:scon`'s machine transports go through the separately defined
`CondStep.MachineSentenceBlocks` (`Construction/Machine/CondStep.lean`), reached from
`BigSentenceCodes` by `machineSentenceBlocks_of_big`.
-/

namespace LogicalInduction

open Nat.Partrec.Code
open LogicalInduction.TraderMachine

/-! ## The certificate recipe -/

/-- **A polynomial segment stream is emitted by a polynomial-time machine.** Its poly-fueled
length and token codes are a clocked pair (`PolySegStream.clockedTokens_certificate`), which
`traderMachine` compiles; reading the emitted word back through
`decodeBits = undigitize ∘ bitsToDigits` recovers the stream, the digit clamp at the
terminator `4` being invisible to `undigitize` (`undigitize_map_min_four`).

This is the recipe every machine reading of a write-out class runs, factored out so it is
stated once. -/
lemma PolySegStream.exists_FP_word {ds : ℕ → List ℕ} (h : PolySegStream ds) :
    ∃ F ∈ Complexity.FP, ∀ d, TokenFold.decodeBits (F (unaryDay d)) = undigitize (ds d) := by
  obtain ⟨lc, tc, a, k, hclk⟩ := PolySegStream.clockedTokens_certificate h
  refine ⟨traderOutput lc tc a k, traderOutput_mem_FP lc tc a k, fun d => ?_⟩
  show undigitize (bitsToDigits (traderOutput lc tc a k (unaryDay d))) = undigitize (ds d)
  rw [bitsToDigits_traderOutput, length_unaryDay, undigitize_map_min_four]
  simp only [clockOf]
  rw [hclk d]

/-! ## The write-out token stream, machine reading -/

/-- **A written-out token stream, machine reading.** Some `Complexity.FP` function of the
unary day emits a word carrying exactly the tokens of `t d`, read back through the
`decodeBits = undigitize ∘ bitsToDigits` pipeline `MachineEfficientTrader` also uses. Token
values are unrestricted: the word's *length* is what the polynomial bounds. -/
def MachineTokenStream (t : ℕ → List ℕ) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧
    ∀ d, TokenFold.decodeBits (F (unaryDay d)) = t d

/-- **Every fuel-metered write-out certificate is machine-metered.** The digit stream
underlying a `BigTokenStream` is a `PolySegStream`, so `PolySegStream.exists_FP_word`
applies and the emitted word decodes to digits that undigitize to the original tokens.
Nothing here bounds a token's value, so the exponential tokens the class exists to admit
survive the bridge. -/
lemma BigTokenStream.toMachine {t : ℕ → List ℕ} (h : BigTokenStream t) :
    MachineTokenStream t := by
  obtain ⟨ds, hds, -, hu⟩ := h
  obtain ⟨F, hF, hd⟩ := hds.exists_FP_word
  exact ⟨F, hF, fun d => (hd d).trans (hu d)⟩

/-! ## The sentence instance -/

/-- **The efficient sentence-sequence class, machine reading.** Some `Complexity.FP`
function of the *unary* day emits a self-delimiting RPN block parsing to `φ d` and nothing
more, read back through the same pipeline `MachineTokenStream` uses. Contrast
`RpnSentenceCodes` (`Framework/RpnSplice.lean`), which asks for a fuel-clocked
`PolySegStream`, and `BigSentenceCodes` (`Framework/WriteOut.lean`), which asks for a
fuel-clocked write-out; both certify here. -/
def MachineSentenceCodes (φ : ℕ → Sentence) : Prop :=
  ∃ B : List Bool → List Bool, B ∈ Complexity.FP ∧
    ∀ d, parseRpn (undigitize (bitsToDigits (B (unaryDay d)))).length
      (undigitize (bitsToDigits (B (unaryDay d)))) = some (φ d, [])

/-- **A written-out sentence sequence is machine-metered.** The `parseRpn` instance of the
token-stream bridge: the underlying stream's machine reading carries the same tokens, so the
parse is unchanged. Unlike `RpnSentenceCodes.toMachine` this admits sequences whose Gödel
codes grow exponentially in the day. -/
lemma BigSentenceCodes.toMachine {φ : ℕ → Sentence} (h : BigSentenceCodes φ) :
    MachineSentenceCodes φ := by
  obtain ⟨s, hs, hp⟩ := h
  obtain ⟨F, hF, hread⟩ := hs.toMachine
  refine ⟨F, hF, fun d => ?_⟩
  have hd : undigitize (bitsToDigits (F (unaryDay d))) = s d := hread d
  rw [hd]
  exact hp d

/-- **Every fuel-metered efficient sentence sequence is machine-metered.** A
`RpnSentenceCodes` certificate is in particular a write-out certificate
(`BigSentenceCodes.ofRpnSentenceCodes`), so the write-out bridge applies. -/
lemma RpnSentenceCodes.toMachine {φ : ℕ → Sentence} (h : RpnSentenceCodes φ) :
    MachineSentenceCodes φ :=
  (BigSentenceCodes.ofRpnSentenceCodes h).toMachine

end LogicalInduction
