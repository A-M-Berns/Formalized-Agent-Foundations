import LogicalInduction.Framework.Machine.TraderMachine
import LogicalInduction.Framework.Emission.WriteOut
import LogicalInduction.Framework.Machine.DigitArithFP
import LogicalInduction.Framework.Machine.Ruler
import LogicalInduction.Framework.Emission.RpnEmission
import LogicalInduction.Framework.Emission.RpnSplice

/-!
# The write-out classes, machine reading

`BigTokenStream`, `BigSentenceCodes` and `BigSpliceStream` (`Framework/Emission/WriteOut.lean`)
state polynomial write-out through the `dd:fuel` device: a fuel-clocked digit emitter.
`MachineTokenStream`, `MachineSentenceCodes` and `MachineSpliceStream` state the corresponding
notion in the shape `EfficientlyComputable` has — a `Complexity.FP` function of the *unary*
day emits the word, and `TokenFold.decodeBits` reads the tokens back. Token values are
unrestricted: the word's *length* is what the polynomial bounds. `MachineDigits`,
`MachineMachineCodes` and `MachineRatCodes` are the same reading of the three value classes.
`MachineDigits` names a different object from its fuel-metered original — the emitted digit
*block*, not random access to a value's digits — and that divergence is disclosed at the
definition itself.

`EfficientlyComputable` (`Framework/Criterion.lean`) is the development's rendering of
`def:ec`; the classes here are the write-out lane's machine readings kept beside it, and none
of them is a paper node of its own.

## Block-completeness is carried, not recovered

`MachineTokenStream` asks for `TokenFold.BlockWF` of the emitted word alongside the decode
equation. The conjunct is what makes the class closed under concatenation:
`TokenFold.decodeBits_append` splits a decode across `++` only when the left word carries a
whole number of complete digit blocks, so without it the class admits no `append` and every
combinator built from `append` is out of reach. `CondStep.MachineSentenceBlocks`
(`Construction/Conditioning/TransductionFrame.lean`) carries the same conjunct for the same
reason. It costs nothing at the bridges: the word a write-out certificate emits is
`TokenFold.tokBits` of its own token stream, which is block-complete by construction.

`MachineSentenceCodes` and `MachineSpliceStream` are stated **over `MachineTokenStream`**,
matching the shape their fuel-metered counterparts have over `BigTokenStream`, so a combinator
proved at the token stream lifts to either of them by one `obtain`.

## The shared recipe, and the bridges built from it

`PolySegStream.exists_FP_word` writes the certificate recipe down: a polynomial segment stream
is a clocked length/token code pair (`PolySegStream.clockedTokens_certificate`),
`traderMachine` compiles that pair into polynomial time
(`Framework/Machine/TraderMachine.lean`), and the emitted word reads back to the same digits
(`bitsToDigits_traderOutput`, `undigitize_map_min_four`). It fixes the decode alone, so it
does not see the emitted word's block structure.

`PolySegStream.exists_FP_rawWord` sharpens it one step: when no digit of the stream exceeds
the terminator, the emitter's clamp `min · 4` is the identity and the emitted word is
literally `digitsToBits` of the stream, not merely a word decoding to the same tokens.

`PolySegStream.exists_FP_blockWord` is that at a `digitize` — which is what
`BigTokenStream.digitizeStream` supplies from any write-out certificate — so the emitted
word is `TokenFold.tokBits` of the token stream, hence `TokenFold.BlockWF`. It is the recipe
every bridge below runs, each one `obtain` from it. `UnaryRuler.of_polyFueled` is the other
instance: a poly-fueled count emitted as its base-four run and read back as a *length*, the
machine-side rendering of every `PolyFueled c cnt` parameter the fuel-metered combinators
take.

`BigTokenStream.toMachine` states the bridge at the token stream. A class defined as "a
`BigTokenStream` whose decode satisfies …" gets its machine reading by carrying its own
decoding condition across unchanged — that is `BigSentenceCodes.toMachine` (condition
`parseRpn`) and `BigSpliceStream.toMachine` (condition `UnRpnContractsTo`), each one line.

`BigDigits` (`Framework/Emission/DigitArith.lean`) and the classes over it,
`DigitMachineCodes` and `DigitRatCodes`, are poly-fueled digit *access* rather than an emitted
word, so they meet the pattern one step earlier: `BigTokenStream.ofBigDigits` emits the
accessed value's self-delimiting digit block as a one-token stream, and `MachineDigits` is the
machine reading of that one-token write-out. The two classes over it read through it, at the
same naming map and the same field split as their fuel-metered originals.

`RpnSentenceCodes.toMachine` is the fuel-metered sentence class's inclusion into its machine
reading, obtained by widening to `BigSentenceCodes` first
(`BigSentenceCodes.ofRpnSentenceCodes`).

## Reach

Every bridge here runs one way. The converse is calibrated in the fuel model card in
`Framework/Emission/Computable.lean`, which states it in full; the `dd:fuel` glossary entry
records that it is open and points at that card. It splits into two targets with different
verdicts, and the obstruction at the open one is a *workspace* bound, not a missing compiler.

At a fixed code, `PolyFueled` is a **poly-time, `O(log n)`-workspace** device. `evaln`'s
`n ≤ k` guard caps every value handed to a sub-code by the fuel, and `PolyFueled`'s own
`IsPolyBounded` conjuncts keep both the fuel and the computed value polynomial in the input;
so every value the run ever handles is bounded by a polynomial in the input, that is, carries
`O(log n)` bits. The code being fixed makes the nest of `prec` and `rfind'` loops
constant-depth. `Complexity.FP` is poly-time with **polynomial** workspace.

So `MachineTokenStream t → BigTokenStream t` says, in substance, that every poly-time
write-out over tally inputs is a logspace write-out: a P-versus-L flavoured containment, a
complexity-theoretic conjecture rather than a lemma. It is equally not refutable here. A
Turing-machine-to-`Nat.Partrec.Code` compiler carrying fuel accounting would not close it:
even a perfect compiler yields a code whose `evaln` run needs fuel at least as large as the
configuration *value*, which is `2 ^ Θ(poly n)`.

The value-metered target is settled rather than open: it is false, refuted by
`not_polyFueled_two_pow`.

The asymmetry is exhibited in Lean by the two `example`s under "The bounded-iteration
asymmetry" below. `PolyFueled.prec` bounds the iterated state's numeric *value*;
`FPFold.foldlBits_mem_FP` bounds its *length*, and it is the bounded-iteration combinator a
converse would run, available on the `Complexity.FP` side only.

A second gap stands independently of the workspace one, and it is a *converse*-direction
obligation only. `BigTokenStream t` demands `(blockSplit (ds n)).2 = []` of a fuel-clocked
digit stream. Recovering that from a machine word means truncating the digit stream to its
last complete block — a bounded maximization — and the `PolyFueled` combinator suite has no
bounded-search combinator, so granting the workspace step would leave this obligation
standing. Going forward no such maximization arises: `MachineTokenStream` carries
`TokenFold.BlockWF` as a conjunct of its own, and every bridge below discharges it by
construction rather than by search.

What the machine side carries instead is closure: `MachineTokenStream.of_eq`,
`.const`, `.comp`, `.append`, `.ifZero` and `.concatVar` mirror the write-out combinators of
`Framework/Emission/WriteOut.lean`, so a class stated over `MachineTokenStream` inherits them
by one `obtain` — `Framework/Machine/SentenceMachine.lean` and
`Framework/Machine/SpliceMachine.lean` are the two classes that do, and the latter carries
the trader capstones (`MachineSpliceStream.ec`,
`EfficientlyComputable.ofSingleTradeBlocksBig`, `.ofTradeBlocksBig`) the whole ladder exists
to reach; `ec_of_machineTokenStream` below is where it meets `EfficientlyComputable`. None
of that is a converse — every one of them builds a machine certificate from machine
certificates, and the fuel-metered hypotheses they replace arrive through
`UnaryRuler.of_polyFueled` (or, at the identity, `UnaryRuler.id`), itself a forward bridge.
The suite needs no length-polynomial field on any class: `Complexity.FP` membership already
bounds an emitted word's length by a polynomial in its argument
(`Cobham.output_length_poly_of_mem_FP`), which is exactly the per-step bound the streaming
concatenation's fold demands.

A fuel-side `PolyFueled c f` parameter has **two** machine renderings, and which one a
combinator takes says what it does with the parameter. Where `f` reindexes — a dispatch test,
a segment count, a day map — the reading is a unary ruler (`UnaryRuler`,
`Framework/Machine/Ruler.lean`, which also carries its closure calculus), and
`UnaryRuler.of_polyFueled` supplies it from a fuel certificate. Where `f`'s value is written into the stream, the reading is `MachineDigits f`,
which admits values exponential in the day and so is strictly more general;
`MachineDigits.ofUnaryRuler` is the bridge from the first reading to the second. That is why
the fuel side's value-bounded/write-out combinator pairs have a single mirror each here.

The value lane is complete. `MachineDigits.natPair` is the square-and-add split of
`BigDigits.natPair` on payload runs, and `MachineRatCodes.toMachineDigits` is the mirror of
`DigitRatCodes.toBigDigits` built from it; both rest on `DigitFP.mulW`
(`Framework/Machine/DigitArithFP.lean`), the base-four word multiplication written for them.
What they serve is *outside* this file: `thm:ref`, `thm:st` and `thm:perkno` take
`MachineRatCodes`, and `PolyPositiveWidths.codes`,
`IntrospectionIntervalQuote.inverse_width_codes` and `PatientSettlementClock.active_codes`
are stated at it, reached through `MachineRatCodes.toMachineDigits` and
`MachineSpliceStream.serialize_const_write`.

The digit lane (`thm:halts`, `thm:loops`, `thm:dontwait`, `thm:pac`) spends its write-out
premise in exactly one place: the compact numeral emitter. The fuel emitter
`polySegStream_binNumeral_const` (`Construction/LUV/SourceCodec.lean`) reads the
value's base-four *length* `len4` and its digits `dig4` at a paired index off the fuel
certificate's two random-access programs. `MachineDigits` is deliberately not that spelling
(see its docstring): it is the emitted block, and the block an emitter chooses need not be
the canonical `natDigits4` run — `TokenFold`'s own note says so — so `len4` is not a function
of the emitted word's length, while `binNumeral`'s shape depends on `len4` exactly. What the
machine emitter therefore needs is an `FP` canonicalization of a digit word, and NOT machine
random access to a digit at a ruler-indexed position. `TokenFold.Strip` is that
canonicalization — one `dgFold` pass stripping the high zero digits — and the emitter
consumes the canonical digits **in order**, most significant first, which the strip client
produces by *prepending* its per-digit emission while the fold runs least significant first.
`machineTokenStream_binNumeralEnc` (`Construction/LUV/SourceCodec.lean`) is the emitter, with
the digit *count* read off a second pass of the same client at one mark per digit.
`MachineDigits.ofTokenListNat` below is the other construction of that kind, and it needs no
word arithmetic at all: base `64` is `4 ^ 3`, so the base-`64` Horner accumulation naming an
emitted run is concatenation.

The *trader* lane is independent of both. `AffineCombination.PolySequence`'s three emission
fields are machine-metered, so `PolySequence.buyBelowTrader_ec` certifies at
`EfficientlyComputable` and the §4 results consuming it take `[IsLogicalInductor]`. The
device that carries it is `MachineTokenStream.primrec`
(`Construction/MachineTraderEnumeration.lean`), the machine twin
of `BigTokenStream.primrec` — `Complexity.FP ⊆ Primrec` is not available, so it is proved
through the trader enumeration's coverage bridge instead. `PolySequence.termCount_poly` is at
`UnaryRuler` (`Framework/Machine/Ruler.lean`); its own bridge is
`UnaryRuler.primrec`, in the same file and by the same coverage argument, reading the count
off the budgeted run's raw output *word length* rather than off its digits.

Inhabitation is separate from closure, and it is discharged separately:
`Framework/Machine/Witnesses.lean` gives each of the six classes a constructed inhabitant that
varies with the day, up to a trader whose traded sentence changes every day, each with the
lemma saying the family is not a constant sequence.

The machine readings here are the hypotheses the development takes, and they are the *only*
ones on the endpoint surface: no canonical endpoint has a fuel- or value-metered data premise,
printed or through a boundary structure.  `MachineSpliceStream` and
`MachineSentenceCodes` are the emission fields of `AffineCombination.PolySequence`,
`PolyTradeEmulatable`, `PGenerableWeighting`, `PairedWeighting`, `GeneratedRatFeature`,
`FeedbackTraderEmission`, `PrefixMachinePresentation`, `ConditioningPresentation` and
`CompactConditioningProcessComputation`; `MachineRatCodes` is the rational data premise of
`PolyPositiveWidths`, `IntrospectionIntervalQuote`, `PatientSettlementClock`,
`DUSThresholdEmission` and `OccamThresholdEmission`.  The write-out classes are kept beside
them as the fuel-side producer routes and calibration foils, so that the fuel/machine
calibration recorded in that model card and in `scripts/coverage-classification.md`'s
`def:ec` row is exhibited in Lean at every data class rather than only asserted; the
deliberate fuel residue is listed at that row (the two ROI schedules' schedule predicate and
the calibration classes).  `thm:scon`'s transports go through the
separately defined `CondStep.MachineSentenceBlocks`
(`Construction/Conditioning/TransductionFrame.lean`), reached from `MachineSentenceCodes` by
`machineSentenceBlocks_of_machine` — a read-off, since a machine-metered word already carries
`TokenFold.BlockWF` and its decode law, so no crossing stands between the field and the
transducer.
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

/-- **A digit stream no digit of which exceeds the terminator is emitted verbatim by a
polynomial-time machine.** The recipe of `PolySegStream.exists_FP_word` read one level
lower: the emitter clamps each digit with `min · 4`, so under the hypothesis that clamp is
the identity and the emitted word is literally `digitsToBits (ds d)` rather than merely a
word decoding to the same tokens.

The two recipes below are its instances — `exists_FP_blockWord` at a `digitize`, where the
word is a `TokenFold.tokBits` and hence block-complete, and `UnaryRuler.of_polyFueled` at a
bare `natDigits4` run, where the word's digit value is read back as a length. -/
lemma PolySegStream.exists_FP_rawWord {ds : ℕ → List ℕ} (h : PolySegStream ds)
    (hle : ∀ n, ∀ d ∈ ds n, d ≤ 4) :
    ∃ F ∈ Complexity.FP, ∀ d, F (unaryDay d) = digitsToBits (ds d) := by
  obtain ⟨lc, tc, a, k, hclk⟩ := PolySegStream.clockedTokens_certificate h
  refine ⟨traderOutput lc tc a k, traderOutput_mem_FP lc tc a k, fun d => ?_⟩
  rw [traderOutput, length_unaryDay]
  simp only [clockOf]
  rw [hclk d]
  congr 1
  refine Eq.trans (List.map_congr_left (fun x hx => ?_)) (List.map_id _)
  have := hle d x hx
  simp only [id_eq]
  omega

/-- **A written-out token stream is emitted, block-complete, by a polynomial-time machine.**
`exists_FP_rawWord` at a digit stream that is a `digitize`, whose digits are payload digits
or the terminator (`TokenFold.mem_digitize_le_four`): the emitted word is then literally
`TokenFold.tokBits (t d)` and carries whole blocks by construction
(`TokenFold.blockWF_tokBits`). `BigTokenStream.digitizeStream` supplies the hypothesis from
any write-out certificate, without bounding a token's value.

This is the recipe every machine reading of a write-out class runs, factored out so it is
stated once. -/
lemma PolySegStream.exists_FP_blockWord {t : ℕ → List ℕ}
    (h : PolySegStream fun n => digitize (t n)) :
    ∃ F ∈ Complexity.FP, (∀ d, TokenFold.BlockWF (F (unaryDay d))) ∧
      ∀ d, TokenFold.decodeBits (F (unaryDay d)) = t d := by
  obtain ⟨F, hF, hw⟩ :=
    h.exists_FP_rawWord (fun n => TokenFold.mem_digitize_le_four (t n))
  refine ⟨F, hF, fun d => ?_, fun d => ?_⟩
  · rw [hw d]; exact TokenFold.blockWF_tokBits (t d)
  · rw [hw d]; exact TokenFold.decodeBits_tokBits (t d)

/-- The payload run of a big value family, as a segment stream: `BigDigits.blockSeg` without
the block terminator, so that the run's `digitVal` is the value itself. Only
`UnaryRuler.of_polyFueled` needs it; its settled home, should a second client appear, is
beside `BigDigits.blockSeg` in `Framework/Emission/DigitArith.lean`. -/
private lemma natDigits4_segStream {x : ℕ → ℕ} (hx : BigDigits x) :
    PolySegStream (fun m => natDigits4 (x m)) := by
  obtain ⟨cl, cd, hl, hd⟩ := hx
  refine ⟨cd, cl, _, _, hd, hl, fun m => rfl, fun m j hj => ?_⟩
  simp only [Nat.unpair_pair, dig4]
  exact (natDigits4_getD (x m) j hj).symm

/-- **A poly-fueled count is a polynomial-time unary ruler.**

A machine cannot take `PolyFueled c cnt` as a hypothesis: `cnt : ℕ → ℕ` is not a word
function. What it can take, and what every fold's iteration count must be anyway, is the
*ruler* `z ↦ 1^(cnt |z|)` — the shape `Cobham.exists_exact_ruler` and
`FPFold.foldlBits_mem_FP` already consume. This is the bridge, and it is the machine-side
rendering of every `PolyFueled c cnt` parameter the fuel-metered write-out combinators take
(`MachineTokenStream.ifZero` and `.concatVar` below both ask for exactly this).

The route is: emit the count's base-four payload run as a word (`natDigits4_segStream`,
`exists_FP_rawWord`), then read that word's value back as a length with the guarded
expansion `TokenFold.LEUnary.unaryOfDigitsLE_le_mem_FP`. The guard is not optional — a
`k`-bit value denotes up to `4 ^ k` marks — and the cap it needs is exactly the
`IsPolyBounded` conjunct `PolyFueled` already carries, materialized as an exact ruler for
`a * (X + 1) ^ k + a`. So the bridge exists but is not free: it costs the emission plus the
clamped read-back, and no client of it may assume a count is available as a length without
it. -/
lemma UnaryRuler.of_polyFueled {c : Nat.Partrec.Code} {cnt : ℕ → ℕ}
    (h : PolyFueled c cnt) : UnaryRuler cnt := by
  show (fun z : List Bool => List.replicate (cnt z.length) false) ∈ Complexity.FP
  obtain ⟨a, k, hak⟩ : IsPolyBounded cnt := by
    obtain ⟨b, -, hb, -⟩ := h; exact hb
  obtain ⟨F, hF, hw⟩ :=
    (natDigits4_segStream (BigDigits.of_polyFueled h)).exists_FP_rawWord
      (fun n d hd => le_of_lt (natDigits4_lt _ d hd))
  have hV : (fun z : List Bool => F (List.replicate z.length true)) ∈ Complexity.FP := by
    simpa [Function.comp_def] using Complexity.mem_FP_comp Complexity.unaryLength_mem_FP hF
  obtain ⟨C, hC, hClen⟩ := Complexity.Cobham.exists_exact_ruler
    (Polynomial.C a * (Polynomial.X + 1) ^ k + Polynomial.C a)
  have htrue := TokenFold.LEUnary.unaryOfDigitsLE_le_mem_FP hV hC
  have heqT : (fun z : List Bool =>
        List.replicate (min (digitVal (bitsToDigits (F (List.replicate z.length true))))
          (C z).length) true)
      = fun z : List Bool => List.replicate (cnt z.length) true := by
    funext z
    have hval : digitVal (bitsToDigits (F (List.replicate z.length true))) = cnt z.length := by
      have hz : F (List.replicate z.length true) = digitsToBits (natDigits4 (cnt z.length)) :=
        hw z.length
      rw [hz, bitsToDigits_digitsToBits _
        (fun d hd => lt_trans (natDigits4_lt _ d hd) (by norm_num)), digitVal_natDigits4]
    have hcap : cnt z.length ≤ (C z).length := by
      rw [hClen z]
      simpa using hak z.length
    rw [hval, min_eq_left hcap]
  rw [heqT] at htrue
  have hfalse := Complexity.Cobham.mulLenFn_mem_FP htrue
    (LogicalInduction.FPFold.constFn_mem_FP [true])
  simpa using hfalse

/-! ## The write-out token stream, machine reading -/

/-- **A written-out token stream, machine reading.** Some `Complexity.FP` function of the
unary day emits a word carrying exactly the tokens of `t d`, read back through the
`decodeBits = undigitize ∘ bitsToDigits` pipeline `EfficientlyComputable` also uses. Token
values are unrestricted: the word's *length* is what the polynomial bounds.

The word is also asked to be block-complete. That conjunct is what closes the class under
concatenation — `TokenFold.decodeBits_append` splits a decode across `++` only under
`TokenFold.BlockWF` of the left word — so it is carried here rather than recovered later,
as `CondStep.MachineSentenceBlocks` carries it. It is free at the bridges: a write-out
certificate's word is `TokenFold.tokBits` of its own token stream. -/
def MachineTokenStream (t : ℕ → List ℕ) : Prop :=
  ∃ F : List Bool → List Bool, F ∈ Complexity.FP ∧
    (∀ d, TokenFold.BlockWF (F (unaryDay d))) ∧
    ∀ d, TokenFold.decodeBits (F (unaryDay d)) = t d

/-- **Every fuel-metered write-out certificate is machine-metered.**
`BigTokenStream.digitizeStream` clocks the certificate's own digit stream — needing no bound
on token values, so the exponential tokens the class exists to admit survive the bridge — and
`PolySegStream.exists_FP_blockWord` emits it as a block-complete word. -/
lemma BigTokenStream.toMachine {t : ℕ → List ℕ} (h : BigTokenStream t) :
    MachineTokenStream t :=
  PolySegStream.exists_FP_blockWord h.digitizeStream

/-! ### Closure

The combinators mirror `BigTokenStream`'s (`Framework/Emission/WriteOut.lean`) and are what
every class stated over `MachineTokenStream` inherits by one `obtain`. Each is the
`Complexity.FP` closure lemma for the word paired with the `TokenFold.BlockWF` discipline
for the splice; nothing here bounds a token's value, and nothing here needs a class to carry
a length polynomial, because `Complexity.FP` membership already bounds an emitted word's
length by a polynomial in its argument.

A `ℕ → ℕ` parameter — a dispatch test, a segment count — reaches the machine side as a
**unary ruler** rather than as a code, since a machine cannot read a `Nat.Partrec.Code`
hypothesis; `UnaryRuler.of_polyFueled` above converts each fuel-metered
`PolyFueled c f` hypothesis into the ruler these ask for. -/

/-- Congruence. -/
lemma MachineTokenStream.of_eq {t t' : ℕ → List ℕ} (h : MachineTokenStream t)
    (he : ∀ n, t n = t' n) : MachineTokenStream t' := by
  obtain ⟨F, hF, hwf, hd⟩ := h
  exact ⟨F, hF, hwf, fun d => by rw [hd d, he d]⟩

/-- **A fixed token list is machine-metered.** The emitted word is the constant
`TokenFold.tokBits` of the list, block-complete by `TokenFold.blockWF_tokBits` and decoding
to it by `TokenFold.decodeBits_tokBits`; the certificate does not read the day at all. No
length side condition.

This is where the fuel side's whole `PolyTokenStream` layer collapses to on the machine
side: a constant word is `FPFold.constFn_mem_FP`, so the token-metered scaffolding class
`BigTokenStream.ofPolySegStream ∘ PolySegStream.ofTokenStream ∘ PolyTokenStream.const`
runs through has no machine counterpart to build. -/
lemma MachineTokenStream.const (ts : List ℕ) : MachineTokenStream (fun _ => ts) :=
  ⟨fun _ => TokenFold.tokBits ts, FPFold.constFn_mem_FP _,
    fun _ => TokenFold.blockWF_tokBits ts, fun _ => TokenFold.decodeBits_tokBits ts⟩

/-- **The class is closed under reindexing by a machine-readable map.** The reindexer
arrives as a unary ruler, and the day it names is rebuilt from that ruler's *length* by
`Complexity.unaryLength_mem_FP` — which is why no separate bound is asked for: an `FP`
ruler's length is already polynomial in its argument, so `f n` is polynomially bounded by
the witness itself rather than by a hypothesis. `UnaryRuler.of_polyFueled` supplies the
ruler from the `PolyFueled c f` hypothesis `BigTokenStream.comp` takes. -/
lemma MachineTokenStream.comp {t : ℕ → List ℕ} (h : MachineTokenStream t) {f : ℕ → ℕ}
    (hf : UnaryRuler f) :
    MachineTokenStream (fun n => t (f n)) := by
  obtain ⟨F, hF, hwf, hd⟩ := h
  have hday : (fun z : List Bool => List.replicate (f z.length) true) ∈ Complexity.FP := by
    simpa [Function.comp_def] using
      Complexity.mem_FP_comp hf Complexity.unaryLength_mem_FP
  refine ⟨fun z => F (List.replicate (f z.length) true),
    by simpa [Function.comp_def] using Complexity.mem_FP_comp hday hF,
    fun d => ?_, fun d => ?_⟩
  · show TokenFold.BlockWF (F (List.replicate (f (unaryDay d).length) true))
    simpa [unaryDay] using hwf (f d)
  · show TokenFold.decodeBits (F (List.replicate (f (unaryDay d).length) true)) = t (f d)
    simpa [unaryDay] using hd (f d)

/-- **The class is closed under concatenation.** The word is `Cobham.appendFn_mem_FP`, the
discipline `TokenFold.BlockWF.append`, and the decode splits across `++` by
`TokenFold.decodeBits_append` — which is precisely what the `BlockWF` conjunct of the class
is carried for. -/
lemma MachineTokenStream.append {a b : ℕ → List ℕ} (ha : MachineTokenStream a)
    (hb : MachineTokenStream b) : MachineTokenStream (fun n => a n ++ b n) := by
  obtain ⟨A, hA, hAwf, hAd⟩ := ha
  obtain ⟨B, hB, hBwf, hBd⟩ := hb
  refine ⟨fun z => A z ++ B z, Complexity.Cobham.appendFn_mem_FP hA hB,
    fun d => (hAwf d).append (hBwf d), fun d => ?_⟩
  rw [TokenFold.decodeBits_append (hAwf d) (hBwf d), hAd d, hBd d]

/-- **Dispatch on whether a parameter vanishes.** The test arrives as a unary ruler: `tf d`
is the length of the ruler word at `unaryDay d`, so "is it zero" is
`TokenFold.ifEqLen_mem_FP` at `0`. `UnaryRuler.of_polyFueled` supplies the hypothesis from a
fuel-metered `PolyFueled ct tf`, which is what `BigTokenStream.ifZero` takes. -/
lemma MachineTokenStream.ifZero {s₀ s₁ : ℕ → List ℕ} {tf : ℕ → ℕ}
    (h₀ : MachineTokenStream s₀) (h₁ : MachineTokenStream s₁)
    (ht : UnaryRuler tf) :
    MachineTokenStream (fun z => if tf z = 0 then s₀ z else s₁ z) := by
  obtain ⟨F₀, hF₀, hwf₀, hd₀⟩ := h₀
  obtain ⟨F₁, hF₁, hwf₁, hd₁⟩ := h₁
  refine ⟨fun z => if (List.replicate (tf z.length) false).length = 0 then F₀ z else F₁ z,
    TokenFold.ifEqLen_mem_FP ht 0 hF₀ hF₁, fun d => ?_, fun d => ?_⟩
  · simp only [length_unaryDay, List.length_replicate]
    by_cases hz : tf d = 0
    · rw [if_pos hz]; exact hwf₀ d
    · rw [if_neg hz]; exact hwf₁ d
  · simp only [length_unaryDay, List.length_replicate]
    by_cases hz : tf d = 0
    · rw [if_pos hz, if_pos hz]; exact hd₀ d
    · rw [if_neg hz, if_neg hz]; exact hd₁ d

/-- **Variable-count concatenation**: `cnt n` machine-metered segments, the `j`-th indexed
`Nat.pair n j`, concatenated on day `n`.

The fuel side proves this by *random access* — `PolySegStream.concatVar` scans a table of
segment lengths and locates the segment enclosing each output token index. A machine has no
random access into its own future output, so the machine proof streams the concatenation
instead: `TokenFold.concatUnaryPair_mem_FP` folds over the ruler, rebuilding
`unaryDay (Nat.pair n j)` at each step and appending the segment emitter's answer, with the
loop counter clamped against the ruler so the per-step length bound holds on the malformed
words `FPFold.foldlBits_mem_FP` also quantifies over. `TokenFold.BlockWF.flatMap` carries
the splice discipline and the decode across the concatenation.

The count arrives as a unary ruler; `UnaryRuler.of_polyFueled` supplies it from the
`PolyFueled ccnt cnt` hypothesis `BigTokenStream.concatVar` takes. -/
lemma MachineTokenStream.concatVar {seg : ℕ → List ℕ} (hseg : MachineTokenStream seg)
    {cnt : ℕ → ℕ}
    (hcnt : UnaryRuler cnt) :
    MachineTokenStream (fun n => (List.range (cnt n)).flatMap fun j => seg (Nat.pair n j)) := by
  obtain ⟨F, hF, hwf, hd⟩ := hseg
  have hid : (fun z : List Bool => z) ∈ Complexity.FP := Complexity.id_mem_FP
  obtain ⟨G, hG, hGeq⟩ := TokenFold.concatUnaryPair_mem_FP hF hcnt hid
  have hGd : ∀ d, G (unaryDay d)
      = (List.range (cnt d)).flatMap fun j => F (unaryDay (Nat.pair d j)) := by
    intro d
    rw [hGeq (unaryDay d)]
    simp only [List.length_replicate, length_unaryDay]
    rfl
  refine ⟨G, hG, fun d => ?_, fun d => ?_⟩
  · rw [hGd d]
    exact (TokenFold.BlockWF.flatMap _ _ (fun j _ => hwf (Nat.pair d j))).1
  · rw [hGd d, (TokenFold.BlockWF.flatMap _ _ (fun j _ => hwf (Nat.pair d j))).2]
    exact List.flatMap_congr (fun j _ => hd (Nat.pair d j))

/-- **The machine write-out capstone**: a machine-metered token stream whose contracted
decode is the target trader's day-`n` strategy realizes a `EfficientlyComputable`
certificate. `EfficientlyComputable` reads its word through
`strategyOfTokens ∘ unRpn ∘ undigitize ∘ bitsToDigits`, whose tail is `TokenFold.decodeBits`
by definition, so the certificate's own emitter is handed over unchanged and the class's
`TokenFold.BlockWF` conjunct is not needed here — it is what the *combinators* consume.
No length side condition. Fuel-side twin: `ec_of_bigTokenStream`
(`Framework/Emission/WriteOut.lean`). -/
lemma ec_of_machineTokenStream (Tr : Trader) {t : ℕ → List ℕ} (h : MachineTokenStream t)
    (hstrategy : ∀ n, strategyOfTokens n (unRpn (t n)) = Tr.strat n) :
    EfficientlyComputable Tr := by
  obtain ⟨F, hF, -, hd⟩ := h
  refine ⟨F, hF, fun n => ?_⟩
  show strategyOfTokens n (unRpn (undigitize (bitsToDigits (F (unaryDay n))))) = Tr.strat n
  rw [show undigitize (bitsToDigits (F (unaryDay n))) = t n from hd n]
  exact hstrategy n

/-! ## The sentence and splice instances -/

/-- **The efficient sentence-sequence class, machine reading.** A machine-metered token
stream whose tokens are a self-delimiting RPN block parsing to `φ d` and nothing more.
Contrast `RpnSentenceCodes` (`Framework/Emission/RpnSplice.lean`), which asks for a
fuel-clocked `PolySegStream`, and `BigSentenceCodes` (`Framework/Emission/WriteOut.lean`),
which asks for a fuel-clocked write-out; both certify here.

Stated over `MachineTokenStream`, exactly as `BigSentenceCodes` is stated over
`BigTokenStream`, so the parse condition is carried across the bridge unchanged. -/
def MachineSentenceCodes (φ : ℕ → Sentence) : Prop :=
  ∃ s : ℕ → List ℕ, MachineTokenStream s ∧
    ∀ d, parseRpn (s d).length (s d) = some (φ d, [])

/-- **A written-out sentence sequence is machine-metered.** The `parseRpn` instance of the
token-stream bridge: the underlying stream's machine reading carries the same tokens, so the
parse condition is reused verbatim. Unlike `RpnSentenceCodes.toMachine` this admits sequences
whose Gödel codes grow exponentially in the day. -/
lemma BigSentenceCodes.toMachine {φ : ℕ → Sentence} (h : BigSentenceCodes φ) :
    MachineSentenceCodes φ := by
  obtain ⟨s, hs, hp⟩ := h
  exact ⟨s, hs.toMachine, hp⟩

/-- **Every fuel-metered efficient sentence sequence is machine-metered.** A
`RpnSentenceCodes` certificate is in particular a write-out certificate
(`BigSentenceCodes.ofRpnSentenceCodes`), so the write-out bridge applies. -/
lemma RpnSentenceCodes.toMachine {φ : ℕ → Sentence} (h : RpnSentenceCodes φ) :
    MachineSentenceCodes φ :=
  (BigSentenceCodes.ofRpnSentenceCodes h).toMachine

/-- **The 𝓔𝓒-sequence class, machine reading.** A machine-metered token stream that
un-RPNs to `ts z` — the interface a trader's serialized strategy is assembled through, with
`UnRpnContractsTo` the same pure-list contraction relation `BigSpliceStream`
(`Framework/Emission/WriteOut.lean`) uses. -/
def MachineSpliceStream (ts : ℕ → List ℕ) : Prop :=
  ∃ s : ℕ → List ℕ, MachineTokenStream s ∧ ∀ z, UnRpnContractsTo (s z) (ts z)

/-- **A written-out splice stream is machine-metered.** The `UnRpnContractsTo` instance of
the token-stream bridge; the contraction relation is a fact about the tokens alone, so it
crosses unchanged. -/
lemma BigSpliceStream.toMachine {ts : ℕ → List ℕ} (h : BigSpliceStream ts) :
    MachineSpliceStream ts := by
  obtain ⟨s, hs, hc⟩ := h
  exact ⟨s, hs.toMachine, hc⟩

/-! ## The value classes, machine reading

`BigDigits` and the two classes over it are poly-fueled digit *access*, so their machine
readings are the machine write-out of the accessed value as a single token, reached through
`BigTokenStream.ofBigDigits`.

The three bridges are one-way, and no converse is claimed for any of them. Two of the three
classes are hypotheses the development takes — `MachineDigits` throughout the emission
suite (`MachineSpliceStream.bigPayload` and every payload leaf built on it) and
`MachineRatCodes` on the rational lane (`PolyPositiveWidths.codes`,
`IntrospectionIntervalQuote.inverse_width_codes`, `PatientSettlementClock.active_codes`, and
the `thm:ref` / `thm:st` / `thm:perkno` endpoints). `MachineMachineCodes` is a hypothesis
too: `thm:halts`, `thm:loops`, `thm:dontwait` and `thm:incons` take it beside
`MachineDigits`, their claim families naming the machine through
`machineTokenStream_binNumeral_const`.

They carry value closure of their own, mirroring `BigDigits`': `MachineDigits.of_eq`,
`.const`, `.add`, `.mod_two` and `.natPair`, and `MachineRatCodes.const` and
`.toMachineDigits`. Each runs through the block/run change of view below and one
`Framework/Machine/DigitArithFP.lean` capstone, so the arithmetic is the same base-four loop
on both sides of the calibration and only the metering differs. -/

/-- **A written-out natural, machine reading.** Some `Complexity.FP` function of the unary day
emits a block-complete word decoding to the one token `x n`. Nothing bounds `x n` itself: as
with `MachineTokenStream`, the emitted word's *length* is what the polynomial bounds.

**Divergence from `BigDigits`, disclosed.** `BigDigits` is poly-fueled *random access* to the
digit `dig4 (x n) j` at a paired index `⟨n, j⟩`. `MachineDigits` is the emitted self-delimiting
block instead — the object `BigTokenStream.ofBigDigits` produces and the one a splicing
emitter consumes. The random-access spelling, `∃ D ∈ Complexity.FP, ∀ n j, … dig4 …`, is
deliberately **not** this class: it has no consumer and no cheap bridge, whereas the block
form makes `BigDigits.toMachine` two existing lemmas composed. The two calibrations therefore
differ in what they name, not only in how they meter it; the forward inclusion still runs in
the same direction as everywhere else in this file.

The machine reading of `BigDigits` (`Framework/Emission/DigitArith.lean`); the emission
suite's payload leaves (`MachineSpliceStream.bigPayload` and everything built on it) take
this class, and `MachineRatCodes` is three of them. -/
def MachineDigits (x : ℕ → ℕ) : Prop := MachineTokenStream (fun n => [x n])

/-- **Every fuel-metered digit certificate is machine-metered.**
`BigTokenStream.ofBigDigits` emits the value's self-delimiting digit block as a one-token
stream — the step `PolySegStream` cannot take — and the token-stream bridge carries that to
the machine reading. The inclusion is stated in this direction only; see the Reach section. -/
lemma BigDigits.toMachine {x : ℕ → ℕ} (h : BigDigits x) : MachineDigits x :=
  (BigTokenStream.ofBigDigits h).toMachine

/-! ### The digit word behind the block

`MachineDigits` carries a whole *block* — a base-four payload run followed by the terminator
`4` — because that is what an emitter splices. `DigitArithFP`'s word arithmetic
(`DigitFP.addW` and the rest) runs on the payload run alone, `DigitFP.IsDigitWord`. The two
lemmas below are the change of view between them, and every value combinator here is stated
by composing them around one `DigitArithFP` capstone.

Going from the block to the run is a *truncation*, not a search: a block-complete word
decoding to one token is a run of digits `< 4` followed by exactly one terminator digit,
which is three bits, so the run is `w.take (|w| - 3)` — `Cobham.takeLenFn_mem_FP` over
`TokenFold.dropLenFn_mem_FP`. `TokenFold.digitRun_of_blockWF` is the pure-list half, stated
beside `TokenFold.BlockWF` because nothing in it mentions the machine; the two `blockSplit`
inversions under it (`TokenFold.blockSplit_eq_nil_fst`, `.blockSplit_eq_single`) are what
make the block shape forced rather than assumed. -/

/-- **Reading a machine digit certificate as a digit word.** The emitted block truncated
three bits short of its terminator is a `DigitFP.IsDigitWord` whose `DigitFP.wordVal` is the
certified value. No side condition: the truncation is `Cobham.takeLenFn_mem_FP` of the word
against itself dropped by the constant three, so it costs one `FP` composition and bounds
nothing.

This is the shape every `DigitArithFP` capstone consumes; `MachineDigits.of_digitWord` is
the way back. -/
lemma MachineDigits.exists_digitWord {x : ℕ → ℕ} (h : MachineDigits x) :
    ∃ D : List Bool → List Bool, D ∈ Complexity.FP ∧
      (∀ d, DigitFP.IsDigitWord (D (unaryDay d))) ∧
      ∀ d, DigitFP.wordVal (D (unaryDay d)) = x d := by
  obtain ⟨F, hF, hwf, hd⟩ := h
  refine ⟨fun z => (F z).take ((F z).drop 3).length,
    Complexity.Cobham.takeLenFn_mem_FP
      (TokenFold.dropLenFn_mem_FP (FPFold.constFn_mem_FP [false, false, false]) hF) hF,
    fun d => ?_, fun d => ?_⟩
  · obtain ⟨cur, hcur, -, he⟩ := TokenFold.digitRun_of_blockWF (hwf d) (hd d)
    show DigitFP.IsDigitWord ((F (unaryDay d)).take ((F (unaryDay d)).drop 3).length)
    rw [he]
    exact DigitFP.isDigitWord_digitsToBits hcur
  · obtain ⟨cur, hcur, hval, he⟩ := TokenFold.digitRun_of_blockWF (hwf d) (hd d)
    show DigitFP.wordVal ((F (unaryDay d)).take ((F (unaryDay d)).drop 3).length) = x d
    rw [he, DigitFP.wordVal_digitsToBits hcur, hval]

/-- **Emitting a digit word as a machine digit certificate.** Appending the constant
terminator `digitBits 4` turns a payload run into one complete block, block-complete by
`TokenFold.blockWF_run` and decoding to the run's value by `TokenFold.decodeBits_run`.
Side condition: the run must consist of digits `< 4` at every day, which is exactly
`DigitFP.IsDigitWord`; nothing bounds the value. -/
lemma MachineDigits.of_digitWord {x : ℕ → ℕ} {D : List Bool → List Bool}
    (hD : D ∈ Complexity.FP)
    (hw : ∀ d, DigitFP.IsDigitWord (D (unaryDay d)))
    (hv : ∀ d, DigitFP.wordVal (D (unaryDay d)) = x d) : MachineDigits x := by
  refine ⟨fun z => D z ++ digitBits 4,
    Complexity.Cobham.appendFn_mem_FP hD (FPFold.constFn_mem_FP (digitBits 4)),
    fun d => ?_, fun d => ?_⟩
  · obtain ⟨cur, hcur, he⟩ := hw d
    show TokenFold.BlockWF (D (unaryDay d) ++ digitBits 4)
    rw [he]
    exact TokenFold.blockWF_run cur hcur
  · obtain ⟨cur, hcur, he⟩ := hw d
    have hval : digitVal cur = x d := by
      rw [← hv d, he, DigitFP.wordVal_digitsToBits hcur]
    show TokenFold.decodeBits (D (unaryDay d) ++ digitBits 4) = [x d]
    rw [he, TokenFold.decodeBits_run cur hcur, hval]

/-! ### Value closure

The combinators below mirror `BigDigits.of_eq`, `.const`, `.add`, `.mod_two` and `.natPair`
(`Framework/Emission/DigitArith.lean`), each by composing the two views above around one
`DigitArithFP` capstone. -/

/-- **Congruence.** The emitted block is untouched; only the certified value's name changes.
Fuel-side twin: `BigDigits.of_eq`. -/
lemma MachineDigits.of_eq {x x' : ℕ → ℕ} (h : MachineDigits x) (he : ∀ n, x n = x' n) :
    MachineDigits x' :=
  MachineTokenStream.of_eq h (fun n => by rw [he n])

/-- **A constant is machine-metered.** The emitted word is the constant base-four run of
`K` (`FPFold.constFn_mem_FP`), so the certificate does not read its argument at all. No
length side condition. Fuel-side twin: `BigDigits.const`. -/
lemma MachineDigits.const (K : ℕ) : MachineDigits (fun _ => K) :=
  MachineDigits.of_digitWord (D := fun _ => digitsToBits (natDigits4 K))
    (FPFold.constFn_mem_FP _)
    (fun _ => DigitFP.isDigitWord_digitsToBits (natDigits4_lt K))
    (fun _ => by rw [DigitFP.wordVal_digitsToBits (natDigits4_lt K), digitVal_natDigits4])

/-- **The class is closed under reindexing by a machine-readable map.** `MachineDigits` is a
one-token stream, so this is `MachineTokenStream.comp` at that stream; the reindexer arrives
as a unary ruler for the reason given there. Fuel-side twin: `BigDigits.comp`, whose
reindexer is a `PolyFueled` count. -/
lemma MachineDigits.comp {x : ℕ → ℕ} (h : MachineDigits x) {f : ℕ → ℕ}
    (hf : UnaryRuler f) : MachineDigits (fun n => x (f n)) :=
  MachineTokenStream.comp h hf

/-- **A unary ruler is a machine-metered value.** A value the machine knows only as a
*length* is emitted as one complete token block by `TokenFold.unaryBlock`, block-complete by
`TokenFold.blockWF_unaryBlock` and decoding to that length by
`TokenFold.decodeBits_unaryBlock`.

This is what makes the ruler the right machine rendering of a `PolyFueled c f` parameter in
a *token* position as well as in a reindexing one: the fuel side emits such a parameter as
`PolyTokenStream.polyTok`, and this is that step. The inclusion is strict in the useful
direction — `MachineDigits` admits values exponential in the day, a ruler cannot, since its
own word is polynomially long — so combinators that only place a value in the stream take
`MachineDigits` and reach a ruler-bearing caller through this lemma. No length side
condition beyond the ruler's own `FP` witness. -/
lemma MachineDigits.ofUnaryRuler {f : ℕ → ℕ}
    (hf : UnaryRuler f) :
    MachineDigits f := by
  refine ⟨fun z => TokenFold.unaryBlock (List.replicate (f z.length) false),
    TokenFold.unaryBlock_mem_FP hf, fun d => TokenFold.blockWF_unaryBlock _, fun d => ?_⟩
  rw [TokenFold.decodeBits_unaryBlock]
  simp

/-- **The class is closed under addition.** `DigitFP.addW` is the ripple-carry loop on the
two payload runs, already `Complexity.FP` with its value spec (`DigitFP.wordVal_addW`) and
its shape spec (`DigitFP.isDigitWord_addW`); this is the wrapper that feeds it the runs and
re-emits the sum as a block. The length side condition is discharged inside `addW`: its
output is a digit run one digit wider than the wider operand, so no bound on either value
is needed here. Fuel-side twin: `BigDigits.add` (whose carry loop is `PolyFueled.prec`). -/
lemma MachineDigits.add {x y : ℕ → ℕ} (hx : MachineDigits x) (hy : MachineDigits y) :
    MachineDigits (fun n => x n + y n) := by
  obtain ⟨X, hX, hXw, hXv⟩ := hx.exists_digitWord
  obtain ⟨Y, hY, hYw, hYv⟩ := hy.exists_digitWord
  refine MachineDigits.of_digitWord
    (D := fun z => DigitFP.addW (Complexity.pair (X z) (Y z)))
    (by simpa [Function.comp_def] using
      Complexity.mem_FP_comp (Complexity.Cobham.pairFn_mem_FP hX hY) DigitFP.addW_mem_FP)
    (fun d => DigitFP.isDigitWord_addW (hXw d) (hYw d))
    (fun d => by rw [DigitFP.wordVal_addW (hXw d) (hYw d), hXv d, hYv d])

/-- **The parity of a machine-metered value is a unary ruler.** The parity is the parity of
the payload run's lowest base-four digit, which `DigitFP.dig3` reads off the leading three
bits in constant depth; the day is rebuilt from the argument's length by
`Complexity.unaryLength_mem_FP`.

The conclusion is a *ruler* rather than a value certificate because that is the shape every
machine-side combinator takes a `ℕ → ℕ` parameter in — `MachineTokenStream.ifZero` and
`.concatVar` both — mirroring how `BigDigits.mod_two` delivers a `PolyFueled` count on the
fuel side. No length side condition: the ruler has length `0` or `1`. Fuel-side twin:
`BigDigits.mod_two`. -/
lemma MachineDigits.mod_two {x : ℕ → ℕ} (h : MachineDigits x) :
    UnaryRuler (fun n => x n % 2) := by
  show (fun z : List Bool => List.replicate (x z.length % 2) false) ∈ Complexity.FP
  obtain ⟨D, hD, hDw, hDv⟩ := h.exists_digitWord
  have hcomp : (fun z : List Bool => D (List.replicate z.length true)) ∈ Complexity.FP := by
    simpa [Function.comp_def] using
      Complexity.mem_FP_comp Complexity.unaryLength_mem_FP hD
  have hFP := DigitFP.dig3_mem_FP hcomp (fun d => List.replicate (d % 2) false)
  have heq : (fun z : List Bool =>
        DigitFP.dig3 (fun d => List.replicate (d % 2) false)
          (D (List.replicate z.length true)))
      = fun z : List Bool => List.replicate (x z.length % 2) false := by
    funext z
    obtain ⟨cur, hcur, he⟩ := hDw z.length
    have hval : digitVal cur = x z.length := by
      rw [← hDv z.length, he, DigitFP.wordVal_digitsToBits hcur]
    show DigitFP.dig3 _ (D (unaryDay z.length)) = _
    rw [he, ← hval]
    cases cur with
    | nil => simp
    | cons c cs =>
        rw [digitsToBits_cons,
          DigitFP.dig3_digitBits _ c (by have := hcur c (by simp); omega)]
        simp only [digitVal_cons]
        congr 1
        omega
  rwa [heq] at hFP

/-- **The class is closed under `Nat.pair`.** `Nat.pair a b` is `b * b + a` when `a < b` and
`a * a + a + b` otherwise, so this is the square-and-add split of `BigDigits.natPair` run on
payload runs: the two arms are `DigitFP.mulW` and `DigitFP.addW`, and the comparison is
`DigitFP.gtFlagW`, the machine counterpart of the fuel side's `ifzSel`-over-`ltNat` dispatch.
Both arms are computed and one is discarded — a constant factor, and what keeps the
certificate a single `Complexity.FP` composition rather than a second loop.

The length side condition is discharged inside `mulW`, which cuts its running product back to
a ruler assembled from the two operands, so nothing here bounds either value. Fuel-side twin:
`BigDigits.natPair`. -/
lemma MachineDigits.natPair {x y : ℕ → ℕ} (hx : MachineDigits x) (hy : MachineDigits y) :
    MachineDigits (fun n => Nat.pair (x n) (y n)) := by
  obtain ⟨X, hX, hXw, hXv⟩ := hx.exists_digitWord
  obtain ⟨Y, hY, hYw, hYv⟩ := hy.exists_digitWord
  have hmul : ∀ {P Q : List Bool → List Bool}, P ∈ Complexity.FP → Q ∈ Complexity.FP →
      (fun z => DigitFP.mulW (Complexity.pair (P z) (Q z))) ∈ Complexity.FP := by
    intro P Q hP hQ
    simpa [Function.comp_def] using
      Complexity.mem_FP_comp (Complexity.Cobham.pairFn_mem_FP hP hQ) DigitFP.mulW_mem_FP
  have hadd : ∀ {P Q : List Bool → List Bool}, P ∈ Complexity.FP → Q ∈ Complexity.FP →
      (fun z => DigitFP.addW (Complexity.pair (P z) (Q z))) ∈ Complexity.FP := by
    intro P Q hP hQ
    simpa [Function.comp_def] using
      Complexity.mem_FP_comp (Complexity.Cobham.pairFn_mem_FP hP hQ) DigitFP.addW_mem_FP
  have hAw : ∀ d, DigitFP.IsDigitWord
      (DigitFP.addW (Complexity.pair
        (DigitFP.mulW (Complexity.pair (Y (unaryDay d)) (Y (unaryDay d)))) (X (unaryDay d)))) :=
    fun d => DigitFP.isDigitWord_addW (DigitFP.isDigitWord_mulW (hYw d) (hYw d)) (hXw d)
  have hBw : ∀ d, DigitFP.IsDigitWord
      (DigitFP.addW (Complexity.pair
        (DigitFP.addW (Complexity.pair
          (DigitFP.mulW (Complexity.pair (X (unaryDay d)) (X (unaryDay d))))
          (X (unaryDay d)))) (Y (unaryDay d)))) :=
    fun d => DigitFP.isDigitWord_addW
      (DigitFP.isDigitWord_addW (DigitFP.isDigitWord_mulW (hXw d) (hXw d)) (hXw d)) (hYw d)
  refine MachineDigits.of_digitWord
    (D := fun z => Complexity.Cobham.selectHead (DigitFP.gtFlagW (Y z) (X z))
      (DigitFP.addW (Complexity.pair (DigitFP.mulW (Complexity.pair (Y z) (Y z))) (X z)))
      (DigitFP.addW (Complexity.pair
        (DigitFP.addW (Complexity.pair (DigitFP.mulW (Complexity.pair (X z) (X z))) (X z)))
        (Y z))))
    ?_ ?_ ?_
  · exact Complexity.Cobham.selectHeadFn_mem_FP (DigitFP.gtFlagW_mem_FP hY hX)
      (hadd (hmul hY hY) hX) (hadd (hadd (hmul hX hX) hX) hY)
  · intro d
    show DigitFP.IsDigitWord (Complexity.Cobham.selectHead _ _ _)
    rw [DigitFP.selectHead_gtFlagW (hYw d) (hXw d)]
    split_ifs
    · exact hBw d
    · exact hAw d
  · intro d
    show DigitFP.wordVal (Complexity.Cobham.selectHead _ _ _) = _
    rw [DigitFP.selectHead_gtFlagW (hYw d) (hXw d), hXv d, hYv d]
    split_ifs with h
    · rw [DigitFP.wordVal_addW
          (DigitFP.isDigitWord_addW (DigitFP.isDigitWord_mulW (hXw d) (hXw d)) (hXw d)) (hYw d),
        DigitFP.wordVal_addW (DigitFP.isDigitWord_mulW (hXw d) (hXw d)) (hXw d),
        DigitFP.wordVal_mulW (hXw d) (hXw d), hXv d, hYv d, Nat.pair, if_neg (by omega)]
    · rw [DigitFP.wordVal_addW (DigitFP.isDigitWord_mulW (hYw d) (hYw d)) (hXw d),
        DigitFP.wordVal_mulW (hYw d) (hYw d), hXv d, hYv d, Nat.pair, if_pos (by omega)]

/-! ### Naming an emitted token run

`BigDigits.ofTokenListNat` (`Framework/Emission/CodeSource.lean`) is the write-out lane's
*delivery* interface: an efficiently emitted token run is efficiently **named**, by
`tokenListNat ts = Nat.ofDigits 64 (ts ++ [63])`.  The machine twin below states the same
thing one metering to the left, and its proof is a tokenizing transduction rather than the
fuel side's digit-access assembly.

The device is `TokenFold.natFold_mem_FP` at a client that keeps no state and emits three
base-four digits per token.  The base-`64` Horner accumulation `acc := acc * 64 + t` costs
no word arithmetic at all, and that is the whole content of the construction: `64 = 4 ^ 3`,
so multiplying a base-four digit word by the base shifts it by exactly three digits, and
every token is below the sentinel `63 < 4 ^ 3`, so the name's digit run is *literally* the
concatenation of the tokens' three-digit zero-padded runs in stream order, sentinel last.
Neither `DigitFP.mulW` nor `DigitFP.addW` appears, and the accumulator needs no ruler
truncation: the emitter's per-token output is nine bits wide, a constant, so
`natFold_mem_FP`'s emission budget closes with `k = 0` and its step budget with `c = 0`. -/

/-- A token's three base-four digits, zero-padded — the fixed-width slot the base `64`
gives every token below `4 ^ 3`.  Little-endian, as `digitVal` reads. -/
private def padTriple (t : ℕ) : List ℕ := [t % 4, t / 4 % 4, t / 16 % 4]

private lemma padTriple_lt (t : ℕ) : ∀ d ∈ padTriple t, d < 4 := by
  intro d hd
  have hcases : d = t % 4 ∨ d = t / 4 % 4 ∨ d = t / 16 % 4 := by
    simpa [padTriple] using hd
  rcases hcases with rfl | rfl | rfl <;> omega

private lemma digitVal_padTriple {t : ℕ} (h : t < 64) : digitVal (padTriple t) = t := by
  simp only [padTriple, digitVal_cons, digitVal_nil]
  omega

private lemma padTriple_sentinel : padTriple 63 = [3, 3, 3] := rfl

private lemma mem_flatMap_padTriple {ts : List ℕ} :
    ∀ d ∈ ts.flatMap padTriple, d < 4 := by
  intro d hd
  obtain ⟨t, -, hdt⟩ := List.mem_flatMap.mp hd
  exact padTriple_lt t d hdt

/-- **The name's digit run is the tokens' padded runs, concatenated.**  This is the
base-`64` Horner accumulation, performed by concatenation because the base is `4 ^ 3`. -/
private lemma digitVal_flatMap_padTriple : ∀ ts : List ℕ, (∀ t ∈ ts, t < 64) →
    digitVal (ts.flatMap padTriple) = Nat.ofDigits 64 ts
  | [], _ => by simp
  | t :: ts, h => by
      rw [List.flatMap_cons, digitVal_append,
        digitVal_padTriple (h t (List.mem_cons_self ..)),
        digitVal_flatMap_padTriple ts (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        Nat.ofDigits_cons]
      simp [padTriple]

private lemma take_nine_digitsToBits : ∀ ds : List ℕ,
    (digitsToBits ds).take 9 = digitsToBits (ds.take 3)
  | [] => rfl
  | [_] => by simp [digitsToBits, digitBits]
  | [_, _] => by simp [digitsToBits, digitBits]
  | a :: b :: c :: ds => by
      have hsplit : digitsToBits (a :: b :: c :: ds)
          = digitsToBits [a, b, c] ++ digitsToBits ds := by
        simp [digitsToBits]
      have hlen : (digitsToBits [a, b, c]).length = 9 := by simp [digitsToBits]
      rw [hsplit, ← hlen, List.take_left]
      simp

/-- The emitter's per-token output, read at a well-formed token block: the block's first
three digits, zero-padded, which are the value's three base-four digits because a token
below `4 ^ 3` has no higher ones. -/
private lemma take_three_pad : ∀ (cur : List ℕ), (∀ d ∈ cur, d < 4) →
    (cur ++ [0, 0, 0]).take 3 = padTriple (digitVal cur) := by
  rintro (_ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩) h
  · rfl
  · have ha : a < 4 := h a (by simp)
    simp only [padTriple, digitVal_cons, digitVal_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
    exact ⟨by omega, by omega, by omega⟩
  · have ha : a < 4 := h a (by simp)
    have hb : b < 4 := h b (by simp)
    simp only [padTriple, digitVal_cons, digitVal_nil, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
    exact ⟨by omega, by omega, by omega⟩
  · have ha : a < 4 := h a (by simp)
    have hb : b < 4 := h b (by simp)
    have hc : c < 4 := h c (by simp)
    simp only [padTriple, digitVal_cons, List.cons_append,
      List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
    exact ⟨by omega, by omega, by omega⟩

private lemma natFold_out_flatMap (E : ℕ → List Bool) :
    ∀ (ts : List ℕ) (cli out : List Bool),
      (TokenFold.natFold (fun c (_ : ℕ) => c) (fun (_ : List Bool) t => E t)
        cli out ts).2 = out ++ ts.flatMap E
  | [], _, out => by simp [TokenFold.natFold]
  | t :: ts, cli, out => by
      rw [TokenFold.natFold, natFold_out_flatMap E ts, List.flatMap_cons,
        List.append_assoc]

open Complexity Complexity.Cobham in
/-- **The delivery interface, machine reading**: an efficiently emitted token run is
efficiently *named*.  Mirror of `BigDigits.ofTokenListNat`
(`Framework/Emission/CodeSource.lean`) statement for statement, one metering to the left.

Side condition, exactly the fuel side's: every emitted token is below the sentinel `63`, so
each occupies exactly three base-four digits and the name's digit run is the tokens' padded
runs concatenated in stream order with `padTriple 63 = [3, 3, 3]` last.  Nothing bounds the
*number* of tokens: the emitted word's length is what the polynomial bounds, as everywhere
in this file.

Proof kind: `C` composition.  Provenance: (a) `TokenFold.natFold_mem_FP`,
`digitVal_flatMap_padTriple`, `take_three_pad`; (b) `Cobham.takeLenFn_mem_FP`,
`Cobham.appendFn_mem_FP`. -/
lemma MachineDigits.ofTokenListNat {L : ℕ → List ℕ} (h : MachineTokenStream L)
    (hlt : ∀ n, ∀ t ∈ L n, t < 63) :
    MachineDigits (fun n => tokenListNat (L n)) := by
  obtain ⟨F, hF, -, hdec⟩ := h
  have hSTEP : (fun v : List Bool => fstBlock (sndBlock v)) ∈ Complexity.FP :=
    Complexity.mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have hEMIT : (fun v : List Bool =>
      (sndBlock (sndBlock v) ++ digitsToBits [0, 0, 0]).take 9) ∈ Complexity.FP := by
    have hraw := takeLenFn_mem_FP (a := fun _ : List Bool => List.replicate 9 true)
      (b := fun v : List Bool => sndBlock (sndBlock v) ++ digitsToBits [0, 0, 0])
      (FPFold.constFn_mem_FP _)
      (appendFn_mem_FP (Complexity.mem_FP_comp sndBlock_mem_FP sndBlock_mem_FP)
        (FPFold.constFn_mem_FP _))
    simpa using hraw
  have hSbnd : ∀ W cli tok : List Bool,
      (fstBlock (sndBlock (Complexity.pair W (Complexity.pair cli tok)))).length
        ≤ cli.length + tok.length + 0 := by
    intro W cli tok
    rw [sndBlock_pair, fstBlock_pair]
    omega
  have hEbnd : ∀ W cli tok : List Bool,
      ((sndBlock (sndBlock (Complexity.pair W (Complexity.pair cli tok)))
          ++ digitsToBits [0, 0, 0]).take 9).length
        ≤ (Polynomial.C 9).eval W.length + 0 * (cli.length + tok.length) := by
    intro W cli tok
    rw [List.length_take]
    simp only [Polynomial.eval_C]
    omega
  have hSeq : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      fstBlock (sndBlock (Complexity.pair W (Complexity.pair cli (digitsToBits cur))))
        = cli := by
    intro W cli cur _
    rw [sndBlock_pair, fstBlock_pair]
  have hEeq : ∀ (W cli : List Bool) (cur : List ℕ), (∀ d ∈ cur, d < 4) →
      (sndBlock (sndBlock (Complexity.pair W (Complexity.pair cli (digitsToBits cur))))
          ++ digitsToBits [0, 0, 0]).take 9
        = digitsToBits (padTriple (digitVal cur)) := by
    intro W cli cur hcur
    rw [sndBlock_pair, sndBlock_pair,
      show digitsToBits cur ++ digitsToBits [0, 0, 0]
        = digitsToBits (cur ++ [0, 0, 0]) from (digitsToBits_append _ _).symm,
      take_nine_digitsToBits, take_three_pad cur hcur]
  have hfold := TokenFold.natFold_mem_FP (STEPn := fun c (_ : ℕ) => c)
    (EMITn := fun (_ : List Bool) t => digitsToBits (padTriple t))
    (c := 0) (k := 0) (qQ := Polynomial.C 9)
    hSTEP hEMIT (FPFold.constFn_mem_FP []) hF hSbnd hEbnd hSeq hEeq [] []
  have hword : ∀ d : ℕ,
      (TokenFold.natFold (fun c (_ : ℕ) => c)
          (fun (_ : List Bool) t => digitsToBits (padTriple t)) [] []
          (undigitize (bitsToDigits (F (unaryDay d))))).2 ++ digitsToBits [3, 3, 3]
        = digitsToBits ((L d ++ [63]).flatMap padTriple) := by
    intro d
    rw [show undigitize (bitsToDigits (F (unaryDay d))) = L d from hdec d,
      natFold_out_flatMap, List.nil_append, digitsToBits_flatMap,
      ← digitsToBits_append, List.flatMap_append]
    simp [padTriple_sentinel]
  refine MachineDigits.of_digitWord
    (D := fun z => (TokenFold.natFold (fun c (_ : ℕ) => c)
        (fun (_ : List Bool) t => digitsToBits (padTriple t)) [] []
        (undigitize (bitsToDigits (F z)))).2 ++ digitsToBits [3, 3, 3])
    (appendFn_mem_FP hfold (FPFold.constFn_mem_FP _)) (fun d => ?_) (fun d => ?_)
  · rw [hword d]
    exact DigitFP.isDigitWord_digitsToBits mem_flatMap_padTriple
  · have hbound : ∀ t ∈ L d ++ [63], t < 64 := by
      intro t ht
      rcases List.mem_append.mp ht with hm | hm
      · exact lt_trans (hlt d t hm) (by norm_num)
      · simp only [List.mem_singleton] at hm
        omega
    rw [hword d, DigitFP.wordVal_digitsToBits mem_flatMap_padTriple,
      digitVal_flatMap_padTriple _ hbound]
    rfl

open Complexity Complexity.Cobham in
/-- **A machine-metered stream's token count is a unary ruler.**

The count is *not* the emitted word's length — tokens have variable width — so it is read
by the same tokenizing fold every other client of the stream runs
(`TokenFold.natFold_mem_FP`), at the client that keeps no state and emits one mark per
token.  Its emission budget closes with `k = 0` because that mark is a constant.

This is the machine reading of the length parameter `PolySegStream`'s own certificate
carries explicitly (`hslen`, a `PolyFueled` length code), and it is what a framing emitter
needs: `structuredLeafBlock` (`Construction/LUV/SourceCodec.lean`) writes a unary run of
the payload's *token* count. No length side condition. -/
lemma MachineTokenStream.lengthRuler {t : ℕ → List ℕ} (h : MachineTokenStream t) :
    UnaryRuler (fun n => (t n).length) := by
  obtain ⟨F, hF, -, hdec⟩ := h
  show (fun z : List Bool => List.replicate (t z.length).length false) ∈ Complexity.FP
  have hDay : (fun z : List Bool => F (List.replicate z.length true)) ∈ Complexity.FP := by
    simpa [Function.comp_def] using
      Complexity.mem_FP_comp Complexity.unaryLength_mem_FP hF
  have hSTEP : (fun v : List Bool => fstBlock (sndBlock v)) ∈ Complexity.FP :=
    Complexity.mem_FP_comp sndBlock_mem_FP fstBlock_mem_FP
  have hfold := TokenFold.natFold_mem_FP (STEPn := fun c (_ : ℕ) => c)
    (EMITn := fun (_ : List Bool) (_ : ℕ) => ([false] : List Bool))
    (c := 0) (k := 0) (qQ := Polynomial.C 1)
    hSTEP (FPFold.constFn_mem_FP [false]) (FPFold.constFn_mem_FP []) hDay
    (fun W cli tok => by rw [sndBlock_pair, fstBlock_pair]; omega)
    (fun W cli tok => by simp)
    (fun W cli cur _ => by rw [sndBlock_pair, fstBlock_pair])
    (fun _ _ _ _ => rfl) [] []
  have heq : (fun z : List Bool => (TokenFold.natFold (fun c (_ : ℕ) => c)
        (fun (_ : List Bool) (_ : ℕ) => ([false] : List Bool)) [] []
        (undigitize (bitsToDigits (F (List.replicate z.length true))))).2)
      = fun z : List Bool => List.replicate (t z.length).length false := by
    funext z
    rw [show undigitize (bitsToDigits (F (List.replicate z.length true))) = t z.length from
        hdec z.length,
      natFold_out_flatMap, List.nil_append, TokenFold.flatMap_const_singleton]
  rwa [heq] at hfold

/-- **The machine-code write-out class, machine reading.** `MachineDigits` at the machine's
*source* number, the same naming map `Code.sourceNat` that `DigitMachineCodes`
(`Framework/Emission/WriteOut.lean`) uses, so the two classes differ only in the metering
device.

Bound by `thm:halts`, `thm:loops`, `thm:dontwait` and `thm:incons`, whose claim families
name the machine through the compact numeral emitter's machine reading
`machineTokenStream_binNumeral_const` (Reach section). -/
def MachineMachineCodes (m : ℕ → Nat.Partrec.Code) : Prop :=
  MachineDigits (fun n => Nat.Partrec.Code.sourceNat (m n))

/-- **A written-out machine-code sequence is machine-metered.** `DigitMachineCodes` is
`BigDigits` at the source number, so this is the digit bridge at that argument. -/
lemma DigitMachineCodes.toMachine {m : ℕ → Nat.Partrec.Code} (h : DigitMachineCodes m) :
    MachineMachineCodes m :=
  BigDigits.toMachine h

/-- **The rational write-out class, machine reading.** Field for field with `DigitRatCodes`
(`Framework/Emission/WriteOut.lean`), `MachineDigits` in place of `BigDigits`: the numerator's
`ℤ`-code, its magnitude and the denominator are carried as separate runs, the representation
choice disclosed at that class and unchanged here.

`DigitRatCodes` is kept as the fuel-side class rather than collapsed into this one: it is
the producer route in (`DigitRatCodes.ofPolyRatCodes`, `.natCast`, `.const`), it carries the
`def:ec` paper node on the fuel side, and it is the subject of the strictness proof
`digitRatCodes_two_pow_inv_not_polyRatCodes`. Consumers bind this class; producers build
that one and cross by `DigitRatCodes.toMachine`, exactly as `BigDigits`/`MachineDigits` and
`BigSentenceCodes`/`MachineSentenceCodes` are arranged. -/
structure MachineRatCodes (q : ℕ → ℚ) : Prop where
  /-- Machine write-out of the `ℤ`-code of the numerator, `⌜(q n).num⌝`. -/
  numCode : MachineDigits (fun n => Encodable.encode (q n).num)
  /-- Machine write-out of the numerator's magnitude. -/
  natAbsNum : MachineDigits (fun n => (q n).num.natAbs)
  /-- Machine write-out of the denominator. -/
  den : MachineDigits (fun n => (q n).den)

/-- **A written-out rational sequence is machine-metered.** The digit bridge at each of the
three runs; no field is derived from another, exactly as in `DigitRatCodes`. -/
lemma DigitRatCodes.toMachine {q : ℕ → ℚ} (h : DigitRatCodes q) : MachineRatCodes q :=
  ⟨BigDigits.toMachine h.numCode, BigDigits.toMachine h.natAbsNum,
    BigDigits.toMachine h.den⟩

/-- **A constant rational is machine-metered.** Each of the three runs is a constant, so
this is `MachineDigits.const` field for field. No length side condition. Fuel-side twin:
`DigitRatCodes.const`, which routes through `PolyRatCodes` instead — here the three runs
are already separate, so no unpairing is involved. -/
lemma MachineRatCodes.const (r : ℚ) : MachineRatCodes (fun _ => r) :=
  ⟨MachineDigits.const _, MachineDigits.const _, MachineDigits.const _⟩

/-- **The flat code of a machine-metered rational is machine-metered.** `⌜q n⌝` is the pair
`⟪⌜(q n).num⌝, (q n).den⟫`, which `MachineDigits.natPair` assembles from two of the three runs
the class carries. This is the interface a splicing emitter consumes — the machine reading of
`DigitRatCodes.toBigDigits`, and the reason `DigitFP.mulW` exists. Fuel-side twin:
`DigitRatCodes.toBigDigits`. -/
lemma MachineRatCodes.toMachineDigits {q : ℕ → ℚ} (h : MachineRatCodes q) :
    MachineDigits (fun n => Encodable.encode (q n)) :=
  (h.numCode.natPair h.den).of_eq (fun n => (encode_rat_eq (q n)).symm)

/-- The flat code of a ruler-measured natural, read as a rational, is a machine-metered
digit block: `⌜(n : ℚ)⌝ = ⟪2n, 1⟫` (`encode_rat_natCast`), so it is `MachineDigits.natPair`
of the doubled ruler and the constant `1`.  This is what `MachineSpliceStream`'s constant
leaf consumes, and it replaces the fuel-metered `PolyRatCodes` rational-cast helper: nothing
here bounds `f`'s value. -/
lemma ratNatCast_machineDigits {f : ℕ → ℕ} (hf : UnaryRuler f) :
    MachineDigits (fun x ↦ Encodable.encode (((f x : ℕ) : ℚ))) :=
  ((MachineDigits.ofUnaryRuler (hf.add hf)).natPair
      (MachineDigits.ofUnaryRuler (UnaryRuler.const 1))).of_eq (fun x ↦ by
    rw [encode_rat_natCast]
    congr 1
    omega)

/-- **Congruence.** The three runs are untouched; only the certified sequence's name
changes. Fuel-side twin: `DigitRatCodes.of_eq`. -/
lemma MachineRatCodes.of_eq {q q' : ℕ → ℚ} (h : MachineRatCodes q) (he : ∀ n, q n = q' n) :
    MachineRatCodes q' := by
  rwa [funext he] at h

/-- **The class is closed under reindexing by a machine-readable map.** `MachineDigits.comp`
at each of the three runs. Fuel-side twin: `DigitRatCodes.comp`. -/
lemma MachineRatCodes.comp {q : ℕ → ℚ} (h : MachineRatCodes q) {f : ℕ → ℕ}
    (hf : UnaryRuler f) : MachineRatCodes (fun n => q (f n)) :=
  ⟨h.numCode.comp hf, h.natAbsNum.comp hf, h.den.comp hf⟩

/-- **The sign is a unary ruler.** `⌜i⌝` is even exactly when `i ≥ 0`
(`encode_int_mod_two`), so the sign bit is the parity of the numerator's code, which
`MachineDigits.mod_two` reads off that run's lowest base-four digit.

The conclusion is a ruler rather than a value certificate for the reason `mod_two`'s is:
a `0`/`1` flag is consumed in reindexing position by `MachineTokenStream.ifZero` and
`MachineSpliceStream.ifZero`. Fuel-side twin: `DigitRatCodes.sign`, whose conclusion is
`∃ c, PolyFueled c …` for the same reason. -/
lemma MachineRatCodes.sign {q : ℕ → ℚ} (h : MachineRatCodes q) :
    UnaryRuler (fun n => if (q n).num < 0 then 1 else 0) :=
  h.numCode.mod_two.of_eq (fun n => encode_int_mod_two (q n).num)

/-- **The reciprocal, by representation rather than arithmetic.** For a positive rational
the inverse exchanges numerator magnitude and denominator, so two of the three runs simply
swap and the third — the numerator's `ℤ`-code, which is the doubled denominator — is one
`MachineDigits.add`. No digit-level division, unpairing or normalization is involved, which
is what the split representation buys; the transport from the fuel proof is exact, `add` for
`add` and permutation for permutation. Fuel-side twin: `DigitRatCodes.inv_of_pos`. -/
lemma MachineRatCodes.inv_of_pos {q : ℕ → ℚ} (h : MachineRatCodes q) (hpos : ∀ n, 0 < q n) :
    MachineRatCodes (fun n => 1 / q n) := by
  have hnum : ∀ n, (1 / q n).num = ((q n).den : ℤ) := fun n => by
    rw [one_div]
    simp [Rat.num_inv, Int.sign_eq_one_iff_pos.mpr (Rat.num_pos.mpr (hpos n))]
  have hden : ∀ n, (1 / q n).den = (q n).num.natAbs := fun n => by
    rw [one_div]; exact Rat.den_inv_of_ne_zero (ne_of_gt (hpos n))
  exact ⟨(h.den.add h.den).of_eq (fun n => by
      rw [hnum n, encode_int_natCast]; omega),
    h.den.of_eq (fun n => by rw [hnum n, Int.natAbs_natCast]),
    h.natAbsNum.of_eq (fun n => (hden n).symm)⟩

/-! ## The bounded-iteration asymmetry

The two `example`s below are the in-Lean form of the calibration the Reach section states in
prose. Each restates an existing lemma's signature and is discharged by naming it, so what
they record is a pair of *signatures*, read against each other.

At a fixed code, `PolyFueled` is a poly-time, `O(log n)`-workspace device: `evaln`'s `n ≤ k`
guard and `PolyFueled`'s own `IsPolyBounded` conjuncts bound every value the run handles by a
polynomial in the input, hence by `O(log n)` bits, and a fixed code is a constant-depth nest
of loops. `Complexity.FP` is poly-time with polynomial workspace.

The gap shows at the bounded iteration each side offers. `PolyFueled.prec` asks that the
iterated state's numeric **value** stay polynomially bounded; `FPFold.foldlBits_mem_FP` asks
that its **length** do so. A converse bridge would need the second shape on the fuel side, and
only the `Complexity.FP` side has it. -/

example {cf cg : Nat.Partrec.Code} {f g : ℕ → ℕ}
    (hf : PolyFueled cf f) (hg : PolyFueled cg g)
    {st : ℕ → ℕ → ℕ} (h0 : ∀ a, st a 0 = f a)
    (hS : ∀ a j, st a (j + 1) = g (Nat.pair a (Nat.pair j (st a j))))
    (hst : IsPolyBounded (fun m => st m.unpair.1 m.unpair.2)) :
    PolyFueled (cf.prec cg) (fun m => st m.unpair.1 m.unpair.2) :=
  PolyFueled.prec hf hg h0 hS hst

example {A B W S : List Bool → List Bool}
    (hA : A ∈ Complexity.FP) (hB : B ∈ Complexity.FP) (hW : W ∈ Complexity.FP)
    (hS : S ∈ Complexity.FP) (e : List Bool) (p : Polynomial ℕ)
    (hbnd : ∀ z u, u.length ≤ (S z).length →
      (FPFold.foldlBits A B (W z) e u).length ≤ p.eval ((W z).length + (S z).length)) :
    (fun z => FPFold.foldlBits A B (W z) e (S z)) ∈ Complexity.FP :=
  FPFold.foldlBits_mem_FP hA hB hW hS e p hbnd

end LogicalInduction
