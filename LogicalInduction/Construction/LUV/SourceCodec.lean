import LogicalInduction.Construction.LUV.PaperLUV
import LogicalInduction.Framework.Emission.RpnEmission
import LogicalInduction.Framework.Emission.RpnSplice
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Structured Foundation-arithmetic RPN codec and the compact `ℒₒᵣ` numeral

This module is the RPN leaf codec that turns one Foundation arithmetic proposition into a
single atomic block of the strategy grammar, together with the compact `ℒₒᵣ` numeral
`binNumeral`.  Nothing here is a paper node; the module supplies `def:ec` (tex:753)
emission certificates consumed downstream.

The public leaf framing is

  `[1, 0, polarity] ++ replicate payload.length 1 ++ [0] ++ payload ++ [19]`.

Sentence code `0` is the dispatch selector for the structured leaf, so the ordinary
two-token sentence escape `[1, code]` for `code ≠ 0` is untouched and the two grammars
agree off code `0` (`parseRpn_of_legacy`).  The unary payload length keeps every framing
token bounded, the payload is the arithmetic alphabet `0..18`, and the reserved terminator
`19` — which the alphabet never contains — closes the block, so a scanner finds the
boundary without replaying the Foundation decoder.  Gödel codes are built by parser
contraction and never emitted.

Objects defined here: the encoders `encodeStructuredNat`, `encodeArithmeticTermSymbols`
and `encodeArithmeticFormulaSymbols` over the complete Foundation arithmetic syntax, with
exact suffix-preserving round trips and the matching decoders
`parseArithmeticTermSymbols` / `parseArithmeticFormulaSymbols`; the payload-generic leaf
block `structuredLeafBlock` and its normal-form instance `structuredPaperPrimeBlock`,
contracting to the public tag-`5` atom `paperPrimeSentence`; the normal-form-metered class
`PolyArithmeticFormulaSeq`; and the compact numeral `binNumeral` with its symbol list
`binNumeralEnc`.

The main results are `structuredPaperPrime_rpnSentenceCodes`, the emission lifting the
LUV threshold layer consumes, and `polySegStream_binNumeralEnc` /
`polySegStream_binNumeral_const`, which are what let a write-out value stream name its own
values — consumed by `Construction/LUV/ArithmeticSource.lean` and
`Construction/Knowledge/SubstEmission.lean`.  `binNumeral_val`
names the value in every model of `𝗣𝗔⁻`.

`PolyArithmeticFormulaSeq` is retained as the strictness foil for the paper's class, not
as the development's condition: it meters Foundation's negation-normal form, which charges
a `⟺` twice per side (`dd:nnf`).  The paper's class is `PolyArithmeticSourceSeq`
(`Construction/LUV/ArithmeticSource.lean`), into which this one embeds by
`PolyArithmeticFormulaSeq.toSource`.

The compact numeral recurses in base **four**, not base two, because a base-two Horner
step branches on parity and yields two different symbol-run widths, which
`PolySegStream.blocks` cannot emit.  Base four gives two uniform runs driven by `len4` and
`dig4`, the two primitives `BigDigits` certifies.  Relatedly, a term's cost is the cost of
its *name*, not of the value denoted: Foundation's `Semiterm.Operator.numeral` is unary
and so costs `2v - 1`, while `binNumeral` names `v` in `O(log v)` nodes.  The paper fixes
no numeral notation (tex:614, tex:757), so neither count is a narrowing of `def:ec`.

Every token the codec emits is a fixed small constant, the reserved terminator appears
exactly once, and `structuredPaperPrimeBlock_span` is the fact the metering classification
in `scripts/coverage-classification.md` cites.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Propositional

/-! ## Structured naturals and arithmetic syntax

Naturals travel as a recursive small-token binary code, never as one large value, and the
Foundation term/formula constructors get one fixed tag each. -/

/-- Binary code of a natural in the tags `0`/`1`/`2`. -/
def encodeStructuredNat : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
      if (n + 1) % 2 = 0 then 1 :: encodeStructuredNat ((n + 1) / 2)
      else 2 :: encodeStructuredNat ((n + 1) / 2)
termination_by n => n
decreasing_by all_goals exact Nat.div_lt_self (Nat.succ_pos _) (by norm_num)

/-- Complete Foundation arithmetic term syntax: bound/free variables, `0`, `1`, `+`, `*`. -/
def encodeArithmeticTermSymbols {k : ℕ} : ArithmeticSemiterm ℕ k → List ℕ
  | .bvar x => 3 :: encodeStructuredNat x
  | .fvar x => 4 :: encodeStructuredNat x
  | .func Language.ORing.Func.zero _ => [5]
  | .func Language.ORing.Func.one _ => [6]
  | .func Language.ORing.Func.add v =>
      7 :: (encodeArithmeticTermSymbols (v 0) ++ encodeArithmeticTermSymbols (v 1))
  | .func Language.ORing.Func.mul v =>
      8 :: (encodeArithmeticTermSymbols (v 0) ++ encodeArithmeticTermSymbols (v 1))

/-- All Foundation arithmetic formula constructors in negation-normal form. -/
def encodeArithmeticFormulaSymbols {k : ℕ} : ArithmeticSemiformula ℕ k → List ℕ
  | .verum => [9]
  | .falsum => [10]
  | .rel Language.ORing.Rel.eq v =>
      11 :: (encodeArithmeticTermSymbols (v 0) ++ encodeArithmeticTermSymbols (v 1))
  | .nrel Language.ORing.Rel.eq v =>
      12 :: (encodeArithmeticTermSymbols (v 0) ++ encodeArithmeticTermSymbols (v 1))
  | .rel Language.ORing.Rel.lt v =>
      13 :: (encodeArithmeticTermSymbols (v 0) ++ encodeArithmeticTermSymbols (v 1))
  | .nrel Language.ORing.Rel.lt v =>
      14 :: (encodeArithmeticTermSymbols (v 0) ++ encodeArithmeticTermSymbols (v 1))
  | .and φ ψ =>
      15 :: (encodeArithmeticFormulaSymbols φ ++ encodeArithmeticFormulaSymbols ψ)
  | .or φ ψ =>
      16 :: (encodeArithmeticFormulaSymbols φ ++ encodeArithmeticFormulaSymbols ψ)
  | .all φ => 17 :: encodeArithmeticFormulaSymbols φ
  | .exs φ => 18 :: encodeArithmeticFormulaSymbols φ

/-! ## Round trips

Each encoder is inverted exactly by its numeric parser, with the unread suffix preserved. -/

/-- The binary natural code is inverted exactly, leaving the unread suffix. -/
lemma parseStructuredNat_encode (n : ℕ) (tail : List ℕ) {fuel : ℕ}
    (hfuel : (encodeStructuredNat n).length ≤ fuel) :
    parseStructuredNat fuel (encodeStructuredNat n ++ tail) = some (n, tail) := by
  induction n using Nat.strong_induction_on generalizing fuel tail with
  | h n ih =>
      cases n with
      | zero =>
          cases fuel with
          | zero => simp [encodeStructuredNat] at hfuel
          | succ fuel => simp [encodeStructuredNat, parseStructuredNat]
      | succ n =>
          have hdiv : (n + 1) / 2 < n + 1 :=
            Nat.div_lt_self (Nat.succ_pos n) (by norm_num)
          rw [encodeStructuredNat]
          split <;> rename_i hpar
          · cases fuel with
            | zero => simp [encodeStructuredNat, hpar] at hfuel
            | succ fuel =>
                simp only [List.cons_append, parseStructuredNat]
                rw [ih _ hdiv tail (fuel := fuel)
                  (by simpa [encodeStructuredNat, hpar] using hfuel)]
                have heven : 2 * ((n + 1) / 2) = n + 1 := by omega
                simp [heven]
          · cases fuel with
            | zero => simp [encodeStructuredNat, hpar] at hfuel
            | succ fuel =>
                simp only [List.cons_append, parseStructuredNat]
                rw [ih _ hdiv tail (fuel := fuel)
                  (by simpa [encodeStructuredNat, hpar] using hfuel)]
                have hodd : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
                simp [hodd]

/-- The term encoder is inverted exactly by the numeric parser, leaving the unread
suffix, provided the fuel covers the encoded run. -/
lemma parseStructuredArithmeticTerm_encode
    {k : ℕ} (t : ArithmeticSemiterm ℕ k) (tail : List ℕ) {fuel depth : ℕ}
    (hfuel : (encodeArithmeticTermSymbols t).length ≤ fuel) :
    parseStructuredArithmeticTerm fuel depth
      (encodeArithmeticTermSymbols t ++ tail) = some (Encodable.encode t, tail) := by
  induction t generalizing fuel tail depth with
  | bvar x =>
      cases fuel with
      | zero => simp [encodeArithmeticTermSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticTermSymbols, List.cons_append,
            parseStructuredArithmeticTerm]
          rw [parseStructuredNat_encode x tail (by
            simpa [encodeArithmeticTermSymbols] using hfuel)]
          simp [x.isLt, LO.FirstOrder.Semiterm.encode_eq_toNat,
            LO.FirstOrder.Semiterm.toNat]
  | fvar x =>
      cases fuel with
      | zero => simp [encodeArithmeticTermSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticTermSymbols, List.cons_append,
            parseStructuredArithmeticTerm]
          rw [parseStructuredNat_encode x tail (by
            simpa [encodeArithmeticTermSymbols] using hfuel)]
          rfl
  | func f v ih =>
      rcases f with _ | _ | _ | _
      · have henc : Encodable.encode Language.ORing.Func.zero = 0 := rfl
        cases fuel <;>
          simp [encodeArithmeticTermSymbols, parseStructuredArithmeticTerm,
            arithmeticFuncCode, henc,
            LO.FirstOrder.Semiterm.encode_eq_toNat,
            LO.FirstOrder.Semiterm.toNat, Matrix.vecToNat] at hfuel ⊢
      · have henc : Encodable.encode Language.ORing.Func.one = 1 := rfl
        cases fuel <;>
          simp [encodeArithmeticTermSymbols, parseStructuredArithmeticTerm,
            arithmeticFuncCode, henc,
            LO.FirstOrder.Semiterm.encode_eq_toNat,
            LO.FirstOrder.Semiterm.toNat, Matrix.vecToNat] at hfuel ⊢
      · cases fuel with
        | zero => simp [encodeArithmeticTermSymbols] at hfuel
        | succ fuel =>
            simp only [encodeArithmeticTermSymbols, List.cons_append,
              List.append_assoc, parseStructuredArithmeticTerm]
            rw [ih 0 (encodeArithmeticTermSymbols (v 1) ++ tail) (by
              simp [encodeArithmeticTermSymbols] at hfuel; omega), Option.bind_some,
              ih 1 tail (by simp [encodeArithmeticTermSymbols] at hfuel; omega)]
            rfl
      · cases fuel with
        | zero => simp [encodeArithmeticTermSymbols] at hfuel
        | succ fuel =>
            simp only [encodeArithmeticTermSymbols, List.cons_append,
              List.append_assoc, parseStructuredArithmeticTerm]
            rw [ih 0 (encodeArithmeticTermSymbols (v 1) ++ tail) (by
              simp [encodeArithmeticTermSymbols] at hfuel; omega), Option.bind_some,
              ih 1 tail (by simp [encodeArithmeticTermSymbols] at hfuel; omega)]
            rfl

/-- The formula encoder is inverted exactly by the numeric parser, leaving the unread
suffix, provided the fuel covers the encoded run. -/
lemma parseStructuredArithmeticFormula_encode
    {k : ℕ} (φ : ArithmeticSemiformula ℕ k) (tail : List ℕ) {fuel depth : ℕ}
    (hfuel : (encodeArithmeticFormulaSymbols φ).length ≤ fuel) :
    parseStructuredArithmeticFormula fuel depth
      (encodeArithmeticFormulaSymbols φ ++ tail) = some (Encodable.encode φ, tail) := by
  induction φ generalizing fuel tail depth with
  | verum => cases fuel <;> simp [encodeArithmeticFormulaSymbols,
      parseStructuredArithmeticFormula, LO.FirstOrder.Semiformula.encode_eq_toNat,
      LO.FirstOrder.Semiformula.toNat] at hfuel ⊢
  | falsum => cases fuel <;> simp [encodeArithmeticFormulaSymbols,
      parseStructuredArithmeticFormula, LO.FirstOrder.Semiformula.encode_eq_toNat,
      LO.FirstOrder.Semiformula.toNat] at hfuel ⊢
  | rel r v =>
      rcases r with _ | _ <;> cases fuel with
      | zero => simp [encodeArithmeticFormulaSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticFormulaSymbols, List.cons_append,
            List.append_assoc, parseStructuredArithmeticFormula]
          rw [parseStructuredArithmeticTerm_encode (v 0)
            (encodeArithmeticTermSymbols (v 1) ++ tail) (by
              simp [encodeArithmeticFormulaSymbols] at hfuel; omega), Option.bind_some,
            parseStructuredArithmeticTerm_encode (v 1) tail (by
              simp [encodeArithmeticFormulaSymbols] at hfuel; omega)]
          rfl
  | nrel r v =>
      rcases r with _ | _ <;> cases fuel with
      | zero => simp [encodeArithmeticFormulaSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticFormulaSymbols, List.cons_append,
            List.append_assoc, parseStructuredArithmeticFormula]
          rw [parseStructuredArithmeticTerm_encode (v 0)
            (encodeArithmeticTermSymbols (v 1) ++ tail) (by
              simp [encodeArithmeticFormulaSymbols] at hfuel; omega), Option.bind_some,
            parseStructuredArithmeticTerm_encode (v 1) tail (by
              simp [encodeArithmeticFormulaSymbols] at hfuel; omega)]
          rfl
  | and φ ψ ihφ ihψ =>
      cases fuel with
      | zero => simp [encodeArithmeticFormulaSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticFormulaSymbols, List.cons_append,
            List.append_assoc, parseStructuredArithmeticFormula]
          rw [ihφ (encodeArithmeticFormulaSymbols ψ ++ tail) (by
            simp [encodeArithmeticFormulaSymbols] at hfuel; omega), Option.bind_some,
            ihψ tail (by simp [encodeArithmeticFormulaSymbols] at hfuel; omega)]
          rfl
  | or φ ψ ihφ ihψ =>
      cases fuel with
      | zero => simp [encodeArithmeticFormulaSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticFormulaSymbols, List.cons_append,
            List.append_assoc, parseStructuredArithmeticFormula]
          rw [ihφ (encodeArithmeticFormulaSymbols ψ ++ tail) (by
            simp [encodeArithmeticFormulaSymbols] at hfuel; omega), Option.bind_some,
            ihψ tail (by simp [encodeArithmeticFormulaSymbols] at hfuel; omega)]
          rfl
  | all φ ih =>
      cases fuel with
      | zero => simp [encodeArithmeticFormulaSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticFormulaSymbols, List.cons_append,
            parseStructuredArithmeticFormula]
          rw [ih tail (by simpa [encodeArithmeticFormulaSymbols] using hfuel)]
          rfl
  | exs φ ih =>
      cases fuel with
      | zero => simp [encodeArithmeticFormulaSymbols] at hfuel
      | succ fuel =>
          simp only [encodeArithmeticFormulaSymbols, List.cons_append,
            parseStructuredArithmeticFormula]
          rw [ih tail (by simpa [encodeArithmeticFormulaSymbols] using hfuel)]
          rfl

/-- Decode one arithmetic term from a symbol stream.  This and
`parseArithmeticFormulaSymbols` are the client-facing inverses of the two encoders: they
return the Foundation object and the unread suffix, rather than a raw code. -/
def parseArithmeticTermSymbols (k : ℕ) (symbols : List ℕ) :
    Option (ArithmeticSemiterm ℕ k × List ℕ) :=
  (parseStructuredArithmeticTerm symbols.length k symbols).bind fun p =>
    (Encodable.decode (α := ArithmeticSemiterm ℕ k) p.1).map fun t => (t, p.2)

/-- Decode one arithmetic formula from a symbol stream. -/
def parseArithmeticFormulaSymbols (k : ℕ) (symbols : List ℕ) :
    Option (ArithmeticSemiformula ℕ k × List ℕ) :=
  (parseStructuredArithmeticFormula symbols.length k symbols).bind fun p =>
    (Encodable.decode (α := ArithmeticSemiformula ℕ k) p.1).map fun φ => (φ, p.2)

/-- **The term round trip at the client interface**: `parseArithmeticTermSymbols` inverts
`encodeArithmeticTermSymbols` back to a `Semiterm`, not to a raw code. -/
lemma parseArithmeticTermSymbols_encode {k : ℕ} (t : ArithmeticSemiterm ℕ k)
    (tail : List ℕ) :
    parseArithmeticTermSymbols k (encodeArithmeticTermSymbols t ++ tail) =
      some (t, tail) := by
  rw [parseArithmeticTermSymbols, parseStructuredArithmeticTerm_encode t tail (by simp)]
  simp [Encodable.encodek]

/-- **The formula round trip at the client interface**: `parseArithmeticFormulaSymbols`
inverts `encodeArithmeticFormulaSymbols` back to a `Semiformula`, not to a raw code. -/
lemma parseArithmeticFormulaSymbols_encode {k : ℕ} (φ : ArithmeticSemiformula ℕ k)
    (tail : List ℕ) :
    parseArithmeticFormulaSymbols k (encodeArithmeticFormulaSymbols φ ++ tail) =
      some (φ, tail) := by
  rw [parseArithmeticFormulaSymbols, parseStructuredArithmeticFormula_encode φ tail (by simp)]
  simp [Encodable.encodek]

/-! ## The structured paper-prime leaf

One arithmetic proposition as a single atomic RPN block: the `[1, 0]` dispatch prefix, the
polarity bit, a unary payload length, the payload, and the reserved terminator.  The block
is defined over an arbitrary payload list, so the source-metered leaf
`structuredPaperSourcePrimeBlock` (`Construction/LUV/ArithmeticSource.lean`) is the same
block at the paper's own source run and inherits contraction, emission and framing from here. -/

/-- **The leaf block over an arbitrary payload**: the `[1, 0]` dispatch prefix, the
polarity bit, the payload length in unary, the payload, and the reserved terminator. -/
def structuredLeafBlock (positive : Bool) (payload : List ℕ) : List ℕ :=
  [1, 0, Encodable.encode positive] ++
    (List.replicate payload.length 1 ++ (0 :: payload ++ [19]))

/-- A leaf block is never empty; this is the fuel side condition `parseRpn` asks for. -/
lemma structuredLeafBlock_length_pos (positive : Bool) (payload : List ℕ) :
    0 < (structuredLeafBlock positive payload).length := by
  simp [structuredLeafBlock]

/-- The atomic block whose contraction is `paperPrimeSentence positive φ`. -/
def structuredPaperPrimeBlock (positive : Bool) (φ : ArithmeticProposition) : List ℕ :=
  structuredLeafBlock positive (encodeArithmeticFormulaSymbols φ)

/-- The unary length field reads back the replicate count, leaving the payload. -/
lemma readStructuredLength_replicate (n : ℕ) (tail : List ℕ) :
    readStructuredLength (List.replicate n 1 ++ 0 :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append,
      readStructuredLength, ih, Option.map_some]

/-- The framed payload contracts to the tag-`5` atom of whatever formula the payload
parses to as a complete run. -/
private lemma parseStructuredPaperPrime_leaf {positive : Bool} {payload : List ℕ}
    {φ : ArithmeticProposition}
    (hpayload : parseStructuredArithmeticFormula payload.length 0 payload =
      some (Encodable.encode φ, []))
    (tail : List ℕ) :
    parseStructuredPaperPrime
      (Encodable.encode positive ::
        (List.replicate payload.length 1 ++ (0 :: (payload ++ 19 :: tail)))) =
      some (paperPrimeSentence positive φ, tail) := by
  rw [parseStructuredPaperPrime.eq_def]
  simp only [List.cons_append]
  have hbool : Encodable.encode positive ≤ 1 := by cases positive <;> simp
  rw [if_pos hbool]
  rw [readStructuredLength_replicate]
  simp only [Option.bind_some, List.length_append]
  rw [if_pos (by omega), List.take_left]
  rw [hpayload]
  simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
    if_pos rfl]
  rw [List.drop_append]
  simp
  simp [paperPrimeSentence, paperPrimeCode, paperPrimeTag]

/-- **Leaf contraction, payload-generic**: a leaf block whose payload is a complete
arithmetic-formula run contracts to that formula's tag-`5` atom, leaving the suffix. -/
lemma parseRpn_structuredLeafBlock {positive : Bool} {payload : List ℕ}
    {φ : ArithmeticProposition}
    (hpayload : parseStructuredArithmeticFormula payload.length 0 payload =
      some (Encodable.encode φ, []))
    (tail : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpn fuel (structuredLeafBlock positive payload ++ tail) =
      some (paperPrimeSentence positive φ, tail) := by
  match fuel, hfuel with
  | fuel + 1, _ =>
      rw [structuredLeafBlock]
      simp only [List.append_assoc, List.cons_append]
      rw [parseRpn.eq_def]
      norm_num
      exact parseStructuredPaperPrime_leaf hpayload tail

lemma structuredPaperPrimeBlock_length_pos (positive : Bool) (φ : ArithmeticProposition) :
    0 < (structuredPaperPrimeBlock positive φ).length :=
  structuredLeafBlock_length_pos positive _

/-- **Normal-form leaf contraction**: the emitted block parses to the exact public tag-`5`
atom of the encoded proposition. -/
lemma parseRpn_structuredPaperPrimeBlock (positive : Bool) (φ : ArithmeticProposition)
    (tail : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpn fuel (structuredPaperPrimeBlock positive φ ++ tail) =
      some (paperPrimeSentence positive φ, tail) :=
  parseRpn_structuredLeafBlock
    (by simpa using parseStructuredArithmeticFormula_encode (depth := 0) φ [] le_rfl)
    tail hfuel

/-! ## The normal-form-metered family class

`PolyArithmeticFormulaSeq φ` asks that the *symbol list*
`encodeArithmeticFormulaSymbols (φ n)` be a `PolySegStream`: polynomially many tokens, each
of polynomially bounded value.  The serializer emits one token per node of the Foundation
formula, so the metered quantity is that formula's own symbol count.  Gödel codes are never
emitted, and no numeral is rewritten into a larger object than the author wrote; the leaf
lifting below adds only fixed tokens and a unary copy of the already poly-fueled payload
length, so the tag-`5` value is constructed by `parseRpn` and never occurs in the
emitter's output range.

This class is the strictness foil, not the paper's condition.  The paper's class is
`PolyArithmeticSourceSeq` (`Construction/LUV/ArithmeticSource.lean`), which meters the source
as the paper writes it; this one is strictly finer, on `⟺` alone, because Foundation's normal form
duplicates both sides of a biconditional (`dd:nnf`).  The embedding is
`PolyArithmeticFormulaSeq.toSource` and the strictness is witnessed there. -/

/-- **The normal-form-metered class** — the strictness foil, not the paper's condition:
it meters one token per node of the *Foundation* formula, which charges `⟺` twice per side
(`dd:nnf`).  The paper's class is `PolyArithmeticSourceSeq`
(`Construction/LUV/ArithmeticSource.lean`), into which this one embeds by
`PolyArithmeticFormulaSeq.toSource`.

*Proof kind:* `Def`. -/
def PolyArithmeticFormulaSeq {k : ℕ} (φ : ℕ → ArithmeticSemiformula ℕ k) : Prop :=
  PolySegStream (fun n => encodeArithmeticFormulaSymbols (φ n))

/-- **Leaf emission, payload-generic**: framing a poly-metered payload stream costs
constant framing plus a unary length run, so the framed blocks are again poly-metered. -/
lemma structuredLeafBlock_polySegStream (positive : Bool) {payload : ℕ → List ℕ}
    (h : PolySegStream payload) :
    PolySegStream (fun n => structuredLeafBlock positive (payload n)) := by
  obtain ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩ := h
  have hpayload : PolySegStream payload :=
    ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩
  have hlength : PolyFueled cl (fun n => (payload n).length) :=
    hl.of_eq fun n => (hlen n).symm
  have hprefix : PolySegStream (fun _ => [1, 0, Encodable.encode positive]) :=
    PolySegStream.ofTokenStream <| (PolyTokenStream.const 1).append <|
      (PolyTokenStream.const 0).append (PolyTokenStream.const (Encodable.encode positive))
  have hframe := (PolySegStream.repeatTag 1 hlength).append
    (PolySegStream.ofTokenStream (PolyTokenStream.const 0))
  have hend : PolySegStream (fun _ => [19]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 19)
  exact (hprefix.append (hframe.append (hpayload.append hend))).of_eq fun n => by
    simp [structuredLeafBlock, List.append_assoc]

/-- The leaf blocks of a normal-form-metered family are efficiently emittable. -/
lemma structuredPaperPrimeBlock_polySegStream (positive : Bool)
    (φ : ℕ → ArithmeticProposition) (hφ : PolyArithmeticFormulaSeq φ) :
    PolySegStream (fun n => structuredPaperPrimeBlock positive (φ n)) :=
  structuredLeafBlock_polySegStream positive hφ

/-- **The emission lifting**: a family of arithmetic propositions certified in the
normal-form-metered class has an efficient stream of exact tag-`5` leaf blocks; the
tag-`5` atom code is built by parser contraction and never emitted. -/
lemma structuredPaperPrime_rpnSentenceCodes (positive : Bool)
    (φ : ℕ → ArithmeticProposition) (hφ : PolyArithmeticFormulaSeq φ) :
    RpnSentenceCodes (fun n => paperPrimeSentence positive (φ n)) := by
  refine ⟨fun n => structuredPaperPrimeBlock positive (φ n),
    structuredPaperPrimeBlock_polySegStream positive φ hφ, fun n => ?_⟩
  simpa using parseRpn_structuredPaperPrimeBlock positive (φ n) []
    (structuredPaperPrimeBlock_length_pos positive (φ n))

/-! ## The emitted alphabet

Every token the structural codec emits is a fixed small constant: payload symbols lie
in the arithmetic alphabet `0..18`, framing uses `0`/`1` and the polarity bit, and the
reserved terminator `19` appears exactly once, at the block's end.  A scanner therefore
locates the block boundary by the first `19`. -/

/-- Every binary natural-code token is a tag below `3`. -/
lemma encodeStructuredNat_lt (n : ℕ) : ∀ x ∈ encodeStructuredNat n, x < 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      cases n with
      | zero =>
          intro x hx
          simp only [encodeStructuredNat, List.mem_singleton] at hx
          omega
      | succ n =>
          intro x hx
          rw [encodeStructuredNat] at hx
          have hdiv : (n + 1) / 2 < n + 1 :=
            Nat.div_lt_self (Nat.succ_pos n) (by norm_num)
          split at hx <;>
            rcases List.mem_cons.mp hx with rfl | hx' <;>
            first
              | omega
              | exact ih _ hdiv x hx'

/-- Every emitted term token lies in the term alphabet `0..8`. -/
lemma encodeArithmeticTermSymbols_lt {k : ℕ} (t : ArithmeticSemiterm ℕ k) :
    ∀ x ∈ encodeArithmeticTermSymbols t, x < 9 := by
  induction t with
  | bvar i =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · have := encodeStructuredNat_lt _ x hx'
        omega
  | fvar i =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · have := encodeStructuredNat_lt _ x hx'
        omega
  | func f v ih =>
      rcases f with _ | _ | _ | _ <;> intro x hx
      · simp only [encodeArithmeticTermSymbols, List.mem_singleton] at hx
        omega
      · simp only [encodeArithmeticTermSymbols, List.mem_singleton] at hx
        omega
      · rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with h | h
          · exact ih 0 x h
          · exact ih 1 x h
      · rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · rcases List.mem_append.mp hx' with h | h
          · exact ih 0 x h
          · exact ih 1 x h

/-- Every payload token lies in the arithmetic alphabet `0..18` — the fact the metering
classification cites for why `PolySegStream`'s per-token value clause is vacuous along
this route. -/
lemma encodeArithmeticFormulaSymbols_lt {k : ℕ} (φ : ArithmeticSemiformula ℕ k) :
    ∀ x ∈ encodeArithmeticFormulaSymbols φ, x < 19 := by
  induction φ with
  | verum =>
      intro x hx
      simp only [encodeArithmeticFormulaSymbols, List.mem_singleton] at hx
      omega
  | falsum =>
      intro x hx
      simp only [encodeArithmeticFormulaSymbols, List.mem_singleton] at hx
      omega
  | rel r v =>
      rcases r with _ | _ <;> intro x hx <;>
        rcases List.mem_cons.mp hx with rfl | hx' <;>
        first
          | omega
          | (rcases List.mem_append.mp hx' with h | h
             · exact lt_trans (encodeArithmeticTermSymbols_lt (v 0) x h)
                 (by norm_num)
             · exact lt_trans (encodeArithmeticTermSymbols_lt (v 1) x h)
                 (by norm_num))
  | nrel r v =>
      rcases r with _ | _ <;> intro x hx <;>
        rcases List.mem_cons.mp hx with rfl | hx' <;>
        first
          | omega
          | (rcases List.mem_append.mp hx' with h | h
             · exact lt_trans (encodeArithmeticTermSymbols_lt (v 0) x h)
                 (by norm_num)
             · exact lt_trans (encodeArithmeticTermSymbols_lt (v 1) x h)
                 (by norm_num))
  | and φ ψ ihφ ihψ =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · rcases List.mem_append.mp hx' with h | h
        · exact ihφ x h
        · exact ihψ x h
  | or φ ψ ihφ ihψ =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · rcases List.mem_append.mp hx' with h | h
        · exact ihφ x h
        · exact ihψ x h
  | all φ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · exact ih x hx'
  | exs φ ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · exact ih x hx'

/-! ### Arity coercion

`Rew.castLE` is *index preserving* (`Rew.castLe_bvar`: `castLE h #x = #(Fin.castLE h x)`,
same `.val`), so raising a formula's arity leaves its emitted symbol run literally
unchanged.  That is what lets a family's `def:ec` certificate transport across the arity
coercions the exact product uses (`Construction/Quotation/ExactProduct.lean`). -/

/-- Raising a term's arity does not change its symbol run. -/
@[simp] lemma encodeArithmeticTermSymbols_castLE {k k' : ℕ} (h : k ≤ k')
    (t : ArithmeticSemiterm ℕ k) :
    encodeArithmeticTermSymbols (Rew.castLE h t) = encodeArithmeticTermSymbols t := by
  induction t with
  | bvar x => simp [encodeArithmeticTermSymbols]
  | fvar x => simp [encodeArithmeticTermSymbols]
  | func f v ih =>
      cases f <;> simp [Rew.func, encodeArithmeticTermSymbols, ih]

/-- Raising a formula's arity does not change its symbol run. -/
@[simp] lemma encodeArithmeticFormulaSymbols_castLE {k : ℕ}
    (φ : ArithmeticSemiformula ℕ k) :
    ∀ {k' : ℕ} (h : k ≤ k'),
      encodeArithmeticFormulaSymbols (Rew.castLE h ▹ φ) =
        encodeArithmeticFormulaSymbols φ := by
  induction φ using Semiformula.rec' with
  | hverum => intro k' h; simp [encodeArithmeticFormulaSymbols]
  | hfalsum => intro k' h; simp [encodeArithmeticFormulaSymbols]
  | hrel r v => intro k' h; cases r <;> simp [encodeArithmeticFormulaSymbols]
  | hnrel r v => intro k' h; cases r <;> simp [encodeArithmeticFormulaSymbols]
  | hand φ ψ ihp ihq =>
      intro k' h
      simp only [LogicalConnective.HomClass.map_and, encodeArithmeticFormulaSymbols,
        ihp h, ihq h]
  | hor φ ψ ihp ihq =>
      intro k' h
      simp only [LogicalConnective.HomClass.map_or, encodeArithmeticFormulaSymbols,
        ihp h, ihq h]
  | hall φ ih =>
      intro k' h
      rw [Rewriting.app_all, Rew.q_castLE]
      simp only [encodeArithmeticFormulaSymbols, ih]
  | hexs φ ih =>
      intro k' h
      rw [Rewriting.app_exs, Rew.q_castLE]
      simp only [encodeArithmeticFormulaSymbols, ih]

/-- **The leaf block is a `19`-free span**: behind the `[1, 0]` dispatch prefix a block
over a `19`-free payload contains no `19` until the single closing terminator, so a
scanner locates the boundary by the first `19`. -/
lemma structuredLeafBlock_span (positive : Bool) {payload : List ℕ}
    (hpayload : ∀ x ∈ payload, x ≠ 19) :
    ∃ w, structuredLeafBlock positive payload = 1 :: 0 :: (w ++ [19]) ∧
      ∀ x ∈ w, x ≠ 19 := by
  refine ⟨Encodable.encode positive ::
    (List.replicate payload.length 1 ++ 0 :: payload), by
        simp [structuredLeafBlock], ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · cases positive <;> simp
  · rcases List.mem_append.mp hx' with h | h
    · have := List.eq_of_mem_replicate h
      omega
    · rcases List.mem_cons.mp h with rfl | h'
      · omega
      · exact hpayload x h'

/-- **The normal-form block is a `19`-free span**, the instance of
`structuredLeafBlock_span` the metering classification cites. -/
lemma structuredPaperPrimeBlock_span (positive : Bool) (φ : ArithmeticProposition) :
    ∃ w, structuredPaperPrimeBlock positive φ = 1 :: 0 :: (w ++ [19]) ∧
      ∀ x ∈ w, x ≠ 19 :=
  structuredLeafBlock_span positive fun x hx => by
    have := encodeArithmeticFormulaSymbols_lt φ x hx; omega

open Nat.Partrec (Code)

/-- Every fixed token list is a segment stream. -/
lemma PolySegStream.constList : ∀ c : List ℕ, PolySegStream (fun _ : ℕ => c)
  | [] => PolySegStream.ofTokenStream PolyTokenStream.nil
  | t :: c =>
      ((PolySegStream.ofTokenStream (PolyTokenStream.const t)).append
        (PolySegStream.constList c)).of_eq fun _ => rfl

/-! ## Foundation's unary numeral

Foundation builds numerals by a left-nested fold of `one` under `add`, so a numeral's
symbol encoding is two constant-tag runs — exactly the shape the repeat-tag emitter
produces.  This is the term-level half of the threshold syntax. -/

/-- Foundation's numeral for `v ≠ 0` costs `2v - 1` symbols: `v - 1` `add` tags followed
by `v` `one` tags. -/
lemma encodeArithmeticTermSymbols_numeral {k : ℕ} :
    ∀ v : ℕ, v ≠ 0 →
      encodeArithmeticTermSymbols
        ((Semiterm.Operator.numeral ℒₒᵣ v).const : ArithmeticSemiterm ℕ k) =
        List.replicate (v - 1) 7 ++ List.replicate v 6
  | 1, _ => by rfl
  | (v + 2), _ => by
      have hv : v + 1 ≠ 0 := by omega
      have hrec := encodeArithmeticTermSymbols_numeral (k := k) (v + 1) hv
      rw [Semiterm.Operator.numeral_succ hv]
      show (7 : ℕ) :: (encodeArithmeticTermSymbols
        ((Semiterm.Operator.numeral ℒₒᵣ (v + 1)).const : ArithmeticSemiterm ℕ k) ++
          encodeArithmeticTermSymbols
            ((Semiterm.Operator.One.one).const : ArithmeticSemiterm ℕ k)) = _
      rw [hrec]
      show (7 : ℕ) :: (List.replicate v 7 ++ List.replicate (v + 1) 6 ++ [6]) = _
      simp [List.replicate_succ]
      rw [← List.replicate_succ', List.replicate_succ]

/-! ## Compact numerals in base four

Foundation's `Semiterm.Operator.numeral` is unary, so naming a large value with it costs
symbols linear in the value.  That is the cost model of the paper's own `ℒₒᵣ`, and the
paper does not pay it: it names large values by *compact terms* or by definitions
(tex:614, "writing `⌜f(3)⌝` does not involve computing `f(3)`").  `binNumeral` is the
compact naming a paper author has in `ℒₒᵣ` itself — Horner form over `0`/`1`/`+`/`*`,
`O(log v)` nodes for the value `v` — with the same value in every model of `𝗣𝗔⁻`.

The recursion is **base four**, not base two, and that choice is load-bearing rather than
cosmetic.  A base-two Horner step has to branch on the parity, so its symbol list has two
different widths (`[8,7,6,6]` against `[7,8,7,6,6] … [6]`); a variable-width run is not
something `PolySegStream.blocks` can emit, and the whole point of a compact numeral in
this development is that a *write-out* value stream can name its own values.  In base
four the digit is carried by a fixed `(1+1) * b₁ + b₀` shape, so the symbol list is two
uniform runs — `binNumeralLen v - 1` copies of the nine-token `hornerPrefix` followed by
`binNumeralLen v` copies of the seven-token `digitEnc` — and both runs are driven by
`len4` and `dig4`, which are exactly the two primitives `BigDigits` certifies.  No base
conversion is performed anywhere: `binNumeralEnc_eq` reads the numeral straight off the
base-4 digits. -/

/-- The `ℒₒᵣ` term naming a single bit. -/
def bitTerm (b : ℕ) : Semiterm.Const ℒₒᵣ :=
  if b = 0 then Semiterm.Operator.Zero.zero else Semiterm.Operator.One.one

/-- The `ℒₒᵣ` term naming a base-4 digit, in the fixed shape `(1+1) * (d / 2) + d % 2`.
The shape is uniform in `d`, which is what makes the numeral's symbol list a
constant-width block. -/
def digitTerm (d : ℕ) : Semiterm.Const ℒₒᵣ :=
  Semiterm.Operator.Add.add.comp
    ![Semiterm.Operator.Mul.mul.comp
        ![Semiterm.Operator.Add.add.comp
            ![Semiterm.Operator.One.one, Semiterm.Operator.One.one],
          bitTerm (d / 2)],
      bitTerm (d % 2)]

/-- The Horner base as an `ℒₒᵣ` term: `(1+1) * (1+1)`. -/
def fourTerm : Semiterm.Const ℒₒᵣ :=
  Semiterm.Operator.Mul.mul.comp
    ![Semiterm.Operator.Add.add.comp
        ![Semiterm.Operator.One.one, Semiterm.Operator.One.one],
      Semiterm.Operator.Add.add.comp
        ![Semiterm.Operator.One.one, Semiterm.Operator.One.one]]

/-- Horner-form ("base-four") numeral: the value `v` named by `O(log v)` `ℒₒᵣ` nodes,
`v ↦ ((1+1)*(1+1)) * ⌜v / 4⌝ + ⌜v % 4⌝` down to a single digit. -/
def binNumeral (v : ℕ) : Semiterm.Const ℒₒᵣ :=
  if v < 4 then digitTerm v
  else
    Semiterm.Operator.Add.add.comp
      ![Semiterm.Operator.Mul.mul.comp ![fourTerm, binNumeral (v / 4)],
        digitTerm (v % 4)]
termination_by v
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The number of base-4 digits the compact numeral writes: `len4 v`, except that the
value `0` still occupies one digit. -/
def binNumeralLen (v : ℕ) : ℕ := max (len4 v) 1

/-- The compact numeral always writes at least one digit. -/
lemma binNumeralLen_pos (v : ℕ) : 0 < binNumeralLen v :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)

/-- A value below the base is a single digit. -/
lemma binNumeralLen_of_lt_four {v : ℕ} (h : v < 4) : binNumeralLen v = 1 := by
  have : len4 v ≤ 1 := (len4_le_iff v 1).mpr (by simpa using h)
  simp only [binNumeralLen]
  omega

/-- Each Horner step consumes one base-4 digit. -/
lemma binNumeralLen_div {v : ℕ} (h : 4 ≤ v) :
    binNumeralLen v = binNumeralLen (v / 4) + 1 := by
  have hq : 0 < v / 4 := Nat.div_pos h (by norm_num)
  have h1 : 0 < len4 (v / 4) := len4_pos hq
  have h2 : len4 v = len4 (v / 4) + 1 := len4_div_four (by omega)
  simp only [binNumeralLen]
  omega

/-- The symbol block of one base-4 digit (width 7). -/
def digitEnc (d : ℕ) : List ℕ := [7, 8, 7, 6, 6, d / 2 + 5, d % 2 + 5]

/-- The symbol block of one Horner step (width 9). -/
def hornerPrefix : List ℕ := [7, 8, 8, 7, 6, 6, 7, 6, 6]

/-- The symbol list of `binNumeral`, read off the same recursion. -/
def binNumeralEnc (v : ℕ) : List ℕ :=
  if v < 4 then digitEnc v
  else hornerPrefix ++ binNumeralEnc (v / 4) ++ digitEnc (v % 4)
termination_by v
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- A bit term emits the single tag `b + 5`. -/
lemma encodeArithmeticTermSymbols_bitTerm {k : ℕ} {b : ℕ} (hb : b < 2) :
    encodeArithmeticTermSymbols ((bitTerm b).const : ArithmeticSemiterm ℕ k)
      = [b + 5] := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl

/-- A base-4 digit term emits the fixed seven-token block `digitEnc d`. -/
lemma encodeArithmeticTermSymbols_digitTerm {k : ℕ} {d : ℕ} (hd : d < 4) :
    encodeArithmeticTermSymbols ((digitTerm d).const : ArithmeticSemiterm ℕ k)
      = digitEnc d := by
  show (7 : ℕ) :: (encodeArithmeticTermSymbols
      ((Semiterm.Operator.Mul.mul.comp
        ![Semiterm.Operator.Add.add.comp
            ![Semiterm.Operator.One.one, Semiterm.Operator.One.one],
          bitTerm (d / 2)] : Semiterm.Const ℒₒᵣ).const : ArithmeticSemiterm ℕ k) ++
      encodeArithmeticTermSymbols ((bitTerm (d % 2)).const : ArithmeticSemiterm ℕ k)) = _
  show (7 : ℕ) :: ((8 : ℕ) :: (encodeArithmeticTermSymbols
      ((Semiterm.Operator.Add.add.comp
        ![Semiterm.Operator.One.one, Semiterm.Operator.One.one] :
          Semiterm.Const ℒₒᵣ).const : ArithmeticSemiterm ℕ k) ++
      encodeArithmeticTermSymbols ((bitTerm (d / 2)).const : ArithmeticSemiterm ℕ k)) ++
      encodeArithmeticTermSymbols ((bitTerm (d % 2)).const : ArithmeticSemiterm ℕ k)) = _
  rw [encodeArithmeticTermSymbols_bitTerm (show d / 2 < 2 by omega),
    encodeArithmeticTermSymbols_bitTerm (show d % 2 < 2 by omega)]
  rfl

/-- The compact numeral's symbol run is exactly `binNumeralEnc`. -/
lemma encodeArithmeticTermSymbols_binNumeral {k : ℕ} :
    ∀ v : ℕ, encodeArithmeticTermSymbols
      ((binNumeral v).const : ArithmeticSemiterm ℕ k) = binNumeralEnc v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases lt_or_ge v 4 with hv | hv
    · rw [binNumeral, if_pos hv, binNumeralEnc, if_pos hv]
      exact encodeArithmeticTermSymbols_digitTerm hv
    · have hlt : v / 4 < v := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih _ hlt
      rw [binNumeral, if_neg (by omega), binNumeralEnc, if_neg (by omega)]
      show (7 : ℕ) :: (encodeArithmeticTermSymbols
          ((Semiterm.Operator.Mul.mul.comp
            ![fourTerm, binNumeral (v / 4)] : Semiterm.Const ℒₒᵣ).const :
              ArithmeticSemiterm ℕ k) ++
          encodeArithmeticTermSymbols
            ((digitTerm (v % 4)).const : ArithmeticSemiterm ℕ k)) = _
      show (7 : ℕ) :: ((8 : ℕ) :: (encodeArithmeticTermSymbols
          ((fourTerm : Semiterm.Const ℒₒᵣ).const : ArithmeticSemiterm ℕ k) ++
          encodeArithmeticTermSymbols
            ((binNumeral (v / 4)).const : ArithmeticSemiterm ℕ k)) ++
          encodeArithmeticTermSymbols
            ((digitTerm (v % 4)).const : ArithmeticSemiterm ℕ k)) = _
      rw [hrec, encodeArithmeticTermSymbols_digitTerm (Nat.mod_lt _ (by norm_num))]
      rfl

private lemma flatMap_range_const (c : List ℕ) :
    ∀ n : ℕ, (List.range n).flatMap (fun _ : ℕ => c) = (List.replicate n c).flatten := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ',
        List.flatten_append]
      simp

/-- **The compact numeral in closed digit form.**  The symbol list is two uniform runs:
`binNumeralLen v - 1` copies of the nine-token Horner block, then one seven-token digit
block per base-4 digit of `v`, most significant first.  This is the shape
`PolySegStream.blocks` emits, and every quantity in it (`len4`, `dig4`) is a primitive
`BigDigits` already certifies — which is what makes `polySegStream_binNumeralEnc` a
composition rather than a new machine. -/
lemma binNumeralEnc_eq (v : ℕ) :
    binNumeralEnc v =
      (List.range (binNumeralLen v - 1)).flatMap (fun _ => hornerPrefix) ++
      (List.range (binNumeralLen v)).flatMap
        (fun j => digitEnc (dig4 v (binNumeralLen v - 1 - j))) := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases lt_or_ge v 4 with hv | hv
    · rw [binNumeralEnc, if_pos hv, binNumeralLen_of_lt_four hv]
      simp [dig4_of_lt_four hv]
    · have hlt : v / 4 < v := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih _ hlt
      have hLv : binNumeralLen v = binNumeralLen (v / 4) + 1 := binNumeralLen_div hv
      obtain ⟨K, hK⟩ : ∃ K, binNumeralLen (v / 4) = K + 1 :=
        ⟨binNumeralLen (v / 4) - 1, by have := binNumeralLen_pos (v / 4); omega⟩
      rw [hK] at hrec hLv
      have e1 : (List.range (K + 1)).flatMap (fun _ : ℕ => hornerPrefix)
          = hornerPrefix ++ (List.range K).flatMap (fun _ : ℕ => hornerPrefix) := by
        rw [flatMap_range_const, flatMap_range_const, List.replicate_succ,
          List.flatten_cons]
      have e2 : (List.range (K + 1 + 1)).flatMap
            (fun j => digitEnc (dig4 v (K + 1 - j)))
          = (List.range (K + 1)).flatMap (fun j => digitEnc (dig4 (v / 4) (K - j)))
            ++ digitEnc (v % 4) := by
        rw [List.range_succ, List.flatMap_append]
        congr 1
        · refine List.flatMap_congr ?_
          intro j hj
          rw [List.mem_range] at hj
          have hj' : K + 1 - j = (K - j) + 1 := by omega
          rw [hj', dig4_succ]
        · simp [dig4_zero]
      rw [binNumeralEnc, if_neg (by omega), hrec, hLv]
      simp only [Nat.add_sub_cancel]
      rw [e1, e2]
      simp [List.append_assoc]

/-- **The exact symbol count**: `16 * binNumeralLen v - 9`, one nine-token Horner block
per digit *after* the first plus one seven-token digit block per digit.  This is the sharp
form of the `O(log v)` bound `binNumeralEnc_length_le` states. -/
lemma binNumeralEnc_length (v : ℕ) :
    (binNumeralEnc v).length = 16 * binNumeralLen v - 9 := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases lt_or_ge v 4 with hv | hv
    · rw [binNumeralEnc, if_pos hv, binNumeralLen_of_lt_four hv]
      rfl
    · have hlt : v / 4 < v := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih _ hlt
      have hLv : binNumeralLen v = binNumeralLen (v / 4) + 1 := binNumeralLen_div hv
      have hp := binNumeralLen_pos (v / 4)
      rw [binNumeralEnc, if_neg (by omega)]
      simp only [List.length_append, hrec, hLv, digitEnc, hornerPrefix,
        List.length_cons, List.length_nil]
      omega

/-- The digit count is at most half the binary logarithm, plus one: two bits of the value
per base-4 digit. -/
lemma binNumeralLen_le_log (v : ℕ) : binNumeralLen v ≤ Nat.log 2 v / 2 + 1 := by
  have hlen : len4 v ≤ Nat.log 2 v / 2 + 1 := by
    rw [len4_le_iff]
    have hpow : (4 : ℕ) ^ (Nat.log 2 v / 2 + 1) = 2 ^ (2 * (Nat.log 2 v / 2) + 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring_nf
    rw [hpow]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · positivity
    · refine lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) v)
        (Nat.pow_le_pow_right (by norm_num) ?_)
      omega
  simp only [binNumeralLen]
  omega

/-- **The compact numeral is logarithmic.**  Each base-4 Horner step contributes sixteen
symbols and consumes two bits of the value, so naming `v` costs `O(log v)` — against
`2 * v - 1` for the unary numeral (`encodeArithmeticTermSymbols_numeral`). -/
lemma binNumeralEnc_length_le (v : ℕ) :
    (binNumeralEnc v).length ≤ 8 * Nat.log 2 v + 7 := by
  have hlen := binNumeralEnc_length v
  have hL := binNumeralLen_le_log v
  omega

private lemma val_one {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] :
    (Semiterm.Operator.One.one : Semiterm.Const ℒₒᵣ).val (![] : Fin 0 → M) = 1 := by
  simp

private lemma val_add_comp {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (s t : Semiterm.Const ℒₒᵣ) :
    (Semiterm.Operator.Add.add.comp ![s, t] : Semiterm.Const ℒₒᵣ).val (![] : Fin 0 → M)
      = s.val (![] : Fin 0 → M) + t.val (![] : Fin 0 → M) := by
  simp [Semiterm.Operator.val_comp, Matrix.fun_eq_vec_two]

private lemma val_mul_comp {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (s t : Semiterm.Const ℒₒᵣ) :
    (Semiterm.Operator.Mul.mul.comp ![s, t] : Semiterm.Const ℒₒᵣ).val (![] : Fin 0 → M)
      = s.val (![] : Fin 0 → M) * t.val (![] : Fin 0 → M) := by
  simp [Semiterm.Operator.val_comp, Matrix.fun_eq_vec_two]

/-- **The compact numeral names its value.**  In every model of `𝗣𝗔⁻` the Horner term
`binNumeral v` evaluates to `v`, so it is interchangeable with Foundation's unary numeral
wherever only the value matters. -/
lemma binNumeral_val {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] :
    ∀ v : ℕ, (binNumeral v).val (![] : Fin 0 → M) = (v : M) := by
  have hbit : ∀ b : ℕ, b < 2 →
      (bitTerm b).val (![] : Fin 0 → M) = (b : M) := by
    intro b hb
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp [bitTerm]
  have hdig : ∀ d : ℕ, d < 4 →
      (digitTerm d).val (![] : Fin 0 → M) = (d : M) := by
    intro d hd
    have hcast : (d : M) = 2 * ((d / 2 : ℕ) : M) + ((d % 2 : ℕ) : M) := by
      have hdd : d = 2 * (d / 2) + d % 2 := by omega
      calc (d : M) = ((2 * (d / 2) + d % 2 : ℕ) : M) := by rw [← hdd]
        _ = 2 * ((d / 2 : ℕ) : M) + ((d % 2 : ℕ) : M) := by push_cast; ring
    rw [digitTerm]
    simp only [val_add_comp, val_mul_comp, val_one,
      hbit _ (show d / 2 < 2 by omega), hbit _ (show d % 2 < 2 by omega)]
    rw [hcast]; ring
  have hfour : (fourTerm : Semiterm.Const ℒₒᵣ).val (![] : Fin 0 → M) = 4 := by
    rw [fourTerm]
    simp only [val_add_comp, val_mul_comp, val_one]
    first | norm_num | ring
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases lt_or_ge v 4 with hv | hv
    · rw [binNumeral, if_pos hv]; exact hdig v hv
    · have hlt : v / 4 < v := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih _ hlt
      have hcast : (v : M) = 4 * ((v / 4 : ℕ) : M) + ((v % 4 : ℕ) : M) := by
        have hvv : v = 4 * (v / 4) + v % 4 := by omega
        calc (v : M) = ((4 * (v / 4) + v % 4 : ℕ) : M) := by rw [← hvv]
          _ = 4 * ((v / 4 : ℕ) : M) + ((v % 4 : ℕ) : M) := by push_cast; ring
      rw [binNumeral, if_neg (by omega)]
      simp only [val_add_comp, val_mul_comp, hfour, hrec,
        hdig _ (Nat.mod_lt _ (by norm_num))]
      rw [hcast]
      try ring

/-- **The compact numeral in the standard model.**  The `M = ℕ` instance of
`binNumeral_val`. -/
lemma binNumeral_val_nat (v : ℕ) : (binNumeral v).val (![] : Fin 0 → ℕ) = v := by
  simpa using binNumeral_val (M := ℕ) v

/-- **Distinct values get distinct names.**  Immediate from `binNumeral_val_nat`: the
standard-model value of `binNumeral v` recovers `v`.  This is the separation fact a client
needs to tell apart claim sentences that differ only by the value they name. -/
lemma binNumeral_injective : Function.Injective binNumeral := by
  intro a b hab
  have ha := binNumeral_val_nat a
  rw [hab, binNumeral_val_nat b] at ha
  exact ha.symm

/-! ## Emitting a compact numeral from write-out digits -/

/-- **The compact numeral is emittable from write-out digit access.**  If the values `v n`
are exponential but their base-4 length and digits are poly-fueled (`BigDigits`), the
compact numerals naming them are a polynomially metered token stream: two
constant-width runs, one counted by `len4` and one emitting `dig4` through a fixed
seven-token block.  Every emitted token is a tag in `5..8`, so the class is
`PolySegStream` and not `BigTokenStream`. -/
lemma polySegStream_binNumeralEnc {v : ℕ → ℕ} (hv : BigDigits v) :
    PolySegStream (fun n => binNumeralEnc (v n)) := by
  obtain ⟨cl, cd, hl, hd⟩ := hv
  obtain ⟨cdm, hdm⟩ := divmodc_polyFueled 2 (by norm_num)
  -- The digit count `binNumeralLen (v n) = if len4 (v n) = 0 then 1 else len4 (v n)`.
  have hL : PolyFueled _ (fun n => binNumeralLen (v n)) :=
    (ifzSel_polyFueled.comp (((PolyFueled.const 1).pair hl).pair hl)).of_eq (fun n => by
      simp only [Nat.unpair_pair, ifzSelFn, binNumeralLen]
      split <;> omega)
  have hL1 : PolyFueled _ (fun n => binNumeralLen (v n) - 1) :=
    (predc_polyFueled.comp hL).of_eq (fun n => Nat.pred_eq_sub_one)
  -- Run 1: the Horner prefixes.
  have hblk1 : PolyTokenStream (fun _ : ℕ => hornerPrefix) :=
    (PolyTokenStream.const 7).append <| (PolyTokenStream.const 8).append <|
      (PolyTokenStream.const 8).append <| (PolyTokenStream.const 7).append <|
      (PolyTokenStream.const 6).append <| (PolyTokenStream.const 6).append <|
      (PolyTokenStream.const 7).append <| (PolyTokenStream.const 6).append
        (PolyTokenStream.const 6)
  have hrun1 := PolySegStream.blocks hblk1 9 (fun _ => rfl) (by omega) hL1
  -- Run 2: the digit blocks, most significant first.
  have hLm : PolyFueled _ (fun m : ℕ => binNumeralLen (v m.unpair.1)) :=
    hL.comp PolyFueled.left
  have hidx : PolyFueled _
      (fun m : ℕ => binNumeralLen (v m.unpair.1) - 1 - m.unpair.2) :=
    (subc_polyFueled.comp ((predc_polyFueled.comp hLm).pair PolyFueled.right)).of_eq
      (fun m => by simp only [Nat.unpair_pair, Nat.pred_eq_sub_one])
  have hdg : PolyFueled _ (fun m : ℕ =>
      dig4 (v m.unpair.1) (binNumeralLen (v m.unpair.1) - 1 - m.unpair.2)) :=
    (hd.comp (PolyFueled.left.pair hidx)).of_eq (fun m => by simp only [Nat.unpair_pair])
  have hq : PolyFueled _ (fun m : ℕ =>
      dig4 (v m.unpair.1) (binNumeralLen (v m.unpair.1) - 1 - m.unpair.2) / 2) :=
    (PolyFueled.left.comp (hdm.comp hdg)).of_eq (fun m => by simp only [Nat.unpair_pair])
  have hr : PolyFueled _ (fun m : ℕ =>
      dig4 (v m.unpair.1) (binNumeralLen (v m.unpair.1) - 1 - m.unpair.2) % 2) :=
    (PolyFueled.right.comp (hdm.comp hdg)).of_eq (fun m => by simp only [Nat.unpair_pair])
  obtain ⟨_, hq5⟩ := hq.addConst 5
  obtain ⟨_, hr5⟩ := hr.addConst 5
  have hblk2 : PolyTokenStream (fun m : ℕ =>
      digitEnc (dig4 (v m.unpair.1) (binNumeralLen (v m.unpair.1) - 1 - m.unpair.2))) :=
    (PolyTokenStream.const 7).append <| (PolyTokenStream.const 8).append <|
      (PolyTokenStream.const 7).append <| (PolyTokenStream.const 6).append <|
      (PolyTokenStream.const 6).append <|
      (PolyTokenStream.polyTok hq5).append (PolyTokenStream.polyTok hr5)
  have hrun2 := PolySegStream.blocks hblk2 7 (fun _ => rfl) (by omega) hL
  refine (hrun1.append hrun2).of_eq fun n => ?_
  simp only [Nat.unpair_pair]
  rw [binNumeralEnc_eq]

/-- **The compact numeral of a write-out family is emittable as `ℒₒᵣ` term symbols.**  The
form the arithmetic source frontend consumes: the RPN symbol stream of the compact
numeral naming `v n` is polynomially metered whenever `v` is written out. -/
lemma polySegStream_binNumeral_const {v : ℕ → ℕ} (hv : BigDigits v) (l : ℕ) :
    PolySegStream (fun n => encodeArithmeticTermSymbols
      ((binNumeral (v n)).const : ArithmeticSemiterm ℕ l)) :=
  (polySegStream_binNumeralEnc hv).of_eq fun n =>
    (encodeArithmeticTermSymbols_binNumeral (k := l) (v n)).symm

/-- **The doubling family is structurally emittable.**  The compact numerals of `2 ^ n`
are emitted by the digit route: `2 ^ n` is written out (`bigDigits_two_pow`) even though
its value is superpolynomial, and a written-out family names its values compactly. -/
lemma binNumeralEnc_two_pow_polySegStream :
    PolySegStream (fun n => binNumeralEnc (2 ^ n)) :=
  polySegStream_binNumeralEnc bigDigits_two_pow

end LogicalInduction
