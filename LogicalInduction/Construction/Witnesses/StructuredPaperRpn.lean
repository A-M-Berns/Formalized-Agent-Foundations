import LogicalInduction.Construction.Witnesses.PaperLUV
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnSplice
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Framework.WriteOut

/-!
# Structured Foundation-arithmetic RPN codec and the literal paper LUV frontend

The public leaf framing is

  `[1, 0, polarity] ++ replicate payload.length 1 ++ [0] ++ payload ++ [19]`.

The formerly invalid sentence code `0` makes the prefix backwards compatible, so the
extended grammar parses every legacy stream unchanged (`parseRpn_of_legacy`).  The unary
payload length keeps every framing token bounded, the payload is a prefix tree over the
arithmetic alphabet `0..18`, and the reserved terminator `19` — which the alphabet never
contains — closes the block, so the syntax-preserving scanners of the strategy grammar
recognize the whole leaf as one atom without replaying the Foundation decoder.  Godel
codes are built by parser contraction and never emitted as tokens.

Contents:

* the encoders `encodeArithmeticTermSymbols` / `encodeArithmeticFormulaSymbols` over the
  complete Foundation arithmetic syntax, with exact suffix-preserving round trips;
* the leaf and decomposition blocks `structuredPaperPrimeBlock` /
  `structuredPaperDecomposeBlock`, contracting to the exact public tag-7 syntax
  `paperPrimeSentence` / `paperPrimeDecompose`;
* the normal-form-metered family interface `PolyArithmeticFormulaSeq` and the emission
  liftings, with the emitted-token audit pinning every token to a fixed small constant;
* the compact numerals `binNumeral`, which name a value in `O(log v)` `ℒₒᵣ` nodes.

`PolyArithmeticFormulaSeq` is **not** the class the development certifies families in:
because Foundation's `Semiformula` is negation-normal-form, it charges a `⟺` twice per
side, which the paper does not.  The paper's own condition is metered on the source
language of `ArithmeticSource.lean` (`PolyArithmeticSourceSeq`), where this class embeds
by `PolyArithmeticFormulaSeq.toSource`; the literal LUV frontend `PaperLUVSeq` and the
strictness separation between the two classes live there.

## Compatibility with the shared grammar

The leaf is an extension of infrastructure several passes share, so the compatibility
obligations are discharged where they live:

* every stream the pre-structured grammar accepted keeps its parse and its suffix
  (`parseRpn_of_legacy`), and the ordinary two-token escape `[1, code]` is unchanged for
  every `code ≠ 0`;
* conditioning consumes a structured leaf as **one** atom: the run automaton gains the
  structured payload modes, the pending-subtree counter decrements exactly once at the
  terminator, and the buffered run keeps the whole block (`RpnConditioning.lean`);
* the freeze pass decides targets at the list level with the full parser, so structured
  leaves are matched like any other block; its *positional* matcher stays scoped to the
  legacy fragment for a `dd:fuel` reason that predates this codec (`RpnFreeze.lean`);
* splice and quotation treat sentence blocks abstractly and needed no change.
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
                rw [ih _ hdiv tail (fuel := fuel) (by simpa [encodeStructuredNat, hpar] using hfuel)]
                have heven : 2 * ((n + 1) / 2) = n + 1 := by omega
                simp [heven]
          · cases fuel with
            | zero => simp [encodeStructuredNat, hpar] at hfuel
            | succ fuel =>
                simp only [List.cons_append, parseStructuredNat]
                rw [ih _ hdiv tail (fuel := fuel) (by simpa [encodeStructuredNat, hpar] using hfuel)]
                have hodd : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
                simp [hodd]

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

/-- Decode one arithmetic term from a symbol stream. -/
def parseArithmeticTermSymbols (k : ℕ) (symbols : List ℕ) :
    Option (ArithmeticSemiterm ℕ k × List ℕ) :=
  (parseStructuredArithmeticTerm symbols.length k symbols).bind fun p =>
    (Encodable.decode (α := ArithmeticSemiterm ℕ k) p.1).map fun t => (t, p.2)

/-- Decode one arithmetic formula from a symbol stream. -/
def parseArithmeticFormulaSymbols (k : ℕ) (symbols : List ℕ) :
    Option (ArithmeticSemiformula ℕ k × List ℕ) :=
  (parseStructuredArithmeticFormula symbols.length k symbols).bind fun p =>
    (Encodable.decode (α := ArithmeticSemiformula ℕ k) p.1).map fun φ => (φ, p.2)

lemma parseArithmeticTermSymbols_encode {k : ℕ} (t : ArithmeticSemiterm ℕ k)
    (tail : List ℕ) :
    parseArithmeticTermSymbols k (encodeArithmeticTermSymbols t ++ tail) = some (t, tail) := by
  rw [parseArithmeticTermSymbols, parseStructuredArithmeticTerm_encode t tail (by simp)]
  simp [Encodable.encodek]

lemma parseArithmeticFormulaSymbols_encode {k : ℕ} (φ : ArithmeticSemiformula ℕ k)
    (tail : List ℕ) :
    parseArithmeticFormulaSymbols k (encodeArithmeticFormulaSymbols φ ++ tail) = some (φ, tail) := by
  rw [parseArithmeticFormulaSymbols, parseStructuredArithmeticFormula_encode φ tail (by simp)]
  simp [Encodable.encodek]

/-! ## The structured paper-prime leaf

One arithmetic proposition as a single atomic RPN block: the `[1, 0]` dispatch prefix, the
polarity bit, a unary payload length, the payload, and the reserved terminator. -/

/-- The atomic block whose contraction is `paperPrimeSentence positive φ`. -/
def structuredPaperPrimeBlock (positive : Bool) (φ : ArithmeticProposition) : List ℕ :=
  let payload := encodeArithmeticFormulaSymbols φ
  [1, 0, Encodable.encode positive] ++
    (List.replicate payload.length 1 ++ (0 :: payload ++ [19]))

/-- The unary length field reads back the replicate count, leaving the payload. -/
lemma readStructuredLength_replicate (n : ℕ) (tail : List ℕ) :
    readStructuredLength (List.replicate n 1 ++ 0 :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append,
      readStructuredLength, ih, Option.map_some]

private lemma parseStructuredPaperPrime_encode (positive : Bool) (φ : ArithmeticProposition)
    (tail : List ℕ) :
    parseStructuredPaperPrime
      (Encodable.encode positive ::
        (List.replicate (encodeArithmeticFormulaSymbols φ).length 1 ++
        (0 :: (encodeArithmeticFormulaSymbols φ ++ 19 :: tail)))) =
      some (paperPrimeSentence positive φ, tail) := by
  rw [parseStructuredPaperPrime.eq_def]
  simp only [List.cons_append]
  have hbool : Encodable.encode positive ≤ 1 := by cases positive <;> simp
  rw [if_pos hbool]
  rw [readStructuredLength_replicate]
  simp only [Option.bind_some, List.length_append]
  rw [if_pos (by omega), List.take_left]
  have hparse := parseStructuredArithmeticFormula_encode (depth := 0) φ [] le_rfl
  simp only [List.append_nil] at hparse
  rw [hparse]
  simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
    if_pos rfl]
  rw [List.drop_append]
  simp
  simp [paperPrimeSentence, paperPrimeCode, paperPrimeTag]

private lemma structuredPaperPrimeBlock_length_pos (positive : Bool) (φ : ArithmeticProposition) :
    0 < (structuredPaperPrimeBlock positive φ).length := by
  simp [structuredPaperPrimeBlock]

lemma parseRpn_structuredPaperPrimeBlock (positive : Bool) (φ : ArithmeticProposition)
    (tail : List ℕ) {fuel : ℕ} (hfuel : 1 ≤ fuel) :
    parseRpn fuel (structuredPaperPrimeBlock positive φ ++ tail) =
      some (paperPrimeSentence positive φ, tail) := by
  match fuel, hfuel with
  | fuel + 1, _ =>
      rw [structuredPaperPrimeBlock]
      simp only [List.append_assoc, List.cons_append]
      rw [parseRpn.eq_def]
      norm_num
      exact parseStructuredPaperPrime_encode positive φ tail

/-! ## The decomposition compiler

`paperPrimeDecompose` recurses through the outer Boolean structure and stops at the
first-order leaves, so the block mirrors that shape exactly. -/

/-- The block whose contraction is `paperPrimeDecompose φ`. -/
def structuredPaperDecomposeBlock : ArithmeticProposition → List ℕ
  | .verum => rpn (⊤ : Sentence)
  | .falsum => rpn (⊥ : Sentence)
  | .and φ ψ => 3 :: (structuredPaperDecomposeBlock φ ++ structuredPaperDecomposeBlock ψ)
  | .or φ ψ => 4 :: (structuredPaperDecomposeBlock φ ++ structuredPaperDecomposeBlock ψ)
  | .rel r v => structuredPaperPrimeBlock true (.rel r v)
  | .nrel r v => 2 :: structuredPaperPrimeBlock true (.rel r v) ++ [0]
  | .exs φ => structuredPaperPrimeBlock true (.exs φ)
  | .all φ => 2 :: structuredPaperPrimeBlock true (.exs (∼φ)) ++ [0]

lemma parseRpn_structuredPaperDecomposeBlock_exact_suffix
    (φ : ArithmeticProposition) (tail : List ℕ) :
    parseRpn (structuredPaperDecomposeBlock φ).length
      (structuredPaperDecomposeBlock φ ++ tail) =
      some (paperPrimeDecompose φ, tail) := by
  fun_induction paperPrimeDecompose φ generalizing tail with
  | case1 => simpa only [structuredPaperDecomposeBlock] using
      parseRpn_rpn (⊤ : Sentence) tail le_rfl
  | case2 => simpa only [structuredPaperDecomposeBlock] using
      parseRpn_rpn (⊥ : Sentence) tail le_rfl
  | case5 arity r v =>
      simpa only [structuredPaperDecomposeBlock] using
        parseRpn_structuredPaperPrimeBlock true (.rel r v) tail
          (structuredPaperPrimeBlock_length_pos true (.rel r v))
  | case6 arity r v =>
      simp only [structuredPaperDecomposeBlock, List.length_cons, List.length_append,
        List.length_singleton, List.cons_append, List.append_assoc]
      rw [parseRpn_cons]
      norm_num
      rw [parseRpn_structuredPaperPrimeBlock true (.rel r v) (0 :: tail) (by omega)]
      simp only [Option.bind_some]
      rw [parseRpn_mono (0 :: tail) (by omega)
        (show parseRpn 1 (0 :: tail) = some (⊥, tail) by rfl)]
      rfl
  | case3 φ ψ ihφ ihψ =>
      simp only [structuredPaperDecomposeBlock, List.length_cons, List.length_append,
        List.cons_append, List.append_assoc]
      rw [parseRpn_cons]
      norm_num
      rw [parseRpn_mono _ (by omega) (ihφ (structuredPaperDecomposeBlock ψ ++ tail))]
      simp only [Option.bind_some]
      rw [parseRpn_mono _ (by omega) (ihψ tail)]
      rfl
  | case4 φ ψ ihφ ihψ =>
      simp only [structuredPaperDecomposeBlock, List.length_cons, List.length_append,
        List.cons_append, List.append_assoc]
      rw [parseRpn_cons]
      norm_num
      rw [parseRpn_mono _ (by omega) (ihφ (structuredPaperDecomposeBlock ψ ++ tail))]
      simp only [Option.bind_some]
      rw [parseRpn_mono _ (by omega) (ihψ tail)]
      rfl
  | case8 φ =>
      simp only [structuredPaperDecomposeBlock, List.length_cons, List.length_append,
        List.length_singleton, List.cons_append, List.append_assoc]
      rw [parseRpn_cons]
      norm_num
      rw [parseRpn_structuredPaperPrimeBlock true (.exs (∼φ)) (0 :: tail) (by omega)]
      simp only [Option.bind_some]
      rw [parseRpn_mono (0 :: tail) (by omega)
        (show parseRpn 1 (0 :: tail) = some (⊥, tail) by rfl)]
      rfl
  | case7 φ =>
      simpa only [structuredPaperDecomposeBlock] using
        parseRpn_structuredPaperPrimeBlock true (.exs φ) tail
          (structuredPaperPrimeBlock_length_pos true (.exs φ))

lemma parseRpn_structuredPaperDecomposeBlock (φ : ArithmeticProposition) (tail : List ℕ)
    {fuel : ℕ} (hfuel : (structuredPaperDecomposeBlock φ).length ≤ fuel) :
    parseRpn fuel (structuredPaperDecomposeBlock φ ++ tail) =
      some (paperPrimeDecompose φ, tail) :=
  parseRpn_mono _ hfuel (parseRpn_structuredPaperDecomposeBlock_exact_suffix φ tail)

lemma parseRpn_structuredPaperDecomposeBlock_exact (φ : ArithmeticProposition) :
    parseRpn (structuredPaperDecomposeBlock φ).length (structuredPaperDecomposeBlock φ) =
      some (paperPrimeDecompose φ, []) := by
  simpa using parseRpn_structuredPaperDecomposeBlock φ [] le_rfl

lemma parseRpn_encodePaperThreshold {T : ArithmeticTheory} [T.Δ₁]
    (X : PaperLUV T) (r : ℚ) :
    parseRpn (structuredPaperDecomposeBlock (X.thresholdFormula r)).length
      (structuredPaperDecomposeBlock (X.thresholdFormula r)) = some (X.toLUV.gt r, []) := by
  simpa using parseRpn_structuredPaperDecomposeBlock_exact (X.thresholdFormula r)

/-! ## Normal-form-metered family interface

This predicate deliberately certifies the structural payload, not Foundation's Godel
code.  The lifting theorem below adds only fixed tokens and a unary copy of the already
poly-fueled payload length.  Thus the final tag-7 value is constructed by `parseRpn` and
never occurs in the emitter's output range.

**What is metered.**  `PolyArithmeticFormulaSeq φ` asks that the *symbol list*
`encodeArithmeticFormulaSymbols (φ n)` be a `PolySegStream`: polynomially many tokens, each
of polynomially bounded value.  The serializer emits **one token per node of the Foundation
formula**, so the metered quantity is that formula's own symbol count.  Nothing here is
expanded: Godel codes are never emitted, and no numeral is rewritten into a larger object
than the author wrote.

**This is the foil, not the paper's class.**  `def:ec` (tex:753) asks for a polynomial-time
writer of the formula *as the paper writes it*, over the primitive connectives
`¬ ∧ ∨ ⟹ ⟺ ∀ ∃` of tex:560.  On `¬`, `∧`, `∨`, `⟹`, `∀`, `∃` and on numerals named
compactly in `ℒₒᵣ`, the count here equals the paper's.  On `⟺` it does not: Foundation's
`Semiformula` has no biconditional constructor, so `a 🡘 b` is notation for
`(a 🡒 b) ⋏ (b 🡒 a)` and costs `3 + 2|a| + 2|b|` symbols
(`encodeArithmeticFormulaSymbols_iff`) — both sides duplicated, a factor of two per nesting
level.  This class is therefore **strictly finer** than `def:ec`, on `⟺` alone.

The paper's condition is `PolyArithmeticSourceSeq` (`ArithmeticSource.lean`), which meters
the paper's *source* — `⟺` a constructor, expanded into normal form inside the parser and
never emitted.  This class embeds into it token for token
(`PolyArithmeticFormulaSeq.toSource`), and the inclusion is strict: the biconditional
family `iffChain` is certified there and provably not here
(`iffChainSource_polyArithmeticSourceSeq` against `iffChain_not_polyArithmeticFormulaSeq`).
Everything downstream — `PaperLUVSeq` and its concrete families — is certified in the
source class; this one survives as the sharp comparison object.

**Naming large values.**  A term's cost is the cost of the *name*, not of the value it
denotes.  Foundation's `Semiterm.Operator.numeral` is unary
(`encodeArithmeticTermSymbols_numeral`: the numeral `v` costs `2 * v - 1` symbols).  That is
an artifact of Foundation's default numeral, not something the paper imposes: the paper fixes
no numeral notation and writes numerals positionally (tex:614, tex:757).  The compact name is
available inside `ℒₒᵣ` — the `Compact numerals` section below supplies it: `binNumeral v` is
the Horner term for `v`, `O(log v)` nodes (`binNumeralEnc_length_le`), with the same value in
every model of `𝗣𝗔⁻` (`binNumeral_val`).  So on numerals neither class is narrower than
`def:ec`; `unaryRendering_two_pow_not_polyArithmeticFormulaSeq` documents the artifact. -/

/-- **The normal-form-metered class** — the strictness foil, not the paper's condition:
it meters one token per node of the *Foundation* formula, which charges `⟺` twice per side.
The paper's class is `PolyArithmeticSourceSeq` (`ArithmeticSource.lean`), into which this
one embeds by `PolyArithmeticFormulaSeq.toSource`.

*Proof kind:* `Def`. -/
def PolyArithmeticFormulaSeq {k : ℕ} (φ : ℕ → ArithmeticSemiformula ℕ k) : Prop :=
  PolySegStream (fun n => encodeArithmeticFormulaSymbols (φ n))

lemma structuredPaperPrimeBlock_polySegStream (positive : Bool)
    (φ : ℕ → ArithmeticProposition) (hφ : PolyArithmeticFormulaSeq φ) :
    PolySegStream (fun n => structuredPaperPrimeBlock positive (φ n)) := by
  obtain ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩ := hφ
  have hpayload : PolySegStream (fun n => encodeArithmeticFormulaSymbols (φ n)) :=
    ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩
  have hlength : PolyFueled cl (fun n => (encodeArithmeticFormulaSymbols (φ n)).length) :=
    hl.of_eq fun n => (hlen n).symm
  have hprefix : PolySegStream (fun _ => [1, 0, Encodable.encode positive]) :=
    PolySegStream.ofTokenStream <| (PolyTokenStream.const 1).append <|
      (PolyTokenStream.const 0).append (PolyTokenStream.const (Encodable.encode positive))
  have hframe := (PolySegStream.repeatTag 1 hlength).append
    (PolySegStream.ofTokenStream (PolyTokenStream.const 0))
  have hend : PolySegStream (fun _ => [19]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 19)
  exact (hprefix.append (hframe.append (hpayload.append hend))).of_eq fun n => by
    simp [structuredPaperPrimeBlock, List.append_assoc]

lemma structuredPaperPrime_rpnSentenceCodes (positive : Bool)
    (φ : ℕ → ArithmeticProposition) (hφ : PolyArithmeticFormulaSeq φ) :
    RpnSentenceCodes (fun n => paperPrimeSentence positive (φ n)) := by
  refine ⟨fun n => structuredPaperPrimeBlock positive (φ n),
    structuredPaperPrimeBlock_polySegStream positive φ hφ, fun n => ?_⟩
  simpa using parseRpn_structuredPaperPrimeBlock positive (φ n) []
    (structuredPaperPrimeBlock_length_pos positive (φ n))

/-! ## Emitted-token audit

Every token the structural codec emits is a fixed small constant: payload symbols lie
in the arithmetic alphabet `0..18`, framing uses `0`/`1` and the polarity bit, and the
reserved terminator `19` appears exactly once, at the block's end.  Together with the
parser-side span facts (`parseStructuredPaperPrime_span`) this pins the whole framing
discipline: scanners may locate the block boundary by the first `19`. -/

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

/-- **Framing audit**: the emitted structured block is a `19`-free span behind the
`[1, 0]` dispatch prefix, closed by exactly one terminator. -/
lemma structuredPaperPrimeBlock_span (positive : Bool) (φ : ArithmeticProposition) :
    ∃ w, structuredPaperPrimeBlock positive φ = 1 :: 0 :: (w ++ [19]) ∧
      ∀ x ∈ w, x ≠ 19 := by
  refine ⟨Encodable.encode positive ::
    (List.replicate (encodeArithmeticFormulaSymbols φ).length 1 ++
      0 :: encodeArithmeticFormulaSymbols φ), by
        simp [structuredPaperPrimeBlock], ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · cases positive <;> simp
  · rcases List.mem_append.mp hx' with h | h
    · have := List.eq_of_mem_replicate h
      omega
    · rcases List.mem_cons.mp h with rfl | h'
      · omega
      · have := encodeArithmeticFormulaSymbols_lt φ x h'
        omega

open Nat.Partrec (Code)

/-- Every fixed token list is a segment stream. -/
lemma PolySegStream.constList : ∀ c : List ℕ, PolySegStream (fun _ : ℕ => c)
  | [] => PolySegStream.ofTokenStream PolyTokenStream.nil
  | t :: c =>
      ((PolySegStream.ofTokenStream (PolyTokenStream.const t)).append
        (PolySegStream.constList c)).of_eq fun _ => rfl

/-! ## Numerals

Foundation builds numerals by a left-nested fold of `one` under `add`, so a numeral's
symbol encoding is two constant-tag runs — exactly the shape the repeat-tag emitter
produces.  This is the term-level half of the threshold syntax. -/

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

/-- Numerals of a poly-fueled value stream are structurally emittable. -/
lemma encodeArithmeticTermSymbols_numeral_polySegStream {k : ℕ} {cv : Code}
    {v : ℕ → ℕ} (hv : PolyFueled cv v) (hne : ∀ n, v n ≠ 0) :
    PolySegStream (fun n => encodeArithmeticTermSymbols
      ((Semiterm.Operator.numeral ℒₒᵣ (v n)).const : ArithmeticSemiterm ℕ k)) := by
  have hpred : PolyFueled _ (fun n => v n - 1) :=
    (subc_polyFueled.comp (hv.pair (PolyFueled.const 1))).of_eq fun n => by
      simp only [Nat.unpair_pair]
  exact ((PolySegStream.repeatTag 7 hpred).append
    (PolySegStream.repeatTag 6 hv)).of_eq fun n =>
      (encodeArithmeticTermSymbols_numeral (v n) (hne n)).symm

/-! ## Compact numerals

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

lemma binNumeralLen_pos (v : ℕ) : 0 < binNumeralLen v :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)

lemma binNumeralLen_of_lt_four {v : ℕ} (h : v < 4) : binNumeralLen v = 1 := by
  have : len4 v ≤ 1 := (len4_le_iff v 1).mpr (by simpa using h)
  simp only [binNumeralLen]
  omega

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

lemma encodeArithmeticTermSymbols_bitTerm {k : ℕ} {b : ℕ} (hb : b < 2) :
    encodeArithmeticTermSymbols ((bitTerm b).const : ArithmeticSemiterm ℕ k)
      = [b + 5] := by
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl

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

/-- The exact symbol count: one nine-token Horner block per digit *after* the first, plus
one seven-token digit block per digit. -/
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

/-- **The compact numeral is logarithmic.**  Each base-4 Horner step contributes sixteen
symbols and consumes two bits of the value, so naming `v` costs `O(log v)` — against
`2 * v - 1` for the unary numeral (`encodeArithmeticTermSymbols_numeral`). -/
lemma binNumeralEnc_length_le : ∀ v : ℕ,
    (binNumeralEnc v).length ≤ 8 * Nat.log 2 v + 7 := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rcases lt_or_ge v 4 with hv | hv
    · rw [binNumeralEnc, if_pos hv]
      simp [digitEnc]
    · have hlt : v / 4 < v := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih _ hlt
      have hlog2 : 2 ≤ Nat.log 2 v := by
        have hpow : (2 : ℕ) ^ 2 = 4 := by norm_num
        exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
      have hdiv : Nat.log 2 (v / 4) = Nat.log 2 v - 2 := by
        have h4 : v / 2 / 2 = v / 4 := by rw [Nat.div_div_eq_div_mul]
        rw [← h4, Nat.log_div_base, Nat.log_div_base]
        omega
      rw [binNumeralEnc, if_neg (by omega)]
      simp only [List.length_append, digitEnc, hornerPrefix, List.length_cons,
        List.length_nil]
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
standard-model value of `binNumeral v` recovers `v`. -/
lemma binNumeral_injective : Function.Injective binNumeral := by
  intro a b hab
  have ha := binNumeral_val_nat a
  rw [hab, binNumeral_val_nat b] at ha
  exact ha.symm

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


#print axioms parseArithmeticTermSymbols_encode
#print axioms parseArithmeticFormulaSymbols_encode
#print axioms parseRpn_structuredPaperPrimeBlock
#print axioms parseRpn_structuredPaperDecomposeBlock_exact
#print axioms parseRpn_encodePaperThreshold
#print axioms structuredPaperPrime_rpnSentenceCodes
#print axioms binNumeral_val
#print axioms binNumeral_val_nat
#print axioms binNumeral_injective
#print axioms binNumeralEnc_eq
#print axioms binNumeralEnc_length
#print axioms binNumeralEnc_length_le
#print axioms encodeArithmeticTermSymbols_binNumeral
#print axioms polySegStream_binNumeralEnc
#print axioms polySegStream_binNumeral_const
#print axioms binNumeralEnc_two_pow_polySegStream

end LogicalInduction
