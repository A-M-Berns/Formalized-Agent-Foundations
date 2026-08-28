import LogicalInduction.Construction.Witnesses.PaperLUV
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnSplice

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
* the symbol-metered family interface `PolyArithmeticFormulaSeq` and the emission
  liftings, with the emitted-token audit pinning every token to a fixed small constant;
* negation as a token map, which transports a structural certificate to the negated
  family without re-deriving its emission;
* the frontend `PaperLUVSeq`: a structurally certified family of literal paper LUVs
  compiles to `LUV.RpnThresholdCodeSeq` at the paper's exact threshold syntax, inhabited by
  the varying `1/(n+1)` family `unitFracPaperLUVSeq` — with the unary-numeral metering
  restriction disclosed at `PolyArithmeticFormulaSeq` and `PaperLUVSeq`.

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

private lemma readStructuredLength_replicate (n : ℕ) (tail : List ℕ) :
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

/-! ## Symbol-metered family interface

This predicate deliberately certifies the structural payload, not Foundation's Godel
code.  The lifting theorem below adds only fixed tokens and a unary copy of the already
poly-fueled payload length.  Thus the final tag-7 value is constructed by `parseRpn` and
never occurs in the emitter's output range.

**Disclosure — what is metered, and which paper LUVs that excludes.**
`PolyArithmeticFormulaSeq φ` asks that the *symbol list*
`encodeArithmeticFormulaSymbols (φ n)` be a `PolySegStream`: polynomially many tokens,
each of polynomially bounded value.  Foundation builds a numeral as a left-nested fold of
`one` under `add`, and `encodeArithmeticTermSymbols_numeral` below computes the cost
exactly — `encodeArithmeticTermSymbols` of the numeral `v` is
`List.replicate (v - 1) 7 ++ List.replicate v 6`, i.e. `2 * v - 1` symbols.  **Numerals
are metered in unary.**  Consequently a defining formula that names a constant of
superpolynomial magnitude has no certificate: the stream length is not
`IsPolyBounded`, which `encodeArithmeticTermSymbols_numeral` together with
`not_isPolyBounded_two_pow` refutes at the numeral `2 ^ n`.

Concretely: the `1/(n+1)` family `unitFracPaperLUVSeq` **is** admissible, since its
numerals are `n + 1`; the same threshold written with the numeral `2 ^ n` — the
paper-natural `X > 2⁻ⁿ` — is **not**.  Both are `def:luv`-admissible data for the paper,
so this is a genuine restriction on the paper's own quantifier range, not merely a
repo-side presentation choice.  It is disclosed in `LogicalInduction/README.md` and
charged per row in `scripts/coverage-classification.md`.  The faithful repair is
identified and **not** done: a write-out arithmetic-formula meter that names numerals in
*binary* — the `Code.sourceNat` pattern applied to `ArithmeticSemiformula`, as
`DigitMachineCodes` did for machine source. -/

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

/-! ## Negation as a token map

Negation-normal-form negation acts on the payload alphabet by swapping the dual tag
pairs and fixing every term token, so a structural certificate for a formula family
transports to its negation without re-deriving the emission. -/

open Nat.Partrec (Code)

/-- Token action of negation-normal-form negation on the formula alphabet. -/
def negArithTok (t : ℕ) : ℕ :=
  if t = 9 then 10 else if t = 10 then 9
  else if t = 11 then 12 else if t = 12 then 11
  else if t = 13 then 14 else if t = 14 then 13
  else if t = 15 then 16 else if t = 16 then 15
  else if t = 17 then 18 else if t = 18 then 17
  else t

lemma negArithTok_of_lt {x : ℕ} (h : x < 9) : negArithTok x = x := by
  rw [negArithTok]
  split_ifs <;> omega

lemma map_negArithTok_term {k : ℕ} (t : ArithmeticSemiterm ℕ k) :
    (encodeArithmeticTermSymbols t).map negArithTok =
      encodeArithmeticTermSymbols t := by
  conv_rhs => rw [← List.map_id (encodeArithmeticTermSymbols t)]
  exact List.map_congr_left fun x hx =>
    negArithTok_of_lt (encodeArithmeticTermSymbols_lt t x hx)

lemma encodeArithmeticFormulaSymbols_neg {k : ℕ} (φ : ArithmeticSemiformula ℕ k) :
    encodeArithmeticFormulaSymbols (∼φ) =
      (encodeArithmeticFormulaSymbols φ).map negArithTok := by
  induction φ with
  | verum => rfl
  | falsum => rfl
  | rel r v =>
      rcases r with _ | _ <;>
        simp [encodeArithmeticFormulaSymbols, negArithTok, map_negArithTok_term]
  | nrel r v =>
      rcases r with _ | _ <;>
        simp [encodeArithmeticFormulaSymbols, negArithTok, map_negArithTok_term]
  | and φ ψ ihφ ihψ =>
      show encodeArithmeticFormulaSymbols ((∼φ).or (∼ψ)) = _
      simp [encodeArithmeticFormulaSymbols, ihφ, ihψ, negArithTok]
  | or φ ψ ihφ ihψ =>
      show encodeArithmeticFormulaSymbols ((∼φ).and (∼ψ)) = _
      simp [encodeArithmeticFormulaSymbols, ihφ, ihψ, negArithTok]
  | all φ ih =>
      show encodeArithmeticFormulaSymbols ((∼φ).exs) = _
      simp [encodeArithmeticFormulaSymbols, ih, negArithTok]
  | exs φ ih =>
      show encodeArithmeticFormulaSymbols ((∼φ).all) = _
      simp [encodeArithmeticFormulaSymbols, ih, negArithTok]

/-- Streams are closed under a poly-fueled token map. -/
lemma PolySegStream.mapTok {s : ℕ → List ℕ} (h : PolySegStream s)
    {cf : Code} {f : ℕ → ℕ} (hf : PolyFueled cf f) :
    PolySegStream (fun n => (s n).map f) := by
  obtain ⟨ct, cl, tokenFn, lenFn, htok, hlen, hslen, hget⟩ := h
  refine ⟨_, cl, fun z => f (tokenFn z), lenFn, hf.comp htok, hlen, fun n => ?_,
    fun n i hi => ?_⟩
  · simpa using hslen n
  · have hilt : i < (s n).length := by rw [hslen n]; exact hi
    show f (tokenFn (Nat.pair n i)) = ((s n).map f).getD i 0
    rw [hget n i hi, List.getD_eq_getElem _ _ hilt,
      List.getD_eq_getElem _ _ (by simpa using hilt), List.getElem_map]

/-- Dispatch on an equality test against a constant. -/
private lemma polyFueled_ifEqK {cf ca cb : Code} {F A B : ℕ → ℕ}
    (hF : PolyFueled cf F) (K : ℕ) (hA : PolyFueled ca A) (hB : PolyFueled cb B) :
    ∃ c, PolyFueled c (fun z => if F z = K then A z else B z) := by
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hT : PolyFueled _ (fun z => (F z - K) + (K - F z)) :=
    (had.comp ((subc_polyFueled.comp (hF.pair (PolyFueled.const K))).pair
      (subc_polyFueled.comp ((PolyFueled.const K).pair hF)))).of_eq fun z => by
        simp only [Nat.unpair_pair]
  refine ⟨_, (ifzSel_polyFueled.comp ((hA.pair hB).pair hT)).of_eq fun z => ?_⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk : F z = K
  · rw [if_pos (by omega), if_pos hk]
  · rw [if_neg (by omega), if_neg hk]

lemma negArithTok_polyFueled {cf : Code} {F : ℕ → ℕ} (hF : PolyFueled cf F) :
    ∃ c, PolyFueled c (fun z => negArithTok (F z)) := by
  obtain ⟨_, h18⟩ := polyFueled_ifEqK hF 18 (PolyFueled.const 17) hF
  obtain ⟨_, h17⟩ := polyFueled_ifEqK hF 17 (PolyFueled.const 18) h18
  obtain ⟨_, h16⟩ := polyFueled_ifEqK hF 16 (PolyFueled.const 15) h17
  obtain ⟨_, h15⟩ := polyFueled_ifEqK hF 15 (PolyFueled.const 16) h16
  obtain ⟨_, h14⟩ := polyFueled_ifEqK hF 14 (PolyFueled.const 13) h15
  obtain ⟨_, h13⟩ := polyFueled_ifEqK hF 13 (PolyFueled.const 14) h14
  obtain ⟨_, h12⟩ := polyFueled_ifEqK hF 12 (PolyFueled.const 11) h13
  obtain ⟨_, h11⟩ := polyFueled_ifEqK hF 11 (PolyFueled.const 12) h12
  obtain ⟨_, h10⟩ := polyFueled_ifEqK hF 10 (PolyFueled.const 9) h11
  obtain ⟨c, h9⟩ := polyFueled_ifEqK hF 9 (PolyFueled.const 10) h10
  exact ⟨c, h9.of_eq fun z => by rw [negArithTok]⟩

/-- The structural certificate is closed under negation. -/
lemma PolyArithmeticFormulaSeq.neg {k : ℕ} {φ : ℕ → ArithmeticSemiformula ℕ k}
    (h : PolyArithmeticFormulaSeq φ) :
    PolyArithmeticFormulaSeq (fun n => ∼(φ n)) := by
  obtain ⟨cf, hf⟩ := negArithTok_polyFueled (PolyFueled.id)
  exact (h.mapTok hf).of_eq fun n =>
    (encodeArithmeticFormulaSymbols_neg (φ n)).symm

/-- Existential closure of a structural certificate: one extra fixed tag. -/
lemma PolyArithmeticFormulaSeq.exs {k : ℕ}
    {φ : ℕ → ArithmeticSemiformula ℕ (k + 1)} (h : PolyArithmeticFormulaSeq φ) :
    PolyArithmeticFormulaSeq (fun n => (φ n).exs) := by
  have htag : PolySegStream (fun _ : ℕ => ([18] : List ℕ)) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 18)
  exact (htag.append h).of_eq fun n => by simp [encodeArithmeticFormulaSymbols]

/-! ## The universally quantified decompose bridge

`paperPrimeDecompose` recurses only through the outer Boolean structure, so a
quantifier-headed proposition decomposes to a single structured leaf inside the
negation shell.  This is the shape the paper's threshold syntax takes. -/

lemma structuredPaperDecomposeBlock_all (φ : ArithmeticSemiformula ℕ 1) :
    structuredPaperDecomposeBlock (.all φ) =
      [2] ++ structuredPaperPrimeBlock true (.exs (∼φ)) ++ [0] := by
  simp [structuredPaperDecomposeBlock]

lemma structuredPaperDecomposeBlock_all_polySegStream
    {φ : ℕ → ArithmeticSemiformula ℕ 1} (hφ : PolyArithmeticFormulaSeq φ) :
    PolySegStream (fun n => structuredPaperDecomposeBlock (.all (φ n))) := by
  have hpayload : PolyArithmeticFormulaSeq (fun n => (∼(φ n)).exs) := hφ.neg.exs
  have hprime := structuredPaperPrimeBlock_polySegStream true
    (fun n => (∼(φ n)).exs) hpayload
  have hshell : PolySegStream (fun _ : ℕ => ([2] : List ℕ)) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 2)
  have hclose : PolySegStream (fun _ : ℕ => ([0] : List ℕ)) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 0)
  exact ((hshell.append hprime).append hclose).of_eq fun n => by
    rw [structuredPaperDecomposeBlock_all]

/-- **Decompose efficiency lifting at a quantified head**: an efficiently presented
family of universally quantified arithmetic propositions has an efficient stream of
exact paper-prime decomposition blocks.  The emitter outputs only the small structured
block; the tag-7 atom code is built by parser contraction. -/
lemma structuredPaperDecomposeAll_rpnSentenceCodes
    (φ : ℕ → ArithmeticSemiformula ℕ 1) (hφ : PolyArithmeticFormulaSeq φ) :
    RpnSentenceCodes (fun n => paperPrimeDecompose (.all (φ n))) :=
  ⟨fun n => structuredPaperDecomposeBlock (.all (φ n)),
    structuredPaperDecomposeBlock_all_polySegStream hφ,
    fun n => parseRpn_structuredPaperDecomposeBlock_exact (.all (φ n))⟩

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

/-! ## The literal first-order LUV frontend

A single `PaperLUV` carries no efficiency certificate, so the family layer supplies
one — and supplies it as *structural symbol emission of the threshold bodies*, never as
a bound on Foundation's Godel codes and never as a caller-provided tag-7 code.  The
compiler below turns that certificate into the paper's exact threshold sentences. -/

section Frontend

variable {T : ArithmeticTheory} [T.Δ₁]

/-- The body under the paper's threshold quantifier, as a proposition-level formula. -/
def paperThresholdBody (X : PaperLUV T) (r : ℚ) : ArithmeticSemiformula ℕ 1 :=
  ((X.formula 🡒 paperRatGtDef r : ArithmeticSemisentence 1) :
    ArithmeticSemiformula ℕ 1)

lemma paperThresholdFormula_eq_all (X : PaperLUV T) (r : ℚ) :
    ((X.thresholdFormula r : ArithmeticSentence) : ArithmeticProposition) =
      .all (paperThresholdBody X r) := by
  simp only [PaperLUV.thresholdFormula, paperThresholdBody]
  simp
  rfl

lemma paperLUV_gt_eq (X : PaperLUV T) (r : ℚ) :
    X.toLUV.gt r = paperPrimeDecompose (.all (paperThresholdBody X r)) := by
  rw [PaperLUV.toLUV_gt, paperThresholdFormula_eq_all]

/-! ### Threshold syntax as small tokens

`paperRatGtDef` is a fixed template around two Foundation numerals, so its encoding
splits into two constant blocks and two numeral runs; the numerals at query index
`⟨n, ⟨k, i⟩⟩` are the reduced numerator and denominator of `i / k`, which the fuel
calculus already computes (`gcdc_polyFueled`, `divmod1_polyFueled`).  Together with the
implication shell this discharges the threshold-body certificate from a certificate on
the LUVs' defining formulas alone. -/

private def ratGtPre : List ℕ :=
  [18, 18, 15, 16, 15, 13, 3, 2, 0, 3, 0, 11, 3, 1, 2, 0, 7, 8, 3, 0, 3, 0, 3, 2,
   0, 15, 16, 11, 3, 0, 3, 2, 0, 13, 3, 0, 3, 2, 0, 11, 3, 1, 2, 0, 7, 7, 8, 3, 2,
   0, 3, 2, 0, 3, 2, 0, 3, 0, 15, 13, 5, 3, 0, 13, 8]

private def ratGtMid : List ℕ := [3, 0, 8, 3, 2, 0]

private lemma oringMul_term :
    (Semiterm.Operator.Mul.mul : Semiterm.Operator ℒₒᵣ 2).term =
      Semiterm.func Language.Mul.mul Semiterm.bvar := rfl

private lemma oringAdd_term :
    (Semiterm.Operator.Add.add : Semiterm.Operator ℒₒᵣ 2).term =
      Semiterm.func Language.Add.add Semiterm.bvar := rfl

private lemma oringOne_term :
    (Semiterm.Operator.One.one : Semiterm.Operator ℒₒᵣ 0).term =
      Semiterm.func Language.One.one ![] := rfl

private lemma oringNumZero_term :
    (Semiterm.Operator.numeral ℒₒᵣ 0).term =
      Semiterm.func Language.Zero.zero ![] := rfl

private lemma emb_subst_nil_comm {n : ℕ} (t : Semiterm ℒₒᵣ Empty 0) :
    (Rew.emb ((Rew.subst ![]) t) : ArithmeticSemiterm ℕ n) =
      (Rew.subst ![]) (Rew.emb t) := by
  have h : ((Rew.emb : Rew ℒₒᵣ Empty n ℕ n).comp (Rew.subst ![])) =
      ((Rew.subst ![]).comp (Rew.emb : Rew ℒₒᵣ Empty 0 ℕ 0)) := by
    ext x
    · exact Fin.elim0 x
    · exact IsEmpty.elim inferInstance x
  rw [← Rew.comp_app, h, Rew.comp_app]

private def encNumeral (v : ℕ) : List ℕ :=
  encodeArithmeticTermSymbols
    ((Semiterm.Operator.numeral ℒₒᵣ v).const : ArithmeticSemiterm ℕ 3)

private lemma enc_paperRatGtDef (r : ℚ) (hr : ¬ r < 0) :
    encodeArithmeticFormulaSymbols
      ((paperRatGtDef r : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      ratGtPre ++ encNumeral r.num.natAbs ++ ratGtMid ++ encNumeral r.den := by
  rw [paperRatGtDef, if_neg hr]
  simp [pairDef, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, ratGtPre, ratGtMid, encNumeral,
    Semiformula.Operator.lt_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.le_def, Semiterm.Operator.operator,
    Semiterm.Operator.const, oringMul_term, oringAdd_term,
    oringNumZero_term, Matrix.fun_eq_vec_two, emb_subst_nil_comm]

private lemma encNumeral_zero : encNumeral 0 = [5] := rfl

private lemma encNumeral_of_ne_zero {v : ℕ} (hv : v ≠ 0) :
    encNumeral v = List.replicate (v - 1) 7 ++ List.replicate v 6 :=
  encodeArithmeticTermSymbols_numeral v hv

/-- Every fixed token list is a segment stream. -/
lemma PolySegStream.constList : ∀ c : List ℕ, PolySegStream (fun _ : ℕ => c)
  | [] => PolySegStream.ofTokenStream PolyTokenStream.nil
  | t :: c =>
      ((PolySegStream.ofTokenStream (PolyTokenStream.const t)).append
        (PolySegStream.constList c)).of_eq fun _ => rfl

/-- Numerals of a poly-fueled value stream are emittable, zero included. -/
lemma encNumeral_polySegStream {cv : Code} {v : ℕ → ℕ} (hv : PolyFueled cv v) :
    PolySegStream (fun n => encNumeral (v n)) := by
  have hpred : PolyFueled _ (fun n => v n - 1) :=
    (subc_polyFueled.comp (hv.pair (PolyFueled.const 1))).of_eq fun n => by
      simp only [Nat.unpair_pair]
  have hpos : PolySegStream (fun n => List.replicate (v n - 1) 7 ++
      List.replicate (v n) 6) :=
    (PolySegStream.repeatTag 7 hpred).append (PolySegStream.repeatTag 6 hv)
  refine ((PolySegStream.constList [5]).ifZero hpos hv).of_eq fun n => ?_
  by_cases h : v n = 0
  · rw [if_pos h, h, encNumeral_zero]
  · rw [if_neg h, encNumeral_of_ne_zero h]

/-- The threshold rational named by a `RpnThresholdCodeSeq` query index `⟨n, ⟨k, i⟩⟩`. -/
def queryRat (m : ℕ) : ℚ :=
  (m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ)

lemma queryRat_nonneg (m : ℕ) : ¬ queryRat m < 0 := by
  rw [queryRat]
  exact not_lt.mpr (div_nonneg (by positivity) (by positivity))

lemma queryNum_polyFueled :
    ∃ c, PolyFueled c (fun m => (queryRat m).num.natAbs) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have numPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hi))
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 0).pair numPF).pair hk)).of_eq fun m => ?_⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, queryRat, hk0]
    simp
  · rw [if_neg hk0, queryRat]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, ComputableLUV.natCast_div_num hk0, Int.natAbs_natCast]

lemma queryDen_polyFueled :
    ∃ c, PolyFueled c (fun m => (queryRat m).den) := by
  obtain ⟨cg, hgcd⟩ := gcdc_polyFueled
  obtain ⟨cdm, hdm⟩ := divmod1_polyFueled
  have hk := PolyFueled.left.comp PolyFueled.right
  have hi := PolyFueled.right.comp PolyFueled.right
  have gPF := hgcd.comp (hi.pair hk)
  have pgPF := predc_polyFueled.comp gPF
  have denPF := PolyFueled.left.comp (hdm.comp (pgPF.pair hk))
  refine ⟨_, (ifzSel_polyFueled.comp
    (((PolyFueled.const 1).pair denPF).pair hk)).of_eq fun m => ?_⟩
  simp only [Nat.unpair_pair, ifzSelFn]
  by_cases hk0 : m.unpair.2.unpair.1 = 0
  · rw [if_pos hk0, queryRat, hk0]
    simp
  · rw [if_neg hk0, queryRat]
    have hg : 0 < Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hk0)
    have hg1 : (Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1).pred + 1 =
        Nat.gcd m.unpair.2.unpair.2 m.unpair.2.unpair.1 :=
      Nat.succ_pred_eq_of_pos hg
    rw [hg1, ComputableLUV.natCast_div_den hk0]

/-- The implication shell in symbol form. -/
lemma encodeArithmeticFormulaSymbols_imp {k : ℕ}
    (A B : ArithmeticSemiformula ℕ k) :
    encodeArithmeticFormulaSymbols (A 🡒 B) =
      16 :: ((encodeArithmeticFormulaSymbols A).map negArithTok ++
        encodeArithmeticFormulaSymbols B) := by
  show encodeArithmeticFormulaSymbols ((∼A).or B) = _
  rw [encodeArithmeticFormulaSymbols, encodeArithmeticFormulaSymbols_neg]

/-- The threshold syntax of a rational query is structurally emittable. -/
lemma paperRatGt_polySegStream :
    PolySegStream (fun m => encodeArithmeticFormulaSymbols
      ((paperRatGtDef (queryRat m) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  obtain ⟨cn, hnum⟩ := queryNum_polyFueled
  obtain ⟨cd, hden⟩ := queryDen_polyFueled
  refine (((PolySegStream.constList ratGtPre).append
    (encNumeral_polySegStream hnum)).append
      ((PolySegStream.constList ratGtMid).append
        (encNumeral_polySegStream hden))).of_eq fun m => ?_
  rw [enc_paperRatGtDef _ (queryRat_nonneg m)]
  simp [List.append_assoc]

lemma paperThresholdBody_polySegStream (X : ℕ → PaperLUV T)
    (h : PolyArithmeticFormulaSeq (fun n =>
      (((X n).formula : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1))) :
    PolyArithmeticFormulaSeq (fun m =>
      paperThresholdBody (X m.unpair.1) (queryRat m)) := by
  obtain ⟨cf, hf⟩ := negArithTok_polyFueled (PolyFueled.id)
  have hX := h.comp (PolyFueled.left)
  refine ((PolySegStream.constList [16]).append
    ((hX.mapTok hf).append paperRatGt_polySegStream)).of_eq fun m => ?_
  show _ = encodeArithmeticFormulaSymbols (paperThresholdBody _ _)
  rw [paperThresholdBody]
  simp only [LogicalConnective.HomClass.map_imply]
  rw [encodeArithmeticFormulaSymbols_imp]
  simp [List.append_assoc]

/-- An efficiently presented family of literal paper LUVs.  The certificate is
structural symbol emission of the LUVs' own *defining formulas* — never a bound on
Foundation codes, a caller-provided tag-7 code, or a semantic handle.  Everything the
threshold syntax adds on top (the implication shell, the fixed comparison template, and
the reduced numerals of the query rational) is discharged internally.

Inhabited by `unitFracPaperLUVSeq`, the family of values `1/(n+1)`.

**Disclosure — this field is a restriction on `def:luv` data.**  `structural` is
`PolyArithmeticFormulaSeq`, which meters the defining formula's *symbol list* with
Foundation's numerals spelled in **unary** (`encodeArithmeticTermSymbols_numeral`: the
numeral `v` costs `2 * v - 1` symbols).  A `PaperLUV` whose defining formula names a
constant of superpolynomial magnitude therefore admits no `PaperLUVSeq` — the excluded
family `X > 2⁻ⁿ`, written with the numeral `2 ^ n`, is refuted by
`encodeArithmeticTermSymbols_numeral` plus `not_isPolyBounded_two_pow`, while the
`1/(n+1)` family is admissible.  `PaperLUV` itself carries no such field; only the
sequence wrapper does, and this wrapper is the repo's only route from a literal
first-order paper LUV into `LUV.RpnThresholdCodeSeq`.  See the *Symbol-metered family
interface* section above for the identified, not-yet-built binary-numeral repair.
Paper node: `def:luv` -/
structure PaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] where
  luv : ℕ → PaperLUV T
  structural : PolyArithmeticFormulaSeq (fun n =>
    (((luv n).formula : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1))

/-- The threshold bodies inherit the family's structural certificate. -/
lemma PaperLUVSeq.thresholdBody_structural (X : PaperLUVSeq T) :
    PolyArithmeticFormulaSeq (fun m =>
      paperThresholdBody (X.luv m.unpair.1) (queryRat m)) :=
  paperThresholdBody_polySegStream X.luv X.structural

/-- Any single literal paper LUV presents as a constant family.  This is a
convenience, not the non-vacuity witness: see `unitFracPaperLUVSeq` for a family whose
defining formulas genuinely vary with `n`. -/
def PaperLUVSeq.const (X : PaperLUV T) : PaperLUVSeq T where
  luv _ := X
  structural := PolySegStream.constList _

/-- The literal threshold syntax of a paper-LUV family is emittable in the symbol-metered
calculus, so the abstract LUVs it compiles to carry the threshold-code certificate the
expectation layer consumes.
Paper node: `def:ec` -/
lemma PaperLUVSeq.rpnThresholdCodeSeq (X : PaperLUVSeq T) :
    LUV.RpnThresholdCodeSeq (fun n => (X.luv n).toLUV) := by
  have h := structuredPaperDecomposeAll_rpnSentenceCodes _ X.thresholdBody_structural
  exact h.of_eq fun m => (paperLUV_gt_eq _ _).symm

/-! ### A concrete family

The interface is inhabited by a genuinely varying family: the LUVs of value `1/(n+1)`,
whose defining formulas grow with `n` and whose uniqueness and unit-interval facts are
discharged in any theory extending `𝗜𝚺₁` by completeness over its models. -/

/-- The value `1/(n+1)`: the code of that fraction, with the denominator named once. -/
def unitFracFormula (n : ℕ) : ArithmeticSemisentence 1 :=
  “q. ∃ b, !!(Semiterm.Operator.numeral ℒₒᵣ (n + 1)) = b ∧ !pairDef q 1 b”

private def unitFracPost : List ℕ :=
  [3, 0, 16, 15, 13, 6, 3, 0, 11, 3, 2, 0, 7, 8, 3, 0, 3, 0, 6, 15, 16, 11, 3, 0,
   6, 13, 3, 0, 6, 11, 3, 2, 0, 7, 7, 8, 6, 6, 6, 3, 0]

private lemma oringNumOne_term :
    (Semiterm.Operator.numeral ℒₒᵣ 1).term =
      Semiterm.func Language.One.one ![] := rfl

/-- The numeral encoding in the normal form the frame computation leaves behind. -/
private lemma encNumeral_norm (k v : ℕ) (hv : v ≠ 0) :
    encodeArithmeticTermSymbols
      (((Rew.subst ![]) (Rew.emb (Semiterm.Operator.numeral ℒₒᵣ v).term)) :
        ArithmeticSemiterm ℕ k) =
      List.replicate (v - 1) 7 ++ List.replicate v 6 := by
  have h := encodeArithmeticTermSymbols_numeral (k := k) v hv
  simpa [Semiterm.Operator.const, Semiterm.Operator.operator] using h

private lemma enc_unitFracFormula (n : ℕ) :
    encodeArithmeticFormulaSymbols
      ((unitFracFormula n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ (List.replicate n 7 ++ List.replicate (n + 1) 6) ++
        unitFracPost := by
  rw [unitFracFormula]
  simp [pairDef, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, unitFracPost,
    Semiformula.Operator.lt_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.le_def, Semiterm.Operator.operator,
    Semiterm.Operator.const, oringMul_term, oringAdd_term,
    oringNumZero_term, oringNumOne_term, Matrix.fun_eq_vec_two,
    emb_subst_nil_comm, encNumeral_norm _ (n + 1) (by omega)]

/-- The literal paper LUV of value `1/(n+1)`. -/
def unitFracPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (n : ℕ) :
    PaperLUV T where
  formula := unitFracFormula n
  unique := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, unitFracFormula, pairDef, numeral_eq_natCast]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn, hn.ne']
  unit := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, unitFracFormula, pairDef, paperRatUnitDef,
      numeral_eq_natCast]
    intro x hx
    refine ⟨1, (n : M) + 1, ?_, ?_, ?_⟩
    · rcases hx with ⟨hn, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨by simpa using hn, rfl⟩
      · exact Or.inr ⟨by simp, by simp⟩
    · simp
    · simp

/-- The defining formulas of the `1/(n+1)` family are structurally emittable. -/
lemma unitFrac_polyArithmeticFormulaSeq :
    PolyArithmeticFormulaSeq (fun n =>
      ((unitFracFormula n : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  have hid : PolyFueled _ (fun n : ℕ => n) := PolyFueled.id
  have hsucc : PolyFueled _ (fun n : ℕ => n + 1) := PolyFueled.id.succ_comp
  refine ((PolySegStream.constList [18, 15, 11]).append
    (((PolySegStream.repeatTag 7 hid).append
      (PolySegStream.repeatTag 6 hsucc)).append
        (PolySegStream.constList unitFracPost))).of_eq fun n => ?_
  rw [enc_unitFracFormula n]
  simp

/-- **Non-vacuity** (`N+`): a genuinely varying family of literal paper LUVs, with
values `1/(n+1)`, carrying the structural certificate.
Paper node: `def:luv` -/
def unitFracPaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : PaperLUVSeq T where
  luv n := unitFracPaperLUV T n
  structural := unitFrac_polyArithmeticFormulaSeq

/-- **The literal paper frontend**: an efficiently presented family of literal
first-order paper LUVs is both semantically valued on every completed world of the
canonical theorem process and efficiently thresholded in the symbol-metered emission
calculus.

This is a statement about `PaperLUVSeq`, **not** about every `PaperLUV` sequence: the
`structural` field is an extra hypothesis `PaperLUV` does not carry, and it excludes
defining formulas naming superpolynomial constants (see `PaperLUVSeq`).
Paper node: `def:luv` -/
lemma PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (X : PaperLUVSeq T) :
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
        ∃ x : ℝ, v.ValuesAt (X.luv n).toLUV x) ∧
      LUV.RpnThresholdCodeSeq (fun n => (X.luv n).toLUV) :=
  ⟨fun n => PaperLUV.source_valued (X.luv n), X.rpnThresholdCodeSeq⟩

/-- **The frontend on a concrete family**: the literal `1/(n+1)` LUVs are valued on every
completed world of the canonical theorem process and efficiently thresholded, so the
frontend's two conclusions hold of an actual first-order family rather than only of a
hypothetical one.
Paper node: `def:luv` -/
lemma unitFracPaperLUVSeq_frontend [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
        ∃ x : ℝ, v.ValuesAt ((unitFracPaperLUVSeq T).luv n).toLUV x) ∧
      LUV.RpnThresholdCodeSeq (fun n => ((unitFracPaperLUVSeq T).luv n).toLUV) :=
  (unitFracPaperLUVSeq T).source_valued_and_rpnThresholdCodeSeq

/-! ### `def:blcp` over literal paper LUVs

`LUVCombination.BoundedSequence` (`Properties/ExpectationProperties.lean`) states the
paper's bounded LUV-combination sequence over the abstract threshold carrier `LUV`, which
admits families that are not the definable quantities of `def:luv`.  The layer below states
the same node over `PaperLUV`: the combination's shares are literal first-order paper LUVs,
and the abstract carrier is reached only through `toLUV`. -/

/-- A LUV-combination sequence whose shares are literal paper LUVs, together with the
paper's efficiency data for its constants and coefficients.  The fields other than `luvs`
are exactly those of `LUVCombinationSyntax`; `luvs` replaces its abstract `luv : ℕ → LUV`
with a structurally certified family of `PaperLUV`s.
Paper node: `def:blcp` -/
structure PaperLUVCombination (T : ArithmeticTheory) [T.Δ₁] where
  /-- The literal paper LUVs; the share at `⟨n,j⟩` is `luvs.luv (Nat.pair n j)`. -/
  luvs : PaperLUVSeq T
  /-- Number of shares in member `n`. -/
  termCount : ℕ → ℕ
  /-- Trailing constant feature of member `n`. -/
  const : ℕ → EF
  /-- Coefficient of the share at `⟨n,j⟩`. -/
  coefficient : ℕ → EF
  /-- The term count is polynomially computable. -/
  termCount_poly : ∃ c, PolyFueled c termCount
  /-- The constants are polynomially emittable. -/
  const_poly : BigSpliceStream (fun n => (const n).serialize)
  /-- The coefficients are polynomially emittable. -/
  coefficient_poly : BigSpliceStream (fun z => (coefficient z).serialize)
  /-- Constants read only prices of days already seen. -/
  const_rank : ∀ n, (const n).rank ≤ n
  /-- Coefficients read only prices of days already seen. -/
  coefficient_rank : ∀ n j, j < termCount n → (coefficient (Nat.pair n j)).rank ≤ n
  /-- Constants are closed: no free variable. -/
  const_closed : ∀ n ρ V, (const n).denoteWith ρ V = (const n).denote V
  /-- Coefficients are closed: no free variable. -/
  coefficient_closed : ∀ z ρ V, (coefficient z).denoteWith ρ V = (coefficient z).denote V

namespace PaperLUVCombination

/-- The combination sequence a paper-LUV presentation denotes, in the abstract carrier. -/
def combination (D : PaperLUVCombination T) : ℕ → LUVCombination := fun n =>
  { const := D.const n
    terms := (List.range (D.termCount n)).map (fun j =>
      (D.coefficient (Nat.pair n j), (D.luvs.luv (Nat.pair n j)).toLUV)) }

/-- The compact combination syntax of the denoted sequence.  Its threshold-code
certificate is the paper family's own structural one, so no code is assumed of the shares
beyond what their defining formulas supply. -/
def toSyntax (D : PaperLUVCombination T) : LUVCombinationSyntax D.combination where
  termCount := D.termCount
  coefficient := D.coefficient
  luv z := (D.luvs.luv z).toLUV
  termCount_poly := D.termCount_poly
  const_poly := D.const_poly
  coefficient_poly := D.coefficient_poly
  threshold_poly := D.luvs.rpnThresholdCodeSeq
  terms_eq _ := rfl
  const_rank := D.const_rank
  coefficient_rank := D.coefficient_rank
  const_closed := D.const_closed
  coefficient_closed := D.coefficient_closed

/-- **`def:blcp` at the paper's own LUVs.**  A polynomially presented combination sequence
over literal first-order paper LUVs, with one uniform `L¹` bound, is a bounded
LUV-combination sequence in the sense the expectation theorems consume.  Kind `C`;
hypotheses `(a)`.
Paper node: `def:blcp` -/
noncomputable def boundedSequence (D : PaperLUVCombination T) {P : History}
    (hB : ∃ B : ℝ, ∀ n, (D.combination n).l1Norm P ≤ B) :
    LUVCombination.BoundedSequence D.combination P where
  poly := D.toSyntax.polySequence
  bounded := hB

end PaperLUVCombination

/-- The single-share combination sequence `1 · X_n + 0` over the `1/(n+1)` paper LUVs.
Its shares genuinely vary with `n`.
Paper node: `def:blcp` -/
def unitFracPaperLUVCombination (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
    PaperLUVCombination T where
  luvs := unitFracPaperLUVSeq T
  termCount _ := 1
  const _ := .const 0
  coefficient _ := .const 1
  termCount_poly := ⟨_, PolyFueled.const 1⟩
  const_poly := BigSpliceStream.serialize_const 0
  coefficient_poly := BigSpliceStream.serialize_const 1
  const_rank n := Nat.zero_le n
  coefficient_rank n _ _ := Nat.zero_le n
  const_closed _ _ _ := by simp
  coefficient_closed _ _ _ := by simp

/-- **Non-vacuity** (`N+`) for `def:blcp` at the paper's own LUVs: the `1/(n+1)` family
presents a bounded combination sequence over every market, with `L¹` bound `1`.
Kind `N+`; hypotheses `(a)`.
Paper node: `def:blcp` -/
noncomputable def unitFracPaperLUVBoundedSequence
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (P : History) :
    LUVCombination.BoundedSequence (unitFracPaperLUVCombination T).combination P :=
  (unitFracPaperLUVCombination T).boundedSequence
    ⟨1, fun n => by
      simp [PaperLUVCombination.combination, unitFracPaperLUVCombination,
        LUVCombination.l1Norm, LUVCombination.shareNorm]⟩

#print axioms PaperLUVCombination.boundedSequence
#print axioms unitFracPaperLUVBoundedSequence

end Frontend

#print axioms unitFracPaperLUVSeq
#print axioms unitFracPaperLUVSeq_frontend
#print axioms PaperLUVSeq.rpnThresholdCodeSeq
#print axioms PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq

#print axioms parseArithmeticTermSymbols_encode
#print axioms parseArithmeticFormulaSymbols_encode
#print axioms parseRpn_structuredPaperPrimeBlock
#print axioms parseRpn_structuredPaperDecomposeBlock_exact
#print axioms parseRpn_encodePaperThreshold
#print axioms structuredPaperPrime_rpnSentenceCodes

end LogicalInduction
