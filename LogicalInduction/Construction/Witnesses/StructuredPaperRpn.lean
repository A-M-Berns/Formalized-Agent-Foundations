import LogicalInduction.Construction.Witnesses.PaperLUV
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnSplice
import LogicalInduction.Properties.ExpectationConvergence

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
  the varying `1/(n+1)` family `unitFracPaperLUVSeq` and by the superpolynomially small
  `2⁻ⁿ` family `dyadicPaperLUVSeq`, whose denominator is named by the compact numeral
  `binNumeral`, with `PaperLUV.rpnThresholdCodes` the single-LUV route into
  `LUV.RpnThresholdCodes` (the hypothesis of `LUV.expect_converges`, `thm:ec`);
* the two recorded boundaries of the metering:
  `unaryRendering_two_pow_not_polyArithmeticFormulaSeq`, an artifact of Foundation's *unary*
  `Operator.numeral` and not a narrowing of `def:ec` (the value is nameable compactly inside
  `ℒₒᵣ`), and `iffChain_not_polyArithmeticFormulaSeq`, a genuine gap: Foundation's
  `Semiformula` is negation-normal-form and has no `⟺` constructor, so a paper-`def:ec`
  family nesting `⟺` to depth `Ω(n)` is excluded here.  That gap is the disclosed
  object-language substitution `dd:nnf`.

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

**What is metered.**  `PolyArithmeticFormulaSeq φ` asks that the *symbol list*
`encodeArithmeticFormulaSymbols (φ n)` be a `PolySegStream`: polynomially many tokens, each
of polynomially bounded value.  The serializer emits **one token per node of the Foundation
formula**, so the metered quantity is that formula's own symbol count.  Nothing here is
expanded: Godel codes are never emitted, and no numeral is rewritten into a larger object
than the author wrote.

**How this compares with `def:ec`.**  `def:ec` (tex:753) asks for a polynomial-time writer of
the formula *as the paper writes it*.  For the paper's `¬`, `∧`, `∨`, `⟹`, `∀` and `∃`, and
for numerals named compactly in `ℒₒᵣ`, the count here **equals** the paper's symbol count.
For `⟺` it does **not**.  Foundation's `Semiformula` is a negation-normal-form datatype whose
constructors are `verum/falsum/rel/nrel/and/or/all/exs`; it has no biconditional constructor,
so `a 🡘 b` is notation for `(a 🡒 b) ⋏ (b 🡒 a)` and costs `3 + 2|a| + 2|b|` symbols
(`encodeArithmeticFormulaSymbols_iff`) — both sides duplicated, a factor of two per nesting
level.  The paper's language has `⟺` as a *primitive* connective (tex:560), so a family
nesting `⟺` to depth `Ω(n)` is `def:ec`-writable in `O(n)` characters and yet has no
certificate here: `iffChain_not_polyArithmeticFormulaSeq`.  The class is therefore **not
coextensive with `def:ec`** — it is strictly finer, on `⟺` alone.  Implication is unaffected,
since negation is a linear token map (`encodeArithmeticFormulaSymbols_neg`), so `🡒` costs
`1 + |a| + |b|`.

This is the object-language substrate substitution `dd:nnf`: sentences and LUV formulas are
Foundation NNF `Semiformula`s.  It is disclosed **once, globally** — in the `dd:*` glossary in
`LogicalInduction.lean`, in `LogicalInduction/README.md`, and in
`scripts/coverage-classification.md` — like `dd:fuel`, and is not charged per row.  The
faithful repair is identified and **not done**: a compact formula *source* language carrying
`iff`/`imp`/`neg` as primitives, metered at the source and decoded into NNF for semantics —
the `Code.sourceNat` pattern this development already uses for programs.  (A binary-numeral
source language was considered for a different purpose and rejected as a permissive widening
past `def:ec`; that objection does not transfer, because `⟺` *is* a paper primitive and a
source language would only restore parity with it.)

**Naming large values.**  A term's cost is the cost of the *name*, not of the value it
denotes.  Foundation's `Semiterm.Operator.numeral` is unary
(`encodeArithmeticTermSymbols_numeral`: the numeral `v` costs `2 * v - 1` symbols).  That is
an artifact of Foundation's default numeral, not something the paper imposes: the paper fixes
no numeral notation and writes numerals positionally (tex:614, tex:757).  The compact name is
available inside `ℒₒᵣ` — the `Compact numerals` section above supplies it: `binNumeral v` is
the Horner term for `v`, `O(log v)` nodes (`binNumeralEnc_length_le`), with the same value in
every model of `𝗣𝗔⁻` (`binNumeral_val`).  So on numerals the class is **not** narrower than
`def:ec`; `unaryRendering_two_pow_not_polyArithmeticFormulaSeq` documents the artifact.

**Reach.**  Two inhabited families bracket the class: `unitFracPaperLUVSeq` at `1/(n+1)` and
`dyadicPaperLUVSeq` at `2⁻ⁿ`, the paper-natural superpolynomially small value, reached by
naming `2 ^ n` with `binNumeral`. -/

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

/-! ## Compact numerals

Foundation's `Semiterm.Operator.numeral` is unary, so naming a large value with it costs
symbols linear in the value.  That is the cost model of the paper's own `ℒₒᵣ`, and the
paper does not pay it: it names large values by *compact terms* or by definitions
(tex:614, "writing `⌜f(3)⌝` does not involve computing `f(3)`").  `binNumeral` is the
compact naming a paper author has in `ℒₒᵣ` itself — Horner form over `0`/`1`/`+`/`*`,
`O(log v)` nodes for the value `v` — with the same value in every model of `𝗣𝗔⁻`. -/

/-- Horner-form ("binary") numeral: the value `v` named by `O(log v)` `ℒₒᵣ` nodes,
`2k ↦ (1+1) * k` and `2k+1 ↦ (1+1) * k + 1`. -/
def binNumeral : ℕ → Semiterm.Const ℒₒᵣ
  | 0 => Semiterm.Operator.Zero.zero
  | 1 => Semiterm.Operator.One.one
  | v + 2 =>
      if (v + 2) % 2 = 0 then
        Semiterm.Operator.Mul.mul.comp
          ![Semiterm.Operator.Add.add.comp
              ![Semiterm.Operator.One.one, Semiterm.Operator.One.one],
            binNumeral ((v + 2) / 2)]
      else
        Semiterm.Operator.Add.add.comp
          ![Semiterm.Operator.Mul.mul.comp
              ![Semiterm.Operator.Add.add.comp
                  ![Semiterm.Operator.One.one, Semiterm.Operator.One.one],
                binNumeral ((v + 2) / 2)],
            Semiterm.Operator.One.one]
termination_by n => n
decreasing_by all_goals exact Nat.div_lt_self (by omega) (by omega)

/-- The symbol list of `binNumeral`, read off the same recursion. -/
def binNumeralEnc : ℕ → List ℕ
  | 0 => [5]
  | 1 => [6]
  | v + 2 =>
      if (v + 2) % 2 = 0 then [8, 7, 6, 6] ++ binNumeralEnc ((v + 2) / 2)
      else [7, 8, 7, 6, 6] ++ binNumeralEnc ((v + 2) / 2) ++ [6]
termination_by n => n
decreasing_by all_goals exact Nat.div_lt_self (by omega) (by omega)

lemma encodeArithmeticTermSymbols_binNumeral {k : ℕ} :
    ∀ v : ℕ, encodeArithmeticTermSymbols
      ((binNumeral v).const : ArithmeticSemiterm ℕ k) = binNumeralEnc v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    match v with
    | 0 => rw [binNumeral, binNumeralEnc]; rfl
    | 1 => rw [binNumeral, binNumeralEnc]; rfl
    | (w + 2) =>
        have hlt : (w + 2) / 2 < w + 2 := Nat.div_lt_self (by omega) (by omega)
        have hrec := ih _ hlt
        rw [binNumeral, binNumeralEnc]
        split <;> rename_i hpar
        · show (8 : ℕ) :: (encodeArithmeticTermSymbols
            ((Semiterm.Operator.Add.add.comp
              ![Semiterm.Operator.One.one, Semiterm.Operator.One.one] :
                Semiterm.Const ℒₒᵣ).const : ArithmeticSemiterm ℕ k) ++
            encodeArithmeticTermSymbols
              ((binNumeral ((w + 2) / 2)).const : ArithmeticSemiterm ℕ k)) = _
          rw [hrec]
          rfl
        · show (7 : ℕ) :: (encodeArithmeticTermSymbols
            ((Semiterm.Operator.Mul.mul.comp
              ![Semiterm.Operator.Add.add.comp
                  ![Semiterm.Operator.One.one, Semiterm.Operator.One.one],
                binNumeral ((w + 2) / 2)] : Semiterm.Const ℒₒᵣ).const :
                  ArithmeticSemiterm ℕ k) ++
            encodeArithmeticTermSymbols
              ((Semiterm.Operator.One.one : Semiterm.Const ℒₒᵣ).const :
                ArithmeticSemiterm ℕ k)) = _
          show (7 : ℕ) :: ((8 : ℕ) :: (encodeArithmeticTermSymbols
            ((Semiterm.Operator.Add.add.comp
              ![Semiterm.Operator.One.one, Semiterm.Operator.One.one] :
                Semiterm.Const ℒₒᵣ).const : ArithmeticSemiterm ℕ k) ++
            encodeArithmeticTermSymbols
              ((binNumeral ((w + 2) / 2)).const : ArithmeticSemiterm ℕ k)) ++ [6]) = _
          rw [hrec]
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

/-- **The compact numeral is logarithmic.**  Each halving contributes at most six
symbols, so naming `v` costs `O(log v)` — against `2 * v - 1` for the unary numeral
(`encodeArithmeticTermSymbols_numeral`). -/
lemma binNumeralEnc_length_le : ∀ v : ℕ,
    (binNumeralEnc v).length ≤ 6 * Nat.log 2 v + 1 := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    match v with
    | 0 => rw [binNumeralEnc]; simp
    | 1 => rw [binNumeralEnc]; simp
    | (w + 2) =>
        have hlt : (w + 2) / 2 < w + 2 := Nat.div_lt_self (by omega) (by omega)
        have hrec := ih _ hlt
        have hlog : Nat.log 2 ((w + 2) / 2) + 1 = Nat.log 2 (w + 2) := by
          rw [Nat.log_div_base]
          have : 0 < Nat.log 2 (w + 2) :=
            Nat.log_pos (by norm_num) (by omega)
          omega
        rw [binNumeralEnc]
        split <;> simp only [List.length_append, List.length_cons,
          List.length_nil] <;> omega

/-- At `2 ^ n` the compact numeral is a run of `n` copies of the doubling block. -/
lemma binNumeralEnc_two_pow : ∀ n : ℕ,
    binNumeralEnc (2 ^ n) = (List.replicate n [8, 7, 6, 6]).flatten ++ [6] := by
  intro n
  induction n with
  | zero => rw [pow_zero, binNumeralEnc]; simp
  | succ n ih =>
      have hge : 2 ≤ 2 ^ (n + 1) := by
        calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (n + 1) = (2 ^ (n + 1) - 2) + 2 := by omega
      have hdiv : (2 ^ (n + 1)) / 2 = 2 ^ n := by
        rw [pow_succ]; omega
      rw [h2, binNumeralEnc, if_pos (by omega), ← h2, hdiv, ih,
        List.replicate_succ, List.flatten_cons]
      simp

/-- **The doubling family is structurally emittable.**  The compact numerals of `2 ^ n`
are `n` repetitions of a fixed four-token block followed by `1`, which the repeating-block
emitter produces with a poly-fueled count — even though the *values* `2 ^ n` are
superpolynomial. -/
lemma binNumeralEnc_two_pow_polySegStream :
    PolySegStream (fun n => binNumeralEnc (2 ^ n)) := by
  have hb : PolyTokenStream (fun _ : ℕ => [8, 7, 6, 6]) :=
    (PolyTokenStream.const 8).append <| (PolyTokenStream.const 7).append <|
      (PolyTokenStream.const 6).append (PolyTokenStream.const 6)
  have hblocks := PolySegStream.blocks hb 4 (fun _ => rfl) (by omega) PolyFueled.id
  refine (hblocks.append
    (PolySegStream.ofTokenStream (PolyTokenStream.const 6))).of_eq fun n => ?_
  rw [binNumeralEnc_two_pow, flatMap_range_const]

/-- **The compact numeral names its value.**  In every model of `𝗣𝗔⁻` the Horner term
`binNumeral v` evaluates to `v`, so it is interchangeable with Foundation's unary numeral
wherever only the value matters. -/
lemma binNumeral_val {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] :
    ∀ v : ℕ, (binNumeral v).val (![] : Fin 0 → M) = (v : M) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    match v with
    | 0 => rw [binNumeral]; simp
    | 1 => rw [binNumeral]; simp
    | (w + 2) =>
        have hlt : (w + 2) / 2 < w + 2 := Nat.div_lt_self (by omega) (by omega)
        have hrec := ih _ hlt
        have hd : (w + 2) / 2 = w / 2 + 1 := by omega
        rw [hd] at hrec
        rw [binNumeral]
        split <;> rename_i hpar <;>
          simp [Semiterm.Operator.val_comp, Matrix.fun_eq_vec_two, hrec]
        · have hcast : (w : M) = 2 * ((w / 2 : ℕ) : M) := by
            have hw : w = 2 * (w / 2) := by omega
            calc (w : M) = ((2 * (w / 2) : ℕ) : M) := by rw [← hw]
              _ = 2 * ((w / 2 : ℕ) : M) := by push_cast; ring
          rw [hcast]; ring
        · have hcast : (w : M) = 2 * ((w / 2 : ℕ) : M) + 1 := by
            have hw : w = 2 * (w / 2) + 1 := by omega
            calc (w : M) = ((2 * (w / 2) + 1 : ℕ) : M) := by rw [← hw]
              _ = 2 * ((w / 2 : ℕ) : M) + 1 := by push_cast; ring
          rw [hcast]; ring

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

`structural` meters the defining formula's symbol list — one token per node of the
Foundation formula.  On the paper's `¬/∧/∨/⟹/∀/∃`, and on numerals named compactly in `ℒₒᵣ`,
that equals the paper's own symbol count under `def:ec`; on `⟺` it does not, because the NNF
substrate has no biconditional constructor and duplicates both sides at every nesting level
(`dd:nnf`, witnessed by `iffChain_not_polyArithmeticFormulaSeq`).  Large values are reached
by *naming* them compactly: the class is inhabited both by `unitFracPaperLUVSeq` at `1/(n+1)`
and by `dyadicPaperLUVSeq` at `2⁻ⁿ`, whose denominator `2 ^ n` is named in `O(n)` symbols by
`binNumeral`; the same `2⁻ⁿ` spelled with Foundation's *unary* numeral has no certificate
(`unaryRendering_two_pow_not_polyArithmeticFormulaSeq`), which is an artifact of that numeral
rather than a restriction the paper imposes.  `PaperLUV` itself carries no such field; only
the sequence wrapper does, and this wrapper is the route from a literal first-order paper LUV
into `LUV.RpnThresholdCodeSeq`, with `PaperLUV.rpnThresholdCodes` its single-LUV corollary.
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

/-- **The single-LUV route.**  A *single* literal paper LUV carries the non-sequence
threshold-code certificate `LUV.RpnThresholdCodes`, which is what the whole-LUV endpoints
take as a hypothesis (`LUV.expect_converges`, `thm:ec`).  It is the constant family
(`PaperLUVSeq.const`) reindexed along the poly-fueled map `m ↦ ⟨0, m⟩`, which turns the
sequence's `⟨n, ⟨k, i⟩⟩` convention into the single-LUV `⟨k, i⟩` one.  No efficiency
hypothesis is needed: a constant formula family is trivially symbol-metered, so this holds of
*every* `PaperLUV`.  Kind `C`; hypotheses `(a)`.
Paper node: `def:ec` -/
lemma PaperLUV.rpnThresholdCodes (X : PaperLUV T) : X.toLUV.RpnThresholdCodes := by
  have h : RpnSentenceCodes (fun m => (((PaperLUVSeq.const X).luv m.unpair.1).toLUV).gt
      ((m.unpair.2.unpair.2 : ℚ) / (m.unpair.2.unpair.1 : ℚ))) :=
    (PaperLUVSeq.const X).rpnThresholdCodeSeq
  have hf : PolyFueled _ (fun m : ℕ => Nat.pair 0 m) :=
    (PolyFueled.const 0).pair PolyFueled.id
  show RpnSentenceCodes _
  exact (h.comp hf).of_eq fun m => by simp [PaperLUVSeq.const]

/-! ### Concrete families

The interface is inhabited by genuinely varying families.  Both are reciprocals `1/v` of a
denominator named by a single closed term, so one template and one pair of model arguments
serve them: `invFormula` is the template and `invPaperLUV` discharges uniqueness and
unit-interval membership from the denominator term's *value* alone, in any theory extending
`𝗜𝚺₁`, by completeness over its models.  The two instances differ only in how that value is
named — `unitFracPaperLUVSeq` has value `1/(n+1)` with a unary numeral, `dyadicPaperLUVSeq`
has value `2⁻ⁿ` with the compact numeral of `2 ^ n`. -/

/-- The reciprocal template: the pair code of `1 / d`, with the denominator named once by
the closed term `d`. -/
def invFormula (d : Semiterm.Const ℒₒᵣ) : ArithmeticSemisentence 1 :=
  “q. ∃ b, !!d = b ∧ !pairDef q 1 b”

/-- **The reciprocal paper LUV.**  A closed `ℒₒᵣ` term of positive standard value `v` names
the literal paper LUV of value `1/v`; uniqueness and unit-interval membership are derived in
`T` by completeness from the term's value and nothing else.  That is what makes the *naming*
of the denominator — unary numeral or compact term — a free choice at this layer.
Kind `C`; hypotheses `(a)`.
Paper node: `def:luv` -/
def invPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (d : Semiterm.Const ℒₒᵣ) (v : ℕ) (hv : 0 < v)
    (hval : ∀ (M : Type) [ORingStructure M] [_i : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻],
      Semiterm.Operator.val (M := M) ![] d = (v : M)) :
    PaperLUV T where
  formula := invFormula d
  unique := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, invFormula, pairDef, hval M]
    rcases Nat.lt_or_ge 1 v with h1 | h1
    · simp [h1, Nat.not_le.mpr h1]
    · simp [Nat.not_lt.mpr h1, h1]
  unit := by
    apply LO.FirstOrder.Arithmetic.complete T
    intro (M : Type) _ hM
    letI : 𝗜𝗢𝗽𝗲𝗻 ⪯ T :=
      Entailment.WeakerThan.trans (𝓣 := 𝗜𝚺₁) inferInstance inferInstance
    haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
      ModelsTheory.of_provably_subtheory M 𝗜𝗢𝗽𝗲𝗻 T inferInstance
    simp [models_iff, invFormula, pairDef, paperRatUnitDef, hval M]
    have hv1 : 1 ≤ v := hv
    intro x hx
    refine ⟨1, (v : M), ?_, ?_, ?_⟩
    · rcases hx with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · exact Or.inl ⟨by exact_mod_cast h1, rfl⟩
      · have hv2 : v = 1 := by omega
        subst hv2
        exact Or.inr ⟨by simp, by push_cast; ring⟩
    · exact_mod_cast hv
    · exact_mod_cast hv1

/-- The value `1/(n+1)`: the code of that fraction, with the denominator named once by the
unary numeral `n + 1`. -/
def unitFracFormula (n : ℕ) : ArithmeticSemisentence 1 :=
  invFormula (Semiterm.Operator.numeral ℒₒᵣ (n + 1))

/-- The value `2⁻ⁿ`: the same code, with the denominator named once by the *compact*
numeral of `2 ^ n`.  The value is superpolynomially small; the name is `O(n)` symbols. -/
def dyadicFormula (n : ℕ) : ArithmeticSemisentence 1 :=
  invFormula (binNumeral (2 ^ n))

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

/-- The compact-numeral encoding in the same normal form. -/
private lemma binNumeral_norm (k v : ℕ) :
    encodeArithmeticTermSymbols
      (((Rew.subst ![]) (Rew.emb (binNumeral v).term)) : ArithmeticSemiterm ℕ k) =
      binNumeralEnc v := by
  have h := encodeArithmeticTermSymbols_binNumeral (k := k) v
  simpa [Semiterm.Operator.const, Semiterm.Operator.operator] using h

/-- The reciprocal template is a fixed frame around the denominator's own symbols: with a
unary numeral the frame encloses that numeral's `2 * v - 1` symbols. -/
private lemma enc_invFormula_numeral (v : ℕ) (hv : v ≠ 0) :
    encodeArithmeticFormulaSymbols
      ((invFormula (Semiterm.Operator.numeral ℒₒᵣ v) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ (List.replicate (v - 1) 7 ++ List.replicate v 6) ++
        unitFracPost := by
  rw [invFormula]
  simp [pairDef, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, unitFracPost,
    Semiformula.Operator.lt_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.le_def, Semiterm.Operator.operator,
    Semiterm.Operator.const, oringMul_term, oringAdd_term,
    oringNumOne_term, Matrix.fun_eq_vec_two,
    emb_subst_nil_comm, encNumeral_norm _ v hv]

/-- The same frame around the compact numeral's symbols. -/
private lemma enc_invFormula_binNumeral (v : ℕ) :
    encodeArithmeticFormulaSymbols
      ((invFormula (binNumeral v) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ binNumeralEnc v ++ unitFracPost := by
  rw [invFormula]
  simp [pairDef, encodeArithmeticFormulaSymbols, encodeArithmeticTermSymbols,
    encodeStructuredNat, unitFracPost,
    Semiformula.Operator.lt_def, Semiformula.Operator.eq_def,
    Semiformula.Operator.le_def, Semiterm.Operator.operator,
    Semiterm.Operator.const, oringMul_term, oringAdd_term,
    oringNumOne_term, Matrix.fun_eq_vec_two,
    emb_subst_nil_comm, binNumeral_norm _ v]

private lemma enc_unitFracFormula (n : ℕ) :
    encodeArithmeticFormulaSymbols
      ((unitFracFormula n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ (List.replicate n 7 ++ List.replicate (n + 1) 6) ++
        unitFracPost := by
  rw [unitFracFormula]
  simpa using enc_invFormula_numeral (n + 1) (by omega)

private lemma enc_dyadicFormula (n : ℕ) :
    encodeArithmeticFormulaSymbols
      ((dyadicFormula n : ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1) =
      [18, 15, 11] ++ binNumeralEnc (2 ^ n) ++ unitFracPost :=
  enc_invFormula_binNumeral (2 ^ n)

/-- The literal paper LUV of value `1/(n+1)`. -/
def unitFracPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (n : ℕ) :
    PaperLUV T :=
  invPaperLUV T (Semiterm.Operator.numeral ℒₒᵣ (n + 1)) (n + 1) (by omega)
    (fun M _ _ => by simp [numeral_eq_natCast])

/-- The literal paper LUV of value `2⁻ⁿ`. -/
def dyadicPaperLUV (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (n : ℕ) :
    PaperLUV T :=
  invPaperLUV T (binNumeral (2 ^ n)) (2 ^ n) (by positivity)
    (fun M _ _ => binNumeral_val (M := M) (2 ^ n))

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
`structural` field is an extra hypothesis `PaperLUV` does not carry.  It is the paper's own
`def:ec` condition on the defining formula — polynomially many `ℒₒᵣ` symbols written out —
and it is inhabited at both ends of the range the paper uses, by
`unitFracPaperLUVSeq_frontend` at `1/(n+1)` and `dyadicPaperLUVSeq_frontend` at `2⁻ⁿ`.
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

/-- The defining formulas of the `2⁻ⁿ` family are structurally emittable: the compact
numeral of `2 ^ n` is `n` copies of the doubling block, so the whole formula is a fixed
frame around a poly-fueled repeating run. -/
lemma dyadic_polyArithmeticFormulaSeq :
    PolyArithmeticFormulaSeq (fun n =>
      ((dyadicFormula n : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)) := by
  refine ((PolySegStream.constList [18, 15, 11]).append
    (binNumeralEnc_two_pow_polySegStream.append
      (PolySegStream.constList unitFracPost))).of_eq fun n => ?_
  rw [enc_dyadicFormula n]
  simp

/-- **Non-vacuity** (`N+`) at a superpolynomially small value: the family of literal paper
LUVs of value `2⁻ⁿ` carries the structural certificate.  This is the value the paper writes
as `X > 2⁻ⁿ`; it is admissible here because the class meters the *formula string*, and the
compact numeral names `2 ^ n` in `O(n)` symbols.  Kind `N+`; hypotheses `(a)`.
Paper node: `def:luv` -/
def dyadicPaperLUVSeq (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : PaperLUVSeq T where
  luv n := dyadicPaperLUV T n
  structural := dyadic_polyArithmeticFormulaSeq

/-- **The frontend at `2⁻ⁿ`**: the literal paper LUVs of value `2⁻ⁿ` are valued on every
completed world of the canonical theorem process and efficiently thresholded.  Together with
`unitFracPaperLUVSeq_frontend` this shows the class is not confined to values of polynomial
denominator.
Paper node: `def:luv` -/
lemma dyadicPaperLUVSeq_frontend [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    (∀ n, ∀ v : PCWorld, v.ConsistentWithTheory (paperTheoryDP T) →
        ∃ x : ℝ, v.ValuesAt ((dyadicPaperLUVSeq T).luv n).toLUV x) ∧
      LUV.RpnThresholdCodeSeq (fun n => ((dyadicPaperLUVSeq T).luv n).toLUV) :=
  (dyadicPaperLUVSeq T).source_valued_and_rpnThresholdCodeSeq

/-- **A Foundation numeral artifact, not a narrowing of the class.**  The *same* value `2⁻ⁿ`
has an admissible rendering — `dyadicPaperLUVSeq`, whose denominator is the compact numeral
`binNumeral (2 ^ n)` — and an inadmissible one: spell the denominator with Foundation's
*unary* `Semiterm.Operator.numeral` and the formula string itself is `2 ^ n` symbols long,
which no polynomial bounds.

The unary cost is an artifact of Foundation's default numeral, **not** a property of the
paper: the paper fixes no numeral notation and writes numerals positionally (tex:614,
tex:757).  What matters for faithfulness is that the *value* is nameable compactly inside
`ℒₒᵣ` — `binNumeral v` has `O(log v)` nodes — so on numerals this class is not narrower than
`def:ec`, and this lemma documents that artifact rather than a gap.  (The one genuine gap is
`⟺`; see `iffChain_not_polyArithmeticFormulaSeq` and `dd:nnf`.)  Kind `P`; hypotheses `(a)`.
Paper node: `def:ec` -/
lemma unaryRendering_two_pow_not_polyArithmeticFormulaSeq :
    ¬ PolyArithmeticFormulaSeq (fun n =>
      ((invFormula (Semiterm.Operator.numeral ℒₒᵣ (2 ^ n)) :
        ArithmeticSemisentence 1) : ArithmeticSemiformula ℕ 1)) := by
  rintro ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩
  obtain ⟨b, hrun, hpb, hbb⟩ := hl
  refine not_isPolyBounded_two_pow (hpb.of_le fun n => ?_)
  have h : (encodeArithmeticFormulaSymbols
      ((invFormula (Semiterm.Operator.numeral ℒₒᵣ (2 ^ n)) : ArithmeticSemisentence 1) :
        ArithmeticSemiformula ℕ 1)).length = lenFn n := hlen n
  rw [enc_invFormula_numeral (2 ^ n) (by positivity)] at h
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil, unitFracPost] at h
  omega

/-! ### The `⟺` gap (`dd:nnf`)

The metering above is one token per node of the *Foundation* formula, and Foundation's
`Semiformula` is a negation-normal-form datatype: `verum/falsum/rel/nrel/and/or/all/exs`.
There is no biconditional constructor, so `a 🡘 b` is notation for `(a 🡒 b) ⋏ (b 🡒 a)` and
**duplicates both sides**.  The paper's language has `⟺` as a primitive connective (tex:560),
so the paper's `def:ec` writer emits a left-nested `⟺` chain in `O(n)` characters while the
same object costs `≥ 2 ^ n` nodes here.  The class is therefore *not* coextensive with
`def:ec`: strictly finer, on `⟺` alone.  This is the object-language substrate substitution
`dd:nnf`, disclosed once and globally rather than charged per row; the identified (and not
taken) repair is a compact formula *source* language with `iff`/`imp`/`neg` primitives,
decoded into NNF for semantics, on the `Code.sourceNat` pattern. -/

/-- The biconditional shell in symbol form.  Unlike `🡒`, which is a linear token map on its
antecedent (`encodeArithmeticFormulaSymbols_imp`), `🡘` charges **both** sides **twice**. -/
lemma encodeArithmeticFormulaSymbols_iff {k : ℕ} (a b : ArithmeticSemiformula ℕ k) :
    (encodeArithmeticFormulaSymbols (a 🡘 b)).length =
      3 + 2 * (encodeArithmeticFormulaSymbols a).length
        + 2 * (encodeArithmeticFormulaSymbols b).length := by
  show (encodeArithmeticFormulaSymbols ((a 🡒 b) ⋏ (b 🡒 a))).length = _
  rw [show ((a 🡒 b) ⋏ (b 🡒 a)) = Semiformula.and (a 🡒 b) (b 🡒 a) from rfl,
    encodeArithmeticFormulaSymbols, encodeArithmeticFormulaSymbols_imp,
    encodeArithmeticFormulaSymbols_imp]
  simp
  omega

/-- The atom the biconditional chain is built from: `x₀ = 0`. -/
def iffChainAtom : ArithmeticSemiformula ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .func Language.ORing.Func.zero ![]]

/-- The left-nested biconditional chain `(⋯((A ⟺ A) ⟺ A) ⋯ ⟺ A)`, `n` levels deep, over the
fixed atom `A = iffChainAtom`.  In the paper's own language — where `⟺` is a primitive
connective (tex:560) — writing this out is `O(n)` characters, so it is exactly the kind of
family `def:ec` (tex:753) asks a polynomial-time writer to produce. -/
def iffChain : ℕ → ArithmeticSemiformula ℕ 1
  | 0 => iffChainAtom
  | n + 1 => iffChain n 🡘 iffChainAtom

/-- Each `⟺` level at least doubles the NNF node count, so the chain is exponential. -/
lemma two_pow_le_encode_iffChain :
    ∀ n, 2 ^ n ≤ (encodeArithmeticFormulaSymbols (iffChain n)).length
  | 0 => by
      have hne : encodeArithmeticFormulaSymbols (iffChain 0) ≠ [] := by
        rw [iffChain, iffChainAtom]
        simp [encodeArithmeticFormulaSymbols]
      have h1 := List.length_pos_of_ne_nil hne
      simp only [pow_zero]
      omega
  | n + 1 => by
      have ih := two_pow_le_encode_iffChain n
      rw [iffChain, encodeArithmeticFormulaSymbols_iff]
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega

/-- **The `⟺` gap, witnessed** (`dd:nnf`).  `iffChain` is `def:ec`-writable in the paper's
language — `O(n)` characters, `⟺` being one of the paper's primitive connectives (tex:560) —
and yet has **no** certificate in this class, because the NNF substrate expands each `⟺` into
a conjunction of two implications and so doubles per nesting level.

This is the honest strictness statement for `def:ec`'s rendering here: the symbol-metered
class is *not* coextensive with the paper's efficiency condition on formulas.  It is finer on
`⟺` and only on `⟺` — `¬`, `∧`, `∨`, `⟹`, `∀`, `∃` and compactly named numerals all cost
what the paper's writer pays.  The gap is disclosed globally as `dd:nnf`, on the footing of
`dd:fuel`, and is not charged to any individual row; the repair — a compact formula source
language with `iff`/`imp`/`neg` primitives decoded into NNF for semantics, the
`Code.sourceNat` pattern — is identified and not done.  Kind `P`; hypotheses `(a)`.
Paper node: `def:ec` -/
lemma iffChain_not_polyArithmeticFormulaSeq :
    ¬ PolyArithmeticFormulaSeq iffChain := by
  rintro ⟨ct, cl, tokenFn, lenFn, ht, hl, hlen, hget⟩
  obtain ⟨b, hrun, hpb, hbb⟩ := hl
  exact not_isPolyBounded_two_pow (hpb.of_le fun n => by
    rw [← hlen n]; exact two_pow_le_encode_iffChain n)

/-- A client consuming the witness: the expectation-of-indicators endpoint (`thm:ei`) takes
the threshold-code class as a hypothesis, and the `2⁻ⁿ` family discharges it outright. -/
example (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP] [𝗜𝚺₁ ⪯ T]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hY : ∀ n, (((dyadicPaperLUVSeq T).luv n).toLUV).IsIndicator (φ n) DP) :
    AsympEq (fun n => (((dyadicPaperLUVSeq T).luv n).toLUV).expect P n)
      (fun n => P n (φ n)) :=
  lic_expectation_indicator P DP φ hφ _ (dyadicPaperLUVSeq T).rpnThresholdCodeSeq
    hcons hY

/-- A client of the single-LUV route: `thm:ec` applied at a *literal* paper LUV, the
`2⁻ⁿ`-valued one, with both representation hypotheses discharged from the frontend —
the threshold-code class by `PaperLUV.rpnThresholdCodes` and the world value by
`PaperLUV.source_valued`.  Only the paper's own consistency premise remains. -/
example (P : History) [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    [IsLogicalInductor P (paperTheoryDP T)] (n : ℕ)
    (hcons : ∀ k, ∃ v : PCWorld, v.ConsistentWith ((paperTheoryDP T).D k)) :
    ∃ L : ℝ, ConvergesTo ((dyadicPaperLUV T n).toLUV.expectSeq P) L :=
  LUV.expect_converges P (paperTheoryDP T) _ (dyadicPaperLUV T n).rpnThresholdCodes
    hcons (PaperLUV.source_valued _)

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

#print axioms invPaperLUV
#print axioms unitFracPaperLUVSeq
#print axioms unitFracPaperLUVSeq_frontend
#print axioms dyadicPaperLUVSeq
#print axioms dyadicPaperLUVSeq_frontend
#print axioms unaryRendering_two_pow_not_polyArithmeticFormulaSeq
#print axioms iffChain_not_polyArithmeticFormulaSeq
#print axioms PaperLUV.rpnThresholdCodes
#print axioms binNumeral_val
#print axioms binNumeralEnc_length_le
#print axioms PaperLUVSeq.rpnThresholdCodeSeq
#print axioms PaperLUVSeq.source_valued_and_rpnThresholdCodeSeq

#print axioms parseArithmeticTermSymbols_encode
#print axioms parseArithmeticFormulaSymbols_encode
#print axioms parseRpn_structuredPaperPrimeBlock
#print axioms parseRpn_structuredPaperDecomposeBlock_exact
#print axioms parseRpn_encodePaperThreshold
#print axioms structuredPaperPrime_rpnSentenceCodes

end LogicalInduction
