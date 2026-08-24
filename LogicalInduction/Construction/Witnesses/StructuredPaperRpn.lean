import LogicalInduction.Construction.Witnesses.PaperLUV
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnSplice

/-!
# Structured Foundation-arithmetic RPN codec

The public leaf framing is
`[1, 0, polarity] ++ replicate payload.length 1 ++ [0] ++ payload`.
The formerly invalid sentence code `0` makes the prefix backwards compatible. Unary
payload length keeps every framing token bounded; the payload is a prefix tree using the
shared `structuredArithmeticArity`. Foundation Godel codes are built only by contraction.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Propositional

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

def parseArithmeticTermSymbols (k : ℕ) (symbols : List ℕ) :
    Option (ArithmeticSemiterm ℕ k × List ℕ) :=
  (parseStructuredArithmeticTerm symbols.length k symbols).bind fun p =>
    (Encodable.decode (α := ArithmeticSemiterm ℕ k) p.1).map fun t => (t, p.2)

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

def structuredPaperPrimeBlock (positive : Bool) (φ : ArithmeticProposition) : List ℕ :=
  let payload := encodeArithmeticFormulaSymbols φ
  [1, 0, Encodable.encode positive] ++
    (List.replicate payload.length 1 ++ (0 :: payload ++ [19]))

lemma readStructuredLength_replicate (n : ℕ) (tail : List ℕ) :
    readStructuredLength (List.replicate n 1 ++ 0 :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append,
      readStructuredLength, ih, Option.map_some]

lemma parseStructuredPaperPrime_encode (positive : Bool) (φ : ArithmeticProposition)
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

lemma structuredPaperPrimeBlock_length_pos (positive : Bool) (φ : ArithmeticProposition) :
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
never occurs in the emitter's output range. -/

def PolyArithmeticFormulaSeq (φ : ℕ → ArithmeticProposition) : Prop :=
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

#print axioms parseArithmeticTermSymbols_encode
#print axioms parseArithmeticFormulaSymbols_encode
#print axioms parseRpn_structuredPaperPrimeBlock
#print axioms parseRpn_structuredPaperDecomposeBlock_exact
#print axioms parseRpn_encodePaperThreshold
#print axioms structuredPaperPrime_rpnSentenceCodes

end LogicalInduction
