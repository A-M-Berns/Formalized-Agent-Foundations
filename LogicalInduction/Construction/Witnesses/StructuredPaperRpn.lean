import LogicalInduction.Construction.Witnesses.PaperFirstOrder
import LogicalInduction.Construction.Witnesses.RpnConditioning
import LogicalInduction.Framework.RpnEmission

/-!
# Structured first-order RPN kill test

This module records the Checkpoint 3 obstruction without changing the established RPN
ABI. A counted structured block is cheap to emit and can contract to the exact existing
tag-`7` sentence. However, the conditioning automaton treats every escape as exactly two
tokens, so globally installing this block would invalidate its run/parse invariant.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Propositional

def structuredFOTestBody : ℕ → ArithmeticSemiproposition 1
  | 0 => ⊤
  | n + 1 => .and (structuredFOTestBody n) ⊤

def structuredFOTestFormula (n : ℕ) : ArithmeticProposition :=
  .exs (structuredFOTestBody n)

def structuredFOTestBodySymbols : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => structuredFOTestBodySymbols n ++ [0, 1]

def structuredFOTestSymbols (n : ℕ) : List ℕ :=
  structuredFOTestBodySymbols n ++ [2]

private def structuredFOTestTopCode : ℕ := Nat.pair 2 0 + 1
private def structuredFOTestAndCode (left right : ℕ) : ℕ :=
  Nat.pair 4 (Nat.pair left right) + 1
private def structuredFOTestExsCode (body : ℕ) : ℕ := Nat.pair 7 body + 1

private def structuredFOTestStep (state : Option (List ℕ)) (symbol : ℕ) :
    Option (List ℕ) :=
  state.bind fun stack =>
    if symbol = 0 then some (structuredFOTestTopCode :: stack)
    else if symbol = 1 then
      match stack with
      | right :: left :: tail => some (structuredFOTestAndCode left right :: tail)
      | _ => none
    else if symbol = 2 then
      match stack with
      | body :: tail => some (structuredFOTestExsCode body :: tail)
      | _ => none
    else none

private def structuredFOTestCode (symbols : List ℕ) : Option ℕ :=
  match symbols.foldl structuredFOTestStep (some []) with
  | some [formulaCode] => some formulaCode
  | _ => none

/-- Experimental counted format proposed for the kill test. It is not installed in
`parseRpn`: `[escape, marker, polarity, count, symbols...]`. -/
def structuredFOTestBlock (n : ℕ) : List ℕ :=
  [1, 0, Encodable.encode true, (structuredFOTestSymbols n).length] ++
    structuredFOTestSymbols n

private def parseStructuredFOTestBlock (tokens : List ℕ) :
    Option (Sentence × List ℕ) :=
  match tokens with
  | 1 :: 0 :: polarityCode :: symbolCount :: payload =>
      if symbolCount ≤ payload.length then
        (Encodable.decode (α := Bool) polarityCode).bind fun positive =>
          (structuredFOTestCode (payload.take symbolCount)).map fun formulaCode =>
            (Formula.atom (Nat.pair paperPrimeTag
              (Nat.pair (Encodable.encode positive) formulaCode)),
              payload.drop symbolCount)
      else none
  | _ => none

private lemma structuredFOTestBody_fold (n : ℕ) (stack : List ℕ) :
    (structuredFOTestBodySymbols n).foldl structuredFOTestStep (some stack) =
      some (Encodable.encode (structuredFOTestBody n) :: stack) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [structuredFOTestBodySymbols, List.foldl_append, ih]
      rfl

lemma structuredFOTestSymbols_length (n : ℕ) :
    (structuredFOTestSymbols n).length = 2 * n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [structuredFOTestSymbols, structuredFOTestBodySymbols] at ih ⊢
      omega

private lemma structuredFOTest_code (n : ℕ) :
    structuredFOTestCode (structuredFOTestSymbols n) =
      some (Encodable.encode (structuredFOTestFormula n)) := by
  rw [structuredFOTestSymbols, structuredFOTestCode, List.foldl_append,
    structuredFOTestBody_fold]
  simp [structuredFOTestStep, structuredFOTestExsCode, structuredFOTestFormula,
    LO.FirstOrder.Semiformula.encode_eq_toNat, LO.FirstOrder.Semiformula.toNat]

/-- Positive half of the experiment: the counted block contracts exactly to the existing
tag-`7` paper-prime sentence, not to an alias. -/
lemma parseStructuredFOTestBlock_exact (n : ℕ) :
    parseStructuredFOTestBlock (structuredFOTestBlock n) =
      some (paperPrimeSentence true (structuredFOTestFormula n), []) := by
  simp [parseStructuredFOTestBlock, structuredFOTestBlock, structuredFOTest_code,
    paperPrimeSentence, paperPrimeCode]

lemma structuredFOTestBlock_length (n : ℕ) :
    (structuredFOTestBlock n).length = 2 * n + 6 := by
  simp [structuredFOTestBlock, structuredFOTestSymbols_length]

/-- Positive emission half: the experimental blocks themselves have a polynomial symbol
stream. This deliberately does not claim `RpnSentenceCodes`, whose public parser rejects
the marker. -/
lemma structuredFOTestBlock_polySegStream : PolySegStream structuredFOTestBlock := by
  obtain ⟨cmul, hmul⟩ := mulc_polyFueled 2
  obtain ⟨ccount, hcount⟩ := hmul.addConst 2
  have hcount' : PolyFueled ccount (fun n => (structuredFOTestSymbols n).length) :=
    hcount.of_eq fun n => by rw [structuredFOTestSymbols_length, Nat.mul_comm]
  have hheader : PolySegStream (fun n =>
      [1, 0, Encodable.encode true, (structuredFOTestSymbols n).length]) :=
    PolySegStream.ofTokenStream
      (((PolyTokenStream.const 1).append (PolyTokenStream.const 0)).append
        ((PolyTokenStream.const (Encodable.encode true)).append
          (PolyTokenStream.polyTok hcount')))
  have hpair : PolyTokenStream (fun _ : ℕ => [0, 1]) :=
    (PolyTokenStream.const 0).append (PolyTokenStream.const 1)
  have hpairs : PolySegStream (fun n =>
      (List.range n).flatMap fun _ => [0, 1]) :=
    PolySegStream.blocks hpair 2 (fun _ => rfl) (by omega) PolyFueled.id
  have hbody : PolySegStream structuredFOTestBodySymbols := by
    refine ((PolySegStream.ofTokenStream (PolyTokenStream.const 0)).append hpairs).of_eq ?_
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [structuredFOTestBodySymbols, List.range_succ, List.flatMap_append]
        change ([0] ++ (List.range n).flatMap (fun _ => [0, 1])) ++ [0, 1] = _
        rw [ih]
  have hsymbols : PolySegStream structuredFOTestSymbols :=
    (hbody.append (PolySegStream.ofTokenStream (PolyTokenStream.const 2))).of_eq
      (fun _ => rfl)
  exact (hheader.append hsymbols).of_eq fun _ => rfl

/-- The established parser rejects the proposed marker at the old invalid escape payload
`0`; consequently the positive stream above cannot yet instantiate `RpnSentenceCodes`. -/
lemma parseRpn_structuredFOTestBlock_none (n : ℕ) :
    parseRpn (structuredFOTestBlock n).length (structuredFOTestBlock n) = none := by
  rw [structuredFOTestBlock]
  simp [parseRpn, decode_zero_sentence]

/-- Precise downstream obstruction: the conditioning run automaton exits an escape after
the marker token, before polarity, count, or any FOL symbol. A global parser extension for
the counted block would therefore falsify its run/parse correspondence theorem. -/
lemma structuredFOTest_conditioning_exits_after_marker (n : ℕ) :
    (structuredFOTestBlock n).take 2 = [1, 0] ∧
    [1, 0].foldl RpnConditioning.rpnCondStep
        (RpnConditioning.rcPack 1 1 0) = RpnConditioning.rcPack 2 0 2 := by
  constructor
  · simp [structuredFOTestBlock]
  · simp [RpnConditioning.rpnCondStep]

#print axioms parseStructuredFOTestBlock_exact
#print axioms structuredFOTestBlock_polySegStream
#print axioms parseRpn_structuredFOTestBlock_none
#print axioms structuredFOTest_conditioning_exits_after_marker

end LogicalInduction
