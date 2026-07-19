/-
# Executable compiler for closure under conditioning

This file constructs the rational conditional-market program used by `thm:scon` from an
actual base-market computation and the polynomial condition-code program.  The finite
denominator patch and the flat token transducer are developed below this core computation.
-/
import LogicalInduction.Construction.ConditioningPresentation
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.M7Witnesses

namespace LogicalInduction

namespace ConditioningCompile

-- Deep polynomial token compositions carry nested `Primcodable` products.  Keep the
-- implementation of pairing opaque during elaboration (the standard `dd:fuel` safeguard).
attribute [local irreducible] Nat.sqrt

/-- Exact rational counterpart of the paper's capped conditional quote. -/
def conditionalRat (numerator denominator : ℚ) : ℚ :=
  if numerator < denominator then numerator / denominator else 1

/-- Raw code of `φ ⋏ ψ` from the canonical codes of `φ` and `ψ`. -/
def conjunctionCode (phiCode psiCode : ℕ) : ℕ :=
  Nat.pair 3 (Nat.pair phiCode psiCode) + 1

theorem conjunctionCode_exact (φ ψ : Sentence) :
    conjunctionCode (Encodable.encode φ) (Encodable.encode ψ) =
      Encodable.encode (φ ⋏ ψ) := by
  rfl

theorem conjunctionCode_decode {phiCode : ℕ} {φ ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) phiCode = some φ) :
    Encodable.decode (α := Sentence)
      (conjunctionCode phiCode (Encodable.encode ψ)) = some (φ ⋏ ψ) := by
  change LO.Propositional.Formula.ofNat phiCode = some φ at hφ
  change LO.Propositional.Formula.ofNat
    (conjunctionCode phiCode (LO.Propositional.Formula.toNat ψ)) = some (φ ⋏ ψ)
  simp [conjunctionCode, LO.Propositional.Formula.ofNat, hφ,
    LO.Propositional.Formula.ofNat_toNat]

theorem conjunctionCode_decode_none {phiCode : ℕ} {ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) phiCode = none) :
    Encodable.decode (α := Sentence)
      (conjunctionCode phiCode (Encodable.encode ψ)) = none := by
  change LO.Propositional.Formula.ofNat phiCode = none at hφ
  change LO.Propositional.Formula.ofNat
    (conjunctionCode phiCode (LO.Propositional.Formula.toNat ψ)) = none
  simp [conjunctionCode, LO.Propositional.Formula.ofNat, hφ,
    LO.Propositional.Formula.ofNat_toNat]

theorem conjunctionCode_prim : Primrec₂ conjunctionCode := by
  exact (Primrec.nat_add.comp₂
    (Primrec₂.natPair.comp₂ (Primrec₂.const 3)
      (Primrec₂.natPair.comp₂ Primrec₂.left Primrec₂.right))
    (Primrec₂.const 1)).of_eq fun _ _ => rfl

/-- One total code implementing the raw conjunction-code constructor. -/
noncomputable def conjunctionCodeCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conjunctionCode_prim)))

theorem conjunctionCodeCode_spec (z : ℕ) :
    conjunctionCode z.unpair.1 z.unpair.2 ∈ conjunctionCodeCode.eval z := by
  have h := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conjunctionCode_prim)))
  rw [conjunctionCodeCode, h]
  exact Part.mem_some _

/-- Decode two rational codes, take the capped conditional ratio, and re-encode it. -/
def conditionalRatNorm (z : ℕ) : ℕ :=
  let numerator := (Encodable.decode (α := ℚ) z.unpair.1).getD 0
  let denominator := (Encodable.decode (α := ℚ) z.unpair.2).getD 0
  Encodable.encode (conditionalRat numerator denominator)

theorem conditionalRatNorm_prim : Primrec conditionalRatNorm := by
  let numerator : ℕ → ℚ := fun z =>
    (Encodable.decode (α := ℚ) z.unpair.1).getD 0
  let denominator : ℕ → ℚ := fun z =>
    (Encodable.decode (α := ℚ) z.unpair.2).getD 0
  have hn : Primrec numerator :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.const 0)
  have hd : Primrec denominator :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)) (Primrec.const 0)
  have hlt : PrimrecPred fun z => numerator z < denominator z :=
    ((ratLE_prim.comp hd hn).not).of_eq fun z => by
      exact not_le
  have hdiv : Primrec fun z => numerator z / denominator z :=
    ratDiv_prim.comp hn hd
  exact (Primrec.encode.comp
    (Primrec.ite hlt hdiv (Primrec.const 1))).of_eq fun z => by
      rfl

theorem conditionalRatNorm_exact (numerator denominator : ℚ) :
    conditionalRatNorm
        (Nat.pair (Encodable.encode numerator) (Encodable.encode denominator)) =
      Encodable.encode (conditionalRat numerator denominator) := by
  simp [conditionalRatNorm]

/-- One total code implementing `conditionalRatNorm`. -/
noncomputable def conditionalRatCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conditionalRatNorm_prim)))

theorem conditionalRatCode_spec (z : ℕ) :
    conditionalRatNorm z ∈ conditionalRatCode.eval z := by
  have h := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conditionalRatNorm_prim)))
  rw [conditionalRatCode, h]
  exact Part.mem_some _

/-- Rational table computed for the conditioned history.  Its values on malformed sentence
codes are deliberately totalized using the same raw conjunction-code operation. -/
def conditionedQuoteTable {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (day code : ℕ) : ℚ :=
  conditionalRat
    (market.quote day (conjunctionCode code (Encodable.encode (ψ day))))
    (market.quote day (Encodable.encode (ψ day)))

theorem conditionedQuoteTable_exact {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (day : ℕ) (φ : Sentence) :
    conditionedHistory P ψ day φ =
      (conditionedQuoteTable market ψ day (Encodable.encode φ) : ℝ) := by
  unfold conditionedHistory
  unfold conditionalQuote
  rw [market.quote_exact day (φ ⋏ ψ day), market.quote_exact day (ψ day)]
  simp only [conditionedQuoteTable, conjunctionCode_exact]
  unfold conditionalRat
  by_cases h : market.quote day (Encodable.encode (φ ⋏ ψ day)) <
      market.quote day (Encodable.encode (ψ day)) <;> simp [h]

/-- The concrete partial-recursive program for the conditioned quote table. -/
noncomputable def conditionedQuoteCode {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) : Nat.Partrec.Code := by
  let ψCode : Nat.Partrec.Code := Classical.choose hψ
  let conditionAt : Nat.Partrec.Code := ψCode.comp Nat.Partrec.Code.left
  let conjunctionInput : Nat.Partrec.Code :=
    Nat.Partrec.Code.left.pair
      (conjunctionCodeCode.comp
        (Nat.Partrec.Code.right.pair conditionAt))
  let denominatorInput : Nat.Partrec.Code :=
    Nat.Partrec.Code.left.pair conditionAt
  exact conditionalRatCode.comp
    ((market.code.comp conjunctionInput).pair (market.code.comp denominatorInput))

theorem conditionedQuoteCode_spec {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) (z : ℕ) :
    Encodable.encode
        (conditionedQuoteTable market ψ z.unpair.1 z.unpair.2) ∈
      (conditionedQuoteCode market ψ hψ).eval z := by
  classical
  have hψPoly : PolyFueled (Classical.choose hψ)
      (fun n => Encodable.encode (ψ n)) :=
    Classical.choose_spec hψ
  obtain ⟨ψFuel, hψRun, _, _⟩ := hψPoly
  have hconditionMem : Encodable.encode (ψ z.unpair.1) ∈
      (Classical.choose hψ).eval z.unpair.1 := by
    apply Nat.Partrec.Code.evaln_sound
    rw [hψRun z.unpair.1]
    simp
  have hcondition : (Classical.choose hψ).eval z.unpair.1 =
      Part.some (Encodable.encode (ψ z.unpair.1)) :=
    Part.eq_some_iff.mpr hconditionMem
  let conjunction := conjunctionCode z.unpair.2
    (Encodable.encode (ψ z.unpair.1))
  have hconjunction : conjunctionCodeCode.eval
      (Nat.pair z.unpair.2 (Encodable.encode (ψ z.unpair.1))) =
        Part.some conjunction := by
    apply Part.eq_some_iff.mpr
    simpa [conjunction] using conjunctionCodeCode_spec
      (Nat.pair z.unpair.2 (Encodable.encode (ψ z.unpair.1)))
  let numerator := market.quote z.unpair.1 conjunction
  let denominator := market.quote z.unpair.1
    (Encodable.encode (ψ z.unpair.1))
  have hnumerator : market.code.eval (Nat.pair z.unpair.1 conjunction) =
      Part.some (Encodable.encode numerator) := by
    apply Part.eq_some_iff.mpr
    simpa [numerator, conjunction] using
      market.code_spec (Nat.pair z.unpair.1 conjunction)
  have hdenominator : market.code.eval
      (Nat.pair z.unpair.1 (Encodable.encode (ψ z.unpair.1))) =
        Part.some (Encodable.encode denominator) := by
    apply Part.eq_some_iff.mpr
    simpa [denominator] using market.code_spec
      (Nat.pair z.unpair.1 (Encodable.encode (ψ z.unpair.1)))
  have hconditional : conditionalRatCode.eval
      (Nat.pair (Encodable.encode numerator) (Encodable.encode denominator)) =
        Part.some (Encodable.encode (conditionalRat numerator denominator)) := by
    apply Part.eq_some_iff.mpr
    simpa [conditionalRatNorm_exact] using
      conditionalRatCode_spec
        (Nat.pair (Encodable.encode numerator) (Encodable.encode denominator))
  simp [conditionedQuoteCode, Nat.Partrec.Code.eval, hcondition, hconjunction,
    hnumerator, hdenominator, hconditional, Seq.seq, conjunction, numerator,
    denominator, conditionedQuoteTable]

/-- The actual conditioned history is a computable rational market whenever the base
market has a named computation and the condition has polynomial (hence recursive) codes. -/
noncomputable def conditionedMarketComputation {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) :
    MarketComputation (conditionedHistory P ψ) where
  quote := conditionedQuoteTable market ψ
  code := conditionedQuoteCode market ψ hψ
  quote_exact := conditionedQuoteTable_exact market ψ
  code_spec := conditionedQuoteCode_spec market ψ hψ

/-! ## The finite denominator patch -/

/-- Replace the condition's quote by one on the finite prefix before `cutoff`.  All other
market cells are unchanged. -/
def denominatorPatchedHistory (P : History) (ψ : ℕ → Sentence)
    (cutoff : ℕ) : History :=
  fun day φ => if day < cutoff ∧ φ = ψ day then 1 else P day φ

theorem denominatorPatchedHistory_tail (P : History) (ψ : ℕ → Sentence)
    (cutoff day : ℕ) (hday : cutoff ≤ day) (φ : Sentence) :
    denominatorPatchedHistory P ψ cutoff day φ = P day φ := by
  simp [denominatorPatchedHistory, Nat.not_lt.mpr hday]

theorem denominatorPatchedHistory_condition_prefix (P : History)
    (ψ : ℕ → Sentence) (cutoff day : ℕ) (hday : day < cutoff) :
    denominatorPatchedHistory P ψ cutoff day (ψ day) = 1 := by
  simp [denominatorPatchedHistory, hday]

theorem denominatorPatchedHistory_mem_Icc (P : History) (ψ : ℕ → Sentence)
    (cutoff : ℕ) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1)
    (day : ℕ) (φ : Sentence) :
    0 ≤ denominatorPatchedHistory P ψ cutoff day φ ∧
      denominatorPatchedHistory P ψ cutoff day φ ≤ 1 := by
  unfold denominatorPatchedHistory
  split
  · norm_num
  · exact hP day φ

theorem denominatorPatchedHistory_floor (P : History) (ψ : ℕ → Sentence)
    (cutoff : ℕ) {ε : ℚ} (hεone : (ε : ℝ) ≤ 1)
    (htail : ∀ day, cutoff ≤ day → (ε : ℝ) ≤ P day (ψ day)) (day : ℕ) :
    (ε : ℝ) ≤ denominatorPatchedHistory P ψ cutoff day (ψ day) := by
  by_cases hday : day < cutoff
  · rw [denominatorPatchedHistory_condition_prefix P ψ cutoff day hday]
    exact hεone
  · rw [denominatorPatchedHistory_tail P ψ cutoff day (Nat.le_of_not_gt hday)]
    exact htail day (Nat.le_of_not_gt hday)

/-- Rational quote table of the finite denominator patch. -/
def denominatorPatchedQuoteTable {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (cutoff day code : ℕ) : ℚ :=
  if day < cutoff ∧ code = Encodable.encode (ψ day) then 1
  else market.quote day code

theorem denominatorPatchedQuoteTable_exact {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence) (cutoff day : ℕ)
    (φ : Sentence) :
    denominatorPatchedHistory P ψ cutoff day φ =
      (denominatorPatchedQuoteTable market ψ cutoff day
        (Encodable.encode φ) : ℝ) := by
  unfold denominatorPatchedHistory denominatorPatchedQuoteTable
  rw [market.quote_exact]
  by_cases hday : day < cutoff <;>
    by_cases hφ : φ = ψ day <;> simp [hday, hφ]

/-- Total raw-code normalizer for the patched table.  Its input is
`⟨⟨day, sentenceCode⟩, ⟨conditionCode, encodedBaseQuote⟩⟩`. -/
def denominatorPatchNorm (cutoff z : ℕ) : ℕ :=
  let input := z.unpair.1
  let output := z.unpair.2
  if input.unpair.1 < cutoff ∧ input.unpair.2 = output.unpair.1 then
    Encodable.encode (1 : ℚ)
  else output.unpair.2

theorem denominatorPatchNorm_prim (cutoff : ℕ) :
    Primrec (denominatorPatchNorm cutoff) := by
  let day : ℕ → ℕ := fun z => z.unpair.1.unpair.1
  let code : ℕ → ℕ := fun z => z.unpair.1.unpair.2
  let condition : ℕ → ℕ := fun z => z.unpair.2.unpair.1
  let baseQuote : ℕ → ℕ := fun z => z.unpair.2.unpair.2
  have hleft : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hright : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hday : Primrec day := Primrec.fst.comp (Primrec.unpair.comp hleft)
  have hcode : Primrec code := Primrec.snd.comp (Primrec.unpair.comp hleft)
  have hcondition : Primrec condition :=
    Primrec.fst.comp (Primrec.unpair.comp hright)
  have hbase : Primrec baseQuote :=
    Primrec.snd.comp (Primrec.unpair.comp hright)
  have hlt : PrimrecPred fun z => day z < cutoff :=
    ((Primrec.nat_le.comp (Primrec.const cutoff) hday).not).of_eq fun z => not_le
  have heq : PrimrecPred fun z => code z = condition z :=
    Primrec.eq.comp hcode hcondition
  exact (Primrec.ite (hlt.and heq)
    (Primrec.const (Encodable.encode (1 : ℚ))) hbase).of_eq fun z => by
      rfl

noncomputable def denominatorPatchNormCode (cutoff : ℕ) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec
      (Primrec.nat_iff.mp (denominatorPatchNorm_prim cutoff))))

theorem denominatorPatchNormCode_spec (cutoff z : ℕ) :
    denominatorPatchNorm cutoff z ∈ (denominatorPatchNormCode cutoff).eval z := by
  have h := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec
      (Primrec.nat_iff.mp (denominatorPatchNorm_prim cutoff))))
  rw [denominatorPatchNormCode, h]
  exact Part.mem_some _

/-- Partial-recursive program for the finitely patched base market. -/
noncomputable def denominatorPatchedQuoteCode {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence)
    (hψ : PolySentenceCodes ψ) (cutoff : ℕ) : Nat.Partrec.Code :=
  let conditionAt := (Classical.choose hψ).comp Nat.Partrec.Code.left
  denominatorPatchNormCode cutoff |>.comp
    ((Nat.Partrec.Code.left.pair Nat.Partrec.Code.right).pair
      (conditionAt.pair market.code))

theorem denominatorPatchedQuoteCode_spec {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence)
    (hψ : PolySentenceCodes ψ) (cutoff z : ℕ) :
    Encodable.encode (denominatorPatchedQuoteTable market ψ cutoff
      z.unpair.1 z.unpair.2) ∈
      (denominatorPatchedQuoteCode market ψ hψ cutoff).eval z := by
  classical
  have hψPoly : PolyFueled (Classical.choose hψ)
      (fun n => Encodable.encode (ψ n)) := Classical.choose_spec hψ
  obtain ⟨ψFuel, hψRun, _, _⟩ := hψPoly
  have hconditionMem : Encodable.encode (ψ z.unpair.1) ∈
      (Classical.choose hψ).eval z.unpair.1 := by
    apply Nat.Partrec.Code.evaln_sound
    rw [hψRun z.unpair.1]
    simp
  have hcondition : (Classical.choose hψ).eval z.unpair.1 =
      Part.some (Encodable.encode (ψ z.unpair.1)) :=
    Part.eq_some_iff.mpr hconditionMem
  let baseQuote := market.quote z.unpair.1 z.unpair.2
  have hbase : market.code.eval z = Part.some (Encodable.encode baseQuote) := by
    apply Part.eq_some_iff.mpr
    simpa [baseQuote] using market.code_spec z
  let normInput := Nat.pair z
    (Nat.pair (Encodable.encode (ψ z.unpair.1)) (Encodable.encode baseQuote))
  have hnorm : (denominatorPatchNormCode cutoff).eval normInput =
      Part.some (denominatorPatchNorm cutoff normInput) :=
    Part.eq_some_iff.mpr (denominatorPatchNormCode_spec cutoff normInput)
  simp [denominatorPatchedQuoteCode, Nat.Partrec.Code.eval, hcondition, hbase,
    hnorm, Seq.seq, normInput, denominatorPatchNorm, denominatorPatchedQuoteTable,
    baseQuote]
  by_cases h : z.unpair.1 < cutoff ∧
      z.unpair.2 = Encodable.encode (ψ z.unpair.1) <;> simp [h]

/-- Named exact computation of the finite denominator patch. -/
noncomputable def denominatorPatchedMarketComputation {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence)
    (hψ : PolySentenceCodes ψ) (cutoff : ℕ) :
    MarketComputation (denominatorPatchedHistory P ψ cutoff) where
  quote := denominatorPatchedQuoteTable market ψ cutoff
  code := denominatorPatchedQuoteCode market ψ hψ cutoff
  quote_exact := denominatorPatchedQuoteTable_exact market ψ cutoff
  code_spec := denominatorPatchedQuoteCode_spec market ψ hψ cutoff

/-! ## Flat feature-price rewrite -/

def rawPriceTokens (sentenceCode day : ℕ) : List ℕ := [0, sentenceCode, day]
def rawConstTokens (ratCode : ℕ) : List ℕ := [1, ratCode]
def rawAddTokens (left right : List ℕ) : List ℕ := left ++ right ++ [2]
def rawMulTokens (left right : List ℕ) : List ℕ := left ++ right ++ [3]
def rawMaxTokens (left right : List ℕ) : List ℕ := left ++ right ++ [4]
def rawSafeRecipTokens (arg : List ℕ) : List ℕ := arg ++ [5]

def rawMinTokens (left right : List ℕ) : List ℕ :=
  rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
    (rawMaxTokens
      (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ))) left)
      (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ))) right))

def rawLowerSafeRecipTokens (denominator : List ℕ) (ε : ℚ) : List ℕ :=
  rawMulTokens (rawConstTokens (Encodable.encode (1 / ε)))
    (rawSafeRecipTokens
      (rawMulTokens (rawConstTokens (Encodable.encode (1 / ε))) denominator))

def rawAbsTokens (arg : List ℕ) : List ℕ :=
  rawMaxTokens arg (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ))) arg)

def rawClip01Tokens (arg : List ℕ) : List ℕ :=
  rawMaxTokens (rawConstTokens (Encodable.encode (0 : ℚ)))
    (rawMinTokens (rawConstTokens (Encodable.encode (1 : ℚ))) arg)

def rawConditioningGateTokens (ratio magnitude : List ℕ)
    (budgetCode inverseBudgetCode : ℕ) : List ℕ :=
  let maxMag := rawMaxTokens (rawConstTokens (Encodable.encode (1 : ℚ))) magnitude
  let tolerance := rawMulTokens (rawConstTokens budgetCode)
    (rawSafeRecipTokens magnitude)
  rawClip01Tokens <| rawMulTokens
    (rawAddTokens
      (rawAddTokens (rawConstTokens (Encodable.encode (1 : ℚ))) tolerance)
      (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ))) ratio))
    (rawMulTokens
      (rawConstTokens inverseBudgetCode) maxMag)

def rawConditioningRatioTokens (sentenceCode conditionCode day : ℕ)
    (ε : ℚ) : List ℕ :=
  rawMulTokens (rawPriceTokens (conjunctionCode sentenceCode conditionCode) day)
    (rawLowerSafeRecipTokens (rawPriceTokens conditionCode day) ε)

def rawLocallyGatedBetaBodyTokens
    (sentenceCode conditionCode day budgetCode inverseBudgetCode : ℕ)
    (ε : ℚ) : List ℕ :=
  let bound := [7, 0]
  let ratio := rawConditioningRatioTokens sentenceCode conditionCode day ε
  let gate := rawConditioningGateTokens ratio (rawAbsTokens bound)
    budgetCode inverseBudgetCode
  rawMinTokens bound (rawMulTokens bound gate)

def rawLocallyGatedSecondBodyTokens
    (sentenceCode conditionCode day budgetCode inverseBudgetCode : ℕ)
    (ε : ℚ) : List ℕ :=
  let beta := rawLocallyGatedBetaBodyTokens
    sentenceCode conditionCode day budgetCode inverseBudgetCode ε
  let ratio := rawConditioningRatioTokens sentenceCode conditionCode day ε
  rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
    (rawMulTokens beta ratio)

theorem streamRead_rawPrice_some {code : ℕ} {φ : Sentence}
    (h : Encodable.decode (α := Sentence) code = some φ)
    (day : ℕ) (stack : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom (rawPriceTokens code day)
        (some ((0, none), (stack, trades))) =
      some ((0, none), (EF.price φ day :: stack, trades)) := by
  simp [rawPriceTokens, EF.streamReadFrom, EF.streamStep, h]

theorem streamRead_rawPrice_none {code : ℕ}
    (h : Encodable.decode (α := Sentence) code = none)
    (day : ℕ) (stack : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom (rawPriceTokens code day)
        (some ((0, none), (stack, trades))) = none := by
  simp [rawPriceTokens, EF.streamReadFrom, EF.streamStep, h]

theorem streamRead_rawConst (q : ℚ) (stack : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom (rawConstTokens (Encodable.encode q))
        (some ((0, none), (stack, trades))) =
      some ((0, none), (EF.const q :: stack, trades)) := by
  simp [rawConstTokens, EF.streamReadFrom, EF.streamStep, Encodable.encodek]

theorem streamRead_rawBinary
    (tag : ℕ) (op : EF → EF → EF) (htag : tag = 2 ∨ tag = 3 ∨ tag = 4)
    (left right : List ℕ) (a b : EF) (stack : List EF)
    (trades : List (EF × Sentence))
    (ha : EF.streamReadFrom left (some ((0, none), (stack, trades))) =
      some ((0, none), (a :: stack, trades)))
    (hb : EF.streamReadFrom right (some ((0, none), (a :: stack, trades))) =
      some ((0, none), (b :: a :: stack, trades)))
    (hop : (tag = 2 → op = EF.add) ∧ (tag = 3 → op = EF.mul) ∧
      (tag = 4 → op = EF.max)) :
    EF.streamReadFrom (left ++ right ++ [tag])
        (some ((0, none), (stack, trades))) =
      some ((0, none), (op a b :: stack, trades)) := by
  rw [EF.streamReadFrom_append, EF.streamReadFrom_append, ha, hb]
  rcases htag with rfl | rfl | rfl <;>
    simp [EF.streamReadFrom, EF.streamStep, hop]

theorem streamRead_rawUnary5 (arg : List ℕ) (a : EF) (stack : List EF)
    (trades : List (EF × Sentence))
    (ha : EF.streamReadFrom arg (some ((0, none), (stack, trades))) =
      some ((0, none), (a :: stack, trades))) :
    EF.streamReadFrom (arg ++ [5]) (some ((0, none), (stack, trades))) =
      some ((0, none), (EF.safeRecip a :: stack, trades)) := by
  rw [EF.streamReadFrom_append, ha]
  simp [EF.streamReadFrom, EF.streamStep]

theorem streamRead_append_none (left right : List ℕ)
    (state : Option EF.StreamState)
    (h : EF.streamReadFrom left state = none) :
    EF.streamReadFrom (left ++ right) state = none := by
  rw [EF.streamReadFrom_append, h, EF.streamReadFrom_none]

/-- Raw literal serialization of the conditional-price feature.  It is defined on raw
sentence codes so an invalid source sentence remains invalid under the rewrite. -/
def rawConditionalPriceTokens (phiCode psiCode day : ℕ) (ε : ℚ) : List ℕ :=
  let numerator := rawPriceTokens (conjunctionCode phiCode psiCode) day
  let denominator := rawPriceTokens psiCode day
  let ratio := rawMulTokens numerator (rawLowerSafeRecipTokens denominator ε)
  rawMinTokens (rawConstTokens (Encodable.encode (1 : ℚ))) ratio

theorem rawConditionalPriceTokens_exact (φ ψ : Sentence) (day : ℕ) (ε : ℚ) :
    rawConditionalPriceTokens (Encodable.encode φ) (Encodable.encode ψ) day ε =
      (EF.conditionalPriceEF ψ ε φ day).serialize := by
  simp [rawConditionalPriceTokens, rawPriceTokens, rawConstTokens, rawMulTokens,
    rawMaxTokens, rawSafeRecipTokens, rawMinTokens, rawLowerSafeRecipTokens,
    EF.conditionalPriceEF, EF.conditionalRatioEF, EF.lowerSafeRecip, efMin,
    EF.serialize, conjunctionCode_exact, List.append_assoc]

theorem rawConditionalPriceTokens_poly
    {phi psi day : ℕ → ℕ} {cφ cψ cd : Nat.Partrec.Code}
    (hφ : PolyFueled cφ phi) (hψ : PolyFueled cψ psi)
    (hday : PolyFueled cd day) (ε : ℚ) :
    PolySegStream (fun z => rawConditionalPriceTokens (phi z) (psi z) (day z) ε) := by
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  have hpayload := hφ.pair hψ
  have htagged := (PolyFueled.const 3).pair hpayload
  have hconj : PolyFueled _ (fun z => conjunctionCode (phi z) (psi z)) :=
    (hadd.comp (htagged.pair (PolyFueled.const 1))).of_eq fun z => by
      simp [conjunctionCode]
  have hnum : PolyTokenStream (fun z => rawPriceTokens
      (conjunctionCode (phi z) (psi z)) (day z)) :=
    ((PolyTokenStream.const 0).append (PolyTokenStream.polyTok hconj)).append
      (PolyTokenStream.polyTok hday)
  have hden : PolyTokenStream (fun z => rawPriceTokens (psi z) (day z)) :=
    ((PolyTokenStream.const 0).append (PolyTokenStream.polyTok hψ)).append
      (PolyTokenStream.polyTok hday)
  have hconst (q : ℚ) : PolyTokenStream (fun _ : ℕ => rawConstTokens
      (Encodable.encode q)) :=
    (PolyTokenStream.const 1).append (PolyTokenStream.const (Encodable.encode q))
  have hmul {a b : ℕ → List ℕ} (ha : PolyTokenStream a) (hb : PolyTokenStream b) :
      PolyTokenStream (fun z => rawMulTokens (a z) (b z)) :=
    (ha.append hb).append (PolyTokenStream.const 3)
  have hmax {a b : ℕ → List ℕ} (ha : PolyTokenStream a) (hb : PolyTokenStream b) :
      PolyTokenStream (fun z => rawMaxTokens (a z) (b z)) :=
    (ha.append hb).append (PolyTokenStream.const 4)
  have hsafe {a : ℕ → List ℕ} (ha : PolyTokenStream a) :
      PolyTokenStream (fun z => rawSafeRecipTokens (a z)) :=
    ha.append (PolyTokenStream.const 5)
  have hlower : PolyTokenStream (fun z => rawLowerSafeRecipTokens
      (rawPriceTokens (psi z) (day z)) ε) :=
    hmul (hconst (1 / ε)) (hsafe (hmul (hconst (1 / ε)) hden))
  have hratio := hmul hnum hlower
  have hnegLeft := hmul (hconst (-1)) (hconst 1)
  have hnegRight := hmul (hconst (-1)) hratio
  have hmin := hmul (hconst (-1)) (hmax hnegLeft hnegRight)
  exact PolySegStream.of_eq (PolySegStream.ofTokenStream hmin) fun z => by
    simp [rawConditionalPriceTokens, rawMinTokens, rawMulTokens, rawMaxTokens,
      rawLowerSafeRecipTokens, rawSafeRecipTokens, rawPriceTokens, rawConstTokens,
      List.append_assoc]

/-- One source-token segment of the parser-transparent price rewrite. -/
def conditionPriceTokenSegment (tokenFn : ℕ → ℕ) (ψCode : ℕ → ℕ)
    (ε : ℚ) (z : ℕ) : List ℕ :=
  let control := PrefixPatchCompile.freezeControlNat tokenFn z
  let mode := control.unpair.1
  let pending := control.unpair.2
  let token := tokenFn z
  if mode = 0 then
    [token]
  else if mode = 1 then [token]
  else if mode = 2 then [token] ++
    rawConditionalPriceTokens pending (ψCode token) token ε ++ [8]
  else [token]

def conditionPriceTokenEmit (ψCode : ℕ → ℕ) (ε : ℚ)
    (state : EF.FreezeTokenState) (token : ℕ) : List ℕ :=
  if state.1 = 2 then [token] ++
    rawConditionalPriceTokens state.2 (ψCode token) token ε ++ [8]
  else [token]

def conditionPriceTokenRun (ψCode : ℕ → ℕ) (ε : ℚ) :
    EF.FreezeTokenState → List ℕ → EF.FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := conditionPriceTokenRun ψCode ε
        (EF.freezeTokenNext state token) tokens
      (rest.1, conditionPriceTokenEmit ψCode ε state token ++ rest.2)

theorem conditionPriceTokenRun_append (ψCode : ℕ → ℕ) (ε : ℚ)
    (state : EF.FreezeTokenState) (xs ys : List ℕ) :
    conditionPriceTokenRun ψCode ε state (xs ++ ys) =
      let first := conditionPriceTokenRun ψCode ε state xs
      let second := conditionPriceTokenRun ψCode ε first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons token tokens ih =>
      simp only [List.cons_append, conditionPriceTokenRun]
      rw [ih]
      simp [List.append_assoc]

theorem conditionPriceTokenRun_serialize (ψ : ℕ → Sentence)
    (ε : ℚ) (e : EF) :
    conditionPriceTokenRun (fun day => Encodable.encode (ψ day)) ε (0, 0)
        e.serialize = ((0, 0), (e.retainedConditionPrices ψ ε).serialize) := by
  induction e with
  | price φ day =>
      simp [EF.serialize, conditionPriceTokenRun, conditionPriceTokenEmit,
        EF.freezeTokenNext, EF.retainedConditionPrices,
        rawConditionalPriceTokens_exact]
  | const q => simp [EF.serialize, conditionPriceTokenRun, conditionPriceTokenEmit,
      EF.freezeTokenNext, EF.retainedConditionPrices]
  | add a b iha ihb =>
      simp only [EF.serialize, EF.retainedConditionPrices, conditionPriceTokenRun_append]
      rw [iha, ihb]
      simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext,
        List.append_assoc]

  | mul a b iha ihb =>
      simp only [EF.serialize, EF.retainedConditionPrices, conditionPriceTokenRun_append]
      rw [iha, ihb]
      simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext,
        List.append_assoc]

  | max a b iha ihb =>
      simp only [EF.serialize, EF.retainedConditionPrices, conditionPriceTokenRun_append]
      rw [iha, ihb]
      simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext,
        List.append_assoc]
  | safeRecip a iha =>
      simp only [EF.serialize, EF.retainedConditionPrices, conditionPriceTokenRun_append]
      rw [iha]
      simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext,
        List.append_assoc]
  | var i => simp [EF.serialize, conditionPriceTokenRun, conditionPriceTokenEmit,
      EF.freezeTokenNext, EF.retainedConditionPrices]
  | letE x body ihx ihbody =>
      simp only [EF.serialize, EF.retainedConditionPrices, conditionPriceTokenRun_append]
      rw [ihx, ihbody]
      simp [conditionPriceTokenRun, conditionPriceTokenEmit, EF.freezeTokenNext,
        List.append_assoc]

theorem streamReadFrom_rawConditionalPriceSuffix
    {phiCode : ℕ} {φ ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) phiCode = some φ)
    (day : ℕ) (ε : ℚ) (stack : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (rawConditionalPriceTokens phiCode (Encodable.encode ψ) day ε ++ [8])
        (some ((0, none), (EF.price φ day :: stack, trades))) =
      some ((0, none),
        (EF.retainedConditionPrices (fun _ => ψ) ε (EF.price φ day) ::
          stack, trades)) := by
  simp [rawConditionalPriceTokens, rawPriceTokens, rawConstTokens, rawMulTokens,
    rawMaxTokens, rawSafeRecipTokens, rawMinTokens, rawLowerSafeRecipTokens,
    EF.streamReadFrom, EF.streamStep, conjunctionCode_decode hφ,
    Encodable.encodek, EF.retainedConditionPrices, EF.conditionalPriceEF,
    EF.conditionalRatioEF, EF.lowerSafeRecip, efMin, EF.serialize]

def retainedConditionStreamState (ψ : ℕ → Sentence) (ε : ℚ) :
    EF.StreamState → EF.StreamState
  | (control, stack, trades) =>
      (control, stack.map fun e => e.retainedConditionPrices ψ ε,
        trades.map fun trade => (trade.1.retainedConditionPrices ψ ε, trade.2))

set_option maxHeartbeats 800000 in
theorem streamReadFrom_conditionPriceTokenEmit
    (ψ : ℕ → Sentence) (ε : ℚ)
    (control : EF.FreezeTokenState) (state : EF.StreamState) (token : ℕ)
    (hmatch : control.Matches state) :
    EF.streamReadFrom
        (conditionPriceTokenEmit (fun day => Encodable.encode (ψ day)) ε control token)
        (some (retainedConditionStreamState ψ ε state)) =
      (EF.streamStep (some state) token).map (retainedConditionStreamState ψ ε) ∧
    ∀ next, EF.streamStep (some state) token = some next →
      (EF.freezeTokenNext control token).Matches next := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  simp only [EF.FreezeTokenState.Matches] at hmatch ⊢
  rcases hmatch with ⟨hmode, hpending⟩
  rcases control with ⟨controlMode, code⟩
  simp only at hmode
  subst controlMode
  cases mode with
  | zero =>
      by_cases h0 : token = 0
      · subst token
        simp [conditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h1 : token = 1
      · subst token
        simp [conditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h2 : token = 2
      · subst token
        cases stack with
        | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPrices]
      by_cases h3 : token = 3
      · subst token
        cases stack with
        | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPrices]
      by_cases h4 : token = 4
      · subst token
        cases stack with
        | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPrices]
      by_cases h5 : token = 5
      · subst token
        cases stack <;> simp [conditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
          EF.retainedConditionPrices]
      by_cases h6 : token = 6
      · subst token
        simp [conditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h7 : token = 7
      · subst token
        simp [conditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h8 : token = 8
      · subst token
        cases stack with
        | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPrices]
      · simp [conditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
  | succ mode =>
      cases mode with
      | zero =>
          cases hdecode : Encodable.decode (α := Sentence) token <;>
            simp [conditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionStreamState, EF.streamReadFrom, EF.streamStep, hdecode]
      | succ mode =>
          cases mode with
          | zero =>
              obtain ⟨φ, hpendingEq, hdecode⟩ := hpending rfl
              subst pending
              constructor
              · rw [show conditionPriceTokenEmit
                    (fun day => Encodable.encode (ψ day)) ε (2, code) token =
                    [token] ++ (rawConditionalPriceTokens code
                      (Encodable.encode (ψ token)) token ε ++ [8]) by
                    simp [conditionPriceTokenEmit]]
                rw [EF.streamReadFrom_append]
                have hday : EF.streamReadFrom [token]
                    (some (retainedConditionStreamState ψ ε
                      ((2, some φ), (stack, trades)))) =
                    some ((0, none),
                      (EF.price φ token ::
                          stack.map (fun e => e.retainedConditionPrices ψ ε),
                        trades.map fun trade =>
                          (trade.1.retainedConditionPrices ψ ε, trade.2))) := by
                  simp [retainedConditionStreamState, EF.streamReadFrom,
                    EF.streamStep, hdecode]
                rw [hday, streamReadFrom_rawConditionalPriceSuffix hdecode]
                rfl
              · intro next hnext
                simp [EF.streamStep] at hnext
                subst next
                simp [EF.freezeTokenNext, EF.FreezeTokenState.Matches]
          | succ mode =>
              cases mode with
              | zero =>
                  cases hdecode : Encodable.decode (α := ℚ) token <;>
                    simp [conditionPriceTokenEmit, EF.freezeTokenNext,
                      retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
                      hdecode, EF.retainedConditionPrices]
              | succ mode =>
                  cases mode with
                  | zero =>
                      cases stack with
                      | nil => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
                          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]
                      | cons e stack =>
                        cases hdecode : Encodable.decode (α := Sentence) token <;>
                          simp [conditionPriceTokenEmit, EF.freezeTokenNext,
                            retainedConditionStreamState, EF.streamReadFrom,
                            EF.streamStep, hdecode]
                  | succ mode =>
                      cases mode with
                      | zero => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
                          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep,
                          EF.retainedConditionPrices]
                      | succ mode => simp [conditionPriceTokenEmit, EF.freezeTokenNext,
                          retainedConditionStreamState, EF.streamReadFrom, EF.streamStep]

theorem streamReadFrom_conditionPriceTokenRun
    (ψ : ℕ → Sentence) (ε : ℚ)
    (control : EF.FreezeTokenState) (state : EF.StreamState) (tokens : List ℕ)
    (hmatch : control.Matches state) :
    let run := conditionPriceTokenRun
      (fun day => Encodable.encode (ψ day)) ε control tokens
    EF.streamReadFrom run.2 (some (retainedConditionStreamState ψ ε state)) =
        (EF.streamReadFrom tokens (some state)).map
          (retainedConditionStreamState ψ ε) ∧
      ∀ next, EF.streamReadFrom tokens (some state) = some next →
        run.1.Matches next := by
  induction tokens generalizing control state with
  | nil => simp [conditionPriceTokenRun, EF.streamReadFrom, hmatch]
  | cons token tokens ih =>
      simp only [conditionPriceTokenRun]
      have hstep := streamReadFrom_conditionPriceTokenEmit ψ ε control state token hmatch
      rcases hstep with ⟨hstep, hnext⟩
      cases hs : EF.streamStep (some state) token with
      | none =>
          constructor
          · rw [EF.streamReadFrom_append, hstep, hs]
            simp only [Option.map_none]
            rw [EF.streamReadFrom_none]
            change none = (EF.streamReadFrom tokens
              (EF.streamStep (some state) token)).map
                (retainedConditionStreamState ψ ε)
            rw [hs, EF.streamReadFrom_none]
            rfl
          · intro final hfinal
            change EF.streamReadFrom tokens (EF.streamStep (some state) token) =
              some final at hfinal
            rw [hs, EF.streamReadFrom_none] at hfinal
            contradiction
      | some next =>
          have hmatches := hnext next hs
          have hrest := ih (EF.freezeTokenNext control token) next hmatches
          simp only at hrest
          rcases hrest with ⟨hrest, hfinal⟩
          constructor
          · rw [EF.streamReadFrom_append, hstep, hs]
            simp only [Option.map_some]
            rw [hrest]
            simp [EF.streamReadFrom, hs]
          · intro final hfinalSource
            apply hfinal final
            simpa [EF.streamReadFrom, hs] using hfinalSource

theorem deserializeTrades_conditionPriceTokenRun
    (ψ : ℕ → Sentence) (ε : ℚ) (tokens : List ℕ) :
    let run := conditionPriceTokenRun
      (fun day => Encodable.encode (ψ day)) ε (0, 0) tokens
    deserializeTrades run.2 =
      (deserializeTrades tokens).map fun trades =>
        trades.map fun trade =>
          (trade.1.retainedConditionPrices ψ ε, trade.2) := by
  have hrun := (streamReadFrom_conditionPriceTokenRun ψ ε
    (0, 0) EF.streamInitial tokens EF.freezeToken_initial_matches).1
  simp only at hrun ⊢
  have hinitial : retainedConditionStreamState ψ ε EF.streamInitial =
      EF.streamInitial := rfl
  rw [hinitial] at hrun
  unfold deserializeTrades
  rw [hrun]
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => rfl
  | some state =>
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
      cases mode <;> cases pending <;> cases stack <;>
        simp [retainedConditionStreamState]

/-! ### Two parser-transparent trade-frame passes -/

def frameBudgetDenominator (day count : ℕ) : ℕ :=
  (day + 1) * (day + 2) * count

def frameBudget (day count : ℕ) : ℚ :=
  if count = 0 then 0 else (frameBudgetDenominator day count : ℚ) ⁻¹

theorem frameBudget_eq (day count : ℕ) (hcount : 0 < count) :
    frameBudget day count =
      Strategy.localConditioningBudget (conditioningBudget day) count := by
  have hpos : 0 < frameBudgetDenominator day count := by
    simp [frameBudgetDenominator]
    positivity
  have hden : (frameBudgetDenominator day count : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  simp [frameBudget, frameBudgetDenominator, Strategy.localConditioningBudget,
    conditioningBudget, Nat.ne_of_gt hcount, hden, div_eq_mul_inv]
  ring

def conditioningFrameTokenEmit (second : Bool) (ψCode : ℕ)
    (day : ℕ) (ε : ℚ) (budgetCode inverseBudgetCode : ℕ)
    (state : EF.FreezeTokenState) (token : ℕ) : List ℕ :=
  if state.1 = 0 ∧ token = 6 then []
  else if state.1 = 4 then
    if second then
      rawLocallyGatedSecondBodyTokens token ψCode day
          budgetCode inverseBudgetCode ε ++ [8, 6, ψCode]
    else
      rawLocallyGatedBetaBodyTokens token ψCode day
          budgetCode inverseBudgetCode ε ++
        [8, 6, conjunctionCode token ψCode]
  else [token]

def conditioningFrameTokenRun (second : Bool) (ψCode : ℕ)
    (day : ℕ) (ε : ℚ) (budgetCode inverseBudgetCode : ℕ) :
    EF.FreezeTokenState → List ℕ → EF.FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := conditioningFrameTokenRun second ψCode day ε
        budgetCode inverseBudgetCode (EF.freezeTokenNext state token) tokens
      (rest.1, conditioningFrameTokenEmit second ψCode day ε
        budgetCode inverseBudgetCode state token ++ rest.2)

theorem conditioningFrameTokenRun_append (second : Bool) (ψCode day : ℕ)
    (ε : ℚ) (budgetCode inverseBudgetCode : ℕ)
    (state : EF.FreezeTokenState) (xs ys : List ℕ) :
    conditioningFrameTokenRun second ψCode day ε budgetCode inverseBudgetCode
        state (xs ++ ys) =
      let first := conditioningFrameTokenRun second ψCode day ε
        budgetCode inverseBudgetCode state xs
      let next := conditioningFrameTokenRun second ψCode day ε
        budgetCode inverseBudgetCode first.1 ys
      (next.1, first.2 ++ next.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons token tokens ih =>
      simp only [List.cons_append, conditioningFrameTokenRun]
      rw [ih]
      simp [List.append_assoc]

def firstFrameBody (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (φ : Sentence) : EF :=
  let bound := EF.var 0
  let ratio := EF.conditionalRatioEF ψ ε φ day
  let gate := EF.conditioningCapGate ratio (EF.absVal bound) q
  efMin bound (EF.mul bound gate)

def secondFrameBody (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (φ : Sentence) : EF :=
  EF.mul (EF.const (-1))
    (EF.mul (firstFrameBody ψ ε q day φ)
      (EF.conditionalRatioEF ψ ε φ day))

theorem streamReadFrom_rawFirstFrame
    {sentenceCode : ℕ} {φ ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) sentenceCode = some φ)
    (day : ℕ) (ε q : ℚ) (e : EF) (stack : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (rawLocallyGatedBetaBodyTokens sentenceCode (Encodable.encode ψ) day
            (Encodable.encode q) (Encodable.encode q⁻¹) ε ++
          [8, 6, conjunctionCode sentenceCode (Encodable.encode ψ)])
        (some ((0, none), (e :: stack, trades))) =
      some ((0, none), (stack,
        trades ++ [(EF.letE e (firstFrameBody ψ ε q day φ), φ ⋏ ψ)])) := by
  simp [rawLocallyGatedBetaBodyTokens, rawConditioningRatioTokens,
    rawConditioningGateTokens, rawAbsTokens, rawClip01Tokens,
    rawPriceTokens, rawConstTokens, rawAddTokens, rawMulTokens, rawMaxTokens,
    rawSafeRecipTokens, rawMinTokens, rawLowerSafeRecipTokens,
    EF.streamReadFrom, EF.streamStep, conjunctionCode_decode hφ,
    Encodable.encodek, firstFrameBody, EF.conditioningCapGate,
    EF.conditioningTolerance, EF.absVal, EF.conditionalRatioEF,
    EF.lowerSafeRecip, clip01, efMin]

theorem streamReadFrom_rawSecondFrame
    {sentenceCode : ℕ} {φ ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) sentenceCode = some φ)
    (day : ℕ) (ε q : ℚ) (e : EF) (stack : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (rawLocallyGatedSecondBodyTokens sentenceCode (Encodable.encode ψ) day
            (Encodable.encode q) (Encodable.encode q⁻¹) ε ++
          [8, 6, Encodable.encode ψ])
        (some ((0, none), (e :: stack, trades))) =
      some ((0, none), (stack,
        trades ++ [(EF.letE e (secondFrameBody ψ ε q day φ), ψ)])) := by
  simp [rawLocallyGatedSecondBodyTokens, rawLocallyGatedBetaBodyTokens,
    rawConditioningRatioTokens, rawConditioningGateTokens, rawAbsTokens,
    rawClip01Tokens, rawPriceTokens, rawConstTokens, rawAddTokens, rawMulTokens,
    rawMaxTokens, rawSafeRecipTokens, rawMinTokens, rawLowerSafeRecipTokens,
    EF.streamReadFrom, EF.streamStep, conjunctionCode_decode hφ,
    Encodable.encodek, firstFrameBody, secondFrameBody,
    EF.conditioningCapGate, EF.conditioningTolerance, EF.absVal,
    EF.conditionalRatioEF, EF.lowerSafeRecip, clip01, efMin]

def frameLeg (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (p : EF × Sentence) : EF × Sentence :=
  if second then (EF.letE p.1 (secondFrameBody ψ ε q day p.2), ψ)
  else (EF.letE p.1 (firstFrameBody ψ ε q day p.2), p.2 ⋏ ψ)

def frameStreamState (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ) :
    EF.StreamState → EF.StreamState
  | ((mode, pending), stack, trades) =>
      ((if mode = 4 then 0 else mode,
          if mode = 4 ∨ mode = 0 then none else pending),
        stack, trades.map (frameLeg second ψ ε q day))

/- The full malformed-frame simulation is the remaining proof obligation for the two-pass
translator.  Keep the attempted case split out of the compiled surface until its invalid-code
and empty-stack helper lemmas are factored into small parser equations.
set_option maxHeartbeats 800000 in
theorem streamReadFrom_conditioningFrameTokenEmit
    (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (control : EF.FreezeTokenState) (state : EF.StreamState) (token : ℕ)
    (hmatch : control.Matches state) :
    EF.streamReadFrom
        (conditioningFrameTokenEmit second (Encodable.encode ψ) day ε
          (Encodable.encode q) (Encodable.encode q⁻¹) control token)
        (some (frameStreamState second ψ ε q day state)) =
      (EF.streamStep (some state) token).map
        (frameStreamState second ψ ε q day) ∧
    ∀ next, EF.streamStep (some state) token = some next →
      (EF.freezeTokenNext control token).Matches next := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  simp only [EF.FreezeTokenState.Matches] at hmatch ⊢
  rcases hmatch with ⟨hmode, hpending⟩
  rcases control with ⟨controlMode, code⟩
  simp only at hmode
  subst controlMode
  cases mode with
  | zero =>
      by_cases h0 : token = 0
      · subst token; simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
          frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h1 : token = 1
      · subst token; simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
          frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h2 : token = 2
      · subst token
        cases stack with
        | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
            frameStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack => cases stack with
          | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h3 : token = 3
      · subst token
        cases stack with
        | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
            frameStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack => cases stack with
          | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h4 : token = 4
      · subst token
        cases stack with
        | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
            frameStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack => cases stack with
          | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h5 : token = 5
      · subst token; cases stack <;> simp [conditioningFrameTokenEmit,
          EF.freezeTokenNext, frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h6 : token = 6
      · subst token; simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
          frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h7 : token = 7
      · subst token; simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
          frameStreamState, EF.streamReadFrom, EF.streamStep]
      by_cases h8 : token = 8
      · subst token
        cases stack with
        | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
            frameStreamState, EF.streamReadFrom, EF.streamStep]
        | cons a stack => cases stack with
          | nil => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
              frameStreamState, EF.streamReadFrom, EF.streamStep]
      · simp [conditioningFrameTokenEmit, EF.freezeTokenNext, frameStreamState,
          EF.streamReadFrom, EF.streamStep, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  | succ mode =>
      cases mode with
      | zero =>
          cases hdecode : Encodable.decode (α := Sentence) token <;>
            simp [conditioningFrameTokenEmit, EF.freezeTokenNext, frameStreamState,
              EF.streamReadFrom, EF.streamStep, hdecode]
      | succ mode =>
          cases mode with
          | zero =>
              obtain ⟨φ, hpendingEq, hdecode⟩ := hpending rfl
              subst pending
              simp [conditioningFrameTokenEmit, EF.freezeTokenNext, frameStreamState,
                EF.streamReadFrom, EF.streamStep, hdecode]
          | succ mode =>
              cases mode with
              | zero =>
                  cases hdecode : Encodable.decode (α := ℚ) token <;>
                    simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
                      frameStreamState, EF.streamReadFrom, EF.streamStep, hdecode]
              | succ mode =>
                  cases mode with
                  | zero =>
                      cases stack with
                      | nil =>
                          cases hdecode : Encodable.decode (α := Sentence) token <;>
                            simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
                              frameStreamState, EF.streamReadFrom, EF.streamStep,
                              hdecode, rawLocallyGatedBetaBodyTokens,
                              rawLocallyGatedSecondBodyTokens]
                      | cons e stack =>
                          cases hdecode : Encodable.decode (α := Sentence) token with
                          | none =>
                              cases second <;> simp [conditioningFrameTokenEmit,
                                frameStreamState, EF.streamReadFrom, EF.streamStep,
                                hdecode, rawLocallyGatedBetaBodyTokens,
                                rawLocallyGatedSecondBodyTokens,
                                rawConditioningRatioTokens, rawPriceTokens]
                          | some φ =>
                              constructor
                              · cases second with
                                | false =>
                                    simpa [conditioningFrameTokenEmit, frameStreamState,
                                      frameLeg] using streamReadFrom_rawFirstFrame
                                        hdecode day ε q e stack
                                        (trades.map (frameLeg false ψ ε q day))
                                | true =>
                                    simpa [conditioningFrameTokenEmit, frameStreamState,
                                      frameLeg] using streamReadFrom_rawSecondFrame
                                        hdecode day ε q e stack
                                        (trades.map (frameLeg true ψ ε q day))
                              · intro next hnext
                                simp [EF.streamStep, hdecode] at hnext
                                subst next
                                simp [EF.freezeTokenNext]
                  | succ mode =>
                      cases mode with
                      | zero => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
                          frameStreamState, EF.streamReadFrom, EF.streamStep]
                      | succ mode => simp [conditioningFrameTokenEmit, EF.freezeTokenNext,
                          frameStreamState, EF.streamReadFrom, EF.streamStep]

/-- A price-leaf rewrite over an arbitrary polynomial-length raw stream.  The source is
addressed by `tokenFn ⟨day,index⟩`; each source token emits a bounded segment, and
`concatVar` performs the varying-width concatenation. -/
theorem conditionPriceTokenSegments_poly
    {tokenFn lenFn : ℕ → ℕ} {ct cl : Nat.Partrec.Code}
    (htoken : PolyFueled ct tokenFn) (hlen : PolyFueled cl lenFn)
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) (ε : ℚ) :
    PolySegStream (fun n => (List.range (lenFn n)).flatMap fun j =>
      conditionPriceTokenSegment tokenFn (fun day => Encodable.encode (ψ day)) ε
        (Nat.pair n j)) := by
  let control : ℕ → ℕ := PrefixPatchCompile.freezeControlNat tokenFn
  let mode : ℕ → ℕ := fun z => (control z).unpair.1
  let pending : ℕ → ℕ := fun z => (control z).unpair.2
  let token : ℕ → ℕ := tokenFn
  let condition : ℕ → ℕ := fun z => Encodable.encode (ψ (token z))
  obtain ⟨ccontrol, hcontrol⟩ :=
    PrefixPatchCompile.freezeControlNat_polyFueled htoken
  have hmode : PolyFueled _ mode := PolyFueled.left.comp hcontrol
  have hpending : PolyFueled _ pending := PolyFueled.right.comp hcontrol
  obtain ⟨cψ, hψPoly⟩ := hψ
  have hcondition : PolyFueled _ condition := hψPoly.comp htoken
  have hlong : PolySegStream (fun z =>
      rawConditionalPriceTokens (pending z) (condition z) (token z) ε) :=
    rawConditionalPriceTokens_poly hpending hcondition htoken ε
  have hcopy : PolySegStream (fun z => [token z]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok htoken)
  obtain ⟨cmode2, hmode2⟩ := polyFueled_eqConst hmode 2
  have hlongSuffix : PolySegStream (fun z =>
      [token z] ++ rawConditionalPriceTokens
        (pending z) (condition z) (token z) ε ++ [8]) :=
    (hcopy.append hlong).append
      (PolySegStream.ofTokenStream (PolyTokenStream.const 8))
  have hmode2Branch : PolySegStream (fun z =>
      if (if mode z = 2 then 1 else 0) = 0 then [token z]
      else [token z] ++ rawConditionalPriceTokens
        (pending z) (condition z) (token z) ε ++ [8]) :=
    hcopy.ifZero hlongSuffix hmode2
  have hsegment : PolySegStream (fun z =>
      conditionPriceTokenSegment tokenFn (fun day => Encodable.encode (ψ day)) ε z) :=
    hmode2Branch.of_eq fun z => by
      simp only [conditionPriceTokenSegment]
      by_cases hm0 : mode z = 0 <;> by_cases hm1 : mode z = 1 <;>
        by_cases hm2 : mode z = 2 <;>
        simp [mode, token, pending, condition, control, hm0, hm1, hm2]
  exact hsegment.concatVar hlen

-/

/-! ### Trade-frame scan -/

/-- Before source index `j`, record the first token after the preceding trade frame and the
number of completed frames.  The shallow streaming control distinguishes a genuine frame
sentence from a numeral `6` occurring inside another token form. -/
def tradeScanAt (tokenFn : ℕ → ℕ) (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | j + 1 =>
      let previous := tradeScanAt tokenFn n j
      let mode := (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1
      if mode = 4 then (j + 1, previous.2 + 1) else previous

def tradeScanNat (tokenFn : ℕ → ℕ) (z : ℕ) : ℕ :=
  let state := tradeScanAt tokenFn z.unpair.1 z.unpair.2
  Nat.pair state.1 state.2

theorem tradeScanAt_fst_le (tokenFn : ℕ → ℕ) (n j : ℕ) :
    (tradeScanAt tokenFn n j).1 ≤ j := by
  induction j with
  | zero => simp [tradeScanAt]
  | succ j ih =>
      simp only [tradeScanAt]
      split
      · simp
      · exact ih.trans (Nat.le_succ _)

theorem tradeScanAt_snd_le (tokenFn : ℕ → ℕ) (n j : ℕ) :
    (tradeScanAt tokenFn n j).2 ≤ j := by
  induction j with
  | zero => simp [tradeScanAt]
  | succ j ih =>
      simp only [tradeScanAt]
      split
      · simpa using Nat.succ_le_succ ih
      · exact ih.trans (Nat.le_succ _)

theorem tradeScanNat_polyFueled {tokenFn : ℕ → ℕ} {ct : Nat.Partrec.Code}
    (htoken : PolyFueled ct tokenFn) :
    ∃ c, PolyFueled c (tradeScanNat tokenFn) := by
  obtain ⟨ccontrol, hcontrol⟩ :=
    PrefixPatchCompile.freezeControlNat_polyFueled htoken
  have hn : PolyFueled Nat.Partrec.Code.left (fun z => z.unpair.1) :=
    PolyFueled.left
  have hj : PolyFueled (Nat.Partrec.Code.left.comp Nat.Partrec.Code.right)
      (fun z => z.unpair.2.unpair.1) :=
    PolyFueled.left.comp PolyFueled.right
  have hprevious : PolyFueled (Nat.Partrec.Code.right.comp Nat.Partrec.Code.right)
      (fun z => z.unpair.2.unpair.2) :=
    PolyFueled.right.comp PolyFueled.right
  have hstart := PolyFueled.left.comp hprevious
  have hcount := PolyFueled.right.comp hprevious
  have hcontrolAt := hcontrol.comp (hn.pair hj)
  have hmode := PolyFueled.left.comp hcontrolAt
  obtain ⟨cmode4, hmode4⟩ := polyFueled_eqConst hmode 4
  have hnext : PolyFueled _ (fun z =>
      Nat.pair (z.unpair.2.unpair.1 + 1)
        ((z.unpair.2.unpair.2).unpair.2 + 1)) :=
    hj.succ_comp.pair hcount.succ_comp
  obtain ⟨cstep, hstep⟩ := PrefixPatchCompile.polyFueled_ifZero
    hmode4 hprevious hnext
  have hstate : IsPolyBounded (fun z => tradeScanNat tokenFn z) := by
    have hmajor : IsPolyBounded (fun z => Nat.pair z z) :=
      (IsPolyBounded.linear 0).pair (IsPolyBounded.linear 0)
    exact hmajor.of_le fun z => by
      simp only [tradeScanNat]
      let r := z.unpair.2
      have ha : (tradeScanAt tokenFn z.unpair.1 r).1 ≤ r :=
        tradeScanAt_fst_le tokenFn z.unpair.1 r
      have hb : (tradeScanAt tokenFn z.unpair.1 r).2 ≤ r :=
        tradeScanAt_snd_le tokenFn z.unpair.1 r
      have hr : r ≤ z := Nat.unpair_right_le z
      exact ((pair_le_pair_left' _ ha).trans (pair_le_pair_right' _ hb)).trans
        ((pair_le_pair_left' _ hr).trans (pair_le_pair_right' _ hr))
  have hstate' : IsPolyBounded (fun m =>
      tradeScanNat tokenFn (Nat.pair m.unpair.1 m.unpair.2)) := by
    simpa only [Nat.pair_unpair] using hstate
  refine ⟨_, (PolyFueled.prec (PolyFueled.const (Nat.pair 0 0)) hstep
    (st := fun n j => tradeScanNat tokenFn (Nat.pair n j))
    (fun n => ?_) (fun n j => ?_) hstate').of_eq fun z => ?_⟩
  · simp [tradeScanNat, tradeScanAt]
  · simp only [tradeScanNat, Nat.unpair_pair, tradeScanAt]
    by_cases hm :
        (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1 = 4
    · simp [hm]
    · simp [hm]
  · rw [Nat.pair_unpair]

end ConditioningCompile

end LogicalInduction
