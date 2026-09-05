import LogicalInduction.Construction.Witnesses.ConditioningPresentation
import LogicalInduction.Construction.LIACompiler
import LogicalInduction.Construction.Witnesses.BoundedEvaluation

/-!
# Executable compiler for closure under conditioning

The machinery behind closure of the logical induction criterion under conditioning
(`thm:scon`); the criterion-level statement itself is not here.  Three layers, each usable on
its own.

**The conditioned market as an exact rational program.**  `conditionalRat`, `conjunctionCode`,
`conditionedQuoteTable`/`conditionedQuoteCode` and `conditionedMarketComputation` build the
market `P(φ | ψ)` from the base market's own rational quote table together with a recursive
naming program for the condition sequence (`BigSentenceCodes.exists_code`); only ordinary
partial recursiveness of the whole code is needed, and none of it is metered.

**The finite denominator patch.**  `denominatorPatchedHistory` pins the condition's price to
`1` on a finite prefix, so a positive rational floor on the denominator is available on every
day, and `denominatorPatchNorm` totalizes the patched table on raw codes.

**The flat token transducer.**  `rawConditionalPriceTokens` and the `raw*Tokens` combinators
rewrite a trader's serialized strategy stream into the conditioned trader's, in a form the
streaming `EF` parser reads back unchanged.  There are two rewrite variants — the
retained-condition run, and the zero-aware run that treats a finite `Finset` of exact
zero-price days exactly — and two parser-transparent frame passes joined safely
(`conditioningFrameTokenRun`, the shallow `parserStructurallyAccepts`/`tradeScanNat`
acceptance scans, and `safeSeparatedFrameTokenOutput`).  Every emitter carries a
`PolyFueled`/`PolySegStream` bound (`dd:fuel`), which is what makes the rewrite an efficiently
computable transform; `EF` being reified syntax (`dd:dsl`) is what makes a token-level rewrite
possible at all.

The closing sections supply the floor the patch consumes:
`exists_eventual_condition_price_floor` derives an eventual positive rational floor on diagonal
condition prices from Uniform Non-Dogmatism plus Preemptive Learning, and
`eventualConditioningFloor_nonempty_of_jointConsistency` turns it into the finite-zero
certificate.  Joint consistency is a hypothesis of *that* argument, not of the paper's theorem.

The operational-witness constructors and the criterion-level `thm:scon` endpoints are in
`Construction/Machine/CondEndpoints.lean` (namespace `ConditioningCompile`);
`Construction/Witnesses/RpnConditioning.lean` (namespace `RpnConditioning`) certifies the same
translation in the token-metered model.  This file carries the economic and floor content both
consume.
-/

namespace LogicalInduction

namespace ConditioningCompile

open Filter

-- `Primrec`/`PolyFueled` elaboration over the deep product types below unfolds `Nat.sqrt`'s
-- well-founded definition during `whnf` and loops; local irreducibility stops that.
attribute [local irreducible] Nat.sqrt

/-! ## The conditioned market as an exact rational program -/

/-- Exact rational counterpart of the paper's capped conditional quote. -/
private def conditionalRat (numerator denominator : ℚ) : ℚ :=
  if numerator < denominator then numerator / denominator else 1

/-- Raw code of `φ ⋏ ψ` from the canonical codes of `φ` and `ψ`. -/
def conjunctionCode (phiCode psiCode : ℕ) : ℕ :=
  Nat.pair 3 (Nat.pair phiCode psiCode) + 1

lemma conjunctionCode_exact (φ ψ : Sentence) :
    conjunctionCode (Encodable.encode φ) (Encodable.encode ψ) =
      Encodable.encode (φ ⋏ ψ) := by
  rfl

private lemma conjunctionCode_decode {phiCode : ℕ} {φ ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) phiCode = some φ) :
    Encodable.decode (α := Sentence)
      (conjunctionCode phiCode (Encodable.encode ψ)) = some (φ ⋏ ψ) := by
  change LO.Propositional.Formula.ofNat phiCode = some φ at hφ
  change LO.Propositional.Formula.ofNat
    (conjunctionCode phiCode (LO.Propositional.Formula.toNat ψ)) = some (φ ⋏ ψ)
  simp [conjunctionCode, LO.Propositional.Formula.ofNat, hφ,
    LO.Propositional.Formula.ofNat_toNat]

lemma conjunctionCode_decode_none {phiCode : ℕ} {ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) phiCode = none) :
    Encodable.decode (α := Sentence)
      (conjunctionCode phiCode (Encodable.encode ψ)) = none := by
  change LO.Propositional.Formula.ofNat phiCode = none at hφ
  change LO.Propositional.Formula.ofNat
    (conjunctionCode phiCode (LO.Propositional.Formula.toNat ψ)) = none
  simp [conjunctionCode, LO.Propositional.Formula.ofNat, hφ,
    LO.Propositional.Formula.ofNat_toNat]

private lemma conjunctionCode_prim : Primrec₂ conjunctionCode := by
  exact (Primrec.nat_add.comp₂
    (Primrec₂.natPair.comp₂ (Primrec₂.const 3)
      (Primrec₂.natPair.comp₂ Primrec₂.left Primrec₂.right))
    (Primrec₂.const 1)).of_eq fun _ _ => rfl

/-- One total code implementing the raw conjunction-code constructor. -/
private noncomputable def conjunctionCodeCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conjunctionCode_prim)))

private lemma conjunctionCodeCode_spec (z : ℕ) :
    conjunctionCode z.unpair.1 z.unpair.2 ∈ conjunctionCodeCode.eval z := by
  have h := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conjunctionCode_prim)))
  rw [conjunctionCodeCode, h]
  exact Part.mem_some _

/-- Decode two rational codes, take the capped conditional ratio, and re-encode it. -/
private def conditionalRatNorm (z : ℕ) : ℕ :=
  let numerator := (Encodable.decode (α := ℚ) z.unpair.1).getD 0
  let denominator := (Encodable.decode (α := ℚ) z.unpair.2).getD 0
  Encodable.encode (conditionalRat numerator denominator)

private lemma conditionalRatNorm_prim : Primrec conditionalRatNorm := by
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

private lemma conditionalRatNorm_exact (numerator denominator : ℚ) :
    conditionalRatNorm
        (Nat.pair (Encodable.encode numerator) (Encodable.encode denominator)) =
      Encodable.encode (conditionalRat numerator denominator) := by
  simp [conditionalRatNorm]

/-- One total code implementing `conditionalRatNorm`. -/
private noncomputable def conditionalRatCode : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conditionalRatNorm_prim)))

private lemma conditionalRatCode_spec (z : ℕ) :
    conditionalRatNorm z ∈ conditionalRatCode.eval z := by
  have h := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp conditionalRatNorm_prim)))
  rw [conditionalRatCode, h]
  exact Part.mem_some _

/-- Rational table computed for the conditioned history.  Its values on malformed sentence
codes are deliberately totalized using the same raw conjunction-code operation. -/
private def conditionedQuoteTable {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (day code : ℕ) : ℚ :=
  conditionalRat
    (market.quote day (conjunctionCode code (Encodable.encode (ψ day))))
    (market.quote day (Encodable.encode (ψ day)))

private lemma conditionedQuoteTable_exact {P : History} (market : MarketComputation P)
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
private noncomputable def conditionedQuoteCode {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) : Nat.Partrec.Code := by
  let ψCode : Nat.Partrec.Code := Classical.choose hψ.exists_code
  let conditionAt : Nat.Partrec.Code := ψCode.comp Nat.Partrec.Code.left
  let conjunctionInput : Nat.Partrec.Code :=
    Nat.Partrec.Code.left.pair
      (conjunctionCodeCode.comp
        (Nat.Partrec.Code.right.pair conditionAt))
  let denominatorInput : Nat.Partrec.Code :=
    Nat.Partrec.Code.left.pair conditionAt
  exact conditionalRatCode.comp
    ((market.code.comp conjunctionInput).pair (market.code.comp denominatorInput))

private lemma conditionedQuoteCode_spec {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) (z : ℕ) :
    Encodable.encode
        (conditionedQuoteTable market ψ z.unpair.1 z.unpair.2) ∈
      (conditionedQuoteCode market ψ hψ).eval z := by
  classical
  have hconditionMem : Encodable.encode (ψ z.unpair.1) ∈
      (Classical.choose hψ.exists_code).eval z.unpair.1 :=
    Classical.choose_spec hψ.exists_code z.unpair.1
  have hcondition : (Classical.choose hψ.exists_code).eval z.unpair.1 =
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

/-- The conditioned history is a computable rational market whenever the base market has a
named computation and the condition sequence is write-out efficient (whence its whole-value
naming program is recursive — `BigSentenceCodes.exists_code`; only ordinary partial
recursiveness of the whole code is needed here, no metering of it). -/
noncomputable def conditionedMarketComputation {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ) :
    MarketComputation (conditionedHistory P ψ) where
  price_mem_Icc := conditionedHistory_mem_Icc P market.price_mem_Icc ψ
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

private lemma denominatorPatchedHistory_tail (P : History) (ψ : ℕ → Sentence)
    (cutoff day : ℕ) (hday : cutoff ≤ day) (φ : Sentence) :
    denominatorPatchedHistory P ψ cutoff day φ = P day φ := by
  simp [denominatorPatchedHistory, Nat.not_lt.mpr hday]

private lemma denominatorPatchedHistory_condition_prefix (P : History)
    (ψ : ℕ → Sentence) (cutoff day : ℕ) (hday : day < cutoff) :
    denominatorPatchedHistory P ψ cutoff day (ψ day) = 1 := by
  simp [denominatorPatchedHistory, hday]

private lemma denominatorPatchedHistory_mem_Icc (P : History) (ψ : ℕ → Sentence)
    (cutoff : ℕ) (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1)
    (day : ℕ) (φ : Sentence) :
    0 ≤ denominatorPatchedHistory P ψ cutoff day φ ∧
      denominatorPatchedHistory P ψ cutoff day φ ≤ 1 := by
  unfold denominatorPatchedHistory
  split
  · norm_num
  · exact hP day φ

lemma denominatorPatchedHistory_floor (P : History) (ψ : ℕ → Sentence)
    (cutoff : ℕ) {ε : ℚ} (hεone : (ε : ℝ) ≤ 1)
    (htail : ∀ day, cutoff ≤ day → (ε : ℝ) ≤ P day (ψ day)) (day : ℕ) :
    (ε : ℝ) ≤ denominatorPatchedHistory P ψ cutoff day (ψ day) := by
  by_cases hday : day < cutoff
  · rw [denominatorPatchedHistory_condition_prefix P ψ cutoff day hday]
    exact hεone
  · rw [denominatorPatchedHistory_tail P ψ cutoff day (Nat.le_of_not_gt hday)]
    exact htail day (Nat.le_of_not_gt hday)

/-- Rational quote table of the finite denominator patch. -/
private def denominatorPatchedQuoteTable {P : History} (market : MarketComputation P)
    (ψ : ℕ → Sentence) (cutoff day code : ℕ) : ℚ :=
  if day < cutoff ∧ code = Encodable.encode (ψ day) then 1
  else market.quote day code

private lemma denominatorPatchedQuoteTable_exact {P : History}
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
private def denominatorPatchNorm (cutoff z : ℕ) : ℕ :=
  let input := z.unpair.1
  let output := z.unpair.2
  if input.unpair.1 < cutoff ∧ input.unpair.2 = output.unpair.1 then
    Encodable.encode (1 : ℚ)
  else output.unpair.2

private lemma denominatorPatchNorm_prim (cutoff : ℕ) :
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

/-- A partial-recursive code for `denominatorPatchNorm cutoff`, chosen by
`Nat.Partrec.Code.exists_code`; `denominatorPatchNormCode_spec` is its evaluation law. -/
private noncomputable def denominatorPatchNormCode (cutoff : ℕ) : Nat.Partrec.Code :=
  Classical.choose (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec
      (Primrec.nat_iff.mp (denominatorPatchNorm_prim cutoff))))

private lemma denominatorPatchNormCode_spec (cutoff z : ℕ) :
    denominatorPatchNorm cutoff z ∈ (denominatorPatchNormCode cutoff).eval z := by
  have h := Classical.choose_spec (Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec
      (Primrec.nat_iff.mp (denominatorPatchNorm_prim cutoff))))
  rw [denominatorPatchNormCode, h]
  exact Part.mem_some _

/-- Partial-recursive program for the finitely patched base market. -/
private noncomputable def denominatorPatchedQuoteCode {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence)
    (hψ : BigSentenceCodes ψ) (cutoff : ℕ) : Nat.Partrec.Code :=
  let conditionAt := (Classical.choose hψ.exists_code).comp Nat.Partrec.Code.left
  denominatorPatchNormCode cutoff |>.comp
    ((Nat.Partrec.Code.left.pair Nat.Partrec.Code.right).pair
      (conditionAt.pair market.code))

private lemma denominatorPatchedQuoteCode_spec {P : History}
    (market : MarketComputation P) (ψ : ℕ → Sentence)
    (hψ : BigSentenceCodes ψ) (cutoff z : ℕ) :
    Encodable.encode (denominatorPatchedQuoteTable market ψ cutoff
      z.unpair.1 z.unpair.2) ∈
      (denominatorPatchedQuoteCode market ψ hψ cutoff).eval z := by
  classical
  have hconditionMem : Encodable.encode (ψ z.unpair.1) ∈
      (Classical.choose hψ.exists_code).eval z.unpair.1 :=
    Classical.choose_spec hψ.exists_code z.unpair.1
  have hcondition : (Classical.choose hψ.exists_code).eval z.unpair.1 =
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
    (hψ : BigSentenceCodes ψ) (cutoff : ℕ) :
    MarketComputation (denominatorPatchedHistory P ψ cutoff) where
  price_mem_Icc := denominatorPatchedHistory_mem_Icc P ψ cutoff market.price_mem_Icc
  quote := denominatorPatchedQuoteTable market ψ cutoff
  code := denominatorPatchedQuoteCode market ψ hψ cutoff
  quote_exact := denominatorPatchedQuoteTable_exact market ψ cutoff
  code_spec := denominatorPatchedQuoteCode_spec market ψ hψ cutoff

/-! ## Flat feature-price rewrite -/

/-! ### Raw token combinators

These build `EF.serialize` streams directly on *raw* codes, so an invalid source code stays
invalid under the rewrite instead of being silently repaired.  The tag alphabet is
`EF.serialize`'s own: `0` price (followed by a sentence code and a day), `1` const (followed by
a rational code), `2` add, `3` mul, `4` max, `5` safeRecip, `7` a de Bruijn variable, `8` a
`letE`, and — from `EF.serializeTrades` — `6` a trade frame, followed by its sentence code.
The combinators without a tag of their own say which identity encodes them. -/

/-- Serialized `EF.price` at a raw sentence code and a day (tag `0`). -/
def rawPriceTokens (sentenceCode day : ℕ) : List ℕ := [0, sentenceCode, day]
/-- Serialized `EF.const` at a raw rational code (tag `1`). -/
def rawConstTokens (ratCode : ℕ) : List ℕ := [1, ratCode]
/-- Serialized `EF.add` in postfix form (tag `2`). -/
def rawAddTokens (left right : List ℕ) : List ℕ := left ++ right ++ [2]
/-- Serialized `EF.mul` in postfix form (tag `3`). -/
def rawMulTokens (left right : List ℕ) : List ℕ := left ++ right ++ [3]
/-- Serialized `EF.max` in postfix form (tag `4`). -/
def rawMaxTokens (left right : List ℕ) : List ℕ := left ++ right ++ [4]
/-- Serialized `EF.safeRecip` in postfix form (tag `5`). -/
def rawSafeRecipTokens (arg : List ℕ) : List ℕ := arg ++ [5]

/-- Minimum: the parser has no `min` tag, so it is encoded as
`-max (-left) (-right)`, matching `efMin`. -/
def rawMinTokens (left right : List ℕ) : List ℕ :=
  rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
    (rawMaxTokens
      (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ))) left)
      (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ))) right))

/-- Reciprocal of a denominator floored at `ε`, encoded as
`ε⁻¹ · safeRecip (ε⁻¹ · denominator)`, matching `EF.lowerSafeRecip`. -/
def rawLowerSafeRecipTokens (denominator : List ℕ) (ε : ℚ) : List ℕ :=
  rawMulTokens (rawConstTokens (Encodable.encode (1 / ε)))
    (rawSafeRecipTokens
      (rawMulTokens (rawConstTokens (Encodable.encode (1 / ε))) denominator))

/-- Absolute value, encoded as `max arg (-arg)`, matching `EF.absVal`. -/
def rawAbsTokens (arg : List ℕ) : List ℕ :=
  rawMaxTokens arg (rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ))) arg)

/-- Clipping into `[0,1]`, encoded as `max 0 (min 1 arg)`. -/
def rawClip01Tokens (arg : List ℕ) : List ℕ :=
  rawMaxTokens (rawConstTokens (Encodable.encode (0 : ℚ)))
    (rawMinTokens (rawConstTokens (Encodable.encode (1 : ℚ))) arg)

/-- Serialized `EF.conditioningCapGate`: the clipped linear ramp
`clip01 (((1 + budget · safeRecip magnitude) - ratio) · (budget⁻¹ · max 1 magnitude))`,
with the budget and its inverse supplied as raw rational codes. -/
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

/-- Serialized `EF.conditionalRatioEF`: the price of `φ ⋏ ψ` times the `ε`-floored
reciprocal of the price of `ψ`, all on day `day`. -/
def rawConditioningRatioTokens (sentenceCode conditionCode day : ℕ)
    (ε : ℚ) : List ℕ :=
  rawMulTokens (rawPriceTokens (conjunctionCode sentenceCode conditionCode) day)
    (rawLowerSafeRecipTokens (rawPriceTokens conditionCode day) ε)

/-- Serialized first (β) frame body: the conditional ratio bound by `letE`, returning the
gated bound `min bound (bound · gate)`.  This is `firstFrameBody` in token form. -/
def rawLocallyGatedBetaBodyTokens
    (sentenceCode conditionCode day budgetCode inverseBudgetCode : ℕ)
    (ε : ℚ) : List ℕ :=
  let ratioValue := rawConditioningRatioTokens sentenceCode conditionCode day ε
  let boundRatio := [7, 0]
  let bound := [7, 1]
  let gate := rawConditioningGateTokens boundRatio (rawAbsTokens bound)
    budgetCode inverseBudgetCode
  ratioValue ++ rawMinTokens bound (rawMulTokens bound gate) ++ [8]

/-- Serialized second frame body: the same `letE` binding, returning `-(β · ratio)`.
This is `secondFrameBody` in token form. -/
def rawLocallyGatedSecondBodyTokens
    (sentenceCode conditionCode day budgetCode inverseBudgetCode : ℕ)
    (ε : ℚ) : List ℕ :=
  let _beta := rawLocallyGatedBetaBodyTokens
    sentenceCode conditionCode day budgetCode inverseBudgetCode ε
  -- The second leg reuses the β leg's leading ratio binding, but negates the product of
  -- the gated bound with the bound ratio.
  let ratioValue := rawConditioningRatioTokens sentenceCode conditionCode day ε
  let boundRatio := [7, 0]
  let bound := [7, 1]
  let gate := rawConditioningGateTokens boundRatio (rawAbsTokens bound)
    budgetCode inverseBudgetCode
  let betaCore := rawMinTokens bound (rawMulTokens bound gate)
  ratioValue ++ rawMulTokens (rawConstTokens (Encodable.encode (-1 : ℚ)))
    (rawMulTokens betaCore boundRatio) ++ [8]

private lemma streamRead_rawPrice_none {code : ℕ}
    (h : Encodable.decode (α := Sentence) code = none)
    (day : ℕ) (stack : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom (rawPriceTokens code day)
        (some ((0, none), (stack, trades))) = none := by
  simp [rawPriceTokens, EF.streamReadFrom, EF.streamStep, h]

private lemma streamRead_append_none (left right : List ℕ)
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

/-- Per-token output of the price rewrite.  Every token is re-emitted; at the day token of
a `price` triple (freeze-token mode `2`) the conditional-price body and its `letE`
terminator are appended, so the price node becomes its conditioned counterpart. -/
def conditionPriceTokenEmit (ψCode : ℕ → ℕ) (ε : ℚ)
    (state : EF.FreezeTokenState) (token : ℕ) : List ℕ :=
  if state.1 = 2 then [token] ++
    rawConditionalPriceTokens state.2 (ψCode token) token ε ++ [8]
  else [token]

/-- `conditionPriceTokenEmit` folded along a token list, threading the freeze-token control
state and returning the state reached together with the rewritten stream. -/
def conditionPriceTokenRun (ψCode : ℕ → ℕ) (ε : ℚ) :
    EF.FreezeTokenState → List ℕ → EF.FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := conditionPriceTokenRun ψCode ε
        (EF.freezeTokenNext state token) tokens
      (rest.1, conditionPriceTokenEmit ψCode ε state token ++ rest.2)

private lemma conditionPriceTokenRun_append (ψCode : ℕ → ℕ) (ε : ℚ)
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

lemma conditionPriceTokenRun_range (tokenFn : ℕ → ℕ) (ψCode : ℕ → ℕ)
    (ε : ℚ) (n count : ℕ) :
    conditionPriceTokenRun ψCode ε (0, 0)
        ((List.range count).map fun j => tokenFn (Nat.pair n j)) =
      (EF.freezeTokenControlAt tokenFn n count,
        (List.range count).flatMap fun j =>
          conditionPriceTokenSegment tokenFn ψCode ε (Nat.pair n j)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.map_append, conditionPriceTokenRun_append, ih]
      simp [conditionPriceTokenRun, conditionPriceTokenSegment,
        conditionPriceTokenEmit, PrefixPatchCompile.freezeControlNat,
        EF.freezeTokenControlAt]
      by_cases hm0 : (EF.freezeTokenControlAt tokenFn n count).1 = 0 <;>
        by_cases hm1 : (EF.freezeTokenControlAt tokenFn n count).1 = 1 <;>
        by_cases hm2 : (EF.freezeTokenControlAt tokenFn n count).1 = 2 <;>
        simp [hm0, hm1, hm2]

private lemma streamReadFrom_rawConditionalPriceSuffix
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
    EF.conditionalRatioEF, EF.lowerSafeRecip, efMin]

/-- The parser state the rewrite produces: control unchanged, every stacked and traded
feature carrying `EF.retainedConditionPrices` in place of its prices. -/
private def retainedConditionStreamState (ψ : ℕ → Sentence) (ε : ℚ) :
    EF.StreamState → EF.StreamState
  | (control, stack, trades) =>
      (control, stack.map fun e => e.retainedConditionPrices ψ ε,
        trades.map fun trade => (trade.1.retainedConditionPrices ψ ε, trade.2))

-- One `simp` per parser mode and per stack shape: nine token tags times the stack cases
-- exceeds the default heartbeat budget.
set_option maxHeartbeats 800000 in
private lemma streamReadFrom_conditionPriceTokenEmit
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
                    EF.streamStep]
                rw [hday, streamReadFrom_rawConditionalPriceSuffix hdecode]
                rfl
              · intro next hnext
                simp [EF.streamStep] at hnext
                subst next
                simp [EF.freezeTokenNext]
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

private lemma streamReadFrom_conditionPriceTokenRun
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

private lemma deserializeTrades_conditionPriceTokenRun
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

lemma strategyOfTokens_conditionPriceTokenRun_trades
    (ψ : ℕ → Sentence) (ε : ℚ) (day : ℕ) (tokens : List ℕ) :
    (strategyOfTokens day
      (conditionPriceTokenRun (fun d => Encodable.encode (ψ d)) ε
        (0, 0) tokens).2).trades =
      (strategyOfTokens day tokens).trades.map fun trade =>
        (trade.1.retainedConditionPrices ψ ε, trade.2) := by
  have hdecode := deserializeTrades_conditionPriceTokenRun ψ ε tokens
  unfold strategyOfTokens
  simp only at hdecode
  rw [hdecode]
  cases hs : deserializeTrades tokens with
  | none => simp
  | some trades =>
      simp only [Option.map_some]
      have hrank :
          (∀ trade ∈ trades.map (fun trade =>
              (trade.1.retainedConditionPrices ψ ε, trade.2)),
              trade.1.rank ≤ day) ↔
            ∀ trade ∈ trades, trade.1.rank ≤ day := by
        constructor
        · intro h trade hmem
          simpa using h (trade.1.retainedConditionPrices ψ ε, trade.2)
            (List.mem_map_of_mem hmem)
        · intro h trade hmem
          simp only [List.mem_map] at hmem
          obtain ⟨source, hsource, rfl⟩ := hmem
          simpa using h source hsource
      by_cases hvalid : ∀ trade ∈ trades, trade.1.rank ≤ day
      · rw [dif_pos (hrank.mpr hvalid), dif_pos hvalid]
      · have hinvalid : ¬∀ trade ∈ trades.map (fun trade =>
            (trade.1.retainedConditionPrices ψ ε, trade.2)),
            trade.1.rank ≤ day := fun h => hvalid (hrank.mp h)
        rw [dif_neg hinvalid, dif_neg hvalid]
        rfl

/-! ### Price rewrite with exact finite zero-denominator exceptions -/

/-- One source-token segment of the prefix-safe rewrite.  A completed price leaf dated on
one of `zeroDays` is bound to the constant `1`; every other price leaf receives the ordinary
conditional-price body. -/
def zeroAwareConditionPriceTokenSegment
    (zeroDays : Finset ℕ) (tokenFn : ℕ → ℕ) (ψCode : ℕ → ℕ)
    (ε : ℚ) (z : ℕ) : List ℕ :=
  let control := PrefixPatchCompile.freezeControlNat tokenFn z
  let mode := control.unpair.1
  let pending := control.unpair.2
  let token := tokenFn z
  if mode = 0 then
    [token]
  else if mode = 1 then [token]
  else if mode = 2 then
    if token ∈ zeroDays then [token, 1, Encodable.encode (1 : ℚ), 8]
    else [token] ++
      rawConditionalPriceTokens pending (ψCode token) token ε ++ [8]
  else [token]

/-- `conditionPriceTokenEmit` with an exact branch on a finite set of days: a price on a
day in `zeroDays` becomes the constant `1` rather than the `ε`-capped ratio. -/
def zeroAwareConditionPriceTokenEmit
    (zeroDays : Finset ℕ) (ψCode : ℕ → ℕ) (ε : ℚ)
    (state : EF.FreezeTokenState) (token : ℕ) : List ℕ :=
  if state.1 = 2 then
    if token ∈ zeroDays then [token, 1, Encodable.encode (1 : ℚ), 8]
    else [token] ++ rawConditionalPriceTokens state.2 (ψCode token) token ε ++ [8]
  else [token]

/-- `zeroAwareConditionPriceTokenEmit` folded along a token list. -/
def zeroAwareConditionPriceTokenRun
    (zeroDays : Finset ℕ) (ψCode : ℕ → ℕ) (ε : ℚ) :
    EF.FreezeTokenState → List ℕ → EF.FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := zeroAwareConditionPriceTokenRun zeroDays ψCode ε
        (EF.freezeTokenNext state token) tokens
      (rest.1,
        zeroAwareConditionPriceTokenEmit zeroDays ψCode ε state token ++ rest.2)

private lemma zeroAwareConditionPriceTokenRun_append
    (zeroDays : Finset ℕ) (ψCode : ℕ → ℕ) (ε : ℚ)
    (state : EF.FreezeTokenState) (xs ys : List ℕ) :
    zeroAwareConditionPriceTokenRun zeroDays ψCode ε state (xs ++ ys) =
      let first := zeroAwareConditionPriceTokenRun zeroDays ψCode ε state xs
      let second :=
        zeroAwareConditionPriceTokenRun zeroDays ψCode ε first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons token tokens ih =>
      simp only [List.cons_append, zeroAwareConditionPriceTokenRun]
      rw [ih]
      simp [List.append_assoc]

lemma zeroAwareConditionPriceTokenRun_range
    (zeroDays : Finset ℕ) (tokenFn : ℕ → ℕ) (ψCode : ℕ → ℕ)
    (ε : ℚ) (n count : ℕ) :
    zeroAwareConditionPriceTokenRun zeroDays ψCode ε (0, 0)
        ((List.range count).map fun j => tokenFn (Nat.pair n j)) =
      (EF.freezeTokenControlAt tokenFn n count,
        (List.range count).flatMap fun j =>
          zeroAwareConditionPriceTokenSegment
            zeroDays tokenFn ψCode ε (Nat.pair n j)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.map_append,
        zeroAwareConditionPriceTokenRun_append, ih]
      simp [zeroAwareConditionPriceTokenRun,
        zeroAwareConditionPriceTokenSegment,
        zeroAwareConditionPriceTokenEmit,
        PrefixPatchCompile.freezeControlNat, EF.freezeTokenControlAt]
      by_cases hm0 : (EF.freezeTokenControlAt tokenFn n count).1 = 0 <;>
        by_cases hm1 : (EF.freezeTokenControlAt tokenFn n count).1 = 1 <;>
        by_cases hm2 : (EF.freezeTokenControlAt tokenFn n count).1 = 2 <;>
        by_cases hz : tokenFn (Nat.pair n count) ∈ zeroDays <;>
        simp [hm0, hm1, hm2, hz]

private lemma streamReadFrom_rawConstantOneSuffix
    {φ : Sentence} (day : ℕ) (stack : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom [1, Encodable.encode (1 : ℚ), 8]
        (some ((0, none), (EF.price φ day :: stack, trades))) =
      some ((0, none),
        (EF.letE (EF.price φ day) (EF.const 1) :: stack, trades)) := by
  simp [EF.streamReadFrom, EF.streamStep, Encodable.encodek]

private lemma streamReadFrom_rawConditionalPriceSuffix_exceptZero
    {phiCode : ℕ} {φ ψ : Sentence}
    (hφ : Encodable.decode (α := Sentence) phiCode = some φ)
    (zeroDays : Finset ℕ) {day : ℕ} (hday : day ∉ zeroDays)
    (ε : ℚ) (stack : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (rawConditionalPriceTokens phiCode (Encodable.encode ψ) day ε ++ [8])
        (some ((0, none), (EF.price φ day :: stack, trades))) =
      some ((0, none),
        (EF.retainedConditionPricesExceptZero
            zeroDays (fun _ => ψ) ε (EF.price φ day) ::
          stack, trades)) := by
  simpa [EF.retainedConditionPricesExceptZero, hday,
    EF.retainedConditionPrices] using
    (streamReadFrom_rawConditionalPriceSuffix hφ day ε stack trades)

/-- The parser state the zero-aware rewrite produces, carrying
`EF.retainedConditionPricesExceptZero`. -/
private def retainedConditionExceptZeroStreamState
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ) :
    EF.StreamState → EF.StreamState
  | (control, stack, trades) =>
      (control,
        stack.map fun e =>
          e.retainedConditionPricesExceptZero zeroDays ψ ε,
        trades.map fun trade =>
          (trade.1.retainedConditionPricesExceptZero zeroDays ψ ε, trade.2))

-- Same mode-by-tag-by-stack case split as the unguarded emitter, with the extra zero-day
-- branch on top; the default heartbeat budget does not cover it.
set_option maxHeartbeats 800000 in
private lemma streamReadFrom_zeroAwareConditionPriceTokenEmit
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ)
    (control : EF.FreezeTokenState) (state : EF.StreamState) (token : ℕ)
    (hmatch : control.Matches state) :
    EF.streamReadFrom
        (zeroAwareConditionPriceTokenEmit zeroDays
          (fun day => Encodable.encode (ψ day)) ε control token)
        (some (retainedConditionExceptZeroStreamState zeroDays ψ ε state)) =
      (EF.streamStep (some state) token).map
        (retainedConditionExceptZeroStreamState zeroDays ψ ε) ∧
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
        simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionExceptZeroStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h1 : token = 1
      · subst token
        simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionExceptZeroStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h2 : token = 2
      · subst token
        cases stack with
        | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionExceptZeroStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [zeroAwareConditionPriceTokenEmit,
              EF.freezeTokenNext, retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPricesExceptZero]
      by_cases h3 : token = 3
      · subst token
        cases stack with
        | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionExceptZeroStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [zeroAwareConditionPriceTokenEmit,
              EF.freezeTokenNext, retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPricesExceptZero]
      by_cases h4 : token = 4
      · subst token
        cases stack with
        | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionExceptZeroStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [zeroAwareConditionPriceTokenEmit,
              EF.freezeTokenNext, retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPricesExceptZero]
      by_cases h5 : token = 5
      · subst token
        cases stack <;> simp [zeroAwareConditionPriceTokenEmit,
          EF.freezeTokenNext, retainedConditionExceptZeroStreamState,
          EF.streamReadFrom, EF.streamStep,
          EF.retainedConditionPricesExceptZero]
      by_cases h6 : token = 6
      · subst token
        simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionExceptZeroStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h7 : token = 7
      · subst token
        simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionExceptZeroStreamState,
          EF.streamReadFrom, EF.streamStep]
      by_cases h8 : token = 8
      · subst token
        cases stack with
        | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
            retainedConditionExceptZeroStreamState,
            EF.streamReadFrom, EF.streamStep]
        | cons a stack =>
          cases stack with
          | nil => simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep]
          | cons b stack => simp [zeroAwareConditionPriceTokenEmit,
              EF.freezeTokenNext, retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep,
              EF.retainedConditionPricesExceptZero]
      · simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
          retainedConditionExceptZeroStreamState,
          EF.streamReadFrom, EF.streamStep,
          h0, h1, h2, h3, h4, h5, h6, h7, h8]
  | succ mode =>
      cases mode with
      | zero =>
          cases hdecode : Encodable.decode (α := Sentence) token <;>
            simp [zeroAwareConditionPriceTokenEmit, EF.freezeTokenNext,
              retainedConditionExceptZeroStreamState,
              EF.streamReadFrom, EF.streamStep, hdecode]
      | succ mode =>
          cases mode with
          | zero =>
              obtain ⟨φ, hpendingEq, hdecode⟩ := hpending rfl
              subst pending
              constructor
              · by_cases hzero : token ∈ zeroDays
                · rw [show zeroAwareConditionPriceTokenEmit zeroDays
                      (fun day => Encodable.encode (ψ day)) ε
                      (2, code) token =
                      [token] ++ [1, Encodable.encode (1 : ℚ), 8] by
                        simp [zeroAwareConditionPriceTokenEmit, hzero]]
                  rw [EF.streamReadFrom_append]
                  have hday : EF.streamReadFrom [token]
                      (some (retainedConditionExceptZeroStreamState
                        zeroDays ψ ε
                        ((2, some φ), (stack, trades)))) =
                      some ((0, none),
                        (EF.price φ token ::
                            stack.map (fun e =>
                              e.retainedConditionPricesExceptZero
                                zeroDays ψ ε),
                          trades.map fun trade =>
                            (trade.1.retainedConditionPricesExceptZero
                              zeroDays ψ ε, trade.2))) := by
                    simp [retainedConditionExceptZeroStreamState,
                      EF.streamReadFrom, EF.streamStep]
                  rw [hday, streamReadFrom_rawConstantOneSuffix]
                  simp [retainedConditionExceptZeroStreamState,
                    EF.retainedConditionPricesExceptZero, EF.streamStep, hzero]
                · rw [show zeroAwareConditionPriceTokenEmit zeroDays
                      (fun day => Encodable.encode (ψ day)) ε
                      (2, code) token =
                      [token] ++
                        (rawConditionalPriceTokens code
                          (Encodable.encode (ψ token)) token ε ++ [8]) by
                        simp [zeroAwareConditionPriceTokenEmit, hzero]]
                  rw [EF.streamReadFrom_append]
                  have hday : EF.streamReadFrom [token]
                      (some (retainedConditionExceptZeroStreamState
                        zeroDays ψ ε
                        ((2, some φ), (stack, trades)))) =
                      some ((0, none),
                        (EF.price φ token ::
                            stack.map (fun e =>
                              e.retainedConditionPricesExceptZero
                                zeroDays ψ ε),
                          trades.map fun trade =>
                            (trade.1.retainedConditionPricesExceptZero
                              zeroDays ψ ε, trade.2))) := by
                    simp [retainedConditionExceptZeroStreamState,
                      EF.streamReadFrom, EF.streamStep]
                  rw [hday,
                    streamReadFrom_rawConditionalPriceSuffix_exceptZero
                      hdecode zeroDays hzero]
                  rfl
              · intro next hnext
                simp [EF.streamStep] at hnext
                subst next
                simp [EF.freezeTokenNext]
          | succ mode =>
              cases mode with
              | zero =>
                  cases hdecode : Encodable.decode (α := ℚ) token <;>
                    simp [zeroAwareConditionPriceTokenEmit,
                      EF.freezeTokenNext,
                      retainedConditionExceptZeroStreamState,
                      EF.streamReadFrom, EF.streamStep, hdecode,
                      EF.retainedConditionPricesExceptZero]
              | succ mode =>
                  cases mode with
                  | zero =>
                      cases stack with
                      | nil => simp [zeroAwareConditionPriceTokenEmit,
                          EF.freezeTokenNext,
                          retainedConditionExceptZeroStreamState,
                          EF.streamReadFrom, EF.streamStep]
                      | cons e stack =>
                        cases hdecode :
                            Encodable.decode (α := Sentence) token <;>
                          simp [zeroAwareConditionPriceTokenEmit,
                            EF.freezeTokenNext,
                            retainedConditionExceptZeroStreamState,
                            EF.streamReadFrom, EF.streamStep, hdecode]
                  | succ mode =>
                      cases mode with
                      | zero => simp [zeroAwareConditionPriceTokenEmit,
                          EF.freezeTokenNext,
                          retainedConditionExceptZeroStreamState,
                          EF.streamReadFrom, EF.streamStep,
                          EF.retainedConditionPricesExceptZero]
                      | succ mode => simp [zeroAwareConditionPriceTokenEmit,
                          EF.freezeTokenNext,
                          retainedConditionExceptZeroStreamState,
                          EF.streamReadFrom, EF.streamStep]

private lemma streamReadFrom_zeroAwareConditionPriceTokenRun
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ)
    (control : EF.FreezeTokenState) (state : EF.StreamState)
    (tokens : List ℕ) (hmatch : control.Matches state) :
    let run := zeroAwareConditionPriceTokenRun zeroDays
      (fun day => Encodable.encode (ψ day)) ε control tokens
    EF.streamReadFrom run.2
        (some (retainedConditionExceptZeroStreamState zeroDays ψ ε state)) =
      (EF.streamReadFrom tokens (some state)).map
        (retainedConditionExceptZeroStreamState zeroDays ψ ε) ∧
      ∀ next, EF.streamReadFrom tokens (some state) = some next →
        run.1.Matches next := by
  induction tokens generalizing control state with
  | nil => simp [zeroAwareConditionPriceTokenRun,
      EF.streamReadFrom, hmatch]
  | cons token tokens ih =>
      simp only [zeroAwareConditionPriceTokenRun]
      have hstep := streamReadFrom_zeroAwareConditionPriceTokenEmit
        zeroDays ψ ε control state token hmatch
      rcases hstep with ⟨hstep, hnext⟩
      cases hs : EF.streamStep (some state) token with
      | none =>
          constructor
          · rw [EF.streamReadFrom_append, hstep, hs]
            simp only [Option.map_none]
            rw [EF.streamReadFrom_none]
            change none = (EF.streamReadFrom tokens
              (EF.streamStep (some state) token)).map
                (retainedConditionExceptZeroStreamState zeroDays ψ ε)
            rw [hs, EF.streamReadFrom_none]
            rfl
          · intro final hfinal
            change EF.streamReadFrom tokens
              (EF.streamStep (some state) token) = some final at hfinal
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

private lemma deserializeTrades_zeroAwareConditionPriceTokenRun
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ)
    (tokens : List ℕ) :
    let run := zeroAwareConditionPriceTokenRun zeroDays
      (fun day => Encodable.encode (ψ day)) ε (0, 0) tokens
    deserializeTrades run.2 =
      (deserializeTrades tokens).map fun trades =>
        trades.map fun trade =>
          (trade.1.retainedConditionPricesExceptZero zeroDays ψ ε, trade.2) := by
  have hrun := (streamReadFrom_zeroAwareConditionPriceTokenRun
    zeroDays ψ ε (0, 0) EF.streamInitial tokens
    EF.freezeToken_initial_matches).1
  simp only at hrun ⊢
  have hinitial :
      retainedConditionExceptZeroStreamState zeroDays ψ ε EF.streamInitial =
        EF.streamInitial := rfl
  rw [hinitial] at hrun
  unfold deserializeTrades
  rw [hrun]
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => rfl
  | some state =>
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
      cases mode <;> cases pending <;> cases stack <;>
        simp [retainedConditionExceptZeroStreamState]

lemma strategyOfTokens_zeroAwareConditionPriceTokenRun_trades
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ)
    (day : ℕ) (tokens : List ℕ) :
    (strategyOfTokens day
      (zeroAwareConditionPriceTokenRun zeroDays
        (fun d => Encodable.encode (ψ d)) ε (0, 0) tokens).2).trades =
      (strategyOfTokens day tokens).trades.map fun trade =>
        (trade.1.retainedConditionPricesExceptZero zeroDays ψ ε, trade.2) := by
  have hdecode :=
    deserializeTrades_zeroAwareConditionPriceTokenRun zeroDays ψ ε tokens
  unfold strategyOfTokens
  simp only at hdecode
  rw [hdecode]
  cases hs : deserializeTrades tokens with
  | none => simp
  | some trades =>
      simp only [Option.map_some]
      have hrank :
          (∀ trade ∈ trades.map (fun trade =>
              (trade.1.retainedConditionPricesExceptZero
                zeroDays ψ ε, trade.2)),
              trade.1.rank ≤ day) ↔
            ∀ trade ∈ trades, trade.1.rank ≤ day := by
        constructor
        · intro h trade hmem
          simpa using h
            (trade.1.retainedConditionPricesExceptZero
              zeroDays ψ ε, trade.2)
            (List.mem_map_of_mem hmem)
        · intro h trade hmem
          simp only [List.mem_map] at hmem
          obtain ⟨source, hsource, rfl⟩ := hmem
          simpa using h source hsource
      by_cases hvalid : ∀ trade ∈ trades, trade.1.rank ≤ day
      · rw [dif_pos (hrank.mpr hvalid), dif_pos hvalid]
      · have hinvalid : ¬∀ trade ∈ trades.map (fun trade =>
            (trade.1.retainedConditionPricesExceptZero
              zeroDays ψ ε, trade.2)),
            trade.1.rank ≤ day := fun h => hvalid (hrank.mp h)
        rw [dif_neg hinvalid, dif_neg hvalid]
        rfl

/-! ## Two parser-transparent trade-frame passes -/

/-- Denominator of the per-trade conditioning budget: `(day+1)(day+2)·count`. -/
def frameBudgetDenominator (day count : ℕ) : ℕ :=
  (day + 1) * (day + 2) * count

/-- The per-trade conditioning budget `1 / ((day+1)(day+2)·count)`, and `0` for a strategy
with no trades (`frameBudget_eq` identifies it with `Strategy.localConditioningBudget`). -/
def frameBudget (day count : ℕ) : ℚ :=
  if count = 0 then 0 else (frameBudgetDenominator day count : ℚ) ⁻¹

/-- Raw rational code of `frameBudget day count` (`frameBudgetCode_exact`). -/
def frameBudgetCode (day count : ℕ) : ℕ :=
  if count = 0 then Encodable.encode (0 : ℚ)
  else Nat.pair 2 (frameBudgetDenominator day count)

/-- Raw rational code of `(frameBudget day count)⁻¹` (`frameInverseBudgetCode_exact`). -/
def frameInverseBudgetCode (day count : ℕ) : ℕ :=
  if count = 0 then Encodable.encode (0 : ℚ)
  else Nat.pair (2 * frameBudgetDenominator day count) 1

lemma frameBudgetCode_exact (day count : ℕ) :
    frameBudgetCode day count = Encodable.encode (frameBudget day count) := by
  by_cases hzero : count = 0
  · simp [frameBudgetCode, frameBudget, hzero]
  · have hpos : 0 < frameBudgetDenominator day count := by
      simp [frameBudgetDenominator]
      positivity
    simp [frameBudgetCode, frameBudget, hzero,
      encode_rat_inv_natCast hpos]

lemma frameInverseBudgetCode_exact (day count : ℕ) :
    frameInverseBudgetCode day count = Encodable.encode (frameBudget day count)⁻¹ := by
  by_cases hzero : count = 0
  · simp [frameInverseBudgetCode, frameBudget, hzero]
  · have hpos : 0 < frameBudgetDenominator day count := by
      simp [frameBudgetDenominator]
      positivity
    simp [frameInverseBudgetCode, frameBudget, hzero,
      encode_rat_natCast]

lemma frameBudgetCodes_polyFueled
    {day count : ℕ → ℕ} {cd cc : Nat.Partrec.Code}
    (hday : PolyFueled cd day) (hcount : PolyFueled cc count) :
    (∃ c, PolyFueled c (fun z => frameBudgetCode (day z) (count z))) ∧
      ∃ c, PolyFueled c (fun z => frameInverseBudgetCode (day z) (count z)) := by
  obtain ⟨cadd, hadd⟩ := addc_polyFueled
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  have hday1 := hday.succ_comp
  have hday2 := hday1.succ_comp
  have hden : PolyFueled _ (fun z => frameBudgetDenominator (day z) (count z)) :=
    (hmul.comp ((hmul.comp (hday1.pair hday2)).pair hcount)).of_eq fun z => by
      simp [frameBudgetDenominator]
  have hbudgetPositive : PolyFueled _ (fun z =>
      Nat.pair 2 (frameBudgetDenominator (day z) (count z))) :=
    (PolyFueled.const 2).pair hden
  have htwice : PolyFueled _ (fun z =>
      2 * frameBudgetDenominator (day z) (count z)) :=
    (hmul.comp ((PolyFueled.const 2).pair hden)).of_eq fun z => by
      simp only [Nat.unpair_pair]
  have hinversePositive : PolyFueled _ (fun z =>
      Nat.pair (2 * frameBudgetDenominator (day z) (count z)) 1) :=
    htwice.pair (PolyFueled.const 1)
  obtain ⟨cb, hb⟩ := PrefixPatchCompile.polyFueled_ifZero hcount
    (PolyFueled.const (Encodable.encode (0 : ℚ))) hbudgetPositive
  obtain ⟨ci, hi⟩ := PrefixPatchCompile.polyFueled_ifZero hcount
    (PolyFueled.const (Encodable.encode (0 : ℚ))) hinversePositive
  exact ⟨⟨cb, hb.of_eq fun z => by simp [frameBudgetCode]⟩,
    ⟨ci, hi.of_eq fun z => by simp [frameInverseBudgetCode]⟩⟩

lemma frameBudget_eq (day count : ℕ) (hcount : 0 < count) :
    frameBudget day count =
      Strategy.localConditioningBudget (conditioningBudget day) count := by
  have hpos : 0 < frameBudgetDenominator day count := by
    simp [frameBudgetDenominator]
    positivity
  have hden : (frameBudgetDenominator day count : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpos
  simp [frameBudget, frameBudgetDenominator, Strategy.localConditioningBudget,
    conditioningBudget, Nat.ne_of_gt hcount, div_eq_mul_inv]
  ring

/-- Per-token output of one frame pass.  A frame marker read in the ready mode is dropped;
at a trade frame (mode `4`) the leg's body is substituted and the frame re-emitted over
`φ ⋏ ψ` on the first leg and over `ψ` on the second; every other token passes through. -/
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

/-- `conditioningFrameTokenEmit` folded along a token list. -/
def conditioningFrameTokenRun (second : Bool) (ψCode : ℕ)
    (day : ℕ) (ε : ℚ) (budgetCode inverseBudgetCode : ℕ) :
    EF.FreezeTokenState → List ℕ → EF.FreezeTokenState × List ℕ
  | state, [] => (state, [])
  | state, token :: tokens =>
      let rest := conditioningFrameTokenRun second ψCode day ε
        budgetCode inverseBudgetCode (EF.freezeTokenNext state token) tokens
      (rest.1, conditioningFrameTokenEmit second ψCode day ε
        budgetCode inverseBudgetCode state token ++ rest.2)

private lemma conditioningFrameTokenRun_append (second : Bool) (ψCode day : ℕ)
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

/-- The first (β) leg's frame body: the conditional ratio bound by `letE`, returning the
gated bound `min bound (bound · gate)` at budget `q`. -/
private def firstFrameBody (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (φ : Sentence) : EF :=
  let ratio := EF.conditionalRatioEF ψ ε φ day
  let boundRatio := EF.var 0
  let bound := EF.var 1
  let gate := EF.conditioningCapGate boundRatio (EF.absVal bound) q
  efMin bound (EF.mul bound gate)
  |> EF.letE ratio

/-- The second leg's frame body: the same binding, returning `-(β · ratio)`. -/
private def secondFrameBody (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (φ : Sentence) : EF :=
  let ratio := EF.conditionalRatioEF ψ ε φ day
  let boundRatio := EF.var 0
  let bound := EF.var 1
  let gate := EF.conditioningCapGate boundRatio (EF.absVal bound) q
  let beta := efMin bound (EF.mul bound gate)
  EF.letE ratio (EF.mul (EF.const (-1)) (EF.mul beta boundRatio))

private lemma streamReadFrom_rawFirstFrame
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

private lemma streamReadFrom_rawSecondFrame
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
  simp [rawLocallyGatedSecondBodyTokens,
    rawConditioningRatioTokens, rawConditioningGateTokens, rawAbsTokens,
    rawClip01Tokens, rawPriceTokens, rawConstTokens, rawAddTokens, rawMulTokens,
    rawMaxTokens, rawSafeRecipTokens, rawMinTokens, rawLowerSafeRecipTokens,
    EF.streamReadFrom, EF.streamStep, conjunctionCode_decode hφ,
    Encodable.encodek, secondFrameBody,
    EF.conditioningCapGate, EF.conditioningTolerance, EF.absVal,
    EF.conditionalRatioEF, EF.lowerSafeRecip, clip01, efMin]

private lemma streamRead_rawConditioningRatio_none {sentenceCode : ℕ} {ψ : Sentence}
    (hdecode : Encodable.decode (α := Sentence) sentenceCode = none)
    (day : ℕ) (ε : ℚ) (stack : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (rawConditioningRatioTokens sentenceCode (Encodable.encode ψ) day ε)
        (some ((0, none), (stack, trades))) = none := by
  apply streamRead_append_none
  apply streamRead_append_none
  exact streamRead_rawPrice_none (conjunctionCode_decode_none hdecode) day stack trades

-- The β body is a deep `++` nest over the raw combinators; associating it for the rewrite
-- exceeds the default heartbeat budget.
set_option maxHeartbeats 800000 in
private lemma streamRead_rawFirstBody_none {sentenceCode : ℕ} {ψ : Sentence}
    (hdecode : Encodable.decode (α := Sentence) sentenceCode = none)
    (day : ℕ) (ε q : ℚ) (stack : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (rawLocallyGatedBetaBodyTokens sentenceCode (Encodable.encode ψ) day
          (Encodable.encode q) (Encodable.encode q⁻¹) ε)
        (some ((0, none), (stack, trades))) = none := by
  rw [rawLocallyGatedBetaBodyTokens, EF.streamReadFrom_append,
    EF.streamReadFrom_append,
    streamRead_rawConditioningRatio_none hdecode, EF.streamReadFrom_none,
    EF.streamReadFrom_none]

-- As for the β body: a deep `++` nest whose reassociation exceeds the default budget.
set_option maxHeartbeats 800000 in
private lemma streamRead_rawSecondBody_none {sentenceCode : ℕ} {ψ : Sentence}
    (hdecode : Encodable.decode (α := Sentence) sentenceCode = none)
    (day : ℕ) (ε q : ℚ) (stack : List EF) (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (rawLocallyGatedSecondBodyTokens sentenceCode (Encodable.encode ψ) day
          (Encodable.encode q) (Encodable.encode q⁻¹) ε)
        (some ((0, none), (stack, trades))) = none := by
  rw [rawLocallyGatedSecondBodyTokens, EF.streamReadFrom_append,
    EF.streamReadFrom_append,
    streamRead_rawConditioningRatio_none hdecode, EF.streamReadFrom_none,
    EF.streamReadFrom_none]

-- The decodable branch simps the whole frame body — every raw combinator unfolded at once
-- against the streaming parser — which does not fit the default budget.
set_option maxHeartbeats 800000 in
private lemma streamRead_rawFrame_empty (second : Bool) (sentenceCode : ℕ)
    (ψ : Sentence) (day : ℕ) (ε q : ℚ) (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (if second then
          rawLocallyGatedSecondBodyTokens sentenceCode (Encodable.encode ψ) day
              (Encodable.encode q) (Encodable.encode q⁻¹) ε ++
            [8, 6, Encodable.encode ψ]
        else
          rawLocallyGatedBetaBodyTokens sentenceCode (Encodable.encode ψ) day
              (Encodable.encode q) (Encodable.encode q⁻¹) ε ++
            [8, 6, conjunctionCode sentenceCode (Encodable.encode ψ)])
        (some ((0, none), ([], trades))) = none := by
  cases hdecode : Encodable.decode (α := Sentence) sentenceCode with
  | none =>
      cases second
      · rw [if_neg (by simp), EF.streamReadFrom_append,
          streamRead_rawFirstBody_none hdecode, EF.streamReadFrom_none]
      · rw [if_pos (by simp), EF.streamReadFrom_append,
          streamRead_rawSecondBody_none hdecode, EF.streamReadFrom_none]
  | some φ =>
      cases second <;>
        simp [rawLocallyGatedSecondBodyTokens, rawLocallyGatedBetaBodyTokens,
          rawConditioningRatioTokens, rawConditioningGateTokens, rawAbsTokens,
          rawClip01Tokens, rawPriceTokens, rawConstTokens, rawAddTokens,
          rawMulTokens, rawMaxTokens, rawSafeRecipTokens, rawMinTokens,
          rawLowerSafeRecipTokens, EF.streamReadFrom, EF.streamStep,
          conjunctionCode_decode hdecode, Encodable.encodek]

private lemma streamRead_rawFrame_invalid (second : Bool) {sentenceCode : ℕ}
    (hdecode : Encodable.decode (α := Sentence) sentenceCode = none)
    (ψ : Sentence) (day : ℕ) (ε q : ℚ) (e : EF) (stack : List EF)
    (trades : List (EF × Sentence)) :
    EF.streamReadFrom
        (if second then
          rawLocallyGatedSecondBodyTokens sentenceCode (Encodable.encode ψ) day
              (Encodable.encode q) (Encodable.encode q⁻¹) ε ++
            [8, 6, Encodable.encode ψ]
        else
          rawLocallyGatedBetaBodyTokens sentenceCode (Encodable.encode ψ) day
              (Encodable.encode q) (Encodable.encode q⁻¹) ε ++
            [8, 6, conjunctionCode sentenceCode (Encodable.encode ψ)])
        (some ((0, none), (e :: stack, trades))) = none := by
  cases second
  · rw [if_neg (by simp), EF.streamReadFrom_append,
      streamRead_rawFirstBody_none hdecode, EF.streamReadFrom_none]
  · rw [if_pos (by simp), EF.streamReadFrom_append,
      streamRead_rawSecondBody_none hdecode, EF.streamReadFrom_none]

/-- One frame pass applied to a single trade: the first leg buys `φ ⋏ ψ` with the gated
coefficient, the second leg sells `ψ` with the negated body. -/
def frameLeg (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (p : EF × Sentence) : EF × Sentence :=
  if second then (EF.letE p.1 (secondFrameBody ψ ε q day p.2), ψ)
  else (EF.letE p.1 (firstFrameBody ψ ε q day p.2), p.2 ⋏ ψ)

/-- The parser state one frame pass produces: pending frame control is cleared and every
trade is rewritten by `frameLeg`. -/
private def frameStreamState (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ) :
    EF.StreamState → EF.StreamState
  | ((mode, pending), stack, trades) =>
      ((if mode = 4 then 0 else mode,
          if mode = 4 ∨ mode = 0 then none else pending),
        stack, trades.map (frameLeg second ψ ε q day))

-- The largest case split in the file: every parser mode against every token tag, and the
-- mode-4 branch additionally unfolds a full frame body.  Needs a large heartbeat budget.
set_option maxHeartbeats 3000000 in
private lemma streamReadFrom_conditioningFrameTokenEmit
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
                EF.streamReadFrom, EF.streamStep]
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
                          cases hdecode : Encodable.decode (α := Sentence) token
                          · constructor
                            · cases second with
                              | false =>
                                  simpa [conditioningFrameTokenEmit, frameStreamState,
                                    EF.streamStep, hdecode] using
                                    streamRead_rawFrame_empty false token ψ day ε q
                                      (trades.map (frameLeg false ψ ε q day))
                              | true =>
                                  simpa [conditioningFrameTokenEmit, frameStreamState,
                                    EF.streamStep, hdecode] using
                                    streamRead_rawFrame_empty true token ψ day ε q
                                      (trades.map (frameLeg true ψ ε q day))
                            · intro next hnext
                              simp [EF.streamStep] at hnext
                          · constructor
                            · cases second with
                              | false =>
                                  simpa [conditioningFrameTokenEmit, frameStreamState,
                                    EF.streamStep, hdecode] using
                                    streamRead_rawFrame_empty false token ψ day ε q
                                      (trades.map (frameLeg false ψ ε q day))
                              | true =>
                                  simpa [conditioningFrameTokenEmit, frameStreamState,
                                    EF.streamStep, hdecode] using
                                    streamRead_rawFrame_empty true token ψ day ε q
                                      (trades.map (frameLeg true ψ ε q day))
                            · intro next hnext
                              simp [EF.streamStep] at hnext
                      | cons e stack =>
                          cases hdecode : Encodable.decode (α := Sentence) token with
                          | none =>
                              constructor
                              · simpa [conditioningFrameTokenEmit, frameStreamState,
                                  EF.streamStep, hdecode] using
                                  streamRead_rawFrame_invalid second (sentenceCode := token)
                                    hdecode ψ day ε q e
                                    stack (trades.map (frameLeg second ψ ε q day))
                              · intro next hnext
                                simp [EF.streamStep, hdecode] at hnext
                          | some φ =>
                              constructor
                              · cases second with
                                | false =>
                                    simpa [conditioningFrameTokenEmit, frameStreamState,
                                      frameLeg, EF.streamStep, hdecode,
                                      List.map_append] using streamReadFrom_rawFirstFrame
                                        (ψ := ψ) hdecode day ε q e stack
                                        (trades.map (frameLeg false ψ ε q day))
                                | true =>
                                    simpa [conditioningFrameTokenEmit, frameStreamState,
                                      frameLeg, EF.streamStep, hdecode,
                                      List.map_append] using streamReadFrom_rawSecondFrame
                                        (ψ := ψ) hdecode day ε q e stack
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

private lemma streamReadFrom_conditioningFrameTokenRun
    (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ)
    (control : EF.FreezeTokenState) (state : EF.StreamState) (tokens : List ℕ)
    (hmatch : control.Matches state) :
    let run := conditioningFrameTokenRun second (Encodable.encode ψ) day ε
      (Encodable.encode q) (Encodable.encode q⁻¹) control tokens
    EF.streamReadFrom run.2 (some (frameStreamState second ψ ε q day state)) =
        (EF.streamReadFrom tokens (some state)).map
          (frameStreamState second ψ ε q day) ∧
      ∀ next, EF.streamReadFrom tokens (some state) = some next →
        run.1.Matches next := by
  induction tokens generalizing control state with
  | nil => simp [conditioningFrameTokenRun, EF.streamReadFrom, hmatch]
  | cons token tokens ih =>
      simp only [conditioningFrameTokenRun]
      have hstep := streamReadFrom_conditioningFrameTokenEmit
        second ψ ε q day control state token hmatch
      rcases hstep with ⟨hstep, hnext⟩
      cases hs : EF.streamStep (some state) token with
      | none =>
          constructor
          · rw [EF.streamReadFrom_append, hstep, hs]
            simp only [Option.map_none]
            rw [EF.streamReadFrom_none]
            change none = (EF.streamReadFrom tokens
              (EF.streamStep (some state) token)).map
                (frameStreamState second ψ ε q day)
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

/-- A successful run of the flat decoder never carries a pending sentence while it is in
the ready mode.  The framing map normalizes that unreachable component, so this invariant
is what prevents a malformed source stream from being accidentally repaired. -/
private def readyPendingInvariant (state : EF.StreamState) : Prop :=
  state.1.1 = 0 → state.1.2 = none

private lemma streamStep_readyPendingInvariant
    (state next : EF.StreamState) (token : ℕ)
    (hinv : readyPendingInvariant state)
    (hstep : EF.streamStep (some state) token = some next) :
    readyPendingInvariant next := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  rcases next with ⟨⟨nextMode, nextPending⟩, ⟨nextStack, nextTrades⟩⟩
  simp only [EF.streamStep] at hstep
  repeat' split at hstep
  all_goals aesop (add simp [readyPendingInvariant])

private lemma streamReadFrom_readyPendingInvariant_from
    (tokens : List ℕ) (initial final : EF.StreamState)
    (hinv : readyPendingInvariant initial)
    (hread : EF.streamReadFrom tokens (some initial) = some final) :
    readyPendingInvariant final := by
  induction tokens generalizing initial final with
  | nil =>
      change some initial = some final at hread
      injection hread with heq
      subst final
      exact hinv
  | cons token tokens ih =>
      change EF.streamReadFrom tokens (EF.streamStep (some initial) token) =
        some final at hread
      cases hstep : EF.streamStep (some initial) token with
      | none =>
          rw [hstep] at hread
          rw [EF.streamReadFrom_none] at hread
          contradiction
      | some next =>
          rw [hstep] at hread
          apply ih next final
            (streamStep_readyPendingInvariant initial next token hinv hstep)
          exact hread

private lemma streamReadFrom_readyPendingInvariant
    (tokens : List ℕ) (state : EF.StreamState)
    (hread : EF.streamReadFrom tokens (some EF.streamInitial) = some state) :
    readyPendingInvariant state :=
  streamReadFrom_readyPendingInvariant_from tokens EF.streamInitial state
    (by simp [readyPendingInvariant, EF.streamInitial]) hread

/-- Flush an unfinished source trade tag.  The frame pass withholds token `6` until it sees
the sentence; re-emitting it at end-of-stream preserves rejection of a truncated frame. -/
def conditioningFrameTokenOutput (second : Bool) (ψCode day : ℕ) (ε : ℚ)
    (budgetCode inverseBudgetCode : ℕ) (tokens : List ℕ) : List ℕ :=
  let run := conditioningFrameTokenRun second ψCode day ε
    budgetCode inverseBudgetCode (0, 0) tokens
  run.2 ++ if run.1.1 = 4 then [6] else []

-- Runs the whole framing pass, plus its flush suffix, through the streaming parser in one
-- proof; the default heartbeat budget is not enough.
set_option maxHeartbeats 1000000 in
lemma deserializeTrades_conditioningFrameTokenRun
    (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ) (tokens : List ℕ) :
    deserializeTrades
      (conditioningFrameTokenOutput second (Encodable.encode ψ) day ε
        (Encodable.encode q) (Encodable.encode q⁻¹) tokens) =
      (deserializeTrades tokens).map fun trades =>
        trades.map (frameLeg second ψ ε q day) := by
  have hrunFull := streamReadFrom_conditioningFrameTokenRun second ψ ε q day
    (0, 0) EF.streamInitial tokens EF.freezeToken_initial_matches
  simp only at hrunFull ⊢
  rcases hrunFull with ⟨hrun, hmatches⟩
  have hinitial : frameStreamState second ψ ε q day EF.streamInitial =
      EF.streamInitial := rfl
  rw [hinitial] at hrun
  unfold deserializeTrades
  simp only [conditioningFrameTokenOutput, EF.streamReadFrom_append]
  rw [hrun]
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => simp [EF.streamReadFrom_none]
  | some state =>
      have hinv := streamReadFrom_readyPendingInvariant tokens state hread
      have hcontrol := hmatches state hread
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
      cases mode with
      | zero =>
          cases pending <;> cases stack <;>
            simp_all [frameStreamState, readyPendingInvariant,
              EF.FreezeTokenState.Matches, EF.streamReadFrom]
      | succ mode =>
          cases pending <;> cases stack <;>
            (by_cases hfour : mode = 3) <;>
            simp_all [frameStreamState, readyPendingInvariant,
              EF.FreezeTokenState.Matches, EF.streamReadFrom, EF.streamStep]

/-- The frame rewrite preserves a trade's rank, so it preserves day-validity of a
strategy. -/
private lemma frameLeg_rank_le_iff (second : Bool) (ψ : Sentence) (ε q : ℚ)
    (day : ℕ) (p : EF × Sentence) :
    (frameLeg second ψ ε q day p).1.rank ≤ day ↔ p.1.rank ≤ day := by
  cases second <;>
    simp [frameLeg, firstFrameBody, secondFrameBody,
      EF.conditioningCapGate_rank, EF.conditionalRatioEF,
      EF.lowerSafeRecip, EF.absVal, efMin, EF.rank]

/-! ### Concatenating independently compiled strategy streams -/

/-- Add already-decoded trades to the front of a streaming parser state. -/
private def prependStreamTrades (prior : List (EF × Sentence)) :
    EF.StreamState → EF.StreamState
  | ((mode, pending), (stack, trades)) =>
      ((mode, pending), (stack, prior ++ trades))

/-- The one-token parser is equivariant under adding a fixed prefix of completed trades. -/
private lemma streamStep_prependStreamTrades (prior : List (EF × Sentence))
    (state : EF.StreamState) (token : ℕ) :
    EF.streamStep (some (prependStreamTrades prior state)) token =
      (EF.streamStep (some state) token).map (prependStreamTrades prior) := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  by_cases h0 : mode = 0
  · subst mode
    simp only [prependStreamTrades, EF.streamStep, if_pos]
    by_cases ht0 : token = 0
    · simp [ht0, prependStreamTrades]
    by_cases ht1 : token = 1
    · simp [ht1, prependStreamTrades]
    by_cases ht2 : token = 2
    · rcases stack with _ | ⟨a, stack⟩
      · simp [ht2]
      · rcases stack with _ | ⟨b, rest⟩ <;>
          simp [ht2, prependStreamTrades]
    by_cases ht3 : token = 3
    · rcases stack with _ | ⟨a, stack⟩
      · simp [ht3]
      · rcases stack with _ | ⟨b, rest⟩ <;>
          simp [ht3, prependStreamTrades]
    by_cases ht4 : token = 4
    · rcases stack with _ | ⟨a, stack⟩
      · simp [ht4]
      · rcases stack with _ | ⟨b, rest⟩ <;>
          simp [ht4, prependStreamTrades]
    by_cases ht5 : token = 5
    · rcases stack with _ | ⟨a, rest⟩ <;>
        simp [ht5, prependStreamTrades]
    by_cases ht6 : token = 6
    · simp [ht6, prependStreamTrades]
    by_cases ht7 : token = 7
    · simp [ht7,
        prependStreamTrades]
    by_cases ht8 : token = 8
    · rcases stack with _ | ⟨a, stack⟩
      · simp [ht8]
      · rcases stack with _ | ⟨b, rest⟩ <;>
          simp [ht8,
            prependStreamTrades]
    simp [ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8]
  · by_cases h1 : mode = 1
    · cases hdecode : Encodable.decode (α := Sentence) token <;>
        simp [EF.streamStep, h1, hdecode, prependStreamTrades]
    by_cases h2 : mode = 2
    · cases pending <;>
        simp [EF.streamStep, h2, prependStreamTrades]
    by_cases h3 : mode = 3
    · cases hdecode : Encodable.decode (α := ℚ) token <;>
        simp [EF.streamStep, h3, hdecode,
          prependStreamTrades]
    by_cases h4 : mode = 4
    · rcases stack with _ | ⟨a, rest⟩
      · simp [EF.streamStep, h4, prependStreamTrades]
      · cases hdecode : Encodable.decode (α := Sentence) token <;>
          simp [EF.streamStep, h4, hdecode,
            prependStreamTrades, List.append_assoc]
    by_cases h5 : mode = 5
    · simp [EF.streamStep, h5,
        prependStreamTrades]
    simp [EF.streamStep, h0, h1, h2, h3, h4, h5, prependStreamTrades]

/-- The same equivariance holds for an arbitrary suffix stream. -/
private lemma streamReadFrom_prependStreamTrades (prior : List (EF × Sentence))
    (tokens : List ℕ) (state : EF.StreamState) :
    EF.streamReadFrom tokens (some (prependStreamTrades prior state)) =
      (EF.streamReadFrom tokens (some state)).map
        (prependStreamTrades prior) := by
  induction tokens generalizing state with
  | nil => rfl
  | cons token rest ih =>
      change
        EF.streamReadFrom rest
            (EF.streamStep (some (prependStreamTrades prior state)) token) =
          (EF.streamReadFrom rest (EF.streamStep (some state) token)).map
            (prependStreamTrades prior)
      rw [streamStep_prependStreamTrades]
      cases hstep : EF.streamStep (some state) token with
      | none => simp
      | some next => simpa using ih next

/-- A successful trade-list decode exposes the exact accepting streaming state. -/
lemma streamReadFrom_eq_ready_of_deserializeTrades_eq_some
    (tokens : List ℕ) (trades : List (EF × Sentence))
    (hdecode : deserializeTrades tokens = some trades) :
    EF.streamReadFrom tokens (some EF.streamInitial) =
      some ((0, none), ([], trades)) := by
  unfold deserializeTrades at hdecode
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => simp [hread] at hdecode
  | some state =>
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, decoded⟩⟩
      simp only [hread] at hdecode
      split at hdecode
      next heq =>
        rcases heq with ⟨⟨rfl, rfl⟩, rfl, rfl⟩
        simpa using hdecode
      next heq => simp at hdecode

/-- Two independently valid streams concatenate to the concatenation of their trade lists. -/
private lemma deserializeTrades_append_of_some (left right : List ℕ)
    (first second : List (EF × Sentence))
    (hfirst : deserializeTrades left = some first)
    (hsecond : deserializeTrades right = some second) :
    deserializeTrades (left ++ right) = some (first ++ second) := by
  have hleft := streamReadFrom_eq_ready_of_deserializeTrades_eq_some left first hfirst
  have hright := streamReadFrom_eq_ready_of_deserializeTrades_eq_some right second hsecond
  unfold deserializeTrades
  rw [EF.streamReadFrom_append, hleft]
  rw [show some ((0, none), ([], first)) =
      some (prependStreamTrades first EF.streamInitial) from by
        simp [prependStreamTrades, EF.streamInitial]]
  rw [streamReadFrom_prependStreamTrades first right EF.streamInitial, hright]
  rfl

/-- Membership in a fixed finite set is polynomial for every polynomial natural-valued
input.  The generated program is a fixed nest of equality tests, one per set element.  It is a
generic certificate fact rather than a conditioning one; its consumers are the zero-day
certificates in `RpnConditioning.lean` and `DigitConditioning.lean`. -/
lemma finsetMembership_polyFueled
    {cf : Nat.Partrec.Code} {f : ℕ → ℕ}
    (hf : PolyFueled cf f) (s : Finset ℕ) :
    ∃ c, PolyFueled c (fun z => if f z ∈ s then 1 else 0) := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨_, (PolyFueled.const 0).of_eq fun z => by simp⟩
  | @insert a s ha ih =>
      obtain ⟨ceq, heq⟩ := polyFueled_eqConst hf a
      obtain ⟨cmem, hmem⟩ := ih
      obtain ⟨cout, hout⟩ :=
        PrefixPatchCompile.polyFueled_ifZero
          heq hmem (PolyFueled.const 1)
      refine ⟨cout, hout.of_eq fun z => ?_⟩
      by_cases hfa : f z = a
      · simp [hfa]
      · simp [hfa, Finset.mem_insert]

/-- The long segment emitted at a completed trade frame is a fixed-width polynomial token
stream in its five varying numeric fields. -/
private lemma rawConditioningFrameTokens_poly
    {sentence condition day budget inverse : ℕ → ℕ}
    {cs cc cd cb ci : Nat.Partrec.Code}
    (hsentence : PolyFueled cs sentence) (hcondition : PolyFueled cc condition)
    (hday : PolyFueled cd day) (hbudget : PolyFueled cb budget)
    (hinverse : PolyFueled ci inverse) (second : Bool) (ε : ℚ) :
    PolySegStream (fun z =>
      if second then
        rawLocallyGatedSecondBodyTokens (sentence z) (condition z) (day z)
            (budget z) (inverse z) ε ++ [8, 6, condition z]
      else
        rawLocallyGatedBetaBodyTokens (sentence z) (condition z) (day z)
            (budget z) (inverse z) ε ++
          [8, 6, conjunctionCode (sentence z) (condition z)]) := by
  obtain ⟨cadd, haddNat⟩ := addc_polyFueled
  have hconj : PolyFueled _ (fun z =>
      conjunctionCode (sentence z) (condition z)) :=
    (haddNat.comp
      (((PolyFueled.const 3).pair (hsentence.pair hcondition)).pair
        (PolyFueled.const 1))).of_eq fun z => by simp [conjunctionCode]
  have hconst (code : ℕ → ℕ) {c : Nat.Partrec.Code}
      (hcode : PolyFueled c code) :
      PolyTokenStream (fun z => rawConstTokens (code z)) :=
    (PolyTokenStream.const 1).append (PolyTokenStream.polyTok hcode)
  have hconstQ (q : ℚ) : PolyTokenStream (fun _ : ℕ =>
      rawConstTokens (Encodable.encode q)) :=
    hconst (fun _ => Encodable.encode q) (PolyFueled.const _)
  have hprice (scode d : ℕ → ℕ) {cscode cd' : Nat.Partrec.Code}
      (hscode : PolyFueled cscode scode) (hd : PolyFueled cd' d) :
      PolyTokenStream (fun z => rawPriceTokens (scode z) (d z)) :=
    ((PolyTokenStream.const 0).append (PolyTokenStream.polyTok hscode)).append
      (PolyTokenStream.polyTok hd)
  have hadd {a b : ℕ → List ℕ} (ha : PolyTokenStream a) (hb : PolyTokenStream b) :
      PolyTokenStream (fun z => rawAddTokens (a z) (b z)) :=
    (ha.append hb).append (PolyTokenStream.const 2)
  have hmul {a b : ℕ → List ℕ} (ha : PolyTokenStream a) (hb : PolyTokenStream b) :
      PolyTokenStream (fun z => rawMulTokens (a z) (b z)) :=
    (ha.append hb).append (PolyTokenStream.const 3)
  have hmax {a b : ℕ → List ℕ} (ha : PolyTokenStream a) (hb : PolyTokenStream b) :
      PolyTokenStream (fun z => rawMaxTokens (a z) (b z)) :=
    (ha.append hb).append (PolyTokenStream.const 4)
  have hsafe {a : ℕ → List ℕ} (ha : PolyTokenStream a) :
      PolyTokenStream (fun z => rawSafeRecipTokens (a z)) :=
    ha.append (PolyTokenStream.const 5)
  have hmin {a b : ℕ → List ℕ} (ha : PolyTokenStream a) (hb : PolyTokenStream b) :
      PolyTokenStream (fun z => rawMinTokens (a z) (b z)) :=
    hmul (hconstQ (-1))
      (hmax (hmul (hconstQ (-1)) ha) (hmul (hconstQ (-1)) hb))
  have habs {a : ℕ → List ℕ} (ha : PolyTokenStream a) :
      PolyTokenStream (fun z => rawAbsTokens (a z)) :=
    hmax ha (hmul (hconstQ (-1)) ha)
  have hclip {a : ℕ → List ℕ} (ha : PolyTokenStream a) :
      PolyTokenStream (fun z => rawClip01Tokens (a z)) :=
    hmax (hconstQ 0) (hmin (hconstQ 1) ha)
  let ratio : ℕ → List ℕ := fun z => rawConditioningRatioTokens
    (sentence z) (condition z) (day z) ε
  have hratio : PolyTokenStream ratio := by
    have hnum := hprice (fun z => conjunctionCode (sentence z) (condition z)) day
      hconj hday
    have hden := hprice condition day hcondition hday
    exact hmul hnum
      (hmul (hconstQ (1 / ε)) (hsafe (hmul (hconstQ (1 / ε)) hden)))
  let boundRatio : ℕ → List ℕ := fun _ => [7, 0]
  let bound : ℕ → List ℕ := fun _ => [7, 1]
  have hboundRatio : PolyTokenStream boundRatio :=
    (PolyTokenStream.const 7).append (PolyTokenStream.const 0)
  have hbound : PolyTokenStream bound :=
    (PolyTokenStream.const 7).append (PolyTokenStream.const 1)
  let gate : ℕ → List ℕ := fun z => rawConditioningGateTokens
    (boundRatio z) (rawAbsTokens (bound z)) (budget z) (inverse z)
  have hgate : PolyTokenStream gate := by
    let magnitude : ℕ → List ℕ := fun z => rawAbsTokens (bound z)
    have hmagnitude : PolyTokenStream magnitude := habs hbound
    have hmaxMag := hmax (hconstQ 1) hmagnitude
    have htolerance := hmul (hconst budget hbudget) (hsafe hmagnitude)
    have hshift := hadd (hadd (hconstQ 1) htolerance)
      (hmul (hconstQ (-1)) hboundRatio)
    exact hclip (hmul hshift (hmul (hconst inverse hinverse) hmaxMag))
  let betaCore : ℕ → List ℕ := fun z =>
    rawMinTokens (bound z) (rawMulTokens (bound z) (gate z))
  have hbetaCore : PolyTokenStream betaCore := hmin hbound (hmul hbound hgate)
  have hfirstBody : PolyTokenStream (fun z =>
      rawLocallyGatedBetaBodyTokens (sentence z) (condition z) (day z)
        (budget z) (inverse z) ε) :=
    (hratio.append hbetaCore).append (PolyTokenStream.const 8)
  have hsecondBody : PolyTokenStream (fun z =>
      rawLocallyGatedSecondBodyTokens (sentence z) (condition z) (day z)
        (budget z) (inverse z) ε) :=
    (hratio.append
      (hmul (hconstQ (-1)) (hmul hbetaCore hboundRatio))).append
        (PolyTokenStream.const 8)
  have hfirst := ((hfirstBody.append (PolyTokenStream.const 8)).append
      (PolyTokenStream.const 6)).append (PolyTokenStream.polyTok hconj)
  have hsecond := ((hsecondBody.append (PolyTokenStream.const 8)).append
      (PolyTokenStream.const 6)).append (PolyTokenStream.polyTok hcondition)
  cases second
  · exact PolySegStream.of_eq (PolySegStream.ofTokenStream hfirst) fun z => by
      simp [rawLocallyGatedBetaBodyTokens, rawConditioningRatioTokens,
        rawConditioningGateTokens, rawAbsTokens, rawClip01Tokens,
        rawLowerSafeRecipTokens, rawPriceTokens, rawConstTokens, rawAddTokens,
        rawMulTokens, rawMaxTokens, rawSafeRecipTokens, rawMinTokens]
  · exact PolySegStream.of_eq (PolySegStream.ofTokenStream hsecond) fun z => by
      simp [rawLocallyGatedSecondBodyTokens, rawConditioningRatioTokens,
        rawConditioningGateTokens, rawAbsTokens, rawClip01Tokens,
        rawLowerSafeRecipTokens, rawPriceTokens, rawConstTokens, rawAddTokens,
        rawMulTokens, rawMaxTokens, rawSafeRecipTokens, rawMinTokens]

/-- The frame pass at a single source index, addressed through the shallow control scan.
`conditioningFrameTokenRun_range` folds these segments into the whole rewritten run. -/
def conditioningFrameTokenSegment (second : Bool) (tokenFn : ℕ → ℕ)
    (ψCode day budgetCode inverseBudgetCode : ℕ) (ε : ℚ)
    (z : ℕ) : List ℕ :=
  let control := PrefixPatchCompile.freezeControlNat tokenFn z
  conditioningFrameTokenEmit second ψCode day ε budgetCode inverseBudgetCode
    (control.unpair.1, control.unpair.2) (tokenFn z)

lemma conditioningFrameTokenRun_range (second : Bool) (tokenFn : ℕ → ℕ)
    (ψCode day budgetCode inverseBudgetCode : ℕ) (ε : ℚ)
    (n count : ℕ) :
    conditioningFrameTokenRun second ψCode day ε budgetCode inverseBudgetCode (0, 0)
        ((List.range count).map fun j => tokenFn (Nat.pair n j)) =
      (EF.freezeTokenControlAt tokenFn n count,
        (List.range count).flatMap fun j =>
          conditioningFrameTokenSegment second tokenFn ψCode day budgetCode
            inverseBudgetCode ε (Nat.pair n j)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.map_append,
        conditioningFrameTokenRun_append, ih]
      simp [conditioningFrameTokenRun, conditioningFrameTokenSegment,
        PrefixPatchCompile.freezeControlNat, EF.freezeTokenControlAt]
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

/-- `tradeScanAt` on a packed `⟨n, j⟩` argument, its two components paired. -/
def tradeScanNat (tokenFn : ℕ → ℕ) (z : ℕ) : ℕ :=
  let state := tradeScanAt tokenFn z.unpair.1 z.unpair.2
  Nat.pair state.1 state.2

/-- The number of completed trade frames in the source stream of length `lenFn n`. -/
def frameTradeCount (tokenFn lenFn : ℕ → ℕ) (n : ℕ) : ℕ :=
  (tradeScanNat tokenFn (Nat.pair n (lenFn n))).unpair.2

private lemma streamStep_trades_length (state next : EF.StreamState) (token : ℕ)
    (hstep : EF.streamStep (some state) token = some next) :
    next.2.2.length = state.2.2.length + if state.1.1 = 4 then 1 else 0 := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  rcases next with ⟨⟨nextMode, nextPending⟩, ⟨nextStack, nextTrades⟩⟩
  simp only [EF.streamStep] at hstep
  repeat' split at hstep
  all_goals aesop (add simp [List.length_append])

private lemma tradeScanAt_count_eq_of_read (tokenFn : ℕ → ℕ) (n j : ℕ)
    (state : EF.StreamState)
    (hread : EF.streamReadFrom
      ((List.range j).map fun i => tokenFn (Nat.pair n i))
      (some EF.streamInitial) = some state) :
    (tradeScanAt tokenFn n j).2 = state.2.2.length ∧
      (EF.freezeTokenControlAt tokenFn n j).Matches state := by
  induction j generalizing state with
  | zero =>
      simp [tradeScanAt, EF.streamReadFrom, EF.streamInitial,
        EF.freezeTokenControlAt, EF.FreezeTokenState.Matches] at hread ⊢
      subst state
      simp
  | succ j ih =>
      rw [List.range_succ, List.map_append, EF.streamReadFrom_append] at hread
      cases hprev : EF.streamReadFrom
          ((List.range j).map fun i => tokenFn (Nat.pair n i))
          (some EF.streamInitial) with
      | none =>
          rw [hprev, EF.streamReadFrom_none] at hread
          contradiction
      | some previous =>
          rw [hprev] at hread
          have hstep : EF.streamStep (some previous) (tokenFn (Nat.pair n j)) =
              some state := by
            simpa [EF.streamReadFrom] using hread
          rcases ih previous hprev with ⟨hcount, hmatches⟩
          have hnext := (streamReadFrom_conditionPriceTokenEmit
            (fun _ => ⊤) 1 (EF.freezeTokenControlAt tokenFn n j) previous
              (tokenFn (Nat.pair n j)) hmatches).2 state hstep
          have hlength := streamStep_trades_length previous state
            (tokenFn (Nat.pair n j)) hstep
          constructor
          · simp only [tradeScanAt]
            rw [hcount, hlength]
            have hmode : (EF.freezeTokenControlAt tokenFn n j).1 =
                previous.1.1 := hmatches.1
            by_cases hm : (EF.freezeTokenControlAt tokenFn n j).1 = 4
            · simp [PrefixPatchCompile.freezeControlNat, hm, ← hmode]
            · simp [PrefixPatchCompile.freezeControlNat, hm, ← hmode, hcount]
          · simpa only [EF.freezeTokenControlAt] using hnext

lemma frameTradeCount_eq_length_of_read
    (tokenFn lenFn : ℕ → ℕ) (n : ℕ) (state : EF.StreamState)
    (hread : EF.streamReadFrom
      ((List.range (lenFn n)).map fun i => tokenFn (Nat.pair n i))
      (some EF.streamInitial) = some state) :
    frameTradeCount tokenFn lenFn n = state.2.2.length := by
  simpa [frameTradeCount, tradeScanNat] using
    (tradeScanAt_count_eq_of_read tokenFn n (lenFn n) state hread).1

/-! ### A shallow acceptance scan for safely joining two passes -/

/-- Update only the feature-stack depth of the streaming parser.  The transition is exact
whenever the real parser step succeeds; on a decoding or stack-underflow failure its value is
irrelevant. -/
def parserDepthNext (mode token depth : ℕ) : ℕ :=
  if mode = 0 then
    if token = 2 then depth.pred
    else if token = 3 then depth.pred
    else if token = 4 then depth.pred
    else if token = 8 then depth.pred
    else depth
  else if mode = 2 then depth + 1
  else if mode = 3 then depth + 1
  else if mode = 4 then depth.pred
  else if mode = 5 then depth + 1
  else depth

/-- The shallow feature-stack depth before source index `j`, stepped by `parserDepthNext`.
It agrees with the real parser's stack depth on any stream the parser accepts. -/
def parserDepthScanAt (tokenFn : ℕ → ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      parserDepthNext
        (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1
        (tokenFn (Nat.pair n j)) (parserDepthScanAt tokenFn n j)

/-- `parserDepthScanAt` on a packed `⟨n, j⟩` argument. -/
def parserDepthScanNat (tokenFn : ℕ → ℕ) (z : ℕ) : ℕ :=
  parserDepthScanAt tokenFn z.unpair.1 z.unpair.2

/-- Boolean-as-natural test for a ready parser with an empty feature stack.  Decode failures
may produce false positives, which are harmless because `none` is absorbing; a successful
real parse agrees exactly with this shallow scan. -/
def parserStructurallyAccepts (tokenFn lenFn : ℕ → ℕ) (n : ℕ) : ℕ :=
  if (PrefixPatchCompile.freezeControlNat tokenFn
      (Nat.pair n (lenFn n))).unpair.1 = 0 then
    if parserDepthScanNat tokenFn (Nat.pair n (lenFn n)) = 0 then 1 else 0
  else 0

private lemma streamStep_stack_length (state next : EF.StreamState) (token : ℕ)
    (hstep : EF.streamStep (some state) token = some next) :
    next.2.1.length = parserDepthNext state.1.1 token state.2.1.length := by
  rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
  rcases next with ⟨⟨nextMode, nextPending⟩, ⟨nextStack, nextTrades⟩⟩
  simp only [EF.streamStep] at hstep
  repeat' split at hstep
  all_goals aesop (add simp [parserDepthNext])

private lemma parserDepthScanAt_eq_of_read (tokenFn : ℕ → ℕ) (n j : ℕ)
    (state : EF.StreamState)
    (hread : EF.streamReadFrom
      ((List.range j).map fun i => tokenFn (Nat.pair n i))
      (some EF.streamInitial) = some state) :
    parserDepthScanAt tokenFn n j = state.2.1.length := by
  induction j generalizing state with
  | zero =>
      simp [parserDepthScanAt, EF.streamReadFrom, EF.streamInitial] at hread ⊢
      subst state
      rfl
  | succ j ih =>
      rw [List.range_succ, List.map_append, EF.streamReadFrom_append] at hread
      cases hprev : EF.streamReadFrom
          ((List.range j).map fun i => tokenFn (Nat.pair n i))
          (some EF.streamInitial) with
      | none =>
          rw [hprev, EF.streamReadFrom_none] at hread
          contradiction
      | some previous =>
          rw [hprev] at hread
          have hstep : EF.streamStep (some previous) (tokenFn (Nat.pair n j)) =
              some state := by
            simpa [EF.streamReadFrom] using hread
          rw [parserDepthScanAt, ih previous hprev]
          have hmode := (tradeScanAt_count_eq_of_read tokenFn n j previous hprev).2.1
          simp only [PrefixPatchCompile.freezeControlNat, Nat.unpair_pair]
          rw [hmode]
          exact (streamStep_stack_length previous state
            (tokenFn (Nat.pair n j)) hstep).symm

private lemma parserStructurallyAccepts_eq_one_of_read
    (tokenFn lenFn : ℕ → ℕ) (n : ℕ) (trades : List (EF × Sentence))
    (hread : EF.streamReadFrom
      ((List.range (lenFn n)).map fun i => tokenFn (Nat.pair n i))
      (some EF.streamInitial) = some ((0, none), ([], trades))) :
    parserStructurallyAccepts tokenFn lenFn n = 1 := by
  have hmatches := (tradeScanAt_count_eq_of_read tokenFn n (lenFn n)
    ((0, none), ([], trades)) hread).2.1
  have hdepth := parserDepthScanAt_eq_of_read tokenFn n (lenFn n)
    ((0, none), ([], trades)) hread
  simp [parserStructurallyAccepts, parserDepthScanNat,
    PrefixPatchCompile.freezeControlNat, hmatches, hdepth]

private lemma parserStructurallyAccepts_eq_one_iff_of_read
    (tokenFn lenFn : ℕ → ℕ) (n : ℕ) (state : EF.StreamState)
    (hread : EF.streamReadFrom
      ((List.range (lenFn n)).map fun i => tokenFn (Nat.pair n i))
      (some EF.streamInitial) = some state) :
    parserStructurallyAccepts tokenFn lenFn n = 1 ↔
      state.1.1 = 0 ∧ state.2.1 = [] := by
  have hmatches := (tradeScanAt_count_eq_of_read tokenFn n (lenFn n) state hread).2.1
  have hdepth := parserDepthScanAt_eq_of_read tokenFn n (lenFn n) state hread
  rw [show parserStructurallyAccepts tokenFn lenFn n =
      if state.1.1 = 0 then if state.2.1.length = 0 then 1 else 0 else 0 by
    simp [parserStructurallyAccepts, parserDepthScanNat,
      PrefixPatchCompile.freezeControlNat, hmatches, hdepth]]
  by_cases hm : state.1.1 = 0 <;> by_cases hs : state.2.1 = [] <;>
    simp [hm, hs, List.length_eq_zero_iff]

lemma parserDepthScanAt_le (tokenFn : ℕ → ℕ) (n j : ℕ) :
    parserDepthScanAt tokenFn n j ≤ j := by
  induction j with
  | zero => simp [parserDepthScanAt]
  | succ j ih =>
      simp only [parserDepthScanAt]
      have hpred := Nat.pred_le (parserDepthScanAt tokenFn n j)
      unfold parserDepthNext
      split_ifs <;> omega

private lemma tradeScanAt_fst_le (tokenFn : ℕ → ℕ) (n j : ℕ) :
    (tradeScanAt tokenFn n j).1 ≤ j := by
  induction j with
  | zero => simp [tradeScanAt]
  | succ j ih =>
      simp only [tradeScanAt]
      split
      · simp
      · exact ih.trans (Nat.le_succ _)

lemma tradeScanAt_snd_le (tokenFn : ℕ → ℕ) (n j : ℕ) :
    (tradeScanAt tokenFn n j).2 ≤ j := by
  induction j with
  | zero => simp [tradeScanAt]
  | succ j ih =>
      simp only [tradeScanAt]
      split
      · simpa using Nat.succ_le_succ ih
      · exact ih.trans (Nat.le_succ _)

private lemma tradeScanNat_polyFueled {tokenFn : ℕ → ℕ} {ct : Nat.Partrec.Code}
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

private lemma parserDepthScanNat_polyFueled {tokenFn : ℕ → ℕ} {ct : Nat.Partrec.Code}
    (htoken : PolyFueled ct tokenFn) :
    ∃ c, PolyFueled c (parserDepthScanNat tokenFn) := by
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
  have hindex := hn.pair hj
  have htokenAt := htoken.comp hindex
  have hcontrolAt := hcontrol.comp hindex
  have hmode := PolyFueled.left.comp hcontrolAt
  have hpred := predc_polyFueled.comp hprevious
  have hsucc := hprevious.succ_comp
  obtain ⟨ct2, ht2⟩ := polyFueled_eqConst htokenAt 2
  obtain ⟨ct3, ht3⟩ := polyFueled_eqConst htokenAt 3
  obtain ⟨ct4, ht4⟩ := polyFueled_eqConst htokenAt 4
  obtain ⟨ct8, ht8⟩ := polyFueled_eqConst htokenAt 8
  obtain ⟨cout8, hout8⟩ := PrefixPatchCompile.polyFueled_ifZero
    ht8 hprevious hpred
  obtain ⟨cout4, hout4⟩ := PrefixPatchCompile.polyFueled_ifZero
    ht4 hout8 hpred
  obtain ⟨cout3, hout3⟩ := PrefixPatchCompile.polyFueled_ifZero
    ht3 hout4 hpred
  obtain ⟨ctoken, htokenBranch⟩ := PrefixPatchCompile.polyFueled_ifZero
    ht2 hout3 hpred
  obtain ⟨cm0, hm0⟩ := polyFueled_eqConst hmode 0
  obtain ⟨cm2, hm2⟩ := polyFueled_eqConst hmode 2
  obtain ⟨cm3, hm3⟩ := polyFueled_eqConst hmode 3
  obtain ⟨cm4, hm4⟩ := polyFueled_eqConst hmode 4
  obtain ⟨cm5, hm5⟩ := polyFueled_eqConst hmode 5
  obtain ⟨cout5, hout5⟩ := PrefixPatchCompile.polyFueled_ifZero
    hm5 hprevious hsucc
  obtain ⟨coutMode4, houtMode4⟩ := PrefixPatchCompile.polyFueled_ifZero
    hm4 hout5 hpred
  obtain ⟨coutMode3, houtMode3⟩ := PrefixPatchCompile.polyFueled_ifZero
    hm3 houtMode4 hsucc
  obtain ⟨coutMode2, houtMode2⟩ := PrefixPatchCompile.polyFueled_ifZero
    hm2 houtMode3 hsucc
  obtain ⟨cstep, hstep⟩ := PrefixPatchCompile.polyFueled_ifZero
    hm0 houtMode2 htokenBranch
  have hstate : IsPolyBounded (parserDepthScanNat tokenFn) := by
    exact (IsPolyBounded.linear 0).of_le fun z => by
      have hjle := parserDepthScanAt_le tokenFn z.unpair.1 z.unpair.2
      exact hjle.trans (Nat.unpair_right_le z)
  have hstate' : IsPolyBounded (fun m =>
      parserDepthScanNat tokenFn (Nat.pair m.unpair.1 m.unpair.2)) := by
    simpa only [Nat.pair_unpair] using hstate
  refine ⟨_, (PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j => parserDepthScanNat tokenFn (Nat.pair n j))
    (fun n => ?_) (fun n j => ?_) hstate').of_eq fun z => ?_⟩
  · simp [parserDepthScanNat, parserDepthScanAt]
  · simp only [parserDepthScanNat, Nat.unpair_pair, parserDepthScanAt]
    unfold parserDepthNext
    by_cases hm0' :
        (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1 = 0 <;>
      by_cases hm2' :
        (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1 = 2 <;>
      by_cases hm3' :
        (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1 = 3 <;>
      by_cases hm4' :
        (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1 = 4 <;>
      by_cases hm5' :
        (PrefixPatchCompile.freezeControlNat tokenFn (Nat.pair n j)).unpair.1 = 5 <;>
      by_cases ht2' : tokenFn (Nat.pair n j) = 2 <;>
      by_cases ht3' : tokenFn (Nat.pair n j) = 3 <;>
      by_cases ht4' : tokenFn (Nat.pair n j) = 4 <;>
      by_cases ht8' : tokenFn (Nat.pair n j) = 8 <;>
      simp [hm0', hm2', hm3', hm4', hm5', ht2', ht3', ht4', ht8']
  · rw [Nat.pair_unpair]

private lemma parserStructurallyAccepts_polyFueled
    {tokenFn lenFn : ℕ → ℕ} {ct cl : Nat.Partrec.Code}
    (htoken : PolyFueled ct tokenFn) (hlen : PolyFueled cl lenFn) :
    ∃ c, PolyFueled c (parserStructurallyAccepts tokenFn lenFn) := by
  obtain ⟨ccontrol, hcontrol⟩ :=
    PrefixPatchCompile.freezeControlNat_polyFueled htoken
  obtain ⟨cdepth, hdepth⟩ := parserDepthScanNat_polyFueled htoken
  have hfinalIndex := PolyFueled.id.pair hlen
  have hmode := PolyFueled.left.comp (hcontrol.comp hfinalIndex)
  have hfinalDepth := hdepth.comp hfinalIndex
  obtain ⟨cmode0, hmode0⟩ := polyFueled_eqConst hmode 0
  obtain ⟨cdepth0, hdepth0⟩ := polyFueled_eqConst hfinalDepth 0
  obtain ⟨cmul, hmul⟩ := mul_polyFueled
  exact ⟨_, (hmul.comp (hmode0.pair hdepth0)).of_eq fun n => by
    by_cases hm : (PrefixPatchCompile.freezeControlNat tokenFn
        (Nat.pair n (lenFn n))).unpair.1 = 0 <;>
      by_cases hd : parserDepthScanNat tokenFn (Nat.pair n (lenFn n)) = 0 <;>
      simp [parserStructurallyAccepts, hm, hd]⟩

/-! ### Safely joining the two conditioning legs -/

/-- A failed source parser run remains failed through either framing pass, including its
end-of-stream flush suffix. -/
lemma streamReadFrom_conditioningFrameTokenOutput_none
    (second : Bool) (ψ : Sentence) (ε q : ℚ) (day : ℕ) (tokens : List ℕ)
    (hread : EF.streamReadFrom tokens (some EF.streamInitial) = none) :
    EF.streamReadFrom
      (conditioningFrameTokenOutput second (Encodable.encode ψ) day ε
        (Encodable.encode q) (Encodable.encode q⁻¹) tokens)
      (some EF.streamInitial) = none := by
  have hrun := (streamReadFrom_conditioningFrameTokenRun second ψ ε q day
    (0, 0) EF.streamInitial tokens EF.freezeToken_initial_matches).1
  unfold conditioningFrameTokenOutput
  rw [EF.streamReadFrom_append]
  have hinitial : frameStreamState second ψ ε q day EF.streamInitial =
      EF.streamInitial := rfl
  rw [← hinitial, hrun, hread]
  simp [EF.streamReadFrom_none]

/-- Join the two independently framed legs only at a structurally accepting source
boundary.  A source decode failure may be a false positive for the shallow test, but then
the first pass has already reached `none`, which is absorbing under append. -/
def safeSeparatedFrameTokenOutput
    (tokenFn lenFn : ℕ → ℕ) (ψ : Sentence) (ε q : ℚ)
    (day : ℕ) (tokens : List ℕ) : List ℕ :=
  let first := conditioningFrameTokenOutput false (Encodable.encode ψ) day ε
    (Encodable.encode q) (Encodable.encode q⁻¹) tokens
  let second := conditioningFrameTokenOutput true (Encodable.encode ψ) day ε
    (Encodable.encode q) (Encodable.encode q⁻¹) tokens
  if parserStructurallyAccepts tokenFn lenFn day = 0 then first else first ++ second

/-- The shallow acceptance test is `0` or `1`. -/
lemma parserStructurallyAccepts_eq_one_of_ne_zero {tokenFn lenFn : ℕ → ℕ} {day : ℕ}
    (h : parserStructurallyAccepts tokenFn lenFn day ≠ 0) :
    parserStructurallyAccepts tokenFn lenFn day = 1 := by
  unfold parserStructurallyAccepts at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- A structurally accepting source whose trades do not decode does not even *read*:
the shallow test can only be a false positive when the stream read has already failed
(a surviving read at an accepting boundary is ready with no pending sentence, and then
`deserializeTrades` succeeds). -/
lemma streamReadFrom_eq_none_of_accepts_of_deserializeTrades_none
    (tokenFn lenFn : ℕ → ℕ) (day : ℕ) (tokens : List ℕ)
    (htokens : tokens =
      (List.range (lenFn day)).map fun i => tokenFn (Nat.pair day i))
    (haccept1 : parserStructurallyAccepts tokenFn lenFn day = 1)
    (hsource : deserializeTrades tokens = none) :
    EF.streamReadFrom tokens (some EF.streamInitial) = none := by
  cases hread : EF.streamReadFrom tokens (some EF.streamInitial) with
  | none => rfl
  | some state =>
      have hread' := hread
      rw [htokens] at hread'
      have hshape := (parserStructurallyAccepts_eq_one_iff_of_read
        tokenFn lenFn day state hread').mp haccept1
      have hpending := streamReadFrom_readyPendingInvariant tokens state hread
      unfold deserializeTrades at hsource
      rw [hread] at hsource
      rcases state with ⟨⟨mode, pending⟩, ⟨stack, decoded⟩⟩
      simp only at hshape hpending
      rcases hshape with ⟨rfl, rfl⟩
      have hp : pending = none := hpending rfl
      subst pending
      simp at hsource

lemma deserializeTrades_safeSeparatedFrameTokenOutput
    (tokenFn lenFn : ℕ → ℕ) (ψ : Sentence) (ε q : ℚ)
    (day : ℕ) (tokens : List ℕ)
    (htokens : tokens =
      (List.range (lenFn day)).map fun i => tokenFn (Nat.pair day i)) :
    deserializeTrades
      (safeSeparatedFrameTokenOutput tokenFn lenFn ψ ε q day tokens) =
      (deserializeTrades tokens).map fun trades =>
        trades.map (frameLeg false ψ ε q day) ++
          trades.map (frameLeg true ψ ε q day) := by
  let first := conditioningFrameTokenOutput false (Encodable.encode ψ) day ε
    (Encodable.encode q) (Encodable.encode q⁻¹) tokens
  let second := conditioningFrameTokenOutput true (Encodable.encode ψ) day ε
    (Encodable.encode q) (Encodable.encode q⁻¹) tokens
  have hfirst := deserializeTrades_conditioningFrameTokenRun false ψ ε q day tokens
  have hsecond := deserializeTrades_conditioningFrameTokenRun true ψ ε q day tokens
  try simp only at hfirst hsecond
  cases hsource : deserializeTrades tokens with
  | some trades =>
      have hready := streamReadFrom_eq_ready_of_deserializeTrades_eq_some
        tokens trades hsource
      have haccept : parserStructurallyAccepts tokenFn lenFn day = 1 := by
        rw [htokens] at hready
        exact parserStructurallyAccepts_eq_one_of_read
          tokenFn lenFn day trades hready
      rw [hsource] at hfirst hsecond
      simp only [Option.map_some] at hfirst hsecond
      unfold safeSeparatedFrameTokenOutput
      simp only [haccept]
      exact deserializeTrades_append_of_some first second _ _ hfirst hsecond
  | none =>
      rw [hsource] at hfirst hsecond
      simp only [Option.map_none] at hfirst hsecond
      by_cases haccept : parserStructurallyAccepts tokenFn lenFn day = 0
      · unfold safeSeparatedFrameTokenOutput
        simp [haccept, hfirst]
      · have haccept1 : parserStructurallyAccepts tokenFn lenFn day = 1 :=
          parserStructurallyAccepts_eq_one_of_ne_zero haccept
        have hreadNone :=
          streamReadFrom_eq_none_of_accepts_of_deserializeTrades_none
            tokenFn lenFn day tokens htokens haccept1 hsource
        have hfirstRead := streamReadFrom_conditioningFrameTokenOutput_none
          false ψ ε q day tokens hreadNone
        unfold safeSeparatedFrameTokenOutput
        simp only [haccept, if_false]
        unfold deserializeTrades
        rw [EF.streamReadFrom_append, hfirstRead, EF.streamReadFrom_none]
        rfl

lemma strategyOfTokens_safeSeparatedFrameTokenOutput_trades
    (tokenFn lenFn : ℕ → ℕ) (ψ : Sentence) (ε q : ℚ)
    (day : ℕ) (tokens : List ℕ)
    (htokens : tokens =
      (List.range (lenFn day)).map fun i => tokenFn (Nat.pair day i)) :
    (strategyOfTokens day
      (safeSeparatedFrameTokenOutput tokenFn lenFn ψ ε q day tokens)).trades =
      (strategyOfTokens day tokens).trades.map (frameLeg false ψ ε q day) ++
        (strategyOfTokens day tokens).trades.map (frameLeg true ψ ε q day) := by
  have hdecode := deserializeTrades_safeSeparatedFrameTokenOutput
    tokenFn lenFn ψ ε q day tokens htokens
  unfold strategyOfTokens
  rw [hdecode]
  cases hs : deserializeTrades tokens with
  | none => simp
  | some trades =>
      simp only [Option.map_some]
      let mapped := trades.map (frameLeg false ψ ε q day) ++
        trades.map (frameLeg true ψ ε q day)
      have hrank :
          (∀ trade ∈ mapped, trade.1.rank ≤ day) ↔
            ∀ trade ∈ trades, trade.1.rank ≤ day := by
        constructor
        · intro h trade hmem
          have hmapped := h (frameLeg false ψ ε q day trade)
            (List.mem_append_left _ (List.mem_map_of_mem hmem))
          exact (frameLeg_rank_le_iff false ψ ε q day trade).mp hmapped
        · intro h trade hmem
          rw [List.mem_append, List.mem_map, List.mem_map] at hmem
          rcases hmem with ⟨source, hsource, rfl⟩ | ⟨source, hsource, rfl⟩
          · exact (frameLeg_rank_le_iff false ψ ε q day source).mpr
              (h source hsource)
          · exact (frameLeg_rank_le_iff true ψ ε q day source).mpr
              (h source hsource)
      by_cases hvalid : ∀ trade ∈ trades, trade.1.rank ≤ day
      · rw [dif_pos (hrank.mpr hvalid), dif_pos hvalid]
      · have hinvalid : ¬∀ trade ∈ mapped, trade.1.rank ≤ day :=
          fun h => hvalid (hrank.mp h)
        rw [dif_neg hinvalid, dif_neg hvalid]
        rfl

lemma frameLeg_retained_eq_locallyGatedFirstLeg
    (ψ : ℕ → Sentence) (ε τ : ℚ) (day count : ℕ) (p : EF × Sentence) :
    frameLeg false (ψ day) ε (Strategy.localConditioningBudget τ count) day
        (p.1.retainedConditionPrices ψ ε, p.2) =
      Strategy.locallyGatedFirstLeg ψ ε day τ count p := by
  simp [frameLeg, firstFrameBody, Strategy.locallyGatedFirstLeg]

lemma frameLeg_retained_eq_locallyGatedSecondLeg
    (ψ : ℕ → Sentence) (ε τ : ℚ) (day count : ℕ) (p : EF × Sentence) :
    frameLeg true (ψ day) ε (Strategy.localConditioningBudget τ count) day
        (p.1.retainedConditionPrices ψ ε, p.2) =
      Strategy.locallyGatedSecondLeg ψ ε day τ count p := by
  simp [frameLeg, secondFrameBody, Strategy.locallyGatedSecondLeg]

lemma frameLeg_exceptZero_eq_locallyGatedFirstLeg
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    (ε τ : ℚ) (day count : ℕ) (p : EF × Sentence) :
    frameLeg false (ψ day) ε (Strategy.localConditioningBudget τ count) day
        (p.1.retainedConditionPricesExceptZero zeroDays ψ ε, p.2) =
      Strategy.exceptZeroLocallyGatedFirstLeg
        zeroDays ψ ε day τ count p := by
  simp [frameLeg, firstFrameBody,
    Strategy.exceptZeroLocallyGatedFirstLeg]

lemma frameLeg_exceptZero_eq_locallyGatedSecondLeg
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    (ε τ : ℚ) (day count : ℕ) (p : EF × Sentence) :
    frameLeg true (ψ day) ε (Strategy.localConditioningBudget τ count) day
        (p.1.retainedConditionPricesExceptZero zeroDays ψ ε, p.2) =
      Strategy.exceptZeroLocallyGatedSecondLeg
        zeroDays ψ ε day τ count p := by
  simp [frameLeg, secondFrameBody,
    Strategy.exceptZeroLocallyGatedSecondLeg]

private lemma conditioningFrameTokenOutput_polySegStream
    {source : ℕ → List ℕ} {tokenFn lenFn : ℕ → ℕ}
    {ct cl : Nat.Partrec.Code}
    (htoken : PolyFueled ct tokenFn) (hlen : PolyFueled cl lenFn)
    (hslen : ∀ n, (source n).length = lenFn n)
    (hget : ∀ n i, i < lenFn n →
      tokenFn (Nat.pair n i) = (source n).getD i 0)
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ)
    (second : Bool) (ε : ℚ) :
    PolySegStream (fun n =>
      let count := frameTradeCount tokenFn lenFn n
      conditioningFrameTokenOutput second (Encodable.encode (ψ n)) n ε
        (frameBudgetCode n count) (frameInverseBudgetCode n count) (source n)) := by
  let count : ℕ → ℕ := frameTradeCount tokenFn lenFn
  obtain ⟨cscan, hscan⟩ := tradeScanNat_polyFueled htoken
  have hscanTotal := hscan.comp (PolyFueled.id.pair hlen)
  have hcount : PolyFueled _ count :=
    (PolyFueled.right.comp hscanTotal).of_eq fun n => by
      simp [count, frameTradeCount]
  rcases frameBudgetCodes_polyFueled PolyFueled.id hcount with
    ⟨⟨cb, hb⟩, ⟨ci, hi⟩⟩
  let control : ℕ → ℕ := PrefixPatchCompile.freezeControlNat tokenFn
  obtain ⟨ccontrol, hcontrol⟩ :=
    PrefixPatchCompile.freezeControlNat_polyFueled htoken
  let mode : ℕ → ℕ := fun z => (control z).unpair.1
  have hmode : PolyFueled _ mode := PolyFueled.left.comp hcontrol
  let condition : ℕ → ℕ := fun z => Encodable.encode (ψ z.unpair.1)
  obtain ⟨cψ, hψCode⟩ := hψ
  have hcondition : PolyFueled _ condition := hψCode.comp PolyFueled.left
  let day : ℕ → ℕ := fun z => z.unpair.1
  have hday : PolyFueled Nat.Partrec.Code.left day := PolyFueled.left
  let budget : ℕ → ℕ := fun z => frameBudgetCode z.unpair.1 (count z.unpair.1)
  have hbudget : PolyFueled _ budget := hb.comp PolyFueled.left
  let inverse : ℕ → ℕ := fun z =>
    frameInverseBudgetCode z.unpair.1 (count z.unpair.1)
  have hinverse : PolyFueled _ inverse := hi.comp PolyFueled.left
  have hlong := rawConditioningFrameTokens_poly htoken hcondition hday
    hbudget hinverse second ε
  have hcopy : PolySegStream (fun z => [tokenFn z]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.polyTok htoken)
  have hempty : PolySegStream (fun _ : ℕ => []) :=
    PolySegStream.ofTokenStream PolyTokenStream.nil
  obtain ⟨ctag6, htag6⟩ := polyFueled_eqConst htoken 6
  obtain ⟨cmode0, hmode0⟩ := polyFueled_eqConst hmode 0
  obtain ⟨cmode4, hmode4⟩ := polyFueled_eqConst hmode 4
  have hready : PolySegStream (fun z =>
      if (if tokenFn z = 6 then 1 else 0) = 0 then [tokenFn z] else []) :=
    hcopy.ifZero hempty htag6
  have hnonready : PolySegStream (fun z =>
      if (if mode z = 4 then 1 else 0) = 0 then [tokenFn z]
      else if second then
        rawLocallyGatedSecondBodyTokens (tokenFn z) (condition z) (day z)
            (budget z) (inverse z) ε ++ [8, 6, condition z]
      else
        rawLocallyGatedBetaBodyTokens (tokenFn z) (condition z) (day z)
            (budget z) (inverse z) ε ++
          [8, 6, conjunctionCode (tokenFn z) (condition z)]) :=
    hcopy.ifZero hlong hmode4
  have hraw : PolySegStream (fun z =>
      if (if mode z = 0 then 1 else 0) = 0 then
        (if (if mode z = 4 then 1 else 0) = 0 then [tokenFn z]
        else if second then
          rawLocallyGatedSecondBodyTokens (tokenFn z) (condition z) (day z)
              (budget z) (inverse z) ε ++ [8, 6, condition z]
        else
          rawLocallyGatedBetaBodyTokens (tokenFn z) (condition z) (day z)
              (budget z) (inverse z) ε ++
            [8, 6, conjunctionCode (tokenFn z) (condition z)])
      else if (if tokenFn z = 6 then 1 else 0) = 0 then [tokenFn z] else []) :=
    hnonready.ifZero hready hmode0
  have hsegment : PolySegStream (fun z =>
      conditioningFrameTokenSegment second tokenFn (condition z) (day z)
        (budget z) (inverse z) ε z) := hraw.of_eq fun z => by
    simp only [conditioningFrameTokenSegment]
    by_cases hm0 : mode z = 0 <;> by_cases hm4 : mode z = 4 <;>
      by_cases ht6 : tokenFn z = 6 <;>
      simp [conditioningFrameTokenEmit, mode, control, hm0, hm4, ht6]
  have hbody := hsegment.concatVar hlen
  let finalControl : ℕ → ℕ := fun n =>
    control (Nat.pair n (lenFn n))
  have hfinalControl : PolyFueled _ finalControl :=
    hcontrol.comp (PolyFueled.id.pair hlen)
  have hfinalMode : PolyFueled _ (fun n => (finalControl n).unpair.1) :=
    PolyFueled.left.comp hfinalControl
  obtain ⟨cfinal4, hfinal4⟩ := polyFueled_eqConst hfinalMode 4
  have hsix : PolySegStream (fun _ : ℕ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  have hsuffix : PolySegStream (fun n =>
      if (if (finalControl n).unpair.1 = 4 then 1 else 0) = 0 then [] else [6]) :=
    hempty.ifZero hsix hfinal4
  have hout := hbody.append hsuffix
  refine hout.of_eq fun n => ?_
  have hsourceEq : source n =
      (List.range (lenFn n)).map (fun j => tokenFn (Nat.pair n j)) := by
    apply List.ext_getElem
    · simp [hslen n]
    · intro i hleft hright
      rw [List.getElem_map]
      simp only [List.getElem_range]
      rw [hget n i (by simpa [hslen n] using hleft)]
      exact (List.getD_eq_getElem (l := source n) (d := 0) hleft).symm
  rw [hsourceEq]
  have hrun := conditioningFrameTokenRun_range second tokenFn
    (Encodable.encode (ψ n)) n (frameBudgetCode n (count n))
    (frameInverseBudgetCode n (count n)) ε n (lenFn n)
  unfold conditioningFrameTokenOutput
  simp only [count] at hrun ⊢
  rw [hrun]
  simp [conditioningFrameTokenSegment, condition, day, budget, inverse, count,
    finalControl, control, PrefixPatchCompile.freezeControlNat]

/-- The guarded concatenation of both conditioning legs is a polynomial segment stream. -/
lemma safeSeparatedFrameTokenOutput_polySegStream
    {source : ℕ → List ℕ} {tokenFn lenFn : ℕ → ℕ}
    {ct cl : Nat.Partrec.Code}
    (htoken : PolyFueled ct tokenFn) (hlen : PolyFueled cl lenFn)
    (hslen : ∀ n, (source n).length = lenFn n)
    (hget : ∀ n i, i < lenFn n →
      tokenFn (Nat.pair n i) = (source n).getD i 0)
    (ψ : ℕ → Sentence) (hψ : PolySentenceCodes ψ) (ε : ℚ) :
    PolySegStream (fun n =>
      let count := frameTradeCount tokenFn lenFn n
      safeSeparatedFrameTokenOutput tokenFn lenFn (ψ n) ε
        (frameBudget n count) n (source n)) := by
  have hfirst := conditioningFrameTokenOutput_polySegStream htoken hlen hslen hget
    ψ hψ false ε
  have hsecond := conditioningFrameTokenOutput_polySegStream htoken hlen hslen hget
    ψ hψ true ε
  obtain ⟨caccept, haccept⟩ := parserStructurallyAccepts_polyFueled htoken hlen
  have hselected := hfirst.ifZero (hfirst.append hsecond) haccept
  refine hselected.of_eq fun n => ?_
  simp [safeSeparatedFrameTokenOutput, frameBudgetCode_exact,
    frameInverseBudgetCode_exact]

/-! ### End-to-end translator closure -/

lemma deserializeTrades_eq_some_of_strategyOfTokens_trades_ne_nil
    (day : ℕ) (tokens : List ℕ)
    (hne : (strategyOfTokens day tokens).trades ≠ []) :
    deserializeTrades tokens = some (strategyOfTokens day tokens).trades := by
  generalize hS : strategyOfTokens day tokens = S at hne ⊢
  unfold strategyOfTokens at hS
  split at hS
  next hdecode =>
    subst S
    simp at hne
  next trades hdecode =>
    split at hS
    next hvalid =>
      subst S
      exact hdecode
    next hinvalid =>
      subst S
      simp at hne

/-! ## The finite-prefix denominator floor -/

/-! ### Constructing the floor -/

/-- A finite family of positive rational numbers and one further positive rational have
one common positive rational lower bound.  This is the finite-prefix step that turns an
eventual price floor into a floor valid on every day. -/
private lemma exists_positive_rational_lower_finset
    (s : Finset ℕ) (f : ℕ → ℚ) (q : ℚ)
    (hf : ∀ x ∈ s, 0 < f x) (hq : 0 < q) :
    ∃ ε : ℚ, 0 < ε ∧ ε ≤ q ∧ ∀ x ∈ s, ε ≤ f x := by
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨q, hq, le_rfl, by simp⟩
  | @insert a s ha ih =>
      have hfa : 0 < f a := hf a (by simp)
      have hfs : ∀ x ∈ s, 0 < f x := by
        intro x hx
        exact hf x (Finset.mem_insert_of_mem hx)
      obtain ⟨ε, hε, hεq, hεs⟩ := ih hfs
      refine ⟨min ε (f a), lt_min hε hfa,
        (min_le_left _ _).trans hεq, ?_⟩
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεs x hx)

/-- An eventual positive rational floor can be shrunk across the finite prefix of an
exact rational market.  The only omitted prefix days are exactly the days on which the
condition price is zero. -/
private lemma eventualConditioningFloor_nonempty_of_tail
    {P : History} (market : MarketComputation P) (ψ : ℕ → Sentence)
    (cutoff : ℕ) (tailε : ℚ) (htailε : 0 < (tailε : ℝ))
    (htail : ∀ d, cutoff ≤ d → (tailε : ℝ) ≤ P d (ψ d)) :
    Nonempty (EventualConditioningFloor P ψ) := by
  let zeroDays : Finset ℕ :=
    (Finset.range cutoff).filter fun d =>
      market.quote d (Encodable.encode (ψ d)) = 0
  let positiveDays : Finset ℕ :=
    (Finset.range cutoff).filter fun d =>
      market.quote d (Encodable.encode (ψ d)) ≠ 0
  have htailεRat : 0 < tailε := by
    exact_mod_cast htailε
  have hpositive : ∀ d ∈ positiveDays,
      0 < market.quote d (Encodable.encode (ψ d)) := by
    intro d hd
    have hne : market.quote d (Encodable.encode (ψ d)) ≠ 0 := by
      exact (Finset.mem_filter.mp hd).2
    have hnonneg : (0 : ℚ) ≤
        market.quote d (Encodable.encode (ψ d)) := by
      have hp := (market.price_mem_Icc d (ψ d)).1
      rw [market.quote_exact d (ψ d)] at hp
      exact_mod_cast hp
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  obtain ⟨ε, hε, hεtail, hεprefix⟩ :=
    exists_positive_rational_lower_finset positiveDays
      (fun d => market.quote d (Encodable.encode (ψ d)))
      tailε hpositive htailεRat
  refine ⟨{
    cutoff := cutoff
    zeroDays := zeroDays
    zeroDays_lt := ?_
    epsilon := ε
    epsilon_pos := ?_
    zero_exact := ?_
    positive_floor := ?_
  }⟩
  · intro d hd
    exact Finset.mem_range.mp (Finset.mem_filter.mp hd).1
  · exact_mod_cast hε
  · intro d hd
    have hquote :
        market.quote d (Encodable.encode (ψ d)) = 0 :=
      (Finset.mem_filter.mp hd).2
    rw [market.quote_exact d (ψ d), hquote]
    norm_num
  · intro d hd
    by_cases hdc : d < cutoff
    · have hquote :
          market.quote d (Encodable.encode (ψ d)) ≠ 0 := by
        intro hzero
        apply hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdc, hzero⟩
      have hmem : d ∈ positiveDays :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdc, hquote⟩
      rw [market.quote_exact d (ψ d)]
      exact_mod_cast hεprefix d hmem
    · have hcast : (ε : ℝ) ≤ (tailε : ℝ) := by
        exact_mod_cast hεtail
      exact hcast.trans (htail d (Nat.le_of_not_gt hdc))

/-! ### Deriving the tail floor from joint consistency

The floor argument below covers the case in which the condition sequence is jointly
consistent with every stage of the deductive process.  That joint-consistency hypothesis is
*added here*: the paper's `thm:scon` assumes no such thing.  The complementary case, where
some stage together with the conditions is unsatisfiable, is handled separately by
`isLogicalInductor_of_stage_unsatisfiable`. -/

/-- Uniform Non-Dogmatism followed by Preemptive Learning gives an eventual positive
rational floor on the diagonal prices of any efficiently codeable, jointly consistent
condition sequence.  This is the analytic content behind the conditioning compiler's
denominator floor.  Joint consistency is needed *here*, in the price-floor argument; it is
not a hypothesis of the paper's theorem.
Paper node: `thm:scon` -/
lemma exists_eventual_condition_price_floor
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (ψ i)) :
    ∃ cutoff : ℕ, ∃ ε : ℚ, 0 < (ε : ℝ) ∧
      ∀ d, cutoff ≤ d → (ε : ℝ) ≤ P d (ψ d) := by
  let rep : EfficientRepeatedEnumeration ψ :=
    EfficientRepeatedEnumeration.ofBig ψ hψ
  obtain ⟨lower, hlower, hlowerLimiting⟩ :=
    lic_uniform_nonDogmatism P DP ψ rep hjoint
  have hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) := by
    intro n
    obtain ⟨v, hv, _⟩ := hjoint n
    exact ⟨v, hv⟩
  let bounded :=
    AffineCombination.sentenceAffine_bounded ψ P
      (fun n φ => IsLogicalInductor.price_mem_Icc
        (P := P) (DP := DP) n φ)
  have hfuture : ∀ n, lower ≤
      affineFutureHigh (AffineCombination.sentenceAffine ψ) P n := by
    intro n
    have hbetween :=
      AffineCombination.futureLow_le_limitingValue_le_futureHigh
        (AffineCombination.sentenceAffine ψ) P DP bounded hworld n
    have hlimit : limitingBelief P (ψ n) ≤
        affineFutureHigh (AffineCombination.sentenceAffine ψ) P n := by
      simpa [AffineCombination.sentenceAffine,
        AffineCombination.value] using hbetween.2
    exact (hlowerLimiting n).trans hlimit
  obtain ⟨hdiagBelow, _, _, hfutureAbove, _, _⟩ := bounded.filterBounds
  have hfutureLiminfAffine : lower ≤
      liminf (affineFutureHigh
        (AffineCombination.sentenceAffine ψ) P) atTop :=
    le_liminf_of_le hfutureAbove.isCobounded_flip
      (Filter.Eventually.of_forall hfuture)
  have hfutureLiminf : lower ≤
      liminf (fun n => sSup
        (Set.range (fun j => P (n + j) (ψ n)))) atTop := by
    have hfutureEq :
        affineFutureHigh (AffineCombination.sentenceAffine ψ) P =
          fun n => sSup (Set.range (fun j => P (n + j) (ψ n))) :=
      funext (AffineCombination.sentenceAffine_futureHigh ψ P)
    rw [hfutureEq] at hfutureLiminfAffine
    exact hfutureLiminfAffine
  have hpreemptive := lic_preemptive_learning P DP ψ hψ hworld
  have hdiagLiminf : lower ≤ liminf (fun n => P n (ψ n)) atTop := by
    rw [hpreemptive.1]
    exact hfutureLiminf
  obtain ⟨ε, hε, hεlower⟩ :
      ∃ ε : ℚ, (0 : ℝ) < ε ∧ (ε : ℝ) < lower :=
    exists_rat_btwn hlower
  have hdiagBelow' :
      IsBoundedUnder (· ≥ ·) atTop (fun n => P n (ψ n)) := by
    simpa only [AffineCombination.sentenceAffine_price] using hdiagBelow
  have hevent : ∀ᶠ d in Filter.atTop, (ε : ℝ) < P d (ψ d) :=
    eventually_lt_of_lt_liminf
      (hεlower.trans_le hdiagLiminf) hdiagBelow'
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.mp hevent
  exact ⟨cutoff, ε, hε, fun d hd => (hcutoff d hd).le⟩

/-- Joint consistency therefore produces the finite-zero floor certificate the conditioning
compiler consumes. -/
private lemma eventualConditioningFloor_nonempty_of_jointConsistency
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (market : MarketComputation P)
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (ψ i)) :
    Nonempty (EventualConditioningFloor P ψ) := by
  obtain ⟨cutoff, ε, hε, htail⟩ :=
    exists_eventual_condition_price_floor P DP ψ hψ hjoint
  exact eventualConditioningFloor_nonempty_of_tail
    market ψ cutoff ε hε htail

/-- The chosen finite-zero floor certificate produced by the joint-consistency argument.
Paper node: `thm:scon` -/
noncomputable def eventualConditioningFloorOfJointConsistency
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (market : MarketComputation P)
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (ψ i)) :
    EventualConditioningFloor P ψ :=
  (eventualConditioningFloor_nonempty_of_jointConsistency
    P DP market ψ hψ hjoint).some

/-! ## Endpoint location

The operational-witness constructors and the criterion-level `thm:scon` endpoints are in
`Construction/Machine/CondEndpoints.lean` (namespace `ConditioningCompile`);
`Construction/Witnesses/RpnConditioning.lean` (namespace `RpnConditioning`) proves the
token-metered (`EfficientlyComputable`) translation certificates they require.  This file
carries the economic and floor content both consume. -/

end ConditioningCompile

end LogicalInduction
