import LogicalInduction.Framework.Machine.DigitArithFP
import LogicalInduction.Construction.Witnesses.PatternAutomaton

/-!
# The escape-leaf decode test, in `Complexity.FP`

Renders `app:ifp` (tex:6018) by inhabiting `PatAuto.HoleGuards`, the one input the spelling
recognizer cannot supply on its own: for a fixed subformula `χ`, decide "does this token's
code decode to `χ`" in polynomial time.  `fiberW_mem_FP` and `holeGuards` are the `Complexity.FP`
decode test the recognizer needs, built rather than assumed.

On a `⊥`-free `χ` the test is a fixed-numeral comparison
(`CanonicalCodes.sentenceMatches_of_botFree`).  In general it is not: Foundation's
`Formula.ofNat` discards the payload at tag `0`, so `⊥`'s decode fibre is `{k² + 1}` and the
multiplicity propagates through every connective.

* The recursion is `PrefixPatchCompile.sentenceMatches`'s, whose correctness against
  `Encodable.decode` is proved in both directions (`sentenceMatches_eq_one_iff`), so nothing
  about the *decoder* is re-derived here.  What is added is that each step — predecessor,
  `Nat.unpair`, comparison against a fixed numeral — is available on a token's **digit word**
  inside `Complexity.FP` (`Framework/Machine/DigitArithFP.lean`).
* `tagW` / `payW` / `leftW` / `rightW` are the digit-word projections, with their
  `IsDigitWord` and `wordVal` laws.
* `fiberW` is the test itself, run on digit words, with the connective conjunction spelled by
  returning the right branch inside the left branch's success case.
* Main results: `fiberW_mem_FP` (polynomial time at a fixed depth set by the target's size, a
  constant of the frozen table, so the whole test is a fixed-depth composition rather than a
  scan) and `length_fiberW_eq_one` (it computes `sentenceMatches`).

`fiberW_mem_FP` and `holeGuards` are in `AxiomAudit.lean`.  `SegmentRecognizer.lean` is
parameterized over the interface `PatAuto.HoleGuards` rather than over these terms;
`FreezeOracle.lean` supplies `holeGuards` as its inhabitant, and the term-level consumers are
`FreezeOracle.lean`, `PatternAutomaton.lean`, `RpnFreeze.lean` and `CanonicalCodes.lean`.
-/

namespace LogicalInduction.FiberTest

open Complexity Complexity.Cobham LogicalInduction.FPFold LogicalInduction.TokenFold
open LogicalInduction.DigitFP LogicalInduction.RunAuto LogicalInduction.PatAuto
open LogicalInduction.PrefixPatchCompile

-- `Nat.pair`/`unpair` unfold `Nat.sqrt`'s well-founded definition during `whnf` and loop;
-- local opacity stops that.  See `notes/lean-gotchas.md`.
attribute [local irreducible] Nat.sqrt

/-! ## Reading a fixed numeral off a digit word -/

lemma numEqBits_iff_wordVal {w : List Bool} (hw : IsDigitWord w) (K : ℕ) :
    NumEqBits K w ↔ wordVal w = K := by
  obtain ⟨cur, hcur, rfl⟩ := hw
  rw [numEqBits_spec K cur hcur, wordVal_digitsToBits hcur]

/-! ## The projections the decoder needs

`Formula.ofNat` reads a nonzero code `e + 1` as the tag `e.unpair.1` and the payload
`e.unpair.2`, and at a connective splits the payload again.  Three word functions cover all
of it. -/

/-- The decoder's tag: `(code - 1).unpair.1`. -/
def tagW (w : List Bool) : List Bool := unpairFstW (predW w)

/-- The decoder's payload: `(code - 1).unpair.2`. -/
def payW (w : List Bool) : List Bool := unpairSndW (predW w)

/-- A connective's left subcode: `(code - 1).unpair.2.unpair.1`. -/
def leftW (w : List Bool) : List Bool := unpairFstW (payW w)

/-- A connective's right subcode: `(code - 1).unpair.2.unpair.2`. -/
def rightW (w : List Bool) : List Bool := unpairSndW (payW w)

private lemma idFn_mem_FP : (fun w : List Bool => w) ∈ FP := Complexity.id_mem_FP

lemma tagW_mem_FP : tagW ∈ FP := by
  show (fun w => unpairFstW (predW w)) ∈ FP
  simpa [Function.comp_def] using mem_FP_comp predW_mem_FP unpairFstW_mem_FP

lemma payW_mem_FP : payW ∈ FP := by
  show (fun w => unpairSndW (predW w)) ∈ FP
  simpa [Function.comp_def] using mem_FP_comp predW_mem_FP unpairSndW_mem_FP

lemma leftW_mem_FP : leftW ∈ FP := by
  show (fun w => unpairFstW (payW w)) ∈ FP
  simpa [Function.comp_def] using mem_FP_comp payW_mem_FP unpairFstW_mem_FP

lemma rightW_mem_FP : rightW ∈ FP := by
  show (fun w => unpairSndW (payW w)) ∈ FP
  simpa [Function.comp_def] using mem_FP_comp payW_mem_FP unpairSndW_mem_FP

/-! `DigitFP.unpairW_spec` bundles the four facts; these are the projections. -/

lemma isDigitWord_unpairFstW {w : List Bool} (hw : IsDigitWord w) :
    IsDigitWord (unpairFstW w) := (unpairW_spec hw).1

lemma isDigitWord_unpairSndW {w : List Bool} (hw : IsDigitWord w) :
    IsDigitWord (unpairSndW w) := (unpairW_spec hw).2.1

lemma wordVal_unpairFstW {w : List Bool} (hw : IsDigitWord w) :
    wordVal (unpairFstW w) = (Nat.unpair (wordVal w)).1 := (unpairW_spec hw).2.2.1

lemma wordVal_unpairSndW {w : List Bool} (hw : IsDigitWord w) :
    wordVal (unpairSndW w) = (Nat.unpair (wordVal w)).2 := (unpairW_spec hw).2.2.2

lemma isDigitWord_tagW {w : List Bool} (hw : IsDigitWord w) : IsDigitWord (tagW w) :=
  isDigitWord_unpairFstW (isDigitWord_predW hw)

lemma isDigitWord_payW {w : List Bool} (hw : IsDigitWord w) : IsDigitWord (payW w) :=
  isDigitWord_unpairSndW (isDigitWord_predW hw)

lemma isDigitWord_leftW {w : List Bool} (hw : IsDigitWord w) : IsDigitWord (leftW w) :=
  isDigitWord_unpairFstW (isDigitWord_payW hw)

lemma isDigitWord_rightW {w : List Bool} (hw : IsDigitWord w) : IsDigitWord (rightW w) :=
  isDigitWord_unpairSndW (isDigitWord_payW hw)

lemma wordVal_tagW {w : List Bool} (hw : IsDigitWord w) :
    wordVal (tagW w) = (Nat.unpair (wordVal w - 1)).1 := by
  rw [tagW, wordVal_unpairFstW (isDigitWord_predW hw), wordVal_predW hw]

lemma wordVal_payW {w : List Bool} (hw : IsDigitWord w) :
    wordVal (payW w) = (Nat.unpair (wordVal w - 1)).2 := by
  rw [payW, wordVal_unpairSndW (isDigitWord_predW hw), wordVal_predW hw]

lemma wordVal_leftW {w : List Bool} (hw : IsDigitWord w) :
    wordVal (leftW w) = (Nat.unpair (Nat.unpair (wordVal w - 1)).2).1 := by
  rw [leftW, wordVal_unpairFstW (isDigitWord_payW hw), wordVal_payW hw]

lemma wordVal_rightW {w : List Bool} (hw : IsDigitWord w) :
    wordVal (rightW w) = (Nat.unpair (Nat.unpair (wordVal w - 1)).2).2 := by
  rw [rightW, wordVal_unpairSndW (isDigitWord_payW hw), wordVal_payW hw]

/-! ## The test -/

/-- **The escape-leaf test.**  A one-bit word when the token's code decodes to the target,
and empty otherwise.  The recursion is `sentenceMatches`'s, run on digit words; at a
connective the conjunction is spelled by returning the right branch's own answer inside the
left branch's success case. -/
def fiberW : Sentence → List Bool → List Bool
  | ⊥, w =>
      if NumEqBits 0 w then []
      else if NumEqBits 0 (tagW w) then [true] else []
  | .atom a, w =>
      if NumEqBits 0 w then []
      else if NumEqBits 1 (tagW w) then
        (if NumEqBits a (payW w) then [true] else [])
      else []
  | φ 🡒 ψ, w =>
      if NumEqBits 0 w then []
      else if NumEqBits 2 (tagW w) then
        (if (fiberW φ (leftW w)).length = 1 then fiberW ψ (rightW w) else [])
      else []
  | φ ⋏ ψ, w =>
      if NumEqBits 0 w then []
      else if NumEqBits 3 (tagW w) then
        (if (fiberW φ (leftW w)).length = 1 then fiberW ψ (rightW w) else [])
      else []
  | φ ⋎ ψ, w =>
      if NumEqBits 0 w then []
      else if NumEqBits 4 (tagW w) then
        (if (fiberW φ (leftW w)).length = 1 then fiberW ψ (rightW w) else [])
      else []

/-- **The test is polynomial time**, at a fixed depth set by the target's size.

Proof kind: `C` composition.  Provenance: (a) `DigitFP.unpairFstW_mem_FP`,
`DigitFP.predW_mem_FP`; (b) `TokenFold.ifNumEq_mem_FP`, `TokenFold.ifEqLen_mem_FP`.
Paper node: `app:ifp` -/
lemma fiberW_mem_FP : ∀ χ : Sentence, fiberW χ ∈ FP := by
  intro χ
  induction χ using LO.Propositional.Formula.rec' with
  | hfalsum =>
      have h := ifNumEq_mem_FP idFn_mem_FP 0 (constFn_mem_FP [])
        (ifNumEq_mem_FP tagW_mem_FP 0 (constFn_mem_FP [true]) (constFn_mem_FP []))
      exact h
  | hatom a =>
      have h := ifNumEq_mem_FP idFn_mem_FP 0 (constFn_mem_FP [])
        (ifNumEq_mem_FP tagW_mem_FP 1
          (ifNumEq_mem_FP payW_mem_FP a (constFn_mem_FP [true]) (constFn_mem_FP []))
          (constFn_mem_FP []))
      exact h
  | himp φ ψ ihφ ihψ =>
      have hl : (fun w => fiberW φ (leftW w)) ∈ FP := by
        simpa [Function.comp_def] using mem_FP_comp leftW_mem_FP ihφ
      have hr : (fun w => fiberW ψ (rightW w)) ∈ FP := by
        simpa [Function.comp_def] using mem_FP_comp rightW_mem_FP ihψ
      have h := ifNumEq_mem_FP idFn_mem_FP 0 (constFn_mem_FP [])
        (ifNumEq_mem_FP tagW_mem_FP 2
          (ifEqLen_mem_FP hl 1 hr (constFn_mem_FP [])) (constFn_mem_FP []))
      exact h
  | hand φ ψ ihφ ihψ =>
      have hl : (fun w => fiberW φ (leftW w)) ∈ FP := by
        simpa [Function.comp_def] using mem_FP_comp leftW_mem_FP ihφ
      have hr : (fun w => fiberW ψ (rightW w)) ∈ FP := by
        simpa [Function.comp_def] using mem_FP_comp rightW_mem_FP ihψ
      have h := ifNumEq_mem_FP idFn_mem_FP 0 (constFn_mem_FP [])
        (ifNumEq_mem_FP tagW_mem_FP 3
          (ifEqLen_mem_FP hl 1 hr (constFn_mem_FP [])) (constFn_mem_FP []))
      exact h
  | hor φ ψ ihφ ihψ =>
      have hl : (fun w => fiberW φ (leftW w)) ∈ FP := by
        simpa [Function.comp_def] using mem_FP_comp leftW_mem_FP ihφ
      have hr : (fun w => fiberW ψ (rightW w)) ∈ FP := by
        simpa [Function.comp_def] using mem_FP_comp rightW_mem_FP ihψ
      have h := ifNumEq_mem_FP idFn_mem_FP 0 (constFn_mem_FP [])
        (ifNumEq_mem_FP tagW_mem_FP 4
          (ifEqLen_mem_FP hl 1 hr (constFn_mem_FP [])) (constFn_mem_FP []))
      exact h

/-- The connective case, shared by the three binary constructors. -/
private lemma bin_spec (tag : ℕ) {φ ψ : Sentence} {w : List Bool} (hw : IsDigitWord w)
    (ihφ : ∀ {v : List Bool}, IsDigitWord v →
      ((fiberW φ v).length = 1 ↔ sentenceMatches φ (wordVal v) = 1))
    (ihψ : ∀ {v : List Bool}, IsDigitWord v →
      ((fiberW ψ v).length = 1 ↔ sentenceMatches ψ (wordVal v) = 1)) :
    ((if NumEqBits 0 w then ([] : List Bool)
        else if NumEqBits tag (tagW w) then
          (if (fiberW φ (leftW w)).length = 1 then fiberW ψ (rightW w) else [])
        else []).length = 1)
      ↔ (if wordVal w = 0 then 0
          else if (wordVal w).pred.unpair.1 = tag then
            sentenceMatches φ (wordVal w).pred.unpair.2.unpair.1 *
              sentenceMatches ψ (wordVal w).pred.unpair.2.unpair.2
          else 0) = 1 := by
  by_cases h0 : wordVal w = 0
  · rw [if_pos ((numEqBits_iff_wordVal hw 0).mpr h0), if_pos h0]; simp
  rw [if_neg (fun hc => h0 ((numEqBits_iff_wordVal hw 0).mp hc)), if_neg h0]
  by_cases ht : (wordVal w).pred.unpair.1 = tag
  · have htw : wordVal (tagW w) = tag := by
      rw [wordVal_tagW hw, ← Nat.pred_eq_sub_one]; exact ht
    rw [if_pos ((numEqBits_iff_wordVal (isDigitWord_tagW hw) tag).mpr htw), if_pos ht]
    have hlv : wordVal (leftW w) = (wordVal w).pred.unpair.2.unpair.1 := by
      rw [wordVal_leftW hw, ← Nat.pred_eq_sub_one]
    have hrv : wordVal (rightW w) = (wordVal w).pred.unpair.2.unpair.2 := by
      rw [wordVal_rightW hw, ← Nat.pred_eq_sub_one]
    have hφ := ihφ (isDigitWord_leftW hw)
    have hψ := ihψ (isDigitWord_rightW hw)
    rw [hlv] at hφ
    rw [hrv] at hψ
    have hbφ := sentenceMatches_le_one φ ((wordVal w).pred.unpair.2.unpair.1)
    by_cases hl : (fiberW φ (leftW w)).length = 1
    · rw [if_pos hl, hφ.mp hl, one_mul]
      exact hψ
    · rw [if_neg hl]
      have hne : sentenceMatches φ ((wordVal w).pred.unpair.2.unpair.1) ≠ 1 :=
        fun hc => hl (hφ.mpr hc)
      have hz : sentenceMatches φ ((wordVal w).pred.unpair.2.unpair.1) = 0 := by omega
      rw [hz, zero_mul]
      simp
  · rw [if_neg (fun hc => ht (by
        rw [Nat.pred_eq_sub_one, ← wordVal_tagW hw]
        exact (numEqBits_iff_wordVal (isDigitWord_tagW hw) tag).mp hc)), if_neg ht]
    simp

/-- **The test computes `sentenceMatches`.**

Proof kind: `P` proved.  Provenance: (a) `numEqBits_iff_wordVal`, `wordVal_tagW`,
`DigitFP.unpairW_spec`. -/
lemma length_fiberW_eq_one : ∀ (χ : Sentence) {w : List Bool}, IsDigitWord w →
    ((fiberW χ w).length = 1 ↔ sentenceMatches χ (wordVal w) = 1) := by
  intro χ
  induction χ using LO.Propositional.Formula.rec' with
  | hfalsum =>
      intro w hw
      simp only [fiberW, sentenceMatches]
      by_cases h0 : wordVal w = 0
      · rw [if_pos ((numEqBits_iff_wordVal hw 0).mpr h0), if_pos h0]; simp
      rw [if_neg (fun hc => h0 ((numEqBits_iff_wordVal hw 0).mp hc)), if_neg h0]
      by_cases ht : (wordVal w).pred.unpair.1 = 0
      · rw [if_pos ((numEqBits_iff_wordVal (isDigitWord_tagW hw) 0).mpr
            (by rw [wordVal_tagW hw, ← Nat.pred_eq_sub_one]; exact ht)), if_pos ht]
        simp
      · rw [if_neg (fun hc => ht (by
            rw [Nat.pred_eq_sub_one, ← wordVal_tagW hw]
            exact (numEqBits_iff_wordVal (isDigitWord_tagW hw) 0).mp hc)), if_neg ht]
        simp
  | hatom a =>
      intro w hw
      simp only [fiberW, sentenceMatches]
      by_cases h0 : wordVal w = 0
      · rw [if_pos ((numEqBits_iff_wordVal hw 0).mpr h0), if_pos h0]; simp
      rw [if_neg (fun hc => h0 ((numEqBits_iff_wordVal hw 0).mp hc)), if_neg h0]
      by_cases ht : (wordVal w).pred.unpair.1 = 1
      · rw [if_pos ((numEqBits_iff_wordVal (isDigitWord_tagW hw) 1).mpr
            (by rw [wordVal_tagW hw, ← Nat.pred_eq_sub_one]; exact ht)), if_pos ht]
        by_cases hp : (wordVal w).pred.unpair.2 = a
        · rw [if_pos ((numEqBits_iff_wordVal (isDigitWord_payW hw) a).mpr
              (by rw [wordVal_payW hw, ← Nat.pred_eq_sub_one]; exact hp)), if_pos hp]
          simp
        · rw [if_neg (fun hc => hp (by
              rw [Nat.pred_eq_sub_one, ← wordVal_payW hw]
              exact (numEqBits_iff_wordVal (isDigitWord_payW hw) a).mp hc)), if_neg hp]
          simp
      · rw [if_neg (fun hc => ht (by
            rw [Nat.pred_eq_sub_one, ← wordVal_tagW hw]
            exact (numEqBits_iff_wordVal (isDigitWord_tagW hw) 1).mp hc)), if_neg ht]
        simp
  | himp φ ψ ihφ ihψ =>
      intro w hw
      simp only [fiberW, sentenceMatches]
      exact bin_spec 2 hw (fun {v} hv => ihφ hv) (fun {v} hv => ihψ hv)
  | hand φ ψ ihφ ihψ =>
      intro w hw
      simp only [fiberW, sentenceMatches]
      exact bin_spec 3 hw (fun {v} hv => ihφ hv) (fun {v} hv => ihψ hv)
  | hor φ ψ ihφ ihψ =>
      intro w hw
      simp only [fiberW, sentenceMatches]
      exact bin_spec 4 hw (fun {v} hv => ihφ hv) (fun {v} hv => ihψ hv)

/-! ## The interface, inhabited -/

/-- The escape-leaf guard for one subformula. -/
def holeGuard (χ : Sentence) : TokGuard where
  P := fun c => decide ((Encodable.decode c : Option Sentence) = some χ)
  gW := fiberW χ
  gW_FP := fiberW_mem_FP χ
  gW_spec := by
    intro cur hcur
    rw [decide_eq_true_eq]
    have h1 := length_fiberW_eq_one χ (isDigitWord_digitsToBits hcur)
    rw [wordVal_digitsToBits hcur] at h1
    exact h1.trans (sentenceMatches_eq_one_iff χ (digitVal cur))

/-- **`PatAuto.HoleGuards` is inhabited.**

With it, `PatAuto.ifParseLegacy_mem_FP` decides "this run denotes `ψ`" in the legacy grammar
for an arbitrary target; `SegRec.ifParseFull_mem_FP` is the corresponding unconditional
decision at the full grammar `parseRpn`.

Kind `N+` non-vacuity witness.  Provenance: (a) `fiberW_mem_FP`, `length_fiberW_eq_one`;
(b) `PrefixPatchCompile.sentenceMatches_eq_one_iff`.
Paper node: `app:ifp` -/
def holeGuards : HoleGuards where
  guard := holeGuard
  guard_spec := fun χ c => by simp [holeGuard]

end LogicalInduction.FiberTest
