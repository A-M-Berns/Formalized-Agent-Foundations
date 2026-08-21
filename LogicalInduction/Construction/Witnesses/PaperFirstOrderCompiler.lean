import LogicalInduction.Construction.Witnesses.PaperFirstOrder

/-!
# Numeric compiler for paper first-order prime decompositions

The fixed all-theorems process cannot execute Lean's structural
`paperPrimeDecompose`; it needs a program on Gödel codes.  This file defines that numeric
compiler directly against Foundation's `Semiformula.toNat` layout.  Invalid inputs receive
the harmless public sentence `⊥`.  On genuine arithmetic sentence codes the compiler is
proved extensionally equal to `paperPrimeDecompose`.

Only the two Boolean first-order constructors recurse.  Prime polarity is stored in the
tag-`7` atom handle, so atomic and quantified formulas are constant-depth translations.
-/

namespace LogicalInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Propositional

private lemma encode_public_formula_eq_toNat (φ : Sentence) :
    Encodable.encode φ = φ.toNat := rfl

private def publicBotCode : ℕ := Encodable.encode (⊥ : Sentence)
private def publicTopCode : ℕ := Encodable.encode (⊤ : Sentence)

/-- Numeric encoding of a tag-`7` paper-prime atom whose first-order formula already has
Gödel code `formulaCode`. -/
def paperPrimeAtomCodeRaw (positive : Bool) (formulaCode : ℕ) : ℕ :=
  Nat.pair 1
    (Nat.pair paperPrimeTag (Nat.pair (Encodable.encode positive) formulaCode)) + 1

/-- Numeric propositional negation. -/
def paperPublicNegCode (sentenceCode : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair sentenceCode publicBotCode) + 1

/-- Numeric propositional conjunction. -/
def paperPublicAndCode (left right : ℕ) : ℕ :=
  Nat.pair 3 (Nat.pair left right) + 1

/-- Numeric propositional disjunction. -/
def paperPublicOrCode (left right : ℕ) : ℕ :=
  Nat.pair 4 (Nat.pair left right) + 1

@[simp] lemma paperPrimeAtomCodeRaw_spec (positive : Bool) (φ : ArithmeticSentence) :
    paperPrimeAtomCodeRaw positive (Encodable.encode φ) =
      Encodable.encode (paperPrimeSentence positive φ) := rfl

@[simp] lemma paperPublicNegCode_spec (φ : Sentence) :
    paperPublicNegCode (Encodable.encode φ) = Encodable.encode (∼φ) := rfl

@[simp] lemma paperPublicAndCode_spec (φ ψ : Sentence) :
    paperPublicAndCode (Encodable.encode φ) (Encodable.encode ψ) =
      Encodable.encode (φ ⋏ ψ) := rfl

@[simp] lemma paperPublicOrCode_spec (φ ψ : Sentence) :
    paperPublicOrCode (Encodable.encode φ) (Encodable.encode ψ) =
      Encodable.encode (φ ⋎ ψ) := rfl

/-- Raw total compiler on Foundation first-order sentence codes.  Malformed Boolean child
codes are still translated totality-first; only correctness on genuine encodings is used
by the theorem enumerator. -/
def paperPrimeDecomposeCode : ℕ → ℕ
  | 0 => publicBotCode
  | n@(e + 1) =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      if tag = 0 then paperPrimeAtomCodeRaw true n
      else if tag = 1 then paperPublicNegCode (paperPrimeAtomCodeRaw false n)
      else if tag = 2 then publicTopCode
      else if tag = 3 then publicBotCode
      else if tag = 4 then
        paperPublicAndCode (paperPrimeDecomposeCode payload.unpair.1)
          (paperPrimeDecomposeCode payload.unpair.2)
      else if tag = 5 then
        paperPublicOrCode (paperPrimeDecomposeCode payload.unpair.1)
          (paperPrimeDecomposeCode payload.unpair.2)
      else if tag = 6 then paperPublicNegCode (paperPrimeAtomCodeRaw false n)
      else if tag = 7 then paperPrimeAtomCodeRaw true n
      else publicBotCode
termination_by n => n
decreasing_by
  all_goals
    exact Nat.lt_succ_iff.mpr <|
      le_trans (by first | exact Nat.unpair_left_le _ | exact Nat.unpair_right_le _)
        (Nat.unpair_right_le _)

/-- Correctness of the raw numeric compiler on every genuine arithmetic sentence. -/
lemma paperPrimeDecomposeCode_spec (φ : ArithmeticSentence) :
    paperPrimeDecomposeCode (Encodable.encode φ) =
      Encodable.encode (paperPrimeDecompose φ) := by
  fun_induction paperPrimeDecompose φ <;>
    simp_all [paperPrimeDecomposeCode, publicBotCode, publicTopCode,
      paperPrimeAtomCodeRaw, paperPublicNegCode,
      paperPublicAndCode, paperPublicOrCode, paperPrimeSentence, paperPrimeCode,
      encode_public_formula_eq_toNat, LO.Propositional.Formula.toNat,
      LO.FirstOrder.Semiformula.encode_eq_toNat, LO.FirstOrder.Semiformula.toNat]

/-! ## Primitive recursiveness

The proof follows the repository's propositional decoder compiler: course-of-values
recursion stores the already compiled codes below `n` in a list. -/

private def paperPrimeBinaryStep (tag : ℕ) (prior : List ℕ) (payload : ℕ) : ℕ :=
  let left := prior.getD payload.unpair.1 publicBotCode
  let right := prior.getD payload.unpair.2 publicBotCode
  if tag = 4 then paperPublicAndCode left right else paperPublicOrCode left right

private lemma paperPrimeBinaryStep_prim (tag : ℕ) :
    Primrec₂ (paperPrimeBinaryStep tag) := by
  let left : List ℕ × ℕ → ℕ :=
    fun p => p.1.getD p.2.unpair.1 publicBotCode
  let right : List ℕ × ℕ → ℕ :=
    fun p => p.1.getD p.2.unpair.2 publicBotCode
  have hleft : Primrec left :=
    (Primrec.list_getD publicBotCode).comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hright : Primrec right :=
    (Primrec.list_getD publicBotCode).comp Primrec.fst
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hand : Primrec fun p : List ℕ × ℕ => paperPublicAndCode (left p) (right p) :=
    (Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 3)
        (Primrec₂.natPair.comp hleft hright))
      (Primrec.const 1)).of_eq fun _ => rfl
  have hor : Primrec fun p : List ℕ × ℕ => paperPublicOrCode (left p) (right p) :=
    (Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 4)
        (Primrec₂.natPair.comp hleft hright))
      (Primrec.const 1)).of_eq fun _ => rfl
  exact (Primrec.ite (Primrec.eq.comp (Primrec.const tag) (Primrec.const 4))
    hand hor).to₂.of_eq fun prior payload => by
      simp [paperPrimeBinaryStep, left, right]

private def paperPrimeCodeSucc (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  let n := e + 1
  if tag = 0 then paperPrimeAtomCodeRaw true n
  else if tag = 1 then paperPublicNegCode (paperPrimeAtomCodeRaw false n)
  else if tag = 2 then publicTopCode
  else if tag = 3 then publicBotCode
  else if tag = 4 then paperPrimeBinaryStep 4 prior payload
  else if tag = 5 then paperPrimeBinaryStep 5 prior payload
  else if tag = 6 then paperPublicNegCode (paperPrimeAtomCodeRaw false n)
  else if tag = 7 then paperPrimeAtomCodeRaw true n
  else publicBotCode

private lemma paperPrimeCodeSucc_prim : Primrec₂ paperPrimeCodeSucc := by
  let tag : List ℕ × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List ℕ × ℕ → ℕ := fun p => p.2.unpair.2
  let n : List ℕ × ℕ → ℕ := fun p => p.2 + 1
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hn : Primrec n := Primrec.succ.comp Primrec.snd
  have hprime (positive : Bool) : Primrec fun p : List ℕ × ℕ =>
      paperPrimeAtomCodeRaw positive (n p) := by
    exact (Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec₂.natPair.comp (Primrec.const paperPrimeTag)
          (Primrec₂.natPair.comp (Primrec.const (Encodable.encode positive)) hn)))
      (Primrec.const 1)).of_eq fun _ => rfl
  have hneg : Primrec fun p : List ℕ × ℕ =>
      paperPublicNegCode (paperPrimeAtomCodeRaw false (n p)) := by
    exact (Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (hprime false) (Primrec.const publicBotCode)))
      (Primrec.const 1)).of_eq fun _ => rfl
  have hbin (k : ℕ) : Primrec fun p : List ℕ × ℕ =>
      paperPrimeBinaryStep k p.1 (payload p) :=
    (paperPrimeBinaryStep_prim k).comp Primrec.fst hpayload
  have htagEq (k : ℕ) : PrimrecPred fun p : List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have h7 := Primrec.ite (htagEq 7) (hprime true) (Primrec.const publicBotCode)
  have h6 := Primrec.ite (htagEq 6) hneg h7
  have h5 := Primrec.ite (htagEq 5) (hbin 5) h6
  have h4 := Primrec.ite (htagEq 4) (hbin 4) h5
  have h3 := Primrec.ite (htagEq 3) (Primrec.const publicBotCode) h4
  have h2 := Primrec.ite (htagEq 2) (Primrec.const publicTopCode) h3
  have h1 := Primrec.ite (htagEq 1) hneg h2
  exact (Primrec.ite (htagEq 0) (hprime true) h1).to₂.of_eq fun prior e => by
    simp [paperPrimeCodeSucc, tag, payload, n]

private def paperPrimeCodeStep (prior : List ℕ) : ℕ :=
  prior.length.casesOn publicBotCode (paperPrimeCodeSucc prior)

private lemma paperPrimeCodeStep_prim : Primrec paperPrimeCodeStep := by
  exact (Primrec.nat_casesOn Primrec.list_length (Primrec.const publicBotCode)
    paperPrimeCodeSucc_prim).of_eq fun prior => by simp [paperPrimeCodeStep]

private lemma paperPrimeCodeHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map paperPrimeDecomposeCode).getD k publicBotCode =
      paperPrimeDecomposeCode k := by
  have hzero : paperPrimeDecomposeCode 0 = publicBotCode := by
    simp [paperPrimeDecomposeCode]
  rw [← hzero, List.getD_map]
  simp [hk]

private lemma paperPrimeCodeStep_history (n : ℕ) :
    paperPrimeCodeStep ((List.range n).map paperPrimeDecomposeCode) =
      paperPrimeDecomposeCode n := by
  cases n with
  | zero => simp [paperPrimeCodeStep, paperPrimeDecomposeCode]
  | succ e =>
      let payload := e.unpair.2
      have hleft : payload.unpair.1 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : payload.unpair.2 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      simp only [paperPrimeCodeStep, List.length_map, List.length_range]
      by_cases h4 : e.unpair.1 = 4
      · simp only [paperPrimeCodeSucc, h4, ↓reduceIte]
        rw [paperPrimeDecomposeCode]
        simp only [h4, ↓reduceIte]
        unfold paperPrimeBinaryStep
        rw [paperPrimeCodeHistory_getD hleft, paperPrimeCodeHistory_getD hright]
        simp [payload]
      by_cases h5 : e.unpair.1 = 5
      · simp only [paperPrimeCodeSucc, h5, ↓reduceIte]
        rw [paperPrimeDecomposeCode]
        simp only [h5, ↓reduceIte]
        unfold paperPrimeBinaryStep
        rw [paperPrimeCodeHistory_getD hleft, paperPrimeCodeHistory_getD hright]
        simp [payload]
      · simp [paperPrimeCodeSucc, paperPrimeDecomposeCode, h4, h5]

/-- The first-order prime-decomposition compiler is primitive recursive on raw Gödel
codes.  This is the executable bridge needed by a fixed universal theorem process. -/
lemma paperPrimeDecomposeCode_prim : Primrec paperPrimeDecomposeCode := by
  have hstep : Primrec₂ fun (_ : Unit) (prior : List ℕ) =>
      some (paperPrimeCodeStep prior) :=
    Primrec₂.option_some_iff.mpr (paperPrimeCodeStep_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec (fun (_ : Unit) n => paperPrimeDecomposeCode n)
    hstep (fun _ n => by simpa using congrArg some (paperPrimeCodeStep_history n))
  exact (hrec.comp (Primrec.const ()) Primrec.id).of_eq fun _ => rfl

#print axioms paperPrimeDecomposeCode_spec
#print axioms paperPrimeDecomposeCode_prim

end LogicalInduction
