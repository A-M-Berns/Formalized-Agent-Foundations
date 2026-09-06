import LogicalInduction.Framework.Emission.RpnComputation
import LogicalInduction.Framework.Emission.WriteOut
import Mathlib.Data.Rat.Denumerable

/-!
# Codes and parser certificates

Every efficiency claim in this development is charged against a *concrete* code for the object
being emitted, so each of the repository's data types needs a `Primcodable` instance proved
from this project's own decoder rather than from a denumeration fallback, and each parser
declared in `Framework/` needs a primitive-recursive certificate.  This module is that layer,
and it is the only place either is built.  Nothing here is about §5:
`Construction/LIACompiler.lean` consumes it to compile the market maker, the budgeter and the
trading firm, and seven modules in the `Conditioning/`, `Knowledge/`, `NonDogmatism/`,
`Freeze/` and `Statistics/` lanes consume it for the codes and the parser certificates alone.

## Encodings

`Primcodable` instances for `Sentence`, `ℚ` (with an integer layer beneath it), `EF`,
`Strategy n` and `Finset Sentence` — the codes `def:ec`'s write-out metering is charged
against.  Foundation's decoders recurse on strictly smaller codes, so every instance is
compiled by primitive-recursive strong recursion rather than by structural recursion on
`Formula` or `EF`.  Beside them sit the arithmetic certificates the emission lanes name
directly: `ratNum_prim`, `ratDen_prim`, `ratAdd_prim`, `ratSub_prim`, `ratMul_prim`,
`ratDiv_prim`, `ratInv_prim`, `ratPow_prim`, `ratLE_prim`, `ratMax_prim` and their integer
counterparts, the `EF` constructor certificates (`efConst_prim`, `efAdd_prim`, `efMul_prim`,
`efMax_prim`, `efPrice_prim`, `efSafeRecip_prim`), and the two list utilities that put a
finite set in canonical form (`listDedup`, `insertionSort_prim`).

## The token decode

`parseRpnC_prim`, `unRpn_prim`, `negFormulaCode_prim`,
`parseStructuredArithmeticFormula_prim`, and the whole-value naming residues
`RpnSentenceCodes.primrec` and `BigSentenceCodes.primrec`, each with its `.exists_code`
corollary.  The parsers compiled here are the ones defined in `Framework/Criterion.lean` and
`Framework/Emission/RpnSentence.lean`, whose tags `20`, `21` and `22` expand `¬`, `⟹` and
`⟺` into normal form internally and charge nothing for it (`dd:nnf`).  A written-out sentence
sequence is reassembled into whole-value codes here, which is legitimate because primitive
recursion carries no time budget — this is the route by which a market quote table keyed by
sentence code accepts write-out data.

`Nat.sqrt` is made locally irreducible around the `Primrec` proofs over the deeply nested
`Primcodable` product types.  The blowup is in `Nat.sqrt` — tens of thousands of unfoldings,
reached through `Nat.unpair` while `isDefEq` reconciles the product type's `Primcodable`
instance — and not in the arithmetic a proof is about; without the attribute `whnf` unfolds
`Nat.sqrt`'s well-founded definition and does not terminate.  The individual sites cite this
paragraph.
-/

namespace LogicalInduction

open LO.Propositional

/-! ## Primitive-recursive `Sentence` codes

Foundation's decoder for propositional sentences recurses on strictly smaller Gödel
numbers, so its encode-after-decode normalizer is compiled by strong recursion (see the
module header).  The four bridges below state `Encodable.encode` and `Encodable.decode` at
`EF` and at `LO.Propositional.Formula ℕ` in their concrete `toNat`/`ofNat` forms, so the
encoding proofs can `simp` with the real decoder. -/
private lemma encode_ef_eq_toNat (e : EF) : Encodable.encode e = e.toNat := rfl
private lemma decode_ef_eq_ofNat (n : ℕ) :
    (Encodable.decode n : Option EF) = EF.ofNat n := rfl
private lemma encode_formula_eq_toNat (φ : LO.Propositional.Formula ℕ) :
    Encodable.encode φ = φ.toNat := rfl
private lemma decode_formula_eq_ofNat (n : ℕ) :
    (Encodable.decode n : Option (LO.Propositional.Formula ℕ)) =
      LO.Propositional.Formula.ofNat n := rfl

private def formulaBinaryNorm (tag : ℕ) (prior : List ℕ) (children : ℕ) : ℕ :=
  let left := prior.getD children.unpair.1 0
  let right := prior.getD children.unpair.2 0
  if left = 0 ∨ right = 0 then 0
  else Nat.pair tag (Nat.pair (left - 1) (right - 1)) + 2

private lemma formulaBinaryNorm_prim (tag : ℕ) :
    Primrec₂ (formulaBinaryNorm tag) := by
  let childLeft : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.1 0
  let childRight : List ℕ × ℕ → ℕ := fun p => p.1.getD p.2.unpair.2 0
  have hindexLeft : Primrec fun p : List ℕ × ℕ => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hindexRight : Primrec fun p : List ℕ × ℕ => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hleft : Primrec childLeft :=
    (Primrec.list_getD 0).comp Primrec.fst hindexLeft
  have hright : Primrec childRight :=
    (Primrec.list_getD 0).comp Primrec.fst hindexRight
  have hbad : PrimrecPred fun p : List ℕ × ℕ =>
      childLeft p = 0 ∨ childRight p = 0 :=
    (Primrec.eq.comp hleft (Primrec.const 0)).or
      (Primrec.eq.comp hright (Primrec.const 0))
  have hchildren : Primrec fun p : List ℕ × ℕ =>
      Nat.pair (childLeft p - 1) (childRight p - 1) :=
    Primrec₂.natPair.comp
      (Primrec.nat_sub.comp hleft (Primrec.const 1))
      (Primrec.nat_sub.comp hright (Primrec.const 1))
  have htagged : Primrec fun p : List ℕ × ℕ =>
      Nat.pair tag (Nat.pair (childLeft p - 1) (childRight p - 1)) :=
    Primrec₂.natPair.comp (Primrec.const tag) hchildren
  have hresult : Primrec fun p : List ℕ × ℕ =>
      Nat.pair tag (Nat.pair (childLeft p - 1) (childRight p - 1)) + 2 :=
    Primrec.nat_add.comp htagged (Primrec.const 2)
  exact (Primrec.ite hbad (Primrec.const 0) hresult).to₂.of_eq fun prior children => by
    simp only [formulaBinaryNorm, childLeft, childRight]

private def formulaNormSucc (prior : List ℕ) (e : ℕ) : ℕ :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then 2
  else if tag = 1 then Nat.pair 1 payload + 2
  else if tag = 2 then formulaBinaryNorm 2 prior payload
  else if tag = 3 then formulaBinaryNorm 3 prior payload
  else if tag = 4 then formulaBinaryNorm 4 prior payload
  else 0

private lemma formulaNormSucc_prim : Primrec₂ formulaNormSucc := by
  let tag : List ℕ × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List ℕ × ℕ → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have htaggedAtom : Primrec fun p : List ℕ × ℕ => Nat.pair 1 (payload p) + 2 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 1) hpayload) (Primrec.const 2)
  have hbinary (k : ℕ) : Primrec fun p : List ℕ × ℕ =>
      formulaBinaryNorm k p.1 (payload p) :=
    (formulaBinaryNorm_prim k).comp Primrec.fst hpayload
  have htagEq (k : ℕ) : PrimrecPred fun p : List ℕ × ℕ => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  exact (Primrec.ite (htagEq 0) (Primrec.const 2)
    (Primrec.ite (htagEq 1) htaggedAtom
      (Primrec.ite (htagEq 2) (hbinary 2)
        (Primrec.ite (htagEq 3) (hbinary 3)
          (Primrec.ite (htagEq 4) (hbinary 4)
            (Primrec.const 0)))))).to₂.of_eq fun prior e => by
    simp only [formulaNormSucc, tag, payload]

private def formulaNormList (prior : List ℕ) : ℕ :=
  prior.length.casesOn 0 (formulaNormSucc prior)

private lemma formulaNormList_prim : Primrec formulaNormList := by
  exact (Primrec.nat_casesOn Primrec.list_length (Primrec.const 0)
    formulaNormSucc_prim).of_eq fun prior => by
      simp only [formulaNormList]

private def sentenceDecodeNorm (n : ℕ) : ℕ :=
  match (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) with
  | none => 0
  | some phi => LO.Propositional.Formula.toNat phi + 1

private lemma formulaHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map fun m =>
      sentenceDecodeNorm m).getD k 0 = sentenceDecodeNorm k := by
  have hzero : sentenceDecodeNorm 0 = 0 := by
    simp [sentenceDecodeNorm, LO.Propositional.Formula.ofNat]
  rw [← hzero, List.getD_map]
  simp [hk]

private lemma formulaBinaryNorm_history (tag payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    formulaBinaryNorm tag ((List.range n).map sentenceDecodeNorm) payload =
      match (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.1 : Option Sentence),
          (@LO.Propositional.Formula.ofNat ℕ inferInstance payload.unpair.2 : Option Sentence) with
      | some phi, some psi => Nat.pair tag (Nat.pair phi.toNat psi.toNat) + 2
      | _, _ => 0 := by
  unfold formulaBinaryNorm
  rw [formulaHistory_getD hleft, formulaHistory_getD hright]
  cases hL : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.1 : Option Sentence) <;>
    cases hR : (@LO.Propositional.Formula.ofNat ℕ inferInstance
      payload.unpair.2 : Option Sentence) <;>
    simp [sentenceDecodeNorm, hL, hR]

private lemma formulaNormList_history (n : ℕ) :
    formulaNormList ((List.range n).map fun k =>
      sentenceDecodeNorm k) = sentenceDecodeNorm n := by
  cases n with
  | zero => simp [formulaNormList, sentenceDecodeNorm, LO.Propositional.Formula.ofNat]
  | succ e =>
      let tag := e.unpair.1
      let payload := e.unpair.2
      have hleft : payload.unpair.1 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have hright : payload.unpair.2 < e + 1 := by
        dsimp [payload]
        exact Nat.lt_succ_iff.mpr <|
          le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      by_cases h0 : tag = 0
      · simp [sentenceDecodeNorm, formulaNormList, formulaNormSucc, LO.Propositional.Formula.ofNat,
          LO.Propositional.Formula.toNat,
          Nat.pair, tag, h0]
      by_cases h1 : tag = 1
      · simp [sentenceDecodeNorm, formulaNormList, formulaNormSucc, LO.Propositional.Formula.ofNat,
          LO.Propositional.Formula.toNat,
          Nat.pair, tag, h1]
      by_cases h2 : tag = 2
      · subst tag
        have hb := formulaBinaryNorm_history 2 payload (e + 1) hleft hright
        simp only [formulaNormList, List.length_map, List.length_range,
          formulaNormSucc, h2, ↓reduceIte]
        rw [hb]
        unfold sentenceDecodeNorm
        simp only [LO.Propositional.Formula.ofNat, h2]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.2 : Option Sentence) <;>
          simp [LO.Propositional.Formula.toNat]
      by_cases h3 : tag = 3
      · subst tag
        have hb := formulaBinaryNorm_history 3 payload (e + 1) hleft hright
        simp only [formulaNormList, List.length_map, List.length_range,
          formulaNormSucc, h3, ↓reduceIte]
        rw [hb]
        unfold sentenceDecodeNorm
        simp only [LO.Propositional.Formula.ofNat, h3]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.2 : Option Sentence) <;>
          simp [LO.Propositional.Formula.toNat]
      by_cases h4 : tag = 4
      · subst tag
        have hb := formulaBinaryNorm_history 4 payload (e + 1) hleft hright
        simp only [formulaNormList, List.length_map, List.length_range,
          formulaNormSucc, h4, ↓reduceIte]
        rw [hb]
        unfold sentenceDecodeNorm
        simp only [LO.Propositional.Formula.ofNat, h4]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.2 : Option Sentence) <;>
          simp [LO.Propositional.Formula.toNat]
      · have htag : 5 ≤ tag := by omega
        simp [sentenceDecodeNorm, formulaNormList, formulaNormSucc, LO.Propositional.Formula.ofNat,

          tag, h0, h1, h2, h3, h4]

/-- Foundation's concrete Gödel encoding of propositional sentences is primitive-recursive.
This is an encoding theorem only; it contains no semantic or logical-inductor premise. -/
instance sentencePrimcodable : Primcodable Sentence where
  prim := by
    have hrec : Primrec sentenceDecodeNorm :=
      Primrec.of_courseOfValues sentenceDecodeNorm formulaNormList_prim
        formulaNormList_history
    exact Primrec.nat_iff.mp (hrec.of_eq fun n => by
      change sentenceDecodeNorm n = Encodable.encode
        ((@LO.Propositional.Formula.ofNat ℕ inferInstance n) : Option Sentence)
      cases h : (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) <;>
        simp [sentenceDecodeNorm, h, encode_formula_eq_toNat])

/-! ## Integer and rational codes -/

private def intCodeNatAbs (n : ℕ) : ℕ :=
  if n.bodd then n.div2 + 1 else n.div2

private lemma intCodeNatAbs_prim : Primrec intCodeNatAbs := by
  exact (Primrec.cond Primrec.nat_bodd
    (Primrec.nat_add.comp Primrec.nat_div2 (Primrec.const 1))
    Primrec.nat_div2).of_eq fun n => by
      simp only [intCodeNatAbs]
      cases n.bodd <;> rfl

private lemma intCodeNatAbs_eq_decode (n : ℕ) :
    intCodeNatAbs n =
      ((@Encodable.decode ℤ Int.encodable n).getD 0).natAbs := by
  simp [intCodeNatAbs, Equiv.intEquivNat,
    Equiv.intEquivNatSumNat, Equiv.natSumNatEquivNat,
    Equiv.boolProdNatEquivNat]
  cases hodd : n.bodd
  · change n.div2 = Int.natAbs (Int.ofNat n.div2)
    rfl
  · change n.div2 + 1 = Int.natAbs (Int.negSucc n.div2)
    rfl

/-- A bounded-common-divisor presentation of coprimality.  The `max + 1` bound also
handles the degenerate zero cases. -/
private def coprimeBounded (a b : ℕ) : Prop :=
  ∀ k < max a b + 1, k ∣ a → k ∣ b → k = 1

private instance coprimeBoundedDecidable : DecidableRel coprimeBounded :=
  fun a b => by
    dsimp [coprimeBounded]
    infer_instance

private lemma coprimeBounded_iff (a b : ℕ) : coprimeBounded a b ↔ a.Coprime b := by
  constructor
  · intro h
    rw [Nat.coprime_iff_isRelPrime]
    intro k hka hkb
    have hnz : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hnz
      push_neg at hnz
      have := h 0 (by omega) (by simp [hnz.1]) (by simp [hnz.2])
      omega
    have hklt : k < max a b + 1 := by
      rcases hnz with ha | hb
      · have hka' : k ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hka
        omega
      · have hkb' : k ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hkb
        omega
    simp [h k hklt hka hkb]
  · intro h k _ hka hkb
    exact Nat.eq_one_of_dvd_coprimes h hka hkb

/-- Divisibility is primitive recursive, through the remainder test. -/
private lemma natDvd_prim : PrimrecRel fun k a : ℕ => k ∣ a := by
  apply PrimrecPred.of_eq
    (Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.snd : Primrec fun p : ℕ × ℕ => p.2)
        (Primrec.fst : Primrec fun p : ℕ × ℕ => p.1))
      (Primrec.const (α := ℕ × ℕ) 0))
  intro p
  rcases p with ⟨k, a⟩
  simp [Nat.dvd_iff_mod_eq_zero]

private lemma coprimeBounded_prim : PrimrecRel coprimeBounded := by
  have hdvd : PrimrecRel fun k a : ℕ => k ∣ a := natDvd_prim
  have hunpairLeft : Primrec fun n : ℕ => n.unpair.1 :=
    Primrec.fst.comp Primrec.unpair
  have hunpairRight : Primrec fun n : ℕ => n.unpair.2 :=
    Primrec.snd.comp Primrec.unpair
  have hdvdLeft : PrimrecRel fun k y : ℕ => k ∣ y.unpair.1 :=
    hdvd.comp₂ Primrec₂.left (hunpairLeft.comp₂ Primrec₂.right)
  have hdvdRight : PrimrecRel fun k y : ℕ => k ∣ y.unpair.2 :=
    hdvd.comp₂ Primrec₂.left (hunpairRight.comp₂ Primrec₂.right)
  have hone : PrimrecRel fun k (_ : ℕ) => k = 1 :=
    Primrec.eq.comp₂ Primrec₂.left (Primrec₂.const 1)
  have hbody : PrimrecRel fun k y : ℕ =>
      k ∣ y.unpair.1 → k ∣ y.unpair.2 → k = 1 := by
    exact ((hdvdLeft.and hdvdRight).not.or hone).of_eq fun p => by tauto
  have hbound : Primrec fun y : ℕ => max y.unpair.1 y.unpair.2 + 1 :=
    Primrec.nat_add.comp
      (Primrec.nat_max.comp hunpairLeft hunpairRight) (Primrec.const 1)
  have hall : PrimrecRel fun n y : ℕ =>
      ∀ k < n, k ∣ y.unpair.1 → k ∣ y.unpair.2 → k = 1 := hbody.forall_lt
  have hpair : Primrec fun p : ℕ × ℕ => Nat.pair p.1 p.2 :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  exact (hall.comp (hbound.comp hpair) hpair).of_eq fun p => by
    simp only [Nat.unpair_pair, coprimeBounded]

/-- Euclid's gcd, compiled as the greatest common divisor below the explicit `a+b`
bound.  This avoids relying on the kernel implementation of Euclid's recursion. -/
private lemma natGCD_prim : Primrec₂ Nat.gcd := by
  let common : ℕ × ℕ → ℕ → Prop := fun p k => k ∣ p.1 ∧ k ∣ p.2
  have hcommon : PrimrecRel common := by
    exact (natDvd_prim.comp₂ Primrec₂.right (Primrec.fst.comp₂ Primrec₂.left)).and
      (natDvd_prim.comp₂ Primrec₂.right (Primrec.snd.comp₂ Primrec₂.left))
  have hbound : Primrec fun p : ℕ × ℕ => p.1 + p.2 :=
    Primrec.nat_add.comp Primrec.fst Primrec.snd
  have hfind : Primrec fun p : ℕ × ℕ =>
      (p.1 + p.2).findGreatest (common p) :=
    Primrec.nat_findGreatest hbound hcommon
  exact hfind.to₂.of_eq fun a b => by
    dsimp only [common]
    by_cases hz : a + b = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a
      subst b
      rfl
    · have hboundGCD : Nat.gcd a b ≤ a + b := by
        by_cases ha : a = 0
        · subst a
          simp
        · exact (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha)).trans (Nat.le_add_right a b)
      have hgcdCommon : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b :=
        ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩
      have hgcdLe : Nat.gcd a b ≤
          (a + b).findGreatest (fun k => k ∣ a ∧ k ∣ b) :=
        Nat.le_findGreatest hboundGCD hgcdCommon
      have honeLe : 1 ≤ a + b := Nat.one_le_iff_ne_zero.mpr hz
      have hfindCommon :
          (a + b).findGreatest (fun k => k ∣ a ∧ k ∣ b) ∣ a ∧
            (a + b).findGreatest (fun k => k ∣ a ∧ k ∣ b) ∣ b :=
        Nat.findGreatest_spec (P := fun k => k ∣ a ∧ k ∣ b) honeLe
          ⟨one_dvd a, one_dvd b⟩
      have hgcdPos : 0 < Nat.gcd a b := by
        by_cases ha : a = 0
        · subst a
          have hb : 0 < b := by omega
          simpa using hb
        · exact Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
      have hfindLe : (a + b).findGreatest (fun k => k ∣ a ∧ k ∣ b) ≤
          Nat.gcd a b :=
        Nat.le_of_dvd hgcdPos (Nat.dvd_gcd hfindCommon.1 hfindCommon.2)
      exact le_antisymm hfindLe hgcdLe

private def ratCodeValid (n : ℕ) : Prop :=
  0 < n.unpair.2 ∧ coprimeBounded (intCodeNatAbs n.unpair.1) n.unpair.2

private instance ratCodeValidDecidable : DecidablePred ratCodeValid :=
  fun n => by
    dsimp [ratCodeValid]
    infer_instance

private lemma ratCodeValid_prim : PrimrecPred ratCodeValid := by
  have hden : Primrec fun n : ℕ => n.unpair.2 :=
    Primrec.snd.comp Primrec.unpair
  have hnum : Primrec fun n : ℕ => intCodeNatAbs n.unpair.1 :=
    intCodeNatAbs_prim.comp (Primrec.fst.comp Primrec.unpair)
  have hpos : PrimrecPred fun n : ℕ => 0 < n.unpair.2 :=
    Primrec.nat_lt.comp (Primrec.const 0) hden
  have hcop : PrimrecPred fun n : ℕ =>
      coprimeBounded (intCodeNatAbs n.unpair.1) n.unpair.2 :=
    coprimeBounded_prim.comp hnum hden
  exact (hpos.and hcop).of_eq fun n => by simp only [ratCodeValid]

private def ratDecodeNorm (n : ℕ) : ℕ :=
  if ratCodeValid n then n + 1 else 0

private lemma ratDecodeNorm_prim : Primrec ratDecodeNorm := by
  exact (Primrec.ite ratCodeValid_prim
    (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
    (Primrec.const 0)).of_eq fun n => by simp only [ratDecodeNorm, id_eq]

private lemma ratDecodeNorm_eq (n : ℕ) :
    ratDecodeNorm n = Encodable.encode (@Encodable.decode ℚ inferInstance n) := by
  have hvalid : ratCodeValid n ↔
      0 < n.unpair.2 ∧
        (Denumerable.ofNat ℤ n.unpair.1).natAbs.Coprime n.unpair.2 := by
    simp [ratCodeValid, coprimeBounded_iff, intCodeNatAbs_eq_decode]
  have hencodeInt (k : ℕ) : Equiv.intEquivNat (Denumerable.ofNat ℤ k) = k := by
    exact @Denumerable.encode_ofNat ℤ Denumerable.int k
  have hsymm : (Equiv.intEquivNat.symm n.unpair.1 : ℤ) =
      Denumerable.ofNat ℤ n.unpair.1 :=
    (Equiv.symm_apply_eq _).mpr (hencodeInt n.unpair.1).symm
  have hstep : (Encodable.decode n.unpair.2 :
      Option {d : ℕ // 0 < d ∧
        (Equiv.intEquivNat.symm n.unpair.1 : ℤ).natAbs.Coprime d}) =
      if hd : 0 < n.unpair.2 ∧
          (Equiv.intEquivNat.symm n.unpair.1 : ℤ).natAbs.Coprime n.unpair.2 then
        some ⟨n.unpair.2, hd⟩ else none := rfl
  by_cases h : ratCodeValid n
  · have hc' : 0 < n.unpair.2 ∧
        (Equiv.intEquivNat.symm n.unpair.1 : ℤ).natAbs.Coprime n.unpair.2 := by
      rw [hsymm]; exact hvalid.mp h
    simp [ratDecodeNorm, h, Encodable.decode_ofEquiv,
      Encodable.decode_sigma_val, hstep, hc']
    rw [dif_pos hc'.2]
    simp [Encodable.encode_ofEquiv, Encodable.encode_sigma_val,
      Encodable.Subtype.encode_eq, Nat.pair_unpair]
  · have hc' : ¬(0 < n.unpair.2 ∧
        (Equiv.intEquivNat.symm n.unpair.1 : ℤ).natAbs.Coprime n.unpair.2) := by
      rw [hsymm]; exact mt hvalid.mpr h
    simp [ratDecodeNorm, h, Encodable.decode_ofEquiv,
      Encodable.decode_sigma_val, hstep, hc']

/-- Mathlib's concrete reduced-numerator/positive-denominator rational encoding is
primitive-recursive.  Unlike the generic denumeration fallback, this is the same encoding
used by `EF.const` and by all external rational quote codes. -/
instance ratPrimcodable : Primcodable ℚ where
  prim := Primrec.nat_iff.mp (ratDecodeNorm_prim.of_eq ratDecodeNorm_eq)

lemma ratNum_prim : Primrec Rat.num := by
  apply Primrec.encode_iff.mp
  exact (Primrec.fst.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun q => by
    simp only [encode_rat_eq, Nat.unpair_pair]

lemma ratDen_prim : Primrec Rat.den := by
  exact (Primrec.snd.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun q => by
    simp only [encode_rat_eq, Nat.unpair_pair]

private lemma intCodeNatAbs_encode (z : ℤ) :
    intCodeNatAbs (Encodable.encode z) = z.natAbs := by
  cases z with
  | ofNat n => simp [intCodeNatAbs, encode_int_natCast]
  | negSucc n =>
      have hencode : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl
      rw [hencode]
      simp [intCodeNatAbs]

lemma intNatAbs_prim : Primrec Int.natAbs :=
  (intCodeNatAbs_prim.comp Primrec.encode).of_eq intCodeNatAbs_encode

/-! The concrete integer encoding alternates nonnegative and negative values.  Working at
the code level keeps the rational compiler independent of any opaque arithmetic oracle. -/

private def intCodeNeg (n : ℕ) : ℕ :=
  if n = 0 then 0 else bif n.bodd then n + 1 else n - 1

private lemma intCodeNeg_prim : Primrec intCodeNeg := by
  have hzero : PrimrecPred fun n : ℕ => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hodd : Primrec fun n : ℕ => bif n.bodd then n + 1 else n - 1 :=
    Primrec.cond Primrec.nat_bodd
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  exact (Primrec.ite hzero (Primrec.const 0) hodd).of_eq fun n => by
    simp only [intCodeNeg]

private lemma intCodeNeg_encode (z : ℤ) :
    intCodeNeg (Encodable.encode z) = Encodable.encode (-z) := by
  cases z with
  | ofNat n =>
      cases n with
      | zero =>
          change intCodeNeg 0 = 0
          simp [intCodeNeg]
      | succ n =>
          change intCodeNeg (2 * (n + 1)) = 2 * n + 1
          simp [intCodeNeg, Nat.bodd_mul]
          omega
  | negSucc n =>
      change intCodeNeg (2 * n + 1) = 2 * (n + 1)
      simp [intCodeNeg, Nat.bodd_mul]
      omega

private lemma encodeIntNegNat {n : ℕ} (hn : 0 < n) :
    Encodable.encode (-((n : ℤ))) = 2 * n - 1 := by
  have h : -((n : ℤ)) = Int.negSucc (n - 1) := by omega
  rw [h, show Encodable.encode (Int.negSucc (n - 1)) = 2 * (n - 1) + 1 from rfl]
  omega

lemma intNeg_prim : Primrec fun z : ℤ => -z :=
  Primrec.encode_iff.mp <|
    (intCodeNeg_prim.comp Primrec.encode).of_eq intCodeNeg_encode

/-- Encode the integer difference `positive - negative`, where both inputs are naturals. -/
private def intCodeSubNat (positive negative : ℕ) : ℕ :=
  if negative ≤ positive then 2 * (positive - negative)
  else 2 * (negative - positive) - 1

private lemma intCodeSubNat_prim : Primrec₂ intCodeSubNat := by
  have hpos : Primrec fun p : ℕ × ℕ => 2 * (p.1 - p.2) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_sub.comp Primrec.fst Primrec.snd)
  have hneg : Primrec fun p : ℕ × ℕ => 2 * (p.2 - p.1) - 1 :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp Primrec.snd Primrec.fst))
      (Primrec.const 1)
  exact (Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    hpos hneg).to₂.of_eq fun positive negative => by
      simp only [intCodeSubNat]

private lemma intCodeSubNat_eq (positive negative : ℕ) :
    intCodeSubNat positive negative =
      Encodable.encode ((positive : ℤ) - (negative : ℤ)) := by
  by_cases h : negative ≤ positive
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp [intCodeSubNat, encode_int_natCast]
  · have hlt : positive < negative := Nat.lt_of_not_ge h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    subst negative
    rw [show (positive : ℤ) - (positive + k + 1 : ℕ) = Int.negSucc k by omega]
    change intCodeSubNat positive (positive + k + 1) = 2 * k + 1
    simp [intCodeSubNat]
    omega

private def intCodeAdd (a b : ℕ) : ℕ :=
  bif a.bodd then
    bif b.bodd then a + b + 1
    else intCodeSubNat b.div2 (a.div2 + 1)
  else bif b.bodd then intCodeSubNat a.div2 (b.div2 + 1)
  else a + b

private lemma intCodeAdd_prim : Primrec₂ intCodeAdd := by
  have ha : Primrec fun p : ℕ × ℕ => p.1.bodd :=
    Primrec.nat_bodd.comp Primrec.fst
  have hb : Primrec fun p : ℕ × ℕ => p.2.bodd :=
    Primrec.nat_bodd.comp Primrec.snd
  have haMag : Primrec fun p : ℕ × ℕ => p.1.div2 + 1 :=
    Primrec.nat_add.comp (Primrec.nat_div2.comp Primrec.fst) (Primrec.const 1)
  have hbMag : Primrec fun p : ℕ × ℕ => p.2.div2 + 1 :=
    Primrec.nat_add.comp (Primrec.nat_div2.comp Primrec.snd) (Primrec.const 1)
  have hbothNeg : Primrec fun p : ℕ × ℕ => p.1 + p.2 + 1 :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)
      (Primrec.const 1)
  have hnegPos : Primrec fun p : ℕ × ℕ =>
      intCodeSubNat p.2.div2 (p.1.div2 + 1) :=
    intCodeSubNat_prim.comp
      (Primrec.nat_div2.comp Primrec.snd) haMag
  have hposNeg : Primrec fun p : ℕ × ℕ =>
      intCodeSubNat p.1.div2 (p.2.div2 + 1) :=
    intCodeSubNat_prim.comp
      (Primrec.nat_div2.comp Primrec.fst) hbMag
  have hbothPos : Primrec fun p : ℕ × ℕ => p.1 + p.2 :=
    Primrec.nat_add.comp Primrec.fst Primrec.snd
  exact (Primrec.cond ha (Primrec.cond hb hbothNeg hnegPos)
    (Primrec.cond hb hposNeg hbothPos)).to₂.of_eq fun a b => by
      simp only [intCodeAdd]

private lemma intCodeAdd_encode (a b : ℤ) :
    intCodeAdd (Encodable.encode a) (Encodable.encode b) =
      Encodable.encode (a + b) := by
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          change intCodeAdd (2 * a) (2 * b) = 2 * (a + b)
          simp [intCodeAdd, Nat.bodd_mul]
          omega
      | negSucc b =>
          change intCodeAdd (2 * a) (2 * b + 1) =
            Encodable.encode ((a : ℤ) - (b + 1 : ℕ))
          simp [intCodeAdd, intCodeSubNat_eq, Nat.bodd_mul,
            Nat.div2_bit0]
  | negSucc a =>
      cases b with
      | ofNat b =>
          have hdiv : (1 + 2 * a).div2 = a := by
            simpa [Nat.add_comm] using Nat.div2_bit1 a
          change intCodeAdd (2 * a + 1) (2 * b) =
            Encodable.encode ((b : ℤ) - (a + 1 : ℕ))
          simp [intCodeAdd, intCodeSubNat_eq, add_comm, Nat.bodd_add,
            Nat.bodd_mul, Nat.div2_bit0, hdiv]
      | negSucc b =>
          change intCodeAdd (2 * a + 1) (2 * b + 1) = 2 * (a + b + 1) + 1
          simp [intCodeAdd, Nat.bodd_mul]
          omega

private lemma intAdd_prim : Primrec₂ fun a b : ℤ => a + b := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeAdd_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq fun a b => intCodeAdd_encode a b

private def intCodeMul (a b : ℕ) : ℕ :=
  let magnitude := intCodeNatAbs a * intCodeNatAbs b
  if magnitude = 0 then 0
  else if a.bodd = b.bodd then 2 * magnitude else 2 * magnitude - 1

private lemma intCodeMul_prim : Primrec₂ intCodeMul := by
  let magnitude : ℕ × ℕ → ℕ := fun p =>
    intCodeNatAbs p.1 * intCodeNatAbs p.2
  have hmag : Primrec magnitude :=
    Primrec.nat_mul.comp (intCodeNatAbs_prim.comp Primrec.fst)
      (intCodeNatAbs_prim.comp Primrec.snd)
  have hzero : PrimrecPred fun p : ℕ × ℕ => magnitude p = 0 :=
    Primrec.eq.comp hmag (Primrec.const 0)
  have hsame : PrimrecPred fun p : ℕ × ℕ => p.1.bodd = p.2.bodd :=
    Primrec.eq.comp (Primrec.nat_bodd.comp Primrec.fst)
      (Primrec.nat_bodd.comp Primrec.snd)
  have hpos : Primrec fun p : ℕ × ℕ => 2 * magnitude p :=
    Primrec.nat_mul.comp (Primrec.const 2) hmag
  have hneg : Primrec fun p : ℕ × ℕ => 2 * magnitude p - 1 :=
    Primrec.nat_sub.comp hpos (Primrec.const 1)
  exact (Primrec.ite hzero (Primrec.const 0)
    (Primrec.ite hsame hpos hneg)).to₂.of_eq fun a b => by
      simp only [intCodeMul, magnitude]

private lemma intCodeMul_encode (a b : ℤ) :
    intCodeMul (Encodable.encode a) (Encodable.encode b) =
      Encodable.encode (a * b) := by
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          change intCodeMul (2 * a) (2 * b) = 2 * (a * b)
          simp [intCodeMul, intCodeNatAbs, Nat.bodd_mul, Nat.div2_bit0]
      | negSucc b =>
          cases a with
          | zero =>
              change intCodeMul 0 (2 * b + 1) = Encodable.encode (0 * Int.negSucc b)
              have hz : (0 : ℤ) * Int.negSucc b = (0 : ℤ) := by simp
              rw [hz, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, encode_int_natCast]
              simp [intCodeMul, intCodeNatAbs]
          | succ a =>
              change intCodeMul (2 * (a + 1)) (2 * b + 1) =
                Encodable.encode (Int.ofNat (a + 1) * Int.negSucc b)
              rw [show Int.ofNat (a + 1) * Int.negSucc b =
                -(((a + 1) * (b + 1) : ℕ) : ℤ) by
                  simp [Int.negSucc_eq]
                  ring]
              rw [encodeIntNegNat (Nat.mul_pos (by omega) (by omega))]
              simp [intCodeMul, intCodeNatAbs, Nat.bodd_mul,
                Nat.div2_bit0]
  | negSucc a =>
      cases b with
      | ofNat b =>
          cases b with
          | zero =>
              change intCodeMul (2 * a + 1) 0 = Encodable.encode (Int.negSucc a * 0)
              rw [show Encodable.encode (Int.negSucc a * 0) = 0 from rfl]
              simp [intCodeMul, intCodeNatAbs]
          | succ b =>
              change intCodeMul (2 * a + 1) (2 * (b + 1)) =
                Encodable.encode (Int.negSucc a * Int.ofNat (b + 1))
              rw [show Int.negSucc a * Int.ofNat (b + 1) =
                -(((a + 1) * (b + 1) : ℕ) : ℤ) by
                  simp [Int.negSucc_eq]
                  ring]
              rw [encodeIntNegNat (Nat.mul_pos (by omega) (by omega))]
              simp [intCodeMul, intCodeNatAbs, Nat.bodd_mul,
                Nat.div2_bit0]
      | negSucc b =>
          rw [Int.negSucc_mul_negSucc]
          change intCodeMul (2 * a + 1) (2 * b + 1) =
            2 * ((a + 1) * (b + 1))
          simp [intCodeMul, intCodeNatAbs, Nat.bodd_mul]

private lemma intMul_prim : Primrec₂ fun a b : ℤ => a * b := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeMul_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq fun a b => intCodeMul_encode a b

lemma intOfNat_prim : Primrec fun n : ℕ => (n : ℤ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq fun n => by
    simp only [encode_int_natCast, id_eq]

private def intCodeLE (a b : ℕ) : Prop :=
  if a.bodd then
    if b.bodd then b.div2 ≤ a.div2 else True
  else if b.bodd then False else a.div2 ≤ b.div2

private instance intCodeLEDecidable : DecidableRel intCodeLE :=
  fun a b => by dsimp [intCodeLE]; infer_instance

private lemma intCodeLE_prim : PrimrecRel intCodeLE := by
  have ha : PrimrecRel fun (a : ℕ) (_ : ℕ) => a.bodd = true :=
    Primrec.eq.comp₂ (Primrec.nat_bodd.comp₂ Primrec₂.left)
      (Primrec₂.const true)
  have hb : PrimrecRel fun (_ : ℕ) (b : ℕ) => b.bodd = true :=
    Primrec.eq.comp₂ (Primrec.nat_bodd.comp₂ Primrec₂.right)
      (Primrec₂.const true)
  have hnegneg : PrimrecRel fun a b : ℕ => b.div2 ≤ a.div2 :=
    Primrec.nat_le.comp₂ (Primrec.nat_div2.comp₂ Primrec₂.right)
      (Primrec.nat_div2.comp₂ Primrec₂.left)
  have hpospos : PrimrecRel fun a b : ℕ => a.div2 ≤ b.div2 :=
    Primrec.nat_le.comp₂ (Primrec.nat_div2.comp₂ Primrec₂.left)
      (Primrec.nat_div2.comp₂ Primrec₂.right)
  have hformula : PrimrecRel fun (a b : ℕ) =>
      (a.bodd = true ∧ (b.bodd ≠ true ∨ b.div2 ≤ a.div2)) ∨
        (a.bodd ≠ true ∧ b.bodd ≠ true ∧ a.div2 ≤ b.div2) :=
    (ha.and (hb.not.or hnegneg)).or (ha.not.and (hb.not.and hpospos))
  exact hformula.of_eq fun a b => by
    simp only [intCodeLE]
    cases a.bodd <;> cases b.bodd <;> simp

private lemma intCodeLE_encode (a b : ℤ) :
    intCodeLE (Encodable.encode a) (Encodable.encode b) ↔ a ≤ b := by
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          change intCodeLE (2 * a) (2 * b) ↔ Int.ofNat a ≤ Int.ofNat b
          simp [intCodeLE, Nat.bodd_mul, Nat.div2_bit0]
      | negSucc b =>
          change intCodeLE (2 * a) (2 * b + 1) ↔ Int.ofNat a ≤ Int.negSucc b
          simp [intCodeLE, Nat.bodd_mul]
          omega
  | negSucc a =>
      cases b with
      | ofNat b =>
          change intCodeLE (2 * a + 1) (2 * b) ↔ Int.negSucc a ≤ Int.ofNat b
          simp [intCodeLE, Nat.bodd_mul]
          omega
      | negSucc b =>
          change intCodeLE (2 * a + 1) (2 * b + 1) ↔
            Int.negSucc a ≤ Int.negSucc b
          simp [intCodeLE, Nat.bodd_mul]
          omega

private lemma intLE_prim : PrimrecRel fun a b : ℤ => a ≤ b := by
  exact (intCodeLE_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq intCodeLE_encode

private def intCodeSign (zCode : ℕ) : ℕ :=
  if zCode = 0 then 0 else if zCode.bodd then 1 else 2

private lemma intCodeSign_prim : Primrec intCodeSign := by
  have hz : PrimrecPred fun n : ℕ => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hodd : PrimrecPred fun n : ℕ => n.bodd = true :=
    Primrec.eq.comp Primrec.nat_bodd (Primrec.const true)
  exact (Primrec.ite hz (Primrec.const 0)
    (Primrec.ite hodd (Primrec.const 1) (Primrec.const 2))).of_eq fun n => by
      simp only [intCodeSign]

private lemma intCodeSign_encode (z : ℤ) :
    intCodeSign (Encodable.encode z) = Encodable.encode z.sign := by
  cases z with
  | ofNat n =>
      cases n with
      | zero =>
          change intCodeSign 0 = 0
          simp [intCodeSign]
      | succ n =>
          change intCodeSign (2 * (n + 1)) = 2
          simp [intCodeSign, Nat.bodd_mul]
  | negSucc n =>
      change intCodeSign (2 * n + 1) = 1
      simp [intCodeSign, Nat.bodd_mul]

private lemma intSign_prim : Primrec Int.sign := by
  apply Primrec.encode_iff.mp
  exact (intCodeSign_prim.comp Primrec.encode).of_eq intCodeSign_encode

private def intCodeDivNat (zCode d : ℕ) : ℕ :=
  if d = 0 then 0
  else if zCode.bodd then 2 * (zCode.div2 / d) + 1
  else 2 * (zCode.div2 / d)

private lemma intCodeDivNat_prim : Primrec₂ intCodeDivNat := by
  have hd0 : PrimrecPred fun p : ℕ × ℕ => p.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hodd : PrimrecPred fun p : ℕ × ℕ => p.1.bodd = true :=
    Primrec.eq.comp (Primrec.nat_bodd.comp Primrec.fst) (Primrec.const true)
  have hquot : Primrec fun p : ℕ × ℕ => p.1.div2 / p.2 :=
    Primrec.nat_div.comp (Primrec.nat_div2.comp Primrec.fst) Primrec.snd
  have hneg : Primrec fun p : ℕ × ℕ => 2 * (p.1.div2 / p.2) + 1 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hquot)
      (Primrec.const 1)
  have hpos : Primrec fun p : ℕ × ℕ => 2 * (p.1.div2 / p.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) hquot
  exact (Primrec.ite hd0 (Primrec.const 0) (Primrec.ite hodd hneg hpos)).to₂.of_eq
    fun zCode d => by simp only [intCodeDivNat]

private lemma intCodeDivNat_encode (z : ℤ) (d : ℕ) :
    intCodeDivNat (Encodable.encode z) d = Encodable.encode (z / (d : ℤ)) := by
  cases z with
  | ofNat n =>
      cases d with
      | zero =>
          change intCodeDivNat (2 * n) 0 = Encodable.encode (Int.ofNat n / 0)
          rw [show Int.ofNat n / 0 = 0 by simp,
            show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, encode_int_natCast]
          simp [intCodeDivNat]
      | succ d =>
          change intCodeDivNat (2 * n) (d + 1) =
            Encodable.encode (Int.ofNat (n / (d + 1)))
          rw [show Encodable.encode (Int.ofNat (n / (d + 1))) =
            2 * (n / (d + 1)) from rfl]
          simp [intCodeDivNat, Nat.bodd_mul, Nat.div2_bit0]
  | negSucc n =>
      cases d with
      | zero =>
          change intCodeDivNat (2 * n + 1) 0 =
            Encodable.encode (Int.negSucc n / 0)
          rw [show Int.negSucc n / 0 = 0 by simp,
            show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, encode_int_natCast]
          simp [intCodeDivNat]
      | succ d =>
          change intCodeDivNat (2 * n + 1) (d + 1) =
            Encodable.encode (Int.negSucc (n / (d + 1)))
          rw [show Encodable.encode (Int.negSucc (n / (d + 1))) =
            2 * (n / (d + 1)) + 1 from rfl]
          simp [intCodeDivNat, Nat.bodd_mul]

lemma intDivNat_prim : Primrec₂ fun z : ℤ => fun d : ℕ => z / (d : ℤ) := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeDivNat_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    Primrec₂.right).of_eq intCodeDivNat_encode

private lemma ratNumNatAbs_prim : Primrec fun q : ℚ => q.num.natAbs :=
  intNatAbs_prim.comp ratNum_prim

/-- The cross-multiplied numerator `q.num * r.den`, the shared ingredient of rational
comparison and rational addition in the canonical encoding. -/
private lemma ratCrossNum_prim : Primrec₂ fun q r : ℚ => q.num * (r.den : ℤ) :=
  intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.left)
    ((intOfNat_prim.comp ratDen_prim).comp₂ Primrec₂.right)

/-- The cross-multiplied numerator with the arguments exchanged. -/
private lemma ratCrossNum_swap_prim : Primrec₂ fun q r : ℚ => r.num * (q.den : ℤ) :=
  intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.right)
    ((intOfNat_prim.comp ratDen_prim).comp₂ Primrec₂.left)

/-- Rational comparison is primitive recursive in the repository's canonical encoding. -/
lemma ratLE_prim : PrimrecRel fun q r : ℚ => q ≤ r := by
  have hleft : Primrec₂ fun q r : ℚ => q.num * (r.den : ℤ) := ratCrossNum_prim
  have hright : Primrec₂ fun q r : ℚ => r.num * (q.den : ℤ) := ratCrossNum_swap_prim
  exact (intLE_prim.comp₂ hleft hright).of_eq fun q r => by
    exact (Rat.le_iff q r).symm

private def ratMkCode (z : ℤ) (d : ℕ) : ℕ :=
  if d = 0 then Nat.pair 0 1
  else
    let g := Nat.gcd z.natAbs d
    Nat.pair (Encodable.encode (z / (g : ℤ))) (d / g)

private lemma ratMkCode_prim : Primrec₂ ratMkCode := by
  have hd0 : PrimrecPred fun p : ℤ × ℕ => p.2 = 0 :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  let g : ℤ × ℕ → ℕ := fun p => Nat.gcd p.1.natAbs p.2
  have hg : Primrec g :=
    natGCD_prim.comp (intNatAbs_prim.comp Primrec.fst) Primrec.snd
  have hnum : Primrec fun p : ℤ × ℕ => Encodable.encode (p.1 / (g p : ℤ)) :=
    Primrec.encode.comp (intDivNat_prim.comp Primrec.fst hg)
  have hden : Primrec fun p : ℤ × ℕ => p.2 / g p :=
    Primrec.nat_div.comp Primrec.snd hg
  have hpair : Primrec fun p : ℤ × ℕ =>
      Nat.pair (Encodable.encode (p.1 / (Nat.gcd p.1.natAbs p.2 : ℤ)))
        (p.2 / Nat.gcd p.1.natAbs p.2) :=
    Primrec₂.natPair.comp hnum hden
  exact (Primrec.ite hd0 (Primrec.const (Nat.pair 0 1)) hpair).to₂.of_eq
    fun z d => by simp only [ratMkCode]

private lemma ratMkCode_eq (z : ℤ) (d : ℕ) :
    ratMkCode z d = Encodable.encode (mkRat z d) := by
  by_cases hd : d = 0
  · subst d
    rw [show mkRat z 0 = (0 : ℚ) by simp [mkRat], encode_rat_eq]
    change Nat.pair 0 1 = Nat.pair (Encodable.encode (0 : ℤ)) 1
    rw [show Encodable.encode (0 : ℤ) = 0 from rfl]
  · rw [encode_rat_eq, Rat.num_mkRat, Rat.den_mkRat]
    simp [ratMkCode, hd, Nat.gcd_comm]

lemma ratMk_prim : Primrec₂ mkRat := by
  apply Primrec₂.encode_iff.mp
  exact ratMkCode_prim.of_eq ratMkCode_eq

lemma ratNeg_prim : Primrec fun q : ℚ => -q := by
  apply Primrec.encode_iff.mp
  have hpair : Primrec fun q : ℚ =>
      Nat.pair (Encodable.encode (-q.num)) q.den :=
    Primrec₂.natPair.comp (Primrec.encode.comp (intNeg_prim.comp ratNum_prim))
      ratDen_prim
  exact hpair.of_eq fun q => by
    simp [encode_rat_eq, Rat.neg_num, Rat.neg_den]

/-- Rational addition is primitive recursive in the canonical encoding. -/
lemma ratAdd_prim : Primrec₂ fun q r : ℚ => q + r := by
  have hqd : Primrec₂ fun q r : ℚ => q.num * (r.den : ℤ) := ratCrossNum_prim
  have hrd : Primrec₂ fun q r : ℚ => r.num * (q.den : ℤ) := ratCrossNum_swap_prim
  have hnum : Primrec₂ fun q r : ℚ => q.num * (r.den : ℤ) + r.num * (q.den : ℤ) :=
    intAdd_prim.comp₂ hqd hrd
  have hden : Primrec₂ fun q r : ℚ => q.den * r.den :=
    Primrec.nat_mul.comp₂ (ratDen_prim.comp₂ Primrec₂.left)
      (ratDen_prim.comp₂ Primrec₂.right)
  exact (ratMk_prim.comp₂ hnum hden).of_eq fun q r => (Rat.add_def' q r).symm

/-- Rational multiplication is primitive recursive in the canonical encoding. -/
lemma ratMul_prim : Primrec₂ fun q r : ℚ => q * r := by
  have hnum : Primrec₂ fun q r : ℚ => q.num * r.num :=
    intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.left)
      (ratNum_prim.comp₂ Primrec₂.right)
  have hden : Primrec₂ fun q r : ℚ => q.den * r.den :=
    Primrec.nat_mul.comp₂ (ratDen_prim.comp₂ Primrec₂.left)
      (ratDen_prim.comp₂ Primrec₂.right)
  exact (ratMk_prim.comp₂ hnum hden).of_eq fun q r => (Rat.mul_def' q r).symm

lemma ratSub_prim : Primrec₂ fun q r : ℚ => q - r := by
  exact (ratAdd_prim.comp₂ Primrec₂.left
    (ratNeg_prim.comp₂ Primrec₂.right)).of_eq fun q r => by simp [sub_eq_add_neg]

lemma ratInv_prim : Primrec fun q : ℚ => q⁻¹ := by
  have hsign : Primrec fun q : ℚ => q.num.sign := intSign_prim.comp ratNum_prim
  have hdenInt : Primrec fun q : ℚ => (q.den : ℤ) := intOfNat_prim.comp ratDen_prim
  have hnum : Primrec fun q : ℚ => q.num.sign * (q.den : ℤ) :=
    intMul_prim.comp hsign hdenInt
  have hzero : PrimrecPred fun q : ℚ => q.num = 0 :=
    Primrec.eq.comp ratNum_prim (Primrec.const 0)
  have hden : Primrec fun q : ℚ => if q.num = 0 then 1 else q.num.natAbs :=
    Primrec.ite hzero (Primrec.const 1) ratNumNatAbs_prim
  apply Primrec.encode_iff.mp
  have hpair : Primrec fun q : ℚ => Nat.pair
      (Encodable.encode (q.num.sign * (q.den : ℤ)))
      (if q.num = 0 then 1 else q.num.natAbs) :=
    Primrec₂.natPair.comp (Primrec.encode.comp hnum) hden
  exact hpair.of_eq fun q => by
    simp [encode_rat_eq, Rat.num_inv, Rat.den_inv]

/-- Rational maximum is primitive recursive in the canonical encoding. -/
lemma ratMax_prim : Primrec₂ fun q r : ℚ => max q r := by
  exact (Primrec.ite ratLE_prim Primrec₂.right Primrec₂.left).to₂.of_eq fun q r => by
    simp [max_def]

/-- Exact rational division is primitive recursive in the canonical encoding. -/
lemma ratDiv_prim : Primrec₂ fun q r : ℚ => q / r := by
  exact (ratMul_prim.comp₂ Primrec₂.left
    (ratInv_prim.comp₂ Primrec₂.right)).of_eq fun q r => by simp [div_eq_mul_inv]

lemma ratPow_prim : Primrec₂ fun q : ℚ => fun n : ℕ => q ^ n := by
  have hstep : Primrec₂ fun (p : ℚ × ℕ) (ni : ℕ × ℚ) => ni.2 * p.1 :=
    ratMul_prim.comp₂ (Primrec.snd.comp₂ Primrec₂.right)
      (Primrec.fst.comp₂ Primrec₂.left)
  have hpow : Primrec fun p : ℚ × ℕ => p.1 ^ p.2 := by
    exact (Primrec.nat_rec' Primrec.snd (Primrec.const 1) hstep).of_eq fun p => by
      rcases p with ⟨q, n⟩
      change Nat.rec 1 (fun _ ih => ih * q) n = q ^ n
      induction n with
      | zero => simp
      | succ n ih => simp [ih, pow_succ]
  exact hpow.to₂

/-! ## Duplicate-free sentence lists

Two consumers need to decide `Nodup` on a `List Sentence`: the finite-set encoding below, and
the market maker's proof-erased belief state (`Construction/LIACompiler.lean`), whose keys
must be distinct. -/

/-- Freedom from duplicates in a list of sentences is a primitive-recursive predicate. -/
lemma sentenceListNodup_prim :
    PrimrecPred fun l : List Sentence => l.Nodup := by
  have hfilter : Primrec₂ fun (l : List Sentence) (φ : Sentence) =>
      l.filter (fun ψ => ψ = φ) := by
    exact PrimrecRel.listFilter Primrec.eq
  have hcount : Primrec₂ fun (φ : Sentence) (l : List Sentence) =>
      (l.filter (fun ψ => ψ = φ)).length :=
    (Primrec.list_length.comp (hfilter.comp Primrec.snd Primrec.fst)).to₂
  have hone : PrimrecRel fun (φ : Sentence) (l : List Sentence) =>
      (l.filter (fun ψ => ψ = φ)).length = 1 :=
    Primrec.eq.comp₂ hcount (Primrec₂.const 1)
  have hall : PrimrecRel fun (l₁ l₂ : List Sentence) =>
      ∀ φ ∈ l₁, (l₂.filter (fun ψ => ψ = φ)).length = 1 :=
    hone.forall_mem_list
  exact (hall.comp Primrec.id Primrec.id).of_eq fun l => by
    have heq (φ : Sentence) :
        l.filter (fun ψ => ψ = φ) = l.filter (fun ψ => ψ == φ) := by
      apply List.filter_congr
      intro ψ _
      apply Bool.eq_iff_iff.mpr
      simp
    constructor
    · intro h
      rw [List.nodup_iff_count_eq_one]
      intro φ hφ
      rw [List.count_eq_length_filter, ← heq φ]
      exact h φ hφ
    · intro h φ hφ
      simp only [id_eq] at hφ ⊢
      rw [heq φ]
      simpa only [List.count_eq_length_filter] using
        (List.nodup_iff_count_eq_one.mp h φ hφ)
private lemma sentenceDecodeNorm_prim : Primrec sentenceDecodeNorm := by
  apply Primrec.nat_iff.mpr
  exact (Primcodable.prim Sentence).of_eq fun n => by
    change Encodable.encode
        ((@LO.Propositional.Formula.ofNat ℕ inferInstance n) : Option Sentence) =
      sentenceDecodeNorm n
    cases h : (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) <;>
      simp [sentenceDecodeNorm, h, encode_formula_eq_toNat]

/-! ## Primitive-recursive `EF` codes

`EF.ofNatAux` decodes a feature code under a fuel bound, recursing on strictly smaller
child codes, so the encode-after-decode normalizer is again compiled by strong recursion on
the paired `(code, fuel)` index rather than by structural recursion on `EF`. -/

/-- Lift one normalized child code through an `EF` unary constructor. -/
private def efUnaryNorm (tag childNorm : ℕ) : ℕ :=
  if childNorm = 0 then 0 else Nat.pair tag (childNorm - 1) + 1

private lemma efUnaryNorm_prim (tag : ℕ) : Primrec (efUnaryNorm tag) := by
  have hzero : PrimrecPred fun n : ℕ => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hresult : Primrec fun n : ℕ => Nat.pair tag (n - 1) + 1 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const tag)
        (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))
      (Primrec.const 1)
  exact (Primrec.ite hzero (Primrec.const 0) hresult).of_eq fun n => by
    simp only [efUnaryNorm]

/-- Lift two normalized child codes through an `EF` binary constructor. -/
private def efBinaryNorm (tag leftNorm rightNorm : ℕ) : ℕ :=
  if leftNorm = 0 ∨ rightNorm = 0 then 0
  else Nat.pair tag (Nat.pair (leftNorm - 1) (rightNorm - 1)) + 1

private lemma efBinaryNorm_prim (tag : ℕ) : Primrec₂ (efBinaryNorm tag) := by
  have hbad : PrimrecPred fun p : ℕ × ℕ => p.1 = 0 ∨ p.2 = 0 :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).or
      (Primrec.eq.comp Primrec.snd (Primrec.const 0))
  have hchildren : Primrec fun p : ℕ × ℕ =>
      Nat.pair (p.1 - 1) (p.2 - 1) :=
    Primrec₂.natPair.comp
      (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
  have hresult : Primrec fun p : ℕ × ℕ =>
      Nat.pair tag (Nat.pair (p.1 - 1) (p.2 - 1)) + 1 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const tag) hchildren)
      (Primrec.const 1)
  exact (Primrec.ite hbad (Primrec.const 0) hresult).to₂.of_eq fun left right => by
    simp only [efBinaryNorm]

/-- Normalize a decoded `price` node. -/
private def efPriceNorm (sentenceNorm day : ℕ) : ℕ :=
  if sentenceNorm = 0 then 0
  else Nat.pair 1 (Nat.pair (sentenceNorm - 1) day) + 1

private lemma efPriceNorm_prim : Primrec₂ efPriceNorm := by
  have hbad : PrimrecPred fun p : ℕ × ℕ => p.1 = 0 :=
    Primrec.eq.comp Primrec.fst (Primrec.const 0)
  have hresult : Primrec fun p : ℕ × ℕ =>
      Nat.pair 1 (Nat.pair (p.1 - 1) p.2) + 1 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec₂.natPair.comp
          (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)) Primrec.snd))
      (Primrec.const 1)
  exact (Primrec.ite hbad (Primrec.const 0) hresult).to₂.of_eq fun sentence day => by
    simp only [efPriceNorm]

/-- Lookup the previous-fuel normalized result for `child`.  The current paired strong-
recursion index is the length of `prior`. -/
private def efPriorNorm (prior : List ℕ) (child : ℕ) : ℕ :=
  prior.getD (Nat.pair child (prior.length.unpair.2 - 1)) 0

private lemma efPriorNorm_prim : Primrec₂ efPriorNorm := by
  have hfuel : Primrec fun prior : List ℕ => prior.length.unpair.2 - 1 :=
    Primrec.nat_sub.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length))
      (Primrec.const 1)
  have hindex : Primrec₂ fun (prior : List ℕ) (child : ℕ) =>
      Nat.pair child (prior.length.unpair.2 - 1) :=
    Primrec₂.natPair.comp₂ Primrec₂.right (hfuel.comp Primrec₂.left)
  exact ((Primrec.list_getD 0).comp₂ Primrec₂.left hindex).of_eq fun prior child => rfl

/-- One strong-recursion step for `encode (EF.ofNatAux fuel code)`. -/
private def efDecodeNormStep (prior : List ℕ) : ℕ :=
  let index := prior.length
  let code := index.unpair.1
  let fuel := index.unpair.2
  if fuel = 0 then 0
  else
    let tag := code.unpair.1
    let payload := code.unpair.2
    if tag = 0 then efUnaryNorm 0 (ratDecodeNorm payload)
    else if tag = 1 then
      efPriceNorm (sentenceDecodeNorm payload.unpair.1) payload.unpair.2
    else if tag = 2 then
      efBinaryNorm 2 (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else if tag = 3 then
      efBinaryNorm 3 (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else if tag = 4 then
      efBinaryNorm 4 (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else if tag = 5 then efUnaryNorm 5 (efPriorNorm prior payload)
    else if tag = 6 then Nat.pair 6 payload + 1
    else if tag = 7 then
      efBinaryNorm 7 (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else 0

private lemma efDecodeNormStep_prim : Primrec efDecodeNormStep := by
  let code : List ℕ → ℕ := fun prior => prior.length.unpair.1
  let fuel : List ℕ → ℕ := fun prior => prior.length.unpair.2
  let tag : List ℕ → ℕ := fun prior => (code prior).unpair.1
  let payload : List ℕ → ℕ := fun prior => (code prior).unpair.2
  have hcode : Primrec code := Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hfuel : Primrec fuel := Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp hcode)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp hcode)
  have hpayloadLeft : Primrec fun prior : List ℕ => (payload prior).unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  have hpayloadRight : Primrec fun prior : List ℕ => (payload prior).unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have htagEq (k : ℕ) : PrimrecPred fun prior : List ℕ => tag prior = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hfuelZero : PrimrecPred fun prior : List ℕ => fuel prior = 0 :=
    Primrec.eq.comp hfuel (Primrec.const 0)
  have hpriorLeft : Primrec fun prior : List ℕ =>
      efPriorNorm prior (payload prior).unpair.1 :=
    efPriorNorm_prim.comp Primrec.id hpayloadLeft
  have hpriorRight : Primrec fun prior : List ℕ =>
      efPriorNorm prior (payload prior).unpair.2 :=
    efPriorNorm_prim.comp Primrec.id hpayloadRight
  have hpriorPayload : Primrec fun prior : List ℕ => efPriorNorm prior (payload prior) :=
    efPriorNorm_prim.comp Primrec.id hpayload
  have hbinary (k : ℕ) : Primrec fun prior : List ℕ =>
      efBinaryNorm k (efPriorNorm prior (payload prior).unpair.1)
        (efPriorNorm prior (payload prior).unpair.2) :=
    (efBinaryNorm_prim k).comp hpriorLeft hpriorRight
  have hconst : Primrec fun prior : List ℕ => efUnaryNorm 0 (ratDecodeNorm (payload prior)) :=
    (efUnaryNorm_prim 0).comp (ratDecodeNorm_prim.comp hpayload)
  have hprice : Primrec fun prior : List ℕ =>
      efPriceNorm (sentenceDecodeNorm (payload prior).unpair.1) (payload prior).unpair.2 :=
    efPriceNorm_prim.comp (sentenceDecodeNorm_prim.comp hpayloadLeft) hpayloadRight
  have hunary : Primrec fun prior : List ℕ =>
      efUnaryNorm 5 (efPriorNorm prior (payload prior)) :=
    (efUnaryNorm_prim 5).comp hpriorPayload
  have hvar : Primrec fun prior : List ℕ => Nat.pair 6 (payload prior) + 1 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 6) hpayload) (Primrec.const 1)
  exact (Primrec.ite hfuelZero (Primrec.const 0)
    (Primrec.ite (htagEq 0) hconst
      (Primrec.ite (htagEq 1) hprice
        (Primrec.ite (htagEq 2) (hbinary 2)
          (Primrec.ite (htagEq 3) (hbinary 3)
            (Primrec.ite (htagEq 4) (hbinary 4)
              (Primrec.ite (htagEq 5) hunary
                (Primrec.ite (htagEq 6) hvar
                  (Primrec.ite (htagEq 7) (hbinary 7)
                    (Primrec.const 0)))))))))).of_eq fun prior => by
    simp only [efDecodeNormStep, code, fuel, tag, payload]

private def efAuxNormIndex (n : ℕ) : ℕ :=
  Encodable.encode (EF.ofNatAux n.unpair.2 n.unpair.1)

private lemma efHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map efAuxNormIndex).getD k 0 = efAuxNormIndex k := by
  have hzero : efAuxNormIndex 0 = 0 := by
    simp [efAuxNormIndex, EF.ofNatAux]
  rw [← hzero, List.getD_map]
  simp [hk]

/-- A child code paired with the smaller fuel is a strictly smaller strong-recursion
index — the well-foundedness step shared by the three `EF` course-of-values towers. -/
private lemma efChildPair_lt (child code fuel : ℕ) (hchild : child ≤ code) :
    Nat.pair child fuel < Nat.pair code (fuel + 1) := by
  rcases hchild.eq_or_lt with heq | hlt
  · subst code
    exact Nat.pair_lt_pair_right child (by omega)
  · exact (Nat.pair_lt_pair_left fuel hlt).trans
      (Nat.pair_lt_pair_right code (by omega))

private lemma efDecodeNormStep_history (n : ℕ) :
    efDecodeNormStep ((List.range n).map efAuxNormIndex) = efAuxNormIndex n := by
  rcases hpair : n.unpair with ⟨code, fuel⟩
  have hn : Nat.pair code fuel = n := by
    simpa [hpair] using Nat.pair_unpair n
  subst n
  cases fuel with
  | zero =>
      simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux]
  | succ fuel =>
      have hprior (child : ℕ) (hchild : child ≤ code) :
          efPriorNorm
              ((List.range (Nat.pair code (fuel + 1))).map efAuxNormIndex) child =
            efAuxNormIndex (Nat.pair child fuel) := by
        unfold efPriorNorm
        simp only [List.length_map, List.length_range, Nat.unpair_pair,
          Nat.add_sub_cancel]
        exact efHistory_getD (efChildPair_lt child code fuel hchild)
      have hleft : code.unpair.2.unpair.1 ≤ code :=
        (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)
      have hright : code.unpair.2.unpair.2 ≤ code :=
        (Nat.unpair_right_le _).trans (Nat.unpair_right_le _)
      have hpayload : code.unpair.2 ≤ code := Nat.unpair_right_le _
      rcases htag : code.unpair.1 with _ | tag
      · cases hq : (@Encodable.decode ℚ inferInstance code.unpair.2)
        <;> simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
          ratDecodeNorm_eq, hq, efUnaryNorm, encode_ef_eq_toNat, EF.toNat]
      · rcases tag with _ | tag
        · cases hs : (@LO.Propositional.Formula.ofNat ℕ inferInstance
              code.unpair.2.unpair.1 : Option Sentence)
          <;> simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
            sentenceDecodeNorm, hs, efPriceNorm, encode_ef_eq_toNat, EF.toNat,
            encode_formula_eq_toNat, decode_formula_eq_ofNat]
        · rcases tag with _ | tag
          · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
              cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
              simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                hprior _ hleft, hprior _ hright, efBinaryNorm,
                encode_ef_eq_toNat, EF.toNat, hL, hR]
          · rcases tag with _ | tag
            · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                  hprior _ hleft, hprior _ hright, efBinaryNorm,
                  encode_ef_eq_toNat, EF.toNat, hL, hR]
            · rcases tag with _ | tag
              · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                  cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                  simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                    hprior _ hleft, hprior _ hright, efBinaryNorm,
                    encode_ef_eq_toNat, EF.toNat, hL, hR]
              · rcases tag with _ | tag
                · cases hA : EF.ofNatAux fuel code.unpair.2 <;>
                    simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                      hprior _ hpayload, efUnaryNorm, encode_ef_eq_toNat, EF.toNat, hA]
                · rcases tag with _ | tag
                  · simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                      encode_ef_eq_toNat, EF.toNat]
                  · rcases tag with _ | tag
                    · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                        cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                        simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                          hprior _ hleft, hprior _ hright, efBinaryNorm,
                          encode_ef_eq_toNat, EF.toNat, hL, hR]
                    · simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag]

private lemma efAuxNormIndex_prim : Primrec efAuxNormIndex := by
  exact Primrec.of_courseOfValues efAuxNormIndex efDecodeNormStep_prim
    efDecodeNormStep_history

/-- The project’s concrete `EF.toNat` / `EF.ofNat` encoding is primitive-recursive.
This instance is proved from the exact decoder, including every failure branch. -/
instance efPrimcodable : Primcodable EF where
  prim := by
    have hindex : Primrec fun n : ℕ => Nat.pair n (n + 1) :=
      Primrec₂.natPair.comp Primrec.id
        (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
    exact Primrec.nat_iff.mp ((efAuxNormIndex_prim.comp hindex).of_eq fun n => by
      simp [efAuxNormIndex, EF.ofNat, decode_ef_eq_ofNat])

/-! ## Primitive-recursive strategy validation -/

/-- A normalized rank result uses `0` for decoder failure and `rank + 1` for success. -/
private def efRankBinaryNorm (left right : ℕ) : ℕ :=
  if left = 0 ∨ right = 0 then 0 else Nat.max left right

private lemma efRankBinaryNorm_prim : Primrec₂ efRankBinaryNorm := by
  have hbad : PrimrecPred fun p : ℕ × ℕ => p.1 = 0 ∨ p.2 = 0 :=
    (Primrec.eq.comp Primrec.fst (Primrec.const 0)).or
      (Primrec.eq.comp Primrec.snd (Primrec.const 0))
  exact (Primrec.ite hbad (Primrec.const 0)
    (Primrec.nat_max.comp Primrec.fst Primrec.snd)).to₂.of_eq fun left right => by
      simp only [efRankBinaryNorm]

/-- One strong-recursion step computing `0` on decoder failure and `EF.rank + 1` on
success.  Carrying success in the positive code prevents an invalid rank-zero child from
being confused with a valid rank-zero child. -/
private def efRankNormStep (prior : List ℕ) : ℕ :=
  let index := prior.length
  let code := index.unpair.1
  let fuel := index.unpair.2
  if fuel = 0 then 0
  else
    let tag := code.unpair.1
    let payload := code.unpair.2
    if tag = 0 then if ratDecodeNorm payload = 0 then 0 else 1
    else if tag = 1 then
      if sentenceDecodeNorm payload.unpair.1 = 0 then 0 else payload.unpair.2 + 1
    else if tag = 2 then
      efRankBinaryNorm (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else if tag = 3 then
      efRankBinaryNorm (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else if tag = 4 then
      efRankBinaryNorm (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else if tag = 5 then efPriorNorm prior payload
    else if tag = 6 then 1
    else if tag = 7 then
      efRankBinaryNorm (efPriorNorm prior payload.unpair.1)
        (efPriorNorm prior payload.unpair.2)
    else 0

private lemma efRankNormStep_prim : Primrec efRankNormStep := by
  let code : List ℕ → ℕ := fun prior => prior.length.unpair.1
  let fuel : List ℕ → ℕ := fun prior => prior.length.unpair.2
  let tag : List ℕ → ℕ := fun prior => (code prior).unpair.1
  let payload : List ℕ → ℕ := fun prior => (code prior).unpair.2
  have hcode : Primrec code := Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hfuel : Primrec fuel := Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp hcode)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp hcode)
  have hpayloadLeft : Primrec fun prior : List ℕ => (payload prior).unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  have hpayloadRight : Primrec fun prior : List ℕ => (payload prior).unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have htagEq (k : ℕ) : PrimrecPred fun prior : List ℕ => tag prior = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hfuelZero : PrimrecPred fun prior : List ℕ => fuel prior = 0 :=
    Primrec.eq.comp hfuel (Primrec.const 0)
  have hpriorLeft : Primrec fun prior : List ℕ =>
      efPriorNorm prior (payload prior).unpair.1 :=
    efPriorNorm_prim.comp Primrec.id hpayloadLeft
  have hpriorRight : Primrec fun prior : List ℕ =>
      efPriorNorm prior (payload prior).unpair.2 :=
    efPriorNorm_prim.comp Primrec.id hpayloadRight
  have hpriorPayload : Primrec fun prior : List ℕ => efPriorNorm prior (payload prior) :=
    efPriorNorm_prim.comp Primrec.id hpayload
  have hbinary : Primrec fun prior : List ℕ =>
      efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
        (efPriorNorm prior (payload prior).unpair.2) :=
    efRankBinaryNorm_prim.comp hpriorLeft hpriorRight
  have hconstBad : PrimrecPred fun prior : List ℕ => ratDecodeNorm (payload prior) = 0 :=
    Primrec.eq.comp (ratDecodeNorm_prim.comp hpayload) (Primrec.const 0)
  have hconst : Primrec fun prior : List ℕ =>
      if ratDecodeNorm (payload prior) = 0 then 0 else 1 :=
    Primrec.ite hconstBad (Primrec.const 0) (Primrec.const 1)
  have hpriceBad : PrimrecPred fun prior : List ℕ =>
      sentenceDecodeNorm (payload prior).unpair.1 = 0 :=
    Primrec.eq.comp (sentenceDecodeNorm_prim.comp hpayloadLeft) (Primrec.const 0)
  have hprice : Primrec fun prior : List ℕ =>
      if sentenceDecodeNorm (payload prior).unpair.1 = 0 then 0
      else (payload prior).unpair.2 + 1 :=
    Primrec.ite hpriceBad (Primrec.const 0)
      (Primrec.nat_add.comp hpayloadRight (Primrec.const 1))
  exact (Primrec.ite hfuelZero (Primrec.const 0)
    (Primrec.ite (htagEq 0) hconst
      (Primrec.ite (htagEq 1) hprice
        (Primrec.ite (htagEq 2) hbinary
          (Primrec.ite (htagEq 3) hbinary
            (Primrec.ite (htagEq 4) hbinary
              (Primrec.ite (htagEq 5) hpriorPayload
                (Primrec.ite (htagEq 6) (Primrec.const 1)
                  (Primrec.ite (htagEq 7) hbinary
                    (Primrec.const 0)))))))))).of_eq fun prior => by
    simp only [efRankNormStep, code, fuel, tag, payload]

private def efAuxRankNormIndex (n : ℕ) : ℕ :=
  match EF.ofNatAux n.unpair.2 n.unpair.1 with
  | none => 0
  | some e => e.rank + 1

private lemma efRankHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map efAuxRankNormIndex).getD k 0 = efAuxRankNormIndex k := by
  have hzero : efAuxRankNormIndex 0 = 0 := by
    simp [efAuxRankNormIndex, EF.ofNatAux]
  rw [← hzero, List.getD_map]
  simp [hk]

private lemma efRankNormStep_history (n : ℕ) :
    efRankNormStep ((List.range n).map efAuxRankNormIndex) = efAuxRankNormIndex n := by
  rcases hpair : n.unpair with ⟨code, fuel⟩
  have hn : Nat.pair code fuel = n := by
    simpa [hpair] using Nat.pair_unpair n
  subst n
  cases fuel with
  | zero => simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux]
  | succ fuel =>
      have hprior (child : ℕ) (hchild : child ≤ code) :
          efPriorNorm
              ((List.range (Nat.pair code (fuel + 1))).map efAuxRankNormIndex) child =
            efAuxRankNormIndex (Nat.pair child fuel) := by
        unfold efPriorNorm
        simp only [List.length_map, List.length_range, Nat.unpair_pair,
          Nat.add_sub_cancel]
        exact efRankHistory_getD (efChildPair_lt child code fuel hchild)
      have hleft : code.unpair.2.unpair.1 ≤ code :=
        (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)
      have hright : code.unpair.2.unpair.2 ≤ code :=
        (Nat.unpair_right_le _).trans (Nat.unpair_right_le _)
      have hpayload : code.unpair.2 ≤ code := Nat.unpair_right_le _
      rcases htag : code.unpair.1 with _ | tag
      · cases hq : (@Encodable.decode ℚ inferInstance code.unpair.2) <;>
          simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag,
            ratDecodeNorm_eq, hq]
      · rcases tag with _ | tag
        · cases hs : (@LO.Propositional.Formula.ofNat ℕ inferInstance
              code.unpair.2.unpair.1 : Option Sentence) <;>
            simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag,
              sentenceDecodeNorm, hs, decode_formula_eq_ofNat]
        · rcases tag with _ | tag
          · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
              cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
              simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag,
                hprior _ hleft, hprior _ hright, efRankBinaryNorm, hL, hR]
          · rcases tag with _ | tag
            · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag,
                  hprior _ hleft, hprior _ hright, efRankBinaryNorm, hL, hR]
            · rcases tag with _ | tag
              · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                  cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                  simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag,
                    hprior _ hleft, hprior _ hright, efRankBinaryNorm, hL, hR]
              · rcases tag with _ | tag
                · cases hA : EF.ofNatAux fuel code.unpair.2 <;>
                    simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag,
                      hprior _ hpayload, hA]
                · rcases tag with _ | tag
                  · simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag]
                  · rcases tag with _ | tag
                    · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                        cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                        simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag,
                          hprior _ hleft, hprior _ hright, efRankBinaryNorm, hL, hR]
                    · simp [efRankNormStep, efAuxRankNormIndex, EF.ofNatAux, htag]

private lemma efAuxRankNormIndex_prim : Primrec efAuxRankNormIndex := by
  exact Primrec.of_courseOfValues efAuxRankNormIndex efRankNormStep_prim
    efRankNormStep_history

private lemma efRank_prim : Primrec EF.rank := by
  have hindex : Primrec fun e : EF => Nat.pair (Encodable.encode e)
      (Encodable.encode e + 1) :=
    Primrec₂.natPair.comp Primrec.encode
      (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
  exact (Primrec.pred.comp (efAuxRankNormIndex_prim.comp hindex)).of_eq fun e => by
    simp [efAuxRankNormIndex, encode_ef_eq_toNat, EF.ofNatAux_toNat]

/-! ## Primitive-recursive `EF.priceQueries`

`EF.priceQueries` (`Framework/Criterion.lean`) lists the `(day, sentence)` market cells a feature
inspects.  Its primitive recursivity is the guard that keeps the total quote table `V`
(which substitutes `0` for an unanswered query) from silently certifying a false
settlement test: `EF.denoteRatWithAtFuel_complete` fires only once every listed query is
answered.  Compiled by course-of-values recursion on the Gödel code, carrying the
list-valued result directly through `Primrec.nat_strong_rec` at
`σ := Option (List (ℕ × Sentence))` rather than through a normalized `ℕ`. -/

/-- Query-list values `List (ℕ × Sentence)`, tracked as `Option` (`none` = decoder
failure). -/
private abbrev EFQueryList := List (ℕ × Sentence)

/-- Append two query lists, propagating decoder failure. -/
private def efQueriesAppend (left right : Option EFQueryList) : Option EFQueryList :=
  left.bind fun a => right.map fun b => a ++ b

private lemma efQueriesAppend_prim : Primrec₂ efQueriesAppend := by
  have hg : Primrec₂ fun (z : (Option EFQueryList × Option EFQueryList) × EFQueryList)
      (b : EFQueryList) => z.2 ++ b :=
    Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hmap : Primrec₂ fun (p : Option EFQueryList × Option EFQueryList)
      (a : EFQueryList) => p.2.map fun b => a ++ b :=
    (Primrec.option_map (Primrec.snd.comp Primrec.fst) hg).to₂
  exact Primrec.option_bind Primrec.fst hmap

/-- Decoded value of a child code from the recursion history, mirroring `efPriorNorm`
but carrying the list value directly (no `Encodable` round-trip). -/
private def efPriorQueries (prior : List (Option EFQueryList)) (child : ℕ) :
    Option EFQueryList :=
  prior.getD (Nat.pair child (prior.length.unpair.2 - 1)) none

private lemma efPriorQueries_prim : Primrec₂ efPriorQueries := by
  have hfuel : Primrec fun prior : List (Option EFQueryList) =>
      prior.length.unpair.2 - 1 :=
    Primrec.nat_sub.comp
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length))
      (Primrec.const 1)
  have hindex : Primrec₂ fun (prior : List (Option EFQueryList)) (child : ℕ) =>
      Nat.pair child (prior.length.unpair.2 - 1) :=
    Primrec₂.natPair.comp₂ Primrec₂.right (hfuel.comp Primrec₂.left)
  exact (Primrec.list_getD none).comp₂ Primrec₂.left hindex

/-- One strong-recursion step for `(EF.ofNatAux fuel code).map EF.priceQueries`. -/
private def efQueriesNormVal (prior : List (Option EFQueryList)) : Option EFQueryList :=
  let index := prior.length
  let code := index.unpair.1
  let fuel := index.unpair.2
  let tag := code.unpair.1
  let payload := code.unpair.2
  if fuel = 0 then none
  else if tag = 0 then (Encodable.decode (α := ℚ) payload).map fun _ => []
  else if tag = 1 then
    (Encodable.decode (α := Sentence) payload.unpair.1).map
      fun φ => [(payload.unpair.2, φ)]
  else if tag = 2 then
    efQueriesAppend (efPriorQueries prior payload.unpair.1)
      (efPriorQueries prior payload.unpair.2)
  else if tag = 3 then
    efQueriesAppend (efPriorQueries prior payload.unpair.1)
      (efPriorQueries prior payload.unpair.2)
  else if tag = 4 then
    efQueriesAppend (efPriorQueries prior payload.unpair.1)
      (efPriorQueries prior payload.unpair.2)
  else if tag = 5 then efPriorQueries prior payload
  else if tag = 6 then some []
  else if tag = 7 then
    efQueriesAppend (efPriorQueries prior payload.unpair.1)
      (efPriorQueries prior payload.unpair.2)
  else none

private lemma efQueriesNormVal_prim : Primrec efQueriesNormVal := by
  let code : List (Option EFQueryList) → ℕ := fun prior => prior.length.unpair.1
  let fuel : List (Option EFQueryList) → ℕ := fun prior => prior.length.unpair.2
  let tag : List (Option EFQueryList) → ℕ := fun prior => (code prior).unpair.1
  let payload : List (Option EFQueryList) → ℕ := fun prior => (code prior).unpair.2
  have hcode : Primrec code := Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hfuel : Primrec fuel := Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp hcode)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp hcode)
  have hpayloadLeft : Primrec fun prior : List (Option EFQueryList) =>
      (payload prior).unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  have hpayloadRight : Primrec fun prior : List (Option EFQueryList) =>
      (payload prior).unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have htagEq (k : ℕ) : PrimrecPred fun prior : List (Option EFQueryList) =>
      tag prior = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hfuelZero : PrimrecPred fun prior : List (Option EFQueryList) => fuel prior = 0 :=
    Primrec.eq.comp hfuel (Primrec.const 0)
  have hbinary : Primrec fun prior : List (Option EFQueryList) =>
      efQueriesAppend (efPriorQueries prior (payload prior).unpair.1)
        (efPriorQueries prior (payload prior).unpair.2) :=
    efQueriesAppend_prim.comp
      (efPriorQueries_prim.comp Primrec.id hpayloadLeft)
      (efPriorQueries_prim.comp Primrec.id hpayloadRight)
  have hconst : Primrec fun prior : List (Option EFQueryList) =>
      (Encodable.decode (α := ℚ) (payload prior)).map fun _ => ([] : EFQueryList) :=
    Primrec.option_map (Primrec.decode.comp hpayload)
      (Primrec.const ([] : EFQueryList)).to₂
  have hprice : Primrec fun prior : List (Option EFQueryList) =>
      (Encodable.decode (α := Sentence) (payload prior).unpair.1).map
        fun φ => [((payload prior).unpair.2, φ)] := by
    refine Primrec.option_map (Primrec.decode.comp hpayloadLeft) ?_
    exact (Primrec.list_cons.comp
      ((Primrec.snd.comp (Primrec.unpair.comp hpayload)).comp Primrec.fst |>.pair
        Primrec.snd)
      (Primrec.const [])).to₂
  have hsafe : Primrec fun prior : List (Option EFQueryList) =>
      efPriorQueries prior (payload prior) :=
    efPriorQueries_prim.comp Primrec.id hpayload
  exact (Primrec.ite hfuelZero (Primrec.const none)
    (Primrec.ite (htagEq 0) hconst
      (Primrec.ite (htagEq 1) hprice
        (Primrec.ite (htagEq 2) hbinary
          (Primrec.ite (htagEq 3) hbinary
            (Primrec.ite (htagEq 4) hbinary
              (Primrec.ite (htagEq 5) hsafe
                (Primrec.ite (htagEq 6) (Primrec.const (some ([] : EFQueryList)))
                  (Primrec.ite (htagEq 7) hbinary
                    (Primrec.const none)))))))))).of_eq fun prior => rfl

/-- The intended value at index `n`: decode `n` under its fuel, take price queries. -/
private def efAuxQueriesVal (n : ℕ) : Option EFQueryList :=
  (EF.ofNatAux n.unpair.2 n.unpair.1).map EF.priceQueries

private lemma efAuxQueriesVal_zero : efAuxQueriesVal 0 = none := by
  simp [efAuxQueriesVal, EF.ofNatAux]

private lemma efQueriesHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map efAuxQueriesVal).getD k none = efAuxQueriesVal k := by
  rw [← efAuxQueriesVal_zero, List.getD_map]
  simp [hk]

private lemma efQueriesNormVal_history (n : ℕ) :
    efQueriesNormVal ((List.range n).map efAuxQueriesVal) = efAuxQueriesVal n := by
  rcases hpair : n.unpair with ⟨code, fuel⟩
  have hn : Nat.pair code fuel = n := by
    simpa [hpair] using Nat.pair_unpair n
  subst n
  simp only [efAuxQueriesVal, Nat.unpair_pair]
  cases fuel with
  | zero => simp [efQueriesNormVal, EF.ofNatAux]
  | succ fuel =>
      have hprior (child : ℕ) (hchild : child ≤ code) :
          efPriorQueries
              ((List.range (Nat.pair code (fuel + 1))).map efAuxQueriesVal) child =
            (EF.ofNatAux fuel child).map EF.priceQueries := by
        unfold efPriorQueries
        simp only [List.length_map, List.length_range, Nat.unpair_pair,
          Nat.add_sub_cancel]
        rw [efQueriesHistory_getD (efChildPair_lt child code fuel hchild)]
        simp [efAuxQueriesVal, Nat.unpair_pair]
      have hleft : code.unpair.2.unpair.1 ≤ code :=
        (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)
      have hright : code.unpair.2.unpair.2 ≤ code :=
        (Nat.unpair_right_le _).trans (Nat.unpair_right_le _)
      have hpayload : code.unpair.2 ≤ code := Nat.unpair_right_le _
      rcases htag : code.unpair.1 with _ | tag
      · cases hq : (@Encodable.decode ℚ inferInstance code.unpair.2) <;>
          simp [efQueriesNormVal, EF.ofNatAux, htag, hq, EF.priceQueries]
      · rcases tag with _ | tag
        · cases hs : (@LO.Propositional.Formula.ofNat ℕ inferInstance
              code.unpair.2.unpair.1 : Option Sentence) <;>
            simp [efQueriesNormVal, EF.ofNatAux, htag, hs, EF.priceQueries,
              decode_formula_eq_ofNat]
        · rcases tag with _ | tag
          · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
              cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
              simp [efQueriesNormVal, EF.ofNatAux, htag,
                hprior _ hleft, hprior _ hright, efQueriesAppend, EF.priceQueries, hL, hR]
          · rcases tag with _ | tag
            · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                simp [efQueriesNormVal, EF.ofNatAux, htag,
                  hprior _ hleft, hprior _ hright, efQueriesAppend, EF.priceQueries, hL, hR]
            · rcases tag with _ | tag
              · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                  cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                  simp [efQueriesNormVal, EF.ofNatAux, htag,
                    hprior _ hleft, hprior _ hright, efQueriesAppend, EF.priceQueries, hL, hR]
              · rcases tag with _ | tag
                · cases hA : EF.ofNatAux fuel code.unpair.2 <;>
                    simp [efQueriesNormVal, EF.ofNatAux, htag,
                      hprior _ hpayload, EF.priceQueries, hA]
                · rcases tag with _ | tag
                  · simp [efQueriesNormVal, EF.ofNatAux, htag, EF.priceQueries]
                  · rcases tag with _ | tag
                    · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                        cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                        simp [efQueriesNormVal, EF.ofNatAux, htag,
                          hprior _ hleft, hprior _ hright, efQueriesAppend,
                          EF.priceQueries, hL, hR]
                    · simp [efQueriesNormVal, EF.ofNatAux, htag]

private lemma efAuxQueriesVal_prim : Primrec efAuxQueriesVal := by
  exact Primrec.of_courseOfValues efAuxQueriesVal efQueriesNormVal_prim
    efQueriesNormVal_history

/-- `EF.priceQueries` is primitive recursive.  The guard behind the settlement checker's
soundness: only when every listed query is answered does the total quote table stand in
for the real market. -/
lemma efPriceQueries_prim : Primrec EF.priceQueries := by
  have hindex : Primrec fun e : EF => Nat.pair (Encodable.encode e)
      (Encodable.encode e + 1) :=
    Primrec₂.natPair.comp Primrec.encode
      (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
  exact (Primrec.option_getD.comp (efAuxQueriesVal_prim.comp hindex)
    (Primrec.const ([] : EFQueryList))).of_eq fun e => by
      simp [efAuxQueriesVal, encode_ef_eq_toNat, EF.ofNatAux_toNat]

private def strategyOfTrades? (n : ℕ) (trades : List (EF × Sentence)) :
    Option (Strategy n) :=
  if h : ∀ p ∈ trades, p.1.rank ≤ n then some ⟨trades, h⟩ else none

private lemma strategyOfTrades?_self {n : ℕ} (T : Strategy n) :
    strategyOfTrades? n T.trades = some T := by
  simp only [strategyOfTrades?, dif_pos T.rank_le]

/-- A strategy is encoded by exactly its finite trade list; its day-rank proof is erased
and revalidated by the decoder. -/
instance strategyEncodable (n : ℕ) : Encodable (Strategy n) :=
  Encodable.ofLeftInjection Strategy.trades (strategyOfTrades? n)
    strategyOfTrades?_self

private lemma strategyTradesValid_prim (n : ℕ) :
    PrimrecPred fun trades : List (EF × Sentence) =>
      ∀ p ∈ trades, p.1.rank ≤ n := by
  have hp : PrimrecPred fun p : EF × Sentence => p.1.rank ≤ n :=
    Primrec.nat_le.comp (efRank_prim.comp Primrec.fst) (Primrec.const n)
  exact hp.forall_mem_list

private def strategyTradesNorm (n : ℕ) (trades : List (EF × Sentence)) : ℕ :=
  if ∀ p ∈ trades, p.1.rank ≤ n then Encodable.encode trades + 1 else 0

private lemma strategyTradesNorm_prim (n : ℕ) :
    Primrec (strategyTradesNorm n) := by
  exact (Primrec.ite (strategyTradesValid_prim n)
    (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
    (Primrec.const 0)).of_eq fun trades => by simp only [strategyTradesNorm]

private lemma strategyTradesNorm_eq (n : ℕ) (trades : List (EF × Sentence)) :
    strategyTradesNorm n trades = Encodable.encode (strategyOfTrades? n trades) := by
  by_cases h : ∀ p ∈ trades, p.1.rank ≤ n
  · let T : Strategy n := ⟨trades, h⟩
    have hof : strategyOfTrades? n trades = some T := by
      simpa [T] using strategyOfTrades?_self T
    rw [strategyTradesNorm, if_pos h, hof]
    rfl
  · have hof : strategyOfTrades? n trades = none := by
      rw [strategyOfTrades?, dif_neg h]
    rw [strategyTradesNorm, if_neg h, hof]
    rfl

private def strategyDecodeNorm (n code : ℕ) : ℕ :=
  match Encodable.decode (α := List (EF × Sentence)) code with
  | none => 0
  | some trades => strategyTradesNorm n trades

private lemma strategyDecodeNorm_prim (n : ℕ) :
    Primrec (strategyDecodeNorm n) := by
  exact (Primrec.option_casesOn
    (Primrec.decode : Primrec fun code : ℕ =>
      Encodable.decode (α := List (EF × Sentence)) code)
    (Primrec.const 0)
    ((strategyTradesNorm_prim n).comp₂ Primrec₂.right)).of_eq fun code => by
      cases h : Encodable.decode (α := List (EF × Sentence)) code <;>
        simp [strategyDecodeNorm, h]

private lemma strategyDecodeNorm_eq (n code : ℕ) :
    strategyDecodeNorm n code =
      Encodable.encode (@Encodable.decode (Strategy n) (strategyEncodable n) code) := by
  change strategyDecodeNorm n code = Encodable.encode
    ((Encodable.decode (α := List (EF × Sentence)) code).bind
      (strategyOfTrades? n))
  cases h : Encodable.decode (α := List (EF × Sentence)) code with
  | none => simp [strategyDecodeNorm, h]
  | some trades => simp [strategyDecodeNorm, h, strategyTradesNorm_eq]

/-- Every day-indexed strategy type has the exact proof-erased primitive-recursive
encoding required by the bounded LIA evaluator. -/
instance strategyPrimcodable (n : ℕ) : Primcodable (Strategy n) where
  prim := Primrec.nat_iff.mp
    ((strategyDecodeNorm_prim n).of_eq (strategyDecodeNorm_eq n))

/-! ## Exact finite-sentence-set encoding

The canonical form of a finite set is its duplicate-free code-sorted list.  The two list
utilities that produce it — last-occurrence deduplication and insertion sort — are compiled
once over an arbitrary `Primcodable` element type and instantiated twice: at `Sentence`
ordered by Gödel code here, and at `ℕ` ordered by `≤` in the Budgeter's atom compiler. -/

/-- Remove duplicates from a list, keeping the last occurrence of each element. -/
def listDedup {α : Type*} [DecidableEq α] (l : List α) : List α :=
  l.foldr (fun a acc => if a ∈ acc then acc else a :: acc) []

@[simp] private lemma listDedup_nil {α : Type*} [DecidableEq α] :
    listDedup ([] : List α) = [] := rfl

@[simp] private lemma listDedup_cons {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    listDedup (a :: l) = if a ∈ listDedup l then listDedup l else a :: listDedup l := rfl

@[simp] private lemma mem_listDedup {α : Type*} [DecidableEq α] :
    ∀ (l : List α) (a : α), a ∈ listDedup l ↔ a ∈ l := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons b l ih =>
      intro a
      by_cases h : b ∈ listDedup l
      · have hbl : b ∈ l := (ih b).mp h
        rw [listDedup_cons, if_pos h, ih a]
        simp only [List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | ha)
          · exact hbl
          · exact ha
      · simp [listDedup_cons, h, ih]

lemma listDedup_nodup {α : Type*} [DecidableEq α] (l : List α) :
    (listDedup l).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : a ∈ listDedup l
      · simpa [listDedup_cons, h] using ih
      · simp [listDedup_cons, h, ih]

lemma listDedup_prim {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (listDedup (α := α)) := by
  have hmem : PrimrecRel fun (tail : List α) (a : α) => a ∈ tail :=
    (Primrec.eq.exists_mem_list).of_eq fun tail a => by simp
  have hstep : Primrec₂ fun (_ : List α) (p : α × List α) =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2 :=
    Primrec.ite
      (hmem.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) |>.to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun _ => rfl

/-- Remove duplicate sentences while preserving the last occurrence of each sentence. -/
def sentenceDedup (l : List Sentence) : List Sentence :=
  l.foldr (fun φ acc => if φ ∈ acc then acc else φ :: acc) []

@[simp] lemma sentenceDedup_nil : sentenceDedup [] = [] := by rfl

@[simp] lemma sentenceDedup_cons (a : Sentence) (l : List Sentence) :
    sentenceDedup (a :: l) =
      if a ∈ sentenceDedup l then sentenceDedup l else a :: sentenceDedup l := by
  rfl

@[simp] lemma mem_sentenceDedup : ∀ (l : List Sentence) (φ : Sentence),
    φ ∈ sentenceDedup l ↔ φ ∈ l :=
  mem_listDedup

/-- The deduplicated list has no repeats. -/
lemma sentenceDedup_nodup (l : List Sentence) :
    (sentenceDedup l).Nodup :=
  listDedup_nodup l

/-- Sentence deduplication is primitive recursive. -/
lemma sentenceDedup_prim : Primrec sentenceDedup :=
  listDedup_prim.of_eq fun _ => rfl

/-- Insertion into a list sorted by a primitive-recursive order is primitive recursive. -/
private lemma orderedInsert_prim {α : Type*} [Primcodable α] (r : α → α → Prop)
    [DecidableRel r] (hr : PrimrecRel r) : Primrec₂ (List.orderedInsert r) := by
  let base : α × List α → List α := fun p => [p.1]
  let step : (α × List α) → (α × List α × List α) → List α :=
    fun p q => if r p.1 q.1 then p.1 :: q.1 :: q.2.1 else q.1 :: q.2.2
  have hbase : Primrec base :=
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])).of_eq fun p => by
      simp [base]
  have hpred : PrimrecPred fun x :
      (α × List α) × (α × List α × List α) => r x.1.1 x.2.1 :=
    hr.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  have hthen : Primrec fun x :
      (α × List α) × (α × List α × List α) => x.1.1 :: x.2.1 :: x.2.2.1 :=
    Primrec.list_cons.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have helse : Primrec fun x :
      (α × List α) × (α × List α × List α) => x.2.1 :: x.2.2.2 :=
    Primrec.list_cons.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ step :=
    (Primrec.ite hpred hthen helse).to₂.of_eq fun p q => by
      simp only [step]
  exact (Primrec.list_rec Primrec.snd hbase hstep).to₂.of_eq fun a l => by
    change List.recOn l [a]
      (fun b tail ih => if r a b then a :: b :: tail else b :: ih) =
      List.orderedInsert r a l
    induction l with
    | nil => rfl
    | cons b l ih => simp [List.orderedInsert, ih]

/-- Insertion sort by a primitive-recursive order is primitive recursive. -/
lemma insertionSort_prim {α : Type*} [Primcodable α] (r : α → α → Prop)
    [DecidableRel r] (hr : PrimrecRel r) : Primrec (List.insertionSort r) :=
  (Primrec.list_foldr Primrec.id (Primrec.const [])
    ((orderedInsert_prim r hr).comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun _ => rfl

/-- Comparison of sentence Gödel codes is primitive recursive. -/
private lemma sentenceCodeLE_prim :
    PrimrecRel fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ :=
  Primrec.nat_le.comp₂
    (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)

/-- The canonical insertion sort used below is primitive recursive. -/
lemma sentenceInsertionSort_prim :
    Primrec (List.insertionSort
      (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ)) :=
  insertionSort_prim _ sentenceCodeLE_prim

private def sentenceFinsetDecodeNorm (n : ℕ) : ℕ :=
  match Encodable.decode (α := List Sentence) n with
  | none => 0
  | some l =>
      if l.Nodup then
        Encodable.encode (l.insertionSort
          (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ)) + 1
      else 0

private lemma sentenceFinsetDecodeNorm_prim :
    Primrec sentenceFinsetDecodeNorm := by
  have hsorted : Primrec fun l : List Sentence => Encodable.encode
      (l.insertionSort
        (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ)) + 1 :=
    Primrec.nat_add.comp
      (Primrec.encode.comp sentenceInsertionSort_prim)
      (Primrec.const 1)
  have hvalid : Primrec fun l : List Sentence =>
      if l.Nodup then
        Encodable.encode (l.insertionSort
          (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ)) + 1
      else 0 :=
    Primrec.ite sentenceListNodup_prim hsorted (Primrec.const 0)
  exact (Primrec.option_casesOn
    (Primrec.decode : Primrec fun n : ℕ =>
      Encodable.decode (α := List Sentence) n)
    (Primrec.const 0)
    (hvalid.comp₂ Primrec₂.right)).of_eq fun n => by
      cases h : Encodable.decode (α := List Sentence) n <;>
        simp [sentenceFinsetDecodeNorm, h]

private lemma sentenceMultisetDecode_eq (n : ℕ) :
    @Encodable.decode (Multiset Sentence) Multiset.encodable n =
      (Encodable.decode (α := List Sentence) n).map
        (fun l => (l : Multiset Sentence)) := by
  unfold Multiset.encodable
  unfold decodeMultiset
  cases h : Encodable.decode (α := List Sentence) n <;> simp [h]

lemma sentenceFinsetEncode_eq (s : Finset Sentence) :
    @Encodable.encode (Finset Sentence) Finset.encodable s =
      encodeMultiset s.1 := by
  rfl

private lemma sentenceFinsetDecodeNorm_eq (n : ℕ) :
    sentenceFinsetDecodeNorm n =
      @Encodable.encode (Option (Finset Sentence)) Option.encodable
        (@Encodable.decode (Finset Sentence) Finset.encodable n) := by
  simp only [Encodable.decode_ofEquiv]
  change sentenceFinsetDecodeNorm n = Encodable.encode
    (Option.map
      (fun x : {s : Multiset Sentence // s.Nodup} =>
        ({ val := x.1, nodup := x.2 } : Finset Sentence))
      (@Encodable.decode {s : Multiset Sentence // s.Nodup}
        (@Subtype.encodable (Multiset Sentence) Multiset.Nodup
          Multiset.encodable
          (fun s => @Multiset.nodupDecidable Sentence
            (Encodable.decidableEqOfEncodable Sentence) s)) n))
  change sentenceFinsetDecodeNorm n = Encodable.encode
    (Option.map
      (fun x : {s : Multiset Sentence // s.Nodup} =>
        ({ val := x.1, nodup := x.2 } : Finset Sentence))
      ((@Encodable.decode (Multiset Sentence) Multiset.encodable n).bind
        fun a => @dite _ a.Nodup
          (@Multiset.nodupDecidable Sentence
            (Encodable.decidableEqOfEncodable Sentence) a)
          (fun h => some ⟨a, h⟩) (fun _ => none)))
  rw [sentenceMultisetDecode_eq]
  cases h : Encodable.decode (α := List Sentence) n with
  | none => simp [sentenceFinsetDecodeNorm, h]
  | some l =>
      by_cases hn : l.Nodup
      · simp [sentenceFinsetDecodeNorm, h, hn]
        rw [sentenceFinsetEncode_eq]
        unfold encodeMultiset
        let r : Sentence → Sentence → Prop := fun φ ψ =>
          Encodable.encode φ ≤ Encodable.encode ψ
        letI : IsTrans Sentence r :=
          ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
        letI : Std.Antisymm r :=
          ⟨fun _ _ hab hba => Encodable.encode_injective (le_antisymm hab hba)⟩
        letI : Std.Total r :=
          ⟨fun φ ψ => le_total (Encodable.encode φ) (Encodable.encode ψ)⟩
        change Encodable.encode (l.insertionSort r) =
          Encodable.encode (Multiset.sort (l : Multiset Sentence) r)
        rw [Multiset.coe_sort, List.mergeSort_eq_insertionSort]
      · simp [sentenceFinsetDecodeNorm, h, hn]

/-- The stock `Finset Sentence` representation is primitive recursive.  The proof uses
insertion sort only as an executable presentation of Mathlib's definitionally chosen merge
sort; `List.mergeSort_eq_insertionSort` proves the encodings coincide exactly. -/
instance sentenceFinsetPrimcodable : Primcodable (Finset Sentence) where
  __ := Finset.encodable
  prim := Primrec.nat_iff.mp
    (sentenceFinsetDecodeNorm_prim.of_eq sentenceFinsetDecodeNorm_eq)

/-! ## Uniform trader-program emulator

The streaming strategy decoder constructs `EF` syntax directly.  Exposing these small
constructor facts separately keeps the parser proof about its control flow rather than the
details of the exact `EF.toNat` representation. -/

lemma efConst_prim : Primrec EF.const := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp (Primrec.const 0) Primrec.encode).of_eq fun q => by
    rfl

lemma efPrice_prim : Primrec₂ EF.price := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd)).to₂).of_eq
      fun φ n => by rfl

lemma efAdd_prim : Primrec₂ EF.add := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun a b => by rfl

lemma efMul_prim : Primrec₂ EF.mul := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 3)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun a b => by rfl

lemma efMax_prim : Primrec₂ EF.max := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun a b => by rfl

lemma efSafeRecip_prim : Primrec EF.safeRecip := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp (Primrec.const 5) Primrec.encode).of_eq fun a => by
    rfl

private lemma efVar_prim : Primrec EF.var := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp (Primrec.const 6) Primrec.id).of_eq fun i => by
    rfl

private lemma efLet_prim : Primrec₂ EF.letE := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 7)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun x body => by rfl

private def efStreamBinary (op : EF → EF → EF)
    (data : List EF × List (EF × Sentence)) : Option EF.StreamState :=
  match data.1 with
  | b :: a :: rest => some ((0, none), (op a b :: rest, data.2))
  | _ => none

private lemma efStreamBinary_prim (op : EF → EF → EF) (hop : Primrec₂ op) :
    Primrec (efStreamBinary op) := by
  let S := List EF × List (EF × Sentence)
  let Y := S × (EF × List EF)
  have hy2 : Primrec fun y : Y => y.2 := Primrec.snd
  have htail : Primrec fun y : Y => y.2.2 := Primrec.snd.comp hy2
  have hresult : Primrec₂ fun (y : Y) (ar : EF × List EF) =>
      some (((0, none), (op ar.1 y.2.1 :: ar.2, y.1.2)) : EF.StreamState) := by
    have hop' : Primrec fun z : Y × (EF × List EF) => op z.2.1 z.1.2.1 :=
      hop.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have hrest : Primrec fun z : Y × (EF × List EF) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hstack : Primrec fun z : Y × (EF × List EF) =>
        op z.2.1 z.1.2.1 :: z.2.2 :=
      Primrec.list_cons.comp hop' hrest
    have htrades : Primrec fun z : Y × (EF × List EF) => z.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    exact Primrec₂.option_some_iff.mpr
      ((Primrec.const (0, (none : Option Sentence))).pair (hstack.pair htrades)).to₂
  have hsecond : Primrec fun y : Y =>
      match y.2.2 with
      | [] => (none : Option EF.StreamState)
      | a :: rest => some ((0, none), (op a y.2.1 :: rest, y.1.2)) :=
    (Primrec.list_casesOn htail (Primrec.const (none : Option EF.StreamState))
      hresult).of_eq fun y => by cases y.2.2 <;> rfl
  have hfirst : Primrec₂ fun (data : S) (br : EF × List EF) =>
      match br.2 with
      | [] => (none : Option EF.StreamState)
      | a :: rest => some ((0, none), (op a br.1 :: rest, data.2)) :=
    hsecond.to₂
  exact (Primrec.list_casesOn Primrec.fst
    (Primrec.const (none : Option EF.StreamState)) hfirst).of_eq
    fun data => by
      rcases data with ⟨stack, trades⟩
      cases stack with
      | nil => rfl
      | cons b tail =>
          cases tail with
          | nil => rfl
          | cons a rest => rfl

private def efStreamUnary (op : EF → EF)
    (data : List EF × List (EF × Sentence)) : Option EF.StreamState :=
  match data.1 with
  | a :: rest => some ((0, none), (op a :: rest, data.2))
  | [] => none

private lemma efStreamUnary_prim (op : EF → EF) (hop : Primrec op) :
    Primrec (efStreamUnary op) := by
  let S := List EF × List (EF × Sentence)
  have hresult : Primrec₂ fun (data : S) (ar : EF × List EF) =>
      some (((0, none), (op ar.1 :: ar.2, data.2)) : EF.StreamState) := by
    have hop' : Primrec fun z : S × (EF × List EF) => op z.2.1 :=
      hop.comp (Primrec.fst.comp Primrec.snd)
    have hrest : Primrec fun z : S × (EF × List EF) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hstack : Primrec fun z : S × (EF × List EF) => op z.2.1 :: z.2.2 :=
      Primrec.list_cons.comp hop' hrest
    have htrades : Primrec fun z : S × (EF × List EF) => z.1.2 :=
      Primrec.snd.comp Primrec.fst
    exact Primrec₂.option_some_iff.mpr
      ((Primrec.const (0, (none : Option Sentence))).pair (hstack.pair htrades)).to₂
  exact (Primrec.list_casesOn Primrec.fst
    (Primrec.const (none : Option EF.StreamState)) hresult).of_eq fun data => by
      rcases data with ⟨stack, trades⟩
      cases stack <;> rfl

private def efStreamMode (mode : ℕ)
    (data : List EF × List (EF × Sentence)) : Option EF.StreamState :=
  some ((mode, none), data)

private lemma efStreamMode_prim (mode : ℕ) : Primrec (efStreamMode mode) := by
  exact Primrec.option_some_iff.mpr
    ((Primrec.const (mode, (none : Option Sentence))).pair Primrec.id)

private def efStreamSentence
    (data : List EF × List (EF × Sentence)) (token : ℕ) :
    Option EF.StreamState :=
  (Encodable.decode (α := Sentence) token).map fun φ => ((2, some φ), data)

private lemma efStreamSentence_prim : Primrec₂ efStreamSentence := by
  let S := List EF × List (EF × Sentence)
  let P := S × ℕ
  have hdecode : Primrec fun p : P => Encodable.decode (α := Sentence) p.2 :=
    Primrec.decode.comp Primrec.snd
  have hmap : Primrec₂ fun (p : P) (φ : Sentence) =>
      (((2, some φ), p.1) : EF.StreamState) := by
    have hpending : Primrec fun z : P × Sentence => some z.2 :=
      Primrec.option_some.comp Primrec.snd
    have hcontrol : Primrec fun z : P × Sentence => (2, some z.2) :=
      (Primrec.const 2).pair hpending
    have hdata : Primrec fun z : P × Sentence => z.1.1 :=
      Primrec.fst.comp Primrec.fst
    exact (hcontrol.pair hdata).to₂
  exact (Primrec.option_map hdecode hmap).to₂

private def efStreamConst
    (data : List EF × List (EF × Sentence)) (token : ℕ) :
    Option EF.StreamState :=
  (Encodable.decode (α := ℚ) token).map fun q =>
    ((0, none), (EF.const q :: data.1, data.2))

private lemma efStreamConst_prim : Primrec₂ efStreamConst := by
  let S := List EF × List (EF × Sentence)
  let P := S × ℕ
  have hdecode : Primrec fun p : P => Encodable.decode (α := ℚ) p.2 :=
    Primrec.decode.comp Primrec.snd
  have hmap : Primrec₂ fun (p : P) (q : ℚ) =>
      (((0, none), (EF.const q :: p.1.1, p.1.2)) : EF.StreamState) := by
    have hfeature : Primrec fun z : P × ℚ => EF.const z.2 :=
      efConst_prim.comp Primrec.snd
    have hstack : Primrec fun z : P × ℚ => EF.const z.2 :: z.1.1.1 :=
      Primrec.list_cons.comp hfeature
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have htrades : Primrec fun z : P × ℚ => z.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    exact ((Primrec.const (0, (none : Option Sentence))).pair
      (hstack.pair htrades)).to₂
  exact (Primrec.option_map hdecode hmap).to₂

private def efStreamVar
    (data : List EF × List (EF × Sentence)) (token : ℕ) :
    Option EF.StreamState :=
  some ((0, none), (EF.var token :: data.1, data.2))

private lemma efStreamVar_prim : Primrec₂ efStreamVar := by
  let S := List EF × List (EF × Sentence)
  let P := S × ℕ
  have hfeature : Primrec fun p : P => EF.var p.2 := efVar_prim.comp Primrec.snd
  have hstack : Primrec fun p : P => EF.var p.2 :: p.1.1 :=
    Primrec.list_cons.comp hfeature (Primrec.fst.comp Primrec.fst)
  have htrades : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  exact (Primrec.option_some_iff.mpr
    ((Primrec.const (0, (none : Option Sentence))).pair
      (hstack.pair htrades))).to₂

private def efStreamPrice
    (input : (Option Sentence × (List EF × List (EF × Sentence))) × ℕ) :
    Option EF.StreamState :=
  input.1.1.map fun φ =>
    ((0, none), (EF.price φ input.2 :: input.1.2.1, input.1.2.2))

private lemma efStreamPrice_prim : Primrec efStreamPrice := by
  let S := List EF × List (EF × Sentence)
  let P := (Option Sentence × S) × ℕ
  have hpending : Primrec fun p : P => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hmap : Primrec₂ fun (p : P) (φ : Sentence) =>
      (((0, none), (EF.price φ p.2 :: p.1.2.1, p.1.2.2)) : EF.StreamState) := by
    have hfeature : Primrec fun z : P × Sentence => EF.price z.2 z.1.2 :=
      efPrice_prim.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
    have hstack : Primrec fun z : P × Sentence =>
        EF.price z.2 z.1.2 :: z.1.1.2.1 :=
      Primrec.list_cons.comp hfeature
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    have htrades : Primrec fun z : P × Sentence => z.1.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    exact ((Primrec.const (0, (none : Option Sentence))).pair
      (hstack.pair htrades)).to₂
  exact Primrec.option_map hpending hmap

private def efStreamTrade
    (input : (List EF × List (EF × Sentence)) × ℕ) :
    Option EF.StreamState :=
  match input.1.1 with
  | e :: rest => (Encodable.decode (α := Sentence) input.2).map fun φ =>
      ((0, none), (rest, input.1.2 ++ [(e, φ)]))
  | [] => none

private lemma efStreamTrade_prim : Primrec efStreamTrade := by
  let S := List EF × List (EF × Sentence)
  let P := S × ℕ
  let Y := P × (EF × List EF)
  have hdecode : Primrec fun y : Y => Encodable.decode (α := Sentence) y.1.2 :=
    Primrec.decode.comp (Primrec.snd.comp Primrec.fst)
  have hmap : Primrec₂ fun (y : Y) (φ : Sentence) =>
      (((0, none), (y.2.2, y.1.1.2 ++ [(y.2.1, φ)])) : EF.StreamState) := by
    have hrest : Primrec fun z : Y × Sentence => z.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have htrade : Primrec fun z : Y × Sentence => (z.1.2.1, z.2) :=
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
    have htrades : Primrec fun z : Y × Sentence => z.1.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hout : Primrec fun z : Y × Sentence =>
        z.1.1.1.2 ++ [(z.1.2.1, z.2)] :=
      Primrec.list_concat.comp htrades htrade
    exact ((Primrec.const (0, (none : Option Sentence))).pair
      (hrest.pair hout)).to₂
  have hcons : Primrec₂ fun (p : P) (er : EF × List EF) =>
      (Encodable.decode (α := Sentence) p.2).map fun φ =>
        (((0, none), (er.2, p.1.2 ++ [(er.1, φ)])) : EF.StreamState) :=
    (Primrec.option_map hdecode hmap).to₂
  exact (Primrec.list_casesOn (Primrec.fst.comp Primrec.fst)
    (Primrec.const (none : Option EF.StreamState)) hcons).of_eq fun input => by
      rcases input with ⟨⟨stack, trades⟩, token⟩
      cases stack <;> rfl

private lemma efStreamStepState_prim : Primrec fun
    input : EF.StreamState × ℕ => EF.streamStep (some input.1) input.2 := by
  let P := EF.StreamState × ℕ
  have hmode : Primrec fun p : P => p.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hpending : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hdata : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have htoken : Primrec fun p : P => p.2 := Primrec.snd
  have hmodeEq (k : ℕ) : PrimrecPred fun p : P => p.1.1.1 = k :=
    Primrec.eq.comp hmode (Primrec.const k)
  have htokenEq (k : ℕ) : PrimrecPred fun p : P => p.2 = k :=
    Primrec.eq.comp htoken (Primrec.const k)
  have hsetMode (k : ℕ) : Primrec fun p : P => efStreamMode k p.1.2 :=
    (efStreamMode_prim k).comp hdata
  have hbinary (op : EF → EF → EF) (hop : Primrec₂ op) :
      Primrec fun p : P => efStreamBinary op p.1.2 :=
    (efStreamBinary_prim op hop).comp hdata
  have hunary (op : EF → EF) (hop : Primrec op) :
      Primrec fun p : P => efStreamUnary op p.1.2 :=
    (efStreamUnary_prim op hop).comp hdata
  have hnone : Primrec fun _ : P => (none : Option EF.StreamState) :=
    Primrec.const (none : Option EF.StreamState)
  have hready : Primrec fun p : P =>
      if p.2 = 0 then efStreamMode 1 p.1.2
      else if p.2 = 1 then efStreamMode 3 p.1.2
      else if p.2 = 2 then efStreamBinary EF.add p.1.2
      else if p.2 = 3 then efStreamBinary EF.mul p.1.2
      else if p.2 = 4 then efStreamBinary EF.max p.1.2
      else if p.2 = 5 then efStreamUnary EF.safeRecip p.1.2
      else if p.2 = 6 then efStreamMode 4 p.1.2
      else if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 0) (hsetMode 1)
      (Primrec.ite (htokenEq 1) (hsetMode 3)
        (Primrec.ite (htokenEq 2) (hbinary EF.add efAdd_prim)
          (Primrec.ite (htokenEq 3) (hbinary EF.mul efMul_prim)
            (Primrec.ite (htokenEq 4) (hbinary EF.max efMax_prim)
              (Primrec.ite (htokenEq 5) (hunary EF.safeRecip efSafeRecip_prim)
                (Primrec.ite (htokenEq 6) (hsetMode 4)
                  (Primrec.ite (htokenEq 7) (hsetMode 5)
                    (Primrec.ite (htokenEq 8) (hbinary EF.letE efLet_prim)
                      hnone))))))))
  have hpriceInput : Primrec fun p : P => ((p.1.1.2, p.1.2), p.2) :=
    (hpending.pair hdata).pair htoken
  have htradeInput : Primrec fun p : P => (p.1.2, p.2) := hdata.pair htoken
  have hmode1 : Primrec fun p : P =>
      if p.1.1.1 = 1 then efStreamSentence p.1.2 p.2
      else if p.1.1.1 = 2 then efStreamPrice ((p.1.1.2, p.1.2), p.2)
      else if p.1.1.1 = 3 then efStreamConst p.1.2 p.2
      else if p.1.1.1 = 4 then efStreamTrade (p.1.2, p.2)
      else if p.1.1.1 = 5 then efStreamVar p.1.2 p.2 else none :=
    Primrec.ite (hmodeEq 1) (efStreamSentence_prim.comp hdata htoken)
      (Primrec.ite (hmodeEq 2) (efStreamPrice_prim.comp hpriceInput)
        (Primrec.ite (hmodeEq 3) (efStreamConst_prim.comp hdata htoken)
          (Primrec.ite (hmodeEq 4) (efStreamTrade_prim.comp htradeInput)
            (Primrec.ite (hmodeEq 5) (efStreamVar_prim.comp hdata htoken)
              hnone))))
  exact (Primrec.ite (hmodeEq 0) hready hmode1).of_eq fun input => by
    rcases input with ⟨⟨⟨mode, pending⟩, ⟨efst, trades⟩⟩, token⟩
    simp only [EF.streamStep, efStreamMode, efStreamBinary, efStreamUnary,
      efStreamSentence, efStreamPrice, efStreamConst, efStreamTrade, efStreamVar]
    by_cases h0 : mode = 0
    · subst mode
      norm_num
      rfl
    by_cases h1 : mode = 1
    · subst mode
      norm_num
    by_cases h2 : mode = 2
    · subst mode
      norm_num
    by_cases h3 : mode = 3
    · subst mode
      norm_num
    by_cases h4 : mode = 4
    · subst mode
      norm_num
      cases efst with
      | nil => rfl
      | cons e rest =>
          cases Encodable.decode (α := Sentence) token <;> rfl
    by_cases h5 : mode = 5
    · subst mode
      norm_num
    simp [h0, h1, h2, h3, h4, h5]

private lemma efStreamStep_prim : Primrec₂ EF.streamStep := by
  let P := Option EF.StreamState × ℕ
  have hsome : Primrec₂ fun (p : P) (state : EF.StreamState) =>
      EF.streamStep (some state) p.2 := by
    have hinput : Primrec fun z : P × EF.StreamState => (z.2, z.1.2) :=
      Primrec.snd.pair (Primrec.snd.comp Primrec.fst)
    exact (efStreamStepState_prim.comp hinput).to₂
  exact ((Primrec.option_casesOn Primrec.fst
    (Primrec.const (none : Option EF.StreamState)) hsome).to₂).of_eq fun state token => by
      cases state <;> rfl

private lemma efStreamReadFrom_prim : Primrec₂ EF.streamReadFrom := by
  let P := List ℕ × Option EF.StreamState
  have hstep : Primrec₂ fun (_p : P) (st : Option EF.StreamState × ℕ) =>
      EF.streamStep st.1 st.2 := by
    have hstate : Primrec fun z : P × (Option EF.StreamState × ℕ) => z.2.1 :=
      Primrec.fst.comp Primrec.snd
    have htoken : Primrec fun z : P × (Option EF.StreamState × ℕ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    exact (efStreamStep_prim.comp hstate htoken).to₂
  exact ((Primrec.list_foldl Primrec.fst Primrec.snd hstep).to₂).of_eq
    fun tokens state => by rfl

private def efStreamFinish (state : Option EF.StreamState) :
    Option (List (EF × Sentence)) :=
  match state with
  | some ((0, none), ([], trades)) => some trades
  | _ => none

private lemma efStreamFinish_prim : Primrec efStreamFinish := by
  have hsome : Primrec₂ fun (_state : Option EF.StreamState) (s : EF.StreamState) =>
      if s.1.1 = 0 then
        match s.1.2 with
        | none =>
            match s.2.1 with
            | [] => some s.2.2
            | _ => none
        | some _ => none
      else none := by
    let P := Option EF.StreamState × EF.StreamState
    have hmode : Primrec fun p : P => p.2.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hmodeZero : PrimrecPred fun p : P => p.2.1.1 = 0 :=
      Primrec.eq.comp hmode (Primrec.const 0)
    have hstack : Primrec fun p : P => p.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have htrades : Primrec fun p : P => p.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hstackFinish : Primrec fun p : P =>
        match p.2.2.1 with
        | [] => some p.2.2.2
        | _ => none :=
      (Primrec.list_casesOn hstack
        (Primrec.option_some.comp htrades)
        (Primrec₂.const (none : Option (List (EF × Sentence))))).of_eq fun p => by
          cases p.2.2.1 <;> rfl
    have hpending : Primrec fun p : P => p.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have hpendingFinish : Primrec fun p : P =>
        match p.2.1.2 with
        | none =>
            match p.2.2.1 with
            | [] => some p.2.2.2
            | _ => none
        | some _ => none :=
      (Primrec.option_casesOn hpending hstackFinish
        (Primrec₂.const (none : Option (List (EF × Sentence))))).of_eq fun p => by
          cases p.2.1.2 <;> rfl
    exact (Primrec.ite hmodeZero hpendingFinish
      (Primrec.const (none : Option (List (EF × Sentence))))).to₂
  exact (Primrec.option_casesOn Primrec.id
    (Primrec.const (none : Option (List (EF × Sentence)))) hsome).of_eq fun state => by
      cases state with
      | none => rfl
      | some s =>
          rcases s with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
          by_cases hm : mode = 0
          · subst mode
            cases pending <;> cases stack <;> rfl
          · cases mode with
            | zero => exact (hm rfl).elim
            | succ mode => rfl

/-- Decoding a token stream into a trade list is primitive recursive. -/
lemma deserializeTrades_prim : Primrec deserializeTrades := by
  have hread : Primrec fun tokens : List ℕ =>
      EF.streamReadFrom tokens (some EF.streamInitial) :=
    efStreamReadFrom_prim.comp Primrec.id (Primrec.const (some EF.streamInitial))
  exact (efStreamFinish_prim.comp hread).of_eq fun tokens => by
    unfold deserializeTrades efStreamFinish
    cases EF.streamReadFrom tokens (some EF.streamInitial) with
    | none => rfl
    | some state =>
        rcases state with ⟨⟨mode, pending⟩, ⟨stack, trades⟩⟩
        cases mode <;> cases pending <;> cases stack <;> rfl

private lemma strategyTradesValid_primDigit :
    PrimrecRel fun (trades : List (EF × Sentence)) n =>
      ∀ p ∈ trades, p.1.rank ≤ n := by
  have hp : PrimrecRel fun (p : EF × Sentence) n => p.1.rank ≤ n :=
    Primrec.nat_le.comp₂
      ((efRank_prim.comp Primrec.fst).comp₂ Primrec₂.left)
      Primrec₂.right
  exact hp.forall_mem_list

lemma strategyOfTokensTrades_prim : Primrec₂ fun n tokens =>
    (strategyOfTokens n tokens).trades := by
  let P := ℕ × List ℕ
  have hdecode : Primrec fun p : P => deserializeTrades p.2 :=
    deserializeTrades_prim.comp Primrec.snd
  have hsome : Primrec₂ fun (p : P) (trades : List (EF × Sentence)) =>
      if ∀ trade ∈ trades, trade.1.rank ≤ p.1 then trades else [] := by
    have hvalid : PrimrecPred fun z : P × List (EF × Sentence) =>
        ∀ trade ∈ z.2, trade.1.rank ≤ z.1.1 :=
      PrimrecRel.comp strategyTradesValid_primDigit Primrec.snd
        (Primrec.fst.comp Primrec.fst)
    exact (Primrec.ite hvalid Primrec.snd (Primrec.const [])).to₂
  exact ((Primrec.option_casesOn hdecode (Primrec.const []) hsome).to₂).of_eq
    fun n tokens => by
      simp only []
      unfold strategyOfTokens
      split
      · simp_all
      · split <;> simp_all

section RpnDecodePrimrec

open Nat.Partrec (Code)
open Nat.Partrec.Code

-- `Nat.sqrt` irreducible: see the module header.
attribute [local irreducible] Nat.sqrt

/-! ## Primitive recursion of the token decode

The trading firm's compiler runs the token-metered decode.  With the concrete
`Primcodable Sentence` instance in scope, each strong-recursion step is a composition of
standard `Primrec` combinators. -/

private abbrev PCtx :=
  (List (Option (ℕ × List ℕ)) × ℕ) × (ℕ × List ℕ)

private lemma structuredNatG_prim : Primrec structuredNatG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  let Ctx := (List (Option (ℕ × List ℕ)) × ℕ) × (ℕ × List ℕ)
  have hprev : Primrec fun x : Ctx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : Ctx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : Ctx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : Ctx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hlook : Primrec fun x : Ctx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hzero : Primrec fun x : Ctx => (some (0, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp ((Primrec.const 0).pair hrest)
  have heven : Primrec fun x : Ctx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
        fun p => (2 * p.1, p.2) := by
    exact Primrec.option_map hlook
      ((Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)).to₂
  have hodd : Primrec fun x : Ctx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
        fun p => (2 * p.1 + 1, p.2) := by
    exact Primrec.option_map hlook
      ((Primrec.succ.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))).pair
        (Primrec.snd.comp Primrec.snd)).to₂
  have heqt : ∀ k : ℕ, PrimrecPred fun x : Ctx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : Ctx =>
      if x.2.1 = 0 then some (0, x.2.2)
      else if x.2.1 = 1 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
          fun p => (2 * p.1, p.2)
      else if x.2.1 = 2 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map
          fun p => (2 * p.1 + 1, p.2)
      else none := by
    exact Primrec.ite (heqt 0) hzero <|
      Primrec.ite (heqt 1) heven <| Primrec.ite (heqt 2) hodd (Primrec.const none)
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 0 then some (0, rest)
          else if t = 1 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).map
              fun (q : ℕ × List ℕ) => (2 * q.1, q.2)
          else if t = 2 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).map
              fun (q : ℕ × List ℕ) => (2 * q.1 + 1, q.2)
          else none :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;> rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq fun prev => ?_
  rw [structuredNatG]
  rcases hf : prev.length.unpair.1 with _ | fuel
  · simp [structuredNatGCore, hf]
  rcases hs : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with _ | ⟨t, rest⟩
  · simp [structuredNatGCore, hf, hs]
  simp [structuredNatGCore, hf, hs]

private lemma parseStructuredNat_prim : Primrec₂ parseStructuredNat := by
  have hF : Primrec₂ (fun (_ : Unit) => structuredNatF) :=
    Primrec.nat_strong_rec _ (structuredNatG_prim.comp Primrec.snd).to₂
      fun _ n => structuredNatG_spec n
  have hF1 : Primrec structuredNatF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      structuredNatF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [structuredNatF, Nat.unpair_pair, Denumerable.ofNat_encode]

private lemma structuredTermG_prim : Primrec structuredTermG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : PCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : PCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : PCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : PCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hnat : Primrec fun x : PCtx => parseStructuredNat x.1.2 x.2.2 :=
    parseStructuredNat_prim.comp hfuel' hrest
  have hvar (kind : ℕ) : Primrec fun x : PCtx =>
      (parseStructuredNat x.1.2 x.2.2).map fun p =>
        (Nat.pair kind p.1 + 1, p.2) := by
    refine Primrec.option_map hnat ?_
    exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const kind)
      (Primrec.fst.comp Primrec.snd))).pair (Primrec.snd.comp Primrec.snd)
  have hconst (symbol : ℕ) : Primrec fun x : PCtx =>
      (some (arithmeticFuncCode 0 symbol 0, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp ((Primrec.const _).pair hrest)
  have hlook1 : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hlook2 : Primrec fun y : PCtx × (ℕ × List ℕ) =>
      ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (hprev.comp Primrec.fst)
        (Primrec₂.natPair.comp (hfuel'.comp Primrec.fst)
          (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const none)
  have hout : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (arithmeticFuncCode 2 (if z.1.1.2.1 = 7 then 0 else 1)
        (arithmeticVec2Code z.1.2.1 z.2.1), z.2.2) := by
    have hsymbol : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        if z.1.1.2.1 = 7 then 0 else 1 :=
      Primrec.ite
        (PrimrecRel.comp Primrec.eq
          (ht.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 7))
        (Primrec.const 0) (Primrec.const 1)
    have hvec : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        arithmeticVec2Code z.1.2.1 z.2.1 := by
      simp only [arithmeticVec2Code]
      exact Primrec.succ.comp (Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.succ.comp (Primrec₂.natPair.comp
          (Primrec.fst.comp Primrec.snd) (Primrec.const 0))))
    have hcode : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        arithmeticFuncCode 2 (if z.1.1.2.1 = 7 then 0 else 1)
          (arithmeticVec2Code z.1.2.1 z.2.1) := by
      simp only [arithmeticFuncCode]
      exact Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (Primrec.const 2)
          (Primrec₂.natPair.comp hsymbol hvec)))
    exact hcode.pair (Primrec.snd.comp Primrec.snd)
  have hbin : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
          (arithmeticFuncCode 2 (if x.2.1 = 7 then 0 else 1)
            (arithmeticVec2Code p.1 q.1), q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_map hlook2 hout.to₂).to₂
  have heqt : ∀ k : ℕ, PrimrecPred fun x : PCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : PCtx =>
      if x.2.1 = 3 then
        (parseStructuredNat x.1.2 x.2.2).map fun p => (Nat.pair 0 p.1 + 1, p.2)
      else if x.2.1 = 4 then
        (parseStructuredNat x.1.2 x.2.2).map fun p => (Nat.pair 1 p.1 + 1, p.2)
      else if x.2.1 = 5 then some (arithmeticFuncCode 0 0 0, x.2.2)
      else if x.2.1 = 6 then some (arithmeticFuncCode 0 1 0, x.2.2)
      else if x.2.1 = 7 ∨ x.2.1 = 8 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
            (arithmeticFuncCode 2 (if x.2.1 = 7 then 0 else 1)
              (arithmeticVec2Code p.1 q.1), q.2)
      else none := by
    exact Primrec.ite (heqt 3) (hvar 0) <| Primrec.ite (heqt 4) (hvar 1) <|
      Primrec.ite (heqt 5) (hconst 0) <| Primrec.ite (heqt 6) (hconst 1) <|
        Primrec.ite ((heqt 7).or (heqt 8)) hbin (Primrec.const none)
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 3 then
            (parseStructuredNat p.2 rest).map fun (q : ℕ × List ℕ) =>
              (Nat.pair 0 q.1 + 1, q.2)
          else if t = 4 then
            (parseStructuredNat p.2 rest).map fun (q : ℕ × List ℕ) =>
              (Nat.pair 1 q.1 + 1, q.2)
          else if t = 5 then some (arithmeticFuncCode 0 0 0, rest)
          else if t = 6 then some (arithmeticFuncCode 0 1 0, rest)
          else if t = 7 ∨ t = 8 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind
                fun (q : ℕ × List ℕ) =>
              ((p.1[Nat.pair p.2 (Encodable.encode q.2)]?).getD none).map
                fun (r : ℕ × List ℕ) =>
                (arithmeticFuncCode 2 (if t = 7 then 0 else 1)
                  (arithmeticVec2Code q.1 r.1), r.2)
          else none :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;> rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq fun prev => ?_
  rw [structuredTermG]
  rcases hf : prev.length.unpair.1 with _ | fuel
  · simp [structuredTermGCore, hf]
  rcases hs : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with _ | ⟨t, rest⟩
  · simp [structuredTermGCore, hf, hs]
  simp [structuredTermGCore, hf, hs]

private lemma parseStructuredArithmeticTerm_prim :
    Primrec₂ fun fuel ts => parseStructuredArithmeticTerm fuel 0 ts := by
  have hF : Primrec₂ (fun (_ : Unit) => structuredTermF) :=
    Primrec.nat_strong_rec _ (structuredTermG_prim.comp Primrec.snd).to₂
      fun _ n => structuredTermG_spec n
  have hF1 : Primrec structuredTermF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      structuredTermF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [structuredTermF, Nat.unpair_pair, Denumerable.ofNat_encode]

/-- Memoized mirror of `negFormulaCode`: the recursive calls are replaced by lookups at
strictly smaller indices, so the whole map is a single strong recursion. -/
private def negFormulaGCore (n : ℕ) (look : ℕ → ℕ) : ℕ :=
  match n with
  | 0 => 0
  | e + 1 =>
      if e.unpair.1 = 0 then Nat.pair 1 e.unpair.2 + 1
      else if e.unpair.1 = 1 then Nat.pair 0 e.unpair.2 + 1
      else if e.unpair.1 = 2 then Nat.pair 3 0 + 1
      else if e.unpair.1 = 3 then Nat.pair 2 0 + 1
      else if e.unpair.1 = 4 then
        Nat.pair 5 (Nat.pair (look e.unpair.2.unpair.1) (look e.unpair.2.unpair.2)) + 1
      else if e.unpair.1 = 5 then
        Nat.pair 4 (Nat.pair (look e.unpair.2.unpair.1) (look e.unpair.2.unpair.2)) + 1
      else if e.unpair.1 = 6 then Nat.pair 7 (look e.unpair.2) + 1
      else if e.unpair.1 = 7 then Nat.pair 6 (look e.unpair.2) + 1
      else 0

private lemma negFormulaGCore_spec (n : ℕ) (look : ℕ → ℕ)
    (hlook : ∀ i, i < n → look i = negFormulaCode i) :
    negFormulaGCore n look = negFormulaCode n := by
  rcases n with _ | e
  · rw [negFormulaCode]
    rfl
  have hc : e.unpair.2 ≤ e := Nat.unpair_right_le e
  have h1 : e.unpair.2.unpair.1 < e + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.unpair_left_le _) hc)
  have h2 : e.unpair.2.unpair.2 < e + 1 :=
    Nat.lt_succ_of_le (le_trans (Nat.unpair_right_le _) hc)
  have h3 : e.unpair.2 < e + 1 := Nat.lt_succ_of_le hc
  rw [negFormulaGCore, negFormulaCode]
  simp only [hlook _ h1, hlook _ h2, hlook _ h3]

private def negFormulaG (prev : List ℕ) : Option ℕ :=
  some (negFormulaGCore prev.length fun i => (prev[i]?).getD 0)

private lemma negFormulaG_spec (n : ℕ) :
    negFormulaG ((List.range n).map negFormulaCode) = some (negFormulaCode n) := by
  rw [negFormulaG,
    show ((List.range n).map negFormulaCode).length = n from by simp]
  congr 1
  refine negFormulaGCore_spec n _ fun i hi => ?_
  have hib : i < ((List.range n).map negFormulaCode).length := by simpa using hi
  rw [List.getElem?_eq_getElem hib, Option.getD_some, List.getElem_map,
    List.getElem_range]

private lemma negFormulaG_prim : Primrec negFormulaG := by
  have hlen : Primrec fun prev : List ℕ => prev.length := Primrec.list_length
  have ha : Primrec fun x : List ℕ × ℕ => x.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hc : Primrec fun x : List ℕ × ℕ => x.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hlookOf : ∀ {i : List ℕ × ℕ → ℕ}, Primrec i →
      Primrec fun x : List ℕ × ℕ => ((x.1[i x]?).getD 0) := fun hi =>
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.fst hi) (Primrec.const 0)
  have hl1 := hlookOf (Primrec.fst.comp (Primrec.unpair.comp hc))
  have hl2 := hlookOf (Primrec.snd.comp (Primrec.unpair.comp hc))
  have hl3 := hlookOf hc
  have heqa : ∀ k : ℕ, PrimrecPred fun x : List ℕ × ℕ => x.2.unpair.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ha (Primrec.const k)
  have hswap (tag : ℕ) : Primrec fun x : List ℕ × ℕ =>
      Nat.pair tag x.2.unpair.2 + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const tag) hc)
  have hbin (tag : ℕ) : Primrec fun x : List ℕ × ℕ =>
      Nat.pair tag (Nat.pair ((x.1[x.2.unpair.2.unpair.1]?).getD 0)
        ((x.1[x.2.unpair.2.unpair.2]?).getD 0)) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const tag)
      (Primrec₂.natPair.comp hl1 hl2))
  have hq (tag : ℕ) : Primrec fun x : List ℕ × ℕ =>
      Nat.pair tag ((x.1[x.2.unpair.2]?).getD 0) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const tag) hl3)
  have hbody : Primrec fun x : List ℕ × ℕ =>
      if x.2.unpair.1 = 0 then Nat.pair 1 x.2.unpair.2 + 1
      else if x.2.unpair.1 = 1 then Nat.pair 0 x.2.unpair.2 + 1
      else if x.2.unpair.1 = 2 then Nat.pair 3 0 + 1
      else if x.2.unpair.1 = 3 then Nat.pair 2 0 + 1
      else if x.2.unpair.1 = 4 then
        Nat.pair 5 (Nat.pair ((x.1[x.2.unpair.2.unpair.1]?).getD 0)
          ((x.1[x.2.unpair.2.unpair.2]?).getD 0)) + 1
      else if x.2.unpair.1 = 5 then
        Nat.pair 4 (Nat.pair ((x.1[x.2.unpair.2.unpair.1]?).getD 0)
          ((x.1[x.2.unpair.2.unpair.2]?).getD 0)) + 1
      else if x.2.unpair.1 = 6 then Nat.pair 7 ((x.1[x.2.unpair.2]?).getD 0) + 1
      else if x.2.unpair.1 = 7 then Nat.pair 6 ((x.1[x.2.unpair.2]?).getD 0) + 1
      else 0 := by
    exact Primrec.ite (heqa 0) (hswap 1) <| Primrec.ite (heqa 1) (hswap 0) <|
      Primrec.ite (heqa 2) (Primrec.const _) <|
        Primrec.ite (heqa 3) (Primrec.const _) <|
          Primrec.ite (heqa 4) (hbin 5) <| Primrec.ite (heqa 5) (hbin 4) <|
            Primrec.ite (heqa 6) (hq 7) <|
              Primrec.ite (heqa 7) (hq 6) (Primrec.const 0)
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hlen (Primrec.const 0) hbody.to₂)).of_eq fun prev => ?_
  rw [negFormulaG]
  rcases hn : prev.length with _ | e
  · simp [negFormulaGCore]
  simp [negFormulaGCore]

/-- Tag-swapping De Morgan negation on formula codes is primitive recursive.  Exported
alongside `parseStructuredArithmeticFormula_prim`, and for the same reason: together they
are the decoding half of the source-text naming of formulas (`negSourceFormulaCode`,
`Construction/Knowledge/SourceNumbering.lean`). -/
lemma negFormulaCode_prim : Primrec negFormulaCode := by
  have hF : Primrec₂ (fun (_ : Unit) => negFormulaCode) :=
    Primrec.nat_strong_rec _ (negFormulaG_prim.comp Primrec.snd).to₂
      fun _ n => negFormulaG_spec n
  exact hF.comp (Primrec.const ()) Primrec.id

private lemma structuredFormulaG_prim : Primrec structuredFormulaG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : PCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : PCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : PCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : PCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hconst (tag : ℕ) : Primrec fun x : PCtx =>
      (some (Nat.pair tag 0 + 1, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp
      ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const tag)
        (Primrec.const 0))).pair hrest)
  have hterm1 : Primrec fun x : PCtx =>
      parseStructuredArithmeticTerm x.1.2 0 x.2.2 :=
    parseStructuredArithmeticTerm_prim.comp hfuel' hrest
  have hterm2 : Primrec fun y : PCtx × (ℕ × List ℕ) =>
      parseStructuredArithmeticTerm y.1.1.2 0 y.2.2 :=
    parseStructuredArithmeticTerm_prim.comp (hfuel'.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hrelOut : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (arithmeticRelCode (z.1.1.2.1 = 12 ∨ z.1.1.2.1 = 14)
        (if z.1.1.2.1 = 11 ∨ z.1.1.2.1 = 12 then 0 else 1)
        z.1.2.1 z.2.1, z.2.2) := by
    have htag : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        z.1.1.2.1 := ht.comp (Primrec.fst.comp Primrec.fst)
    have heqt : ∀ k : ℕ, PrimrecPred fun z :
        (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) => z.1.1.2.1 = k := fun k =>
      PrimrecRel.comp Primrec.eq htag (Primrec.const k)
    have hnegative : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        if decide (z.1.1.2.1 = 12 ∨ z.1.1.2.1 = 14) then 1 else 0 :=
      (Primrec.ite ((heqt 12).or (heqt 14)) (Primrec.const 1)
        (Primrec.const 0)).of_eq fun z => by simp
    have hsymbol : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        if z.1.1.2.1 = 11 ∨ z.1.1.2.1 = 12 then 0 else 1 :=
      Primrec.ite ((heqt 11).or (heqt 12)) (Primrec.const 0) (Primrec.const 1)
    have hvec : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        arithmeticVec2Code z.1.2.1 z.2.1 := by
      simp only [arithmeticVec2Code]
      exact Primrec.succ.comp (Primrec₂.natPair.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.succ.comp (Primrec₂.natPair.comp
          (Primrec.fst.comp Primrec.snd) (Primrec.const 0))))
    have hcode : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        arithmeticRelCode (z.1.1.2.1 = 12 ∨ z.1.1.2.1 = 14)
          (if z.1.1.2.1 = 11 ∨ z.1.1.2.1 = 12 then 0 else 1)
          z.1.2.1 z.2.1 := by
      simp only [arithmeticRelCode]
      exact Primrec.succ.comp (Primrec₂.natPair.comp hnegative
        (Primrec₂.natPair.comp (Primrec.const 2)
          (Primrec₂.natPair.comp hsymbol hvec)))
    exact hcode.pair (Primrec.snd.comp Primrec.snd)
  have hrel : Primrec fun x : PCtx =>
      (parseStructuredArithmeticTerm x.1.2 0 x.2.2).bind fun p =>
        (parseStructuredArithmeticTerm x.1.2 0 p.2).map fun q =>
          (arithmeticRelCode (x.2.1 = 12 ∨ x.2.1 = 14)
            (if x.2.1 = 11 ∨ x.2.1 = 12 then 0 else 1) p.1 q.1, q.2) :=
    Primrec.option_bind hterm1 (Primrec.option_map hterm2 hrelOut.to₂).to₂
  have hlook1 : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hlook2 : Primrec fun y : PCtx × (ℕ × List ℕ) =>
      ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (hprev.comp Primrec.fst)
        (Primrec₂.natPair.comp (hfuel'.comp Primrec.fst)
          (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const none)
  have hbinOut : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (Nat.pair (if z.1.1.2.1 = 15 then 4 else 5)
        (Nat.pair z.1.2.1 z.2.1) + 1, z.2.2) := by
    have htag : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        z.1.1.2.1 := ht.comp (Primrec.fst.comp Primrec.fst)
    have hkind : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        if z.1.1.2.1 = 15 then 4 else 5 :=
      Primrec.ite (PrimrecRel.comp Primrec.eq htag (Primrec.const 15))
        (Primrec.const 4) (Primrec.const 5)
    have hpq : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        Nat.pair z.1.2.1 z.2.1 :=
      Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd)
    exact (Primrec.succ.comp (Primrec₂.natPair.comp hkind hpq)).pair
      (Primrec.snd.comp Primrec.snd)
  have hbin : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
          (Nat.pair (if x.2.1 = 15 then 4 else 5) (Nat.pair p.1 q.1) + 1, q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_map hlook2 hbinOut.to₂).to₂
  have hquantOut : Primrec fun y : PCtx × (ℕ × List ℕ) =>
      (Nat.pair (if y.1.2.1 = 17 then 6 else 7) y.2.1 + 1, y.2.2) := by
    have hkind : Primrec fun y : PCtx × (ℕ × List ℕ) =>
        if y.1.2.1 = 17 then 6 else 7 :=
      Primrec.ite (PrimrecRel.comp Primrec.eq (ht.comp Primrec.fst) (Primrec.const 17))
        (Primrec.const 6) (Primrec.const 7)
    exact (Primrec.succ.comp (Primrec₂.natPair.comp hkind
      (Primrec.fst.comp Primrec.snd))).pair (Primrec.snd.comp Primrec.snd)
  have hquant : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map fun p =>
        (Nat.pair (if x.2.1 = 17 then 6 else 7) p.1 + 1, p.2) :=
    Primrec.option_map hlook1 hquantOut.to₂
  have hnegOut : Primrec fun y : PCtx × (ℕ × List ℕ) =>
      (negFormulaCode y.2.1, y.2.2) :=
    (negFormulaCode_prim.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  have hneg : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map fun p =>
        (negFormulaCode p.1, p.2) :=
    Primrec.option_map hlook1 hnegOut.to₂
  have hnegP : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      negFormulaCode z.1.2.1 :=
    negFormulaCode_prim.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hnegQ : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      negFormulaCode z.2.1 :=
    negFormulaCode_prim.comp (Primrec.fst.comp Primrec.snd)
  have hPfst : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      z.1.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hQfst : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      z.2.1 := Primrec.fst.comp Primrec.snd
  have himpCode : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      Nat.pair 5 (Nat.pair (negFormulaCode z.1.2.1) z.2.1) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5)
      (Primrec₂.natPair.comp hnegP hQfst))
  have hconvCode : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      Nat.pair 5 (Nat.pair (negFormulaCode z.2.1) z.1.2.1) + 1 :=
    Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5)
      (Primrec₂.natPair.comp hnegQ hPfst))
  have himpOut : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (Nat.pair 5 (Nat.pair (negFormulaCode z.1.2.1) z.2.1) + 1, z.2.2) :=
    himpCode.pair (Primrec.snd.comp Primrec.snd)
  have himp : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
          (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1, q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_map hlook2 himpOut.to₂).to₂
  have hiffOut : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (Nat.pair 4
        (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode z.1.2.1) z.2.1) + 1)
          (Nat.pair 5 (Nat.pair (negFormulaCode z.2.1) z.1.2.1) + 1)) + 1, z.2.2) :=
    (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4)
      (Primrec₂.natPair.comp himpCode hconvCode))).pair
      (Primrec.snd.comp Primrec.snd)
  have hiff : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
          (Nat.pair 4
            (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1)
              (Nat.pair 5 (Nat.pair (negFormulaCode q.1) p.1) + 1)) + 1, q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_map hlook2 hiffOut.to₂).to₂
  have heqt : ∀ k : ℕ, PrimrecPred fun x : PCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : PCtx =>
      if x.2.1 = 9 then some (Nat.pair 2 0 + 1, x.2.2)
      else if x.2.1 = 10 then some (Nat.pair 3 0 + 1, x.2.2)
      else if x.2.1 = 11 ∨ x.2.1 = 12 ∨ x.2.1 = 13 ∨ x.2.1 = 14 then
        (parseStructuredArithmeticTerm x.1.2 0 x.2.2).bind fun p =>
          (parseStructuredArithmeticTerm x.1.2 0 p.2).map fun q =>
            (arithmeticRelCode (x.2.1 = 12 ∨ x.2.1 = 14)
              (if x.2.1 = 11 ∨ x.2.1 = 12 then 0 else 1) p.1 q.1, q.2)
      else if x.2.1 = 15 ∨ x.2.1 = 16 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
            (Nat.pair (if x.2.1 = 15 then 4 else 5) (Nat.pair p.1 q.1) + 1, q.2)
      else if x.2.1 = 17 ∨ x.2.1 = 18 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map fun p =>
          (Nat.pair (if x.2.1 = 17 then 6 else 7) p.1 + 1, p.2)
      else if x.2.1 = 20 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).map fun p =>
          (negFormulaCode p.1, p.2)
      else if x.2.1 = 21 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
            (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1, q.2)
      else if x.2.1 = 22 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).map fun q =>
            (Nat.pair 4
              (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode p.1) q.1) + 1)
                (Nat.pair 5 (Nat.pair (negFormulaCode q.1) p.1) + 1)) + 1, q.2)
      else none := by
    exact Primrec.ite (heqt 9) (hconst 2) <| Primrec.ite (heqt 10) (hconst 3) <|
      Primrec.ite ((heqt 11).or ((heqt 12).or ((heqt 13).or (heqt 14)))) hrel <|
        Primrec.ite ((heqt 15).or (heqt 16)) hbin <|
          Primrec.ite ((heqt 17).or (heqt 18)) hquant <|
            Primrec.ite (heqt 20) hneg <| Primrec.ite (heqt 21) himp <|
              Primrec.ite (heqt 22) hiff (Primrec.const none)
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 9 then some (Nat.pair 2 0 + 1, rest)
          else if t = 10 then some (Nat.pair 3 0 + 1, rest)
          else if t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 then
            (parseStructuredArithmeticTerm p.2 0 rest).bind fun q =>
              (parseStructuredArithmeticTerm p.2 0 q.2).map fun (r : ℕ × List ℕ) =>
                (arithmeticRelCode (t = 12 ∨ t = 14)
                  (if t = 11 ∨ t = 12 then 0 else 1) q.1 r.1, r.2)
          else if t = 15 ∨ t = 16 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind fun q =>
              ((p.1[Nat.pair p.2 (Encodable.encode q.2)]?).getD none).map
                fun (r : ℕ × List ℕ) =>
                (Nat.pair (if t = 15 then 4 else 5) (Nat.pair q.1 r.1) + 1, r.2)
          else if t = 17 ∨ t = 18 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).map
              fun (q : ℕ × List ℕ) =>
              (Nat.pair (if t = 17 then 6 else 7) q.1 + 1, q.2)
          else if t = 20 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).map
              fun (q : ℕ × List ℕ) => (negFormulaCode q.1, q.2)
          else if t = 21 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind fun q =>
              ((p.1[Nat.pair p.2 (Encodable.encode q.2)]?).getD none).map
                fun (r : ℕ × List ℕ) =>
                (Nat.pair 5 (Nat.pair (negFormulaCode q.1) r.1) + 1, r.2)
          else if t = 22 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind fun q =>
              ((p.1[Nat.pair p.2 (Encodable.encode q.2)]?).getD none).map
                fun (r : ℕ × List ℕ) =>
                (Nat.pair 4
                  (Nat.pair (Nat.pair 5 (Nat.pair (negFormulaCode q.1) r.1) + 1)
                    (Nat.pair 5 (Nat.pair (negFormulaCode r.1) q.1) + 1)) + 1, r.2)
          else none :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;> rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq fun prev => ?_
  rw [structuredFormulaG]
  rcases hf : prev.length.unpair.1 with _ | fuel
  · simp [structuredFormulaGCore, hf]
  rcases hs : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with _ | ⟨t, rest⟩
  · simp [structuredFormulaGCore, hf, hs]
  simp [structuredFormulaGCore, hf, hs]

/-- The structured arithmetic formula grammar is primitive recursive.  Exported (rather
than private, like its siblings in this section) because it is also the decoding half of
the source-text naming of formulas: `negSourceFormulaCode`
(`Construction/Knowledge/SourceNumbering.lean`) recovers a formula's Godel code from the
numeral naming its written run, and needs exactly this certificate. -/
lemma parseStructuredArithmeticFormula_prim :
    Primrec₂ fun fuel ts => parseStructuredArithmeticFormula fuel 0 ts := by
  have hF : Primrec₂ (fun (_ : Unit) => structuredFormulaF) :=
    Primrec.nat_strong_rec _ (structuredFormulaG_prim.comp Primrec.snd).to₂
      fun _ n => structuredFormulaG_spec n
  have hF1 : Primrec structuredFormulaF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      structuredFormulaF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [structuredFormulaF, Nat.unpair_pair, Denumerable.ofNat_encode]

private lemma readStructuredLength_prim : Primrec readStructuredLength := by
  have hstep : Primrec fun x : List ℕ × (ℕ × List ℕ × Option (ℕ × List ℕ)) =>
      if x.2.1 = 0 then some (0, x.2.2.1)
      else if x.2.1 = 1 then x.2.2.2.map fun p => (p.1 + 1, p.2)
      else none := by
    have ht : Primrec fun x : List ℕ × (ℕ × List ℕ × Option (ℕ × List ℕ)) =>
        x.2.1 := Primrec.fst.comp Primrec.snd
    have hrest : Primrec fun x : List ℕ × (ℕ × List ℕ × Option (ℕ × List ℕ)) =>
        x.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hzero : Primrec fun x : List ℕ × (ℕ × List ℕ × Option (ℕ × List ℕ)) =>
        (some (0, x.2.2.1) : Option (ℕ × List ℕ)) :=
      Primrec.option_some.comp ((Primrec.const 0).pair hrest)
    have hih : Primrec fun x : List ℕ × (ℕ × List ℕ × Option (ℕ × List ℕ)) =>
        x.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hsucc : Primrec fun x : List ℕ × (ℕ × List ℕ × Option (ℕ × List ℕ)) =>
        x.2.2.2.map fun p => (p.1 + 1, p.2) := by
      refine Primrec.option_map hih ?_
      exact (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)
    have heqt : ∀ k : ℕ, PrimrecPred fun x :
        List ℕ × (ℕ × List ℕ × Option (ℕ × List ℕ)) => x.2.1 = k := fun k =>
      PrimrecRel.comp Primrec.eq ht (Primrec.const k)
    exact Primrec.ite (heqt 0) hzero <|
      Primrec.ite (heqt 1) hsucc (Primrec.const none)
  exact (Primrec.list_rec Primrec.id (Primrec.const none) hstep.to₂).of_eq fun ts => by
    induction ts with
    | nil => rfl
    | cons t rest ih =>
        simp only [id_eq] at ih ⊢
        rw [ih]
        rcases t with _ | t
        · rfl
        rcases t with _ | t
        · rfl
        simp [readStructuredLength]

private abbrev StructuredPrimeHeadCtx := List ℕ × (ℕ × List ℕ)
private abbrev StructuredPrimeLenCtx := StructuredPrimeHeadCtx × (ℕ × List ℕ)

private lemma parseStructuredPaperPrimeC_prim : Primrec parseStructuredPaperPrimeC := by
  have hpol : Primrec fun y : StructuredPrimeHeadCtx => y.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hframed : Primrec fun y : StructuredPrimeHeadCtx => y.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hlen : Primrec fun y : StructuredPrimeHeadCtx => readStructuredLength y.2.2 :=
    readStructuredLength_prim.comp hframed
  have hn : Primrec fun z : StructuredPrimeLenCtx => z.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hpayload : Primrec fun z : StructuredPrimeLenCtx => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have htake : Primrec fun z : StructuredPrimeLenCtx => z.2.2.take z.2.1 :=
    Primrec.list_take.comp hn hpayload
  have hdrop : Primrec fun z : StructuredPrimeLenCtx => z.2.2.drop (z.2.1 + 1) :=
    Primrec.list_drop.comp (Primrec.succ.comp hn) hpayload
  have hformula : Primrec fun z : StructuredPrimeLenCtx =>
      parseStructuredArithmeticFormula z.2.1 0 (z.2.2.take z.2.1) :=
    parseStructuredArithmeticFormula_prim.comp hn htake
  have hresult : Primrec fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) =>
      if w.2.2 = [] ∧ List.getD w.1.2.2 w.1.2.1 0 = 19 then
        some (Nat.pair 1 (Nat.pair 5 (Nat.pair w.1.1.2.1 w.2.1)) + 1,
          w.1.2.2.drop (w.1.2.1 + 1))
      else none := by
    have hrest : Primrec fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) => w.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hempty : PrimrecPred fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) =>
        w.2.2 = [] := by
      exact (PrimrecRel.comp Primrec.eq (Primrec.list_length.comp hrest)
        (Primrec.const 0)).of_eq fun w => by simp
    have hget : Primrec fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) =>
        List.getD w.1.2.2 w.1.2.1 0 :=
      (Primrec.list_getD 0).comp (hpayload.comp Primrec.fst) (hn.comp Primrec.fst)
    have hterm : PrimrecPred fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) =>
        List.getD w.1.2.2 w.1.2.1 0 = 19 :=
      PrimrecRel.comp Primrec.eq hget (Primrec.const 19)
    have hpol' : Primrec fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) =>
        w.1.1.2.1 := hpol.comp (Primrec.fst.comp Primrec.fst)
    have hcode : Primrec fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) => w.2.1 :=
      Primrec.fst.comp Primrec.snd
    have houtCode : Primrec fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) =>
        Nat.pair 1 (Nat.pair 5 (Nat.pair w.1.1.2.1 w.2.1)) + 1 :=
      Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec₂.natPair.comp (Primrec.const 5)
          (Primrec₂.natPair.comp hpol' hcode)))
    have houtRest : Primrec fun w : StructuredPrimeLenCtx × (ℕ × List ℕ) =>
        w.1.2.2.drop (w.1.2.1 + 1) :=
      hdrop.comp Primrec.fst
    exact Primrec.ite (hempty.and hterm)
      (Primrec.option_some.comp (houtCode.pair houtRest)) (Primrec.const none)
  have hparsed : Primrec fun z : StructuredPrimeLenCtx =>
      (parseStructuredArithmeticFormula z.2.1 0 (z.2.2.take z.2.1)).bind fun p =>
        if p.2 = [] ∧ List.getD z.2.2 z.2.1 0 = 19 then
          some (Nat.pair 1 (Nat.pair 5 (Nat.pair z.1.2.1 p.1)) + 1,
            z.2.2.drop (z.2.1 + 1))
        else none :=
    Primrec.option_bind hformula hresult.to₂
  have hwithin : PrimrecPred fun z : StructuredPrimeLenCtx =>
      z.2.1 ≤ z.2.2.length :=
    Primrec.nat_le.comp hn (Primrec.list_length.comp hpayload)
  have hafterLength : Primrec fun z : StructuredPrimeLenCtx =>
      if z.2.1 ≤ z.2.2.length then
        (parseStructuredArithmeticFormula z.2.1 0 (z.2.2.take z.2.1)).bind fun p =>
          if p.2 = [] ∧ List.getD z.2.2 z.2.1 0 = 19 then
            some (Nat.pair 1 (Nat.pair 5 (Nat.pair z.1.2.1 p.1)) + 1,
              z.2.2.drop (z.2.1 + 1))
          else none
      else none :=
    Primrec.ite hwithin hparsed (Primrec.const none)
  have hlengthBody : Primrec fun y : StructuredPrimeHeadCtx =>
      (readStructuredLength y.2.2).bind fun p =>
        if p.1 ≤ p.2.length then
          (parseStructuredArithmeticFormula p.1 0 (p.2.take p.1)).bind fun q =>
            if q.2 = [] ∧ List.getD p.2 p.1 0 = 19 then
              some (Nat.pair 1 (Nat.pair 5 (Nat.pair y.2.1 q.1)) + 1,
                p.2.drop (p.1 + 1))
            else none
        else none :=
    Primrec.option_bind hlen hafterLength.to₂
  have hpolarity : PrimrecPred fun y : StructuredPrimeHeadCtx => y.2.1 ≤ 1 :=
    Primrec.nat_le.comp hpol (Primrec.const 1)
  have hcons : Primrec fun y : StructuredPrimeHeadCtx =>
      if y.2.1 ≤ 1 then
        (readStructuredLength y.2.2).bind fun p =>
          if p.1 ≤ p.2.length then
            (parseStructuredArithmeticFormula p.1 0 (p.2.take p.1)).bind fun q =>
              if q.2 = [] ∧ List.getD p.2 p.1 0 = 19 then
                some (Nat.pair 1 (Nat.pair 5 (Nat.pair y.2.1 q.1)) + 1,
                  p.2.drop (p.1 + 1))
              else none
          else none
      else none :=
    Primrec.ite hpolarity hlengthBody (Primrec.const none)
  exact (Primrec.list_casesOn Primrec.id (Primrec.const none) hcons.to₂).of_eq fun ts => by
    rcases ts with _ | ⟨polarity, framed⟩
    · rfl
    simp only [id_eq, parseStructuredPaperPrimeC]
    by_cases hpol : polarity ≤ 1
    · simp only [hpol, if_true]
      rcases hl : readStructuredLength framed with _ | p
      · simp
      simp only [Option.bind_some]
      by_cases hlen : p.1 ≤ p.2.length
      · simp only [hlen, if_true]
        rcases hf : parseStructuredArithmeticFormula p.1 0 (p.2.take p.1) with
          _ | ⟨code, rest⟩
        · simp
        rcases rest with _ | ⟨r, rest⟩ <;> simp
      · simp [hlen]
    · simp [hpol]

private lemma parseG_prim : Primrec parseG := by
  have hfuel : Primrec fun prev : List (Option (ℕ × List ℕ)) =>
      prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : PCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : PCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : PCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : PCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hbr0 : Primrec fun x : PCtx =>
      (some (Nat.pair 0 0 + 1, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp ((Primrec.const (Nat.pair 0 0 + 1)).pair hrest)
  have hesc : Primrec fun x : PCtx =>
      match x.2.2 with
      | 0 :: payload => parseStructuredPaperPrimeC payload
      | c :: tail =>
          if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
          else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1, tail)
      | [] => none := by
    have hc : Primrec fun y : PCtx × (ℕ × List ℕ) => y.2.1 :=
      Primrec.fst.comp Primrec.snd
    have htail : Primrec fun y : PCtx × (ℕ × List ℕ) => y.2.2 :=
      Primrec.snd.comp Primrec.snd
    have he : Primrec fun y : PCtx × (ℕ × List ℕ) =>
        Encodable.encode (Encodable.decode (α := Sentence) y.2.1) :=
      (Primrec.encdec.comp hc).of_eq fun y => rfl
    have hstructured : Primrec fun y : PCtx × (ℕ × List ℕ) =>
        parseStructuredPaperPrimeC y.2.2 :=
      parseStructuredPaperPrimeC_prim.comp htail
    have hsentenceCode : Primrec fun y : PCtx × (ℕ × List ℕ) =>
        if Encodable.encode (Encodable.decode (α := Sentence) y.2.1) = 0 then none
        else some (Encodable.encode (Encodable.decode (α := Sentence) y.2.1) - 1,
          y.2.2) :=
      Primrec.ite (PrimrecRel.comp Primrec.eq he (Primrec.const 0))
        (Primrec.const none)
        (Primrec.option_some.comp ((Primrec.pred.comp he).pair htail))
    have hcons : Primrec fun y : PCtx × (ℕ × List ℕ) =>
        if y.2.1 = 0 then parseStructuredPaperPrimeC y.2.2
        else if Encodable.encode (Encodable.decode (α := Sentence) y.2.1) = 0 then none
        else some (Encodable.encode (Encodable.decode (α := Sentence) y.2.1) - 1,
          y.2.2) :=
      Primrec.ite (PrimrecRel.comp Primrec.eq hc (Primrec.const 0))
        hstructured hsentenceCode
    exact (Primrec.list_casesOn hrest (Primrec.const none) hcons.to₂).of_eq fun x => by
      rcases x.2.2 with _ | ⟨c, tail⟩
      · rfl
      rcases c with _ | c
      · rfl
      simp
  have hlook1 : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hprev
        (Primrec₂.natPair.comp hfuel' (Primrec.encode.comp hrest)))
      (Primrec.const none)
  have hlook2 : Primrec fun y : PCtx × (ℕ × List ℕ) =>
      ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD none) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (hprev.comp Primrec.fst)
        (Primrec₂.natPair.comp (hfuel'.comp Primrec.fst)
          (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.const none)
  have hout : Primrec fun z : (PCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
      (some (Nat.pair z.1.1.2.1 (Nat.pair z.1.2.1 z.2.1) + 1, z.2.2) :
        Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp
      ((Primrec.succ.comp (Primrec₂.natPair.comp
          (ht.comp (Primrec.fst.comp Primrec.fst))
          (Primrec₂.natPair.comp
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd)))).pair
        (Primrec.snd.comp Primrec.snd))
  have hbin : Primrec fun x : PCtx =>
      ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).bind fun q =>
          some (Nat.pair x.2.1 (Nat.pair p.1 q.1) + 1, q.2) :=
    Primrec.option_bind hlook1 (Primrec.option_bind hlook2 hout.to₂).to₂
  have hatom : Primrec fun x : PCtx =>
      (some (Nat.pair 1 (x.2.1 - 5) + 1, x.2.2) : Option (ℕ × List ℕ)) :=
    Primrec.option_some.comp
      ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec.nat_sub.comp ht (Primrec.const 5)))).pair hrest)
  have heqt : ∀ k : ℕ, PrimrecPred fun x : PCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : PCtx =>
      if x.2.1 = 0 then some (Nat.pair 0 0 + 1, x.2.2)
      else if x.2.1 = 1 then
        match x.2.2 with
        | 0 :: payload => parseStructuredPaperPrimeC payload
        | c :: tail =>
            if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
            else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1, tail)
        | [] => none
      else if x.2.1 = 2 ∨ x.2.1 = 3 ∨ x.2.1 = 4 then
        ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD none).bind fun p =>
          ((x.1.1[Nat.pair x.1.2 (Encodable.encode p.2)]?).getD none).bind fun q =>
            some (Nat.pair x.2.1 (Nat.pair p.1 q.1) + 1, q.2)
      else some (Nat.pair 1 (x.2.1 - 5) + 1, x.2.2) := by
    refine Primrec.ite (heqt 0) hbr0 ?_
    refine Primrec.ite (heqt 1) hesc ?_
    exact Primrec.ite ((heqt 2).or ((heqt 3).or (heqt 4))) hbin hatom
  have hinner : Primrec fun p : List (Option (ℕ × List ℕ)) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => (none : Option (ℕ × List ℕ))
      | t :: rest =>
          if t = 0 then some (Nat.pair 0 0 + 1, rest)
          else if t = 1 then
            match rest with
            | 0 :: payload => parseStructuredPaperPrimeC payload
            | c :: tail =>
                if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
                else some
                  (Encodable.encode (Encodable.decode (α := Sentence) c) - 1, tail)
            | [] => none
          else if t = 2 ∨ t = 3 ∨ t = 4 then
            ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD none).bind
              fun q1 =>
                ((p.1[Nat.pair p.2 (Encodable.encode q1.2)]?).getD none).bind
                  fun q2 =>
                    some (Nat.pair t (Nat.pair q1.1 q2.1) + 1, q2.2)
          else some (Nat.pair 1 (t - 5) + 1, rest) :=
    (Primrec.list_casesOn hts0 (Primrec.const none) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;>
        rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel (Primrec.const none) hinner.to₂)).of_eq
    fun prev => ?_
  rw [parseG, parseGCore]
  cases hf : prev.length.unpair.1 with
  | zero => rfl
  | succ fuel' =>
      cases hts : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
      | nil => simp [hts]
      | cons t rest =>
          simp only [hts]
          rfl

/-- The symbol-block parser is primitive recursive. -/
lemma parseRpnC_prim : Primrec₂ parseRpnC := by
  have hF : Primrec₂ (fun (_ : Unit) => parseF) :=
    Primrec.nat_strong_rec _ (parseG_prim.comp Primrec.snd).to₂
      fun _ n => parseG_spec n
  have hF1 : Primrec parseF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun p : ℕ × List ℕ =>
      parseF (Nat.pair p.1 (Encodable.encode p.2)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd))
  exact h2.to₂.of_eq fun fuel ts => by
    rw [parseF, Nat.unpair_pair, Denumerable.ofNat_encode]

private abbrev UCtx := (List (List ℕ) × ℕ) × (ℕ × List ℕ)

private lemma unG_prim : Primrec unG := by
  have hfuel : Primrec fun prev : List (List ℕ) => prev.length.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hts0 : Primrec fun p : List (List ℕ) × ℕ =>
      Denumerable.ofNat (List ℕ) p.1.length.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)))
  have hprev : Primrec fun x : UCtx => x.1.1 := Primrec.fst.comp Primrec.fst
  have hfuel' : Primrec fun x : UCtx => x.1.2 := Primrec.snd.comp Primrec.fst
  have ht : Primrec fun x : UCtx => x.2.1 := Primrec.fst.comp Primrec.snd
  have hrest : Primrec fun x : UCtx => x.2.2 := Primrec.snd.comp Primrec.snd
  have hlook : ∀ {γ : Type} [Primcodable γ]
      {fp : γ → List (List ℕ)} {ff : γ → ℕ} {fr : γ → List ℕ},
      Primrec fp → Primrec ff → Primrec fr →
      Primrec fun y : γ => ((fp y)[Nat.pair (ff y) (Encodable.encode (fr y))]?).getD
        ([] : List ℕ) := by
    intro γ _ fp ff fr hp hf hr
    exact Primrec.option_getD.comp
      (Primrec.list_getElem?.comp hp
        (Primrec₂.natPair.comp hf (Primrec.encode.comp hr)))
      (Primrec.const [])
  have hparse : Primrec fun x : UCtx => parseRpnC x.2.2.length x.2.2 :=
    parseRpnC_prim.comp (Primrec.list_length.comp hrest) hrest
  -- price branch
  have hbr0inner : Primrec fun y : UCtx × (ℕ × List ℕ) =>
      match y.2.2 with
      | [] => [0, y.2.1]
      | d :: r2 =>
          0 :: y.2.1 :: d ::
            ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode r2)]?).getD []) := by
    have hnil : Primrec fun y : UCtx × (ℕ × List ℕ) => [0, y.2.1] :=
      Primrec.list_cons.comp (Primrec.const 0)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.const []))
    have hcons : Primrec fun z : (UCtx × (ℕ × List ℕ)) × (ℕ × List ℕ) =>
        0 :: z.1.2.1 :: z.2.1 ::
          ((z.1.1.1.1[Nat.pair z.1.1.1.2 (Encodable.encode z.2.2)]?).getD []) :=
      Primrec.list_cons.comp (Primrec.const 0)
        (Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
            (hlook (Primrec.fst.comp (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst)))
              (Primrec.snd.comp (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst)))
              (Primrec.snd.comp Primrec.snd))))
    exact (Primrec.list_casesOn (Primrec.snd.comp Primrec.snd) hnil
      hcons.to₂).of_eq fun y => by rcases y.2.2 with _ | ⟨d, r2⟩ <;> rfl
  have hbr0 : Primrec fun x : UCtx =>
      match parseRpnC x.2.2.length x.2.2 with
      | none => [0, 0]
      | some (e, r1) =>
          match r1 with
          | [] => [0, e]
          | d :: r2 =>
              0 :: e :: d ::
                ((x.1.1[Nat.pair x.1.2 (Encodable.encode r2)]?).getD []) :=
    (Primrec.option_casesOn hparse (Primrec.const [0, 0]) hbr0inner.to₂).of_eq
      fun x => by
        rcases parseRpnC x.2.2.length x.2.2 with _ | ⟨e, r1⟩
        · rfl
        rcases r1 with _ | ⟨d, r2⟩ <;> rfl
  -- trade branch
  have hbr6inner : Primrec fun y : UCtx × (ℕ × List ℕ) =>
      6 :: y.2.1 ::
        ((y.1.1.1[Nat.pair y.1.1.2 (Encodable.encode y.2.2)]?).getD []) :=
    Primrec.list_cons.comp (Primrec.const 6)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (hlook (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
  have hbr6 : Primrec fun x : UCtx =>
      match parseRpnC x.2.2.length x.2.2 with
      | none => [6, 0]
      | some (e, r1) =>
          6 :: e :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r1)]?).getD []) :=
    (Primrec.option_casesOn hparse (Primrec.const [6, 0]) hbr6inner.to₂).of_eq
      fun x => by rcases parseRpnC x.2.2.length x.2.2 with _ | ⟨e, r1⟩ <;> rfl
  -- opaque payload branches
  have hpayinner : ∀ tag : ℕ, Primrec fun z : UCtx × (ℕ × List ℕ) =>
      tag :: z.2.1 ::
        ((z.1.1.1[Nat.pair z.1.1.2 (Encodable.encode z.2.2)]?).getD []) := by
    intro tag
    exact Primrec.list_cons.comp (Primrec.const tag)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (hlook (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd)))
  have hpay : ∀ tag : ℕ, Primrec fun x : UCtx =>
      match x.2.2 with
      | [] => [tag]
      | c :: r =>
          tag :: c :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r)]?).getD []) := by
    intro tag
    exact (Primrec.list_casesOn hrest (Primrec.const [tag])
      (hpayinner tag).to₂).of_eq fun x => by
        rcases x.2.2 with _ | ⟨c, r⟩ <;> rfl
  -- copy branch
  have hcopy : Primrec fun x : UCtx =>
      x.2.1 :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD []) :=
    Primrec.list_cons.comp ht (hlook hprev hfuel' hrest)
  have heqt : ∀ k : ℕ, PrimrecPred fun x : UCtx => x.2.1 = k := fun k =>
    PrimrecRel.comp Primrec.eq ht (Primrec.const k)
  have hbody : Primrec fun x : UCtx =>
      if x.2.1 = 0 then
        match parseRpnC x.2.2.length x.2.2 with
        | none => [0, 0]
        | some (e, r1) =>
            match r1 with
            | [] => [0, e]
            | d :: r2 =>
                0 :: e :: d ::
                  ((x.1.1[Nat.pair x.1.2 (Encodable.encode r2)]?).getD [])
      else if x.2.1 = 6 then
        match parseRpnC x.2.2.length x.2.2 with
        | none => [6, 0]
        | some (e, r1) =>
            6 :: e :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r1)]?).getD [])
      else if x.2.1 = 1 then
        match x.2.2 with
        | [] => [1]
        | c :: r =>
            1 :: c :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r)]?).getD [])
      else if x.2.1 = 7 then
        match x.2.2 with
        | [] => [7]
        | c :: r =>
            7 :: c :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode r)]?).getD [])
      else x.2.1 :: ((x.1.1[Nat.pair x.1.2 (Encodable.encode x.2.2)]?).getD []) := by
    refine Primrec.ite (heqt 0) hbr0 ?_
    refine Primrec.ite (heqt 6) hbr6 ?_
    refine Primrec.ite (heqt 1) (hpay 1) ?_
    exact Primrec.ite (heqt 7) (hpay 7) hcopy
  have hinner : Primrec fun p : List (List ℕ) × ℕ =>
      match Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with
      | [] => ([] : List ℕ)
      | t :: rest =>
          if t = 0 then
            match parseRpnC rest.length rest with
            | none => [0, 0]
            | some (e, r1) =>
                match r1 with
                | [] => [0, e]
                | d :: r2 =>
                    0 :: e :: d ::
                      ((p.1[Nat.pair p.2 (Encodable.encode r2)]?).getD [])
          else if t = 6 then
            match parseRpnC rest.length rest with
            | none => [6, 0]
            | some (e, r1) =>
                6 :: e :: ((p.1[Nat.pair p.2 (Encodable.encode r1)]?).getD [])
          else if t = 1 then
            match rest with
            | [] => [1]
            | c :: r =>
                1 :: c :: ((p.1[Nat.pair p.2 (Encodable.encode r)]?).getD [])
          else if t = 7 then
            match rest with
            | [] => [7]
            | c :: r =>
                7 :: c :: ((p.1[Nat.pair p.2 (Encodable.encode r)]?).getD [])
          else t :: ((p.1[Nat.pair p.2 (Encodable.encode rest)]?).getD []) :=
    (Primrec.list_casesOn hts0 (Primrec.const []) hbody.to₂).of_eq fun p => by
      rcases Denumerable.ofNat (List ℕ) p.1.length.unpair.2 with _ | ⟨t, rest⟩ <;>
        rfl
  refine (Primrec.option_some.comp
    (Primrec.nat_casesOn hfuel
      ((Primrec.list_casesOn
        ((Primrec.ofNat (List ℕ)).comp
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)))
        (Primrec.const []) (Primrec.const []).to₂).of_eq fun prev => by
          rcases Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
            _ | ⟨t, rest⟩ <;> rfl)
      hinner.to₂)).of_eq fun prev => ?_
  rw [unG, unGCore]
  cases hf : prev.length.unpair.1 with
  | zero =>
      cases hts : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
      | nil => simp [hts]
      | cons t rest => simp [hts]
  | succ fuel' =>
      cases hts : Denumerable.ofNat (List ℕ) prev.length.unpair.2 with
      | nil => simp [hts]
      | cons t rest =>
          simp only [hts]
          rfl

/-- The stream contraction is primitive recursive. -/
lemma unRpn_prim : Primrec unRpn := by
  have hF : Primrec₂ (fun (_ : Unit) => unF) :=
    Primrec.nat_strong_rec _ (unG_prim.comp Primrec.snd).to₂
      fun _ n => unG_spec n
  have hF1 : Primrec unF := hF.comp (Primrec.const ()) Primrec.id
  have h2 : Primrec fun ts : List ℕ =>
      unF (Nat.pair ts.length (Encodable.encode ts)) :=
    hF1.comp (Primrec₂.natPair.comp Primrec.list_length Primrec.encode)
  exact h2.of_eq fun ts => by
    rw [unF, Nat.unpair_pair, Denumerable.ofNat_encode, ← unRpn_eq_unRpnTokensC]

/-- A token-metered sentence sequence (`def:ec`) has primitive-recursive whole-value
codes: its block stream is primitive recursive (`PolySegStream.primrec`) and the block
parser decodes each segment.  Note the codes are **not** polynomially fueled — a deep
sentence's pair code is value-exponential in its symbol count — so this is exactly the
recursive-naming residue available at arithmetic quotation boundaries. -/
lemma RpnSentenceCodes.primrec {φ : ℕ → Sentence} (h : RpnSentenceCodes φ) :
    Primrec fun n => Encodable.encode (φ n) := by
  obtain ⟨s, hs, hp⟩ := h
  have hsp : Primrec s := hs.primrec
  have hparse : Primrec fun n => parseRpnC (s n).length (s n) :=
    parseRpnC_prim.comp (Primrec.list_length.comp hsp) hsp
  have hmap : Primrec fun n =>
      (parseRpnC (s n).length (s n)).map Prod.fst :=
    Primrec.option_map hparse (Primrec.fst.comp Primrec.snd).to₂
  refine ((Primrec.option_getD.comp hmap (Primrec.const 0)).of_eq fun n => ?_)
  rw [parseRpnC_eq, hp n]
  rfl

/-- The whole-value naming program extracted from a token-metered sentence sequence.
Used where a *value* code is genuinely required (market quote tables keyed by sentence
code), as opposed to token-metered emission. -/
lemma RpnSentenceCodes.exists_code {φ : ℕ → Sentence} (h : RpnSentenceCodes φ) :
    ∃ c : Nat.Partrec.Code, ∀ n, Encodable.encode (φ n) ∈ c.eval n := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp h.primrec))
  exact ⟨c, fun n => by rw [hc]; exact Part.mem_some _⟩

/-- The write-out mirror of `RpnSentenceCodes.primrec`: a written-out sentence stream is
primitive recursive, via `BigTokenStream.primrec`.  Primitive recursion carries no time
budget, so reassembling an exponentially-named code here is legitimate — this is the route
by which a market quote table keyed by sentence code accepts write-out data. -/
lemma BigSentenceCodes.primrec {φ : ℕ → Sentence} (h : BigSentenceCodes φ) :
    Primrec fun n => Encodable.encode (φ n) := by
  obtain ⟨s, hs, hp⟩ := h
  have hsp : Primrec s := hs.primrec
  have hparse : Primrec fun n => parseRpnC (s n).length (s n) :=
    parseRpnC_prim.comp (Primrec.list_length.comp hsp) hsp
  have hmap : Primrec fun n =>
      (parseRpnC (s n).length (s n)).map Prod.fst :=
    Primrec.option_map hparse (Primrec.fst.comp Primrec.snd).to₂
  refine ((Primrec.option_getD.comp hmap (Primrec.const 0)).of_eq fun n => ?_)
  rw [parseRpnC_eq, hp n]
  rfl

/-- The whole-value naming program extracted from a written-out sentence sequence. -/
lemma BigSentenceCodes.exists_code {φ : ℕ → Sentence} (h : BigSentenceCodes φ) :
    ∃ c : Nat.Partrec.Code, ∀ n, Encodable.encode (φ n) ∈ c.eval n := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp
    (Nat.Partrec.of_primrec (Primrec.nat_iff.mp h.primrec))
  exact ⟨c, fun n => by rw [hc]; exact Part.mem_some _⟩

end RpnDecodePrimrec

end LogicalInduction
