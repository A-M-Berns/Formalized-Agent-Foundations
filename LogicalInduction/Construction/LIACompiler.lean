import LogicalInduction.Construction.LIAComputation
import Mathlib.Data.Rat.Denumerable

/-!
# Concrete compiler for the bounded LIA evaluator

This file supplies the primitive-recursive encoding infrastructure needed to instantiate
`LIABoundedEvaluatorCompiler`.  The first boundary is the project's actual propositional
sentence encoding: Foundation's decoder is structurally recursive on smaller Gödel numbers,
so we compile its encode-after-decode normalizer by primitive-recursive strong recursion.
-/

namespace LogicalInduction

open LO.Propositional

private def formulaBinaryNorm (tag : ℕ) (prior : List ℕ) (children : ℕ) : ℕ :=
  let left := prior.getD children.unpair.1 0
  let right := prior.getD children.unpair.2 0
  if left = 0 ∨ right = 0 then 0
  else Nat.pair tag (Nat.pair (left - 1) (right - 1)) + 2

private theorem formulaBinaryNorm_prim (tag : ℕ) :
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

private theorem formulaNormSucc_prim : Primrec₂ formulaNormSucc := by
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
  have h4 : Primrec fun p : List ℕ × ℕ =>
      if tag p = 4 then formulaBinaryNorm 4 p.1 (payload p) else 0 :=
    Primrec.ite (htagEq 4) (hbinary 4) (Primrec.const 0)
  have h3 : Primrec fun p : List ℕ × ℕ =>
      if tag p = 3 then formulaBinaryNorm 3 p.1 (payload p)
      else if tag p = 4 then formulaBinaryNorm 4 p.1 (payload p) else 0 :=
    Primrec.ite (htagEq 3) (hbinary 3) h4
  have h2 : Primrec fun p : List ℕ × ℕ =>
      if tag p = 2 then formulaBinaryNorm 2 p.1 (payload p)
      else if tag p = 3 then formulaBinaryNorm 3 p.1 (payload p)
      else if tag p = 4 then formulaBinaryNorm 4 p.1 (payload p) else 0 :=
    Primrec.ite (htagEq 2) (hbinary 2) h3
  have h1 : Primrec fun p : List ℕ × ℕ =>
      if tag p = 1 then Nat.pair 1 (payload p) + 2
      else if tag p = 2 then formulaBinaryNorm 2 p.1 (payload p)
      else if tag p = 3 then formulaBinaryNorm 3 p.1 (payload p)
      else if tag p = 4 then formulaBinaryNorm 4 p.1 (payload p) else 0 :=
    Primrec.ite (htagEq 1) htaggedAtom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const 2) h1).to₂.of_eq fun prior e => by
    simp only [formulaNormSucc, tag, payload]

private def formulaNormList (prior : List ℕ) : ℕ :=
  prior.length.casesOn 0 (formulaNormSucc prior)

private theorem formulaNormList_prim : Primrec formulaNormList := by
  exact (Primrec.nat_casesOn Primrec.list_length (Primrec.const 0)
    formulaNormSucc_prim).of_eq fun prior => by
      simp only [formulaNormList]

private def sentenceDecodeNorm (n : ℕ) : ℕ :=
  match (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) with
  | none => 0
  | some phi => LO.Propositional.Formula.toNat phi + 1

private theorem formulaHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map fun m =>
      sentenceDecodeNorm m).getD k 0 = sentenceDecodeNorm k := by
  have hzero : sentenceDecodeNorm 0 = 0 := by
    simp [sentenceDecodeNorm, LO.Propositional.Formula.ofNat]
  rw [← hzero, List.getD_map]
  simp [List.getD_eq_getElem, hk]

private theorem formulaBinaryNorm_history (tag payload n : ℕ)
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

private theorem formulaNormList_history (n : ℕ) :
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
          Nat.pair, tag, payload, h0]
      by_cases h1 : tag = 1
      · simp [sentenceDecodeNorm, formulaNormList, formulaNormSucc, LO.Propositional.Formula.ofNat,
          LO.Propositional.Formula.toNat,
          Nat.pair, tag, payload, h0, h1]
      by_cases h2 : tag = 2
      · subst tag
        have hb := formulaBinaryNorm_history 2 payload (e + 1) hleft hright
        simp only [formulaNormList, List.length_map, List.length_range,
          formulaNormSucc, h0, h1, h2, ↓reduceIte]
        rw [hb]
        unfold sentenceDecodeNorm
        simp only [LO.Propositional.Formula.ofNat, h2, ↓reduceIte]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.2 : Option Sentence) <;>
          simp [LO.Propositional.Formula.toNat]
      by_cases h3 : tag = 3
      · subst tag
        have hb := formulaBinaryNorm_history 3 payload (e + 1) hleft hright
        simp only [formulaNormList, List.length_map, List.length_range,
          formulaNormSucc, h0, h1, h2, h3, ↓reduceIte]
        rw [hb]
        unfold sentenceDecodeNorm
        simp only [LO.Propositional.Formula.ofNat, h3, ↓reduceIte]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.2 : Option Sentence) <;>
          simp [LO.Propositional.Formula.toNat]
      by_cases h4 : tag = 4
      · subst tag
        have hb := formulaBinaryNorm_history 4 payload (e + 1) hleft hright
        simp only [formulaNormList, List.length_map, List.length_range,
          formulaNormSucc, h0, h1, h2, h3, h4, ↓reduceIte]
        rw [hb]
        unfold sentenceDecodeNorm
        simp only [LO.Propositional.Formula.ofNat, h4, ↓reduceIte]
        cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.1 : Option Sentence) <;>
          cases (@LO.Propositional.Formula.ofNat ℕ inferInstance
            payload.unpair.2 : Option Sentence) <;>
          simp [LO.Propositional.Formula.toNat]
      · have htag : 5 ≤ tag := by omega
        simp [sentenceDecodeNorm, formulaNormList, formulaNormSucc, LO.Propositional.Formula.ofNat,
          LO.Propositional.Formula.toNat,
          tag, payload, h0, h1, h2, h3, h4, htag]

/-- Foundation's concrete Gödel encoding of propositional sentences is primitive-recursive.
This is an encoding theorem only; it contains no semantic or logical-inductor premise. -/
instance sentencePrimcodable : Primcodable Sentence where
  prim := by
    have hstep : Primrec₂ (fun (_ : Unit) (prior : List ℕ) =>
        some (formulaNormList prior)) :=
      Primrec₂.option_some_iff.mpr (formulaNormList_prim.comp Primrec₂.right)
    have hrec := Primrec.nat_strong_rec
      (fun (_ : Unit) n => sentenceDecodeNorm n)
      hstep (fun _ n => by simpa using congrArg some (formulaNormList_history n))
    exact Primrec.nat_iff.mp ((hrec.comp (Primrec.const ()) Primrec.id).of_eq fun n => by
      change sentenceDecodeNorm n = Encodable.encode
        ((@LO.Propositional.Formula.ofNat ℕ inferInstance n) : Option Sentence)
      cases h : (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) <;>
        simp [sentenceDecodeNorm, h, LO.Propositional.Formula.instEncodable,
          LO.Propositional.Formula.toNat])

/-! ## Primitive-recursive normalization of the concrete `EF` decoder -/

private def intCodeNatAbs (n : ℕ) : ℕ :=
  if n.bodd then n.div2 + 1 else n.div2

private theorem intCodeNatAbs_prim : Primrec intCodeNatAbs := by
  exact (Primrec.cond Primrec.nat_bodd
    (Primrec.nat_add.comp Primrec.nat_div2 (Primrec.const 1))
    Primrec.nat_div2).of_eq fun n => by
      simp only [intCodeNatAbs]
      cases n.bodd <;> rfl

private theorem intCodeNatAbs_eq_decode (n : ℕ) :
    intCodeNatAbs n =
      ((@Encodable.decode ℤ Int.encodable n).getD 0).natAbs := by
  have hof : Denumerable.ofNat ℤ n = Equiv.intEquivNat.symm n := by
    apply Denumerable.ofNat_of_decode
    rfl
  simp [intCodeNatAbs, Int.encodable, hof, Equiv.intEquivNat,
    Equiv.intEquivNatSumNat, Equiv.natSumNatEquivNat,
    Equiv.boolProdNatEquivNat, Nat.boddDiv2_eq]
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

private theorem coprimeBounded_iff (a b : ℕ) : coprimeBounded a b ↔ a.Coprime b := by
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
    simpa [h k hklt hka hkb]
  · intro h k _ hka hkb
    exact Nat.eq_one_of_dvd_coprimes h hka hkb

private theorem coprimeBounded_prim : PrimrecRel coprimeBounded := by
  have hdvd : PrimrecRel fun k a : ℕ => k ∣ a := by
    apply PrimrecPred.of_eq
      (Primrec.eq.comp
        (Primrec.nat_mod.comp (Primrec.snd : Primrec fun p : ℕ × ℕ => p.2)
          (Primrec.fst : Primrec fun p : ℕ × ℕ => p.1))
        (Primrec.const (α := ℕ × ℕ) 0))
    intro p
    rcases p with ⟨k, a⟩
    simp [Nat.dvd_iff_mod_eq_zero]
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

private theorem natDvd_prim : PrimrecRel fun k a : ℕ => k ∣ a := by
  apply PrimrecPred.of_eq
    (Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.snd : Primrec fun p : ℕ × ℕ => p.2)
        (Primrec.fst : Primrec fun p : ℕ × ℕ => p.1))
      (Primrec.const (α := ℕ × ℕ) 0))
  intro p
  rcases p with ⟨k, a⟩
  simp [Nat.dvd_iff_mod_eq_zero]

/-- Euclid's gcd, compiled as the greatest common divisor below the explicit `a+b`
bound.  This avoids relying on the kernel implementation of Euclid's recursion. -/
private theorem natGCD_prim : Primrec₂ Nat.gcd := by
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

private theorem ratCodeValid_prim : PrimrecPred ratCodeValid := by
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

private theorem ratDecodeNorm_prim : Primrec ratDecodeNorm := by
  exact (Primrec.ite ratCodeValid_prim
    (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
    (Primrec.const 0)).of_eq fun n => by simp only [ratDecodeNorm, id_eq]

private theorem ratDecodeNorm_eq (n : ℕ) :
    ratDecodeNorm n = Encodable.encode (@Encodable.decode ℚ inferInstance n) := by
  have hvalid : ratCodeValid n ↔
      0 < n.unpair.2 ∧
        (Denumerable.ofNat ℤ n.unpair.1).natAbs.Coprime n.unpair.2 := by
    simp [ratCodeValid, coprimeBounded_iff, intCodeNatAbs_eq_decode,
      Int.encodable]
  have hencodeInt (k : ℕ) : Equiv.intEquivNat (Denumerable.ofNat ℤ k) = k := by
    exact @Denumerable.encode_ofNat ℤ Denumerable.int k
  by_cases h : ratCodeValid n
  · have hc := hvalid.mp h
    simp [ratDecodeNorm, h, Rat.instEncodable, Encodable.decode_ofEquiv,
      Encodable.decode_sigma_val, Encodable.decodeSubtype, Subtype.encodable, hc.1, hc.2,
      Encodable.Subtype.encode_eq, Nat.pair_unpair]
    rw [dif_pos hc.2]
    simp [Rat.instEncodable, Encodable.encode_ofEquiv,
      Encodable.encode_sigma_val, Encodable.Subtype.encode_eq, Nat.pair_unpair]
    rw [hencodeInt]
    change n = Nat.pair n.unpair.1 n.unpair.2
    exact (Nat.pair_unpair n).symm
  · have hc := mt hvalid.mpr h
    simp [ratDecodeNorm, h, Rat.instEncodable, Encodable.decode_ofEquiv,
      Encodable.decode_sigma_val, Encodable.decodeSubtype, Subtype.encodable, hc]

/-- Mathlib's concrete reduced-numerator/positive-denominator rational encoding is
primitive-recursive.  Unlike the generic denumeration fallback, this is the same encoding
used by `EF.const` and by all external rational quote codes. -/
instance ratPrimcodable : Primcodable ℚ where
  prim := Primrec.nat_iff.mp (ratDecodeNorm_prim.of_eq ratDecodeNorm_eq)

private theorem ratNum_prim : Primrec Rat.num := by
  apply Primrec.encode_iff.mp
  exact (Primrec.fst.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun q => by
    simp only [encode_rat_eq, Nat.unpair_pair]

private theorem ratDen_prim : Primrec Rat.den := by
  exact (Primrec.snd.comp (Primrec.unpair.comp Primrec.encode)).of_eq fun q => by
    simp only [encode_rat_eq, Nat.unpair_pair]

private theorem intCodeNatAbs_encode (z : ℤ) :
    intCodeNatAbs (Encodable.encode z) = z.natAbs := by
  cases z with
  | ofNat n => simp [intCodeNatAbs, encode_int_natCast]
  | negSucc n =>
      have hencode : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl
      rw [hencode]
      simp [intCodeNatAbs]

private theorem intNatAbs_prim : Primrec Int.natAbs :=
  (intCodeNatAbs_prim.comp Primrec.encode).of_eq intCodeNatAbs_encode

/-! The concrete integer encoding alternates nonnegative and negative values.  Working at
the code level keeps the rational compiler independent of any opaque arithmetic oracle. -/

private def intCodeNeg (n : ℕ) : ℕ :=
  if n = 0 then 0 else bif n.bodd then n + 1 else n - 1

private theorem intCodeNeg_prim : Primrec intCodeNeg := by
  have hzero : PrimrecPred fun n : ℕ => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hodd : Primrec fun n : ℕ => bif n.bodd then n + 1 else n - 1 :=
    Primrec.cond Primrec.nat_bodd
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  exact (Primrec.ite hzero (Primrec.const 0) hodd).of_eq fun n => by
    simp only [intCodeNeg]

private theorem intCodeNeg_encode (z : ℤ) :
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
      simp [intCodeNeg, Nat.bodd_add, Nat.bodd_mul]
      omega

private theorem encodeIntNegNat {n : ℕ} (hn : 0 < n) :
    Encodable.encode (-((n : ℤ))) = 2 * n - 1 := by
  have h : -((n : ℤ)) = Int.negSucc (n - 1) := by omega
  rw [h, show Encodable.encode (Int.negSucc (n - 1)) = 2 * (n - 1) + 1 from rfl]
  omega

private theorem intNeg_prim : Primrec fun z : ℤ => -z :=
  Primrec.encode_iff.mp <|
    (intCodeNeg_prim.comp Primrec.encode).of_eq intCodeNeg_encode

/-- Encode the integer difference `positive - negative`, where both inputs are naturals. -/
private def intCodeSubNat (positive negative : ℕ) : ℕ :=
  if negative ≤ positive then 2 * (positive - negative)
  else 2 * (negative - positive) - 1

private theorem intCodeSubNat_prim : Primrec₂ intCodeSubNat := by
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

private theorem intCodeSubNat_eq (positive negative : ℕ) :
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

private theorem intCodeAdd_prim : Primrec₂ intCodeAdd := by
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

private theorem intCodeAdd_encode (a b : ℤ) :
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
          simp [intCodeAdd, intCodeSubNat_eq, Nat.bodd_add, Nat.bodd_mul,
            Nat.div2_bit0, Nat.div2_bit1]
  | negSucc a =>
      cases b with
      | ofNat b =>
          have hdiv : (1 + 2 * a).div2 = a := by
            simpa [Nat.add_comm] using Nat.div2_bit1 a
          change intCodeAdd (2 * a + 1) (2 * b) =
            Encodable.encode ((b : ℤ) - (a + 1 : ℕ))
          simp [intCodeAdd, intCodeSubNat_eq, add_comm, Nat.bodd_add,
            Nat.bodd_mul, Nat.div2_bit0, Nat.div2_bit1, hdiv]
      | negSucc b =>
          change intCodeAdd (2 * a + 1) (2 * b + 1) = 2 * (a + b + 1) + 1
          simp [intCodeAdd, Nat.bodd_add, Nat.bodd_mul]
          omega

private theorem intAdd_prim : Primrec₂ fun a b : ℤ => a + b := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeAdd_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq fun a b => intCodeAdd_encode a b

private def intCodeMul (a b : ℕ) : ℕ :=
  let magnitude := intCodeNatAbs a * intCodeNatAbs b
  if magnitude = 0 then 0
  else if a.bodd = b.bodd then 2 * magnitude else 2 * magnitude - 1

private theorem intCodeMul_prim : Primrec₂ intCodeMul := by
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

private theorem intCodeMul_encode (a b : ℤ) :
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
              simp [intCodeMul, intCodeNatAbs, Nat.bodd_add, Nat.bodd_mul,
                Nat.div2_bit0, Nat.div2_bit1]
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
              simp [intCodeMul, intCodeNatAbs, Nat.bodd_add, Nat.bodd_mul,
                Nat.div2_bit0, Nat.div2_bit1]
      | negSucc b =>
          rw [Int.negSucc_mul_negSucc]
          change intCodeMul (2 * a + 1) (2 * b + 1) =
            2 * ((a + 1) * (b + 1))
          simp [intCodeMul, intCodeNatAbs, Nat.bodd_add, Nat.bodd_mul,
            Nat.div2_bit1]

private theorem intMul_prim : Primrec₂ fun a b : ℤ => a * b := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeMul_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq fun a b => intCodeMul_encode a b

private theorem intOfNat_prim : Primrec fun n : ℕ => (n : ℤ) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq fun n => by
    simp only [encode_int_natCast, id_eq]

private def intCodeLE (a b : ℕ) : Prop :=
  if a.bodd then
    if b.bodd then b.div2 ≤ a.div2 else True
  else if b.bodd then False else a.div2 ≤ b.div2

private instance intCodeLEDecidable : DecidableRel intCodeLE :=
  fun a b => by dsimp [intCodeLE]; infer_instance

private theorem intCodeLE_prim : PrimrecRel intCodeLE := by
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

private theorem intCodeLE_encode (a b : ℤ) :
    intCodeLE (Encodable.encode a) (Encodable.encode b) ↔ a ≤ b := by
  cases a with
  | ofNat a =>
      cases b with
      | ofNat b =>
          change intCodeLE (2 * a) (2 * b) ↔ Int.ofNat a ≤ Int.ofNat b
          simp [intCodeLE, Nat.bodd_mul, Nat.div2_bit0]
      | negSucc b =>
          change intCodeLE (2 * a) (2 * b + 1) ↔ Int.ofNat a ≤ Int.negSucc b
          simp [intCodeLE, Nat.bodd_add, Nat.bodd_mul]
          omega
  | negSucc a =>
      cases b with
      | ofNat b =>
          change intCodeLE (2 * a + 1) (2 * b) ↔ Int.negSucc a ≤ Int.ofNat b
          simp [intCodeLE, Nat.bodd_add, Nat.bodd_mul]
          omega
      | negSucc b =>
          change intCodeLE (2 * a + 1) (2 * b + 1) ↔
            Int.negSucc a ≤ Int.negSucc b
          simp [intCodeLE, Nat.bodd_add, Nat.bodd_mul, Nat.div2_bit1]
          omega

private theorem intLE_prim : PrimrecRel fun a b : ℤ => a ≤ b := by
  exact (intCodeLE_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq intCodeLE_encode

private def intCodeSign (zCode : ℕ) : ℕ :=
  if zCode = 0 then 0 else if zCode.bodd then 1 else 2

private theorem intCodeSign_prim : Primrec intCodeSign := by
  have hz : PrimrecPred fun n : ℕ => n = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hodd : PrimrecPred fun n : ℕ => n.bodd = true :=
    Primrec.eq.comp Primrec.nat_bodd (Primrec.const true)
  exact (Primrec.ite hz (Primrec.const 0)
    (Primrec.ite hodd (Primrec.const 1) (Primrec.const 2))).of_eq fun n => by
      simp only [intCodeSign]

private theorem intCodeSign_encode (z : ℤ) :
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
      simp [intCodeSign, Nat.bodd_add, Nat.bodd_mul]

private theorem intSign_prim : Primrec Int.sign := by
  apply Primrec.encode_iff.mp
  exact (intCodeSign_prim.comp Primrec.encode).of_eq intCodeSign_encode

private def intCodeDivNat (zCode d : ℕ) : ℕ :=
  if d = 0 then 0
  else if zCode.bodd then 2 * (zCode.div2 / d) + 1
  else 2 * (zCode.div2 / d)

private theorem intCodeDivNat_prim : Primrec₂ intCodeDivNat := by
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

private theorem intCodeDivNat_encode (z : ℤ) (d : ℕ) :
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
          simp [intCodeDivNat, Nat.bodd_add, Nat.bodd_mul, Nat.div2_bit1]

private theorem intDivNat_prim : Primrec₂ fun z : ℤ => fun d : ℕ => z / (d : ℤ) := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeDivNat_prim.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
    Primrec₂.right).of_eq intCodeDivNat_encode

private theorem ratNumNatAbs_prim : Primrec fun q : ℚ => q.num.natAbs :=
  intNatAbs_prim.comp ratNum_prim

/-- Rational comparison is primitive recursive in the repository's canonical encoding. -/
theorem ratLE_prim : PrimrecRel fun q r : ℚ => q ≤ r := by
  have hleft : Primrec₂ fun q r : ℚ => q.num * (r.den : ℤ) :=
    intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.left)
      ((intOfNat_prim.comp ratDen_prim).comp₂ Primrec₂.right)
  have hright : Primrec₂ fun q r : ℚ => r.num * (q.den : ℤ) :=
    intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.right)
      ((intOfNat_prim.comp ratDen_prim).comp₂ Primrec₂.left)
  exact (intLE_prim.comp₂ hleft hright).of_eq fun q r => by
    exact (Rat.le_iff q r).symm

private def ratMkCode (z : ℤ) (d : ℕ) : ℕ :=
  if d = 0 then Nat.pair 0 1
  else
    let g := Nat.gcd z.natAbs d
    Nat.pair (Encodable.encode (z / (g : ℤ))) (d / g)

private theorem ratMkCode_prim : Primrec₂ ratMkCode := by
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
    fun z d => by simp only [ratMkCode, g]

private theorem ratMkCode_eq (z : ℤ) (d : ℕ) :
    ratMkCode z d = Encodable.encode (mkRat z d) := by
  by_cases hd : d = 0
  · subst d
    rw [show mkRat z 0 = (0 : ℚ) by simp [mkRat], encode_rat_eq]
    change Nat.pair 0 1 = Nat.pair (Encodable.encode (0 : ℤ)) 1
    rw [show Encodable.encode (0 : ℤ) = 0 from rfl]
  · rw [encode_rat_eq, Rat.num_mkRat, Rat.den_mkRat]
    simp [ratMkCode, hd, Nat.gcd_comm]

private theorem ratMk_prim : Primrec₂ mkRat := by
  apply Primrec₂.encode_iff.mp
  exact ratMkCode_prim.of_eq ratMkCode_eq

private theorem ratNeg_prim : Primrec fun q : ℚ => -q := by
  apply Primrec.encode_iff.mp
  have hpair : Primrec fun q : ℚ =>
      Nat.pair (Encodable.encode (-q.num)) q.den :=
    Primrec₂.natPair.comp (Primrec.encode.comp (intNeg_prim.comp ratNum_prim))
      ratDen_prim
  exact hpair.of_eq fun q => by
    simp [encode_rat_eq, Rat.neg_num, Rat.neg_den]

theorem ratAdd_prim : Primrec₂ fun q r : ℚ => q + r := by
  have hqd : Primrec₂ fun q r : ℚ => q.num * (r.den : ℤ) :=
    intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.left)
      ((intOfNat_prim.comp ratDen_prim).comp₂ Primrec₂.right)
  have hrd : Primrec₂ fun q r : ℚ => r.num * (q.den : ℤ) :=
    intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.right)
      ((intOfNat_prim.comp ratDen_prim).comp₂ Primrec₂.left)
  have hnum : Primrec₂ fun q r : ℚ => q.num * (r.den : ℤ) + r.num * (q.den : ℤ) :=
    intAdd_prim.comp₂ hqd hrd
  have hden : Primrec₂ fun q r : ℚ => q.den * r.den :=
    Primrec.nat_mul.comp₂ (ratDen_prim.comp₂ Primrec₂.left)
      (ratDen_prim.comp₂ Primrec₂.right)
  exact (ratMk_prim.comp₂ hnum hden).of_eq fun q r => (Rat.add_def' q r).symm

theorem ratMul_prim : Primrec₂ fun q r : ℚ => q * r := by
  have hnum : Primrec₂ fun q r : ℚ => q.num * r.num :=
    intMul_prim.comp₂ (ratNum_prim.comp₂ Primrec₂.left)
      (ratNum_prim.comp₂ Primrec₂.right)
  have hden : Primrec₂ fun q r : ℚ => q.den * r.den :=
    Primrec.nat_mul.comp₂ (ratDen_prim.comp₂ Primrec₂.left)
      (ratDen_prim.comp₂ Primrec₂.right)
  exact (ratMk_prim.comp₂ hnum hden).of_eq fun q r => (Rat.mul_def' q r).symm

private theorem ratSub_prim : Primrec₂ fun q r : ℚ => q - r := by
  exact (ratAdd_prim.comp₂ Primrec₂.left
    (ratNeg_prim.comp₂ Primrec₂.right)).of_eq fun q r => by simp [sub_eq_add_neg]

private theorem ratInv_prim : Primrec fun q : ℚ => q⁻¹ := by
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

/-- Exact rational division is primitive recursive in the canonical encoding. -/
theorem ratDiv_prim : Primrec₂ fun q r : ℚ => q / r := by
  exact (ratMul_prim.comp₂ Primrec₂.left
    (ratInv_prim.comp₂ Primrec₂.right)).of_eq fun q r => by simp [div_eq_mul_inv]

private theorem ratPow_prim : Primrec₂ fun q : ℚ => fun n : ℕ => q ^ n := by
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

/-! ## Proof-erased finite rational belief states -/

private theorem sentenceListNodup_prim :
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

private theorem beliefEntryListKeys_prim :
    Primrec fun entries : List (Sentence × ℚ) => entries.map Prod.fst := by
  exact Primrec.list_map Primrec.id
    (Primrec.fst.comp₂ Primrec₂.right)

private theorem beliefEntryBounded_prim :
    PrimrecPred fun p : Sentence × ℚ => 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  have hlo : PrimrecPred fun p : Sentence × ℚ => 0 ≤ p.2 :=
    ratLE_prim.comp (Primrec.const 0) Primrec.snd
  have hhi : PrimrecPred fun p : Sentence × ℚ => p.2 ≤ 1 :=
    ratLE_prim.comp Primrec.snd (Primrec.const 1)
  exact hlo.and hhi

private theorem beliefEntriesBounded_prim :
    PrimrecPred fun entries : List (Sentence × ℚ) =>
      ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1 :=
  beliefEntryBounded_prim.forall_mem_list

private theorem beliefEntriesValid_prim :
    PrimrecPred fun entries : List (Sentence × ℚ) =>
      (entries.map Prod.fst).Nodup ∧
        ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1 :=
  (sentenceListNodup_prim.comp beliefEntryListKeys_prim).and beliefEntriesBounded_prim

private def beliefEntriesNorm (entries : List (Sentence × ℚ)) : ℕ :=
  if (entries.map Prod.fst).Nodup ∧
      (∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1) then
    Encodable.encode entries + 1
  else 0

private theorem beliefEntriesNorm_prim : Primrec beliefEntriesNorm := by
  exact (Primrec.ite beliefEntriesValid_prim
    (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
    (Primrec.const 0)).of_eq fun entries => by simp only [beliefEntriesNorm]

/-- The encoding of a rational belief state erases its proof fields and stores exactly its
validated finite association list. -/
instance rationalBeliefStateEncodable : Encodable RationalBeliefState :=
  Encodable.ofLeftInjection RationalBeliefState.entries
    RationalBeliefState.ofEntries? RationalBeliefState.ofEntries?_self

private theorem beliefEntriesNorm_eq (entries : List (Sentence × ℚ)) :
    beliefEntriesNorm entries =
      Encodable.encode (RationalBeliefState.ofEntries? entries) := by
  by_cases hn : (entries.map Prod.fst).Nodup
  · by_cases hb : ∀ p ∈ entries, 0 ≤ p.2 ∧ p.2 ≤ 1
    · let B : RationalBeliefState := ⟨entries, hn, hb⟩
      have hof : RationalBeliefState.ofEntries? entries = some B := by
        simpa [B] using RationalBeliefState.ofEntries?_self B
      rw [beliefEntriesNorm, if_pos ⟨hn, hb⟩, hof]
      rfl
    · have hof : RationalBeliefState.ofEntries? entries = none := by
        rw [RationalBeliefState.ofEntries?, dif_pos hn, dif_neg hb]
      rw [beliefEntriesNorm, if_neg (by tauto), hof]
      rfl
  · have hof : RationalBeliefState.ofEntries? entries = none := by
      simp [RationalBeliefState.ofEntries?, hn]
    rw [beliefEntriesNorm, if_neg (by tauto), hof]
    rfl

/-- Normalize a raw natural-number candidate to the exact code of the validated belief
state decoded by `rationalBeliefStateEncodable`. -/
private def beliefStateDecodeNorm (n : ℕ) : ℕ :=
  match Encodable.decode (α := List (Sentence × ℚ)) n with
  | none => 0
  | some entries => beliefEntriesNorm entries

private theorem beliefStateDecodeNorm_prim : Primrec beliefStateDecodeNorm := by
  exact (Primrec.option_casesOn
    (Primrec.decode : Primrec fun n : ℕ =>
      Encodable.decode (α := List (Sentence × ℚ)) n)
    (Primrec.const 0)
    (beliefEntriesNorm_prim.comp₂ Primrec₂.right)).of_eq fun n => by
      cases h : Encodable.decode (α := List (Sentence × ℚ)) n <;>
        simp [beliefStateDecodeNorm, h]

private theorem beliefStateDecodeNorm_eq (n : ℕ) :
    beliefStateDecodeNorm n =
      Encodable.encode
        (@Encodable.decode RationalBeliefState rationalBeliefStateEncodable n) := by
  change beliefStateDecodeNorm n = Encodable.encode
    ((Encodable.decode (α := List (Sentence × ℚ)) n).bind
      RationalBeliefState.ofEntries?)
  cases h : Encodable.decode (α := List (Sentence × ℚ)) n with
  | none => simp [beliefStateDecodeNorm, h]
  | some entries => simp [beliefStateDecodeNorm, h, beliefEntriesNorm_eq]

/-- The validated finite-state representation used by MarketMaker is primitive-recursive;
its proof fields carry no runtime information. -/
instance rationalBeliefStatePrimcodable : Primcodable RationalBeliefState where
  prim := Primrec.nat_iff.mp
    (beliefStateDecodeNorm_prim.of_eq beliefStateDecodeNorm_eq)

private theorem sentenceDecodeNorm_prim : Primrec sentenceDecodeNorm := by
  apply Primrec.nat_iff.mpr
  exact (Primcodable.prim Sentence).of_eq fun n => by
    change Encodable.encode
        ((@LO.Propositional.Formula.ofNat ℕ inferInstance n) : Option Sentence) =
      sentenceDecodeNorm n
    cases h : (@LO.Propositional.Formula.ofNat ℕ inferInstance n : Option Sentence) <;>
      simp [sentenceDecodeNorm, h, LO.Propositional.Formula.instEncodable]

/-- Lift one normalized child code through an `EF` unary constructor. -/
private def efUnaryNorm (tag childNorm : ℕ) : ℕ :=
  if childNorm = 0 then 0 else Nat.pair tag (childNorm - 1) + 1

private theorem efUnaryNorm_prim (tag : ℕ) : Primrec (efUnaryNorm tag) := by
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

private theorem efBinaryNorm_prim (tag : ℕ) : Primrec₂ (efBinaryNorm tag) := by
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

private theorem efPriceNorm_prim : Primrec₂ efPriceNorm := by
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

private theorem efPriorNorm_prim : Primrec₂ efPriorNorm := by
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

private theorem efDecodeNormStep_prim : Primrec efDecodeNormStep := by
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
  have h7 : Primrec fun prior : List ℕ =>
      if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 7) (hbinary 7) (Primrec.const 0)
  have h6 : Primrec fun prior : List ℕ =>
      if tag prior = 6 then Nat.pair 6 (payload prior) + 1
      else if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 6) hvar h7
  have h5 : Primrec fun prior : List ℕ =>
      if tag prior = 5 then efUnaryNorm 5 (efPriorNorm prior (payload prior))
      else if tag prior = 6 then Nat.pair 6 (payload prior) + 1
      else if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 5) hunary h6
  have h4 : Primrec fun prior : List ℕ =>
      if tag prior = 4 then
        efBinaryNorm 4 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efUnaryNorm 5 (efPriorNorm prior (payload prior))
      else if tag prior = 6 then Nat.pair 6 (payload prior) + 1
      else if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 4) (hbinary 4) h5
  have h3 : Primrec fun prior : List ℕ =>
      if tag prior = 3 then
        efBinaryNorm 3 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efBinaryNorm 4 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efUnaryNorm 5 (efPriorNorm prior (payload prior))
      else if tag prior = 6 then Nat.pair 6 (payload prior) + 1
      else if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 3) (hbinary 3) h4
  have h2 : Primrec fun prior : List ℕ =>
      if tag prior = 2 then
        efBinaryNorm 2 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 3 then
        efBinaryNorm 3 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efBinaryNorm 4 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efUnaryNorm 5 (efPriorNorm prior (payload prior))
      else if tag prior = 6 then Nat.pair 6 (payload prior) + 1
      else if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 2) (hbinary 2) h3
  have h1 : Primrec fun prior : List ℕ =>
      if tag prior = 1 then
        efPriceNorm (sentenceDecodeNorm (payload prior).unpair.1) (payload prior).unpair.2
      else if tag prior = 2 then
        efBinaryNorm 2 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 3 then
        efBinaryNorm 3 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efBinaryNorm 4 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efUnaryNorm 5 (efPriorNorm prior (payload prior))
      else if tag prior = 6 then Nat.pair 6 (payload prior) + 1
      else if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 1) hprice h2
  have h0 : Primrec fun prior : List ℕ =>
      if tag prior = 0 then efUnaryNorm 0 (ratDecodeNorm (payload prior))
      else if tag prior = 1 then
        efPriceNorm (sentenceDecodeNorm (payload prior).unpair.1) (payload prior).unpair.2
      else if tag prior = 2 then
        efBinaryNorm 2 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 3 then
        efBinaryNorm 3 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efBinaryNorm 4 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efUnaryNorm 5 (efPriorNorm prior (payload prior))
      else if tag prior = 6 then Nat.pair 6 (payload prior) + 1
      else if tag prior = 7 then
        efBinaryNorm 7 (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 0) hconst h1
  exact (Primrec.ite hfuelZero (Primrec.const 0) h0).of_eq fun prior => by
    simp only [efDecodeNormStep, code, fuel, tag, payload]

private def efAuxNormIndex (n : ℕ) : ℕ :=
  Encodable.encode (EF.ofNatAux n.unpair.2 n.unpair.1)

private theorem efHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map efAuxNormIndex).getD k 0 = efAuxNormIndex k := by
  have hzero : efAuxNormIndex 0 = 0 := by
    simp [efAuxNormIndex, EF.ofNatAux]
  rw [← hzero, List.getD_map]
  simp [hk]

theorem efChildPair_lt (child code fuel : ℕ) (hchild : child ≤ code) :
    Nat.pair child fuel < Nat.pair code (fuel + 1) := by
  rcases hchild.eq_or_lt with heq | hlt
  · subst code
    exact Nat.pair_lt_pair_right child (by omega)
  · exact (Nat.pair_lt_pair_left fuel hlt).trans
      (Nat.pair_lt_pair_right code (by omega))

private theorem efDecodeNormStep_history (n : ℕ) :
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
          ratDecodeNorm_eq, hq, efUnaryNorm, EF.instEncodable, EF.toNat]
      · rcases tag with _ | tag
        · cases hs : (@LO.Propositional.Formula.ofNat ℕ inferInstance
              code.unpair.2.unpair.1 : Option Sentence)
          <;> simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
            sentenceDecodeNorm, hs, efPriceNorm, EF.instEncodable, EF.toNat,
            LO.Propositional.Formula.instEncodable]
        · rcases tag with _ | tag
          · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
              cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
              simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                hprior _ hleft, hprior _ hright, efBinaryNorm,
                EF.instEncodable, EF.toNat, hL, hR]
          · rcases tag with _ | tag
            · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                  hprior _ hleft, hprior _ hright, efBinaryNorm,
                  EF.instEncodable, EF.toNat, hL, hR]
            · rcases tag with _ | tag
              · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                  cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                  simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                    hprior _ hleft, hprior _ hright, efBinaryNorm,
                    EF.instEncodable, EF.toNat, hL, hR]
              · rcases tag with _ | tag
                · cases hA : EF.ofNatAux fuel code.unpair.2 <;>
                    simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                      hprior _ hpayload, efUnaryNorm, EF.instEncodable,
                      EF.toNat, hA]
                · rcases tag with _ | tag
                  · simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                      EF.instEncodable, EF.toNat]
                  · rcases tag with _ | tag
                    · cases hL : EF.ofNatAux fuel code.unpair.2.unpair.1 <;>
                        cases hR : EF.ofNatAux fuel code.unpair.2.unpair.2 <;>
                        simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag,
                          hprior _ hleft, hprior _ hright, efBinaryNorm,
                          EF.instEncodable, EF.toNat, hL, hR]
                    · simp [efDecodeNormStep, efAuxNormIndex, EF.ofNatAux, htag]

private theorem efAuxNormIndex_prim : Primrec efAuxNormIndex := by
  have hstep : Primrec₂ (fun (_ : Unit) (prior : List ℕ) =>
      some (efDecodeNormStep prior)) :=
    Primrec₂.option_some_iff.mpr (efDecodeNormStep_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec
    (fun (_ : Unit) n => efAuxNormIndex n)
    hstep (fun _ n => by simpa using congrArg some (efDecodeNormStep_history n))
  exact hrec.comp (Primrec.const ()) Primrec.id

/-- The project’s concrete `EF.toNat` / `EF.ofNat` encoding is primitive-recursive.
This instance is proved from the exact decoder, including every failure branch. -/
instance efPrimcodable : Primcodable EF where
  prim := by
    have hindex : Primrec fun n : ℕ => Nat.pair n (n + 1) :=
      Primrec₂.natPair.comp Primrec.id
        (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
    exact Primrec.nat_iff.mp ((efAuxNormIndex_prim.comp hindex).of_eq fun n => by
      simp [efAuxNormIndex, EF.ofNat, EF.instEncodable])

/-! ## Primitive-recursive strategy validation -/

/-- A normalized rank result uses `0` for decoder failure and `rank + 1` for success. -/
private def efRankBinaryNorm (left right : ℕ) : ℕ :=
  if left = 0 ∨ right = 0 then 0 else Nat.max left right

private theorem efRankBinaryNorm_prim : Primrec₂ efRankBinaryNorm := by
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

private theorem efRankNormStep_prim : Primrec efRankNormStep := by
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
  have h7 : Primrec fun prior : List ℕ =>
      if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 7) hbinary (Primrec.const 0)
  have h6 : Primrec fun prior : List ℕ =>
      if tag prior = 6 then 1
      else if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 6) (Primrec.const 1) h7
  have h5 : Primrec fun prior : List ℕ =>
      if tag prior = 5 then efPriorNorm prior (payload prior)
      else if tag prior = 6 then 1
      else if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 5) hpriorPayload h6
  have h4 : Primrec fun prior : List ℕ =>
      if tag prior = 4 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efPriorNorm prior (payload prior)
      else if tag prior = 6 then 1
      else if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 4) hbinary h5
  have h3 : Primrec fun prior : List ℕ =>
      if tag prior = 3 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efPriorNorm prior (payload prior)
      else if tag prior = 6 then 1
      else if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 3) hbinary h4
  have h2 : Primrec fun prior : List ℕ =>
      if tag prior = 2 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 3 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efPriorNorm prior (payload prior)
      else if tag prior = 6 then 1
      else if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 2) hbinary h3
  have h1 : Primrec fun prior : List ℕ =>
      if tag prior = 1 then
        (if sentenceDecodeNorm (payload prior).unpair.1 = 0 then 0
         else (payload prior).unpair.2 + 1)
      else if tag prior = 2 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 3 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efPriorNorm prior (payload prior)
      else if tag prior = 6 then 1
      else if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 1) hprice h2
  have h0 : Primrec fun prior : List ℕ =>
      if tag prior = 0 then
        (if ratDecodeNorm (payload prior) = 0 then 0 else 1)
      else if tag prior = 1 then
        (if sentenceDecodeNorm (payload prior).unpair.1 = 0 then 0
         else (payload prior).unpair.2 + 1)
      else if tag prior = 2 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 3 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 4 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else if tag prior = 5 then efPriorNorm prior (payload prior)
      else if tag prior = 6 then 1
      else if tag prior = 7 then
        efRankBinaryNorm (efPriorNorm prior (payload prior).unpair.1)
          (efPriorNorm prior (payload prior).unpair.2)
      else 0 := Primrec.ite (htagEq 0) hconst h1
  exact (Primrec.ite hfuelZero (Primrec.const 0) h0).of_eq fun prior => by
    simp only [efRankNormStep, code, fuel, tag, payload]

private def efAuxRankNormIndex (n : ℕ) : ℕ :=
  match EF.ofNatAux n.unpair.2 n.unpair.1 with
  | none => 0
  | some e => e.rank + 1

private theorem efRankHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map efAuxRankNormIndex).getD k 0 = efAuxRankNormIndex k := by
  have hzero : efAuxRankNormIndex 0 = 0 := by
    simp [efAuxRankNormIndex, EF.ofNatAux]
  rw [← hzero, List.getD_map]
  simp [hk]

private theorem efRankNormStep_history (n : ℕ) :
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
              sentenceDecodeNorm, hs, LO.Propositional.Formula.instEncodable]
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

private theorem efAuxRankNormIndex_prim : Primrec efAuxRankNormIndex := by
  have hstep : Primrec₂ (fun (_ : Unit) (prior : List ℕ) =>
      some (efRankNormStep prior)) :=
    Primrec₂.option_some_iff.mpr (efRankNormStep_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec
    (fun (_ : Unit) n => efAuxRankNormIndex n)
    hstep (fun _ n => by simpa using congrArg some (efRankNormStep_history n))
  exact hrec.comp (Primrec.const ()) Primrec.id

private theorem efRank_prim : Primrec EF.rank := by
  have hindex : Primrec fun e : EF => Nat.pair (Encodable.encode e)
      (Encodable.encode e + 1) :=
    Primrec₂.natPair.comp Primrec.encode
      (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
  exact (Primrec.pred.comp (efAuxRankNormIndex_prim.comp hindex)).of_eq fun e => by
    simp [efAuxRankNormIndex, EF.instEncodable, EF.ofNatAux_toNat]

/-! ## Primitive-recursive `EF.priceQueries`

`EF.priceQueries` (`Criterion.lean`) lists the `(day, sentence)` market cells a feature
inspects.  Its primitive recursivity is the guard that keeps the total quote table `V`
(which substitutes `0` for an unanswered query) from silently certifying a false
settlement test: `EF.denoteRatWithAtFuel_complete` fires only once every listed query is
answered.  Compiled by course-of-values recursion on the Gödel code, exactly mirroring the
`EF.rank` compiler above, but carrying the list-valued result directly through
`Nat.strong_rec` (`σ := Option (List (ℕ × Sentence))`) rather than a normalized `ℕ`. -/

/-- Query-list values `List (ℕ × Sentence)`, tracked as `Option` (`none` = decoder
failure). -/
private abbrev EFQueryList := List (ℕ × Sentence)

/-- Append two query lists, propagating decoder failure. -/
private def efQueriesAppend (left right : Option EFQueryList) : Option EFQueryList :=
  left.bind fun a => right.map fun b => a ++ b

private theorem efQueriesAppend_prim : Primrec₂ efQueriesAppend := by
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

private theorem efPriorQueries_prim : Primrec₂ efPriorQueries := by
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

private theorem efQueriesNormVal_prim : Primrec efQueriesNormVal := by
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

private theorem efAuxQueriesVal_zero : efAuxQueriesVal 0 = none := by
  simp [efAuxQueriesVal, EF.ofNatAux]

private theorem efQueriesHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map efAuxQueriesVal).getD k none = efAuxQueriesVal k := by
  rw [← efAuxQueriesVal_zero, List.getD_map]
  simp [hk]

private theorem efQueriesNormVal_history (n : ℕ) :
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
              LO.Propositional.Formula.instEncodable]
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

private theorem efAuxQueriesVal_prim : Primrec efAuxQueriesVal := by
  have hstep : Primrec₂ (fun (_ : Unit) (prior : List (Option EFQueryList)) =>
      some (efQueriesNormVal prior)) :=
    Primrec₂.option_some_iff.mpr (efQueriesNormVal_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec
    (fun (_ : Unit) n => efAuxQueriesVal n)
    hstep (fun _ n => by simpa using congrArg some (efQueriesNormVal_history n))
  exact hrec.comp (Primrec.const ()) Primrec.id

/-- `EF.priceQueries` is primitive recursive.  The guard behind the settlement checker's
soundness: only when every listed query is answered does the total quote table stand in
for the real market. -/
theorem efPriceQueries_prim : Primrec EF.priceQueries := by
  have hindex : Primrec fun e : EF => Nat.pair (Encodable.encode e)
      (Encodable.encode e + 1) :=
    Primrec₂.natPair.comp Primrec.encode
      (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
  exact (Primrec.option_getD.comp (efAuxQueriesVal_prim.comp hindex)
    (Primrec.const ([] : EFQueryList))).of_eq fun e => by
      simp [efAuxQueriesVal, EF.instEncodable, EF.ofNatAux_toNat]

private def strategyOfTrades? (n : ℕ) (trades : List (EF × Sentence)) :
    Option (Strategy n) :=
  if h : ∀ p ∈ trades, p.1.rank ≤ n then some ⟨trades, h⟩ else none

private theorem strategyOfTrades?_self {n : ℕ} (T : Strategy n) :
    strategyOfTrades? n T.trades = some T := by
  simp only [strategyOfTrades?, dif_pos T.rank_le]

/-- A strategy is encoded by exactly its finite trade list; its day-rank proof is erased
and revalidated by the decoder. -/
instance strategyEncodable (n : ℕ) : Encodable (Strategy n) :=
  Encodable.ofLeftInjection Strategy.trades (strategyOfTrades? n)
    strategyOfTrades?_self

private theorem strategyTradesValid_prim (n : ℕ) :
    PrimrecPred fun trades : List (EF × Sentence) =>
      ∀ p ∈ trades, p.1.rank ≤ n := by
  have hp : PrimrecPred fun p : EF × Sentence => p.1.rank ≤ n :=
    Primrec.nat_le.comp (efRank_prim.comp Primrec.fst) (Primrec.const n)
  exact hp.forall_mem_list

private def strategyTradesNorm (n : ℕ) (trades : List (EF × Sentence)) : ℕ :=
  if ∀ p ∈ trades, p.1.rank ≤ n then Encodable.encode trades + 1 else 0

private theorem strategyTradesNorm_prim (n : ℕ) :
    Primrec (strategyTradesNorm n) := by
  exact (Primrec.ite (strategyTradesValid_prim n)
    (Primrec.nat_add.comp Primrec.encode (Primrec.const 1))
    (Primrec.const 0)).of_eq fun trades => by simp only [strategyTradesNorm]

private theorem strategyTradesNorm_eq (n : ℕ) (trades : List (EF × Sentence)) :
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

private theorem strategyDecodeNorm_prim (n : ℕ) :
    Primrec (strategyDecodeNorm n) := by
  exact (Primrec.option_casesOn
    (Primrec.decode : Primrec fun code : ℕ =>
      Encodable.decode (α := List (EF × Sentence)) code)
    (Primrec.const 0)
    ((strategyTradesNorm_prim n).comp₂ Primrec₂.right)).of_eq fun code => by
      cases h : Encodable.decode (α := List (EF × Sentence)) code <;>
        simp [strategyDecodeNorm, h]

private theorem strategyDecodeNorm_eq (n code : ℕ) :
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

/-! ## Exact finite-state accessors -/

/-- Association-list quotation is primitive recursive.  `List.lookup` has exactly the
first-key-wins behavior used by `quoteFromEntries`. -/
private theorem quoteFromEntries_prim : Primrec₂ quoteFromEntries := by
  have hlookup : Primrec₂ fun entries : List (Sentence × ℚ) => fun φ =>
      entries.lookup φ := Primrec₂.swap Primrec.listLookup
  exact (Primrec.option_getD.comp₂ hlookup (Primrec₂.const 0)).of_eq fun entries φ => by
    induction entries with
    | nil => rfl
    | cons entry entries ih =>
        rcases entry with ⟨ψ, q⟩
        simp only [quoteFromEntries, List.lookup]
        split <;> simp_all

/-- Quoting a proof-erased rational belief state is primitive recursive. -/
private theorem rationalBeliefStateEntries_prim :
    Primrec RationalBeliefState.entries := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec fun B : RationalBeliefState =>
    Encodable.encode B).of_eq fun B => by rfl

private theorem rationalBeliefStateQuote_prim :
    Primrec₂ RationalBeliefState.quote := by
  exact (quoteFromEntries_prim.comp₂
    (rationalBeliefStateEntries_prim.comp₂ Primrec₂.left)
    Primrec₂.right).of_eq fun B φ => by
    rfl

/-- The finite chronological rational history is primitive recursive in the state list,
day, and queried sentence. -/
private theorem rationalHistory_prim :
    Primrec fun p : (List RationalBeliefState × ℕ) × Sentence =>
      rationalHistory p.1.1 p.1.2 p.2 := by
  let stateAt : (List RationalBeliefState × ℕ) × Sentence →
      Option RationalBeliefState := fun p => p.1.1[p.1.2]?
  have hstateAt : Primrec stateAt :=
    Primrec.list_getElem?.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  have hquote : Primrec₂ fun
      (p : (List RationalBeliefState × ℕ) × Sentence)
      (B : RationalBeliefState) => B.quote p.2 :=
    rationalBeliefStateQuote_prim.comp₂ Primrec₂.right
      (Primrec.snd.comp₂ Primrec₂.left)
  exact (Primrec.option_casesOn hstateAt (Primrec.const 0)
    hquote).of_eq fun p => by
        rcases p with ⟨⟨past, day⟩, φ⟩
        cases h : past[day]? <;> simp [stateAt, rationalHistory, h]

/-- The candidate enumeration searched by MarketMaker is precisely the decoder of the
proof-erased belief-state representation, hence primitive recursive. -/
private theorem marketMakerCandidate_prim : Primrec marketMakerCandidate := by
  exact (Primrec.decode : Primrec fun k : ℕ =>
    Encodable.decode (α := RationalBeliefState) k).of_eq fun k => by rfl

/-! ## Exact finite-sentence-set encoding -/

/-- Comparison of sentence Gödel codes is primitive recursive. -/
theorem sentenceCodeLE_prim :
    PrimrecRel fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ :=
  Primrec.nat_le.comp₂
    (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)

/-- Insertion into the code-sorted sentence list is primitive recursive. -/
theorem sentenceOrderedInsert_prim :
    Primrec₂ (List.orderedInsert
      (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ)) := by
  let r : Sentence → Sentence → Prop := fun φ ψ =>
    Encodable.encode φ ≤ Encodable.encode ψ
  let base : Sentence × List Sentence → List Sentence := fun p => [p.1]
  let step : (Sentence × List Sentence) →
      (Sentence × List Sentence × List Sentence) → List Sentence :=
    fun p q => if r p.1 q.1 then p.1 :: q.1 :: q.2.1 else q.1 :: q.2.2
  have hbase : Primrec base :=
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])).of_eq fun p => by
      simp [base]
  have hpred : PrimrecPred fun x :
      (Sentence × List Sentence) ×
        (Sentence × List Sentence × List Sentence) =>
      r x.1.1 x.2.1 :=
    sentenceCodeLE_prim.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hthen : Primrec fun x :
      (Sentence × List Sentence) ×
        (Sentence × List Sentence × List Sentence) =>
      x.1.1 :: x.2.1 :: x.2.2.1 :=
    Primrec.list_cons.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have helse : Primrec fun x :
      (Sentence × List Sentence) ×
        (Sentence × List Sentence × List Sentence) =>
      x.2.1 :: x.2.2.2 :=
    Primrec.list_cons.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ step :=
    (Primrec.ite hpred hthen helse).to₂.of_eq fun p q => by
      simp only [step]
  exact (Primrec.list_rec Primrec.snd hbase hstep).to₂.of_eq fun φ l => by
    change List.recOn l [φ]
      (fun ψ tail ih => if Encodable.encode φ ≤ Encodable.encode ψ then
        φ :: ψ :: tail else ψ :: ih) =
      List.orderedInsert
        (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ) φ l
    induction l with
    | nil => rfl
    | cons ψ l ih => simp [List.orderedInsert, ih]

/-- The canonical insertion sort used below is primitive recursive. -/
theorem sentenceInsertionSort_prim :
    Primrec (List.insertionSort
      (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const [])
    (sentenceOrderedInsert_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun l => by
        rfl

private def sentenceFinsetDecodeNorm (n : ℕ) : ℕ :=
  match Encodable.decode (α := List Sentence) n with
  | none => 0
  | some l =>
      if l.Nodup then
        Encodable.encode (l.insertionSort
          (fun φ ψ : Sentence => Encodable.encode φ ≤ Encodable.encode ψ)) + 1
      else 0

private theorem sentenceFinsetDecodeNorm_prim :
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

private theorem sentenceMultisetDecode_eq (n : ℕ) :
    @Encodable.decode (Multiset Sentence) Multiset.encodable n =
      (Encodable.decode (α := List Sentence) n).map
        (fun l => (l : Multiset Sentence)) := by
  unfold Multiset.encodable
  unfold decodeMultiset
  cases h : Encodable.decode (α := List Sentence) n <;> simp [h]

private theorem sentenceFinsetEncode_eq (s : Finset Sentence) :
    @Encodable.encode (Finset Sentence) Finset.encodable s =
      encodeMultiset s.1 := by
  rfl

private theorem sentenceFinsetDecodeNorm_eq (n : ℕ) :
    sentenceFinsetDecodeNorm n =
      @Encodable.encode (Option (Finset Sentence)) Option.encodable
        (@Encodable.decode (Finset Sentence) Finset.encodable n) := by
  simp only [Finset.encodable, Encodable.decode_ofEquiv]
  change sentenceFinsetDecodeNorm n = Encodable.encode
    (Option.map
      (fun x : {s : Multiset Sentence // s.Nodup} =>
        ({ val := x.1, nodup := x.2 } : Finset Sentence))
      (@Encodable.decode {s : Multiset Sentence // s.Nodup}
        (@Subtype.encodable (Multiset Sentence) Multiset.Nodup
          Multiset.encodable
          (fun s => @Multiset.nodupDecidable Sentence
            (Encodable.decidableEqOfEncodable Sentence) s)) n))
  simp only [Subtype.encodable, Encodable.decodeSubtype]
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

/-- A fixed deductive-process program, run for a supplied clock, is primitive recursive in
the clock and requested day, including exact decoding of its finite sentence set. -/
theorem processStageAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ fun fuel n => process.stageAtFuel fuel n := by
  have heval : Primrec fun p : ℕ × ℕ =>
      Nat.Partrec.Code.evaln p.1 process.code p.2 :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.fst.pair (Primrec.const process.code)).pair Primrec.snd)
  have hdecode : Primrec fun out : ℕ =>
      Encodable.decode (α := Finset Sentence) out := Primrec.decode
  exact (Primrec.option_bind heval
    ((hdecode.comp Primrec.snd).to₂)).to₂.of_eq fun fuel n => by
      rfl

/-- A fixed market program, run for a supplied clock, is primitive recursive in the clock,
day and sentence, including exact decoding of its rational output. -/
theorem quoteAtFuel_prim {P : History} (market : MarketComputation P) :
    Primrec fun p : ℕ × ℕ × Sentence => market.quoteAtFuel p.1 p.2.1 p.2.2 := by
  have hz : Primrec fun p : ℕ × ℕ × Sentence =>
      Nat.pair p.2.1 (Encodable.encode p.2.2) :=
    Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))
  have heval : Primrec fun p : ℕ × ℕ × Sentence =>
      Nat.Partrec.Code.evaln p.1 market.code
        (Nat.pair p.2.1 (Encodable.encode p.2.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.fst.pair (Primrec.const market.code)).pair hz)
  have hdecode : Primrec fun out : ℕ =>
      Encodable.decode (α := ℚ) out := Primrec.decode
  exact (Primrec.option_bind heval
    ((hdecode.comp Primrec.snd).to₂)).of_eq fun p => rfl

/-- Decoding the entire finite deductive-stage prefix under one common clock is primitive
recursive. -/
private theorem processStagePrefixAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ fun fuel n => processStagePrefixAtFuel process fuel n := by
  have hbase : Primrec fun _fuel : ℕ =>
      (some [] : Option (List (Finset Sentence))) := Primrec.const (some [])
  have hstep : Primrec₂ fun fuel
      (ni : ℕ × Option (List (Finset Sentence))) =>
      ni.2.bind fun accumulated =>
        (process.stageAtFuel fuel ni.1).bind fun stage =>
          some (accumulated ++ [stage]) := by
    let X := ℕ × (ℕ × Option (List (Finset Sentence)))
    have hstage : Primrec fun x : X =>
        process.stageAtFuel x.1 x.2.1 :=
      processStageAtFuel_prim process |>.comp Primrec.fst
        (Primrec.fst.comp Primrec.snd)
    have hout : Primrec₂ fun
        (y : X × List (Finset Sentence)) (stage : Finset Sentence) =>
        some (y.2 ++ [stage]) :=
      Primrec₂.option_some_iff.mpr
        (Primrec.list_concat.comp₂
          (Primrec.snd.comp₂ Primrec₂.left)
          Primrec₂.right)
    have hinner : Primrec₂ fun (x : X)
        (accumulated : List (Finset Sentence)) =>
        (process.stageAtFuel x.1 x.2.1).bind fun stage =>
          some (accumulated ++ [stage]) := by
      exact (Primrec.option_bind
        (hstage.comp Primrec.fst) hout).to₂
    exact (Primrec.option_bind
      (Primrec.snd.comp Primrec.snd) hinner).to₂
  exact (Primrec.nat_rec hbase hstep).of_eq fun fuel n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [processStagePrefixAtFuel, ih]

/-- Lookup in a successfully decoded stage prefix, with the empty theory as the
out-of-range default, is primitive recursive. -/
private theorem decodedStageTable_prim : Primrec₂ decodedStageTable := by
  exact (Primrec.list_getD (∅ : Finset Sentence)).of_eq fun stages n => by
    rfl

/-! ## Uniform trader-program emulator -/

/-! The streaming strategy decoder constructs `EF` syntax directly.  Exposing these small
constructor facts separately keeps the parser proof about its control flow rather than the
details of the exact `EF.toNat` representation. -/

private theorem efConst_prim : Primrec EF.const := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp (Primrec.const 0) Primrec.encode).of_eq fun q => by
    rfl

private theorem efPrice_prim : Primrec₂ EF.price := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 1)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd)).to₂).of_eq
      fun φ n => by rfl

private theorem efAdd_prim : Primrec₂ EF.add := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun a b => by rfl

private theorem efMul_prim : Primrec₂ EF.mul := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 3)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun a b => by rfl

private theorem efMax_prim : Primrec₂ EF.max := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun a b => by rfl

private theorem efSafeRecip_prim : Primrec EF.safeRecip := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp (Primrec.const 5) Primrec.encode).of_eq fun a => by
    rfl

private theorem efVar_prim : Primrec EF.var := by
  apply Primrec.encode_iff.mp
  exact (Primrec₂.natPair.comp (Primrec.const 6) Primrec.id).of_eq fun i => by
    rfl

private theorem efLet_prim : Primrec₂ EF.letE := by
  apply Primrec₂.encode_iff.mp
  exact ((Primrec₂.natPair.comp (Primrec.const 7)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to₂).of_eq fun x body => by rfl

private def efStreamBinary (op : EF → EF → EF)
    (data : List EF × List (EF × Sentence)) : Option EF.StreamState :=
  match data.1 with
  | b :: a :: rest => some ((0, none), (op a b :: rest, data.2))
  | _ => none

private theorem efStreamBinary_prim (op : EF → EF → EF) (hop : Primrec₂ op) :
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

private theorem efStreamUnary_prim (op : EF → EF) (hop : Primrec op) :
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

private theorem efStreamMode_prim (mode : ℕ) : Primrec (efStreamMode mode) := by
  exact Primrec.option_some_iff.mpr
    ((Primrec.const (mode, (none : Option Sentence))).pair Primrec.id)

private def efStreamSentence
    (data : List EF × List (EF × Sentence)) (token : ℕ) :
    Option EF.StreamState :=
  (Encodable.decode (α := Sentence) token).map fun φ => ((2, some φ), data)

private theorem efStreamSentence_prim : Primrec₂ efStreamSentence := by
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

private theorem efStreamConst_prim : Primrec₂ efStreamConst := by
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

private theorem efStreamVar_prim : Primrec₂ efStreamVar := by
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

private theorem efStreamPrice_prim : Primrec efStreamPrice := by
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

private theorem efStreamTrade_prim : Primrec efStreamTrade := by
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

private theorem efStreamStepState_prim : Primrec fun
    input : EF.StreamState × ℕ => EF.streamStep (some input.1) input.2 := by
  let S := List EF × List (EF × Sentence)
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
  have h8 : Primrec fun p : P =>
      if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 8) (hbinary EF.letE efLet_prim)
      (Primrec.const (none : Option EF.StreamState))
  have h7 : Primrec fun p : P =>
      if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 7) (hsetMode 5) h8
  have h6 : Primrec fun p : P =>
      if p.2 = 6 then efStreamMode 4 p.1.2
      else if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 6) (hsetMode 4) h7
  have h5 : Primrec fun p : P =>
      if p.2 = 5 then efStreamUnary EF.safeRecip p.1.2
      else if p.2 = 6 then efStreamMode 4 p.1.2
      else if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 5) (hunary EF.safeRecip efSafeRecip_prim) h6
  have h4 : Primrec fun p : P =>
      if p.2 = 4 then efStreamBinary EF.max p.1.2
      else if p.2 = 5 then efStreamUnary EF.safeRecip p.1.2
      else if p.2 = 6 then efStreamMode 4 p.1.2
      else if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 4) (hbinary EF.max efMax_prim) h5
  have h3 : Primrec fun p : P =>
      if p.2 = 3 then efStreamBinary EF.mul p.1.2
      else if p.2 = 4 then efStreamBinary EF.max p.1.2
      else if p.2 = 5 then efStreamUnary EF.safeRecip p.1.2
      else if p.2 = 6 then efStreamMode 4 p.1.2
      else if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 3) (hbinary EF.mul efMul_prim) h4
  have h2 : Primrec fun p : P =>
      if p.2 = 2 then efStreamBinary EF.add p.1.2
      else if p.2 = 3 then efStreamBinary EF.mul p.1.2
      else if p.2 = 4 then efStreamBinary EF.max p.1.2
      else if p.2 = 5 then efStreamUnary EF.safeRecip p.1.2
      else if p.2 = 6 then efStreamMode 4 p.1.2
      else if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 2) (hbinary EF.add efAdd_prim) h3
  have h1 : Primrec fun p : P =>
      if p.2 = 1 then efStreamMode 3 p.1.2
      else if p.2 = 2 then efStreamBinary EF.add p.1.2
      else if p.2 = 3 then efStreamBinary EF.mul p.1.2
      else if p.2 = 4 then efStreamBinary EF.max p.1.2
      else if p.2 = 5 then efStreamUnary EF.safeRecip p.1.2
      else if p.2 = 6 then efStreamMode 4 p.1.2
      else if p.2 = 7 then efStreamMode 5 p.1.2
      else if p.2 = 8 then efStreamBinary EF.letE p.1.2 else none :=
    Primrec.ite (htokenEq 1) (hsetMode 3) h2
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
    Primrec.ite (htokenEq 0) (hsetMode 1) h1
  have hpriceInput : Primrec fun p : P => ((p.1.1.2, p.1.2), p.2) :=
    (hpending.pair hdata).pair htoken
  have htradeInput : Primrec fun p : P => (p.1.2, p.2) := hdata.pair htoken
  have hmode5 : Primrec fun p : P =>
      if p.1.1.1 = 5 then efStreamVar p.1.2 p.2 else none :=
    Primrec.ite (hmodeEq 5) (efStreamVar_prim.comp hdata htoken)
      (Primrec.const (none : Option EF.StreamState))
  have hmode4 : Primrec fun p : P =>
      if p.1.1.1 = 4 then efStreamTrade (p.1.2, p.2)
      else if p.1.1.1 = 5 then efStreamVar p.1.2 p.2 else none :=
    Primrec.ite (hmodeEq 4) (efStreamTrade_prim.comp htradeInput) hmode5
  have hmode3 : Primrec fun p : P =>
      if p.1.1.1 = 3 then efStreamConst p.1.2 p.2
      else if p.1.1.1 = 4 then efStreamTrade (p.1.2, p.2)
      else if p.1.1.1 = 5 then efStreamVar p.1.2 p.2 else none :=
    Primrec.ite (hmodeEq 3) (efStreamConst_prim.comp hdata htoken) hmode4
  have hmode2 : Primrec fun p : P =>
      if p.1.1.1 = 2 then efStreamPrice ((p.1.1.2, p.1.2), p.2)
      else if p.1.1.1 = 3 then efStreamConst p.1.2 p.2
      else if p.1.1.1 = 4 then efStreamTrade (p.1.2, p.2)
      else if p.1.1.1 = 5 then efStreamVar p.1.2 p.2 else none :=
    Primrec.ite (hmodeEq 2) (efStreamPrice_prim.comp hpriceInput) hmode3
  have hmode1 : Primrec fun p : P =>
      if p.1.1.1 = 1 then efStreamSentence p.1.2 p.2
      else if p.1.1.1 = 2 then efStreamPrice ((p.1.1.2, p.1.2), p.2)
      else if p.1.1.1 = 3 then efStreamConst p.1.2 p.2
      else if p.1.1.1 = 4 then efStreamTrade (p.1.2, p.2)
      else if p.1.1.1 = 5 then efStreamVar p.1.2 p.2 else none :=
    Primrec.ite (hmodeEq 1) (efStreamSentence_prim.comp hdata htoken) hmode2
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

private theorem efStreamStep_prim : Primrec₂ EF.streamStep := by
  let P := Option EF.StreamState × ℕ
  have hsome : Primrec₂ fun (p : P) (state : EF.StreamState) =>
      EF.streamStep (some state) p.2 := by
    have hinput : Primrec fun z : P × EF.StreamState => (z.2, z.1.2) :=
      Primrec.snd.pair (Primrec.snd.comp Primrec.fst)
    exact (efStreamStepState_prim.comp hinput).to₂
  exact ((Primrec.option_casesOn Primrec.fst
    (Primrec.const (none : Option EF.StreamState)) hsome).to₂).of_eq fun state token => by
      cases state <;> rfl

private theorem efStreamReadFrom_prim : Primrec₂ EF.streamReadFrom := by
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

private theorem efStreamFinish_prim : Primrec efStreamFinish := by
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

theorem deserializeTrades_prim : Primrec deserializeTrades := by
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

private theorem strategyTradesValid_prim₂ :
    PrimrecRel fun (trades : List (EF × Sentence)) n =>
      ∀ p ∈ trades, p.1.rank ≤ n := by
  have hp : PrimrecRel fun (p : EF × Sentence) n => p.1.rank ≤ n :=
    Primrec.nat_le.comp₂
      ((efRank_prim.comp Primrec.fst).comp₂ Primrec₂.left)
      Primrec₂.right
  exact hp.forall_mem_list

private theorem strategyOfTokensTrades_prim : Primrec₂ fun n tokens =>
    (strategyOfTokens n tokens).trades := by
  let P := ℕ × List ℕ
  have hdecode : Primrec fun p : P => deserializeTrades p.2 :=
    deserializeTrades_prim.comp Primrec.snd
  have hsome : Primrec₂ fun (p : P) (trades : List (EF × Sentence)) =>
      if ∀ trade ∈ trades, trade.1.rank ≤ p.1 then trades else [] := by
    have hvalid : PrimrecPred fun z : P × List (EF × Sentence) =>
        ∀ trade ∈ z.2, trade.1.rank ≤ z.1.1 :=
      PrimrecRel.comp strategyTradesValid_prim₂ Primrec.snd
        (Primrec.fst.comp Primrec.fst)
    exact (Primrec.ite hvalid Primrec.snd (Primrec.const [])).to₂
  exact ((Primrec.option_casesOn hdecode (Primrec.const []) hsome).to₂).of_eq
    fun n tokens => by
      simp only [Prod.snd]
      unfold strategyOfTokens
      split
      · simp_all
      · split <;> simp_all

/-- The token-indexed bounded emulator is primitive recursive uniformly in its two programs,
clock, and day. -/
private theorem clockedTokens_prim : Primrec fun
    p : ((Nat.Partrec.Code × Nat.Partrec.Code) × ℕ) × ℕ =>
      clockedTokens p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((Nat.Partrec.Code × Nat.Partrec.Code) × ℕ) × ℕ
  have hLengthCode : Primrec fun p : P => p.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hTokenCode : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hClock : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hDay : Primrec fun p : P => p.2 := Primrec.snd
  have hLengthEval : Primrec fun p : P =>
      Nat.Partrec.Code.evaln p.1.2 p.1.1.1 p.2 :=
    Nat.Partrec.Code.primrec_evaln.comp
      ((hClock.pair hLengthCode).pair hDay)
  have hTokenEval : Primrec₂ fun (p : P) i =>
      Nat.Partrec.Code.evaln p.1.2 p.1.1.2 (Nat.pair p.2 i) := by
    exact (Nat.Partrec.Code.primrec_evaln.comp
      (((hClock.comp Primrec.fst).pair
        (hTokenCode.comp Primrec.fst)).pair
        (Primrec₂.natPair.comp
          (hDay.comp Primrec.fst) Primrec.snd))).to₂
  have hToken : Primrec₂ fun (p : P) i =>
      (Nat.Partrec.Code.evaln p.1.2 p.1.1.2 (Nat.pair p.2 i)).getD 0 :=
    Primrec.option_getD.comp₂ hTokenEval (Primrec₂.const 0)
  have hSome : Primrec₂ fun (p : P) length =>
      (List.range (min length p.1.2)).map fun i =>
        (Nat.Partrec.Code.evaln p.1.2 p.1.1.2 (Nat.pair p.2 i)).getD 0 := by
    let Y := P × ℕ
    have hRange : Primrec fun y : Y => List.range (min y.2 y.1.1.2) :=
      Primrec.list_range.comp
        (Primrec.nat_min.comp Primrec.snd (hClock.comp Primrec.fst))
    have hMapToken : Primrec₂ fun (y : Y) i =>
        (Nat.Partrec.Code.evaln y.1.1.2 y.1.1.1.2
          (Nat.pair y.1.2 i)).getD 0 :=
      hToken.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
    exact (Primrec.list_map hRange hMapToken).to₂
  exact (Primrec.option_casesOn hLengthEval (Primrec.const []) hSome).of_eq fun p => by
    unfold clockedTokens
    cases h : Nat.Partrec.Code.evaln p.1.2 p.1.1.1 p.2 with
    | none => simp [h]
    | some length =>
        simp only [h]
        apply List.ext_getElem
        · simp
        · intro i hi₁ hi₂
          simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

private theorem codeAt_prim : Primrec codeAt := by
  exact (Primrec.option_getD.comp Primrec.decode
    (Primrec.const Nat.Partrec.Code.zero)).of_eq fun i => by rfl

private theorem traderProgramLengthCode_prim : Primrec fun j =>
    (traderProgramAt j).lengthCode := by
  have houter : Primrec Nat.unpair := Primrec.unpair
  have hmiddle : Primrec fun j : ℕ => j.unpair.1.unpair :=
    Primrec.unpair.comp (Primrec.fst.comp houter)
  have hinner : Primrec fun j : ℕ => j.unpair.1.unpair.1.unpair :=
    Primrec.unpair.comp (Primrec.fst.comp hmiddle)
  exact (codeAt_prim.comp (Primrec.fst.comp hinner)).of_eq fun j => by
    rfl

private theorem traderProgramTokenCode_prim : Primrec fun j =>
    (traderProgramAt j).tokenCode := by
  have houter : Primrec Nat.unpair := Primrec.unpair
  have hmiddle : Primrec fun j : ℕ => j.unpair.1.unpair :=
    Primrec.unpair.comp (Primrec.fst.comp houter)
  have hinner : Primrec fun j : ℕ => j.unpair.1.unpair.1.unpair :=
    Primrec.unpair.comp (Primrec.fst.comp hmiddle)
  exact (codeAt_prim.comp (Primrec.snd.comp hinner)).of_eq fun j => by
    rfl

private theorem traderProgramCoefficient_prim : Primrec fun j =>
    (traderProgramAt j).coefficient := by
  have houter : Primrec Nat.unpair := Primrec.unpair
  have hmiddle : Primrec fun j : ℕ => j.unpair.1.unpair :=
    Primrec.unpair.comp (Primrec.fst.comp houter)
  exact (Primrec.snd.comp hmiddle).of_eq fun j => by rfl

private theorem traderProgramDegree_prim : Primrec fun j =>
    (traderProgramAt j).degree := by
  exact (Primrec.snd.comp Primrec.unpair).of_eq fun j => by rfl

private theorem traderProgramClock_prim : Primrec₂ fun j n =>
    (traderProgramAt j).clock n := by
  let P := ℕ × ℕ
  have hcoefficient : Primrec fun p : P => (traderProgramAt p.1).coefficient :=
    traderProgramCoefficient_prim.comp Primrec.fst
  have hdegree : Primrec fun p : P => (traderProgramAt p.1).degree :=
    traderProgramDegree_prim.comp Primrec.fst
  have hbase : Primrec fun p : P => p.2 + 1 :=
    Primrec.nat_add.comp Primrec.snd (Primrec.const 1)
  have hpow₂ : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hpow : Primrec fun p : P => (p.2 + 1) ^ (traderProgramAt p.1).degree :=
    hpow₂.comp hbase hdegree
  have hmul : Primrec fun p : P =>
      (traderProgramAt p.1).coefficient *
        (p.2 + 1) ^ (traderProgramAt p.1).degree :=
    Primrec.nat_mul.comp hcoefficient hpow
  exact (Primrec.nat_add.comp hmul hcoefficient).to₂.of_eq fun j n => by
    rfl

private theorem enumeratedTraderTrades_prim : Primrec₂ fun j n =>
    ((enumeratedTrader j).strat n).trades := by
  let P := ℕ × ℕ
  have hj : Primrec fun p : P => p.1 := Primrec.fst
  have hn : Primrec fun p : P => p.2 := Primrec.snd
  have hlengthCode : Primrec fun p : P => (traderProgramAt p.1).lengthCode :=
    traderProgramLengthCode_prim.comp hj
  have htokenCode : Primrec fun p : P => (traderProgramAt p.1).tokenCode :=
    traderProgramTokenCode_prim.comp hj
  have hclock : Primrec fun p : P => (traderProgramAt p.1).clock p.2 :=
    traderProgramClock_prim.comp hj hn
  have hinput : Primrec fun p : P =>
      ((((traderProgramAt p.1).lengthCode, (traderProgramAt p.1).tokenCode),
        (traderProgramAt p.1).clock p.2), p.2) :=
    ((hlengthCode.pair htokenCode).pair hclock).pair hn
  have htoks : Primrec fun p : P => (traderProgramAt p.1).tokens p.2 :=
    (clockedTokens_prim.comp hinput).of_eq fun p => by rfl
  exact (strategyOfTokensTrades_prim.comp hn htoks).to₂.of_eq fun j n => by
    rfl

private theorem firmRawTraderTrades_prim : Primrec₂ fun j n =>
    ((firmRawTrader j).strat n).trades := by
  have hbefore : PrimrecRel fun j n => n < j :=
    PrimrecRel.comp₂ Primrec.nat_lt Primrec₂.right Primrec₂.left
  exact (Primrec.ite hbefore (Primrec.const [])
    enumeratedTraderTrades_prim).of_eq fun p => by
      rcases p with ⟨j, n⟩
      unfold firmRawTrader Trader.gate
      by_cases h : n < j
      · have hle : ¬j ≤ n := by omega
        simp [h, hle, Trader.zero]
      · have hle : j ≤ n := by omega
        simp [h, hle, Trader.zero]

/-! ## First-order finite-operation compiler -/

private theorem allBoolLists_prim : Primrec allBoolLists := by
  have hprepend (b : Bool) : Primrec fun xs : List (List Bool) =>
      xs.map (List.cons b) :=
    Primrec.list_map Primrec.id
      (Primrec.list_cons.comp₂ (Primrec₂.const b) Primrec₂.right)
  have hstep : Primrec₂ fun (_ : Unit)
      (ni : ℕ × List (List Bool)) =>
      ni.2.map (false :: ·) ++ ni.2.map (true :: ·) :=
    Primrec.list_append.comp₂
      ((hprepend false).comp₂ (Primrec.snd.comp₂ Primrec₂.right))
      ((hprepend true).comp₂ (Primrec.snd.comp₂ Primrec₂.right))
  have hrec : Primrec₂ fun (_ : Unit) n => allBoolLists n :=
    (Primrec.nat_rec (Primrec.const [[]]) hstep).of_eq fun _ n => by
      induction n with
      | zero => rfl
      | succ n ih => simp [allBoolLists, ih]
  exact hrec.comp (Primrec.const ()) Primrec.id

private theorem efNeg_prim : Primrec EF.neg := by
  exact (efMul_prim.comp
    (efConst_prim.comp (Primrec.const (-1 : ℚ))) Primrec.id).of_eq fun e => by
      rfl

private theorem efMin_prim : Primrec₂ EF.min := by
  have hinner : Primrec₂ fun a b : EF => EF.max (EF.neg a) (EF.neg b) :=
    efMax_prim.comp (efNeg_prim.comp Primrec.fst) (efNeg_prim.comp Primrec.snd)
  exact (efNeg_prim.comp hinner).to₂.of_eq fun a b => by rfl

private theorem efListMin_prim : Primrec EF.listMin := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const (EF.const 1))
    (efMin_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun es => by
        rfl

private theorem sumFeatures_prim : Primrec ROIBudget.sumFeatures := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const (EF.const 0))
    (efAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun es => by
        rfl

private theorem scaleConstTradeList_prim : Primrec₂ scaleConstTradeList := by
  let P := ℚ × List (EF × Sentence)
  have htrade : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      (EF.mul (EF.const p.1) trade.1, trade.2) :=
    (efMul_prim.comp
      (efConst_prim.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd) |>.to₂
  exact (Primrec.list_map Primrec.snd htrade).to₂.of_eq fun q trades => by
    rfl

private theorem tradingFirmWeight_prim : Primrec₂ tradingFirmWeight := by
  let P := ℕ × ℕ
  have hexponent : Primrec fun p : P => p.1 + 1 + p.2 :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)) Primrec.snd
  have hpow : Primrec fun p : P => (2 : ℚ) ^ (p.1 + 1 + p.2) :=
    ratPow_prim.comp (Primrec.const 2) hexponent
  exact (ratDiv_prim.comp (Primrec.const 1) hpow).to₂.of_eq fun j b => by
    rfl

/-- Remove duplicate sentences while preserving the last occurrence of each sentence. -/
def sentenceDedup (l : List Sentence) : List Sentence :=
  l.foldr (fun φ acc => if φ ∈ acc then acc else φ :: acc) []

@[simp] theorem sentenceDedup_nil : sentenceDedup [] = [] := by rfl

@[simp] theorem sentenceDedup_cons (a : Sentence) (l : List Sentence) :
    sentenceDedup (a :: l) =
      if a ∈ sentenceDedup l then sentenceDedup l else a :: sentenceDedup l := by
  rfl

@[simp] theorem mem_sentenceDedup : ∀ (l : List Sentence) (φ : Sentence),
    φ ∈ sentenceDedup l ↔ φ ∈ l := by
  intro l
  induction l with
  | nil => intro φ; simp
  | cons a l ih =>
      intro φ
      by_cases h : a ∈ sentenceDedup l
      · have hal : a ∈ l := (ih a).mp h
        rw [sentenceDedup_cons, if_pos h, ih φ]
        simp only [List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | hφ)
          · exact hal
          · exact hφ
      · have hal : a ∉ l := fun hal => h ((ih a).mpr hal)
        simp [sentenceDedup_cons, h, ih φ, hal]

theorem sentenceDedup_nodup (l : List Sentence) :
    (sentenceDedup l).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : a ∈ sentenceDedup l
      · simpa [sentenceDedup_cons, h] using ih
      · simp [sentenceDedup_cons, h, ih]

theorem sentenceDedup_prim : Primrec sentenceDedup := by
  have hmem : PrimrecRel fun (tail : List Sentence) (φ : Sentence) => φ ∈ tail :=
    (Primrec.eq.exists_mem_list).of_eq fun tail φ => by
      simp [eq_comm]
  have hstep : Primrec₂ fun (_ : List Sentence)
      (p : Sentence × List Sentence) =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2 :=
    Primrec.ite
      (hmem.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) |>.to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun l => by
    rfl

private theorem tradeListSupportSentenceList_prim :
    Primrec fun trades : List (EF × Sentence) =>
      supportSentenceList (tradeListSupport trades) := by
  let r : Sentence → Sentence → Prop := fun φ ψ =>
    Encodable.encode φ ≤ Encodable.encode ψ
  have hsentences : Primrec fun trades : List (EF × Sentence) =>
      trades.map Prod.snd :=
    Primrec.list_map Primrec.id (Primrec.snd.comp₂ Primrec₂.right)
  have hcanonical : Primrec fun trades : List (EF × Sentence) =>
      (sentenceDedup (trades.map Prod.snd)).insertionSort r :=
    sentenceInsertionSort_prim.comp (sentenceDedup_prim.comp hsentences)
  exact hcanonical.of_eq fun trades => by
    letI : IsTrans Sentence r :=
      ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
    letI : Std.Antisymm r :=
      ⟨fun _ _ hab hba => Encodable.encode_injective (le_antisymm hab hba)⟩
    letI : Std.Total r :=
      ⟨fun φ ψ => le_total (Encodable.encode φ) (Encodable.encode ψ)⟩
    let l := (sentenceDedup (trades.map Prod.snd)).insertionSort r
    have hnodup : l.Nodup :=
      (List.perm_insertionSort r _).nodup_iff.mpr
        (sentenceDedup_nodup (trades.map Prod.snd))
    have hsorted : l.Pairwise r := List.pairwise_insertionSort r _
    have htoFinset : l.toFinset = tradeListSupport trades := by
      ext φ
      simp [l, tradeListSupport]
    have hsort : (tradeListSupport trades).sort r = l := by
      rw [← htoFinset]
      exact (List.toFinset_sort (r := r) hnodup).mpr hsorted
    simpa [supportSentenceList, r] using hsort.symm

private theorem sentenceFinsetEncode_eq_supportSentenceList
    (S : Finset Sentence) :
    Encodable.encode S = Encodable.encode (supportSentenceList S) := by
  rw [sentenceFinsetEncode_eq]
  rfl

private theorem tradeListSupport_prim : Primrec tradeListSupport := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode.comp tradeListSupportSentenceList_prim).of_eq fun trades => by
    rw [sentenceFinsetEncode_eq_supportSentenceList]

private theorem tradeListSupportCard_prim :
    Primrec fun trades : List (EF × Sentence) => (tradeListSupport trades).card := by
  exact (Primrec.list_length.comp tradeListSupportSentenceList_prim).of_eq fun trades => by
    simp [supportSentenceList]

/-- The canonical code-sorted presentation of an arbitrary finite sentence set is
primitive recursive in the proof-erased finite-set encoding. -/
private theorem supportSentenceList_prim : Primrec supportSentenceList := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec fun S : Finset Sentence => Encodable.encode S).of_eq
    fun S => by
      rw [sentenceFinsetEncode_eq_supportSentenceList]

private theorem sentenceMemSupport_prim :
    PrimrecRel fun (S : Finset Sentence) (φ : Sentence) => φ ∈ S := by
  have hmem : PrimrecRel fun (l : List Sentence) (φ : Sentence) => φ ∈ l :=
    (Primrec.eq.exists_mem_list).of_eq fun l φ => by simp [eq_comm]
  exact (hmem.comp₂
    (supportSentenceList_prim.comp₂ Primrec₂.left) Primrec₂.right).of_eq fun S φ => by
    simp [supportSentenceList]

private theorem sentenceMemTradeListSupport_prim :
    PrimrecRel fun (trades : List (EF × Sentence)) (φ : Sentence) =>
      φ ∈ tradeListSupport trades := by
  exact sentenceMemSupport_prim.comp₂
    (tradeListSupport_prim.comp₂ Primrec₂.left) Primrec₂.right

/-- The support side-condition in first-order MarketMaker acceptance is an exact
primitive-recursive predicate on the raw trades and candidate entries. -/
private theorem rationalBeliefStateSupportSubsetTradeList_prim :
    PrimrecPred fun p : List (EF × Sentence) × RationalBeliefState =>
      p.2.support ⊆ tradeListSupport p.1 := by
  have hentry : PrimrecRel
      (fun (trades : List (EF × Sentence)) (entry : Sentence × ℚ) =>
        entry.1 ∈ tradeListSupport trades) :=
    sentenceMemTradeListSupport_prim.comp₂ Primrec₂.left
      (Primrec.fst.comp₂ Primrec₂.right)
  have hall : PrimrecRel
      (fun (trades : List (EF × Sentence)) (entries : List (Sentence × ℚ)) =>
        ∀ entry ∈ entries, entry.1 ∈ tradeListSupport trades) :=
    hentry.swap.forall_mem_list.swap
  exact (hall.comp Primrec.fst
    (rationalBeliefStateEntries_prim.comp Primrec.snd)).of_eq fun p => by
      rcases p with ⟨trades, B⟩
      constructor
      · intro hall φ hφ
        have hlist : φ ∈ B.entries.map Prod.fst := by
          exact List.mem_toFinset.mp hφ
        obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hlist
        rw [← heq]
        exact hall entry hentry
      · intro hsubset entry hentry
        apply hsubset
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, hentry, rfl⟩)

/-- Exact quotation from the candidate-updated rational history is primitive recursive
when all five inputs are packed as first-order data. -/
private theorem candidateRationalHistoryQuote_prim :
    Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        candidateRationalHistory p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2 := by
  have hday : PrimrecPred fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        p.1.2 = p.1.1.1.2 :=
    Primrec.eq.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hcandidate : Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        p.1.1.2.quote p.2 :=
    rationalBeliefStateQuote_prim.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hpastInput : Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        ((p.1.1.1.1, p.1.2), p.2) :=
    (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)
  have hpast : Primrec fun p :
      ((((List RationalBeliefState × ℕ) × RationalBeliefState) × ℕ) × Sentence) =>
        rationalHistory p.1.1.1.1 p.1.2 p.2 :=
    rationalHistory_prim.comp hpastInput
  exact (Primrec.ite hday hcandidate hpast).of_eq fun p => by
    rcases p with ⟨⟨⟨⟨past, n⟩, B⟩, day⟩, φ⟩
    by_cases h : day = n <;>
      simp [candidateRationalHistory, Function.update, h]

/-- The raw support-world lookup used by first-order MarketMaker acceptance is
primitive recursive in the trade list, Boolean table, and queried sentence. -/
private theorem tradeListSupportBitWorldRatFromList_prim :
    Primrec fun p : ((List (EF × Sentence) × List Bool) × Sentence) =>
      tradeListSupportBitWorldRatFromList p.1.1 p.1.2 p.2 := by
  let P := ((List (EF × Sentence) × List Bool) × Sentence)
  have htrades : Primrec fun p : P => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hbits : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hsentence : Primrec fun p : P => p.2 := Primrec.snd
  have hsupport : Primrec (fun p : P =>
      supportSentenceList (tradeListSupport p.1.1)) :=
    tradeListSupportSentenceList_prim.comp htrades
  have hmem : PrimrecPred fun p :
      P =>
        p.2 ∈ tradeListSupport p.1.1 :=
    sentenceMemTradeListSupport_prim.comp htrades hsentence
  have hidx : Primrec (fun p : P =>
      (supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) :=
    Primrec.list_idxOf.comp hsentence hsupport
  have hbit : Primrec (fun p : P =>
      p.1.2.getD ((supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) false) :=
    (Primrec.list_getD false).comp hbits hidx
  have hvalue : Primrec (fun p : P =>
      if p.1.2.getD ((supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) false
      then (1 : ℚ) else 0) :=
    (Primrec.cond hbit (Primrec.const 1) (Primrec.const 0)).of_eq fun p => by
      cases p.1.2.getD
          ((supportSentenceList (tradeListSupport p.1.1)).idxOf p.2) false <;> rfl
  exact (Primrec.ite hmem hvalue (Primrec.const 0)).of_eq fun p => by
    rcases p with ⟨⟨trades, xs⟩, φ⟩
    rfl

/-! ## Exact stack-machine semantics for rational `EF` evaluation -/

/-- A command is `(kind, payload, environment)`.  Kind `0` evaluates the raw `EF.toNat`
payload; kinds `1`--`4` combine values; kind `5` enters a saved `letE` body.  Using only
products and lists keeps the runtime state first-order and automatically `Primcodable`. -/
private abbrev EFRatCommand := ℕ × (ℕ × List ℚ)

private abbrev EFRatMachineState := List EFRatCommand × List ℚ

private def efRatRawEvalCommand (code : ℕ) (rho : List ℚ) : EFRatCommand :=
  (0, code, rho)

private def efRatEvalCommand (e : EF) (rho : List ℚ) : EFRatCommand :=
  efRatRawEvalCommand e.toNat rho

private def efRatOpCommand (kind : ℕ) : EFRatCommand := (kind, 0, [])

private def efRatLetBodyCommand (bodyCode : ℕ) (rho : List ℚ) : EFRatCommand :=
  (5, bodyCode, rho)

/-- One deterministic evaluator instruction.  Malformed raw syntax and malformed stacks
are totalized with zero or by dropping the bad instruction; reachable states from an `EF`
never use those fallback branches. -/
private def efRatMachineStep {C : Type*} (V : C → ℕ → Sentence → ℚ) (ctx : C) :
    EFRatMachineState → EFRatMachineState
  | ([], values) => ([], values)
  | ((kind, payload, rho) :: commands, values) =>
      match kind with
      | 0 =>
          let code := payload
          let efPayload := code.unpair.2
          match code.unpair.1 with
          | 0 =>
              (commands,
                (Encodable.decode (α := ℚ) efPayload).getD 0 :: values)
          | 1 =>
              let q := match Encodable.decode (α := Sentence) efPayload.unpair.1 with
                | some φ => V ctx efPayload.unpair.2 φ
                | none => 0
              (commands, q :: values)
          | 2 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatRawEvalCommand efPayload.unpair.2 rho ::
                efRatOpCommand 1 :: commands, values)
          | 3 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatRawEvalCommand efPayload.unpair.2 rho ::
                efRatOpCommand 2 :: commands, values)
          | 4 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatRawEvalCommand efPayload.unpair.2 rho ::
                efRatOpCommand 3 :: commands, values)
          | 5 =>
              (efRatRawEvalCommand efPayload rho :: efRatOpCommand 4 :: commands,
                values)
          | 6 => (commands, rho.getD efPayload 0 :: values)
          | 7 =>
              (efRatRawEvalCommand efPayload.unpair.1 rho ::
                efRatLetBodyCommand efPayload.unpair.2 rho :: commands, values)
          | _ => (commands, 0 :: values)
      | 1 =>
          match values with
          | b :: a :: rest => (commands, (a + b) :: rest)
          | _ => (commands, values)
      | 2 =>
          match values with
          | b :: a :: rest => (commands, (a * b) :: rest)
          | _ => (commands, values)
      | 3 =>
          match values with
          | b :: a :: rest => (commands, max a b :: rest)
          | _ => (commands, values)
      | 4 =>
          match values with
          | a :: rest => (commands, (max 1 a)⁻¹ :: rest)
          | _ => (commands, values)
      | 5 =>
          match values with
          | q :: rest =>
              (efRatRawEvalCommand payload (q :: rho) :: commands, rest)
          | _ => (commands, values)
      | _ => (commands, values)

/-- Exact instruction count needed by the evaluator. -/
private def efRatMachineSteps : EF → ℕ
  | .price _ _ => 1
  | .const _ => 1
  | .add a b => efRatMachineSteps a + efRatMachineSteps b + 2
  | .mul a b => efRatMachineSteps a + efRatMachineSteps b + 2
  | .max a b => efRatMachineSteps a + efRatMachineSteps b + 2
  | .safeRecip a => efRatMachineSteps a + 2
  | .var _ => 1
  | .letE x body => efRatMachineSteps x + efRatMachineSteps body + 2

private theorem efRatMachineSteps_le (e : EF) :
    efRatMachineSteps e ≤ 2 * e.cost := by
  induction e with
  | price => simp [efRatMachineSteps, EF.cost]
  | const => simp [efRatMachineSteps, EF.cost]
  | add a b iha ihb => simp only [efRatMachineSteps, EF.cost]; omega
  | mul a b iha ihb => simp only [efRatMachineSteps, EF.cost]; omega
  | max a b iha ihb => simp only [efRatMachineSteps, EF.cost]; omega
  | safeRecip a iha => simp only [efRatMachineSteps, EF.cost]; omega
  | var => simp [efRatMachineSteps, EF.cost]
  | letE x body ihx ihbody => simp only [efRatMachineSteps, EF.cost]; omega

private theorem iterate_add_forward {α : Type*} (f : α → α) (m n : ℕ) (x : α) :
    f^[m + n] x = f^[n] (f^[m] x) := by
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- Running exactly the structural instruction count evaluates one feature and preserves
the surrounding continuation/value stack. -/
private theorem efRatMachine_correct {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (ctx : C) (e : EF) (rho : List ℚ) (commands : List EFRatCommand)
    (values : List ℚ) :
    (efRatMachineStep V ctx)^[efRatMachineSteps e]
        (efRatEvalCommand e rho :: commands, values) =
      (commands, e.denoteRatWith rho (V ctx) :: values) := by
  induction e generalizing rho commands values with
  | price φ day =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efRatMachineStep, EF.toNat, EF.denoteRatWith, Encodable.encodek]
  | const q =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efRatMachineStep, EF.toNat, EF.denoteRatWith, Encodable.encodek]
  | var i =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efRatMachineStep, EF.toNat, EF.denoteRatWith]
  | add a b iha ihb =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.add a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.add a b) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: (0, b.toNat, rho) :: efRatOpCommand 1 :: commands, values) =
          ((0, b.toNat, rho) :: efRatOpCommand 1 :: commands,
            a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          ((0, b.toNat, rho) :: efRatOpCommand 1 :: commands,
            a.denoteRatWith rho (V ctx) :: values) =
          (efRatOpCommand 1 :: commands,
            b.denoteRatWith rho (V ctx) :: a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihb rho (efRatOpCommand 1 :: commands) (a.denoteRatWith rho (V ctx) :: values)]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | mul a b iha ihb =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.mul a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.mul a b) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: (0, b.toNat, rho) :: efRatOpCommand 2 :: commands, values) =
          ((0, b.toNat, rho) :: efRatOpCommand 2 :: commands,
            a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          ((0, b.toNat, rho) :: efRatOpCommand 2 :: commands,
            a.denoteRatWith rho (V ctx) :: values) =
          (efRatOpCommand 2 :: commands,
            b.denoteRatWith rho (V ctx) :: a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihb rho (efRatOpCommand 2 :: commands) (a.denoteRatWith rho (V ctx) :: values)]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | max a b iha ihb =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.max a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.max a b) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: (0, b.toNat, rho) :: efRatOpCommand 3 :: commands, values) =
          ((0, b.toNat, rho) :: efRatOpCommand 3 :: commands,
            a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 3 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          ((0, b.toNat, rho) :: efRatOpCommand 3 :: commands,
            a.denoteRatWith rho (V ctx) :: values) =
          (efRatOpCommand 3 :: commands,
            b.denoteRatWith rho (V ctx) :: a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihb rho (efRatOpCommand 3 :: commands) (a.denoteRatWith rho (V ctx) :: values)]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | safeRecip a iha =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.safeRecip a) =
          1 + efRatMachineSteps a + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + 1 =
          1 + (efRatMachineSteps a + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + 1]
          (f (efRatEvalCommand (EF.safeRecip a) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [iterate_add_forward f (efRatMachineSteps a) 1]
      rw [show f^[efRatMachineSteps a]
          ((0, a.toNat, rho) :: efRatOpCommand 4 :: commands, values) =
          (efRatOpCommand 4 :: commands, a.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatOpCommand 4 :: commands) values]
      simp [f, efRatMachineStep, efRatOpCommand, EF.denoteRatWith]
  | letE x body ihx ihbody =>
      let f := efRatMachineStep V ctx
      rw [show efRatMachineSteps (EF.letE x body) =
          1 + efRatMachineSteps x + 1 + efRatMachineSteps body by
        simp [efRatMachineSteps]; omega]
      rw [show 1 + efRatMachineSteps x + 1 + efRatMachineSteps body =
          1 + (efRatMachineSteps x + 1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps x + 1 + efRatMachineSteps body]
          (f (efRatEvalCommand (EF.letE x body) rho :: commands, values)) = _
      simp only [f, efRatEvalCommand, efRatRawEvalCommand, efRatMachineStep,
        EF.toNat, Nat.unpair_pair]
      rw [show efRatMachineSteps x + 1 + efRatMachineSteps body =
          efRatMachineSteps x + (1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f (efRatMachineSteps x)]
      rw [show f^[efRatMachineSteps x]
          ((0, x.toNat, rho) :: efRatLetBodyCommand body.toNat rho :: commands, values) =
          (efRatLetBodyCommand body.toNat rho :: commands,
            x.denoteRatWith rho (V ctx) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihx rho (efRatLetBodyCommand body.toNat rho :: commands) values]
      rw [iterate_add_forward f 1 (efRatMachineSteps body)]
      simp only [Function.iterate_one]
      simp only [f, efRatMachineStep, efRatLetBodyCommand]
      rw [show (efRatMachineStep V ctx)^[efRatMachineSteps body]
          (efRatRawEvalCommand body.toNat (x.denoteRatWith rho (V ctx) :: rho) ::
            commands, values) =
          (commands, body.denoteRatWith (x.denoteRatWith rho (V ctx) :: rho) (V ctx) :: values) by
        simpa only [efRatEvalCommand] using
          ihbody (x.denoteRatWith rho (V ctx) :: rho) commands values]
      rfl

/-! ## Primitive-recursive compilation of the evaluator transition -/

private def efRatBinaryValueStep (op : ℚ → ℚ → ℚ) :
    EFRatMachineState → EFRatMachineState
  | (commands, b :: a :: rest) => (commands, op a b :: rest)
  | state => state

private theorem efRatBinaryValueStep_prim (op : ℚ → ℚ → ℚ) (hop : Primrec₂ op) :
    Primrec (efRatBinaryValueStep op) := by
  let S := EFRatMachineState
  let Y := S × (ℚ × List ℚ)
  have htail : Primrec fun y : Y => y.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hresult : Primrec₂ fun (y : Y) (ar : ℚ × List ℚ) =>
      (y.1.1, op ar.1 y.2.1 :: ar.2) := by
    have ha : Primrec fun z : Y × (ℚ × List ℚ) => z.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hb : Primrec fun z : Y × (ℚ × List ℚ) => z.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hrest : Primrec fun z : Y × (ℚ × List ℚ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hvalues : Primrec fun z : Y × (ℚ × List ℚ) =>
        op z.2.1 z.1.2.1 :: z.2.2 :=
      Primrec.list_cons.comp (hop.comp ha hb) hrest
    have hcommands : Primrec fun z : Y × (ℚ × List ℚ) => z.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    exact (hcommands.pair hvalues).to₂
  have hsecond : Primrec fun y : Y =>
      match y.2.2 with
      | [] => y.1
      | a :: rest => (y.1.1, op a y.2.1 :: rest) :=
    (Primrec.list_casesOn htail Primrec.fst hresult).of_eq fun y => by
      cases y.2.2 <;> rfl
  exact (Primrec.list_casesOn Primrec.snd Primrec.id hsecond.to₂).of_eq fun state => by
    rcases state with ⟨commands, values⟩
    cases values with
    | nil => rfl
    | cons b tail =>
        cases tail <;> rfl

private def efRatUnaryValueStep (op : ℚ → ℚ) :
    EFRatMachineState → EFRatMachineState
  | (commands, a :: rest) => (commands, op a :: rest)
  | state => state

private theorem efRatUnaryValueStep_prim (op : ℚ → ℚ) (hop : Primrec op) :
    Primrec (efRatUnaryValueStep op) := by
  have hresult : Primrec₂ fun (state : EFRatMachineState) (ar : ℚ × List ℚ) =>
      (state.1, op ar.1 :: ar.2) := by
    have hop' : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) => op z.2.1 :=
      hop.comp (Primrec.fst.comp Primrec.snd)
    have hrest : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hvalues : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) =>
        op z.2.1 :: z.2.2 :=
      Primrec.list_cons.comp hop' hrest
    have hcommands : Primrec fun z : EFRatMachineState × (ℚ × List ℚ) => z.1.1 :=
      Primrec.fst.comp Primrec.fst
    exact (hcommands.pair hvalues).to₂
  exact (Primrec.list_casesOn Primrec.snd Primrec.id hresult).of_eq fun state => by
    rcases state with ⟨commands, values⟩
    cases values <;> rfl

private def efRatLetValueStep (payload : ℕ) (rho : List ℚ) :
    EFRatMachineState → EFRatMachineState
  | (commands, q :: rest) =>
      (efRatRawEvalCommand payload (q :: rho) :: commands, rest)
  | state => state

private theorem efRatLetValueStep_prim :
    Primrec fun p : (ℕ × List ℚ) × EFRatMachineState =>
      efRatLetValueStep p.1.1 p.1.2 p.2 := by
  let P := (ℕ × List ℚ) × EFRatMachineState
  have hvalues : Primrec fun p : P => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hresult : Primrec₂ fun (p : P) (qr : ℚ × List ℚ) =>
      (efRatRawEvalCommand p.1.1 (qr.1 :: p.1.2) :: p.2.1, qr.2) := by
    have hq : Primrec fun z : P × (ℚ × List ℚ) => z.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hrho : Primrec fun z : P × (ℚ × List ℚ) => z.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have henv : Primrec fun z : P × (ℚ × List ℚ) => z.2.1 :: z.1.1.2 :=
      Primrec.list_cons.comp hq hrho
    have hpayload : Primrec fun z : P × (ℚ × List ℚ) => z.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hcommand : Primrec fun z : P × (ℚ × List ℚ) =>
        efRatRawEvalCommand z.1.1.1 (z.2.1 :: z.1.1.2) :=
      (Primrec.const 0).pair (hpayload.pair henv)
    have hcommands : Primrec fun z : P × (ℚ × List ℚ) => z.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hnewCommands : Primrec fun z : P × (ℚ × List ℚ) =>
        efRatRawEvalCommand z.1.1.1 (z.2.1 :: z.1.1.2) :: z.1.2.1 :=
      Primrec.list_cons.comp hcommand hcommands
    have hrest : Primrec fun z : P × (ℚ × List ℚ) => z.2.2 :=
      Primrec.snd.comp Primrec.snd
    exact (hnewCommands.pair hrest).to₂
  exact (Primrec.list_casesOn hvalues Primrec.snd hresult).of_eq fun p => by
    rcases p with ⟨⟨payload, rho⟩, commands, values⟩
    cases values <;> rfl

/-- Rational maximum is primitive recursive in the canonical encoding. -/
theorem ratMax_prim : Primrec₂ fun q r : ℚ => max q r := by
  exact (Primrec.ite ratLE_prim Primrec₂.right Primrec₂.left).to₂.of_eq fun q r => by
    simp [max_def]

private theorem efRatSafeRecip_prim : Primrec fun q : ℚ => (max 1 q)⁻¹ := by
  have hmax : Primrec fun q : ℚ => max 1 q :=
    ratMax_prim.comp (Primrec.const 1) Primrec.id
  exact ratInv_prim.comp hmax

private abbrev EFRatRawInput (C : Type*) :=
  C × (ℕ × (List ℚ × EFRatMachineState))

private def efRatRawStep {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (p : EFRatRawInput C) : EFRatMachineState :=
  let ctx := p.1
  let code := p.2.1
  let rho := p.2.2.1
  let commands := p.2.2.2.1
  let values := p.2.2.2.2
  let tag := code.unpair.1
  let payload := code.unpair.2
  if tag = 0 then
    (commands, (Encodable.decode (α := ℚ) payload).getD 0 :: values)
  else if tag = 1 then
    let q := match Encodable.decode (α := Sentence) payload.unpair.1 with
      | some φ => V ctx payload.unpair.2 φ
      | none => 0
    (commands, q :: values)
  else if tag = 2 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatRawEvalCommand payload.unpair.2 rho ::
      efRatOpCommand 1 :: commands, values)
  else if tag = 3 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatRawEvalCommand payload.unpair.2 rho ::
      efRatOpCommand 2 :: commands, values)
  else if tag = 4 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatRawEvalCommand payload.unpair.2 rho ::
      efRatOpCommand 3 :: commands, values)
  else if tag = 5 then
    (efRatRawEvalCommand payload rho :: efRatOpCommand 4 :: commands, values)
  else if tag = 6 then
    (commands, rho.getD payload 0 :: values)
  else if tag = 7 then
    (efRatRawEvalCommand payload.unpair.1 rho ::
      efRatLetBodyCommand payload.unpair.2 rho :: commands, values)
  else
    (commands, 0 :: values)

private theorem efRatRawStep_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec (efRatRawStep V) := by
  let P := EFRatRawInput C
  have hctx : Primrec fun p : P => p.1 := Primrec.fst
  have hcode : Primrec fun p : P => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hrho : Primrec fun p : P => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcommands : Primrec fun p : P => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hvalues : Primrec fun p : P => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htag : Primrec fun p : P => p.2.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hcode)
  have hpayload : Primrec fun p : P => p.2.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hcode)
  have hpayloadLeft : Primrec fun p : P => p.2.1.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hpayload)
  have hpayloadRight : Primrec fun p : P => p.2.1.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hpayload)
  have hstate : Primrec fun p : P => (p.2.2.2.1, p.2.2.2.2) :=
    hcommands.pair hvalues
  have hrawLeft : Primrec fun p : P =>
      efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 :=
    (Primrec.const 0).pair (hpayloadLeft.pair hrho)
  have hrawRight : Primrec fun p : P =>
      efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 :=
    (Primrec.const 0).pair (hpayloadRight.pair hrho)
  have hrawPayload : Primrec fun p : P =>
      efRatRawEvalCommand p.2.1.unpair.2 p.2.2.1 :=
    (Primrec.const 0).pair (hpayload.pair hrho)
  have hopCommand (kind : ℕ) : Primrec fun _p : P => efRatOpCommand kind :=
    Primrec.const (efRatOpCommand kind)
  have hletCommand : Primrec fun p : P =>
      efRatLetBodyCommand p.2.1.unpair.2.unpair.2 p.2.2.1 :=
    (Primrec.const 5).pair (hpayloadRight.pair hrho)
  have hprepend3 {first second third : P → EFRatCommand}
      (hfirst : Primrec first) (hsecond : Primrec second) (hthird : Primrec third) :
      Primrec fun p : P => first p :: second p :: third p :: p.2.2.2.1 :=
    Primrec.list_cons.comp hfirst
      (Primrec.list_cons.comp hsecond (Primrec.list_cons.comp hthird hcommands))
  have hprepend2 {first second : P → EFRatCommand}
      (hfirst : Primrec first) (hsecond : Primrec second) :
      Primrec fun p : P => first p :: second p :: p.2.2.2.1 :=
    Primrec.list_cons.comp hfirst (Primrec.list_cons.comp hsecond hcommands)
  have hcase0 : Primrec fun p : P =>
      (p.2.2.2.1,
        (Encodable.decode (α := ℚ) p.2.1.unpair.2).getD 0 :: p.2.2.2.2) := by
    have hq : Primrec fun p : P =>
        (Encodable.decode (α := ℚ) p.2.1.unpair.2).getD 0 :=
      Primrec.option_getD.comp
        ((Primrec.decode : Primrec fun n : ℕ => Encodable.decode (α := ℚ) n).comp hpayload)
        (Primrec.const 0)
    exact hcommands.pair (Primrec.list_cons.comp hq hvalues)
  have hcase1 : Primrec fun p : P =>
      (p.2.2.2.1,
        (match Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 with
          | some φ => V p.1 p.2.1.unpair.2.unpair.2 φ
          | none => 0) :: p.2.2.2.2) := by
    have hs : Primrec fun p : P =>
        Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 :=
      (Primrec.decode : Primrec fun n : ℕ => Encodable.decode (α := Sentence) n).comp
        hpayloadLeft
    have hsome : Primrec₂ fun (p : P) (φ : Sentence) =>
        V p.1 p.2.1.unpair.2.unpair.2 φ := by
      have harg : Primrec fun z : P × Sentence =>
          (z.1.1, (z.1.2.1.unpair.2.unpair.2, z.2)) := by
        have hc : Primrec fun z : P × Sentence => z.1.1 :=
          Primrec.fst.comp Primrec.fst
        have hd : Primrec fun z : P × Sentence => z.1.2.1.unpair.2.unpair.2 :=
          hpayloadRight.comp Primrec.fst
        exact hc.pair (hd.pair Primrec.snd)
      exact (hV.comp harg).to₂
    have hq : Primrec fun p : P =>
        match Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 with
        | some φ => V p.1 p.2.1.unpair.2.unpair.2 φ
        | none => 0 :=
      (Primrec.option_casesOn hs (Primrec.const 0) hsome).of_eq fun p => by
        cases h : Encodable.decode (α := Sentence) p.2.1.unpair.2.unpair.1 <;>
          simp [h]
    exact hcommands.pair (Primrec.list_cons.comp hq hvalues)
  have hcommandCase {first second third : P → EFRatCommand}
      (hfirst : Primrec first) (hsecond : Primrec second) (hthird : Primrec third) :
      Primrec fun p : P =>
        (first p :: second p :: third p :: p.2.2.2.1, p.2.2.2.2) :=
    (hprepend3 hfirst hsecond hthird).pair hvalues
  have hcase2 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 ::
        efRatOpCommand 1 :: p.2.2.2.1, p.2.2.2.2) :=
    hcommandCase hrawLeft hrawRight (hopCommand 1)
  have hcase3 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 ::
        efRatOpCommand 2 :: p.2.2.2.1, p.2.2.2.2) :=
    hcommandCase hrawLeft hrawRight (hopCommand 2)
  have hcase4 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatRawEvalCommand p.2.1.unpair.2.unpair.2 p.2.2.1 ::
        efRatOpCommand 3 :: p.2.2.2.1, p.2.2.2.2) :=
    hcommandCase hrawLeft hrawRight (hopCommand 3)
  have hcase5 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2 p.2.2.1 ::
        efRatOpCommand 4 :: p.2.2.2.1, p.2.2.2.2) :=
    (hprepend2 hrawPayload (hopCommand 4)).pair hvalues
  have hcase6 : Primrec fun p : P =>
      (p.2.2.2.1, p.2.2.1.getD p.2.1.unpair.2 0 :: p.2.2.2.2) := by
    have hq : Primrec fun p : P => p.2.2.1.getD p.2.1.unpair.2 0 :=
      (Primrec.list_getD 0).comp hrho hpayload
    exact hcommands.pair (Primrec.list_cons.comp hq hvalues)
  have hcase7 : Primrec fun p : P =>
      (efRatRawEvalCommand p.2.1.unpair.2.unpair.1 p.2.2.1 ::
        efRatLetBodyCommand p.2.1.unpair.2.unpair.2 p.2.2.1 :: p.2.2.2.1,
        p.2.2.2.2) :=
    (hprepend2 hrawLeft hletCommand).pair hvalues
  have hfallback : Primrec fun p : P =>
      (p.2.2.2.1, (0 : ℚ) :: p.2.2.2.2) :=
    hcommands.pair (Primrec.list_cons.comp (Primrec.const 0) hvalues)
  have htagEq (k : ℕ) : PrimrecPred fun p : P => p.2.1.unpair.1 = k :=
    Primrec.eq.comp htag (Primrec.const k)
  exact (Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) hcase1
      (Primrec.ite (htagEq 2) hcase2
        (Primrec.ite (htagEq 3) hcase3
          (Primrec.ite (htagEq 4) hcase4
            (Primrec.ite (htagEq 5) hcase5
              (Primrec.ite (htagEq 6) hcase6
                (Primrec.ite (htagEq 7) hcase7 hfallback)))))))).of_eq fun p => by
    rfl

private abbrev EFRatCommandInput (C : Type*) :=
  C × (EFRatCommand × EFRatMachineState)

private def efRatCommandStep {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (p : EFRatCommandInput C) : EFRatMachineState :=
  let ctx := p.1
  let kind := p.2.1.1
  let payload := p.2.1.2.1
  let rho := p.2.1.2.2
  let state := p.2.2
  if kind = 0 then
    efRatRawStep V (ctx, payload, rho, state)
  else if kind = 1 then
    efRatBinaryValueStep (· + ·) state
  else if kind = 2 then
    efRatBinaryValueStep (· * ·) state
  else if kind = 3 then
    efRatBinaryValueStep max state
  else if kind = 4 then
    efRatUnaryValueStep (fun q => (max 1 q)⁻¹) state
  else if kind = 5 then
    efRatLetValueStep payload rho state
  else
    state

private theorem efRatCommandStep_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec (efRatCommandStep V) := by
  let P := EFRatCommandInput C
  have hctx : Primrec fun p : P => p.1 := Primrec.fst
  have hkind : Primrec fun p : P => p.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hpayload : Primrec fun p : P => p.2.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hrho : Primrec fun p : P => p.2.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hstate : Primrec fun p : P => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hrawArg : Primrec fun p : P =>
      (p.1, (p.2.1.2.1, (p.2.1.2.2, p.2.2))) :=
    hctx.pair (hpayload.pair (hrho.pair hstate))
  have hcase0 : Primrec fun p : P =>
      efRatRawStep V (p.1, p.2.1.2.1, p.2.1.2.2, p.2.2) :=
    (efRatRawStep_prim V hV).comp hrawArg
  have hcase1 : Primrec fun p : P => efRatBinaryValueStep (· + ·) p.2.2 :=
    (efRatBinaryValueStep_prim (· + ·) ratAdd_prim).comp hstate
  have hcase2 : Primrec fun p : P => efRatBinaryValueStep (· * ·) p.2.2 :=
    (efRatBinaryValueStep_prim (· * ·) ratMul_prim).comp hstate
  have hcase3 : Primrec fun p : P => efRatBinaryValueStep max p.2.2 :=
    (efRatBinaryValueStep_prim max ratMax_prim).comp hstate
  have hcase4 : Primrec fun p : P =>
      efRatUnaryValueStep (fun q => (max 1 q)⁻¹) p.2.2 :=
    (efRatUnaryValueStep_prim (fun q => (max 1 q)⁻¹) efRatSafeRecip_prim).comp hstate
  have hletArg : Primrec fun p : P => ((p.2.1.2.1, p.2.1.2.2), p.2.2) :=
    (hpayload.pair hrho).pair hstate
  have hcase5 : Primrec fun p : P =>
      efRatLetValueStep p.2.1.2.1 p.2.1.2.2 p.2.2 :=
    efRatLetValueStep_prim.comp hletArg
  have hkindEq (k : ℕ) : PrimrecPred fun p : P => p.2.1.1 = k :=
    Primrec.eq.comp hkind (Primrec.const k)
  exact (Primrec.ite (hkindEq 0) hcase0
    (Primrec.ite (hkindEq 1) hcase1
      (Primrec.ite (hkindEq 2) hcase2
        (Primrec.ite (hkindEq 3) hcase3
          (Primrec.ite (hkindEq 4) hcase4
            (Primrec.ite (hkindEq 5) hcase5 hstate)))))).of_eq fun p => by
    rfl

private theorem efRatMachineStep_packed_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec fun p : C × EFRatMachineState => efRatMachineStep V p.1 p.2 := by
  let P := C × EFRatMachineState
  have hcommands : Primrec fun p : P => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hcons : Primrec₂ fun (p : P) (cr : EFRatCommand × List EFRatCommand) =>
      efRatCommandStep V (p.1, cr.1, cr.2, p.2.2) := by
    have harg : Primrec fun z : P × (EFRatCommand × List EFRatCommand) =>
        (z.1.1, (z.2.1, (z.2.2, z.1.2.2))) := by
      have hctx : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.1.1 :=
        Primrec.fst.comp Primrec.fst
      have hcommand : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.2.1 :=
        Primrec.fst.comp Primrec.snd
      have hrest : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.2.2 :=
        Primrec.snd.comp Primrec.snd
      have hvalues : Primrec fun z : P × (EFRatCommand × List EFRatCommand) => z.1.2.2 :=
        Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
      exact hctx.pair (hcommand.pair (hrest.pair hvalues))
    exact ((efRatCommandStep_prim V hV).comp harg).to₂
  refine (Primrec.list_casesOn hcommands Primrec.snd hcons).of_eq ?_
  intro p
  rcases p with ⟨ctx, commands, values⟩
  cases commands with
  | nil => rfl
  | cons command rest =>
      rcases command with ⟨kind, payload, rho⟩
      simp only [efRatCommandStep]
      by_cases h0 : kind = 0
      · subst kind
        simp only [if_pos]
        generalize ht : payload.unpair.1 = tag
        by_cases hlt : tag < 8
        · interval_cases tag <;> simp [efRatRawStep, efRatMachineStep, ht]
        · have hle : 8 ≤ tag := by omega
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
          cases k with
          | zero => simp [efRatRawStep, efRatMachineStep, ht]
          | succ n =>
              rw [show 8 + (n + 1) = n + 9 by omega] at ht
              simp [efRatRawStep, efRatMachineStep, ht]
      · by_cases h1 : kind = 1
        · subst kind
          simp only [h0, if_false, if_pos]
          rcases values with _ | ⟨b, tail⟩
          · rfl
          · rcases tail with _ | ⟨a, tail⟩ <;> rfl
        · by_cases h2 : kind = 2
          · subst kind
            simp only [h0, h1, if_false, if_pos]
            rcases values with _ | ⟨b, tail⟩
            · rfl
            · rcases tail with _ | ⟨a, tail⟩ <;> rfl
          · by_cases h3 : kind = 3
            · subst kind
              simp only [h0, h1, h2, if_false, if_pos]
              rcases values with _ | ⟨b, tail⟩
              · rfl
              · rcases tail with _ | ⟨a, tail⟩ <;> rfl
            · by_cases h4 : kind = 4
              · subst kind
                simp only [h0, h1, h2, h3, if_false, if_pos]
                cases values <;> rfl
              · by_cases h5 : kind = 5
                · subst kind
                  simp only [h0, h1, h2, h3, h4, if_false, if_pos]
                  cases values <;> rfl
                · simp [h0, h1, h2, h3, h4, h5, efRatMachineStep]

private theorem efCost_le_toNat_succ (e : EF) : e.cost ≤ e.toNat + 1 := by
  induction e with
  | const q => simp [EF.cost, EF.toNat]
  | price φ day => simp [EF.cost, EF.toNat]
  | add a b iha ihb =>
      have hp := Nat.add_le_pair a.toNat b.toNat
      have ho := Nat.add_le_pair 2 (Nat.pair a.toNat b.toNat)
      simp only [EF.cost, EF.toNat]
      omega
  | mul a b iha ihb =>
      have hp := Nat.add_le_pair a.toNat b.toNat
      have ho := Nat.add_le_pair 3 (Nat.pair a.toNat b.toNat)
      simp only [EF.cost, EF.toNat]
      omega
  | max a b iha ihb =>
      have hp := Nat.add_le_pair a.toNat b.toNat
      have ho := Nat.add_le_pair 4 (Nat.pair a.toNat b.toNat)
      simp only [EF.cost, EF.toNat]
      omega
  | safeRecip a iha =>
      have ho := Nat.add_le_pair 5 a.toNat
      simp only [EF.cost, EF.toNat]
      omega
  | var i => simp [EF.cost, EF.toNat]
  | letE x body ihx ihbody =>
      have hp := Nat.add_le_pair x.toNat body.toNat
      have ho := Nat.add_le_pair 7 (Nat.pair x.toNat body.toNat)
      simp only [EF.cost, EF.toNat]
      omega

private def efRatMachineFuel (e : EF) : ℕ := 2 * (e.toNat + 1)

private theorem efRatMachineSteps_le_fuel (e : EF) :
    efRatMachineSteps e ≤ efRatMachineFuel e := by
  exact (efRatMachineSteps_le e).trans
    (Nat.mul_le_mul_left 2 (efCost_le_toNat_succ e))

private theorem efRatMachine_terminal {C : Type*}
    (V : C → ℕ → Sentence → ℚ) (ctx : C) (values : List ℚ) :
    efRatMachineStep V ctx ([], values) = ([], values) := rfl

private theorem efRatMachine_fuel_correct {C : Type*}
    (V : C → ℕ → Sentence → ℚ) (ctx : C) (e : EF) :
    (efRatMachineStep V ctx)^[efRatMachineFuel e]
        ([efRatEvalCommand e []], []) = ([], [e.denoteRat (V ctx)]) := by
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le (efRatMachineSteps_le_fuel e)
  rw [hextra, iterate_add_forward]
  rw [efRatMachine_correct V ctx e [] [] []]
  exact Function.iterate_fixed (efRatMachine_terminal V ctx [e.denoteRat (V ctx)]) extra

def efRatCompiledEval {C : Type*} (V : C → ℕ → Sentence → ℚ)
    (ctx : C) (e : EF) : ℚ :=
  (((efRatMachineStep V ctx)^[efRatMachineFuel e]
      ([efRatEvalCommand e []], [])).2).getD 0 0

theorem efRatCompiledEval_eq {C : Type*}
    (V : C → ℕ → Sentence → ℚ) (ctx : C) (e : EF) :
    efRatCompiledEval V ctx e = e.denoteRat (V ctx) := by
  rw [efRatCompiledEval, efRatMachine_fuel_correct]
  rfl

theorem efRatCompiledEval_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2) :
    Primrec fun p : C × EF => efRatCompiledEval V p.1 p.2 := by
  let P := C × EF
  have he : Primrec fun p : P => p.2 := Primrec.snd
  have hcode : Primrec fun p : P => p.2.toNat := by
    exact (Primrec.encode.comp he).of_eq fun p => rfl
  have hfuel : Primrec fun p : P => efRatMachineFuel p.2 := by
    have hsucc : Primrec fun p : P => p.2.toNat + 1 :=
      Primrec.nat_add.comp hcode (Primrec.const 1)
    exact (Primrec.nat_mul.comp (Primrec.const 2) hsucc).of_eq fun p => by
      rfl
  have hcommand : Primrec fun p : P => efRatEvalCommand p.2 [] :=
    (Primrec.const 0).pair (hcode.pair (Primrec.const []))
  have hcommands : Primrec fun p : P => [efRatEvalCommand p.2 []] :=
    Primrec.list_cons.comp hcommand (Primrec.const [])
  have hinit : Primrec fun p : P =>
      (([efRatEvalCommand p.2 []], []) : EFRatMachineState) :=
    hcommands.pair (Primrec.const [])
  have hstep : Primrec₂ fun (p : P) (state : EFRatMachineState) =>
      efRatMachineStep V p.1 state := by
    have harg : Primrec fun z : P × EFRatMachineState => (z.1.1, z.2) :=
      (Primrec.fst.comp Primrec.fst).pair Primrec.snd
    exact ((efRatMachineStep_packed_prim V hV).comp harg).to₂
  have hrun : Primrec fun p : P =>
      (efRatMachineStep V p.1)^[efRatMachineFuel p.2]
        ([efRatEvalCommand p.2 []], []) :=
    Primrec.nat_iterate hfuel hinit hstep
  have hresultValues : Primrec fun p : P =>
      ((efRatMachineStep V p.1)^[efRatMachineFuel p.2]
        ([efRatEvalCommand p.2 []], [])).2 :=
    Primrec.snd.comp hrun
  exact (Primrec.list_getD 0).comp hresultValues (Primrec.const 0)

private abbrev CandidateQuoteContext :=
  (List RationalBeliefState × ℕ) × RationalBeliefState

private def candidateQuote (ctx : CandidateQuoteContext)
    (day : ℕ) (φ : Sentence) : ℚ :=
  candidateRationalHistory ctx.1.1 ctx.1.2 ctx.2 day φ

private theorem candidateQuote_prim :
    Primrec fun p : CandidateQuoteContext × (ℕ × Sentence) =>
      candidateQuote p.1 p.2.1 p.2.2 := by
  have hpack : Primrec fun p : CandidateQuoteContext × (ℕ × Sentence) =>
      ((((p.1.1.1, p.1.1.2), p.1.2), p.2.1), p.2.2) :=
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.fst.comp Primrec.snd) |>.pair
          (Primrec.snd.comp Primrec.snd)
  exact (candidateRationalHistoryQuote_prim.comp hpack).of_eq fun p => by
    rfl

private def candidateCompiledEFValue (ctx : CandidateQuoteContext) (e : EF) : ℚ :=
  efRatCompiledEval candidateQuote ctx e

private theorem candidateCompiledEFValue_eq (ctx : CandidateQuoteContext) (e : EF) :
    candidateCompiledEFValue ctx e =
      e.denoteRat (candidateRationalHistory ctx.1.1 ctx.1.2 ctx.2) := by
  exact efRatCompiledEval_eq candidateQuote ctx e

private theorem candidateCompiledEFValue_prim :
    Primrec fun p : CandidateQuoteContext × EF =>
      candidateCompiledEFValue p.1 p.2 :=
  efRatCompiledEval_prim candidateQuote candidateQuote_prim

attribute [local irreducible] Nat.sqrt in
/-- A generic exact compiler for rational market value.  The context supplies both the
history quotation and the finite world's payout; the trade list itself remains ordinary
first-order data. -/
private theorem tradeListMarketValueRat_prim {C : Type*} [Primcodable C]
    (V : C → ℕ → Sentence → ℚ) (W : C → Sentence → ℚ)
    (hV : Primrec fun p : C × (ℕ × Sentence) => V p.1 p.2.1 p.2.2)
    (hW : Primrec fun p : C × Sentence => W p.1 p.2) :
    Primrec fun p : ((C × ℕ) × List (EF × Sentence)) =>
      tradeListMarketValueRat p.2 p.1.2 (V p.1.1) (W p.1.1) := by
  let P := ((C × ℕ) × List (EF × Sentence))
  let A := ((EF × Sentence) × ℚ)
  have hctx : Primrec fun z : P × A => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hday : Primrec fun z : P × A => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have he : Primrec fun z : P × A => z.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hsentence : Primrec fun z : P × A => z.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hacc : Primrec fun z : P × A => z.2.2 :=
    Primrec.snd.comp Primrec.snd
  have heval : Primrec fun z : P × A =>
      efRatCompiledEval V z.1.1.1 z.2.1.1 :=
    (efRatCompiledEval_prim V hV).comp (hctx.pair he)
  have hworld : Primrec fun z : P × A => W z.1.1.1 z.2.1.2 :=
    hW.comp (hctx.pair hsentence)
  have hprice : Primrec fun z : P × A => V z.1.1.1 z.1.1.2 z.2.1.2 :=
    hV.comp (hctx.pair (hday.pair hsentence))
  have hstep : Primrec₂ fun (p : P) (a : A) =>
      efRatCompiledEval V p.1.1 a.1.1 *
          (W p.1.1 a.1.2 - V p.1.1 p.1.2 a.1.2) + a.2 :=
    (ratAdd_prim.comp
      (ratMul_prim.comp heval (ratSub_prim.comp hworld hprice)) hacc).to₂
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0) hstep).of_eq fun p => by
    rcases p with ⟨⟨ctx, day⟩, trades⟩
    simp only [tradeListMarketValueRat]
    induction trades with
    | nil => rfl
    | cons trade rest ih =>
        simp only [List.foldr, List.map_cons, List.sum_cons]
        rw [efRatCompiledEval_eq, ih]

private abbrev MarketValueContext :=
  CandidateQuoteContext × (List (EF × Sentence) × List Bool)

private def marketValueHistory (ctx : MarketValueContext)
    (day : ℕ) (φ : Sentence) : ℚ := candidateQuote ctx.1 day φ

private def marketValueWorld (ctx : MarketValueContext) (φ : Sentence) : ℚ :=
  tradeListSupportBitWorldRatFromList ctx.2.1 ctx.2.2 φ

private theorem marketValueHistory_prim :
    Primrec fun p : MarketValueContext × (ℕ × Sentence) =>
      marketValueHistory p.1 p.2.1 p.2.2 := by
  have hinput : Primrec fun p : MarketValueContext × (ℕ × Sentence) =>
      (p.1.1, p.2) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  exact (candidateQuote_prim.comp hinput).of_eq fun p => rfl

private theorem marketValueWorld_prim :
    Primrec fun p : MarketValueContext × Sentence =>
      marketValueWorld p.1 p.2 := by
  have hinput : Primrec fun p : MarketValueContext × Sentence =>
      ((p.1.2.1, p.1.2.2), p.2) :=
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd
  exact (tradeListSupportBitWorldRatFromList_prim.comp hinput).of_eq fun p => rfl

private abbrev MarketMakerWorldInput :=
  ((((List (EF × Sentence) × ℕ) × List RationalBeliefState) ×
    RationalBeliefState) × List Bool)

private def marketMakerWorldValue (p : MarketMakerWorldInput) : ℚ :=
  tradeListMarketValueRat p.1.1.1.1 p.1.1.1.2
    (candidateRationalHistory p.1.1.2 p.1.1.1.2 p.1.2)
    (tradeListSupportBitWorldRatFromList p.1.1.1.1 p.2)

attribute [local irreducible] Nat.sqrt in
private theorem marketMakerWorldValue_prim :
    Primrec marketMakerWorldValue := by
  have htrades : Primrec fun p : MarketMakerWorldInput => p.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hday : Primrec fun p : MarketMakerWorldInput => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hpast : Primrec fun p : MarketMakerWorldInput => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hcandidate : Primrec fun p : MarketMakerWorldInput =>
      ((p.1.1.2, p.1.1.1.2), p.1.2) :=
    (hpast.pair hday).pair (Primrec.snd.comp Primrec.fst)
  have hworld : Primrec fun p : MarketMakerWorldInput =>
      (p.1.1.1.1, p.2) := htrades.pair Primrec.snd
  have hctx : Primrec fun p : MarketMakerWorldInput =>
      (((p.1.1.2, p.1.1.1.2), p.1.2), (p.1.1.1.1, p.2)) :=
    hcandidate.pair hworld
  have hsource : Primrec fun p : MarketMakerWorldInput =>
      (((((p.1.1.2, p.1.1.1.2), p.1.2), (p.1.1.1.1, p.2)),
        p.1.1.1.2), p.1.1.1.1) :=
    (hctx.pair hday).pair htrades
  exact ((tradeListMarketValueRat_prim marketValueHistory marketValueWorld
    marketValueHistory_prim marketValueWorld_prim).comp hsource).of_eq fun p => by
      rfl

private abbrev MarketMakerCoreInput :=
  (((List (EF × Sentence) × ℕ) × List RationalBeliefState) × RationalBeliefState)

private abbrev MarketMakerAcceptInput := MarketMakerCoreInput × ℚ

private def marketMakerAcceptsData (p : MarketMakerAcceptInput) : Prop :=
  p.1.2.support ⊆ tradeListSupport p.1.1.1.1 ∧
    ∀ xs ∈ allBoolLists (tradeListSupport p.1.1.1.1).card,
      marketMakerWorldValue (p.1, xs) ≤ p.2

private theorem marketMakerAcceptsData_iff (p : MarketMakerAcceptInput) :
    marketMakerAcceptsData p ↔
      MarketMakerAcceptsTradeList p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2 p.1.2 := by
  rfl

private theorem marketMakerAcceptsData_prim :
    PrimrecPred marketMakerAcceptsData := by
  have htrades : Primrec fun p : MarketMakerAcceptInput => p.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hcandidate : Primrec fun p : MarketMakerAcceptInput => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hsubset : PrimrecPred fun p : MarketMakerAcceptInput =>
      p.1.2.support ⊆ tradeListSupport p.1.1.1.1 :=
    rationalBeliefStateSupportSubsetTradeList_prim.comp
      (htrades.pair hcandidate)
  have hworld : Primrec fun z : MarketMakerAcceptInput × List Bool =>
      marketMakerWorldValue (z.1.1, z.2) :=
    marketMakerWorldValue_prim.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hle : PrimrecRel fun (p : MarketMakerAcceptInput) (xs : List Bool) =>
      marketMakerWorldValue (p.1, xs) ≤ p.2 :=
    ratLE_prim.comp hworld (Primrec.snd.comp Primrec.fst)
  have hall : PrimrecRel fun (p : MarketMakerAcceptInput)
      (xss : List (List Bool)) =>
        ∀ xs ∈ xss, marketMakerWorldValue (p.1, xs) ≤ p.2 :=
    hle.swap.forall_mem_list.swap
  have hassignments : Primrec fun p : MarketMakerAcceptInput =>
      allBoolLists (tradeListSupport p.1.1.1.1).card :=
    allBoolLists_prim.comp (tradeListSupportCard_prim.comp htrades)
  have hworlds : PrimrecPred fun p : MarketMakerAcceptInput =>
      ∀ xs ∈ allBoolLists (tradeListSupport p.1.1.1.1).card,
        marketMakerWorldValue (p.1, xs) ≤ p.2 :=
    hall.comp Primrec.id hassignments
  exact (hsubset.and hworlds).of_eq fun p => by
    rfl

private abbrev MarketMakerSearchInput :=
  (((List (EF × Sentence) × ℕ) × List RationalBeliefState) × ℚ)

/-- The first-order candidate test used by the executable MarketMaker search.  Decoding
failure is rejection; a successful decode is checked by the exact finite Boolean-world
acceptance predicate above. -/
private def marketMakerCandidateAcceptsData
    (p : MarketMakerSearchInput × ℕ) : Prop :=
  match marketMakerCandidate p.2 with
  | none => False
  | some B => marketMakerAcceptsData ((p.1.1, B), p.1.2)

private theorem marketMakerCandidateAcceptsData_iff
    (p : MarketMakerSearchInput × ℕ) :
    marketMakerCandidateAcceptsData p ↔
      MarketMakerCandidateAcceptsTradeList p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 := by
  unfold marketMakerCandidateAcceptsData
  cases hB : marketMakerCandidate p.2 with
  | none =>
      simp [MarketMakerCandidateAcceptsTradeList, hB]
  | some B =>
      simp [MarketMakerCandidateAcceptsTradeList, hB,
        marketMakerAcceptsData_iff]

private instance marketMakerCandidateAcceptsDataDecidable
    (p : MarketMakerSearchInput × ℕ) :
    Decidable (marketMakerCandidateAcceptsData p) :=
  decidable_of_iff
    (MarketMakerCandidateAcceptsTradeList p.1.1.1.1 p.1.1.1.2
      p.1.1.2 p.1.2 p.2)
    (marketMakerCandidateAcceptsData_iff p).symm

attribute [local irreducible] Nat.sqrt in
private theorem marketMakerCandidateAcceptsData_prim :
    PrimrecPred marketMakerCandidateAcceptsData := by
  letI : DecidablePred marketMakerAcceptsData :=
    marketMakerAcceptsData_prim.choose
  have hcandidate : Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerCandidate p.2 :=
    marketMakerCandidate_prim.comp Primrec.snd
  have hacceptInput : Primrec₂ fun
      (p : MarketMakerSearchInput × ℕ) (B : RationalBeliefState) =>
      ((p.1.1, B), p.1.2) := by
    have hcore : Primrec₂ fun
        (p : MarketMakerSearchInput × ℕ) (B : RationalBeliefState) =>
        (p.1.1, B) :=
      Primrec₂.pair.comp₂
        (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
        Primrec₂.right
    exact Primrec₂.pair.comp₂ hcore
      (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
  have hsome : Primrec₂ fun
      (p : MarketMakerSearchInput × ℕ) (B : RationalBeliefState) =>
      decide (marketMakerAcceptsData ((p.1.1, B), p.1.2)) :=
    marketMakerAcceptsData_prim.decide.comp₂ hacceptInput
  have hdecide : Primrec fun p : MarketMakerSearchInput × ℕ =>
      decide (marketMakerCandidateAcceptsData p) :=
    (Primrec.option_casesOn hcandidate (Primrec.const false) hsome).of_eq fun p => by
      cases hB : marketMakerCandidate p.2 <;>
        simp [marketMakerCandidateAcceptsData, hB]
  exact hdecide.primrecPred

private def marketMakerSearchStepData (ctx : MarketMakerSearchInput)
    (ni : ℕ × Option ℕ) : Option ℕ :=
  match ni.2 with
  | some k => some k
  | none =>
      if marketMakerCandidateAcceptsData (ctx, ni.1) then some ni.1 else none

/-- Packed, first-order form of MarketMaker's bounded least-candidate search. -/
private def marketMakerSearchIndexData (ctx : MarketMakerSearchInput) :
    ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
      marketMakerSearchStepData ctx
        (fuel, marketMakerSearchIndexData ctx fuel)

private theorem marketMakerSearchIndexData_eq
    (ctx : MarketMakerSearchInput) (fuel : ℕ) :
    marketMakerSearchIndexData ctx fuel =
      marketMakerSearchIndexUpToTradeList ctx.1.1.1 ctx.1.1.2
        ctx.1.2 ctx.2 fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [marketMakerSearchIndexData,
        marketMakerSearchStepData, marketMakerSearchIndexUpToTradeList, ih]
      cases hsearch : marketMakerSearchIndexUpToTradeList ctx.1.1.1
          ctx.1.1.2 ctx.1.2 ctx.2 fuel with
      | some k => rfl
      | none =>
          by_cases h : marketMakerCandidateAcceptsData (ctx, fuel)
          · have h' : MarketMakerCandidateAcceptsTradeList ctx.1.1.1
                ctx.1.1.2 ctx.1.2 ctx.2 fuel :=
              (marketMakerCandidateAcceptsData_iff (ctx, fuel)).mp h
            simp [h, h']
          · have h' : ¬MarketMakerCandidateAcceptsTradeList ctx.1.1.1
                ctx.1.1.2 ctx.1.2 ctx.2 fuel := fun hs =>
              h ((marketMakerCandidateAcceptsData_iff (ctx, fuel)).mpr hs)
            simp [h, h']

attribute [local irreducible] Nat.sqrt in
private theorem marketMakerSearchStepData_prim :
    Primrec₂ marketMakerSearchStepData := by
  let X := MarketMakerSearchInput × (ℕ × Option ℕ)
  have hfuel : Primrec fun x : X => x.2.1 :=
    Primrec.fst.comp (Primrec.snd)
  have htestInput : Primrec fun x : X => (x.1, x.2.1) :=
    Primrec.fst.pair hfuel
  have htest : PrimrecPred fun x : X =>
      marketMakerCandidateAcceptsData (x.1, x.2.1) :=
    marketMakerCandidateAcceptsData_prim.comp htestInput
  have hnone : Primrec fun x : X =>
      if marketMakerCandidateAcceptsData (x.1, x.2.1) then
        some x.2.1
      else none :=
    Primrec.ite htest
      (Primrec.option_some.comp hfuel)
      (Primrec.const none)
  have hprior : Primrec fun x : X => x.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hsome : Primrec₂ fun (_x : X) (k : ℕ) => (some k : Option ℕ) :=
    Primrec₂.option_some_iff.mpr Primrec₂.right
  have hstepPacked : Primrec fun x : X => marketMakerSearchStepData x.1 x.2 :=
    Primrec.option_casesOn hprior hnone hsome
      |>.of_eq fun x => by
        cases h : x.2.2 <;> simp [marketMakerSearchStepData, h]
  exact hstepPacked.to₂

private theorem marketMakerSearchIndexData_prim :
    Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerSearchIndexData p.1 p.2 := by
  have hrec : Primrec₂ fun (ctx : MarketMakerSearchInput) fuel =>
      marketMakerSearchIndexData ctx fuel :=
    (Primrec.nat_rec (Primrec.const none)
      marketMakerSearchStepData_prim).of_eq fun ctx fuel => by
      induction fuel with
      | zero => rfl
      | succ fuel ih => simp [marketMakerSearchIndexData, ih]
  exact hrec.comp Primrec.fst Primrec.snd

/-- The actual raw-trade-list MarketMaker search is primitive recursive, with no appeal
to the semantic fixed-point witness or to unbounded minimization. -/
private theorem marketMakerSearchIndexUpToTradeList_prim :
    Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerSearchIndexUpToTradeList p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 :=
  marketMakerSearchIndexData_prim.of_eq fun p =>
    marketMakerSearchIndexData_eq p.1 p.2

/-- Decoding the successful bounded-search index is primitive recursive as well. -/
private theorem marketMakerSearchUpToTradeList_prim :
    Primrec fun p : MarketMakerSearchInput × ℕ =>
      marketMakerSearchUpToTradeList p.1.1.1.1 p.1.1.1.2
        p.1.1.2 p.1.2 p.2 := by
  have hdecode : Primrec₂ fun
      (_p : MarketMakerSearchInput × ℕ) (k : ℕ) =>
      marketMakerCandidate k :=
    marketMakerCandidate_prim.comp₂ Primrec₂.right
  exact (Primrec.option_bind marketMakerSearchIndexUpToTradeList_prim
    hdecode).of_eq fun p => by
      rfl

/-! ## First-order Budgeter atom compiler -/

/-- Occurrence list of atoms in a sentence.  Deduplication and sorting are deliberately
kept separate, since the Budgeter atom universe combines many sentences before
canonicalizing. -/
private def sentenceAtomOccurrences : Sentence → List ℕ
  | .atom a => [a]
  | .falsum => []
  | .and φ ψ => sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ
  | .or φ ψ => sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ
  | .imp φ ψ => sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ

private def formulaAtomOccurrencesBinary
    (prior : List (Option (List ℕ))) (children : ℕ) : Option (List ℕ) := do
  let left ← prior.getD children.unpair.1 none
  let right ← prior.getD children.unpair.2 none
  some (left ++ right)

private theorem formulaAtomOccurrencesBinary_prim :
    Primrec₂ formulaAtomOccurrencesBinary := by
  let X := List (Option (List ℕ)) × ℕ
  have hleftIndex : Primrec fun p : X => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hrightIndex : Primrec fun p : X => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hleft : Primrec fun p : X => p.1.getD p.2.unpair.1 none :=
    (Primrec.list_getD none).comp Primrec.fst hleftIndex
  have hright : Primrec fun p : X => p.1.getD p.2.unpair.2 none :=
    (Primrec.list_getD none).comp Primrec.fst hrightIndex
  have hrightBind : Primrec₂ fun (p : X) (left : List ℕ) =>
      (p.1.getD p.2.unpair.2 none).bind fun right =>
        some (left ++ right) := by
    let Y := X × List ℕ
    have hrightY : Primrec fun y : Y =>
        y.1.1.getD y.1.2.unpair.2 none :=
      hright.comp Primrec.fst
    have hout : Primrec₂ fun (y : Y) (right : List ℕ) =>
        some (y.2 ++ right) :=
      Primrec₂.option_some_iff.mpr
        (Primrec.list_append.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    exact (Primrec.option_bind hrightY hout).to₂
  exact (Primrec.option_bind hleft hrightBind).to₂.of_eq fun prior children => by
    rfl

private def formulaAtomOccurrencesSucc
    (prior : List (Option (List ℕ))) (e : ℕ) : Option (List ℕ) :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then some []
  else if tag = 1 then some [payload]
  else if tag = 2 then formulaAtomOccurrencesBinary prior payload
  else if tag = 3 then formulaAtomOccurrencesBinary prior payload
  else if tag = 4 then formulaAtomOccurrencesBinary prior payload
  else none

private theorem formulaAtomOccurrencesSucc_prim :
    Primrec₂ formulaAtomOccurrencesSucc := by
  let tag : List (Option (List ℕ)) × ℕ → ℕ := fun p => p.2.unpair.1
  let payload : List (Option (List ℕ)) × ℕ → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have htagEq (k : ℕ) : PrimrecPred fun p : List (Option (List ℕ)) × ℕ =>
      tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hbinary : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      formulaAtomOccurrencesBinary p.1 (payload p) :=
    formulaAtomOccurrencesBinary_prim.comp Primrec.fst hpayload
  have hatom : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      (some [payload p] : Option (List ℕ)) :=
    Primrec.option_some.comp
      (Primrec.list_cons.comp hpayload (Primrec.const []))
  have h4 : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      if tag p = 4 then formulaAtomOccurrencesBinary p.1 (payload p) else none :=
    Primrec.ite (htagEq 4) hbinary (Primrec.const none)
  have h3 : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      if tag p = 3 then formulaAtomOccurrencesBinary p.1 (payload p)
      else if tag p = 4 then formulaAtomOccurrencesBinary p.1 (payload p) else none :=
    Primrec.ite (htagEq 3) hbinary h4
  have h2 : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      if tag p = 2 then formulaAtomOccurrencesBinary p.1 (payload p)
      else if tag p = 3 then formulaAtomOccurrencesBinary p.1 (payload p)
      else if tag p = 4 then formulaAtomOccurrencesBinary p.1 (payload p) else none :=
    Primrec.ite (htagEq 2) hbinary h3
  have h1 : Primrec fun p : List (Option (List ℕ)) × ℕ =>
      if tag p = 1 then some [payload p]
      else if tag p = 2 then formulaAtomOccurrencesBinary p.1 (payload p)
      else if tag p = 3 then formulaAtomOccurrencesBinary p.1 (payload p)
      else if tag p = 4 then formulaAtomOccurrencesBinary p.1 (payload p) else none :=
    Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const (some [])) h1).to₂.of_eq
    fun prior e => by simp only [formulaAtomOccurrencesSucc, tag, payload]

private def formulaAtomOccurrencesStep
    (prior : List (Option (List ℕ))) : Option (List ℕ) :=
  prior.length.casesOn none (formulaAtomOccurrencesSucc prior)

private theorem formulaAtomOccurrencesStep_prim :
    Primrec formulaAtomOccurrencesStep := by
  exact (Primrec.nat_casesOn Primrec.list_length (Primrec.const none)
    formulaAtomOccurrencesSucc_prim).of_eq fun prior => by
      simp only [formulaAtomOccurrencesStep]

private def formulaAtomOccurrencesDecoded (n : ℕ) : Option (List ℕ) :=
  (LO.Propositional.Formula.ofNat (α := ℕ) n).map sentenceAtomOccurrences

private theorem formulaAtomOccurrencesHistory_getD {n k : ℕ} (hk : k < n) :
    ((List.range n).map formulaAtomOccurrencesDecoded).getD k none =
      formulaAtomOccurrencesDecoded k := by
  have hzero : formulaAtomOccurrencesDecoded 0 = none := by
    simp [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat]
  rw [← hzero, List.getD_map]
  simp [List.getD_eq_getElem, hk]

private theorem formulaAtomOccurrencesBinary_history
    (payload n : ℕ) (hleft : payload.unpair.1 < n)
    (hright : payload.unpair.2 < n) :
    formulaAtomOccurrencesBinary
        ((List.range n).map formulaAtomOccurrencesDecoded) payload =
      ((LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1).bind fun φ =>
        (LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2).map fun ψ =>
          sentenceAtomOccurrences φ ++ sentenceAtomOccurrences ψ) := by
  unfold formulaAtomOccurrencesBinary
  rw [formulaAtomOccurrencesHistory_getD hleft,
    formulaAtomOccurrencesHistory_getD hright]
  cases hL : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
    cases hR : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
    simp [formulaAtomOccurrencesDecoded, hL, hR]

private theorem formulaAtomOccurrencesStep_history (n : ℕ) :
    formulaAtomOccurrencesStep
        ((List.range n).map formulaAtomOccurrencesDecoded) =
      formulaAtomOccurrencesDecoded n := by
  cases n with
  | zero =>
      simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesDecoded,
        LO.Propositional.Formula.ofNat]
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
      · simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesSucc,
          formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          tag, payload, h0, sentenceAtomOccurrences]
      by_cases h1 : tag = 1
      · simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesSucc,
          formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          tag, payload, h0, h1, sentenceAtomOccurrences]
      by_cases h2 : tag = 2
      · subst tag
        have hb := formulaAtomOccurrencesBinary_history payload (e + 1) hleft hright
        simp only [formulaAtomOccurrencesStep, List.length_map, List.length_range,
          formulaAtomOccurrencesSucc, h0, h1, h2, ↓reduceIte]
        rw [hb]
        simp only [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          h2, ↓reduceIte]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h3 : tag = 3
      · subst tag
        have hb := formulaAtomOccurrencesBinary_history payload (e + 1) hleft hright
        simp only [formulaAtomOccurrencesStep, List.length_map, List.length_range,
          formulaAtomOccurrencesSucc, h0, h1, h2, h3, ↓reduceIte]
        rw [hb]
        simp only [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          h3, ↓reduceIte]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h4 : tag = 4
      · subst tag
        have hb := formulaAtomOccurrencesBinary_history payload (e + 1) hleft hright
        simp only [formulaAtomOccurrencesStep, List.length_map, List.length_range,
          formulaAtomOccurrencesSucc, h0, h1, h2, h3, h4, ↓reduceIte]
        rw [hb]
        simp only [formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          h4, ↓reduceIte]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      · have htag : 5 ≤ tag := by omega
        simp [formulaAtomOccurrencesStep, formulaAtomOccurrencesSucc,
          formulaAtomOccurrencesDecoded, LO.Propositional.Formula.ofNat,
          tag, payload, h0, h1, h2, h3, h4, htag]

private theorem formulaAtomOccurrencesDecoded_prim :
    Primrec formulaAtomOccurrencesDecoded := by
  have hstep : Primrec₂ fun (_ : Unit) (prior : List (Option (List ℕ))) =>
      some (formulaAtomOccurrencesStep prior) :=
    Primrec₂.option_some_iff.mpr
      (formulaAtomOccurrencesStep_prim.comp Primrec₂.right)
  have hrec := Primrec.nat_strong_rec
    (fun (_ : Unit) n => formulaAtomOccurrencesDecoded n)
    hstep (fun _ n => by
      simpa using congrArg some (formulaAtomOccurrencesStep_history n))
  exact hrec.comp (Primrec.const ()) Primrec.id

private theorem sentenceAtomOccurrences_prim :
    Primrec sentenceAtomOccurrences := by
  have hdecoded : Primrec fun φ : Sentence =>
      formulaAtomOccurrencesDecoded (Encodable.encode φ) :=
    formulaAtomOccurrencesDecoded_prim.comp Primrec.encode
  have hget : Primrec fun o : Option (List ℕ) => o.getD [] :=
    (Primrec.option_casesOn Primrec.id (Primrec.const [])
      Primrec₂.right).of_eq fun o => by cases o <;> rfl
  exact (hget.comp hdecoded).of_eq fun φ => by
    rw [show Encodable.encode φ =
      LO.Propositional.Formula.toNat φ by rfl]
    simp [formulaAtomOccurrencesDecoded,
      LO.Propositional.Formula.ofNat_toNat]

@[simp] private theorem mem_sentenceAtomOccurrences :
    ∀ (φ : Sentence) (a : ℕ),
      a ∈ sentenceAtomOccurrences φ ↔ a ∈ φ.atoms := by
  intro φ
  induction φ with
  | atom b => intro a; simp [sentenceAtomOccurrences, Sentence.atoms]
  | falsum => intro a; simp [sentenceAtomOccurrences, Sentence.atoms]
  | imp φ ψ ihφ ihψ =>
      intro a
      simp [sentenceAtomOccurrences, Sentence.atoms, ihφ, ihψ]
  | and φ ψ ihφ ihψ =>
      intro a
      simp [sentenceAtomOccurrences, Sentence.atoms, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      intro a
      simp [sentenceAtomOccurrences, Sentence.atoms, ihφ, ihψ]

/-! ### Canonical finite atom lists

The operational Budgeter only needs a sorted, duplicate-free list of the atoms in its
finite universe.  Keeping that presentation as ordinary data avoids asking the runtime
compiler to inspect the quotient representation of `Finset`. -/

private def natDedup (l : List ℕ) : List ℕ :=
  l.foldr (fun a acc => if a ∈ acc then acc else a :: acc) []

@[simp] private theorem natDedup_nil : natDedup [] = [] := by rfl

@[simp] private theorem natDedup_cons (a : ℕ) (l : List ℕ) :
    natDedup (a :: l) =
      if a ∈ natDedup l then natDedup l else a :: natDedup l := by
  rfl

@[simp] private theorem mem_natDedup : ∀ (l : List ℕ) (a : ℕ),
    a ∈ natDedup l ↔ a ∈ l := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons b l ih =>
      intro a
      by_cases h : b ∈ natDedup l
      · have hbl : b ∈ l := (ih b).mp h
        rw [natDedup_cons, if_pos h, ih a]
        simp only [List.mem_cons]
        constructor
        · exact fun ha => Or.inr ha
        · rintro (hab | ha)
          · simpa [hab] using hbl
          · exact ha
      · have hbl : b ∉ l := fun hbl => h ((ih b).mpr hbl)
        simp [natDedup_cons, h, ih, hbl]

private theorem natDedup_nodup (l : List ℕ) : (natDedup l).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : a ∈ natDedup l
      · simpa [natDedup_cons, h] using ih
      · simp [natDedup_cons, h, ih]

private theorem natDedup_prim : Primrec natDedup := by
  have hmem : PrimrecRel fun (tail : List ℕ) (a : ℕ) => a ∈ tail :=
    (Primrec.eq.exists_mem_list).of_eq fun tail a => by simp [eq_comm]
  have hstep : Primrec₂ fun (_ : List ℕ) (p : ℕ × List ℕ) =>
      if p.1 ∈ p.2 then p.2 else p.1 :: p.2 :=
    Primrec.ite
      (hmem.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) |>.to₂
  exact (Primrec.list_foldr Primrec.id (Primrec.const []) hstep).of_eq fun l => by
    rfl

private theorem natOrderedInsert_prim :
    Primrec₂ (List.orderedInsert (fun a b : ℕ => a ≤ b)) := by
  let base : ℕ × List ℕ → List ℕ := fun p => [p.1]
  let step : (ℕ × List ℕ) → (ℕ × List ℕ × List ℕ) → List ℕ :=
    fun p q => if p.1 ≤ q.1 then p.1 :: q.1 :: q.2.1 else q.1 :: q.2.2
  have hbase : Primrec base :=
    (Primrec.list_cons.comp Primrec.fst (Primrec.const [])).of_eq fun p => by
      simp [base]
  have hpred : PrimrecPred fun x :
      (ℕ × List ℕ) × (ℕ × List ℕ × List ℕ) => x.1.1 ≤ x.2.1 :=
    Primrec.nat_le.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hthen : Primrec fun x :
      (ℕ × List ℕ) × (ℕ × List ℕ × List ℕ) =>
        x.1.1 :: x.2.1 :: x.2.2.1 :=
    Primrec.list_cons.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have helse : Primrec fun x :
      (ℕ × List ℕ) × (ℕ × List ℕ × List ℕ) => x.2.1 :: x.2.2.2 :=
    Primrec.list_cons.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hstep : Primrec₂ step :=
    (Primrec.ite hpred hthen helse).to₂.of_eq fun p q => by simp [step]
  exact (Primrec.list_rec Primrec.snd hbase hstep).to₂.of_eq fun a l => by
    change List.recOn l [a]
      (fun b tail ih => if a ≤ b then a :: b :: tail else b :: ih) =
        List.orderedInsert (fun a b : ℕ => a ≤ b) a l
    induction l with
    | nil => rfl
    | cons b l ih => simp [List.orderedInsert, ih]

private theorem natInsertionSort_prim :
    Primrec (List.insertionSort (fun a b : ℕ => a ≤ b)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const [])
    (natOrderedInsert_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))).of_eq fun l => by rfl

private def canonicalNatList (l : List ℕ) : List ℕ :=
  (natDedup l).insertionSort (fun a b => a ≤ b)

private theorem canonicalNatList_prim : Primrec canonicalNatList :=
  natInsertionSort_prim.comp natDedup_prim

private theorem canonicalNatList_eq_sort (l : List ℕ) :
    canonicalNatList l = l.toFinset.sort (fun a b => a ≤ b) := by
  let r : ℕ → ℕ → Prop := fun a b => a ≤ b
  let canonical := canonicalNatList l
  have hnodup : canonical.Nodup :=
    (List.perm_insertionSort r _).nodup_iff.mpr (natDedup_nodup l)
  have hsorted : canonical.Pairwise r := List.pairwise_insertionSort r _
  have htoFinset : canonical.toFinset = l.toFinset := by
    ext a
    simp [canonical, canonicalNatList]
  have hsort : l.toFinset.sort r = canonical := by
    rw [← htoFinset]
    exact (List.toFinset_sort (r := r) hnodup).mpr hsorted
  exact hsort.symm

private def sentenceListAtomOccurrences (sentences : List Sentence) : List ℕ :=
  sentences.flatMap sentenceAtomOccurrences

private theorem sentenceListAtomOccurrences_prim :
    Primrec sentenceListAtomOccurrences := by
  exact Primrec.list_flatMap Primrec.id
    (sentenceAtomOccurrences_prim.comp₂ Primrec₂.right)

@[simp] private theorem mem_sentenceListAtomOccurrences
    (sentences : List Sentence) (a : ℕ) :
    a ∈ sentenceListAtomOccurrences sentences ↔
      ∃ φ ∈ sentences, a ∈ φ.atoms := by
  simp [sentenceListAtomOccurrences]

private def tradeListAtomOccurrences (trades : List (EF × Sentence)) : List ℕ :=
  trades.flatMap fun trade => sentenceAtomOccurrences trade.2

private theorem tradeListAtomOccurrences_prim :
    Primrec tradeListAtomOccurrences := by
  exact Primrec.list_flatMap Primrec.id
    (sentenceAtomOccurrences_prim.comp₂
      (Primrec.snd.comp₂ Primrec₂.right))

@[simp] private theorem mem_tradeListAtomOccurrences
    (trades : List (EF × Sentence)) (a : ℕ) :
    a ∈ tradeListAtomOccurrences trades ↔
      a ∈ tradeListSentenceAtoms trades := by
  simp only [tradeListAtomOccurrences, List.mem_flatMap,
    mem_sentenceAtomOccurrences, tradeListSentenceAtoms, Finset.mem_biUnion,
    tradeListSupport, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨⟨e, φ⟩, htrade, ha⟩
    exact ⟨φ, ⟨⟨e, φ⟩, htrade, rfl⟩, ha⟩
  · rintro ⟨φ, ⟨trade, htrade, hEq⟩, ha⟩
    exact ⟨trade, htrade, by simpa [hEq] using ha⟩

private def stageAtomOccurrences
    (stages : List (Finset Sentence)) (n : ℕ) : List ℕ :=
  sentenceListAtomOccurrences
    (supportSentenceList (decodedStageTable stages n))

private theorem stageAtomOccurrences_prim : Primrec₂ stageAtomOccurrences := by
  exact (sentenceListAtomOccurrences_prim.comp
    (supportSentenceList_prim.comp
      (decodedStageTable_prim.comp Primrec.fst Primrec.snd))).to₂

@[simp] private theorem mem_stageAtomOccurrences
    (stages : List (Finset Sentence)) (n a : ℕ) :
    a ∈ stageAtomOccurrences stages n ↔
      a ∈ (decodedStageTable stages n).biUnion Sentence.atoms := by
  simp [stageAtomOccurrences, supportSentenceList]

private def firmPrefixAtomOccurrences (j n : ℕ) : List ℕ :=
  (List.range (n + 1)).flatMap fun i =>
    tradeListAtomOccurrences ((firmRawTrader j).strat i).trades

private theorem firmPrefixAtomOccurrences_prim :
    Primrec₂ firmPrefixAtomOccurrences := by
  let P := ℕ × ℕ
  have hrange : Primrec fun p : P => List.range (p.2 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have htrades : Primrec₂ fun (p : P) (i : ℕ) =>
      ((firmRawTrader p.1).strat i).trades :=
    firmRawTraderTrades_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  exact (Primrec.list_flatMap hrange
    (tradeListAtomOccurrences_prim.comp₂ htrades)).to₂

@[simp] private theorem mem_firmPrefixAtomOccurrences (j n a : ℕ) :
    a ∈ firmPrefixAtomOccurrences j n ↔
      a ∈ (Finset.range (n + 1)).biUnion fun i =>
        tradeListSentenceAtoms ((firmRawTrader j).strat i).trades := by
  simp [firmPrefixAtomOccurrences]

private def budgetAtomList
    (stages : List (Finset Sentence)) (j n : ℕ) : List ℕ :=
  canonicalNatList
    (stageAtomOccurrences stages n ++ firmPrefixAtomOccurrences j n)

private theorem budgetAtomList_prim : Primrec fun p :
    (List (Finset Sentence) × ℕ) × ℕ => budgetAtomList p.1.1 p.1.2 p.2 := by
  have hraw : Primrec fun p : (List (Finset Sentence) × ℕ) × ℕ =>
      stageAtomOccurrences p.1.1 p.2 ++ firmPrefixAtomOccurrences p.1.2 p.2 :=
    Primrec.list_append.comp
      (stageAtomOccurrences_prim.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (firmPrefixAtomOccurrences_prim.comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact canonicalNatList_prim.comp hraw

private theorem budgetAtomList_eq (stages : List (Finset Sentence)) (j n : ℕ) :
    budgetAtomList stages j n =
      (budgetAtomsFromStageTradeLists (decodedStageTable stages)
        (fun i => ((firmRawTrader j).strat i).trades) n).sort
          (fun a b => a ≤ b) := by
  rw [budgetAtomList, canonicalNatList_eq_sort]
  congr 1
  ext a
  simp [budgetAtomsFromStageTradeLists]

private def atomListTable (atoms : List ℕ) (xs : List Bool) (a : ℕ) : Bool :=
  if a ∈ atoms then xs.getD (atoms.idxOf a) false else false

private theorem atomListTable_prim : Primrec fun p :
    (List ℕ × List Bool) × ℕ => atomListTable p.1.1 p.1.2 p.2 := by
  have hmemList : PrimrecRel fun (atoms : List ℕ) (a : ℕ) => a ∈ atoms :=
    (Primrec.eq.exists_mem_list).of_eq fun atoms a => by simp [eq_comm]
  have hmem : PrimrecPred fun p : (List ℕ × List Bool) × ℕ =>
      p.2 ∈ p.1.1 :=
    hmemList.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hidx : Primrec fun p : (List ℕ × List Bool) × ℕ =>
      p.1.1.idxOf p.2 :=
    Primrec.list_idxOf.comp Primrec.snd
      (Primrec.fst.comp Primrec.fst)
  have hbit : Primrec fun p : (List ℕ × List Bool) × ℕ =>
      p.1.2.getD (p.1.1.idxOf p.2) false :=
    (Primrec.list_getD false).comp
      (Primrec.snd.comp Primrec.fst) hidx
  exact (Primrec.ite hmem hbit (Primrec.const false)).of_eq fun p => by
    rfl

private theorem atomListTable_sort_eq (A : Finset ℕ) (xs : List Bool) :
    atomListTable (A.sort (fun a b => a ≤ b)) xs =
      finiteAtomTableFromList A xs := by
  funext a
  simp [atomListTable, finiteAtomTableFromList]

private def sentenceBoolFromAtomList
    (atoms : List ℕ) (xs : List Bool) (φ : Sentence) : Bool :=
  sentenceBool (atomListTable atoms xs) φ

private def formulaBoolBinary (op : Bool → Bool → Bool)
    (prior : List (Option Bool)) (children : ℕ) : Option Bool := do
  let left ← prior.getD children.unpair.1 none
  let right ← prior.getD children.unpair.2 none
  some (op left right)

private theorem formulaBoolBinary_prim (op : Bool → Bool → Bool) :
    Primrec₂ (formulaBoolBinary op) := by
  let X := List (Option Bool) × ℕ
  have hleftIndex : Primrec fun p : X => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hrightIndex : Primrec fun p : X => p.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hleft : Primrec fun p : X => p.1.getD p.2.unpair.1 none :=
    (Primrec.list_getD none).comp Primrec.fst hleftIndex
  have hright : Primrec fun p : X => p.1.getD p.2.unpair.2 none :=
    (Primrec.list_getD none).comp Primrec.fst hrightIndex
  have hrightBind : Primrec₂ fun (p : X) (left : Bool) =>
      (p.1.getD p.2.unpair.2 none).bind fun right =>
        some (op left right) := by
    let Y := X × Bool
    have hrightY : Primrec fun y : Y =>
        y.1.1.getD y.1.2.unpair.2 none :=
      hright.comp Primrec.fst
    have hout : Primrec₂ fun (y : Y) (right : Bool) =>
        some (op y.2 right) :=
      Primrec₂.option_some_iff.mpr
        ((Primrec.dom_bool₂ op).comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    exact (Primrec.option_bind hrightY hout).to₂
  exact (Primrec.option_bind hleft hrightBind).to₂.of_eq fun prior children => by
    rfl

private def formulaBoolSucc
    (env : List ℕ × List Bool) (prior : List (Option Bool))
    (e : ℕ) : Option Bool :=
  let tag := e.unpair.1
  let payload := e.unpair.2
  if tag = 0 then some false
  else if tag = 1 then some (atomListTable env.1 env.2 payload)
  else if tag = 2 then formulaBoolBinary (fun a b => !a || b) prior payload
  else if tag = 3 then formulaBoolBinary (· && ·) prior payload
  else if tag = 4 then formulaBoolBinary (· || ·) prior payload
  else none

private theorem formulaBoolSucc_prim : Primrec₂ fun
    (p : (List ℕ × List Bool) × List (Option Bool)) (e : ℕ) =>
      formulaBoolSucc p.1 p.2 e := by
  let X := ((List ℕ × List Bool) × List (Option Bool)) × ℕ
  let tag : X → ℕ := fun p => p.2.unpair.1
  let payload : X → ℕ := fun p => p.2.unpair.2
  have htag : Primrec tag := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpayload : Primrec payload :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have htagEq (k : ℕ) : PrimrecPred fun p : X => tag p = k :=
    Primrec.eq.comp htag (Primrec.const k)
  have hatom : Primrec fun p : X =>
      (some (atomListTable p.1.1.1 p.1.1.2 (payload p)) : Option Bool) :=
    Primrec.option_some.comp
      (atomListTable_prim.comp
        (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
            hpayload))
  have hbinary (op : Bool → Bool → Bool) : Primrec fun p : X =>
      formulaBoolBinary op p.1.2 (payload p) :=
    (formulaBoolBinary_prim op).comp
      (Primrec.snd.comp Primrec.fst) hpayload
  have h4 : Primrec fun p : X =>
      if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 4) (hbinary (· || ·)) (Primrec.const none)
  have h3 : Primrec fun p : X =>
      if tag p = 3 then formulaBoolBinary (· && ·) p.1.2 (payload p)
      else if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 3) (hbinary (· && ·)) h4
  have h2 : Primrec fun p : X =>
      if tag p = 2 then
        formulaBoolBinary (fun a b => !a || b) p.1.2 (payload p)
      else if tag p = 3 then formulaBoolBinary (· && ·) p.1.2 (payload p)
      else if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 2) (hbinary fun a b => !a || b) h3
  have h1 : Primrec fun p : X =>
      if tag p = 1 then some (atomListTable p.1.1.1 p.1.1.2 (payload p))
      else if tag p = 2 then
        formulaBoolBinary (fun a b => !a || b) p.1.2 (payload p)
      else if tag p = 3 then formulaBoolBinary (· && ·) p.1.2 (payload p)
      else if tag p = 4 then
        formulaBoolBinary (· || ·) p.1.2 (payload p)
      else none :=
    Primrec.ite (htagEq 1) hatom h2
  exact (Primrec.ite (htagEq 0) (Primrec.const (some false)) h1).to₂.of_eq
    fun p e => by simp only [formulaBoolSucc, tag, payload]

private def formulaBoolStep
    (env : List ℕ × List Bool) (prior : List (Option Bool)) : Option Bool :=
  prior.length.casesOn none (formulaBoolSucc env prior)

private theorem formulaBoolStep_prim : Primrec₂ formulaBoolStep := by
  have hsucc : Primrec₂ fun
      (p : (List ℕ × List Bool) × List (Option Bool)) (e : ℕ) =>
        formulaBoolSucc p.1 p.2 e := formulaBoolSucc_prim
  exact (Primrec.nat_casesOn
    (Primrec.list_length.comp Primrec.snd)
    (Primrec.const none) hsucc).of_eq fun p => by
      simp only [formulaBoolStep]

private def formulaBoolDecoded
    (env : List ℕ × List Bool) (n : ℕ) : Option Bool :=
  (LO.Propositional.Formula.ofNat (α := ℕ) n).map
    (sentenceBoolFromAtomList env.1 env.2)

private theorem formulaBoolHistory_getD
    (env : List ℕ × List Bool) {n k : ℕ} (hk : k < n) :
    ((List.range n).map (formulaBoolDecoded env)).getD k none =
      formulaBoolDecoded env k := by
  have hzero : formulaBoolDecoded env 0 = none := by
    simp [formulaBoolDecoded, LO.Propositional.Formula.ofNat]
  rw [← hzero, List.getD_map]
  simp [List.getD_eq_getElem, hk]

private theorem formulaBoolBinary_history (op : Bool → Bool → Bool)
    (env : List ℕ × List Bool) (payload n : ℕ)
    (hleft : payload.unpair.1 < n) (hright : payload.unpair.2 < n) :
    formulaBoolBinary op ((List.range n).map (formulaBoolDecoded env)) payload =
      ((LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1).bind fun φ =>
        (LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2).map fun ψ =>
          op (sentenceBoolFromAtomList env.1 env.2 φ)
            (sentenceBoolFromAtomList env.1 env.2 ψ)) := by
  unfold formulaBoolBinary
  rw [formulaBoolHistory_getD env hleft, formulaBoolHistory_getD env hright]
  cases hL : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
    cases hR : LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
    simp [formulaBoolDecoded, hL, hR]

private theorem formulaBoolStep_history
    (env : List ℕ × List Bool) (n : ℕ) :
    formulaBoolStep env ((List.range n).map (formulaBoolDecoded env)) =
      formulaBoolDecoded env n := by
  cases n with
  | zero =>
      simp [formulaBoolStep, formulaBoolDecoded,
        LO.Propositional.Formula.ofNat]
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
      · simp [formulaBoolStep, formulaBoolSucc, formulaBoolDecoded,
          LO.Propositional.Formula.ofNat, tag, payload, h0,
          sentenceBoolFromAtomList, sentenceBool]
      by_cases h1 : tag = 1
      · simp [formulaBoolStep, formulaBoolSucc, formulaBoolDecoded,
          LO.Propositional.Formula.ofNat, tag, payload, h0, h1,
          sentenceBoolFromAtomList, sentenceBool]
      by_cases h2 : tag = 2
      · subst tag
        have hb := formulaBoolBinary_history (fun a b => !a || b)
          env payload (e + 1)
          hleft hright
        simp only [formulaBoolStep, List.length_map, List.length_range,
          formulaBoolSucc, h0, h1, h2, ↓reduceIte]
        rw [hb]
        simp only [formulaBoolDecoded, LO.Propositional.Formula.ofNat,
          h2, ↓reduceIte]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h3 : tag = 3
      · subst tag
        have hb := formulaBoolBinary_history (· && ·) env payload (e + 1)
          hleft hright
        simp only [formulaBoolStep, List.length_map, List.length_range,
          formulaBoolSucc, h0, h1, h2, h3, ↓reduceIte]
        rw [hb]
        simp only [formulaBoolDecoded, LO.Propositional.Formula.ofNat,
          h3, ↓reduceIte]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      by_cases h4 : tag = 4
      · subst tag
        have hb := formulaBoolBinary_history (· || ·) env payload (e + 1)
          hleft hright
        simp only [formulaBoolStep, List.length_map, List.length_range,
          formulaBoolSucc, h0, h1, h2, h3, h4, ↓reduceIte]
        rw [hb]
        simp only [formulaBoolDecoded, LO.Propositional.Formula.ofNat,
          h4, ↓reduceIte]
        cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.1 <;>
          cases LO.Propositional.Formula.ofNat (α := ℕ) payload.unpair.2 <;>
          rfl
      · have htag : 5 ≤ tag := by omega
        simp [formulaBoolStep, formulaBoolSucc, formulaBoolDecoded,
          LO.Propositional.Formula.ofNat, tag, payload, h0, h1, h2, h3, h4,
          htag]

private theorem formulaBoolDecoded_prim : Primrec₂ formulaBoolDecoded := by
  have hstep : Primrec₂ fun (env : List ℕ × List Bool)
      (prior : List (Option Bool)) => some (formulaBoolStep env prior) :=
    Primrec₂.option_some_iff.mpr formulaBoolStep_prim
  exact Primrec.nat_strong_rec formulaBoolDecoded hstep
    (fun env n => by simpa using congrArg some (formulaBoolStep_history env n))

private theorem sentenceBoolFromAtomList_prim : Primrec fun p :
    (List ℕ × List Bool) × Sentence =>
      sentenceBoolFromAtomList p.1.1 p.1.2 p.2 := by
  have hdecoded : Primrec fun p : (List ℕ × List Bool) × Sentence =>
      formulaBoolDecoded p.1 (Encodable.encode p.2) :=
    formulaBoolDecoded_prim.comp Primrec.fst
      (Primrec.encode.comp Primrec.snd)
  have hget : Primrec fun o : Option Bool => o.getD false :=
    (Primrec.option_casesOn Primrec.id (Primrec.const false)
      Primrec₂.right).of_eq fun o => by cases o <;> rfl
  exact (hget.comp hdecoded).of_eq fun p => by
    rcases p with ⟨env, φ⟩
    rw [show Encodable.encode φ =
      LO.Propositional.Formula.toNat φ by rfl]
    simp [formulaBoolDecoded, LO.Propositional.Formula.ofNat_toNat]

private def tableConsistentFromAtomList
    (atoms : List ℕ) (xs : List Bool) (D : Finset Sentence) : Bool :=
  (supportSentenceList D).foldr (fun φ ok =>
    sentenceBoolFromAtomList atoms xs φ && ok) true

private theorem tableConsistentFromAtomList_prim : Primrec fun p :
    (List ℕ × List Bool) × Finset Sentence =>
      tableConsistentFromAtomList p.1.1 p.1.2 p.2 := by
  let P := (List ℕ × List Bool) × Finset Sentence
  have hsentences : Primrec fun p : P => supportSentenceList p.2 :=
    supportSentenceList_prim.comp Primrec.snd
  have heval : Primrec₂ fun (p : P) (φ : Sentence) =>
      sentenceBoolFromAtomList p.1.1 p.1.2 φ :=
    sentenceBoolFromAtomList_prim.to₂.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have hstep : Primrec₂ fun (p : P) (q : Sentence × Bool) =>
      sentenceBoolFromAtomList p.1.1 p.1.2 q.1 && q.2 :=
    (Primrec.dom_bool₂ (· && ·)).comp₂
      (heval.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hsentences (Primrec.const true) hstep).of_eq
    fun p => by rfl

private theorem tableConsistentFromAtomList_sort_eq
    (A : Finset ℕ) (xs : List Bool) (D : Finset Sentence) :
    tableConsistentFromAtomList (A.sort (fun a b => a ≤ b)) xs D =
      tableConsistent (finiteAtomTableFromList A xs) D := by
  rw [← atomListTable_sort_eq A xs]
  have hfold : ∀ l : List Sentence,
      (l.foldr (fun φ ok =>
        sentenceBoolFromAtomList (A.sort fun a b => a ≤ b) xs φ && ok) true = true ↔
        ∀ φ ∈ l,
          sentenceBoolFromAtomList (A.sort fun a b => a ≤ b) xs φ = true) := by
    intro l
    induction l with
    | nil => simp
    | cons φ l ih => simp [ih]
  rw [Bool.eq_iff_iff]
  simp only [tableConsistentFromAtomList, tableConsistent,
    decide_eq_true_eq, hfold]
  simp [supportSentenceList, sentenceBoolFromAtomList]

private abbrev BudgetWorldContext :=
  List RationalBeliefState × (List ℕ × List Bool)

private def budgetWorldHistory (ctx : BudgetWorldContext)
    (day : ℕ) (φ : Sentence) : ℚ :=
  rationalHistory ctx.1 day φ

private def budgetWorldPayout (ctx : BudgetWorldContext)
    (φ : Sentence) : ℚ :=
  boolPayoutRat (atomListTable ctx.2.1 ctx.2.2) φ

private theorem budgetWorldHistory_prim : Primrec fun p :
    BudgetWorldContext × (ℕ × Sentence) =>
      budgetWorldHistory p.1 p.2.1 p.2.2 := by
  have hinput : Primrec fun p : BudgetWorldContext × (ℕ × Sentence) =>
      ((p.1.1, p.2.1), p.2.2) :=
    ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)
  exact (rationalHistory_prim.comp hinput).of_eq fun p => by rfl

private theorem budgetWorldPayout_prim : Primrec fun p :
    BudgetWorldContext × Sentence => budgetWorldPayout p.1 p.2 := by
  have heval : Primrec fun p : BudgetWorldContext × Sentence =>
      sentenceBoolFromAtomList p.1.2.1 p.1.2.2 p.2 :=
    sentenceBoolFromAtomList_prim.comp
      (((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)
  exact (Primrec.cond heval (Primrec.const (1 : ℚ))
    (Primrec.const 0)).of_eq fun p => by
      cases h : sentenceBoolFromAtomList p.1.2.1 p.1.2.2 p.2 <;>
        simp only [sentenceBoolFromAtomList] at h <;>
        simp [budgetWorldPayout, boolPayoutRat, h]

private def firmDayMarketValueData
    (ctx : BudgetWorldContext) (j i : ℕ) : ℚ :=
  tradeListMarketValueRat ((firmRawTrader j).strat i).trades i
    (budgetWorldHistory ctx) (budgetWorldPayout ctx)

attribute [local irreducible] Nat.sqrt in
private theorem firmDayMarketValueData_prim : Primrec fun p :
    (BudgetWorldContext × ℕ) × ℕ =>
      firmDayMarketValueData p.1.1 p.1.2 p.2 := by
  have htrades : Primrec fun p : (BudgetWorldContext × ℕ) × ℕ =>
      ((firmRawTrader p.1.2).strat p.2).trades :=
    firmRawTraderTrades_prim.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hsource : Primrec fun p : (BudgetWorldContext × ℕ) × ℕ =>
      ((p.1.1, p.2), ((firmRawTrader p.1.2).strat p.2).trades) :=
    ((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair htrades
  exact ((tradeListMarketValueRat_prim budgetWorldHistory budgetWorldPayout
    budgetWorldHistory_prim budgetWorldPayout_prim).comp hsource).of_eq
      fun p => by rfl

private def firmRawPriorWorthData
    (ctx : BudgetWorldContext) (j n : ℕ) : ℚ :=
  ((List.range n).map fun i => firmDayMarketValueData ctx j i).sum

attribute [local irreducible] Nat.sqrt in
private theorem firmRawPriorWorthData_prim : Primrec fun p :
    (BudgetWorldContext × ℕ) × ℕ =>
      firmRawPriorWorthData p.1.1 p.1.2 p.2 := by
  let P := (BudgetWorldContext × ℕ) × ℕ
  have hrange : Primrec fun p : P => List.range p.2 :=
    Primrec.list_range.comp Primrec.snd
  have hday : Primrec₂ fun (p : P) (i : ℕ) =>
      firmDayMarketValueData p.1.1 p.1.2 i :=
    firmDayMarketValueData_prim.to₂.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have hvalues : Primrec fun p : P =>
      (List.range p.2).map fun i => firmDayMarketValueData p.1.1 p.1.2 i :=
    Primrec.list_map hrange hday
  have hstep : Primrec₂ fun (_p : P) (q : ℚ × ℚ) => q.1 + q.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hvalues (Primrec.const 0) hstep).of_eq
    fun p => by rfl

private theorem firmRawPriorWorthData_eq
    (past : List RationalBeliefState) (atoms : List ℕ) (xs : List Bool)
    (j n : ℕ) :
    firmRawPriorWorthData (past, atoms, xs) j n =
      rawPriorWorthRatTradeLists
        (fun i => ((firmRawTrader j).strat i).trades)
        (rationalHistory past) (atomListTable atoms xs) n := by
  unfold firmRawPriorWorthData rawPriorWorthRatTradeLists
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.sum_range_succ, Finset.sum_range_succ, ih]
      rfl

private theorem natCastRat_prim : Primrec fun n : ℕ => (n : ℚ) := by
  exact (ratMk_prim.comp (intOfNat_prim.comp Primrec.id)
    (Primrec.const 1)).of_eq fun n => by
      rw [Rat.mkRat_eq_divInt]
      simp

private abbrev BudgetCoreInput :=
  (((List (Finset Sentence) × List RationalBeliefState) × ℕ) × ℕ) × ℕ

private def budgetConsistentAtDayData
    (atoms : List ℕ) (xs : List Bool)
    (stages : List (Finset Sentence)) (m : ℕ) : Bool :=
  tableConsistentFromAtomList atoms xs (decodedStageTable stages m)

private theorem budgetConsistentAtDayData_prim : Primrec fun p :
    ((List ℕ × List Bool) × List (Finset Sentence)) × ℕ =>
      budgetConsistentAtDayData p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have hstage : Primrec fun p :
      ((List ℕ × List Bool) × List (Finset Sentence)) × ℕ =>
        decodedStageTable p.1.2 p.2 :=
    decodedStageTable_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (tableConsistentFromAtomList_prim.comp
    (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair hstage)).of_eq
        fun p => by rfl

private def budgetWorthBreachedData
    (ctx : BudgetWorldContext) (j b m : ℕ) : Bool :=
  decide (firmRawPriorWorthData ctx j (m + 1) ≤ -(b : ℚ))

attribute [local irreducible] Nat.sqrt in
private theorem budgetWorthBreachedData_prim : Primrec fun p :
    ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      budgetWorthBreachedData p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have hctx : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.1.2 := Primrec.snd.comp Primrec.fst
  have hm : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      p.2 := Primrec.snd
  have hworth : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      firmRawPriorWorthData p.1.1.1 p.1.1.2 (p.2 + 1) :=
    firmRawPriorWorthData_prim.comp
      ((hctx.pair hj).pair (Primrec.nat_add.comp hm (Primrec.const 1)))
  have hnegBudget : Primrec fun p : ((BudgetWorldContext × ℕ) × ℕ) × ℕ =>
      -((p.1.2 : ℕ) : ℚ) :=
    ratNeg_prim.comp (natCastRat_prim.comp hb)
  exact ((ratLE_prim.comp hworth hnegBudget).decide).of_eq fun p => by
    rfl

private def firmBudgetBreachAtDayData
    (core : BudgetCoreInput) (xs : List Bool) (m : ℕ) : Bool :=
  budgetConsistentAtDayData
      (budgetAtomList core.1.1.1.1 core.1.1.2 core.2) xs core.1.1.1.1 m &&
    budgetWorthBreachedData
      (core.1.1.1.2, budgetAtomList core.1.1.1.1 core.1.1.2 core.2, xs)
      core.1.1.2 core.1.2 m

-- INTERACTIVE-SESSION SCAFFOLD (2026-07-15).  The `have` chain below elaborates cleanly
-- and fast (verified by bisection).  The sole obstruction is the final `exact`: the defeq
-- bridge `firmBudgetBreachAtDayData p.1.1 p.1.2 p.2 =?= (composed && form)` sends `whnf`
-- into a heartbeat blowup (isDefEq eagerly reduces the rational `decide`/`budgetAtomList`
-- leaves).  The `attribute [local irreducible]` line below is the candidate fix — it stops
-- isDefEq from unfolding those leaves so the bridge matches structurally.  If the `exact`
-- still spins in the Infoview, try: (a) `unfold firmBudgetBreachAtDayData; exact …`;
-- (b) `with_reducible exact …`; (c) profile with `set_option trace.profiler true in` at
-- low `maxHeartbeats` to see which leaf whnf is stuck on.  This is a tooling/defeq fix,
-- not a mathematical gap.  It is the last Budgeter-gate primrec piece.
section
-- Scoped so the reducibility overrides do not leak to later declarations.  Diagnostics
-- (`set_option diagnostics true`) showed the final `exact` blows up computing `Nat.sqrt`
-- (23k unfoldings) via `Nat.unpair` — i.e. isDefEq reconciling the `Primcodable` instance
-- of the deeply-nested product type, not the budget math.  Blocking `Nat.sqrt` (and the
-- budget leaves) stops that reduction so the instances/leaves match structurally.
attribute [local irreducible] Nat.sqrt budgetConsistentAtDayData budgetWorthBreachedData
  budgetAtomList firmRawPriorWorthData decodedStageTable tableConsistentFromAtomList

private theorem firmBudgetBreachAtDayData_prim : Primrec fun p :
    (BudgetCoreInput × List Bool) × ℕ =>
      firmBudgetBreachAtDayData p.1.1 p.1.2 p.2 := by
  let P := (BudgetCoreInput × List Bool) × ℕ
  have hstages : Primrec fun p : P => p.1.1.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hpast : Primrec fun p : P => p.1.1.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hj : Primrec fun p : P => p.1.1.1.1.2 :=
    Primrec.snd.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hb : Primrec fun p : P => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hn : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hxs : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hm : Primrec fun p : P => p.2 := Primrec.snd
  have hatoms : Primrec fun p : P =>
      budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have hconsistent : Primrec fun p : P =>
      budgetConsistentAtDayData
        (budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2)
        p.1.2 p.1.1.1.1.1.1 p.2 :=
    budgetConsistentAtDayData_prim.comp
      (((hatoms.pair hxs).pair hstages).pair hm)
  have hctx : Primrec fun p : P =>
      ((p.1.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2,
          p.1.2) : BudgetWorldContext) :=
    hpast.pair (hatoms.pair hxs)
  have hbreach : Primrec fun p : P =>
      budgetWorthBreachedData
        (p.1.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1.1 p.1.1.1.1.2 p.1.1.2,
          p.1.2)
        p.1.1.1.1.2 p.1.1.1.2 p.2 :=
    budgetWorthBreachedData_prim.comp
      (((hctx.pair hj).pair hb).pair hm)
  exact (Primrec.dom_bool₂ (· && ·)).comp hconsistent hbreach

end

/-! ## Exact compiler for the TradingFirm cutoff

The firm cutoff uses `EF.absBound`, whose operations differ slightly from ordinary
rational denotation.  We reuse the verified rational machine's command format and
continuation discipline, changing only constants, prices, `max`, and `safeRecip`. -/

private theorem ratAbs_prim : Primrec fun q : ℚ => |q| := by
  exact (ratMax_prim.comp Primrec.id (ratNeg_prim.comp Primrec.id)).of_eq
    fun q => by simp [abs_eq_max_neg]

private def efBoundRawStep
    (p : ℕ × (List ℚ × EFRatMachineState)) : EFRatMachineState :=
  let code := p.1
  let rho := p.2.1
  let state := p.2.2
  let tag := code.unpair.1
  let payload := code.unpair.2
  if tag = 0 then
    (state.1, |(Encodable.decode (α := ℚ) payload).getD 0| :: state.2)
  else if tag = 1 then
    (state.1, (1 : ℚ) :: state.2)
  else if tag = 4 then
    efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
      ((), Nat.pair 2 payload, rho, state)
  else
    efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
      ((), code, rho, state)

private theorem efBoundRawStep_prim : Primrec efBoundRawStep := by
  let P := ℕ × (List ℚ × EFRatMachineState)
  have hcode : Primrec fun p : P => p.1 := Primrec.fst
  have hrho : Primrec fun p : P => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hstate : Primrec fun p : P => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hcommands : Primrec fun p : P => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hvalues : Primrec fun p : P => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htag : Primrec fun p : P => p.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hcode)
  have hpayload : Primrec fun p : P => p.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hcode)
  have hzeroQuote : Primrec fun
      _p : Unit × (ℕ × Sentence) => (0 : ℚ) := Primrec.const 0
  have hraw := efRatRawStep_prim
    (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => (0 : ℚ)) hzeroQuote
  have hdefaultArg : Primrec fun p : P =>
      ((), (p.1, (p.2.1, p.2.2))) :=
    (Primrec.const ()).pair (hcode.pair (hrho.pair hstate))
  have hdefault : Primrec fun p : P =>
      efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
        ((), p.1, p.2.1, p.2.2) :=
    hraw.comp hdefaultArg
  have hmaxCode : Primrec fun p : P => Nat.pair 2 p.1.unpair.2 :=
    Primrec₂.natPair.comp (Primrec.const 2) hpayload
  have hmaxArg : Primrec fun p : P =>
      ((), (Nat.pair 2 p.1.unpair.2, (p.2.1, p.2.2))) :=
    (Primrec.const ()).pair (hmaxCode.pair (hrho.pair hstate))
  have hmax : Primrec fun p : P =>
      efRatRawStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
        ((), Nat.pair 2 p.1.unpair.2, p.2.1, p.2.2) :=
    hraw.comp hmaxArg
  have hdecoded : Primrec fun p : P =>
      (Encodable.decode (α := ℚ) p.1.unpair.2).getD 0 :=
    Primrec.option_getD.comp
      ((Primrec.decode : Primrec fun n : ℕ => Encodable.decode (α := ℚ) n).comp
        hpayload)
      (Primrec.const 0)
  have hcase0 : Primrec fun p : P =>
      (p.2.2.1, |(Encodable.decode (α := ℚ) p.1.unpair.2).getD 0| ::
        p.2.2.2) :=
    hcommands.pair (Primrec.list_cons.comp
      (ratAbs_prim.comp hdecoded) hvalues)
  have hcase1 : Primrec fun p : P =>
      (p.2.2.1, (1 : ℚ) :: p.2.2.2) :=
    hcommands.pair (Primrec.list_cons.comp (Primrec.const 1) hvalues)
  have htagEq (k : ℕ) : PrimrecPred fun p : P => p.1.unpair.1 = k :=
    Primrec.eq.comp htag (Primrec.const k)
  exact (Primrec.ite (htagEq 0) hcase0
    (Primrec.ite (htagEq 1) hcase1
      (Primrec.ite (htagEq 4) hmax hdefault))).of_eq fun p => by
        simp only [efBoundRawStep]

private def efBoundCommandStep
    (p : EFRatCommand × EFRatMachineState) : EFRatMachineState :=
  let kind := p.1.1
  let payload := p.1.2.1
  let rho := p.1.2.2
  let state := p.2
  if kind = 0 then efBoundRawStep (payload, rho, state)
  else if kind = 4 then efRatUnaryValueStep (fun _ => (1 : ℚ)) state
  else efRatCommandStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
    ((), p.1, state)

private theorem efBoundCommandStep_prim : Primrec efBoundCommandStep := by
  let P := EFRatCommand × EFRatMachineState
  have hkind : Primrec fun p : P => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hpayload : Primrec fun p : P => p.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hrho : Primrec fun p : P => p.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hstate : Primrec fun p : P => p.2 := Primrec.snd
  have hcase0 : Primrec fun p : P =>
      efBoundRawStep (p.1.2.1, p.1.2.2, p.2) :=
    efBoundRawStep_prim.comp (hpayload.pair (hrho.pair hstate))
  have hcase4 : Primrec fun p : P =>
      efRatUnaryValueStep (fun _ => (1 : ℚ)) p.2 :=
    (efRatUnaryValueStep_prim (fun _ => (1 : ℚ))
      (Primrec.const 1)).comp hstate
  have hzeroQuote : Primrec fun
      _p : Unit × (ℕ × Sentence) => (0 : ℚ) := Primrec.const 0
  have hdefaultArg : Primrec fun p : P => ((), (p.1, p.2)) :=
    (Primrec.const ()).pair (Primrec.fst.pair Primrec.snd)
  have hdefault : Primrec fun p : P =>
      efRatCommandStep (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => 0)
        ((), p.1, p.2) :=
    (efRatCommandStep_prim
      (fun (_ : Unit) (_ : ℕ) (_ : Sentence) => (0 : ℚ))
      hzeroQuote).comp hdefaultArg
  have hkindEq (k : ℕ) : PrimrecPred fun p : P => p.1.1 = k :=
    Primrec.eq.comp hkind (Primrec.const k)
  exact (Primrec.ite (hkindEq 0) hcase0
    (Primrec.ite (hkindEq 4) hcase4 hdefault)).of_eq fun p => by
      simp only [efBoundCommandStep]

private def efBoundMachineStep : EFRatMachineState → EFRatMachineState
  | ([], values) => ([], values)
  | (command :: commands, values) =>
      efBoundCommandStep (command, commands, values)

private theorem efBoundMachineStep_prim : Primrec efBoundMachineStep := by
  have hcommands : Primrec fun state : EFRatMachineState => state.1 :=
    Primrec.fst
  have hcons : Primrec₂ fun (state : EFRatMachineState)
      (cr : EFRatCommand × List EFRatCommand) =>
      efBoundCommandStep (cr.1, cr.2, state.2) := by
    have harg : Primrec fun z :
        EFRatMachineState × (EFRatCommand × List EFRatCommand) =>
        (z.2.1, (z.2.2, z.1.2)) :=
      (Primrec.fst.comp Primrec.snd).pair
        ((Primrec.snd.comp Primrec.snd).pair
          (Primrec.snd.comp Primrec.fst))
    exact (efBoundCommandStep_prim.comp harg).to₂
  exact (Primrec.list_casesOn hcommands Primrec.id hcons).of_eq fun state => by
    rcases state with ⟨commands, values⟩
    cases commands <;> rfl

private theorem efBoundMachineStep_add (a b : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.add a b) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
        efRatOpCommand 1 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatCommandStep, efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private theorem efBoundMachineStep_mul (a b : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.mul a b) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
        efRatOpCommand 2 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatCommandStep, efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private theorem efBoundMachineStep_max (a b : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.max a b) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
        efRatOpCommand 1 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatCommandStep, efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private theorem efBoundMachineStep_safeRecip (a : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.safeRecip a) rho :: commands, values) =
      (efRatEvalCommand a rho :: efRatOpCommand 4 :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatCommandStep, efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private theorem efBoundMachineStep_letE (x body : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatEvalCommand (EF.letE x body) rho :: commands, values) =
      (efRatEvalCommand x rho :: efRatLetBodyCommand body.toNat rho :: commands,
        values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
    efRatCommandStep, efRatRawStep, efRatEvalCommand, efRatRawEvalCommand,
    EF.toNat]

private theorem efBoundMachineStep_letBody (payload : ℕ) (rho : List ℚ)
    (q : ℚ) (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep
        (efRatLetBodyCommand payload rho :: commands, q :: values) =
      (efRatRawEvalCommand payload (q :: rho) :: commands, values) := by
  simp [efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
    efRatLetBodyCommand, efRatLetValueStep]

private theorem efBoundMachine_correct (e : EF) (rho : List ℚ)
    (commands : List EFRatCommand) (values : List ℚ) :
    efBoundMachineStep^[efRatMachineSteps e]
        (efRatEvalCommand e rho :: commands, values) =
      (commands, e.absBoundWith (rho.getD · 0) :: values) := by
  induction e generalizing rho commands values with
  | price φ day =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
        EF.toNat, EF.absBoundWith]
  | const q =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
        EF.toNat, EF.absBoundWith, Encodable.encodek]
  | var i =>
      simp [efRatMachineSteps, efRatEvalCommand, efRatRawEvalCommand,
        efBoundMachineStep, efBoundCommandStep, efBoundRawStep,
        efRatCommandStep, efRatRawStep, EF.toNat, EF.absBoundWith]
  | add a b iha ihb =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.add a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.add a b) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.add a b) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) by
        exact efBoundMachineStep_add a b rho commands values]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) =
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) =
          (efRatOpCommand 1 :: commands,
            b.absBoundWith (rho.getD · 0) ::
              a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihb rho (efRatOpCommand 1 :: commands)
            (a.absBoundWith (rho.getD · 0) :: values)]
      simp [f, efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
        efRatOpCommand, efRatBinaryValueStep, EF.absBoundWith]
  | mul a b iha ihb =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.mul a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.mul a b) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.mul a b) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 2 :: commands, values) by
        exact efBoundMachineStep_mul a b rho commands values]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 2 :: commands, values) =
          (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          (efRatEvalCommand b rho :: efRatOpCommand 2 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) =
          (efRatOpCommand 2 :: commands,
            b.absBoundWith (rho.getD · 0) ::
              a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihb rho (efRatOpCommand 2 :: commands)
            (a.absBoundWith (rho.getD · 0) :: values)]
      simp [f, efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
        efRatOpCommand, efRatBinaryValueStep, EF.absBoundWith]
  | max a b iha ihb =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.max a b) =
          1 + efRatMachineSteps a + efRatMachineSteps b + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + efRatMachineSteps b + 1 =
          1 + (efRatMachineSteps a + efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + efRatMachineSteps b + 1]
          (f (efRatEvalCommand (EF.max a b) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.max a b) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) by
        exact efBoundMachineStep_max a b rho commands values]
      rw [show efRatMachineSteps a + efRatMachineSteps b + 1 =
          efRatMachineSteps a + (efRatMachineSteps b + 1) by omega]
      rw [iterate_add_forward f (efRatMachineSteps a)]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatEvalCommand b rho ::
            efRatOpCommand 1 :: commands, values) =
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands) values]
      rw [iterate_add_forward f (efRatMachineSteps b) 1]
      rw [show f^[efRatMachineSteps b]
          (efRatEvalCommand b rho :: efRatOpCommand 1 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) =
          (efRatOpCommand 1 :: commands,
            b.absBoundWith (rho.getD · 0) ::
              a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihb rho (efRatOpCommand 1 :: commands)
            (a.absBoundWith (rho.getD · 0) :: values)]
      simp [f, efBoundMachineStep, efBoundCommandStep, efRatCommandStep,
        efRatOpCommand, efRatBinaryValueStep, EF.absBoundWith]
  | safeRecip a iha =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.safeRecip a) =
          1 + efRatMachineSteps a + 1 by
        simp only [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps a + 1 =
          1 + (efRatMachineSteps a + 1) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps a + 1]
          (f (efRatEvalCommand (EF.safeRecip a) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.safeRecip a) rho :: commands, values) =
          (efRatEvalCommand a rho :: efRatOpCommand 4 :: commands, values) by
        exact efBoundMachineStep_safeRecip a rho commands values]
      rw [iterate_add_forward f (efRatMachineSteps a) 1]
      rw [show f^[efRatMachineSteps a]
          (efRatEvalCommand a rho :: efRatOpCommand 4 :: commands, values) =
          (efRatOpCommand 4 :: commands,
            a.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          iha rho (efRatOpCommand 4 :: commands) values]
      simp [f, efBoundMachineStep, efBoundCommandStep,
        efRatOpCommand, efRatUnaryValueStep, EF.absBoundWith]
  | letE x body ihx ihbody =>
      let f := efBoundMachineStep
      rw [show efRatMachineSteps (EF.letE x body) =
          1 + efRatMachineSteps x + 1 + efRatMachineSteps body by
        simp [efRatMachineSteps]
        omega]
      rw [show 1 + efRatMachineSteps x + 1 + efRatMachineSteps body =
          1 + (efRatMachineSteps x + 1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f 1]
      simp only [Function.iterate_one]
      change f^[efRatMachineSteps x + 1 + efRatMachineSteps body]
          (f (efRatEvalCommand (EF.letE x body) rho :: commands, values)) = _
      rw [show f (efRatEvalCommand (EF.letE x body) rho :: commands, values) =
          (efRatEvalCommand x rho :: efRatLetBodyCommand body.toNat rho :: commands,
            values) by
        exact efBoundMachineStep_letE x body rho commands values]
      rw [show efRatMachineSteps x + 1 + efRatMachineSteps body =
          efRatMachineSteps x + (1 + efRatMachineSteps body) by omega]
      rw [iterate_add_forward f (efRatMachineSteps x)]
      rw [show f^[efRatMachineSteps x]
          (efRatEvalCommand x rho :: efRatLetBodyCommand body.toNat rho :: commands,
            values) =
          (efRatLetBodyCommand body.toNat rho :: commands,
            x.absBoundWith (rho.getD · 0) :: values) by
        simpa only [f, efRatEvalCommand] using
          ihx rho (efRatLetBodyCommand body.toNat rho :: commands) values]
      rw [iterate_add_forward f 1 (efRatMachineSteps body)]
      simp only [Function.iterate_one]
      rw [show f
          (efRatLetBodyCommand body.toNat rho :: commands,
            x.absBoundWith (rho.getD · 0) :: values) =
          (efRatRawEvalCommand body.toNat
            (x.absBoundWith (rho.getD · 0) :: rho) :: commands, values) by
        exact efBoundMachineStep_letBody body.toNat rho
          (x.absBoundWith (rho.getD · 0)) commands values]
      rw [show efBoundMachineStep^[efRatMachineSteps body]
          (efRatRawEvalCommand body.toNat
              (x.absBoundWith (rho.getD · 0) :: rho) :: commands, values) =
          (commands, body.absBoundWith
            ((x.absBoundWith (rho.getD · 0) :: rho).getD · 0) :: values) by
        simpa only [efRatEvalCommand] using
          ihbody (x.absBoundWith (rho.getD · 0) :: rho) commands values]
      congr 2
      apply congrArg body.absBoundWith
      funext i
      cases i <;> rfl

private theorem efBoundMachine_terminal (values : List ℚ) :
    efBoundMachineStep ([], values) = ([], values) := rfl

private theorem efBoundMachine_fuel_correct (e : EF) :
    efBoundMachineStep^[efRatMachineFuel e]
        ([efRatEvalCommand e []], []) = ([], [e.absBound]) := by
  obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le
    (efRatMachineSteps_le_fuel e)
  rw [hextra, iterate_add_forward]
  rw [show efBoundMachineStep^[efRatMachineSteps e]
      ([efRatEvalCommand e []], []) = ([], [e.absBound]) by
    simpa [EF.absBound] using efBoundMachine_correct e [] [] []]
  exact Function.iterate_fixed (efBoundMachine_terminal [e.absBound]) extra

private def efCompiledAbsBound (e : EF) : ℚ :=
  ((efBoundMachineStep^[efRatMachineFuel e]
    ([efRatEvalCommand e []], [])).2).getD 0 0

private theorem efCompiledAbsBound_eq (e : EF) :
    efCompiledAbsBound e = e.absBound := by
  rw [efCompiledAbsBound, efBoundMachine_fuel_correct]
  rfl

private theorem efCompiledAbsBound_prim : Primrec efCompiledAbsBound := by
  have hcode : Primrec fun e : EF => e.toNat := by
    exact Primrec.encode.of_eq fun e => rfl
  have hfuel : Primrec fun e : EF => efRatMachineFuel e := by
    have hsucc : Primrec fun e : EF => e.toNat + 1 :=
      Primrec.nat_add.comp hcode (Primrec.const 1)
    exact (Primrec.nat_mul.comp (Primrec.const 2) hsucc).of_eq fun e => by
      rfl
  have hcommand : Primrec fun e : EF => efRatEvalCommand e [] :=
    (Primrec.const 0).pair (hcode.pair (Primrec.const []))
  have hcommands : Primrec fun e : EF => [efRatEvalCommand e []] :=
    Primrec.list_cons.comp hcommand (Primrec.const [])
  have hinit : Primrec fun e : EF =>
      (([efRatEvalCommand e []], []) : EFRatMachineState) :=
    hcommands.pair (Primrec.const [])
  have hstep : Primrec₂ fun (_e : EF) (state : EFRatMachineState) =>
      efBoundMachineStep state :=
    efBoundMachineStep_prim.comp₂ Primrec₂.right
  have hrun : Primrec fun e : EF =>
      efBoundMachineStep^[efRatMachineFuel e]
        ([efRatEvalCommand e []], []) :=
    Primrec.nat_iterate hfuel hinit hstep
  exact (Primrec.list_getD 0).comp (Primrec.snd.comp hrun)
    (Primrec.const 0)

private theorem efAbsBound_prim : Primrec EF.absBound :=
  efCompiledAbsBound_prim.of_eq efCompiledAbsBound_eq

private theorem tradeListAbsBound_prim :
    Primrec Strategy.tradeListAbsBound := by
  have hbounds : Primrec fun trades : List (EF × Sentence) =>
      trades.map fun trade => trade.1.absBound :=
    Primrec.list_map Primrec.id
      (efAbsBound_prim.comp₂ (Primrec.fst.comp₂ Primrec₂.right))
  have hstep : Primrec₂ fun (_trades : List (EF × Sentence))
      (p : ℚ × ℚ) => p.1 + p.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hbounds (Primrec.const 0) hstep).of_eq
    fun trades => by rfl

private def firmDayAbsBoundData (j i : ℕ) : ℚ :=
  Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades

private theorem firmDayAbsBoundData_prim :
    Primrec₂ firmDayAbsBoundData := by
  exact (tradeListAbsBound_prim.comp
    (firmRawTraderTrades_prim.comp Primrec.fst Primrec.snd)).to₂

private def firmPrefixTotalBoundData (n j : ℕ) : ℚ :=
  ((List.range (n + 1)).map fun i => firmDayAbsBoundData j i).sum

private theorem firmPrefixTotalBoundData_prim :
    Primrec₂ firmPrefixTotalBoundData := by
  let P := ℕ × ℕ
  have hrange : Primrec fun p : P => List.range (p.1 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
  have hday : Primrec₂ fun (p : P) (i : ℕ) =>
      firmDayAbsBoundData p.2 i :=
    firmDayAbsBoundData_prim.comp₂
      (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  have hvalues : Primrec fun p : P =>
      (List.range (p.1 + 1)).map fun i => firmDayAbsBoundData p.2 i :=
    Primrec.list_map hrange hday
  have hstep : Primrec₂ fun (_p : P) (q : ℚ × ℚ) => q.1 + q.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hvalues (Primrec.const 0) hstep).to₂.of_eq
    fun n j => by rfl

private theorem firmPrefixTotalBoundData_eq (n j : ℕ) :
    firmPrefixTotalBoundData n j =
      ∑ i ∈ Finset.range (n + 1),
        Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades := by
  unfold firmPrefixTotalBoundData firmDayAbsBoundData
  have hsum : ∀ k : ℕ,
      ((List.range k).map fun i =>
        Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades).sum =
      ∑ i ∈ Finset.range k,
        Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.sum_range_succ, Finset.sum_range_succ, ih]
  exact hsum (n + 1)

private def firmTotalBoundData (n : ℕ) : ℚ :=
  ((List.range (n + 1)).map fun j => firmPrefixTotalBoundData n j).sum

private theorem firmTotalBoundData_prim : Primrec firmTotalBoundData := by
  have hrange : Primrec fun n : ℕ => List.range (n + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
  have hvalue : Primrec₂ fun (n j : ℕ) => firmPrefixTotalBoundData n j :=
    firmPrefixTotalBoundData_prim
  have hvalues : Primrec fun n : ℕ =>
      (List.range (n + 1)).map fun j => firmPrefixTotalBoundData n j :=
    Primrec.list_map hrange hvalue
  have hstep : Primrec₂ fun (_n : ℕ) (q : ℚ × ℚ) => q.1 + q.2 :=
    ratAdd_prim.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hvalues (Primrec.const 0) hstep).of_eq
    fun n => by rfl

private theorem firmTotalBoundData_eq (n : ℕ) :
    firmTotalBoundData n = tradingFirmTotalBoundTradeLists n := by
  unfold firmTotalBoundData tradingFirmTotalBoundTradeLists
  have hsum : ∀ k : ℕ,
      ((List.range k).map fun j => firmPrefixTotalBoundData n j).sum =
      ∑ j ∈ Finset.range k,
        ∑ i ∈ Finset.range (n + 1),
          Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.sum_range_succ, Finset.sum_range_succ, ih,
          firmPrefixTotalBoundData_eq]
  exact hsum (n + 1)

private def ratNatCeilData (q : ℚ) : ℕ :=
  (-((-q.num) / (q.den : ℤ))).natAbs

private theorem ratNatCeilData_prim : Primrec ratNatCeilData := by
  exact (intNatAbs_prim.comp
    (intNeg_prim.comp
      (intDivNat_prim.comp (intNeg_prim.comp ratNum_prim)
        ratDen_prim))).of_eq fun q => by rfl

private theorem ratNatCeilData_eq (q : ℚ) (hq : 0 ≤ q) :
    ratNatCeilData q = ⌈q⌉₊ := by
  have hceil : (0 : ℤ) ≤ ⌈q⌉ := Int.ceil_nonneg hq
  change (-((-q.num) / (q.den : ℤ))).natAbs = Int.toNat ⌈q⌉
  rw [← Rat.ceil_def']
  apply Int.ofNat_inj.mp
  rw [Int.natAbs_of_nonneg hceil, Int.toNat_of_nonneg hceil]

private theorem tradingFirmTotalBoundTradeLists_prim :
    Primrec tradingFirmTotalBoundTradeLists :=
  firmTotalBoundData_prim.of_eq firmTotalBoundData_eq

private theorem tradingFirmCutoffTradeLists_prim :
    Primrec tradingFirmCutoffTradeLists := by
  have hcompiled : Primrec fun n =>
      ratNatCeilData (tradingFirmTotalBoundTradeLists n) + 1 :=
    Primrec.nat_add.comp
      (ratNatCeilData_prim.comp tradingFirmTotalBoundTradeLists_prim)
      (Primrec.const 1)
  exact hcompiled.of_eq fun n => by
    unfold tradingFirmCutoffTradeLists
    rw [ratNatCeilData_eq]
    simpa using tradingFirmTotalBound_nonneg n


private def firmBudgetAssignmentBreachesData
    (core : BudgetCoreInput) (xs : List Bool) : Bool :=
  (List.range core.2).any fun m => firmBudgetBreachAtDayData core xs m

private theorem firmBudgetAssignmentBreachesData_prim : Primrec fun p :
    BudgetCoreInput × List Bool =>
      firmBudgetAssignmentBreachesData p.1 p.2 := by
  let P := BudgetCoreInput × List Bool
  have hrange : Primrec fun p : P => List.range p.1.2 :=
    Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)
  have hday : Primrec₂ fun (p : P) (m : ℕ) =>
      firmBudgetBreachAtDayData p.1 p.2 m :=
    firmBudgetBreachAtDayData_prim.to₂.comp₂
      Primrec₂.left Primrec₂.right
  have hstep : Primrec₂ fun (p : P) (q : ℕ × Bool) =>
      firmBudgetBreachAtDayData p.1 p.2 q.1 || q.2 :=
    (Primrec.dom_bool₂ (· || ·)).comp₂
      (hday.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hrange (Primrec.const false) hstep).of_eq
    fun p => by
      unfold firmBudgetAssignmentBreachesData
      induction List.range p.1.2 with
      | nil => rfl
      | cons m ms ih => simp [List.any, ih]

private def priorBudgetBreachData (core : BudgetCoreInput) : Bool :=
  let atoms := budgetAtomList core.1.1.1.1 core.1.1.2 core.2
  (allBoolLists atoms.length).any fun xs =>
    firmBudgetAssignmentBreachesData core xs

set_option maxHeartbeats 1600000 in
private theorem priorBudgetBreachData_prim : Primrec priorBudgetBreachData := by
  have hstages : Primrec fun core : BudgetCoreInput => core.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hj : Primrec fun core : BudgetCoreInput => core.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun core : BudgetCoreInput => core.2 := Primrec.snd
  have hatoms : Primrec fun core : BudgetCoreInput =>
      budgetAtomList core.1.1.1.1 core.1.1.2 core.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have hassignments : Primrec fun core : BudgetCoreInput =>
      allBoolLists (budgetAtomList core.1.1.1.1 core.1.1.2 core.2).length :=
    allBoolLists_prim.comp (Primrec.list_length.comp hatoms)
  have hassignment : Primrec₂ fun (core : BudgetCoreInput) (xs : List Bool) =>
      firmBudgetAssignmentBreachesData core xs :=
    firmBudgetAssignmentBreachesData_prim.to₂
  have hstep : Primrec₂ fun (core : BudgetCoreInput)
      (q : List Bool × Bool) =>
      firmBudgetAssignmentBreachesData core q.1 || q.2 :=
    (Primrec.dom_bool₂ (· || ·)).comp₂
      (hassignment.comp₂ Primrec₂.left
        (Primrec.fst.comp₂ Primrec₂.right))
      (Primrec.snd.comp₂ Primrec₂.right)
  exact (Primrec.list_foldr hassignments (Primrec.const false) hstep).of_eq
    fun core => by
      unfold priorBudgetBreachData
      let assignments :=
        allBoolLists (budgetAtomList core.1.1.1.1 core.1.1.2 core.2).length
      have hAny : ∀ l : List (List Bool),
          l.foldr (fun xs found =>
            firmBudgetAssignmentBreachesData core xs || found) false =
          l.any (firmBudgetAssignmentBreachesData core) := by
        intro l
        induction l with
        | nil => rfl
        | cons xs xss ih => simp [ih]
      exact hAny assignments

/-! The remaining Budgeter compiler builds the proof-erased world-value feature before
assembling the finite minimum.  Keeping this syntax constructor separate makes the bridge
back to `Strategy.tradeListWorldValueFeature` exact and reusable. -/

private def tradeListWorldValueFeatureData
    (atoms : List ℕ) (xs : List Bool) (trades : List (EF × Sentence))
    (n : ℕ) : EF :=
  ROIBudget.sumFeatures (trades.map fun p =>
    .mul p.1 (.add
      (.const (bif sentenceBoolFromAtomList atoms xs p.2 then 1 else 0))
      (.mul (.const (-1)) (.price p.2 n))))

section
attribute [local irreducible] Nat.sqrt sentenceBoolFromAtomList
  tradeListWorldValueFeatureData

private theorem tradeListWorldValueFeatureData_prim : Primrec fun p :
    ((List ℕ × List Bool) × List (EF × Sentence)) × ℕ =>
      tradeListWorldValueFeatureData p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  let P := ((List ℕ × List Bool) × List (EF × Sentence)) × ℕ
  have htrades : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have heval : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 :=
    sentenceBoolFromAtomList_prim.to₂.comp₂
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) |>.comp₂
          Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right)
  have hpayout : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      (bif sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 then
        (1 : ℚ) else 0) :=
    Primrec.cond heval (Primrec.const 1) (Primrec.const 0)
  have hprice : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      EF.price trade.2 p.2 :=
    efPrice_prim.comp₂
      (Primrec.snd.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.left)
  have hdelta : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      EF.add
        (EF.const (bif sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 then
          1 else 0))
        (EF.mul (EF.const (-1)) (EF.price trade.2 p.2)) :=
    efAdd_prim.comp₂
      (efConst_prim.comp₂ hpayout)
      (efMul_prim.comp₂
        (efConst_prim.comp₂ (Primrec₂.const (-1 : ℚ))) hprice)
  have htrade : Primrec₂ fun (p : P) (trade : EF × Sentence) =>
      EF.mul trade.1
        (EF.add
          (EF.const (bif sentenceBoolFromAtomList p.1.1.1 p.1.1.2 trade.2 then
            1 else 0))
          (EF.mul (EF.const (-1)) (EF.price trade.2 p.2))) :=
    efMul_prim.comp₂ (Primrec.fst.comp₂ Primrec₂.right) hdelta
  exact (sumFeatures_prim.comp
    (Primrec.list_map htrades htrade)).of_eq fun p => by
      unfold tradeListWorldValueFeatureData
      rfl

end

private theorem tradeListWorldValueFeatureData_eq
    (atoms : List ℕ) (xs : List Bool) (trades : List (EF × Sentence))
    (n : ℕ) :
    tradeListWorldValueFeatureData atoms xs trades n =
      Strategy.tradeListWorldValueFeature trades n (atomListTable atoms xs) := by
  unfold tradeListWorldValueFeatureData Strategy.tradeListWorldValueFeature
  apply congrArg ROIBudget.sumFeatures
  apply List.map_congr_left
  intro trade htrade
  rcases trade with ⟨e, φ⟩
  cases h : sentenceBoolFromAtomList atoms xs φ
  · have h' : sentenceBool (atomListTable atoms xs) φ = false := h
    simp [boolPayoutRat, h']
  · have h' : sentenceBool (atomListTable atoms xs) φ = true := h
    simp [boolPayoutRat, h']

private def budgetWorldScaleData
    (core : BudgetCoreInput) (xs : List Bool) : EF :=
  let atoms := budgetAtomList core.1.1.1.1 core.1.1.2 core.2
  let trades := ((firmRawTrader core.1.1.2).strat core.2).trades
  .safeRecip (.mul
    (.const (((core.1.2 : ℕ) : ℚ) + firmRawPriorWorthData
      (core.1.1.1.2, atoms, xs) core.1.1.2 core.2)⁻¹)
    (EF.neg (tradeListWorldValueFeatureData atoms xs trades core.2)))

section
attribute [local irreducible] Nat.sqrt budgetWorldScaleData budgetAtomList
  firmRawPriorWorthData tradeListWorldValueFeatureData

private theorem budgetWorldScaleData_prim : Primrec fun p :
    BudgetCoreInput × List Bool => budgetWorldScaleData p.1 p.2 := by
  let P := BudgetCoreInput × List Bool
  have hstages : Primrec fun p : P => p.1.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hpast : Primrec fun p : P => p.1.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hj : Primrec fun p : P => p.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hb : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hxs : Primrec fun p : P => p.2 := Primrec.snd
  have hatoms : Primrec fun p : P =>
      budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have htrades : Primrec fun p : P =>
      ((firmRawTrader p.1.1.1.2).strat p.1.2).trades :=
    firmRawTraderTrades_prim.comp hj hn
  have hctx : Primrec fun p : P =>
      ((p.1.1.1.1.2,
        budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2,
        p.2) : BudgetWorldContext) :=
    hpast.pair (hatoms.pair hxs)
  have hworth : Primrec fun p : P =>
      firmRawPriorWorthData
        (p.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2, p.2)
        p.1.1.1.2 p.1.2 :=
    firmRawPriorWorthData_prim.comp ((hctx.pair hj).pair hn)
  have hcoefficient : Primrec fun p : P =>
      (((p.1.1.2 : ℕ) : ℚ) + firmRawPriorWorthData
        (p.1.1.1.1.2,
          budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2, p.2)
        p.1.1.1.2 p.1.2)⁻¹ :=
    ratInv_prim.comp (ratAdd_prim.comp (natCastRat_prim.comp hb) hworth)
  have hvalue : Primrec fun p : P =>
      tradeListWorldValueFeatureData
        (budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2) p.2
        ((firmRawTrader p.1.1.1.2).strat p.1.2).trades p.1.2 :=
    tradeListWorldValueFeatureData_prim.comp
      (((hatoms.pair hxs).pair htrades).pair hn)
  exact (efSafeRecip_prim.comp
    (efMul_prim.comp (efConst_prim.comp hcoefficient)
      (efNeg_prim.comp hvalue))).of_eq fun p => by
        unfold budgetWorldScaleData
        rfl

end

private theorem budgetWorldScaleData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) (xs : List Bool) :
    budgetWorldScaleData ((((stages, past), j), b), n) xs =
      budgetWorldScaleTradeLists
        (fun i => ((firmRawTrader j).strat i).trades) b
        (rationalHistory past)
        (atomListTable (budgetAtomList stages j n) xs) n := by
  change EF.safeRecip (EF.mul
      (EF.const (((b : ℕ) : ℚ) + firmRawPriorWorthData
        (past, budgetAtomList stages j n, xs) j n)⁻¹)
      (EF.neg (tradeListWorldValueFeatureData
        (budgetAtomList stages j n) xs
        ((firmRawTrader j).strat n).trades n))) =
    EF.safeRecip (EF.mul
      (EF.const (((b : ℕ) : ℚ) + rawPriorWorthRatTradeLists
        (fun i => ((firmRawTrader j).strat i).trades)
        (rationalHistory past) (atomListTable (budgetAtomList stages j n) xs) n)⁻¹)
      (EF.neg (Strategy.tradeListWorldValueFeature
        ((firmRawTrader j).strat n).trades n
        (atomListTable (budgetAtomList stages j n) xs))))
  rw [firmRawPriorWorthData_eq,
    tradeListWorldValueFeatureData_eq]

private def budgetScaleFeaturesData (core : BudgetCoreInput) : List EF :=
  let atoms := budgetAtomList core.1.1.1.1 core.1.1.2 core.2
  (allBoolLists atoms.length).foldr (fun xs acc =>
    bif budgetConsistentAtDayData atoms xs core.1.1.1.1 core.2 then
      budgetWorldScaleData core xs :: acc
    else acc) []

private def budgetScaleFeatureData (core : BudgetCoreInput) : EF :=
  EF.listMin (budgetScaleFeaturesData core)

section
attribute [local irreducible] Nat.sqrt budgetScaleFeaturesData
  budgetScaleFeatureData budgetConsistentAtDayData budgetWorldScaleData
  budgetAtomList decodedStageTable tableConsistentFromAtomList

private theorem budgetScaleFeaturesData_prim :
    Primrec budgetScaleFeaturesData := by
  have hstages : Primrec fun core : BudgetCoreInput => core.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hj : Primrec fun core : BudgetCoreInput => core.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun core : BudgetCoreInput => core.2 := Primrec.snd
  have hatoms : Primrec fun core : BudgetCoreInput =>
      budgetAtomList core.1.1.1.1 core.1.1.2 core.2 :=
    budgetAtomList_prim.comp ((hstages.pair hj).pair hn)
  have hassignments : Primrec fun core : BudgetCoreInput =>
      allBoolLists
        (budgetAtomList core.1.1.1.1 core.1.1.2 core.2).length :=
    allBoolLists_prim.comp (Primrec.list_length.comp hatoms)
  have hconsistent : Primrec fun p : BudgetCoreInput × List Bool =>
      budgetConsistentAtDayData
        (budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2)
        p.2 p.1.1.1.1.1 p.1.2 :=
    budgetConsistentAtDayData_prim.comp
      ((((hatoms.comp Primrec.fst).pair Primrec.snd).pair
        (hstages.comp Primrec.fst)).pair (hn.comp Primrec.fst))
  have hstep : Primrec₂ fun (core : BudgetCoreInput)
      (q : List Bool × List EF) =>
      bif budgetConsistentAtDayData
          (budgetAtomList core.1.1.1.1 core.1.1.2 core.2)
          q.1 core.1.1.1.1 core.2 then
        budgetWorldScaleData core q.1 :: q.2
      else q.2 := by
    have htest : Primrec fun p : BudgetCoreInput × (List Bool × List EF) =>
        budgetConsistentAtDayData
          (budgetAtomList p.1.1.1.1.1 p.1.1.1.2 p.1.2)
          p.2.1 p.1.1.1.1.1 p.1.2 :=
      hconsistent.comp ((Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
    have hthen : Primrec fun p : BudgetCoreInput × (List Bool × List EF) =>
        budgetWorldScaleData p.1 p.2.1 :: p.2.2 :=
      Primrec.list_cons.comp
        (budgetWorldScaleData_prim.comp
          (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)
    exact (Primrec.cond htest hthen
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hassignments (Primrec.const []) hstep).of_eq
    fun core => by
      unfold budgetScaleFeaturesData
      rfl

private theorem budgetScaleFeatureData_prim :
    Primrec budgetScaleFeatureData := by
  exact (efListMin_prim.comp budgetScaleFeaturesData_prim).of_eq fun core => by
    unfold budgetScaleFeatureData
    rfl

end

private theorem firmBudgetBreachAtDayData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) (xs : List Bool) (m : ℕ) :
    firmBudgetBreachAtDayData ((((stages, past), j), b), n) xs m =
      (tableConsistent
          (finiteAtomTableFromList
            (budgetAtomsFromStageTradeLists (decodedStageTable stages)
              (fun i => ((firmRawTrader j).strat i).trades) n) xs)
          (decodedStageTable stages m) &&
        decide (rawWorthRatTradeLists
          (fun i => ((firmRawTrader j).strat i).trades)
          (rationalHistory past)
          (finiteAtomTableFromList
            (budgetAtomsFromStageTradeLists (decodedStageTable stages)
              (fun i => ((firmRawTrader j).strat i).trades) n) xs)
          m ≤ -(b : ℚ))) := by
  let A := budgetAtomsFromStageTradeLists (decodedStageTable stages)
    (fun i => ((firmRawTrader j).strat i).trades) n
  change
    (tableConsistentFromAtomList (budgetAtomList stages j n) xs
        (decodedStageTable stages m) &&
      decide (firmRawPriorWorthData
        (past, budgetAtomList stages j n, xs) j (m + 1) ≤ -(b : ℚ))) =
    (tableConsistent (finiteAtomTableFromList A xs)
        (decodedStageTable stages m) &&
      decide (rawWorthRatTradeLists
        (fun i => ((firmRawTrader j).strat i).trades)
        (rationalHistory past) (finiteAtomTableFromList A xs) m ≤ -(b : ℚ)))
  rw [budgetAtomList_eq]
  rw [tableConsistentFromAtomList_sort_eq, firmRawPriorWorthData_eq,
    atomListTable_sort_eq]
  rfl

private theorem firmBudgetAssignmentBreachesData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) (xs : List Bool) :
    firmBudgetAssignmentBreachesData ((((stages, past), j), b), n) xs =
      (List.range n).any fun m =>
        tableConsistent
            (finiteAtomTableFromList
              (budgetAtomsFromStageTradeLists (decodedStageTable stages)
                (fun i => ((firmRawTrader j).strat i).trades) n) xs)
            (decodedStageTable stages m) &&
          decide (rawWorthRatTradeLists
            (fun i => ((firmRawTrader j).strat i).trades)
            (rationalHistory past)
            (finiteAtomTableFromList
              (budgetAtomsFromStageTradeLists (decodedStageTable stages)
                (fun i => ((firmRawTrader j).strat i).trades) n) xs)
            m ≤ -(b : ℚ)) := by
  unfold firmBudgetAssignmentBreachesData
  apply List.any_congr rfl
  intro m
  exact firmBudgetBreachAtDayData_eq stages past j b n xs m

private theorem priorBudgetBreachData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) :
    priorBudgetBreachData ((((stages, past), j), b), n) =
      priorBudgetBreachFromStageTradeLists (decodedStageTable stages)
        (fun i => ((firmRawTrader j).strat i).trades) b
        (rationalHistory past) n := by
  unfold priorBudgetBreachData priorBudgetBreachFromStageTradeLists
  dsimp only
  rw [budgetAtomList_eq, Finset.length_sort]
  apply List.any_congr rfl
  intro xs
  exact firmBudgetAssignmentBreachesData_eq stages past j b n xs

private theorem budgetScaleFeatureData_eq
    (stages : List (Finset Sentence)) (past : List RationalBeliefState)
    (j b n : ℕ) :
    budgetScaleFeatureData ((((stages, past), j), b), n) =
      budgetScaleFeatureFromStageTradeLists (decodedStageTable stages)
        (fun i => ((firmRawTrader j).strat i).trades) b
        (rationalHistory past) n := by
  let A := budgetAtomsFromStageTradeLists (decodedStageTable stages)
    (fun i => ((firmRawTrader j).strat i).trades) n
  have hatoms : budgetAtomList stages j n = A.sort (fun a b => a ≤ b) :=
    budgetAtomList_eq stages j n
  have hconsistent (xs : List Bool) :
      budgetConsistentAtDayData (A.sort (fun a b => a ≤ b)) xs stages n =
        tableConsistent (finiteAtomTableFromList A xs)
          (decodedStageTable stages n) := by
    unfold budgetConsistentAtDayData
    exact tableConsistentFromAtomList_sort_eq A xs
      (decodedStageTable stages n)
  have hscale (xs : List Bool) :
      budgetWorldScaleData ((((stages, past), j), b), n) xs =
        budgetWorldScaleTradeLists
          (fun i => ((firmRawTrader j).strat i).trades) b
          (rationalHistory past) (finiteAtomTableFromList A xs) n := by
    rw [budgetWorldScaleData_eq, hatoms, atomListTable_sort_eq]
  unfold budgetScaleFeatureData budgetScaleFeaturesData
    budgetScaleFeatureFromStageTradeLists
  rw [hatoms]
  dsimp only
  rw [Finset.length_sort]
  apply congrArg EF.listMin
  generalize allBoolLists A.card = assignments
  induction assignments with
  | nil => rfl
  | cons xs rest ih =>
      rw [List.foldr_cons, hconsistent xs, hscale xs, List.filter_cons]
      cases h : tableConsistent (finiteAtomTableFromList A xs)
          (decodedStageTable stages n)
      · exact ih
      · exact congrArg
          (List.cons (budgetWorldScaleTradeLists
            (fun i => ((firmRawTrader j).strat i).trades) b
            (rationalHistory past) (finiteAtomTableFromList A xs) n)) ih

section
attribute [local irreducible] Nat.sqrt priorBudgetBreachData
  budgetScaleFeatureData

private theorem budgeterTradesFromStageTradeLists_prim : Primrec fun core :
    BudgetCoreInput =>
      budgeterTradesFromStageTradeLists
        (decodedStageTable core.1.1.1.1)
        (fun i => ((firmRawTrader core.1.1.2).strat i).trades)
        core.1.2 (rationalHistory core.1.1.1.2) core.2 := by
  have hj : Primrec fun core : BudgetCoreInput => core.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun core : BudgetCoreInput => core.2 := Primrec.snd
  have hraw : Primrec fun core : BudgetCoreInput =>
      ((firmRawTrader core.1.1.2).strat core.2).trades :=
    firmRawTraderTrades_prim.comp hj hn
  have htrade : Primrec₂ fun (core : BudgetCoreInput)
      (trade : EF × Sentence) =>
      (EF.mul (budgetScaleFeatureData core) trade.1, trade.2) :=
    Primrec₂.pair.comp₂
      (efMul_prim.comp₂
        (budgetScaleFeatureData_prim.comp₂ Primrec₂.left)
        (Primrec.fst.comp₂ Primrec₂.right))
        (Primrec.snd.comp₂ Primrec₂.right)
  have hscaled : Primrec fun core : BudgetCoreInput =>
      (((firmRawTrader core.1.1.2).strat core.2).trades.map fun trade =>
        (EF.mul (budgetScaleFeatureData core) trade.1, trade.2)) :=
    Primrec.list_map hraw htrade
  have hcompiled : Primrec fun core : BudgetCoreInput =>
      bif priorBudgetBreachData core then [] else
        ((firmRawTrader core.1.1.2).strat core.2).trades.map fun trade =>
          (EF.mul (budgetScaleFeatureData core) trade.1, trade.2) :=
    Primrec.cond priorBudgetBreachData_prim (Primrec.const []) hscaled
  exact hcompiled.of_eq fun core => by
    rcases core with ⟨⟨⟨⟨stages, past⟩, j⟩, b⟩, n⟩
    rw [priorBudgetBreachData_eq, budgetScaleFeatureData_eq]
    unfold budgeterTradesFromStageTradeLists
    cases priorBudgetBreachFromStageTradeLists (decodedStageTable stages)
      (fun i => ((firmRawTrader j).strat i).trades) b
      (rationalHistory past) n <;> rfl

end

private abbrev TradingFirmComponentInput :=
  ((List (Finset Sentence) × List RationalBeliefState) × ℕ) × ℕ

section
attribute [local irreducible] Nat.sqrt tradingFirmCutoffTradeLists
  budgeterTradesFromStageTradeLists

private theorem tradingFirmComponentTradesFromStageTradeLists_prim :
    Primrec fun p : TradingFirmComponentInput =>
      tradingFirmComponentTradesFromStageTradeLists
        (decodedStageTable p.1.1.1) (rationalHistory p.1.1.2)
        p.1.2 p.2 := by
  let P := TradingFirmComponentInput
  have hstages : Primrec fun p : P => p.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hpast : Primrec fun p : P => p.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hj : Primrec fun p : P => p.2 := Primrec.snd
  have hcutoff : Primrec fun p : P =>
      tradingFirmCutoffTradeLists p.1.2 :=
    tradingFirmCutoffTradeLists_prim.comp hn
  have hrange : Primrec fun p : P =>
      List.range (tradingFirmCutoffTradeLists p.1.2) :=
    Primrec.list_range.comp hcutoff
  have hbudget : Primrec₂ fun (p : P) (r : ℕ) =>
      budgeterTradesFromStageTradeLists
        (decodedStageTable p.1.1.1)
        (fun i => ((firmRawTrader p.2).strat i).trades)
        (r + 1) (rationalHistory p.1.1.2) p.1.2 := by
    have hcore : Primrec fun z : P × ℕ =>
        (((((z.1.1.1.1, z.1.1.1.2), z.1.2), z.2 + 1), z.1.1.2) :
          BudgetCoreInput) := by
      have hstages' : Primrec fun z : P × ℕ => z.1.1.1.1 :=
        hstages.comp Primrec.fst
      have hpast' : Primrec fun z : P × ℕ => z.1.1.1.2 :=
        hpast.comp Primrec.fst
      have hj' : Primrec fun z : P × ℕ => z.1.2 :=
        hj.comp Primrec.fst
      have hb' : Primrec fun z : P × ℕ => z.2 + 1 :=
        Primrec.nat_add.comp Primrec.snd (Primrec.const 1)
      have hn' : Primrec fun z : P × ℕ => z.1.1.2 :=
        hn.comp Primrec.fst
      exact (((hstages'.pair hpast').pair hj').pair hb').pair hn'
    exact (budgeterTradesFromStageTradeLists_prim.comp hcore).to₂
  have hweight : Primrec₂ fun (p : P) (r : ℕ) =>
      tradingFirmWeight p.2 (r + 1) :=
    tradingFirmWeight_prim.comp₂
      (hj.comp₂ Primrec₂.left)
      (Primrec.nat_add.comp₂ Primrec₂.right (Primrec₂.const 1))
  have hscaledBudget : Primrec₂ fun (p : P) (r : ℕ) =>
      scaleConstTradeList (tradingFirmWeight p.2 (r + 1))
        (budgeterTradesFromStageTradeLists
          (decodedStageTable p.1.1.1)
          (fun i => ((firmRawTrader p.2).strat i).trades)
          (r + 1) (rationalHistory p.1.1.2) p.1.2) :=
    scaleConstTradeList_prim.comp₂ hweight hbudget
  have hbudgets : Primrec fun p : P =>
      (List.range (tradingFirmCutoffTradeLists p.1.2)).flatMap fun r =>
        scaleConstTradeList (tradingFirmWeight p.2 (r + 1))
          (budgeterTradesFromStageTradeLists
            (decodedStageTable p.1.1.1)
            (fun i => ((firmRawTrader p.2).strat i).trades)
            (r + 1) (rationalHistory p.1.1.2) p.1.2) :=
    Primrec.list_flatMap hrange hscaledBudget
  have htailWeight : Primrec fun p : P =>
      tradingFirmWeight p.2 (tradingFirmCutoffTradeLists p.1.2) :=
    tradingFirmWeight_prim.comp hj hcutoff
  have htailRaw : Primrec fun p : P =>
      ((firmRawTrader p.2).strat p.1.2).trades :=
    firmRawTraderTrades_prim.comp hj hn
  have htail : Primrec fun p : P =>
      scaleConstTradeList
        (tradingFirmWeight p.2 (tradingFirmCutoffTradeLists p.1.2))
        ((firmRawTrader p.2).strat p.1.2).trades :=
    scaleConstTradeList_prim.comp htailWeight htailRaw
  exact (Primrec.list_append.comp hbudgets htail).of_eq fun p => by
    unfold tradingFirmComponentTradesFromStageTradeLists
    rfl

end

private abbrev TradingFirmInput :=
  (List (Finset Sentence) × List RationalBeliefState) × ℕ

section
attribute [local irreducible] Nat.sqrt
  tradingFirmComponentTradesFromStageTradeLists

private theorem tradingFirmTradesFromStageTradeLists_prim :
    Primrec fun p : TradingFirmInput =>
      tradingFirmTradesFromStageTradeLists
        (decodedStageTable p.1.1) (rationalHistory p.1.2) p.2 := by
  let P := TradingFirmInput
  have hrange : Primrec fun p : P => List.range (p.2 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have hcomponent : Primrec₂ fun (p : P) (j : ℕ) =>
      tradingFirmComponentTradesFromStageTradeLists
        (decodedStageTable p.1.1) (rationalHistory p.1.2) p.2 j := by
    have hinput : Primrec fun z : P × ℕ =>
        ((((z.1.1.1, z.1.1.2), z.1.2), z.2) :
          TradingFirmComponentInput) :=
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
    exact (tradingFirmComponentTradesFromStageTradeLists_prim.comp hinput).to₂
  exact (Primrec.list_flatMap hrange hcomponent).of_eq fun p => by
    unfold tradingFirmTradesFromStageTradeLists
    rfl

end

private theorem marketMakerError_prim : Primrec marketMakerError := by
  have hexponent : Primrec fun n : ℕ => n + 1 :=
    Primrec.nat_add.comp Primrec.id (Primrec.const 1)
  have hpow : Primrec fun n : ℕ => (2 : ℚ) ^ (n + 1) :=
    ratPow_prim.comp (Primrec.const 2) hexponent
  exact (ratDiv_prim.comp (Primrec.const 1) hpow).of_eq fun n => by
    rfl

section
attribute [local irreducible] Nat.sqrt liaPrefixFromTradeListsAtFuel
  tradingFirmTradesFromStageTradeLists marketMakerSearchUpToTradeList

private theorem liaPrefixFromTradeListsAtFuel_prim : Primrec fun p :
    (List (Finset Sentence) × ℕ) × ℕ =>
      liaPrefixFromTradeListsAtFuel
        (decodedStageTable p.1.1) p.1.2 p.2 := by
  let C := List (Finset Sentence) × ℕ
  have hbase : Primrec fun _ctx : C =>
      (some [] : Option (List RationalBeliefState)) :=
    Primrec.const (some [])
  have hstep : Primrec₂ fun (ctx : C)
      (ni : ℕ × Option (List RationalBeliefState)) =>
      ni.2.bind fun past =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable ctx.1) (rationalHistory past) ni.1)
          ni.1 past (marketMakerError ni.1) ctx.2).bind fun state =>
            some (past ++ [state]) := by
    let X := C × (ℕ × Option (List RationalBeliefState))
    have hfirm : Primrec₂ fun (x : X)
        (past : List RationalBeliefState) =>
        tradingFirmTradesFromStageTradeLists
          (decodedStageTable x.1.1) (rationalHistory past) x.2.1 := by
      have hinput : Primrec fun z : X × List RationalBeliefState =>
          (((z.1.1.1, z.2), z.1.2.1) : TradingFirmInput) :=
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          Primrec.snd).pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      exact (tradingFirmTradesFromStageTradeLists_prim.comp hinput).to₂
    have hsearch : Primrec₂ fun (x : X)
        (past : List RationalBeliefState) =>
        marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1)
          x.2.1 past (marketMakerError x.2.1) x.1.2 := by
      have htrades : Primrec fun z : X × List RationalBeliefState =>
          tradingFirmTradesFromStageTradeLists
            (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1 :=
        hfirm.comp Primrec.fst Primrec.snd
      have hn : Primrec fun z : X × List RationalBeliefState => z.1.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      have hpast : Primrec fun z : X × List RationalBeliefState => z.2 :=
        Primrec.snd
      have hepsilon : Primrec fun z : X × List RationalBeliefState =>
          marketMakerError z.1.2.1 :=
        marketMakerError_prim.comp hn
      have hfuel : Primrec fun z : X × List RationalBeliefState => z.1.1.2 :=
        Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
      have hinput : Primrec fun z : X × List RationalBeliefState =>
          (((((tradingFirmTradesFromStageTradeLists
              (decodedStageTable z.1.1.1) (rationalHistory z.2) z.1.2.1,
            z.1.2.1), z.2), marketMakerError z.1.2.1),
              z.1.1.2) : MarketMakerSearchInput × ℕ) :=
        (((htrades.pair hn).pair hpast).pair hepsilon).pair hfuel
      exact (marketMakerSearchUpToTradeList_prim.comp hinput).to₂
    have hout : Primrec₂ fun
        (y : (X × List RationalBeliefState))
        (state : RationalBeliefState) =>
        some (y.2 ++ [state]) :=
      Primrec₂.option_some_iff.mpr
        (Primrec.list_concat.comp₂
          (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right)
    have hinner : Primrec₂ fun (x : X)
        (past : List RationalBeliefState) =>
        (marketMakerSearchUpToTradeList
          (tradingFirmTradesFromStageTradeLists
            (decodedStageTable x.1.1) (rationalHistory past) x.2.1)
          x.2.1 past (marketMakerError x.2.1) x.1.2).bind fun state =>
            some (past ++ [state]) :=
      (Primrec.option_bind
        (hsearch.comp Primrec.fst Primrec.snd) hout).to₂
    exact (Primrec.option_bind
      (Primrec.snd.comp Primrec.snd) hinner).to₂
  have hrec : Primrec₂ fun (ctx : C) n =>
      liaPrefixFromTradeListsAtFuel
        (decodedStageTable ctx.1) ctx.2 n := by
    exact (Primrec.nat_rec hbase hstep).of_eq fun ctx n => by
      induction n with
      | zero => simp [liaPrefixFromTradeListsAtFuel]
      | succ n ih => simp [liaPrefixFromTradeListsAtFuel, ih]
  exact hrec.comp Primrec.fst Primrec.snd

end

/-- The proof-carrying finite-stage recurrence has the same primitive-recursive
first-order implementation as its fully erased trade-list presentation. -/
private theorem liaPrefixFromStagesAtFuel_prim : Primrec fun p :
    (List (Finset Sentence) × ℕ) × ℕ =>
      liaPrefixFromStagesAtFuel
        (decodedStageTable p.1.1) p.1.2 p.2 := by
  exact liaPrefixFromTradeListsAtFuel_prim.of_eq fun p => by
    rw [liaPrefixFromTradeListsAtFuel_eq,
      liaPrefixFromStageListsAtFuel_eq]

/-- The complete common-clock LIA state-prefix evaluator is primitive recursive. -/
private theorem liaPrefixAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ fun fuel n => liaPrefixAtFuel process fuel n := by
  let X := ℕ × ℕ
  have hstages : Primrec fun x : X =>
      processStagePrefixAtFuel process x.1 x.2 :=
    (processStagePrefixAtFuel_prim process).comp Primrec.fst Primrec.snd
  have hrun : Primrec₂ fun (x : X) (stages : List (Finset Sentence)) =>
      liaPrefixFromStagesAtFuel
        (decodedStageTable stages) x.1 x.2 := by
    have hinput : Primrec fun z : X × List (Finset Sentence) =>
        (((z.2, z.1.1), z.1.2) :
          (List (Finset Sentence) × ℕ) × ℕ) :=
      ((Primrec.snd.pair
        (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.fst))
    exact (liaPrefixFromStagesAtFuel_prim.comp hinput).to₂
  exact ((Primrec.option_bind hstages hrun).to₂).of_eq fun fuel n => by
    rfl

section
attribute [local irreducible] Nat.sqrt liaEncodedQuoteAtFuel

/-- The bounded exact rational quote evaluator is primitive recursive in its common
clock, day, and external sentence code. -/
private theorem liaEncodedQuoteAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) : Primrec fun p :
    (ℕ × ℕ) × ℕ =>
      liaEncodedQuoteAtFuel process p.1.1 p.1.2 p.2 := by
  let P := (ℕ × ℕ) × ℕ
  have hfuel : Primrec fun p : P => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hday : Primrec fun p : P => p.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hdaySucc : Primrec fun p : P => p.1.2 + 1 :=
    Primrec.nat_add.comp hday (Primrec.const 1)
  have hprefix : Primrec fun p : P =>
      liaPrefixAtFuel process p.1.1 (p.1.2 + 1) :=
    (liaPrefixAtFuel_prim process).comp hfuel hdaySucc
  let Y := P × List RationalBeliefState
  have hlookup : Primrec fun y : Y => y.2[y.1.1.2]? :=
    Primrec.list_getElem?.comp Primrec.snd
      (hday.comp Primrec.fst)
  have hfinish : Primrec₂ fun (y : Y) (state : RationalBeliefState) =>
      some (match Encodable.decode (α := Sentence) y.1.2 with
        | some phi => state.quote phi
        | none => 0) := by
    let Z := Y × RationalBeliefState
    have hdecode : Primrec fun z : Z =>
        Encodable.decode (α := Sentence) z.1.1.2 :=
      (Primrec.decode : Primrec fun n : ℕ =>
        Encodable.decode (α := Sentence) n).comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hquote : Primrec₂ fun (z : Z) (phi : Sentence) =>
        z.2.quote phi :=
      rationalBeliefStateQuote_prim.comp₂
        (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
    let valueCompiled : Z → ℚ := fun z =>
      Option.casesOn (Encodable.decode (α := Sentence) z.1.1.2)
        (0 : ℚ) fun phi => z.2.quote phi
    have hvalueCompiled : Primrec valueCompiled :=
      Primrec.option_casesOn hdecode (Primrec.const 0) hquote
    have hvalue : Primrec fun z : Z =>
        match Encodable.decode (α := Sentence) z.1.1.2 with
        | some phi => z.2.quote phi
        | none => 0 := hvalueCompiled.of_eq fun z => by
      unfold valueCompiled
      cases Encodable.decode (α := Sentence) z.1.1.2 <;> rfl
    exact Primrec₂.option_some_iff.mpr hvalue.to₂
  have hinner : Primrec₂ fun (p : P)
      (states : List RationalBeliefState) =>
      states[p.1.2]?.bind fun state =>
        some (match Encodable.decode (α := Sentence) p.2 with
          | some phi => state.quote phi
          | none => 0) :=
    (Primrec.option_bind hlookup hfinish).to₂
  exact (Primrec.option_bind hprefix hinner).of_eq fun p => by
    unfold liaEncodedQuoteAtFuel
    rfl

end

section
attribute [local irreducible] Nat.sqrt liaEncodedQuoteNatAtFuel

/-- The natural-coded bounded evaluator is primitive recursive in the paired
day/sentence input and its common fuel clock. -/
private theorem liaEncodedQuoteNatAtFuel_prim {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Primrec₂ (liaEncodedQuoteNatAtFuel process) := by
  let X := ℕ × ℕ
  have hleft : Primrec fun p : X => p.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hright : Primrec fun p : X => p.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hinput : Primrec fun p : X =>
      (((p.2, p.1.unpair.1), p.1.unpair.2) : (ℕ × ℕ) × ℕ) :=
    (Primrec.snd.pair hleft).pair hright
  have hquote : Primrec fun p : X =>
      liaEncodedQuoteAtFuel process p.2 p.1.unpair.1 p.1.unpair.2 :=
    liaEncodedQuoteAtFuel_prim process |>.comp hinput
  have hencode : Primrec₂ fun (_p : X) (q : ℚ) =>
      Encodable.encode q :=
    Primrec.encode.comp₂ Primrec₂.right
  exact ((Primrec.option_map hquote hencode).to₂).of_eq fun z fuel => by
    unfold liaEncodedQuoteNatAtFuel
    rfl

end


/-- Concrete computability certificate for the sole bounded-evaluator boundary in the
core LIA construction. -/
theorem liaEncodedQuoteNatAtFuel_computable {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    Computable₂ (liaEncodedQuoteNatAtFuel process) :=
  (liaEncodedQuoteNatAtFuel_prim process).to_comp

/-- The concrete bounded evaluator compiler assembled from the primitive-recursive
first-order implementation above. -/
def liaBoundedEvaluatorCompiler {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) :
    LIABoundedEvaluatorCompiler process where
  computable := liaEncodedQuoteNatAtFuel_computable process

/-- `thm:lia`: the recursively constructed rational LIA market is a logical inductor
over every computable deductive process. -/
theorem LIA_is_logical_inductor (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    IsLogicalInductor (liaHistory DP) DP := by
  obtain ⟨process⟩ := hDP.nonemptyComputation
  exact lia_isLogicalInductor_of_compiler process
    (liaBoundedEvaluatorCompiler process)

/-- `thm:li`: every computable deductive process admits a logical inductor. -/
theorem exists_logical_inductor (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) :
    ∃ P : History, IsLogicalInductor P DP :=
  ⟨liaHistory DP, LIA_is_logical_inductor DP hDP⟩

#print axioms liaEncodedQuoteNatAtFuel_computable
#print axioms LIA_is_logical_inductor
#print axioms exists_logical_inductor

end LogicalInduction
