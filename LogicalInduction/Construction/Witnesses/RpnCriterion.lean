/-
# The symbol-metered criterion layer (`Tok₃`, part 4: inclusions)

The two model inclusions into the symbol-metered class: a token-model or digit-model
certificate transfers by the escape splice — every sentence-slot token is prefixed by
the escape tag, a poly digit-level rewrite whose contracted decode is the original
strategy (`strategyOfTokens_unRpn_escExpand`).

Paper node: `def:ec` (symbol-metered sentence slots).
-/
import LogicalInduction.Construction.Witnesses.DigitConditioning
import LogicalInduction.Framework.RpnEmission
import LogicalInduction.Framework.RpnComputation

namespace LogicalInduction

open Nat.Partrec (Code)
open Nat.Partrec.Code

attribute [local irreducible] Nat.sqrt

/-- **Digit-metered certificates are symbol-metered** (`Tok₂ ⊆ Tok₃`): the escape
splice transfers the certificate verbatim.
Paper node: `def:ec` -/
theorem EfficientlyComputableTok₂.toTok₃ {Tr : Trader}
    (h : EfficientlyComputableTok₂ Tr) : EfficientlyComputableTok₃ Tr := by
  obtain ⟨lc, tc, a, k, hTr⟩ := h
  let ds : ℕ → List ℕ := fun n =>
    clockedTokens lc tc (PrefixPatchCompile.ecClock a k n) n
  have hds : PolySegStream ds :=
    PrefixPatchCompile.clockedTokens_polySegStream lc tc a k
  obtain ⟨⟨cc, hcnt⟩, hbig⟩ := hds.undigitizeTokens
  obtain ⟨cm, hmode⟩ := hds.escModeScan
  obtain ⟨cad, had⟩ := addc_polyFueled
  obtain ⟨cml, hml⟩ := mul_polyFueled
  -- Per-position digit segment: escape-prefix the sentence slots.
  have hcopy := hbig.blockSeg
  have hesc := (PolySegStream.block (PolyFueled.const 1)).append hcopy
  have heq1 := had.comp ((subc_polyFueled.comp (hmode.pair (PolyFueled.const 1))).pair
    (subc_polyFueled.comp ((PolyFueled.const 1).pair hmode)))
  have heq3 := had.comp ((subc_polyFueled.comp (hmode.pair (PolyFueled.const 3))).pair
    (subc_polyFueled.comp ((PolyFueled.const 3).pair hmode)))
  have hsel := hml.comp (heq1.pair heq3)
  have hseg := hesc.ifZero hcopy hsel
  have hassembled := hseg.concatVar hcnt
  have hclean : PolySegStream (fun n => digitize (escExpand (undigitize (ds n)))) := by
    refine hassembled.of_eq fun n => ?_
    have hget : ∀ i, i < (undigitize (ds n)).length →
        (fun w => (undigitize (ds w.unpair.1)).getD w.unpair.2 0) (Nat.pair n i) =
          (undigitize (ds n)).getD i 0 := fun i _ => by
      simp only [Nat.unpair_pair]
    rw [escExpand_eq_flatMap
        (tf := fun w => (undigitize (ds w.unpair.1)).getD w.unpair.2 0)
        (n := n) hget,
      ConditioningCompile.digitize_flatMap]
    refine List.flatMap_congr fun j hj => ?_
    simp only [Nat.unpair_pair]
    by_cases hm : escModeList (vpre
        (fun w => (undigitize (ds w.unpair.1)).getD w.unpair.2 0) n j) = 1 ∨
        escModeList (vpre
        (fun w => (undigitize (ds w.unpair.1)).getD w.unpair.2 0) n j) = 3
    · rw [if_pos (by
        rcases hm with hm | hm <;> rw [hm] <;> norm_num), if_pos hm]
      simp [digitize]
    · rw [if_neg (by
        push_neg at hm
        simp only [Nat.mul_eq_zero]
        omega), if_neg hm]
      simp [digitize]
  apply ecTok₃_of_rawSegStream Tr hclean
  intro n
  rw [undigitize_digitize, strategyOfTokens_unRpn_escExpand]
  exact congrFun (congrArg Trader.strat hTr) n

/-- **Token-model certificates are symbol-metered** (`Tok ⊆ Tok₃`), through the digit
inclusion.
Paper node: `def:ec` -/
theorem EfficientlyComputableTok.toTok₃ {Tr : Trader}
    (h : EfficientlyComputableTok Tr) : EfficientlyComputableTok₃ Tr :=
  h.toTok₂.toTok₃

/-! ## Primitive recursion of the decode

The trading firm's compiler runs the symbol-metered decode; with the concrete
`Primcodable Sentence` instance in scope the strong-recursion steps assemble from
standard combinators. -/

private abbrev PCtx :=
  (List (Option (ℕ × List ℕ)) × ℕ) × (ℕ × List ℕ)

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
      x.2.2.head?.bind fun c =>
        if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
        else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1,
          x.2.2.tail) := by
    refine Primrec.option_bind (Primrec.list_head?.comp hrest) ?_
    have he : Primrec fun y : PCtx × ℕ =>
        Encodable.encode (Encodable.decode (α := Sentence) y.2) :=
      (Primrec.encdec.comp Primrec.snd).of_eq fun y => rfl
    exact (Primrec.ite (PrimrecRel.comp Primrec.eq he (Primrec.const 0))
      (Primrec.const none)
      (Primrec.option_some.comp ((Primrec.pred.comp he).pair
        (Primrec.list_tail.comp (hrest.comp Primrec.fst))))).to₂
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
        x.2.2.head?.bind fun c =>
          if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then none
          else some (Encodable.encode (Encodable.decode (α := Sentence) c) - 1,
            x.2.2.tail)
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
            rest.head?.bind fun c =>
              if Encodable.encode (Encodable.decode (α := Sentence) c) = 0 then
                none
              else some
                (Encodable.encode (Encodable.decode (α := Sentence) c) - 1,
                  rest.tail)
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
      | cons t rest => simp [hts]

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

#print axioms parseRpnC_prim
#print axioms EfficientlyComputableTok₂.toTok₃
#print axioms EfficientlyComputableTok.toTok₃

end LogicalInduction
