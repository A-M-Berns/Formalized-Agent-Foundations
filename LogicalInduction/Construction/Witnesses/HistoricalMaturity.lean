import LogicalInduction.Construction.Witnesses.M7Witnesses

/-!
# Uniform historical-maturity verification

This file discharges the computational boundary isolated by
`AffineCombination.BiasRunHistoricallyVerifiable`.  The semantic finite maturity checker
lives in `Properties.Calibration`; here it is compiled for a uniformly emulatable trader
family, placed behind the generic bounded dovetail, and packaged as the historical
verification schedule consumed by repeatable ROI.
-/

namespace LogicalInduction
namespace HistoricalMaturityCompile

private def markerSentence : Sentence := LO.Propositional.Formula.atom 0

/-- The structured polynomial interface on a trader family entails primitive-recursive
access to every member/day trade list.  This is the trader-family analogue of
`AffineCombination.PolySequence.primrec`. -/
lemma PolyTradeEmulatable.trades_primrec {Ts : ℕ → Trader}
    (h : PolyTradeEmulatable Ts) :
    Primrec fun z : ℕ => ((Ts z.unpair.1).strat z.unpair.2).trades := by
  have hcount : Primrec h.tradeCount := by
    obtain ⟨c, hc⟩ := h.tradeCount_poly
    exact hc.primrec
  have hcoefficientTokens : Primrec fun z => (h.coefficient z).serialize := by
    obtain ⟨s, hs, hcontract⟩ := h.coefficient_poly
    refine (unRpn_prim.comp hs.primrec).of_eq fun z => ?_
    have h0 := (hcontract z).unRpn_eq
    rwa [show unRpn ([] : List ℕ) = [] from rfl, List.append_nil] at h0
  have hcoefficient : Primrec h.coefficient :=
    (efFromSerializedTokens_prim.comp hcoefficientTokens).of_eq fun z =>
      efFromSerializedTokens_serialize (h.coefficient z)
  have hsentenceCode : Primrec fun z => Encodable.encode (h.sentence z) := by
    obtain ⟨s, hs, hp⟩ := h.sentence_poly
    have hlist := hs.primrec
    have hparse : Primrec fun z => parseRpnC (s z).length (s z) :=
      parseRpnC_prim.comp (Primrec.list_length.comp hlist) hlist
    refine (Primrec.fst.comp (Primrec.option_getD.comp hparse
      (Primrec.const ((0, []) : ℕ × List ℕ)))).of_eq fun z => ?_
    rw [show parseRpnC (s z).length (s z) =
        some (Encodable.encode (h.sentence z), []) by
      rw [parseRpnC_eq, hp z]; rfl]
    rfl
  have hsentence : Primrec h.sentence := by
    have hdecode : Primrec fun z =>
        (Encodable.decode (Encodable.encode (h.sentence z))).getD markerSentence :=
      Primrec.option_getD.comp (Primrec.decode.comp hsentenceCode)
        (Primrec.const markerSentence)
    exact hdecode.of_eq fun z => by rw [Encodable.encodek]; rfl
  have hrange : Primrec fun z => List.range (h.tradeCount z) :=
    Primrec.list_range.comp hcount
  have htrade : Primrec₂ fun z j =>
      (h.coefficient (Nat.pair z j), h.sentence (Nat.pair z j)) :=
    ((hcoefficient.comp Primrec₂.natPair).pair
      (hsentence.comp Primrec₂.natPair)).to₂
  have hraw : Primrec fun z =>
      (List.range (h.tradeCount z)).map fun j =>
        (h.coefficient (Nat.pair z j), h.sentence (Nat.pair z j)) :=
    Primrec.list_map hrange htrade
  exact hraw.of_eq fun z => by
    simpa using (h.trades_eq z.unpair.1 z.unpair.2).symm

/-! ## Primitive-recursive finite-prefix data -/

private def ratNeg (q : ℚ) : ℚ := (-1) * q

private lemma ratNeg_prim : Primrec ratNeg := by
  exact (ratMul_prim.comp (Primrec.const (-1)) Primrec.id).of_eq fun q => by
    simp [ratNeg]

private def ratSub (q r : ℚ) : ℚ := q + ratNeg r

private lemma ratSub_prim : Primrec₂ ratSub := by
  exact (ratAdd_prim.comp₂ Primrec₂.left
    (ratNeg_prim.comp₂ Primrec₂.right)).of_eq fun _ _ => rfl

private def ratAbs (q : ℚ) : ℚ := if 0 ≤ q then q else ratNeg q

private lemma ratAbs_eq (q : ℚ) : ratAbs q = |q| := by
  by_cases h : 0 ≤ q
  · simp [ratAbs, h, abs_of_nonneg h]
  · have hq : q ≤ 0 := le_of_lt (lt_of_not_ge h)
    simp [ratAbs, h, abs_of_nonpos hq, ratNeg]

private lemma ratAbs_prim : Primrec ratAbs := by
  exact (Primrec.ite
    (ratLE_prim.comp (Primrec.const 0) Primrec.id)
    Primrec.id ratNeg_prim).of_eq fun q => by rfl

private lemma natListSum_prim : Primrec (fun l : List ℕ => l.sum) := by
  have h := Primrec.list_foldr (f := fun l : List ℕ => l)
    (g := fun _ : List ℕ => 0) Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun l => by
    induction l with
    | nil => rfl
    | cons a t ih => simp [List.sum_cons, ← ih]

private def tradeAtomBoundSum (trades : List (EF × Sentence)) : ℕ :=
  (trades.map fun p => BoolPCWorld.atomBound p.2).sum

private lemma tradeAtomBoundSum_prim : Primrec tradeAtomBoundSum := by
  exact (natListSum_prim.comp
    (Primrec.list_map Primrec.id
      (atomBound_prim.comp (Primrec.snd.comp₂ Primrec₂.right)).to₂)).of_eq
    fun _ => rfl

/-- Support bound for a family member's strategies through day `m`, excluding the
deductive stage. -/
def familyTradeAtomLimit {Ts : ℕ → Trader} (i m : ℕ) : ℕ :=
  ((List.range (m + 1)).map fun d =>
    tradeAtomBoundSum ((Ts i).strat d).trades).sum

lemma familyTradeAtomLimit_prim {Ts : ℕ → Trader}
    (h : PolyTradeEmulatable Ts) :
    Primrec₂ (familyTradeAtomLimit (Ts := Ts)) := by
  have hrange : Primrec fun p : ℕ × ℕ => List.range (p.2 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have hday : Primrec₂ fun (p : ℕ × ℕ) (d : ℕ) =>
      tradeAtomBoundSum ((Ts p.1).strat d).trades :=
    ((tradeAtomBoundSum_prim.comp
      (PolyTradeEmulatable.trades_primrec h |>.comp
        (Primrec₂.natPair.comp (Primrec.fst.comp₂ Primrec₂.left)
          Primrec₂.right))).to₂).of_eq fun p d => by rw [Nat.unpair_pair]
  have hmap : Primrec fun p : ℕ × ℕ =>
      (List.range (p.2 + 1)).map fun d =>
        tradeAtomBoundSum ((Ts p.1).strat d).trades :=
    Primrec.list_map hrange hday
  exact (natListSum_prim.comp hmap).to₂.of_eq fun _ _ => rfl

/-- Fully executable support bound, using the decoded deductive stage. -/
def familyMaturityAtomLimit {Ts : ℕ → Trader}
    (i : ℕ) (stage : Finset Sentence) (m : ℕ) : ℕ :=
  stage.sum BoolPCWorld.atomBound + familyTradeAtomLimit (Ts := Ts) i m

lemma familyMaturityAtomLimit_eq {Ts : ℕ → Trader}
    (i : ℕ) (stage : Finset Sentence) (m : ℕ) :
    familyMaturityAtomLimit (Ts := Ts) i stage m =
      AffineCombination.maturityAtomLimitFromStage (Ts i) stage m := by
  rw [familyMaturityAtomLimit, AffineCombination.maturityAtomLimitFromStage,
    finset_sum_eq_stageSort_sum]
  rfl

lemma familyMaturityAtomLimit_prim {Ts : ℕ → Trader}
    (h : PolyTradeEmulatable Ts) :
    Primrec fun q : (ℕ × Finset Sentence) × ℕ =>
      familyMaturityAtomLimit (Ts := Ts) q.1.1 q.1.2 q.2 := by
  have hstage : Primrec fun q : (ℕ × Finset Sentence) × ℕ =>
      ((stageSort q.1.2).map BoolPCWorld.atomBound).sum :=
    natListSum_prim.comp
      (Primrec.list_map (stageSort_prim.comp (Primrec.snd.comp Primrec.fst))
        (atomBound_prim.comp Primrec.snd).to₂)
  have htrades : Primrec fun q : (ℕ × Finset Sentence) × ℕ =>
      familyTradeAtomLimit (Ts := Ts) q.1.1 q.2 :=
    (familyTradeAtomLimit_prim h |>.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd)
  exact (Primrec.nat_add.comp hstage htrades).of_eq fun q => by
    rw [familyMaturityAtomLimit, finset_sum_eq_stageSort_sum]

/-! ## Compiled rational risk and payoff folds -/

/-- Every trade through day `m`, tagged by the day on which it was placed. -/
def familyDatedTrades {Ts : ℕ → Trader} (i m : ℕ) :
    List (ℕ × (EF × Sentence)) :=
  (List.range (m + 1)).flatMap fun d =>
    ((Ts i).strat d).trades.map fun p => (d, p)

lemma familyDatedTrades_prim {Ts : ℕ → Trader}
    (h : PolyTradeEmulatable Ts) :
    Primrec₂ (familyDatedTrades (Ts := Ts)) := by
  have hrange : Primrec fun p : ℕ × ℕ => List.range (p.2 + 1) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have hpfirst : Primrec₂ fun (p : ℕ × ℕ) (_d : ℕ) => p.1 :=
    (Primrec.fst.comp₂ (Primrec₂.left : Primrec₂ fun (p : ℕ × ℕ) (_d : ℕ) => p))
  have hindex : Primrec₂ fun (p : ℕ × ℕ) (d : ℕ) => Nat.pair p.1 d :=
    Primrec₂.natPair.comp hpfirst Primrec₂.right
  have htrades : Primrec₂ fun (p : ℕ × ℕ) (d : ℕ) =>
      ((Ts p.1).strat d).trades := by
    have hraw := (PolyTradeEmulatable.trades_primrec h).comp hindex
    exact hraw.to₂.of_eq fun p d => by rw [Nat.unpair_pair]
  have hday : Primrec₂ fun (p : ℕ × ℕ) (d : ℕ) =>
      ((Ts p.1).strat d).trades.map fun x => (d, x) := by
    have htrades' : Primrec fun q : (ℕ × ℕ) × ℕ =>
        ((Ts q.1.1).strat q.2).trades := htrades
    have htag : Primrec₂ fun (q : (ℕ × ℕ) × ℕ)
        (x : EF × Sentence) => (q.2, x) := by
      exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact (Primrec.list_map htrades' htag).to₂
  exact (Primrec.list_flatMap hrange hday).to₂.of_eq fun _ _ => rfl

/-- Fuel-bounded magnitude of a dated trade list.  The date tags are ignored for risk;
they are retained so the same prefix representation can feed payoff computation. -/
def datedMagnitudeComp {P : History} (market : MarketComputation P) (fuel : ℕ)
    (trades : List (ℕ × (EF × Sentence))) : Option ℚ :=
  trades.foldr (fun p acc =>
    (market.denoteRatComp fuel p.2.1).bind fun coefficient =>
      acc.map fun tail => ratAbs coefficient + tail) (some 0)

/-- Fuel-bounded net worth of a dated trade list at a finite Boolean world. -/
def datedValueComp {P : History} (market : MarketComputation P) (fuel : ℕ)
    (bits : List Bool) (trades : List (ℕ × (EF × Sentence))) : Option ℚ :=
  trades.foldr (fun p acc =>
    (market.denoteRatComp fuel p.2.1).bind fun coefficient =>
      (market.quoteAtFuel fuel p.1 p.2.2).bind fun price =>
        acc.map fun tail => coefficient *
          ratSub (BoolPCWorld.bitsPayoutRat bits p.2.2) price + tail) (some 0)

section
attribute [local irreducible] Nat.sqrt

lemma datedMagnitudeComp_prim {P : History} (market : MarketComputation P) :
    Primrec fun q : ℕ × List (ℕ × (EF × Sentence)) =>
      datedMagnitudeComp market q.1 q.2 := by
  let Q := ℕ × List (ℕ × (EF × Sentence))
  have hcoefficient : Primrec fun z : Q ×
      ((ℕ × (EF × Sentence)) × Option ℚ) =>
      market.denoteRatComp z.1.1 z.2.1.2.1 :=
    market.denoteRatComp_prim.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hmap : Primrec₂ fun (z : Q ×
      ((ℕ × (EF × Sentence)) × Option ℚ)) (coefficient : ℚ) =>
      z.2.2.map fun tail => ratAbs coefficient + tail :=
    (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (ratAdd_prim.comp (ratAbs_prim.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd).to₂).to₂
  have hstep : Primrec₂ fun (q : Q)
      (x : (ℕ × (EF × Sentence)) × Option ℚ) =>
      (market.denoteRatComp q.1 x.1.2.1).bind fun coefficient =>
        x.2.map fun tail => ratAbs coefficient + tail :=
    (Primrec.option_bind hcoefficient hmap).to₂
  exact (Primrec.list_foldr Primrec.snd (Primrec.const (some 0)) hstep).of_eq
    fun q => by simp only [datedMagnitudeComp]

lemma datedValueComp_prim {P : History} (market : MarketComputation P) :
    Primrec fun q : (ℕ × List Bool) ×
        List (ℕ × (EF × Sentence)) =>
      datedValueComp market q.1.1 q.1.2 q.2 := by
  let Q := (ℕ × List Bool) × List (ℕ × (EF × Sentence))
  let X := (ℕ × (EF × Sentence)) × Option ℚ
  have hcoefficient : Primrec fun z : Q × X =>
      market.denoteRatComp z.1.1.1 z.2.1.2.1 :=
    market.denoteRatComp_prim.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hprice : Primrec fun z : Q × X =>
      market.quoteAtFuel z.1.1.1 z.2.1.1 z.2.1.2.2 :=
    quoteAtFuel_prim market |>.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))
  have hpayout : Primrec fun z : Q × X =>
      BoolPCWorld.bitsPayoutRat z.1.1.2 z.2.1.2.2 :=
    bitsPayoutRat_prim.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  -- Insert multiplication by the coefficient after both partial computations succeed.
  have hfull : Primrec₂ fun (z : Q × X) (coefficient : ℚ) =>
      (market.quoteAtFuel z.1.1.1 z.2.1.1 z.2.1.2.2).bind fun price =>
        z.2.2.map fun tail => coefficient *
          ratSub (BoolPCWorld.bitsPayoutRat z.1.1.2 z.2.1.2.2) price + tail := by
    have hmap : Primrec₂ fun (w : (Q × X) × ℚ) (price : ℚ) =>
        w.1.2.2.map fun tail => w.2 *
          ratSub (BoolPCWorld.bitsPayoutRat w.1.1.1.2 w.1.2.1.2.2) price + tail := by
      have hterm : Primrec fun v : ((Q × X) × ℚ) × ℚ =>
          v.1.2 * ratSub
            (BoolPCWorld.bitsPayoutRat v.1.1.1.1.2 v.1.1.2.1.2.2) v.2 :=
        ratMul_prim.comp
          (Primrec.snd.comp Primrec.fst)
          (ratSub_prim.comp
            (hpayout.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      exact (Primrec.option_map
        (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst)))
        (ratAdd_prim.comp (hterm.comp Primrec.fst) Primrec.snd).to₂).to₂
    exact (Primrec.option_bind (hprice.comp Primrec.fst) hmap).to₂
  have hstep : Primrec₂ fun (q : Q) (x : X) =>
      (market.denoteRatComp q.1.1 x.1.2.1).bind fun coefficient =>
        (market.quoteAtFuel q.1.1 x.1.1 x.1.2.2).bind fun price =>
          x.2.map fun tail => coefficient *
            ratSub (BoolPCWorld.bitsPayoutRat q.1.2 x.1.2.2) price + tail :=
    (Primrec.option_bind hcoefficient hfull).to₂
  exact (Primrec.list_foldr Primrec.snd (Primrec.const (some 0)) hstep).of_eq
    fun q => by simp only [datedValueComp]

end

private lemma ratSub_eq_sub (q r : ℚ) : ratSub q r = q - r := by
  simp [ratSub, ratNeg, sub_eq_add_neg]

private lemma datedMagnitude_day_fold {P : History} (market : MarketComputation P)
    (fuel d : ℕ) (trades : List (EF × Sentence))
    (acc : Option ℚ) :
    (((trades.map fun p => (d, p)).foldr (fun p tail =>
      (market.denoteRatComp fuel p.2.1).bind fun coefficient =>
        tail.map fun q => ratAbs coefficient + q) acc)) =
      (Strategy.magnitudeRatListAtFuel market fuel trades).bind fun today =>
        acc.map fun tail => today + tail := by
  induction trades with
  | nil => simp [Strategy.magnitudeRatListAtFuel]
  | cons p rest ih =>
      simp only [List.map_cons, List.foldr_cons,
        Strategy.magnitudeRatListAtFuel, Option.bind_eq_bind]
      rw [market.denoteRatComp_eq]
      cases hc : p.1.denoteRatWithAtFuel market fuel [] with
      | none => simp
      | some coefficient =>
          simp only [Option.bind_some]
          rw [ih]
          cases ht : Strategy.magnitudeRatListAtFuel market fuel rest with
          | none => simp
          | some tail =>
              cases acc <;> simp [ratAbs_eq, add_assoc]

private lemma datedValue_day_fold {P : History} (market : MarketComputation P)
    (fuel d : ℕ) (bits : List Bool) (trades : List (EF × Sentence))
    (acc : Option ℚ) :
    (((trades.map fun p => (d, p)).foldr (fun p tail =>
      (market.denoteRatComp fuel p.2.1).bind fun coefficient =>
        (market.quoteAtFuel fuel p.1 p.2.2).bind fun price =>
          tail.map fun q => coefficient *
            ratSub (BoolPCWorld.bitsPayoutRat bits p.2.2) price + q) acc)) =
      (Strategy.valueRatListAtFuel market fuel d
        (BoolPCWorld.bitsPayoutRat bits) trades).bind fun today =>
          acc.map fun tail => today + tail := by
  induction trades with
  | nil => simp [Strategy.valueRatListAtFuel]
  | cons p rest ih =>
      simp only [List.map_cons, List.foldr_cons,
        Strategy.valueRatListAtFuel, Option.bind_eq_bind]
      rw [market.denoteRatComp_eq]
      cases hc : p.1.denoteRatWithAtFuel market fuel [] with
      | none => simp
      | some coefficient =>
          simp only [Option.bind_some]
          cases hp : market.quoteAtFuel fuel d p.2 with
          | none => simp
          | some price =>
              simp only [Option.bind_some]
              rw [ih]
              cases ht : Strategy.valueRatListAtFuel market fuel d
                  (BoolPCWorld.bitsPayoutRat bits) rest with
              | none => simp
              | some tail =>
                  cases acc <;> simp [ratSub_eq_sub, add_assoc]

lemma datedMagnitudeComp_familyDatedTrades_eq {Ts : ℕ → Trader}
    {P : History} (market : MarketComputation P) (i fuel m : ℕ) :
    datedMagnitudeComp market fuel (familyDatedTrades (Ts := Ts) i m) =
      (Ts i).partialMagnitudeRatAtFuel market fuel m := by
  unfold familyDatedTrades Trader.partialMagnitudeRatAtFuel
  generalize List.range (m + 1) = days
  induction days with
  | nil => rfl
  | cons d rest ih =>
      simp only [List.flatMap_cons,
        Trader.partialMagnitudeRatDaysAtFuel, Option.bind_eq_bind]
      rw [datedMagnitudeComp, List.foldr_append]
      rw [datedMagnitude_day_fold]
      change (Strategy.magnitudeRatListAtFuel market fuel
        ((Ts i).strat d).trades).bind (fun today =>
          (datedMagnitudeComp market fuel
            (List.flatMap (fun d => List.map (fun p => (d, p))
              ((Ts i).strat d).trades) rest)).map fun tail => today + tail) = _
      rw [ih]
      unfold Strategy.magnitudeRatAtFuel
      cases Strategy.magnitudeRatListAtFuel market fuel
          ((Ts i).strat d).trades <;>
        cases (Ts i).partialMagnitudeRatDaysAtFuel market fuel rest <;> rfl

lemma datedValueComp_familyDatedTrades_eq {Ts : ℕ → Trader}
    {P : History} (market : MarketComputation P)
    (i fuel m : ℕ) (bits : List Bool) :
    datedValueComp market fuel bits (familyDatedTrades (Ts := Ts) i m) =
      (Ts i).partialNetWorthRatAtFuel market fuel
        (BoolPCWorld.bitsPayoutRat bits) m := by
  unfold familyDatedTrades Trader.partialNetWorthRatAtFuel
  generalize List.range (m + 1) = days
  induction days with
  | nil => rfl
  | cons d rest ih =>
      simp only [List.flatMap_cons,
        Trader.partialNetWorthRatDaysAtFuel, Option.bind_eq_bind]
      rw [datedValueComp, List.foldr_append]
      rw [datedValue_day_fold]
      change (Strategy.valueRatListAtFuel market fuel d
        (BoolPCWorld.bitsPayoutRat bits) ((Ts i).strat d).trades).bind
          (fun today => (datedValueComp market fuel bits
            (List.flatMap (fun d => List.map (fun p => (d, p))
              ((Ts i).strat d).trades) rest)).map fun tail => today + tail) = _
      rw [ih]
      unfold Strategy.valueRatAtFuel
      cases Strategy.valueRatListAtFuel market fuel d
          (BoolPCWorld.bitsPayoutRat bits) ((Ts i).strat d).trades <;>
        cases (Ts i).partialNetWorthRatDaysAtFuel market fuel
          (BoolPCWorld.bitsPayoutRat bits) rest <;> rfl

/-- Compiled finite-prefix risk for one family member. -/
def familyPartialMagnitudeComp {Ts : ℕ → Trader} {P : History}
    (market : MarketComputation P) (i fuel m : ℕ) : Option ℚ :=
  datedMagnitudeComp market fuel (familyDatedTrades (Ts := Ts) i m)

/-- Compiled finite-prefix net worth for one family member at a bit-list world. -/
def familyPartialValueComp {Ts : ℕ → Trader} {P : History}
    (market : MarketComputation P) (i fuel m : ℕ) (bits : List Bool) : Option ℚ :=
  datedValueComp market fuel bits (familyDatedTrades (Ts := Ts) i m)

section
attribute [local irreducible] Nat.sqrt

lemma familyPartialMagnitudeComp_prim {Ts : ℕ → Trader} {P : History}
    (h : PolyTradeEmulatable Ts) (market : MarketComputation P) :
    Primrec fun q : (ℕ × ℕ) × ℕ =>
      familyPartialMagnitudeComp (Ts := Ts) market q.1.1 q.1.2 q.2 := by
  have htrades : Primrec fun q : (ℕ × ℕ) × ℕ =>
      familyDatedTrades (Ts := Ts) q.1.1 q.2 :=
    (familyDatedTrades_prim h).comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (datedMagnitudeComp_prim market).comp
    ((Primrec.snd.comp Primrec.fst).pair htrades)

lemma familyPartialValueComp_prim {Ts : ℕ → Trader} {P : History}
    (h : PolyTradeEmulatable Ts) (market : MarketComputation P) :
    Primrec fun q : (((ℕ × ℕ) × ℕ) × List Bool) =>
      familyPartialValueComp (Ts := Ts) market
        q.1.1.1 q.1.1.2 q.1.2 q.2 := by
  have htrades : Primrec fun q : (((ℕ × ℕ) × ℕ) × List Bool) =>
      familyDatedTrades (Ts := Ts) q.1.1.1 q.1.2 :=
    (familyDatedTrades_prim h).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  exact (datedValueComp_prim market).comp
    (((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      Primrec.snd).pair htrades)

end

/-! ## The non-dependent maturity checker -/

def halfRat (q : ℚ) : ℚ := (1 / 2) * q

lemma halfRat_eq (q : ℚ) : halfRat q = q / 2 := by
  rw [halfRat]
  ring

lemma halfRat_prim : Primrec halfRat :=
  ratMul_prim.comp (Primrec.const (1 / 2)) Primrec.id

/-- One Boolean-world branch of the compiled family checker. -/
def familyMaturityWorldCheck {Ts : ℕ → Trader} {P : History}
    (market : MarketComputation P) (epsilon tolerance : ℚ)
    (i m fuel : ℕ) (stage : Finset Sentence) (bits : List Bool) : Bool :=
  !(stageSatBits stage bits) ||
    match familyPartialValueComp (Ts := Ts) market i fuel m bits with
    | none => false
    | some worth => decide (epsilon - halfRat tolerance ≤ worth)

/-- The executable checker at a fixed interpreter clock. -/
def familyMaturityCheckAtFuel {Ts : ℕ → Trader} {P : History}
    {DP : DeductiveProcess} (market : MarketComputation P)
    (process : DeductiveProcessComputation DP) (epsilon : ℚ)
    (tolerance : ℕ → ℚ) (i m fuel : ℕ) : Bool :=
  match process.stageAtFuel fuel m with
  | none => false
  | some stage =>
      match familyPartialMagnitudeComp (Ts := Ts) market i fuel m with
      | none => false
      | some risk =>
          decide (1 - halfRat (tolerance i) ≤ risk) &&
            (allBitLists (familyMaturityAtomLimit (Ts := Ts) i stage m)).all
              (familyMaturityWorldCheck (Ts := Ts) market epsilon (tolerance i)
                i m fuel stage)

lemma familyPartialMagnitudeComp_eq {Ts : ℕ → Trader} {P : History}
    (market : MarketComputation P) (i fuel m : ℕ) :
    familyPartialMagnitudeComp (Ts := Ts) market i fuel m =
      (Ts i).partialMagnitudeRatAtFuel market fuel m :=
  datedMagnitudeComp_familyDatedTrades_eq market i fuel m

lemma familyPartialValueComp_eq {Ts : ℕ → Trader} {P : History}
    (market : MarketComputation P) (i fuel m : ℕ) (bits : List Bool) :
    familyPartialValueComp (Ts := Ts) market i fuel m bits =
      (Ts i).partialNetWorthRatAtFuel market fuel
        (BoolPCWorld.bitsPayoutRat bits) m :=
  datedValueComp_familyDatedTrades_eq market i fuel m bits

private lemma familyMaturityWorldCheck_iff {Ts : ℕ → Trader}
    {P : History} (market : MarketComputation P) (epsilon tolerance : ℚ)
    (i m fuel : ℕ) (stage : Finset Sentence) (bits : List Bool)
    (hlen : bits.length = familyMaturityAtomLimit (Ts := Ts) i stage m) :
    familyMaturityWorldCheck (Ts := Ts) market epsilon tolerance
        i m fuel stage bits = true ↔
      AffineCombination.unitMaturityWorldProperty (Ts i) P market
        epsilon (halfRat tolerance) m fuel stage
        (bitsToFin (AffineCombination.maturityAtomLimitFromStage (Ts i) stage m)
          bits) := by
  rw [familyMaturityWorldCheck]
  have hlimit := familyMaturityAtomLimit_eq (Ts := Ts) i stage m
  have hlen' : bits.length =
      AffineCombination.maturityAtomLimitFromStage (Ts i) stage m :=
    hlen.trans hlimit
  rw [Bool.or_eq_true]
  rw [show Bool.not (stageSatBits stage bits) = true ↔
      stageSatBits stage bits ≠ true by
        cases stageSatBits stage bits <;> simp]
  rw [familyPartialValueComp_eq]
  unfold AffineCombination.unitMaturityWorldProperty
  rw [toBoolPCWorld_bitsToFin hlen', payoutRat_bitsToFin hlen']
  constructor
  · intro h hsat
    rcases h with hnot | hworth
    · exact (hnot ((stageSatBits_eq_true_iff stage bits).2
        (fun φ hφ => hsat ⟨φ, hφ⟩))).elim
    · cases hv : (Ts i).partialNetWorthRatAtFuel market fuel
          (BoolPCWorld.bitsPayoutRat bits) m with
      | none => simp [hv] at hworth
      | some worth =>
          simpa [hv, decide_eq_true_iff, ratSub_eq_sub] using hworth
  · intro h
    by_cases hsat : ∀ φ ∈ stage,
        BoolPCWorld.eval (BoolPCWorld.bitsWorld bits) φ = true
    · right
      cases hv : (Ts i).partialNetWorthRatAtFuel market fuel
          (BoolPCWorld.bitsPayoutRat bits) m with
      | none => simpa [hv] using h (fun φ => hsat φ.1 φ.2)
      | some worth =>
          have hw := h (fun φ => hsat φ.1 φ.2)
          simpa [hv, decide_eq_true_iff, ratSub_eq_sub] using hw
    · exact Or.inl (fun hs =>
        hsat ((stageSatBits_eq_true_iff stage bits).1 hs))

private lemma familyMaturityWorlds_all_iff {Ts : ℕ → Trader}
    {P : History} (market : MarketComputation P) (epsilon tolerance : ℚ)
    (i m fuel : ℕ) (stage : Finset Sentence) :
    (allBitLists (familyMaturityAtomLimit (Ts := Ts) i stage m)).all
        (familyMaturityWorldCheck (Ts := Ts) market epsilon tolerance
          i m fuel stage) = true ↔
      ∀ u : BoolPCWorld.FiniteWorld
          (AffineCombination.maturityAtomLimitFromStage (Ts i) stage m),
        AffineCombination.unitMaturityWorldProperty (Ts i) P market
          epsilon (halfRat tolerance) m fuel stage u := by
  rw [List.all_eq_true]
  constructor
  · intro h u
    let bits := List.ofFn u
    have hlimit := familyMaturityAtomLimit_eq (Ts := Ts) i stage m
    have hlen : bits.length = familyMaturityAtomLimit (Ts := Ts) i stage m := by
      simp [bits, hlimit]
    have hmem : bits ∈ allBitLists
        (familyMaturityAtomLimit (Ts := Ts) i stage m) :=
      (mem_allBitLists _ _).2 hlen
    have hw := (familyMaturityWorldCheck_iff market epsilon tolerance
      i m fuel stage bits hlen).1 (h bits hmem)
    simpa [bitsToFin_ofFn, bits] using hw
  · intro h bits hmem
    have hlen := (mem_allBitLists _ _).1 hmem
    apply (familyMaturityWorldCheck_iff market epsilon tolerance
      i m fuel stage bits hlen).2
    exact h (bitsToFin
      (AffineCombination.maturityAtomLimitFromStage (Ts i) stage m) bits)

/-- The compiled non-dependent checker recognizes exactly the existing semantic unit
maturity check. -/
lemma familyMaturityCheckAtFuel_iff {Ts : ℕ → Trader} {P : History}
    {DP : DeductiveProcess} (market : MarketComputation P)
    (process : DeductiveProcessComputation DP) (epsilon : ℚ)
    (tolerance : ℕ → ℚ) (i m fuel : ℕ) :
    familyMaturityCheckAtFuel (Ts := Ts) market process epsilon tolerance
        i m fuel = true ↔
      AffineCombination.unitMaturityCheckAtFuel (Ts i) P DP market process
        epsilon (halfRat (tolerance i)) m fuel = true := by
  unfold familyMaturityCheckAtFuel AffineCombination.unitMaturityCheckAtFuel
  cases hstage : process.stageAtFuel fuel m with
  | none => simp
  | some stage =>
      rw [familyPartialMagnitudeComp_eq]
      cases hrisk : (Ts i).partialMagnitudeRatAtFuel market fuel m with
      | none => simp
      | some risk =>
          letI : DecidablePred (fun u : BoolPCWorld.FiniteWorld
              (AffineCombination.maturityAtomLimitFromStage (Ts i) stage m) =>
              AffineCombination.unitMaturityWorldProperty (Ts i) P market epsilon
                (halfRat (tolerance i)) m fuel stage u) :=
            AffineCombination.unitMaturityWorldPropertyDecidable (Ts i) P market
              epsilon (halfRat (tolerance i)) m fuel stage
          letI : Decidable (∀ u : BoolPCWorld.FiniteWorld
              (AffineCombination.maturityAtomLimitFromStage (Ts i) stage m),
              AffineCombination.unitMaturityWorldProperty (Ts i) P market epsilon
                (halfRat (tolerance i)) m fuel stage u) :=
            Fintype.decidableForallFintype
          rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
          exact and_congr Iff.rfl
            (familyMaturityWorlds_all_iff market epsilon (tolerance i)
              i m fuel stage)

section
attribute [local irreducible] Nat.sqrt

/-- The bounded family maturity checker is primitive recursive in `(member, day, fuel)`
for fixed family, market, process, rational threshold, and tolerance stream. -/
lemma familyMaturityCheckAtFuel_prim {Ts : ℕ → Trader} {P : History}
    {DP : DeductiveProcess} (hTs : PolyTradeEmulatable Ts)
    (market : MarketComputation P) (process : DeductiveProcessComputation DP)
    (epsilon : ℚ) (tolerance : ℕ → ℚ) (htolerance : Primrec tolerance) :
    Primrec fun q : (ℕ × ℕ) × ℕ =>
      familyMaturityCheckAtFuel (Ts := Ts) market process epsilon tolerance
        q.1.1 q.1.2 q.2 := by
  let Q := (ℕ × ℕ) × ℕ
  let S := Q × Finset Sentence
  let R := S × List Bool
  have listAll_eq_foldr {X : Type} (l : List X) (p : X → Bool) :
      l.all p = l.foldr (fun x acc => p x && acc) true := by
    induction l with
    | nil => rfl
    | cons x xs ih => simp [ih]
  have hiQ : Primrec fun q : Q => q.1.1 := Primrec.fst.comp Primrec.fst
  have hmQ : Primrec fun q : Q => q.1.2 := Primrec.snd.comp Primrec.fst
  have hfuelQ : Primrec fun q : Q => q.2 := Primrec.snd
  have htoleranceQ : Primrec fun q : Q => tolerance q.1.1 :=
    htolerance.comp hiQ
  have hhalfQ : Primrec fun q : Q => halfRat (tolerance q.1.1) :=
    halfRat_prim.comp htoleranceQ
  have hthresholdQ : Primrec fun q : Q => epsilon - halfRat (tolerance q.1.1) :=
    (ratSub_prim.comp (Primrec.const epsilon) hhalfQ).of_eq fun q =>
      ratSub_eq_sub epsilon (halfRat (tolerance q.1.1))
  have hlimit : Primrec fun s : S =>
      familyMaturityAtomLimit (Ts := Ts) s.1.1.1 s.2 s.1.1.2 :=
    (familyMaturityAtomLimit_prim hTs).comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hworlds : Primrec fun s : S =>
      allBitLists (familyMaturityAtomLimit (Ts := Ts)
        s.1.1.1 s.2 s.1.1.2) :=
    allBitLists_prim.comp hlimit
  have hsat : Primrec fun r : R => stageSatBits r.1.2 r.2 :=
    stageSatBits_prim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hvalue : Primrec fun r : R =>
      familyPartialValueComp (Ts := Ts) market
        r.1.1.1.1 r.1.1.2 r.1.1.1.2 r.2 :=
    (familyPartialValueComp_prim hTs market).comp
      ((((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).pair
        Primrec.snd)
  have hthresholdR : Primrec fun r : R =>
      epsilon - halfRat (tolerance r.1.1.1.1) :=
    hthresholdQ.comp (Primrec.fst.comp Primrec.fst)
  have hworthTrue : Primrec₂ fun (r : R) (worth : ℚ) =>
      decide (epsilon - halfRat (tolerance r.1.1.1.1) ≤ worth) :=
    (ratLE_prim.comp (hthresholdR.comp₂ Primrec₂.left) Primrec₂.right).decide
  have hworth : Primrec fun r : R =>
      match familyPartialValueComp (Ts := Ts) market
          r.1.1.1.1 r.1.1.2 r.1.1.1.2 r.2 with
      | none => false
      | some worth => decide
          (epsilon - halfRat (tolerance r.1.1.1.1) ≤ worth) :=
    (Primrec.option_casesOn hvalue (Primrec.const false) hworthTrue).of_eq fun r => by
      cases familyPartialValueComp (Ts := Ts) market
        r.1.1.1.1 r.1.1.2 r.1.1.1.2 r.2 <;> rfl
  have hcondition : Primrec fun r : R =>
      familyMaturityWorldCheck (Ts := Ts) market epsilon
        (tolerance r.1.1.1.1) r.1.1.1.1 r.1.1.1.2 r.1.1.2 r.1.2 r.2 := by
    exact (Primrec.or.comp (Primrec.not.comp hsat) hworth).of_eq fun r => by
      unfold familyMaturityWorldCheck
      rfl
  have hstep : Primrec₂ fun (s : S) (x : List Bool × Bool) =>
      familyMaturityWorldCheck (Ts := Ts) market epsilon
          (tolerance s.1.1.1) s.1.1.1 s.1.1.2 s.1.2 s.2 x.1 && x.2 :=
    (Primrec.and.comp
      (hcondition.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  have hall : Primrec fun s : S =>
      (allBitLists (familyMaturityAtomLimit (Ts := Ts)
        s.1.1.1 s.2 s.1.1.2)).foldr
          (fun bits acc => familyMaturityWorldCheck (Ts := Ts) market epsilon
            (tolerance s.1.1.1) s.1.1.1 s.1.1.2 s.1.2 s.2 bits && acc) true :=
    Primrec.list_foldr hworlds (Primrec.const true) hstep
  have hriskQ : Primrec fun q : Q =>
      familyPartialMagnitudeComp (Ts := Ts) market q.1.1 q.2 q.1.2 :=
    (familyPartialMagnitudeComp_prim hTs market).comp
      (((Primrec.fst.comp Primrec.fst).pair Primrec.snd).pair
        (Primrec.snd.comp Primrec.fst))
  have hriskS : Primrec fun s : S =>
      familyPartialMagnitudeComp (Ts := Ts) market
        s.1.1.1 s.1.2 s.1.1.2 := hriskQ.comp Primrec.fst
  have hriskThresholdS : Primrec fun s : S =>
      1 - halfRat (tolerance s.1.1.1) :=
    ((ratSub_prim.comp (Primrec.const 1)
      (hhalfQ.comp Primrec.fst)).of_eq fun s =>
        ratSub_eq_sub 1 (halfRat (tolerance s.1.1.1)))
  have hriskTrue : Primrec₂ fun (s : S) (risk : ℚ) =>
      decide (1 - halfRat (tolerance s.1.1.1) ≤ risk) &&
        (allBitLists (familyMaturityAtomLimit (Ts := Ts)
          s.1.1.1 s.2 s.1.1.2)).foldr
            (fun bits acc => familyMaturityWorldCheck (Ts := Ts) market epsilon
              (tolerance s.1.1.1) s.1.1.1 s.1.1.2 s.1.2 s.2 bits && acc) true :=
    (Primrec.and.comp
      ((ratLE_prim.comp
        (hriskThresholdS.comp₂ Primrec₂.left) Primrec₂.right).decide)
      (hall.comp Primrec.fst)).to₂
  have hriskBranch : Primrec fun s : S =>
      match familyPartialMagnitudeComp (Ts := Ts) market
          s.1.1.1 s.1.2 s.1.1.2 with
      | none => false
      | some risk =>
          decide (1 - halfRat (tolerance s.1.1.1) ≤ risk) &&
            (allBitLists (familyMaturityAtomLimit (Ts := Ts)
              s.1.1.1 s.2 s.1.1.2)).foldr
                (fun bits acc => familyMaturityWorldCheck (Ts := Ts) market epsilon
                  (tolerance s.1.1.1) s.1.1.1 s.1.1.2 s.1.2 s.2 bits && acc) true :=
    (Primrec.option_casesOn hriskS (Primrec.const false) hriskTrue).of_eq fun s => by
      cases familyPartialMagnitudeComp (Ts := Ts) market
        s.1.1.1 s.1.2 s.1.1.2 <;> rfl
  have hstage : Primrec fun q : Q => process.stageAtFuel q.2 q.1.2 :=
    (processStageAtFuel_prim process).comp hfuelQ hmQ
  have hcompiled : Primrec fun q : Q =>
      match process.stageAtFuel q.2 q.1.2 with
      | none => false
      | some stage =>
          match familyPartialMagnitudeComp (Ts := Ts) market
              q.1.1 q.2 q.1.2 with
          | none => false
          | some risk =>
              decide (1 - halfRat (tolerance q.1.1) ≤ risk) &&
                (allBitLists (familyMaturityAtomLimit (Ts := Ts)
                  q.1.1 stage q.1.2)).foldr
                    (fun bits acc => familyMaturityWorldCheck (Ts := Ts) market epsilon
                      (tolerance q.1.1) q.1.1 q.1.2 q.2 stage bits && acc) true :=
    (Primrec.option_casesOn hstage (Primrec.const false)
      (hriskBranch.comp (Primrec.fst.pair Primrec.snd)).to₂).of_eq fun q => by
        cases process.stageAtFuel q.2 q.1.2 <;> rfl
  exact hcompiled.of_eq fun q => by
    unfold familyMaturityCheckAtFuel
    cases process.stageAtFuel q.2 q.1.2 with
    | none => rfl
    | some stage =>
        cases familyPartialMagnitudeComp (Ts := Ts) market q.1.1 q.2 q.1.2 with
        | none => rfl
        | some risk =>
            simp only
            rw [listAll_eq_foldr]

end

/-! ## Arbitrary-runtime semidecider and bounded dovetail -/

/-- A single partial-recursive program semidecides historical maturity for every member
and candidate day of a polynomial trader family. -/
structure FamilyMaturitySemidecider (Ts : ℕ → Trader) (P : History)
    (DP : DeductiveProcess) (market : MarketComputation P)
    (process : DeductiveProcessComputation DP) (epsilon : ℚ)
    (tolerance : ℕ → ℚ) where
  code : Nat.Partrec.Code
  spec : ∀ i m,
    (∃ fuel, acceptsWithin code fuel (Nat.pair i m) = true) ↔
      ∃ fuel, familyMaturityCheckAtFuel (Ts := Ts) market process
        epsilon tolerance i m fuel = true

/-- Extract the unbounded maturity semidecider from the primitive-recursive bounded
checker.  `rfindOpt` searches only for an interpreter clock; the outer historical table
below will run this code through the polynomial bounded dovetail. -/
noncomputable def FamilyMaturitySemidecider.ofComputations
    {Ts : ℕ → Trader} {P : History} {DP : DeductiveProcess}
    (hTs : PolyTradeEmulatable Ts) (market : MarketComputation P)
    (process : DeductiveProcessComputation DP) (epsilon : ℚ)
    (tolerance : ℕ → ℚ) (htolerance : Primrec tolerance) :
    FamilyMaturitySemidecider Ts P DP market process epsilon tolerance := by
  have hcheck : Primrec₂ fun (z fuel : ℕ) =>
      familyMaturityCheckAtFuel (Ts := Ts) market process epsilon tolerance
        z.unpair.1 z.unpair.2 fuel := by
    have hinput : Primrec fun p : ℕ × ℕ =>
        (p.1.unpair, p.2) :=
      (Primrec.unpair.comp Primrec.fst).pair Primrec.snd
    exact ((familyMaturityCheckAtFuel_prim hTs market process
      epsilon tolerance htolerance).comp hinput).to₂
  let guard : ℕ → ℕ → Option ℕ := fun z fuel =>
    if familyMaturityCheckAtFuel (Ts := Ts) market process epsilon tolerance
        z.unpair.1 z.unpair.2 fuel then some 1 else none
  have hguard : Computable₂ guard := by
    have hp : Primrec fun p : ℕ × ℕ =>
        if familyMaturityCheckAtFuel (Ts := Ts) market process epsilon tolerance
            p.1.unpair.1 p.1.unpair.2 p.2 then some 1 else none := by
      exact Primrec.ite
        (Primrec.eq.comp hcheck (Primrec.const true))
        (Primrec.const (some 1)) (Primrec.const (none : Option ℕ))
    exact hp.to₂.to_comp
  have hpart : Partrec fun z => Nat.rfindOpt (guard z) :=
    Partrec.rfindOpt hguard
  have hnat : Nat.Partrec fun z => Nat.rfindOpt (guard z) :=
    Partrec.nat_iff.mp hpart
  let code := Classical.choose (Nat.Partrec.Code.exists_code.mp hnat)
  have hcode : Nat.Partrec.Code.eval code = fun z => Nat.rfindOpt (guard z) :=
    Classical.choose_spec (Nat.Partrec.Code.exists_code.mp hnat)
  refine ⟨code, fun i m => ?_⟩
  constructor
  · rintro ⟨fuel, haccept⟩
    have hevaln : Nat.Partrec.Code.evaln fuel code (Nat.pair i m) = some 1 := by
      cases he : Nat.Partrec.Code.evaln fuel code (Nat.pair i m) with
      | none => simp [acceptsWithin, codeEvalnNat, he] at haccept
      | some out =>
          simp [acceptsWithin, codeEvalnNat, he] at haccept
          obtain rfl : out = 1 := by omega
          rfl
    have hmem : 1 ∈ Nat.rfindOpt (guard (Nat.pair i m)) := by
      have : 1 ∈ Nat.Partrec.Code.eval code (Nat.pair i m) :=
        Nat.Partrec.Code.evaln_sound hevaln
      rw [hcode] at this
      exact this
    obtain ⟨fuel', hfuel'⟩ := Nat.rfindOpt_spec hmem
    refine ⟨fuel', ?_⟩
    simpa [guard] using hfuel'
  · rintro ⟨fuel, hfuel⟩
    have hdom : (Nat.rfindOpt (guard (Nat.pair i m))).Dom := by
      rw [Nat.rfindOpt_dom]
      exact ⟨fuel, 1, by simp [guard, hfuel]⟩
    have hone : 1 ∈ Nat.rfindOpt (guard (Nat.pair i m)) := by
      have hout := Part.get_mem hdom
      obtain ⟨fuel', hfuel'⟩ := Nat.rfindOpt_spec hout
      have houtEq : (Nat.rfindOpt (guard (Nat.pair i m))).get hdom = 1 := by
        have hp : familyMaturityCheckAtFuel (Ts := Ts) market process
              epsilon tolerance i m fuel' = true ∧
            1 = (Nat.rfindOpt (guard (Nat.pair i m))).get hdom := by
          simpa [guard] using hfuel'
        exact hp.2.symm
      rw [houtEq] at hout
      exact hout
    have hmem : 1 ∈ Nat.Partrec.Code.eval code (Nat.pair i m) := by
      rw [hcode]
      exact hone
    obtain ⟨fuel', hevaln⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
    refine ⟨fuel', ?_⟩
    change Nat.Partrec.Code.evaln fuel' code (Nat.pair i m) = some 1 at hevaln
    simp [acceptsWithin, codeEvalnNat, hevaln]

private lemma zero_matured (P : History) (DP : DeductiveProcess)
    (epsilon eta : ℝ) (m : ℕ) :
    Trader.zero.Matured P DP epsilon eta m := by
  have hmag : Trader.zero.magnitude P = 0 := by
    simp [Trader.magnitude, Trader.zero, Strategy.magnitude]
  constructor
  · rw [hmag, mul_zero]
    simp [Trader.zero, Strategy.magnitude]
  · intro v hv
    rw [hmag, mul_zero, Trader.zero_netWorth]

/-- Uniform historical verified-maturity schedule constructed from the family token
stream and the certified market/process programs.  The finite prefix is handled directly
by zero traders; only post-`start` unit-magnitude members enter the semantic checker. -/
noncomputable def historicalScheduleOfComputations
    {Ts : ℕ → Trader} {P : History} {DP : DeductiveProcess}
    (hTs : PolyTradeEmulatable Ts) (market : MarketComputation P)
    (process : DeductiveProcessComputation DP) (epsilon : ℚ)
    (tolerance : ℕ → ℚ) (htolerance : Primrec tolerance)
    (htolerancePos : ∀ i, 0 < (tolerance i : ℝ)) (start : ℕ)
    (hmag : ∀ i, start ≤ i → (Ts i).magnitude P = 1)
    (hroi : ∀ i, start ≤ i → HasROI (Ts i) P DP (epsilon : ℝ)) :
    ROIBudget.HistoricalVerifiedMaturitySchedule
      (gateTraderFamily start Ts) P DP (epsilon : ℝ)
      (fun i => (tolerance i : ℝ)) := by
  let semidecider := FamilyMaturitySemidecider.ofComputations
    hTs market process epsilon tolerance htolerance
  let check : ℕ → ℕ → Bool := fun i n =>
    if start ≤ i then dovetailFound semidecider.code i n else true
  refine {
    check := check
    check_poly := ?_
    sound := ?_
    complete := ?_
  }
  · obtain ⟨cd, hd⟩ := polyFueled_dovetailFound semidecider.code
    have htest : PolyFueled _ (fun z => start - z.unpair.1) :=
      (subc_polyFueled.comp ((PolyFueled.const start).pair PolyFueled.left)).of_eq
        fun z => by rw [Nat.unpair_pair]
    refine ⟨_, (ifzSel_polyFueled.comp
      ((hd.pair (PolyFueled.const 1)).pair htest)).of_eq fun z => ?_⟩
    simp only [ifzSelFn, Nat.unpair_pair]
    by_cases hi : start ≤ z.unpair.1
    · have hz : start - z.unpair.1 = 0 := Nat.sub_eq_zero_of_le hi
      simp [check, hi, hz]
    · have hz : start - z.unpair.1 ≠ 0 := by omega
      simp [check, hi, hz]
  · intro i n hcheck
    by_cases hi : start ≤ i
    · have hdovetail : dovetailFound semidecider.code i n = true := by
        simpa [check, hi] using hcheck
      obtain ⟨m, hmn, haccept⟩ :=
        (dovetailFound_eq_true_iff semidecider.code i n).1 hdovetail
      have hrecognized : ∃ fuel,
          familyMaturityCheckAtFuel (Ts := Ts) market process epsilon tolerance
            i m fuel = true :=
        (semidecider.spec i m).1 ⟨n, haccept⟩
      obtain ⟨fuel, hfamily⟩ := hrecognized
      have hunit := (familyMaturityCheckAtFuel_iff market process
        epsilon tolerance i m fuel).1 hfamily
      have hmature := AffineCombination.unitMaturityCheckAtFuel_sound
        market process hunit (hmag i hi)
      refine ⟨m, hmn, ?_⟩
      simpa [gateTraderFamily, hi, halfRat_eq] using hmature
    · refine ⟨0, Nat.zero_le n, ?_⟩
      simpa [gateTraderFamily, hi] using
        (zero_matured P DP (epsilon : ℝ)
          ((tolerance i : ℝ) / 2) 0)
  · intro i
    by_cases hi : start ≤ i
    · have hhalfPos : 0 < ((tolerance i : ℝ) / 2) := by
        nlinarith [htolerancePos i]
      obtain ⟨m, hmature⟩ := (hroi i hi).exists_matured hhalfPos
      have hmature' : (Ts i).Matured P DP (epsilon : ℝ)
          (halfRat (tolerance i) : ℝ) m := by
        simpa [halfRat_eq] using hmature
      obtain ⟨fuel, hunit⟩ :=
        AffineCombination.unitMaturityCheckAtFuel_eventually_complete
          market process hmature' (hmag i hi)
      have hfamily := (familyMaturityCheckAtFuel_iff market process
        epsilon tolerance i m fuel).2 hunit
      obtain ⟨acceptFuel, haccept⟩ :=
        (semidecider.spec i m).2 ⟨fuel, hfamily⟩
      let n := max m acceptFuel
      have haccept' : acceptsWithin semidecider.code n (Nat.pair i m) = true :=
        acceptsWithin_mono semidecider.code (le_max_right m acceptFuel) haccept
      have hdovetail : dovetailFound semidecider.code i n = true :=
        (dovetailFound_eq_true_iff semidecider.code i n).2
          ⟨m, le_max_left m acceptFuel, haccept'⟩
      exact ⟨n, by simp [check, hi, hdovetail]⟩
    · exact ⟨0, by simp [check, hi]⟩

end HistoricalMaturityCompile

namespace AffineCombination

open Filter

/-- The canonical geometric ROI tolerance stream is primitive recursive as an exact
rational sequence. -/
lemma roiToleranceRat_prim : Primrec roiToleranceRat := by
  have hstep : Primrec₂ fun (_n : ℕ) (prev : ℚ) => prev * (1 / 2) :=
    ratMul_prim.comp₂ Primrec₂.right (Primrec₂.const (1 / 2))
  have hrec : Primrec (Nat.rec (motive := fun _ => ℚ) (1 / 2)
      (fun n prev => prev * (1 / 2))) :=
    Primrec.nat_rec₁ (1 / 2) hstep
  exact hrec.of_eq fun n => by
    induction n with
    | zero => simp [roiToleranceRat]
    | succ n ih =>
        change (Nat.rec (motive := fun _ => ℚ) (1 / 2)
          (fun n prev => prev * (1 / 2)) n) * (1 / 2) = roiToleranceRat (n + 1)
        rw [ih]
        simp only [roiToleranceRat, pow_succ]

lemma roiToleranceRat_pos (i : ℕ) : 0 < (roiToleranceRat i : ℝ) := by
  rw [roiToleranceRat]
  positivity

/-- One-sided affine recurring unbiasedness with the historical verifier constructed
from the logical inductor's certified market and deductive-process programs. -/
lemma DeterminedViaTheory.not_eventually_weightedBias_lt_ofComputations
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [hLI : IsLogicalInductor P DP]
    {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ¬ ∀ᶠ n in Filter.atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -ε := by
  intro hbias
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, (0 : ℝ) < q ∧ (q : ℝ) < ε :=
    exists_rat_btwn hε
  have hbiasQ : ∀ᶠ n in Filter.atTop,
      weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n < -(q : ℝ) :=
    hbias.mono fun n hn => by linarith
  let market : MarketComputation P := hLI.marketComputable.nonemptyComputation.some
  let process : DeductiveProcessComputation DP :=
    hLI.processComputable.nonemptyComputation.some
  have hverify : ∀ scale N,
      (∀ k, N ≤ k →
        HasROI (biasRunTrader hpoly hWgen (biasRunRate scale) k)
          P DP ((q : ℝ) / 4)) →
      ROIBudget.HistoricalVerifiedMaturitySchedule
        (gateTraderFamily N
          (biasRunTrader hpoly hWgen (biasRunRate scale)))
        P DP ((q : ℝ) / 4) roiTolerance := by
    intro scale N hroi
    let Ts : ℕ → Trader :=
      biasRunTrader hpoly hWgen (biasRunRate scale)
    have hTs : PolyTradeEmulatable Ts := by
      simpa [Ts] using biasRunTrader_polyTrade hpoly hWgen
        (biasRunRate scale) (biasRunRate_codes scale)
    have hunit : ∀ i, N ≤ i → (Ts i).magnitude P = 1 := by
      intro i hi
      simpa [Ts] using
        (hdet.biasRunTrader_magnitude_eq_one_of_negative_bias hpoly hWgen
          hWdiv hmag hworld hP (biasRunRate scale)
          (fun k => (biasRunRate_pos scale k).le)
          (biasRunRate_le_one scale) (q : ℝ) hq0 hbiasQ i
          (biasRunRate_pos scale i))
    have hroi' : ∀ i, N ≤ i →
        HasROI (Ts i) P DP ((q / 4 : ℚ) : ℝ) := by
      intro i hi
      simpa [Ts] using hroi i hi
    have hs := HistoricalMaturityCompile.historicalScheduleOfComputations
      hTs market process (q / 4) roiToleranceRat roiToleranceRat_prim
      roiToleranceRat_pos N hunit hroi'
    simpa [Ts, roiTolerance] using hs
  have hnotQ := hdet.not_eventually_weightedBias_lt_of_historicalVerifier
    hpoly hWgen hWdiv hmag hworld (q : ℝ) hq0 roiTolerance
      roiTolerance_nonneg roiTolerance_summable hverify
  exact hnotQ hbiasQ

/-- Affine recurring unbiasedness with both one-sided historical schedules constructed
from the logical inductor computations. -/
lemma DeterminedViaTheory.recunbiasedaff_ofComputations
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ}
    (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
     :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth) 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).price P i
  let f : ℕ → ℝ := weightedBias w market truth
  have hstep : Tendsto (fun n => f (n + 1) - f n) Filter.atTop (nhds 0) := by
    apply weightedAverage_step_tendsto_zero w
      (fun i => market i - truth i) 1
    · exact fun n => (hWdiv.1 n).1
    · exact fun n => (hWdiv.1 n).2
    · intro n
      have hn := hdet.abs_truth_sub_price_le_magnitude hpoly hworld hP n
      rw [abs_sub_comm] at hn
      exact hn.trans (hmag n)
    · exact hWdiv.2
  have hlower : ∀ ε > 0, ∃ᶠ n in Filter.atTop, -ε < f n := by
    intro ε hε
    have hnot := hdet.not_eventually_weightedBias_lt_ofComputations
      hpoly hWgen hWdiv hmag hworld hP (ε / 2) (by linarith)
    rw [Filter.not_eventually] at hnot
    exact hnot.mono (fun n hn => by
      simp only [not_lt] at hn
      dsimp only [f, w, market]
      linarith)
  have hdetNeg := hdet.neg
  have hmagNeg : ∀ i, ((As i).neg).magnitude P ≤ 1 := by
    intro i
    rw [AffineCombination.neg_magnitude]
    exact hmag i
  have hupper : ∀ ε > 0, ∃ᶠ n in Filter.atTop, f n < ε := by
    intro ε hε
    have hnot := hdetNeg.not_eventually_weightedBias_lt_ofComputations
      hpoly.neg hWgen hWdiv hmagNeg hworld hP (ε / 2) (by linarith)
    rw [Filter.not_eventually] at hnot
    exact hnot.mono (fun n hn => by
      simp only [not_lt] at hn
      rw [show (fun i => ((As i).neg).price P i) = fun i => -market i by
        funext i
        exact AffineCombination.neg_price (As i) P i,
        weightedBias_neg] at hn
      dsimp only [f]
      linarith)
  exact hasLimitPoint_zero_of_two_sided_recurring f hstep hlower hupper

/-! ## Statistical-learning capstones -/

/-- The patient settlement clock is **derived, not assumed**: `IsLogicalInductor` already
carries a computable market and a computable deductive process (`def:lic`), and those two
programs are exactly what the paper's `app:prandaff` `DefinitelySettled` dovetail needs.
`PatientSettlementClock.ofComputations` runs that dovetail, so no endpoint below has to
take a clock as a hypothesis. -/
private noncomputable def patientClockOfInductor
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [hLI : IsLogicalInductor P DP] {truth : ℕ → ℝ}
    (hpoly : PolySequence As) (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) : PatientSettlementClock As P DP truth f :=
  PatientSettlementClock.ofComputations hpoly
    hLI.marketComputable.nonemptyComputation.some
    hLI.processComputable.nonemptyComputation.some hdet hworld f

/-- The nonnegative affine pseudorandomness branch with historical maturity constructed
from the logical inductor computations.
Paper node: `thm:prandaff` -/
theorem DeterminedViaTheory.lic_prandaff_above
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (clock : PatientSettlementClock As P DP truth f)
    (hpseudo : PseudorandomAbove truth f P) :
    (fun n ↦ (As n).price P n) ≳ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  intro ε hε
  by_contra hnotEventually
  rw [Filter.not_eventually] at hnotEventually
  have hfreqBad : ∃ᶠ n in Filter.atTop, (As n).price P n + ε < 0 :=
    hnotEventually.mono (fun n hn ↦ lt_of_not_ge hn)
  obtain ⟨q, hq0, hqε⟩ : ∃ q : ℚ, (0 : ℝ) < q ∧ (q : ℝ) < ε / 2 :=
    exists_rat_btwn (half_pos hε)
  have hfreqLow : ∃ᶠ n in Filter.atTop,
      (As n).price P n < ((-2 * q : ℚ) : ℝ) :=
    hfreqBad.mono (fun n hn ↦ by push_cast; linarith)
  let W : ℕ → EF := patientUnderpriceWeight clock (-2 * q) q
  have hWgen : PGenerableWeighting W := by
    simpa only [W] using patientUnderpriceWeight_pgenerable hpoly clock (-2 * q) q
  have hWdiv : DivergentWeighting W P := by
    simpa only [W] using
      patientUnderpriceWeight_divergent hpoly clock (-2 * q) q hq0 hfreqLow
  have hWpatient : DeferralPatient f W P := by
    simpa only [W] using
      patientUnderpriceWeight_deferralPatient hpoly clock (-2 * q) q
  let w : ℕ → ℝ := fun i ↦ (W i).denote P
  let market : ℕ → ℝ := fun i ↦ (As i).price P i
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ (hWdiv.1 i).1
  have hden : ∀ᶠ n in Filter.atTop, 0 < prefixSum w n := by
    simpa only [w] using hWdiv.eventually_prefixSum_pos
  obtain ⟨B, hB0, hB⟩ := hbounded
  have hsupport : ∀ i, 0 < w i → market i ∈ Set.Icc (-B) (-(q : ℝ)) := by
    intro i hi
    have hpriceLow := patientUnderpriceWeight_pos_imp_price_lt
      hpoly clock (-2 * q) q hq0 i (by simpa only [w, W] using hi)
    constructor
    · have habs := hB i i
      exact (neg_le_neg habs).trans (neg_abs_le ((As i).price P i))
    · dsimp only [market]
      push_cast at hpriceLow
      linarith
  have hmarketBad : ∀ᶠ n in Filter.atTop,
      weightedAverage w market n < -((q : ℝ) / 2) := by
    filter_upwards [hden] with n hn
    have hmem := weightedAverage_mem_Icc_of_support hw0 hsupport hn
    linarith [hmem.2, hq0]
  have htruth : (weightedAverage w truth) ≳ₙ (fun _ ↦ 0) := by
    simpa only [w] using hpseudo W hWgen hWdiv hWpatient
  have hbias : HasLimitPoint (weightedBias w market truth) 0 := by
    simpa only [w, market] using
      hdet.recunbiasedaff_ofComputations hpoly hWgen hWdiv hmag hworld
  exact (not_eventually_weightedAverage_lt_of_limitPoint_bias
    w market truth hden hbias htruth ((q : ℝ) / 2) (half_pos hq0)) hmarketBad

/-- The nonpositive affine pseudorandomness branch with constructed maturity schedules.
Paper node: `thm:prandaff` -/
theorem DeterminedViaTheory.lic_prandaff_below
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (clock : PatientSettlementClock As P DP truth f)
    (hpseudo : PseudorandomBelow truth f P) :
    (fun n ↦ (As n).price P n) ≲ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  have hboundedNeg : BoundedAffinePrices (fun n ↦ (As n).neg) P := by
    obtain ⟨B, hB0, hB⟩ := hbounded
    refine ⟨B, hB0, fun n m ↦ ?_⟩
    rw [neg_price, abs_neg]
    exact hB n m
  have hmagNeg : ∀ i, ((As i).neg).magnitude P ≤ 1 := by
    intro i
    rw [neg_magnitude]
    exact hmag i
  have haboveNeg := hdet.neg.lic_prandaff_above hpoly.neg hboundedNeg hmagNeg
    hworld f clock.neg hpseudo.neg
  intro ε hε
  filter_upwards [haboveNeg ε hε] with n hn
  rw [neg_price] at hn
  simp only [zero_add]
  linarith

/-- Exact two-sided affine pseudorandomness with no historical-verifier premises.
Paper node: `thm:prandaff` -/
theorem DeterminedViaTheory.lic_prandaff
    {As : ℕ → AffineCombination} (hpoly : PolySequence As)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ i, (As i).magnitude P ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (clock : PatientSettlementClock As P DP truth f)
    (hpseudo : Pseudorandom truth f P) :
    (fun n ↦ (As n).price P n) ≈ₙ (fun _ ↦ 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨hdet.lic_prandaff_below hpoly hbounded hmag hworld f clock hpseudo.2,
    hdet.lic_prandaff_above hpoly hbounded hmag hworld f clock hpseudo.1⟩

/-- Paper-facing bounded affine recurring-unbiasedness with no verifier hypothesis.
Paper node: `thm:recunbiasedaff` -/
theorem BoundedCombinationSequence.recunbiasedaff
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
     :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth) 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℚ := h.unitNormalization.scale
  have hq : 0 < (q : ℝ) := h.unitNormalization.scale_pos
  have hdetScaled : DeterminedViaTheory
      (fun n => (As n).scale (.const q)) P DP
      (fun n => (q : ℝ) * truth n) := by
    intro n v hv
    rw [AffineCombination.scale_value, EF.denote_const, hdet n v hv]
  have hs := hdetScaled.recunbiasedaff_ofComputations
    (h.poly.scaleRat q) hWgen hWdiv h.unitNormalization.magnitude_le_one
      hworld
  have hscaled : HasLimitPoint
      (fun n => (q : ℝ) * weightedBias (fun i => (W i).denote P)
        (fun i => (As i).price P i) truth n) 0 := by
    have hs' : HasLimitPoint
        (weightedBias (fun i => (W i).denote P)
          (fun i => (q : ℝ) * (As i).price P i)
          (fun i => (q : ℝ) * truth i)) 0 := by
      simpa only [q, AffineCombination.scale_price, EF.denote_const] using hs
    have heq : weightedBias (fun i => (W i).denote P)
        (fun i => (q : ℝ) * (As i).price P i)
        (fun i => (q : ℝ) * truth i) =
        fun n => (q : ℝ) * weightedBias (fun i => (W i).denote P)
          (fun i => (As i).price P i) truth n := by
      funext n
      exact weightedBias_const_mul _ _ _ _ _
    rwa [heq] at hs'
  exact hasLimitPoint_zero_of_const_mul (ne_of_gt hq) hscaled

/-- Paper-facing nonnegative `thm:prandaff` for an arbitrary bounded combination
sequence, with historical maturity constructed internally.
Paper node: `thm:prandaff` -/
theorem BoundedCombinationSequence.prandaff_above
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : PseudorandomAbove truth f P) :
    (fun n => (As n).price P n) ≳ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℚ := h.unitNormalization.scale
  have hq : 0 < (q : ℝ) := h.unitNormalization.scale_pos
  have hdetScaled : DeterminedViaTheory
      (fun n => (As n).scale (.const q)) P DP
      (fun n => (q : ℝ) * truth n) := by
    intro n v hv
    rw [scale_value, EF.denote_const, hdet n v hv]
  have hs := hdetScaled.lic_prandaff_above
    (h.poly.scaleRat q) ((h.boundedPrices hP).scaleRat q)
      h.unitNormalization.magnitude_le_one hworld f
      (patientClockOfInductor (h.poly.scaleRat q) hdetScaled hworld f)
      (hpseudo.const_mul_pos hq)
  have hscaled : (fun n => (q : ℝ) * (As n).price P n) ≳ₙ (fun _ => 0) := by
    simpa only [q, scale_price, EF.denote_const] using hs
  exact asympGE_zero_of_const_mul_pos hq hscaled

/-- Paper-facing nonpositive `thm:prandaff` with constructed maturity schedules.
Paper node: `thm:prandaff` -/
theorem BoundedCombinationSequence.prandaff_below
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : PseudorandomBelow truth f P) :
    (fun n => (As n).price P n) ≲ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℚ := h.unitNormalization.scale
  have hq : 0 < (q : ℝ) := h.unitNormalization.scale_pos
  have hdetScaled : DeterminedViaTheory
      (fun n => (As n).scale (.const q)) P DP
      (fun n => (q : ℝ) * truth n) := by
    intro n v hv
    rw [scale_value, EF.denote_const, hdet n v hv]
  have hs := hdetScaled.lic_prandaff_below
    (h.poly.scaleRat q) ((h.boundedPrices hP).scaleRat q)
      h.unitNormalization.magnitude_le_one hworld f
      (patientClockOfInductor (h.poly.scaleRat q) hdetScaled hworld f)
      (hpseudo.const_mul_pos hq)
  have hscaled : (fun n => (q : ℝ) * (As n).price P n) ≲ₙ (fun _ => 0) := by
    simpa only [q, scale_price, EF.denote_const] using hs
  exact asympLE_zero_of_const_mul_pos hq hscaled

/-- Exact two-sided paper `thm:prandaff`, without historical-verifier premises.
Paper node: `thm:prandaff` -/
theorem BoundedCombinationSequence.prandaff
    {As : ℕ → AffineCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedCombinationSequence As P)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : Pseudorandom truth f P) :
    (fun n => (As n).price P n) ≈ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨h.prandaff_below hdet hworld f hpseudo.2,
    h.prandaff_above hdet hworld f hpseudo.1⟩

/-- Ordinary recurring unbiasedness with its affine historical schedules constructed.
Paper node: `thm:recurringunbiasedness` -/
lemma recurringunbiasedness
    (φ : ℕ → Sentence) (hpoly : PolySequence (sentenceAffine φ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    {truth : ℕ → ℝ} (htruth : TheoryTruth φ DP truth)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
     :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => P i (φ i)) truth) 0 := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hdet : DeterminedViaTheory (sentenceAffine φ) P DP truth := by
    intro n v hv
    simpa [sentenceAffine, AffineCombination.value] using htruth n v hv
  have hmag : ∀ i, (sentenceAffine φ i).magnitude P ≤ 1 := by
    intro i
    simp
  have h := hdet.recunbiasedaff_ofComputations hpoly hWgen hWdiv
    hmag hworld
  simpa using h

/-- Recurring calibration with no historical-verifier premises.
Paper node: `thm:simcal` -/
lemma simcal
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (truth : ℕ → ℝ)
    (a b : ℚ) (δ : ℕ → ℚ)
    (hδ : PolyPositiveWidths δ)
    (hpoly : PolySequence (sentenceAffine φ))
    (htruth : TheoryTruth φ DP truth)
    (hWgen : PGenerableWeighting (calibrationIndicator φ a b δ))
    (hdiv : DivergentWeighting (calibrationIndicator φ a b δ) P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
     :
    HasLimitPointIn
        (weightedAverage
          (fun n => (calibrationIndicator φ a b δ n).denote P) truth)
        (Set.Icc (a : ℝ) (b : ℝ)) ∧
      ∀ x, ConvergesTo
          (weightedAverage
            (fun n => (calibrationIndicator φ a b δ n).denote P) truth) x →
        x ∈ Set.Icc (a : ℝ) (b : ℝ) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hbias := recurringunbiasedness φ hpoly hWgen
    htruth hdiv hworld
  exact simcal_of_recurring_unbiasedness P φ truth a b δ hδ
    (fun n => htruth.isBoolean hworld n) hdiv hbias

end AffineCombination

namespace LUVCombination

open Filter

/-- `thm:recurringunbiasednessexp` with the normalized-mesh maturity schedule constructed
from the logical inductor computations.
Paper node: `thm:recurringunbiasednessexp` -/
theorem BoundedSequence.recurringunbiasednessexp
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).expect P i) truth) 0 := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).expect P i
  let meshTruth : ℕ → ℝ := meshTheoryTruth As P DP hworld
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : q ≠ 0 := ne_of_gt (meshNormScale_pos b)
  have haff := (hexact.normalizedMesh_determined hworld b).recunbiasedaff_ofComputations
    (h.normalizedMesh_poly b) hWgen hWdiv
      (normalizedMesh_magnitude_le_one b hshare) hworld
  have hscaled : HasLimitPoint
      (fun n => q * weightedBias w market meshTruth n) 0 := by
    have haff' : HasLimitPoint
        (weightedBias w (fun i => q * market i) (fun i => q * meshTruth i)) 0 := by
      simpa only [w, market, meshTruth, q, normalizedMesh, normalizedMeshTruth,
        AffineCombination.scale_price, EF.denote_const, meshAffine_price_diagonal] using haff
    have heq : weightedBias w (fun i => q * market i) (fun i => q * meshTruth i) =
        fun n => q * weightedBias w market meshTruth n := by
      funext n
      exact weightedBias_const_mul w market meshTruth q n
    rwa [heq] at haff'
  have hmeshBias : HasLimitPoint (weightedBias w market meshTruth) 0 :=
    hasLimitPoint_zero_of_const_mul hq hscaled
  let d : ℕ → ℝ := fun n => weightedAverage w (fun i => meshTruth i - truth i) n
  have herr : Tendsto (fun n => meshTruth n - truth n) Filter.atTop (nhds 0) := by
    simpa only [meshTruth] using
      hexact.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare
  have hd : Tendsto d Filter.atTop (nhds 0) :=
    weightedAverage_tendsto_zero_of_tendsto_zero
      (fun n => (hWdiv.1 n).1) hWdiv.2 herr
  have hsum : HasLimitPoint (fun n => weightedBias w market meshTruth n + d n) 0 :=
    hasLimitPoint_add_tendsto_zero hmeshBias hd
  apply hsum.congrFun
  filter_upwards [hWdiv.eventually_prefixSum_pos] with n hn
  dsimp only [d]
  rw [weightedBias, weightedBias]
  rw [← weightedAverage_add w (fun i => market i - meshTruth i)
    (fun i => meshTruth i - truth i) (ne_of_gt hn)]
  congr 1
  funext i
  ring

/-- Paper-facing nonnegative `thm:prandexp`, without historical-verifier premises.
Paper node: `thm:prandexp` -/
theorem BoundedSequence.prandexp
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : PseudorandomAbove truth f P) :
    (fun n => (As n).expect P n) ≳ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : 0 < q := meshNormScale_pos b
  have hpseudoMesh := hexact.normalizedMeshTruth_pseudorandomAbove
    hdet hworld b hshare hpseudo
  have haff :=
    AffineCombination.DeterminedViaTheory.lic_prandaff_above
      (h.normalizedMesh_poly b) (hexact.normalizedMesh_determined hworld b)
      (h.normalizedMesh_boundedPrices b hP)
      (normalizedMesh_magnitude_le_one b hshare) hworld f
      (AffineCombination.patientClockOfInductor (h.normalizedMesh_poly b)
        (hexact.normalizedMesh_determined hworld b) hworld f) hpseudoMesh
  have hscaled : (fun n => q * (As n).expect P n) ≳ₙ (fun _ => 0) := by
    simpa only [q, normalizedMesh, AffineCombination.scale_price, EF.denote_const,
      meshAffine_price_diagonal] using haff
  exact asympGE_zero_of_const_mul_pos hq hscaled

/-- The nonpositive comparison direction of `thm:prandexp`, with constructed maturity.
Paper node: `thm:prandexp` -/
theorem BoundedSequence.prandexp_below
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : PseudorandomBelow truth f P) :
    (fun n => (As n).expect P n) ≲ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : 0 < q := meshNormScale_pos b
  have hpseudoMesh := hexact.normalizedMeshTruth_pseudorandomBelow
    hdet hworld b hshare hpseudo
  have haff :=
    AffineCombination.DeterminedViaTheory.lic_prandaff_below
      (h.normalizedMesh_poly b) (hexact.normalizedMesh_determined hworld b)
      (h.normalizedMesh_boundedPrices b hP)
      (normalizedMesh_magnitude_le_one b hshare) hworld f
      (AffineCombination.patientClockOfInductor (h.normalizedMesh_poly b)
        (hexact.normalizedMesh_determined hworld b) hworld f) hpseudoMesh
  have hscaled : (fun n => q * (As n).expect P n) ≲ₙ (fun _ => 0) := by
    simpa only [q, normalizedMesh, AffineCombination.scale_price, EF.denote_const,
      meshAffine_price_diagonal] using haff
  exact asympLE_zero_of_const_mul_pos hq hscaled

/-- Exact two-sided expectation pseudorandomness, without verifier premises.
Paper node: `thm:prandexp` -/
theorem BoundedSequence.prandexp_eq
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : Pseudorandom truth f P) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => 0) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    fun n φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨h.prandexp_below hexact hdet b hshare hworld f hpseudo.2,
    h.prandexp hexact hdet b hshare hworld f hpseudo.1⟩

end LUVCombination

/-! ## Sentence-frequency specializations -/

/-- `thm:prand`, varied-pseudorandom-above branch with constructed maturity schedules.
Paper node: `thm:prand` -/
theorem lic_learning_varied_pseudorandom_above
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (p : ℕ → ℚ) (pFeature : ℕ → EF)
    (hφ : RpnSentenceCodes φ) (hp : GeneratedRatFeature P p pFeature)
    (truth : ℕ → ℝ) (htruth : AffineCombination.TheoryTruth φ DP truth)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : VariedPseudorandomAbove truth p f P) :
    (fun n ↦ P n (φ n)) ≳ₙ (fun n ↦ (p n : ℝ)) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hdet := htruth.sentenceMinusFeature_determined hp
  have hres := hdet.lic_prandaff_above
    (AffineCombination.sentenceMinusFeature_polySequence φ pFeature hφ hp)
    (AffineCombination.sentenceMinusFeature_bounded φ pFeature hp hP hpProb)
    (fun i ↦ by simp) hworld f
    (AffineCombination.patientClockOfInductor
      (AffineCombination.sentenceMinusFeature_polySequence φ pFeature hφ hp)
      hdet hworld f) hpseudo
  intro ε hε
  filter_upwards [hres ε hε] with n hn
  rw [AffineCombination.sentenceMinusFeature_price, hp.denote n] at hn
  linarith

/-- `thm:prand`, varied-pseudorandom-below branch with constructed maturity schedules.
Paper node: `thm:prand` -/
theorem lic_learning_varied_pseudorandom_below
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (p : ℕ → ℚ) (pFeature : ℕ → EF)
    (hφ : RpnSentenceCodes φ) (hp : GeneratedRatFeature P p pFeature)
    (truth : ℕ → ℝ) (htruth : AffineCombination.TheoryTruth φ DP truth)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : VariedPseudorandomBelow truth p f P) :
    (fun n ↦ P n (φ n)) ≲ₙ (fun n ↦ (p n : ℝ)) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hdet := htruth.sentenceMinusFeature_determined hp
  have hres := hdet.lic_prandaff_below
    (AffineCombination.sentenceMinusFeature_polySequence φ pFeature hφ hp)
    (AffineCombination.sentenceMinusFeature_bounded φ pFeature hp hP hpProb)
    (fun i ↦ by simp) hworld f
    (AffineCombination.patientClockOfInductor
      (AffineCombination.sentenceMinusFeature_polySequence φ pFeature hφ hp)
      hdet hworld f) hpseudo
  intro ε hε
  filter_upwards [hres ε hε] with n hn
  rw [AffineCombination.sentenceMinusFeature_price, hp.denote n] at hn
  linarith

/-- Exact two-sided `thm:prand`, without historical-verifier premises.
Paper node: `thm:prand` -/
theorem lic_learning_varied_pseudorandom
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (p : ℕ → ℚ) (pFeature : ℕ → EF)
    (hφ : RpnSentenceCodes φ) (hp : GeneratedRatFeature P p pFeature)
    (truth : ℕ → ℝ) (htruth : AffineCombination.TheoryTruth φ DP truth)
    (hpProb : ∀ n, 0 ≤ (p n : ℝ) ∧ (p n : ℝ) ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (hpseudo : VariedPseudorandom truth p f P) :
    (fun n ↦ P n (φ n)) ≈ₙ (fun n ↦ (p n : ℝ)) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hdet := htruth.sentenceMinusFeature_determined hp
  have hres := hdet.lic_prandaff
    (AffineCombination.sentenceMinusFeature_polySequence φ pFeature hφ hp)
    (AffineCombination.sentenceMinusFeature_bounded φ pFeature hp hP hpProb)
    (fun i ↦ by simp) hworld f
    (AffineCombination.patientClockOfInductor
      (AffineCombination.sentenceMinusFeature_polySequence φ pFeature hφ hp)
      hdet hworld f) hpseudo
  show Filter.Tendsto (fun n ↦ P n (φ n) - (p n : ℝ)) Filter.atTop (nhds 0)
  simpa only [AsympEq, AffineCombination.sentenceMinusFeature_price,
    hp.denote, sub_zero] using hres

/-- Lower half of fixed-frequency `thm:benford`, with maturity and settlement both
constructed internally: no operational infrastructure hypothesis remains.
Paper node: `thm:benford` -/
theorem lic_learning_pseudorandom_frequency_above
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (truth : ℕ → ℝ) (htruth : AffineCombination.TheoryTruth φ DP truth)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (hpseudo : PseudorandomFrequency truth p f P) :
    (fun n ↦ P n (φ n)) ≳ₙ (fun _ ↦ p) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  intro ε hε
  by_cases hp0 : p = 0
  · subst p
    exact Filter.Eventually.of_forall fun n ↦ by
      have hn := (hP n (φ n)).1
      linarith
  · have hp_pos : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    have hinterval : max 0 (p - ε / 2) < p := max_lt hp_pos (by linarith)
    obtain ⟨q, hqlow, hqhigh⟩ := exists_rat_btwn hinterval
    have hq0 : 0 ≤ (q : ℝ) :=
      (le_max_left 0 (p - ε / 2)).trans hqlow.le
    have hq1 : (q : ℝ) ≤ 1 := hqhigh.le.trans hp.2
    have hlearn := lic_learning_varied_pseudorandom_above
      P DP φ (fun _ ↦ q) (AffineCombination.constantRatFeature q)
      hφ (AffineCombination.constantRatFeature_generated P q)
      truth htruth (fun _ ↦ ⟨hq0, hq1⟩) hworld f
      (hpseudo.variedAbove_of_lt q hqhigh)
    filter_upwards [hlearn (ε / 2) (by linarith)] with n hn
    have hqnear : p - ε / 2 < (q : ℝ) :=
      (le_max_right 0 (p - ε / 2)).trans_lt hqlow
    linarith

/-- Upper half of fixed-frequency `thm:benford`, with maturity constructed internally.
Paper node: `thm:benford` -/
theorem lic_learning_pseudorandom_frequency_below
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (truth : ℕ → ℝ) (htruth : AffineCombination.TheoryTruth φ DP truth)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (hpseudo : PseudorandomFrequency truth p f P) :
    (fun n ↦ P n (φ n)) ≲ₙ (fun _ ↦ p) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  intro ε hε
  by_cases hp1 : p = 1
  · subst p
    exact Filter.Eventually.of_forall fun n ↦ by
      have hn := (hP n (φ n)).2
      linarith
  · have hp_lt_one : p < 1 := lt_of_le_of_ne hp.2 hp1
    have hinterval : p < min 1 (p + ε / 2) := lt_min hp_lt_one (by linarith)
    obtain ⟨q, hqlow, hqhigh⟩ := exists_rat_btwn hinterval
    have hq0 : 0 ≤ (q : ℝ) := hp.1.trans hqlow.le
    have hq1 : (q : ℝ) ≤ 1 :=
      hqhigh.le.trans (min_le_left 1 (p + ε / 2))
    have hlearn := lic_learning_varied_pseudorandom_below
      P DP φ (fun _ ↦ q) (AffineCombination.constantRatFeature q)
      hφ (AffineCombination.constantRatFeature_generated P q)
      truth htruth (fun _ ↦ ⟨hq0, hq1⟩) hworld f
      (hpseudo.variedBelow_of_lt q hqlow)
    filter_upwards [hlearn (ε / 2) (by linarith)] with n hn
    have hqnear : (q : ℝ) < p + ε / 2 :=
      hqhigh.trans_le (min_le_right 1 (p + ε / 2))
    linarith

/-- Exact fixed-frequency `thm:benford`; the infrastructure contains clocks only.
Paper node: `thm:benford` -/
theorem lic_learning_pseudorandom_frequency
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (truth : ℕ → ℝ) (htruth : AffineCombination.TheoryTruth φ DP truth)
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) (hpseudo : PseudorandomFrequency truth p f P) :
    (fun n ↦ P n (φ n)) ≈ₙ (fun _ ↦ p) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨
    lic_learning_pseudorandom_frequency_below P DP φ hφ truth htruth p hp hworld
      f hpseudo,
    lic_learning_pseudorandom_frequency_above P DP φ hφ truth htruth p hp hworld
      f hpseudo⟩

end LogicalInduction
