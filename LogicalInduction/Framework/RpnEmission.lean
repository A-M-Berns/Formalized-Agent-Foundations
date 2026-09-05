import LogicalInduction.Framework.DigitArith
import LogicalInduction.Framework.RpnSentence
import LogicalInduction.Framework.Emission
import LogicalInduction.Framework.RpnSplice

/-!
# RPN emission bridges

The realization half of `def:ec` (tex:753) in the **token-metered** model: the bridges that
turn an emission certificate into `EfficientlyComputable`, with the decode routed through
`unRpn ∘ undigitize`.

* **The escape splice, per position.** `escExpandFold_range` and `escExpand_eq_flatMap`
  re-express `escExpand` as a `flatMap` over token positions, each position's decision taken
  at the escape mode of the prefix before it, so that a digit-level segment stream can
  reproduce the splice position by position.
* **The escape-slot scan.** `PolySegStream.escModeScan` runs the escape-slot automaton over
  an arbitrary digit `PolySegStream`. It is the token-model twin of
  `PolySegStream.freezeModeScan` (`Framework/DigitArith.lean`).
* **The realization chain.** `clockedTokens_eq_of_emission` → `ec_of_rawClocked` →
  `ec_of_rawSegStream`. Its reusable step is `PolySegStream.clockedTokens_certificate`,
  which says a polynomial segment stream is a clocked emission of itself; the machine-model
  compilers and the conditioning transducer consume it too.
* **The model inclusions.** `EfficientlyComputable.ofDigitEmitter` and `.ofTokenEmitter`
  carry a digit- or token-metered certificate into the class, and
  `IsLogicalInductor.noExploitTok` / `.noExploitDigit` are the no-exploitation forms the §4
  property proofs invoke for their concretely constructed traders.
* **The trader constructors.** `RpnSpliceStream.ec`,
  `EfficientlyComputable.ofSingleTradeBlocks` and `.ofTradeBlocks` are the token-metered
  entry points a client builds with; their write-out mirrors are in
  `Framework/WriteOut.lean`.

**Design** (`dd:fuel`). What is metered here is the token stream: a certificate bounds both
how many tokens day `n` emits and how large each one is. The write-out class that keeps the
first bound and drops the second is `BigTokenStream` (`Framework/WriteOut.lean`).

**Design.** `Nat.sqrt` is locally irreducible file-wide; see the note in
`Framework/Emission.lean`.

Paper node: `def:ec` (token-metered sentence slots).
-/

namespace LogicalInduction

open Nat.Partrec (Code)
open Nat.Partrec.Code

attribute [local irreducible] Nat.sqrt

/-! ## The per-position range form of the escape splice -/

/-- Prefix form of the escape splice: expanding the first `count` emitted tokens is the
position-wise `flatMap`, with each position's decision taken at the escape mode of the
prefix before it. -/
lemma escExpandFold_range (tf : ℕ → ℕ) (n count : ℕ) :
    escExpandFold 0 ((List.range count).map fun j => tf (Nat.pair n j)) =
      (List.range count).flatMap fun j =>
        if escModeList (vpre tf n j) = 1 ∨ escModeList (vpre tf n j) = 3
        then if tf (Nat.pair n j) = 0 then [1, 0, 2]
          else [1, tf (Nat.pair n j)]
        else [tf (Nat.pair n j)] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.flatMap_append,
        escExpandFold_append, ih]
      have hmode : List.foldl escModeStep 0
          ((List.range count).map fun j => tf (Nat.pair n j)) =
          escModeList (vpre tf n count) := rfl
      rw [hmode]
      simp [escExpandFold]

/-- The escape splice of a full token stream, per position. -/
lemma escExpand_eq_flatMap {ts : List ℕ} {tf : ℕ → ℕ} {n : ℕ}
    (hget : ∀ i, i < ts.length → tf (Nat.pair n i) = ts.getD i 0) :
    escExpand ts = (List.range ts.length).flatMap fun j =>
      if escModeList (vpre tf n j) = 1 ∨ escModeList (vpre tf n j) = 3
      then if tf (Nat.pair n j) = 0 then [1, 0, 2]
        else [1, tf (Nat.pair n j)]
      else [tf (Nat.pair n j)] := by
  have hts : ts = (List.range ts.length).map fun j => tf (Nat.pair n j) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [hget i (by simpa using h2)]
      exact (List.getD_eq_getElem ts 0 (by simpa using h2)).symm
  calc escExpand ts = escExpandFold 0 ts :=
        (escExpandFold_eq_escExpand ts.length ts le_rfl).symm
    _ = _ := by
        conv_lhs => rw [hts]
        rw [escExpandFold_range]

/-! ## The escape-slot scan -/

/-- The escape-slot automaton is poly-fueled over any digit `PolySegStream`
(input `⟨n, j⟩`). -/
lemma PolySegStream.escModeScan {s : ℕ → List ℕ} (h : PolySegStream s) :
    ∃ c, PolyFueled c (fun z =>
      escModeList (vpre (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0)
        z.unpair.1 z.unpair.2)) := by
  obtain ⟨-, hbig⟩ := h.undigitizeTokens
  obtain ⟨ctc, htc⟩ := hbig.clampVal (PolyFueled.const 8)
  obtain ⟨cad, had⟩ := addc_polyFueled
  have hn := PolyFueled.left
  have hj := PolyFueled.left.comp PolyFueled.right
  have hprev := PolyFueled.right.comp PolyFueled.right
  have htok := htc.comp (hn.pair hj)
  have heq6 := had.comp ((subc_polyFueled.comp (htok.pair (PolyFueled.const 6))).pair
    (subc_polyFueled.comp ((PolyFueled.const 6).pair htok)))
  have heq1 := had.comp ((subc_polyFueled.comp (htok.pair (PolyFueled.const 1))).pair
    (subc_polyFueled.comp ((PolyFueled.const 1).pair htok)))
  have heq7 := had.comp ((subc_polyFueled.comp (htok.pair (PolyFueled.const 7))).pair
    (subc_polyFueled.comp ((PolyFueled.const 7).pair htok)))
  have hA3 := ifzSel_polyFueled.comp
    (((PolyFueled.const 4).pair (PolyFueled.const 0)).pair heq7)
  have hA2 := ifzSel_polyFueled.comp (((PolyFueled.const 4).pair hA3).pair heq1)
  have hA1 := ifzSel_polyFueled.comp (((PolyFueled.const 3).pair hA2).pair heq6)
  have hA0 := ifzSel_polyFueled.comp (((PolyFueled.const 1).pair hA1).pair htok)
  have hM1 := ifzSel_polyFueled.comp
    (((PolyFueled.const 2).pair (PolyFueled.const 0)).pair
      (subc_polyFueled.comp (hprev.pair (PolyFueled.const 1))))
  have hstep := ifzSel_polyFueled.comp ((hA0.pair hM1).pair hprev)
  refine ⟨_, PolyFueled.prec (PolyFueled.const 0) hstep
    (st := fun n j =>
      escModeList (vpre (fun w => (undigitize (s w.unpair.1)).getD w.unpair.2 0) n j))
    (fun n => rfl)
    (fun n j => ?_)
    ((IsPolyBounded.linear 4).of_le fun z =>
      le_trans (escModeList_le _) (by omega))⟩
  rw [vpre_succ, escModeList_snoc, ← escModeStep_clamp]
  simp only [escModeStep, Nat.unpair_pair, ifzSelFn, Nat.reduceAdd]
  split_ifs <;> omega

/-! ## The token-metered realization bridges -/

/-- A length/token emission under one polynomial clock *is* the clocked token stream.
This is the step shared by every raw-emission certificate below. -/
lemma clockedTokens_eq_of_emission (raw : ℕ → List ℕ)
    (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ)
    (hlength : ∀ n, evaln (a * (n + 1) ^ k + a) lengthCode n =
      some (raw n).length)
    (hsize : ∀ n, (raw n).length ≤ a * (n + 1) ^ k + a)
    (htoken : ∀ n i, i < (raw n).length →
      evaln (a * (n + 1) ^ k + a) tokenCode (Nat.pair n i) =
        some ((raw n).getD i 0)) :
    ∀ n, clockedTokens lengthCode tokenCode (a * (n + 1) ^ k + a) n = raw n := by
  intro n
  unfold clockedTokens
  rw [hlength n]
  simp only []
  rw [min_eq_left (hsize n)]
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp only [List.getElem_ofFn]
    rw [htoken n i hright, Option.getD_some]
    exact List.getD_eq_get (raw n) 0 ⟨i, hright⟩

/-- A trader whose day-`n` decode is a clocked token stream is efficiently computable. -/
lemma ec_of_rawClocked (Tr : Trader) (raw : ℕ → List ℕ)
    (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ)
    (hclock : ∀ n, clockedTokens lengthCode tokenCode (a * (n + 1) ^ k + a) n = raw n)
    (hstrategy : ∀ n, strategyOfTokens n (unRpn (undigitize (raw n))) = Tr.strat n) :
    EfficientlyComputable Tr := by
  refine ⟨lengthCode, tokenCode, a, k, congrArg Trader.mk (funext fun n => ?_)⟩
  change strategyOfTokens n (unRpn (undigitize
    (clockedTokens lengthCode tokenCode (a * (n + 1) ^ k + a) n))) = Tr.strat n
  rw [hclock n]
  exact hstrategy n

/-- **A polynomial segment stream is a clocked emission of itself.** Its poly-fueled
length and token codes, run under one polynomial day clock dominating both fuel bounds and
the stream length, produce the stream on the nose. This is the certificate the trader
compiler consumes, in both the fuel model (`ec_of_rawSegStream`) and the machine model
(`RpnSentenceCodes.toMachine`, `BigTokenStream.toMachine`). -/
lemma PolySegStream.clockedTokens_certificate {raw : ℕ → List ℕ} (h : PolySegStream raw) :
    ∃ (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ),
      ∀ n, clockedTokens lengthCode tokenCode (a * (n + 1) ^ k + a) n = raw n := by
  obtain ⟨ct, cl, tokenFn, lenFn, htokf, hlenf, hlens, hspec⟩ := h
  have hlenRaw : PolyFueled cl (fun n => (raw n).length) :=
    hlenf.of_eq (fun n => (hlens n).symm)
  obtain ⟨bc, hfc, _, a₀, k₀, hk₀⟩ := htokf
  obtain ⟨bl, hfl, hlenBounded, hblBounded⟩ := hlenRaw
  set len := fun n => (raw n).length with hlendef
  have hbcbound : IsPolyBounded (fun n => a₀ * (Nat.pair n (len n) + 1) ^ k₀ + a₀) :=
    (show IsPolyBounded (fun x => a₀ * (x + 1) ^ k₀ + a₀) from
      ⟨a₀, k₀, fun _ => le_rfl⟩).comp
      ((IsPolyBounded.linear 0).pair hlenBounded)
  obtain ⟨A, K, hAK⟩ := (hblBounded.max hbcbound).max hlenBounded
  refine ⟨cl, ct, A, K, clockedTokens_eq_of_emission raw cl ct A K
    (fun n => ?_) (fun n => ?_) (fun n i hi => ?_)⟩
  · exact evaln_mono
      ((le_max_left _ _).trans ((le_max_left _ _).trans (hAK n))) (hfl n)
  · exact (le_max_right _ _).trans (hAK n)
  · have hple : Nat.pair n i ≤ Nat.pair n (len n) :=
      pair_le_pair_right' n (le_of_lt hi)
    have hbc : bc (Nat.pair n i) ≤ A * (n + 1) ^ K + A := by
      calc bc (Nat.pair n i) ≤ a₀ * (Nat.pair n i + 1) ^ k₀ + a₀ := hk₀ _
        _ ≤ a₀ * (Nat.pair n (len n) + 1) ^ k₀ + a₀ := by gcongr
        _ ≤ A * (n + 1) ^ K + A :=
          (le_max_right _ _).trans ((le_max_left _ _).trans (hAK n))
    have key := hfc (Nat.pair n i)
    rw [hspec n i (by rw [← hlens n]; exact hi)] at key
    exact evaln_mono hbc key

/-- Any `PolySegStream` whose contracted undigitized decode is the target trader
realizes an `EfficientlyComputable` certificate. -/
lemma ec_of_rawSegStream (Tr : Trader) {raw : ℕ → List ℕ}
    (h : PolySegStream raw)
    (hstrategy : ∀ n, strategyOfTokens n (unRpn (undigitize (raw n))) = Tr.strat n) :
    EfficientlyComputable Tr := by
  obtain ⟨lc, tc, a, k, hclock⟩ := h.clockedTokens_certificate
  exact ec_of_rawClocked Tr raw lc tc a k hclock hstrategy

/-! ## The model inclusions

A token-model or digit-model certificate transfers into the token-metered class by
the escape splice — every sentence-slot token is prefixed by the escape tag, a poly
digit-level rewrite whose contracted decode is the original strategy
(`strategyOfTokens_unRpn_escExpand`). -/

/-- **The digit-emitter constructor**: a digit-metered certificate
(`EfficientlyComputableDigit`, internal) is efficiently computable — the escape splice
transfers the certificate verbatim.
Paper node: `def:ec` -/
theorem EfficientlyComputable.ofDigitEmitter {Tr : Trader}
    (h : EfficientlyComputableDigit Tr) : EfficientlyComputable Tr := by
  obtain ⟨lc, tc, a, k, hTr⟩ := h
  let ds : ℕ → List ℕ := fun n =>
    clockedTokens lc tc (PrefixPatchCompile.ecClock a k n) n
  have hds : PolySegStream ds :=
    PrefixPatchCompile.clockedTokens_polySegStream lc tc a k
  obtain ⟨⟨cc, hcnt⟩, hbig⟩ := hds.undigitizeTokens
  have hbigCopy := hbig
  obtain ⟨clen, cdig, hlen, hdig⟩ := hbig
  obtain ⟨cm, hmode⟩ := hds.escModeScan
  obtain ⟨cad, had⟩ := addc_polyFueled
  obtain ⟨cml, hml⟩ := mul_polyFueled
  -- Per-position digit segment: escape-prefix the sentence slots.
  have hcopy := hbigCopy.blockSeg
  have hesc := (PolySegStream.block (PolyFueled.const 1)).append hcopy
  have hpoison := (PolySegStream.block (PolyFueled.const 1)).append
    ((PolySegStream.block (PolyFueled.const 0)).append
      (PolySegStream.block (PolyFueled.const 2)))
  have hescSafe := hpoison.ifZero hesc hlen
  have heq1 := had.comp ((subc_polyFueled.comp (hmode.pair (PolyFueled.const 1))).pair
    (subc_polyFueled.comp ((PolyFueled.const 1).pair hmode)))
  have heq3 := had.comp ((subc_polyFueled.comp (hmode.pair (PolyFueled.const 3))).pair
    (subc_polyFueled.comp ((PolyFueled.const 3).pair hmode)))
  have hsel := hml.comp (heq1.pair heq3)
  have hseg := hescSafe.ifZero hcopy hsel
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
      digitize_flatMap]
    refine List.flatMap_congr fun j hj => ?_
    simp only [Nat.unpair_pair]
    by_cases hm : escModeList (vpre
        (fun w => (undigitize (ds w.unpair.1)).getD w.unpair.2 0) n j) = 1 ∨
        escModeList (vpre
        (fun w => (undigitize (ds w.unpair.1)).getD w.unpair.2 0) n j) = 3
    · rw [if_pos (by
        rcases hm with hm | hm <;> rw [hm]), if_pos hm]
      by_cases hz : (undigitize (ds n)).getD j 0 = 0
      · rw [if_pos hz]
        have hlen_zero : len4 ((undigitize (ds n)).getD j 0) = 0 := by
          rw [hz]
          exact len4_zero
        rw [if_pos hlen_zero]
        simp [digitize, hz]
      · rw [if_neg hz]
        have hlen_ne : len4 ((undigitize (ds n)).getD j 0) ≠ 0 := by
          have hpos : 0 < len4 ((undigitize (ds n)).getD j 0) :=
            (lt_len4_iff _ 0).mpr (Nat.one_le_iff_ne_zero.mpr hz)
          omega
        rw [if_neg hlen_ne]
        simp [digitize, hz]
    · rw [if_neg (by
        push_neg at hm
        simp only [Nat.mul_eq_zero]
        omega), if_neg hm]
      simp [digitize]
  apply ec_of_rawSegStream Tr hclean
  intro n
  rw [undigitize_digitize, strategyOfTokens_unRpn_escExpand]
  exact congrFun (congrArg Trader.strat hTr) n

/-- **The token-emitter constructor**: a token-metered certificate
(`EfficientlyComputableTok`, internal) is efficiently computable, through the digit
emitter.
Paper node: `def:ec` -/
theorem EfficientlyComputable.ofTokenEmitter {Tr : Trader}
    (h : EfficientlyComputableTok Tr) : EfficientlyComputable Tr :=
  EfficientlyComputable.ofDigitEmitter h.toDigit

/-- Token-model no-exploitation, through the emission constructor: the compat form the
property proofs invoke for their concretely constructed exploiting traders.
Paper node: `def:lic` -/
lemma IsLogicalInductor.noExploitTok {P : History} {DP : DeductiveProcess}
    [hLI : IsLogicalInductor P DP] :
    ∀ Tr : Trader, EfficientlyComputableTok Tr → ¬ Tr.Exploits P DP :=
  fun Tr h => hLI.noExploit Tr (EfficientlyComputable.ofTokenEmitter h)

/-- Digit-model no-exploitation, through the emission constructor.
Paper node: `def:lic` -/
lemma IsLogicalInductor.noExploitDigit {P : History} {DP : DeductiveProcess}
    [hLI : IsLogicalInductor P DP] :
    ∀ Tr : Trader, EfficientlyComputableDigit Tr → ¬ Tr.Exploits P DP :=
  fun Tr h => hLI.noExploit Tr (EfficientlyComputable.ofDigitEmitter h)

/-! ## Trader constructors

The token-metered entry points a client builds an exploiting trader with. Their write-out
mirrors — the same constructors with the per-token value bound dropped — are
`EfficientlyComputable.ofSingleTradeBlocksBig` and `.ofTradeBlocksBig`
(`Framework/WriteOut.lean`). -/

/-- **The capstone realization**: a trader whose per-day trade serialization is
RPN-spliceable is efficiently computable.
Paper node: `def:ec` -/
lemma RpnSpliceStream.ec (Tr : Trader)
    (h : RpnSpliceStream (fun n => serializeTrades (Tr.strat n).trades)) :
    EfficientlyComputable Tr := by
  obtain ⟨s, hs, hc⟩ := h
  apply ec_of_rawSegStream Tr hs.digitizeStream
  intro n
  rw [undigitize_digitize]
  have hun : unRpn (s n) = serializeTrades (Tr.strat n).trades := by
    have h0 := (hc n).unRpn_eq
    rw [show unRpn ([] : List ℕ) = [] from rfl, List.append_nil] at h0
    exact h0
  rw [hun]
  have hdecode := deserializeTrades_serializeTrades (Tr.strat n).trades
  cases hS : Tr.strat n with
  | mk trades rank_le =>
      simp only [strategyOfTokens]
      rw [hS] at hdecode
      split
      · next hnone =>
          rw [hdecode] at hnone; exact absurd hnone (by simp)
      · next trades' hsome =>
          rw [hdecode] at hsome
          obtain rfl := Option.some.inj hsome
          rw [dif_pos rank_le]

/-- **Single-trade realization over an 𝓔𝓒 sentence sequence**: a trader playing one
trade per day, with a polynomially emittable price-free coefficient stream and an
`RpnSentenceCodes` sentence sequence, is efficiently computable.  This is the entry point
used by the copy-only property families, which need only the token-metered
`RpnSentenceCodes` hypothesis rather than the stronger whole-value `PolySentenceCodes`.
Paper node: `def:ec` -/
lemma EfficientlyComputable.ofSingleTradeBlocks (Tr : Trader) (f : ℕ → EF)
    (φ : ℕ → Sentence)
    (hf : PolySegStream fun n => (f n).serialize)
    (hfree : ∀ n, (f n).priceFree)
    (hφ : RpnSentenceCodes φ)
    (hTr : ∀ n, (Tr.strat n).trades = [(f n, φ n)]) :
    EfficientlyComputable Tr := by
  obtain ⟨sφ, hsφ, hparse⟩ := hφ
  have htag : PolySegStream (fun _ : ℕ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  have hassemble : PolySegStream (fun n => (f n).serialize ++ 6 :: sφ n) :=
    ((hf.append htag).append hsφ).of_eq fun n => by
      simp [List.append_assoc]
  apply ec_of_rawSegStream Tr hassemble.digitizeStream
  intro n
  rw [undigitize_digitize]
  have hcontract : unRpn ((f n).serialize ++ 6 :: sφ n) =
      serializeTrades [(f n, φ n)] := by
    have := unRpn_tradeBlocks [((f n, φ n), sφ n)]
      (fun p hp => by
        rw [List.mem_singleton] at hp; subst hp
        exact EF.serialize_unRpnTransparent (f n) (hfree n))
      (fun p hp => by
        rw [List.mem_singleton] at hp; subst hp
        exact hparse n)
    simpa using this
  rw [hcontract]
  have hrank : ∀ trade ∈ [(f n, φ n)], trade.1.rank ≤ n := by
    intro trade htrade
    have := (Tr.strat n).rank_le
    rw [hTr n] at this
    exact this trade htrade
  have hdecode := deserializeTrades_serializeTrades [(f n, φ n)]
  cases hS : Tr.strat n with
  | mk trades rank_le =>
      have htrades : trades = [(f n, φ n)] := by
        have := hTr n; rwa [hS] at this
      subst htrades
      simp only [strategyOfTokens]
      split
      · next hnone => rw [hdecode] at hnone; exact absurd hnone (by simp)
      · next trades' hsome =>
          rw [hdecode] at hsome
          obtain rfl := Option.some.inj hsome
          rw [dif_pos hrank]

/-- **Variable-count realization over an 𝓔𝓒 sentence sequence**: a trader playing
`count n` trades on day `n` (indexed `z = ⟨n, j⟩`), with polynomially emittable
price-free coefficient streams and an `RpnSentenceCodes` sentence family, is
efficiently computable.  `EfficientlyComputable.ofTradeBlocksBig`
(`Framework/WriteOut.lean`) is the same constructor over the write-out sentence class. -/
lemma EfficientlyComputable.ofTradeBlocks (Tr : Trader)
    (count : ℕ → ℕ) (f : ℕ → EF) (φ : ℕ → Sentence)
    (hcount : ∃ c, PolyFueled c count)
    (hf : PolySegStream fun z => (f z).serialize)
    (hfree : ∀ z, (f z).priceFree)
    (hφ : RpnSentenceCodes φ)
    (hTr : ∀ n, (Tr.strat n).trades =
      (List.range (count n)).map fun j => (f (Nat.pair n j), φ (Nat.pair n j))) :
    EfficientlyComputable Tr := by
  obtain ⟨sφ, hsφ, hparse⟩ := hφ
  obtain ⟨ccount, hcountF⟩ := hcount
  have htag : PolySegStream (fun _ : ℕ => [6]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 6)
  have hseg : PolySegStream (fun z => (f z).serialize ++ 6 :: sφ z) :=
    ((hf.append htag).append hsφ).of_eq fun z => by simp [List.append_assoc]
  have hall := PolySegStream.concatVar hseg hcountF
  apply ec_of_rawSegStream Tr hall.digitizeStream
  intro n
  rw [undigitize_digitize]
  have hcontract : unRpn ((List.range (count n)).flatMap fun j =>
      (f (Nat.pair n j)).serialize ++ 6 :: sφ (Nat.pair n j)) =
      serializeTrades ((List.range (count n)).map fun j =>
        (f (Nat.pair n j), φ (Nat.pair n j))) := by
    have := unRpn_tradeBlocks ((List.range (count n)).map fun j =>
        ((f (Nat.pair n j), φ (Nat.pair n j)), sφ (Nat.pair n j)))
      (fun p hp => by
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨j, -, rfl⟩ := hp
        exact EF.serialize_unRpnTransparent _ (hfree _))
      (fun p hp => by
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨j, -, rfl⟩ := hp
        exact hparse _)
    rw [List.flatMap_map, List.map_map] at this
    exact this
  rw [hcontract]
  have hrank : ∀ trade ∈ (List.range (count n)).map fun j =>
      (f (Nat.pair n j), φ (Nat.pair n j)), trade.1.rank ≤ n := by
    intro trade htrade
    have := (Tr.strat n).rank_le
    rw [hTr n] at this
    exact this trade htrade
  have hdecode := deserializeTrades_serializeTrades
    ((List.range (count n)).map fun j => (f (Nat.pair n j), φ (Nat.pair n j)))
  cases hS : Tr.strat n with
  | mk trades rank_le =>
      have htrades : trades = (List.range (count n)).map fun j =>
          (f (Nat.pair n j), φ (Nat.pair n j)) := by
        have := hTr n; rwa [hS] at this
      subst htrades
      simp only [strategyOfTokens]
      split
      · next hnone => rw [hdecode] at hnone; exact absurd hnone (by simp)
      · next trades' hsome =>
          rw [hdecode] at hsome
          obtain rfl := Option.some.inj hsome
          rw [dif_pos hrank]

end LogicalInduction
