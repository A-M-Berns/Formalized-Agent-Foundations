/-
# RPN emission bridges (the `Tok₃` layer, part 3: fuelled scans and realization)

The poly-fuelled side of the symbol-metered emission model: the escape-slot automaton
scanned over any digit `PolySegStream`, the per-position range form of the escape
splice, and the `₃`-model realization bridges (mirrors of `ecTok₂_of_rawEmission` /
`ecTok₂_of_rawSegStream`, with the decode routed through `unRpn ∘ undigitize`).

Paper node: `def:ec` (symbol-metered sentence slots).
-/
import LogicalInduction.Framework.DigitArith
import LogicalInduction.Framework.RpnSentence

namespace LogicalInduction

open Nat.Partrec (Code)
open Nat.Partrec.Code

attribute [local irreducible] Nat.sqrt

/-! ## The per-position range form of the escape splice -/

lemma escExpandFold_range (tf : ℕ → ℕ) (n count : ℕ) :
    escExpandFold 0 ((List.range count).map fun j => tf (Nat.pair n j)) =
      (List.range count).flatMap fun j =>
        if escModeList (vpre tf n j) = 1 ∨ escModeList (vpre tf n j) = 3
        then [1, tf (Nat.pair n j)] else [tf (Nat.pair n j)] := by
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
      then [1, tf (Nat.pair n j)] else [tf (Nat.pair n j)] := by
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
  simp only []
  rw [vpre_succ, escModeList_snoc, ← escModeStep_clamp]
  simp only [escModeStep, Nat.unpair_pair, ifzSelFn, Nat.reduceAdd]
  split_ifs <;> omega

/-! ## The `₃`-model realization bridges -/

/-- Exact digit emitters instantiate the symbol-metered bounded-emulator definition. -/
lemma ecTok₃_of_rawEmission (Tr : Trader) (raw : ℕ → List ℕ)
    (lengthCode tokenCode : Nat.Partrec.Code) (a k : ℕ)
    (hlength : ∀ n, evaln (a * (n + 1) ^ k + a) lengthCode n =
      some (raw n).length)
    (hsize : ∀ n, (raw n).length ≤ a * (n + 1) ^ k + a)
    (htoken : ∀ n i, i < (raw n).length →
      evaln (a * (n + 1) ^ k + a) tokenCode (Nat.pair n i) =
        some ((raw n).getD i 0))
    (hstrategy : ∀ n, strategyOfTokens n (unRpn (undigitize (raw n))) = Tr.strat n) :
    EfficientlyComputableTok₃ Tr := by
  refine ⟨lengthCode, tokenCode, a, k, ?_⟩
  have hstrat :
      (clockedTrader₃ lengthCode tokenCode (fun n => a * (n + 1) ^ k + a)).strat =
        Tr.strat := by
    funext n
    change strategyOfTokens n (unRpn (undigitize
      (clockedTokens lengthCode tokenCode (a * (n + 1) ^ k + a) n))) = Tr.strat n
    have htoks :
        clockedTokens lengthCode tokenCode (a * (n + 1) ^ k + a) n = raw n := by
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
    rw [htoks]
    exact hstrategy n
  exact congrArg Trader.mk hstrat

/-- Any `PolySegStream` whose contracted undigitized decode is the target trader
realizes a `₃`-certificate. -/
lemma ecTok₃_of_rawSegStream (Tr : Trader) {raw : ℕ → List ℕ}
    (h : PolySegStream raw)
    (hstrategy : ∀ n, strategyOfTokens n (unRpn (undigitize (raw n))) = Tr.strat n) :
    EfficientlyComputableTok₃ Tr := by
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
  refine ecTok₃_of_rawEmission Tr raw cl ct A K (fun n => ?_) (fun n => ?_)
    (fun n i hi => ?_) hstrategy
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

#print axioms escExpand_eq_flatMap
#print axioms PolySegStream.escModeScan
#print axioms ecTok₃_of_rawSegStream

end LogicalInduction
