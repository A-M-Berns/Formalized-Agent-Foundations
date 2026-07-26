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

#print axioms EfficientlyComputableTok₂.toTok₃
#print axioms EfficientlyComputableTok.toTok₃

end LogicalInduction
