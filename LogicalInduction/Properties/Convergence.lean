/-
# `thm:con` — Convergence (reduction + arbitrage trader)
-/
import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.Hysteresis

namespace LogicalInduction

open Filter Topology

/-- **Reduction step for `thm:con`** (fully proved). A `[0,1]`-bounded price that does *not*
converge must **oscillate across a rational gap**: there are rationals `a < b` with the price
below `a` infinitely often and above `b` infinitely often.

This is the contrapositive of `tendsto_of_no_upcrossings` instantiated at the dense range of
`(↑) : ℚ → ℝ`; the rationality of `a, b` is what lets the arbitrage trader use them as `EF`
constants. -/
theorem exists_rat_oscillation_of_not_convergesTo (P : History) (φ : Sentence)
    (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hnc : ¬ ∃ L, ConvergesTo (fun n => P n φ) L) :
    ∃ a b : ℚ, (a : ℝ) < b ∧ (∃ᶠ n in atTop, P n φ < (a : ℝ)) ∧
      (∃ᶠ n in atTop, (b : ℝ) < P n φ) := by
  by_contra hcon
  refine hnc (tendsto_of_no_upcrossings (u := fun n => P n φ) Rat.denseRange_cast ?_
    (isBoundedUnder_of ⟨1, fun n => (hb n).2⟩) (isBoundedUnder_of ⟨0, fun n => (hb n).1⟩))
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab ⟨hA, hB⟩
  exact hcon ⟨a, b, hab, hA, hB⟩


/-- **The oscillation-arbitrage trader exists and exploits** (`app:con` — proved).

Given a rational oscillation of `Pₙφ` across `[a, b]` (price `< a` i.o. and `> b` i.o.), with
plausible worlds available every day, there is an *efficiently computable* trader that
exploits `P`.

The witness is the **hysteresis trader** (`Properties/Hysteresis.lean`, band `δ = (b−a)/4`):
a size-`Θ(n)` running holdings state — buy on dips below `a`, hold through the ramp, sell on
spikes above `b`. Its net worth is `≥ ((b−a)/2)·B₋ − (a+δ)` in *every* world (buys happen
only below `a+δ`, sells only above `b−δ`), and each completed swing adds `1` to the negative
variation `B₋`, so the oscillation drives it to unbounded upside off bounded downside.
Efficient computability is discharged through the clocked interpreter via the five-segment
`PolySegStream` emission (`hystTrader_ecTok`) — this is exactly the deep (linear-depth)
exploiter the poly-size `EfficientlyComputableTok` redefinition of `def:ec` was built to
admit (OPEN RISK 4). -/
theorem oscillation_exploitable (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (a b : ℚ) (hab : (a : ℝ) < b) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∃ Tr : Trader, EfficientlyComputableTok Tr ∧ Tr.Exploits P DP :=
  oscillation_exploitable_hyst P DP φ a b hab hb hcons hA hB


/-- **Convergence** (`thm:con`): under a logical inductor, the price of every sentence `φ`
converges. Proof: if not, the price oscillates across a rational gap
(`exists_rat_oscillation_of_not_convergesTo`), and that oscillation is exploitable
(`oscillation_exploitable`) by an e.c. trader — contradicting `def:lic`.

Hypotheses (both honest, both matching the rest of this file): prices lie in `[0,1]`, and each
day admits a plausible world (`hcons`; without it the market is vacuously unexploitable and
nothing constrains the price). -/
theorem lic_price_convergesTo (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (φ : Sentence)
    (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ L, ConvergesTo (fun n => P n φ) L := by
  by_contra hnc
  obtain ⟨a, b, hab, hA, hB⟩ := exists_rat_oscillation_of_not_convergesTo P φ hb hnc
  obtain ⟨Tr, hec, hexp⟩ := oscillation_exploitable P DP φ a b hab hb hcons hA hB
  exact hLI.noExploit Tr hec hexp

end LogicalInduction
