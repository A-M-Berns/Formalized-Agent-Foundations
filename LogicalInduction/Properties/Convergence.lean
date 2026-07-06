/-
# `thm:con` — Convergence (reduction + arbitrage-trader interface)
-/
import LogicalInduction.Properties.Basic

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


/-- **The oscillation-arbitrage trader exists and exploits** (`app:con`, the genuine hard
core — currently `sorry`).

Given a rational oscillation of `Pₙφ` across `[a, b]` (price `< a` i.o. and `> b` i.o.), with
plausible worlds available every day, there is an *efficiently computable* trader that
exploits `P`.

**The construction is genuinely subtle — hysteresis is required.** A *memoryless* target
holding `T(Pₙφ)` (hold a share when cheap, none when dear) does **not** work: its net worth is
`≈ Σ T(Pₙφ)·ΔPₙφ ≈ ∫ T dP`, and since `T` is a function of price alone this integral is
*path-independent* — it telescopes to `G(P_N) − G(P₀)` (a bounded state function) and nets
**zero over a closed oscillation cycle**. So a memoryless trader stays bounded and cannot
exploit. This is exactly the "discontinuous / not-well-formed trader" subtlety the paper flags
(`sec:convergence`): the real arbitrage needs a **stopping-time / hysteresis** rule — *buy* when
`Pₙφ < a`, then **hold** (memory!) until some later `m` with `Pₘφ > b`, then *sell* — so that
each completed swing banks `Pₘφ − Pₙφ ≥ b − a` at no risk (position closed ⇒ payout cancels),
and infinitely many swings give unbounded upside off bounded downside. Encoding that
path-dependent rule as a continuous `EF`-history function is the deferred work.

Status of the two ingredients:
- *Efficient computability — RESOLVED.* Such a trader references two consecutive days' prices;
  the day-`(n-1)` feature is now e.c. via `PolyEF.pricePred` (`Computable.lean`, the prec-fueled
  `predc`). So once the trader is written, its e.c. certification is in reach.
- *Exploitation inequality — the remaining hard core.* Constructing the hysteresis `EF` and
  proving its net worth is bounded below yet unbounded above under the oscillation hypothesis is
  a genuine discrete-arbitrage lemma (the paper itself sidesteps it in `app:con` by routing
  convergence through `thm:tbo`). Not yet formalized.

`sorry`, honestly; nothing is stubbed, and the earlier memoryless-`T` sketch is retracted as
mathematically insufficient. -/
theorem oscillation_exploitable (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (a b : ℚ) (hab : (a : ℝ) < b) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∃ Tr : Trader, EfficientlyComputable Tr ∧ Tr.Exploits P DP := by
  sorry


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
