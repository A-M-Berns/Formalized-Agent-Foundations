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

**Why this is blocked — a genuine `def:ec` fidelity limit (type-`(c)`), surfaced not stubbed.**
The investigation below is recorded because it pins down *exactly* what fails; see `PROGRESS.md`
OPEN RISK 4.

Every trader whose day-`n` coefficient is a **bounded-depth** `EF` (references a fixed window
`Pₙ, Pₙ₋₁, …, Pₙ₋d`) provably fails to exploit a *smooth* oscillation:
- *Memoryless target-holding* `c_n = T(Pₙ) − T(Pₙ₋₁)` telescopes the position to `T(Pₙ) − T(P₀)`
  (a state function of the current price); its net worth is `≈ ∫ T dP`, path-independent, and
  nets ~0 over a closed cycle. (The earlier "just use `Pₙ` and `Pₙ₋₁`" sketch — retracted.)
- *Mean-reversion* `c_n = Pₙ₋₁ − Pₙ` does slightly better: its net worth is exactly
  `(P_N² − P₀²)/2 + ½·Σ(Pᵢ − Pᵢ₋₁)²` (in the `payout = 0` world) — it harvests the price's
  **quadratic variation**. But a smooth ramp from `a` to `b` in `M` steps contributes
  `≈ (b−a)²/M → 0`, so an adversary that oscillates *smoothly* keeps the quadratic variation
  bounded and this trader stays bounded too.

Banking the full `b − a` per swing *regardless of smoothness* requires **holding a fixed
position through the whole ramp** and flipping it only at the thresholds — a stopping-time /
**hysteresis** rule (buy at `a`, hold until `> b`, sell). "Am I currently holding" depends on how
long ago the price last crossed `a` vs `b` — an **unbounded look-back**, i.e. a **linear-depth**
(size-`Θ(n)`) `EF`.

And here is the wall: our `EfficientlyComputable` requires a `Code` that outputs the strategy's
`Encodable.encode` — the `EF.toNat`, a **`Nat.pair`-nested number whose bit-length quadruples per
depth level** (measured: `6, 23, 91, 362, 1445, …` bits at depth `0,1,2,3,4` — `≈ 6·4ᵈ`). A
linear-depth feature therefore has a `~4ⁿ`-bit code, which **no `evaln (poly n)` run can even
write down**. So the hysteresis trader — legal under the paper's poly-*size* `def:ec` (a size-`n`
syntax tree is poly-size) — is **excluded by our poly-*runtime*-of-`toNat` model**. Our e.c.
class is thus strictly *smaller* than the paper's on exactly the deep-but-poly-size strategies
convergence needs, so `IsLogicalInductor` does not forbid the exploiter, and `thm:con` is not
derivable as stated. This is not a trader to build; it is a **trust-surface decision** (redefine
`EfficientlyComputable` to bound the poly *size of a structural description*, not the runtime of
the `Nat.pair` `toNat`) that needs Anson before proceeding. Kept `sorry`, honestly. -/
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
