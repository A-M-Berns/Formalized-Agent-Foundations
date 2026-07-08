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

**Status update — the `def:ec` wall (OPEN RISK 4) is gone; this is now a construction task.**
The exploiter here is a **hysteresis** trader: buy one share whenever the price dips below `a`,
hold through the ramp, sell when it rises above `b`, banking `b − a` per swing *regardless of
smoothness*. "Am I currently holding" is an unbounded look-back — a **linear-depth**, size-`Θ(n)`
`EF`. Under the *old* whole-number-`toNat` `EfficientlyComputable` that feature's code was a
`~4ⁿ`-bit number, unemittable in `evaln (poly n)`, so the exploiter fell outside the e.c. class
and `thm:con` genuinely did not follow. Bounded-depth substitutes provably fail (memoryless
target-holding telescopes to a path-independent state function; mean-reversion harvests only
quadratic variation, which a smooth ramp drives to `0`).

That obstruction is **resolved at the definition level**: `EfficientlyComputableTok` (the
token-indexed, poly-*size* model — see `Criterion.lean` and `PROGRESS.md` OPEN RISK 4) admits
strategies whose stream is poly-*length* with poly-*value* tokens, which is exactly what a
size-`Θ(n)` structural description of the hysteresis feature is. So the exploiter is now inside
the e.c. class in principle, `IsLogicalInductor` forbids it, and `thm:con` *does* follow — **once
the trader is actually built and certified**. Two concrete pieces of real work remain (neither a
trust-surface question):
1. Construct the hysteresis `EF` — a size-`Θ(n)` running-state feature (its shape grows with `n`,
   unlike every trader certified so far) — prove it banks `≥ b − a` per completed swing, and feed
   the accumulation to `exploits_of_ge_partialSums`.
2. Discharge its e.c.: the existing `ecTok_of_tokenList`/`PolyTokenStream` layer only handles
   **fixed-length** streams (bounded-shape strategies); a size-`Θ(n)` strategy has a *growing*
   stream, so it needs a **varying-length** emission helper (a genuine generalization, not yet
   built). The definition supports it; the tooling does not yet.

Per Rule 1 (no arithmetic stub may stand in for a trader) this stays `sorry` until both exist. -/
theorem oscillation_exploitable (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (a b : ℚ) (hab : (a : ℝ) < b) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∃ Tr : Trader, EfficientlyComputableTok Tr ∧ Tr.Exploits P DP := by
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
