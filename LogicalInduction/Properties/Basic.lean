import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.RpnEmission
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Shared substrate for the property proofs

The pieces every §4 property family reuses. This module renders no paper node of its own and
carries no `Paper node` line.

* The continuous buy-signal `buySignal feat ε = max(0, feat − ε/2)`, the one-sided ramp of
  `def:ctsind` at an arbitrary feature, with its denotation, rank, nonnegativity and firing
  value. Consumed by `Coherence.sigEF` and by `Relationships.sig2EF` / `Relationships.impSig`.
* The Boolean payout laws for p.c. worlds — `PCWorld.holds_neg`, `PCWorld.holds_or`,
  `PCWorld.holds_and` — the substrate on which the coherence and logical-relationship payout
  cancellations rest. The cancellations themselves live with their families: `payout_or_of_excl`
  in `Coherence.lean`, `payout_eq_of_iff` and `payout_le_of_imp` in `Relationships.lean`.
* Three exploitation engines, the only general route from a net-worth bound to
  `Trader.Exploits`. `exploits_of_ge_partialSums` takes a world-independent lower bound on the
  partial sums; `exploits_of_nonneg_partialSums` is its equality specialization, for traders
  whose day-`i` value is the same in every plausible world; `exploits_of_bddBelow_of_unbounded`
  is `Trader.Exploits`' own definition, for traders whose growth is itself world-dependent.
  Their consumers are `ProvabilityInduction`, `Coherence`, `Relationships`,
  `AffineProvability`, `Hysteresis`, `NonDogmatism`, `UniformNonDogmatism`, `OccamBounds` and
  `UniversalSemimeasure`.
* `list_range_map_sum`, the `List.range`/`Finset.range` sum bridge used wherever a payout
  bundle is built as a list and reasoned about as a `Finset` sum (`UniversalSemimeasure`,
  `Construction/Witnesses/UniversalDovetailer.lean`).

Two design choices govern the module. Features are `EF` syntax with a denotation (`dd:dsl`), so
the buy-signal is built from the `max`/`add`/`const` constructors rather than written as a Lean
function. And the engines take the existence of a plausible world each day (`hcons`) as an
explicit hypothesis rather than through `IsLogicalInductor`, so they are usable outside the
criterion.
-/

namespace LogicalInduction

open Filter Topology

/-! ## The continuous buy-signal

Every responsive coherence or relationship trader gates its portfolio by a continuous
buy-signal on a deterministic *feature* `feat` (a price gap): it trades only when `feat`
exceeds `ε/2`, and proportionally to the excess. Factoring the signal here gives its
denotation, rank, nonnegativity and firing value once. -/

/-- Continuous buy-signal `max(0, feat − ε/2)`. -/
noncomputable def buySignal (feat : EF) (ε : ℚ) : EF :=
  .max (.const 0) (.add feat (.const (-ε/2)))

@[simp] lemma buySignal_denote (feat : EF) (ε : ℚ) (P : History) :
    (buySignal feat ε).denote P = max 0 (feat.denote P + (-(ε:ℝ)/2)) := by
  simp only [buySignal, EF.denote_max, EF.denote_add, EF.denote_const, Pi.add_apply]
  push_cast; ring_nf

@[simp] lemma buySignal_rank (feat : EF) (ε : ℚ) : (buySignal feat ε).rank = feat.rank := by
  simp [buySignal]

/-- The signal is nonnegative: `0 ≤ buySignal feat ε`. A trader gated by it therefore never
takes the opposite side of its position. -/
lemma buySignal_nonneg (feat : EF) (ε : ℚ) (P : History) :
    0 ≤ (buySignal feat ε).denote P := by rw [buySignal_denote]; exact le_max_left _ _

/-- When the signal fires (`feat ≥ ε/2`), its value is exactly the excess `feat − ε/2`. -/
lemma buySignal_eq_of_pos (feat : EF) (ε : ℚ) (P : History)
    (h : (0:ℝ) ≤ feat.denote P + (-(ε:ℝ)/2)) :
    (buySignal feat ε).denote P = feat.denote P + (-(ε:ℝ)/2) := by
  rw [buySignal_denote, max_eq_right h]

/-! ## Boolean payout laws for p.c. worlds

A p.c. world evaluates compound sentences by Boolean algebra (Foundation's `val`), so its
`{0,1}` payouts compose the way a coherent probability must. -/

/-- `∼χ`-worlds falsify `χ` (Foundation: `∼χ = χ 🡒 ⊥`). -/
lemma PCWorld.holds_neg (v : PCWorld) (χ : Sentence) : v.Holds (∼χ) ↔ ¬ v.Holds χ := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- A world holds a disjunction exactly when it holds one of the disjuncts. -/
lemma PCWorld.holds_or (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋎ ψ) ↔ v.Holds φ ∨ v.Holds ψ := Iff.rfl

/-- A world holds a conjunction exactly when it holds both conjuncts. -/
lemma PCWorld.holds_and (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋏ ψ) ↔ v.Holds φ ∧ v.Holds ψ := Iff.rfl

/-! ## Exploitation engines -/

/-! ### The world-independent engines

Both take a nonnegative sequence `w` that is frequently `≥ ε` and bound the trader's plausible
net worths below by its partial sums: unbounded upside off bounded (`≥ 0`) downside is exactly
`Trader.Exploits`. `exploits_of_ge_partialSums` is the general form; the equality form below is
the ergonomic one for a trader whose day-`i` value does not depend on the world. -/

/-- Exploitation from a world-independent lower bound: if each plausible-world net worth is at
least the partial sum of a nonnegative sequence `w` that is `≥ ε` frequently, the trader
exploits. -/
lemma exploits_of_ge_partialSums (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hnonneg : ∀ i, 0 ≤ w i)
    (hge : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∑ i ∈ Finset.range (n+1), w i ≤ Tr.netWorth P v n)
    (hfreq : ∃ᶠ n in atTop, ε ≤ w n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tr.Exploits P DP := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨m, v, hv, rfl⟩
    exact le_trans (Finset.sum_nonneg (fun i _ => hnonneg i)) (hge m v hv)
  · rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hcons (g M)
    have hsub : (Finset.range (M+1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi; simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge2 : (M+1 : ℝ) * ε ≤ Tr.netWorth P v (g M) := by
      refine le_trans ?_ (hge (g M) v hv)
      calc (M+1:ℝ)*ε = ∑ _k ∈ Finset.range (M+1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M+1), w (g k) := Finset.sum_le_sum (fun k _ => hg k)
        _ = ∑ i ∈ (Finset.range (M+1)).image g, w i :=
            (Finset.sum_image (hg_mono.injective.injOn)).symm
        _ ≤ ∑ i ∈ Finset.range (g M + 1), w i :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
    have hmem : Tr.netWorth P v (g M) ∈ Tr.plausibleAssessments P DP := ⟨g M, v, hv, rfl⟩
    have hBm : B < (M+1:ℝ)*ε := by rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge2 (hB hmem)) (by linarith)

/-- Exploitation for a world-neutral trader: its day-`i` value in every plausible world equals a
fixed nonnegative sequence `w i`, with `w n ≥ ε` frequently. The equality specialization of
`exploits_of_ge_partialSums`. -/
lemma exploits_of_nonneg_partialSums (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hnonneg : ∀ i, 0 ≤ w i)
    (hval : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      Tr.netWorth P v n = ∑ i ∈ Finset.range (n+1), w i)
    (hfreq : ∃ᶠ n in atTop, ε ≤ w n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tr.Exploits P DP :=
  exploits_of_ge_partialSums Tr P DP w ε hε hnonneg
    (fun n v hv => (hval n v hv).ge) hfreq hcons

/-! ### The definitional engine

The partial-sums engines force world-independent growth. The non-dogmatism and Occam traders
grow only in the `φ`-worlds their hypotheses supply, so for those the engine is
`Trader.Exploits`' definition itself: bounded below everywhere, unbounded along a witness
family. -/

/-- Definitional exploitation: plausible assessments bounded below by `−C` and reaching above
every bound. -/
lemma exploits_of_bddBelow_of_unbounded (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (C : ℝ) (h1 : ∀ x ∈ Tr.plausibleAssessments P DP, -C ≤ x)
    (h2 : ∀ B : ℝ, ∃ x ∈ Tr.plausibleAssessments P DP, B < x) :
    Tr.Exploits P DP := by
  refine ⟨⟨-C, fun x hx => h1 x hx⟩, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨x, hx, hBx⟩ := h2 B
  exact absurd (hB hx) (not_le.mpr hBx)

/-! ## Sum bridges -/

/-- A `Finset.range` sum written as the sum of the corresponding mapped `List.range`.
Used wherever a payout bundle is built as a list but reasoned about as a `Finset` sum. -/
lemma list_range_map_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | (n + 1) => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ,
        list_range_map_sum f n]
      simp

end LogicalInduction
