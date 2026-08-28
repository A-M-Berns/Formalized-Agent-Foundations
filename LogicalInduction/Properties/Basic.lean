/-
# Shared substrate for the property proofs

The pieces every property family reuses: the continuous buy-signal `max(0, feat − ε/2)`,
the Boolean payout lemmas for p.c. worlds, and the exploitation engines
(`exploits_of_nonneg_partialSums` for world-neutral traders, `exploits_of_ge_partialSums`
for world-dependent ones bounded below by a world-independent quantity, and
`exploits_of_bddBelow_of_unbounded` for traders whose growth itself is world-dependent).
-/
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Computable
import LogicalInduction.Framework.RpnEmission
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LiminfLimsup

namespace LogicalInduction

open Filter Topology

/-! ### The continuous buy-signal `max(0, feat − ε/2)`

Every responsive coherence/relationship trader gates its portfolio by a continuous buy-signal on
some deterministic *feature* `feat` (a price gap): it trades only when `feat` exceeds `ε/2`, and
proportionally to the excess. Factoring the signal here gives its denotation, rank, efficient
computability, and the two facts the exploitation arguments need (nonnegativity of `signal·feat`
when `feat ≥ 0` at trade time, and the `≥ ε²/2` lower bound on frequently-large days) once. -/

/-- Continuous buy-signal `max(0, feat − ε/2)`. -/
noncomputable def buySignal (feat : EF) (ε : ℚ) : EF :=
  .max (.const 0) (.add feat (.const (-ε/2)))

@[simp] lemma buySignal_denote (feat : EF) (ε : ℚ) (P : History) :
    (buySignal feat ε).denote P = max 0 (feat.denote P + (-(ε:ℝ)/2)) := by
  simp only [buySignal, EF.denote_max, EF.denote_add, EF.denote_const, Pi.add_apply]
  push_cast; ring_nf

@[simp] lemma buySignal_rank (feat : EF) (ε : ℚ) : (buySignal feat ε).rank = feat.rank := by
  simp [buySignal]

lemma buySignal_polyEF {t : ℕ → EF} (ht : PolyEF t) (ε : ℚ) :
    PolyEF (fun n => buySignal (t n) ε) :=
  (PolyEF.const 0).max (ht.add (PolyEF.const (-ε/2)))

/-- `0 ≤ buySignal feat ε`. -/
lemma buySignal_nonneg (feat : EF) (ε : ℚ) (P : History) :
    0 ≤ (buySignal feat ε).denote P := by rw [buySignal_denote]; exact le_max_left _ _

/-- When the signal fires (`feat > ε/2 ≥ 0`), its value equals `feat − ε/2`. -/
lemma buySignal_eq_of_pos (feat : EF) (ε : ℚ) (P : History)
    (h : (0:ℝ) ≤ feat.denote P + (-(ε:ℝ)/2)) :
    (buySignal feat ε).denote P = feat.denote P + (-(ε:ℝ)/2) := by
  rw [buySignal_denote, max_eq_right h]


/-! ### Boolean payout lemmas

A p.c. world evaluates compound sentences by Boolean algebra (Foundation's `val`), so its
`{0,1}` payouts compose the way a coherent probability must. These `Holds`-connective lemmas are
the shared substrate the coherence and logical-relationship traders' payout cancellations rest
on (additivity uses `payout_or_of_excl`; `thm:lex` uses `payout_eq_of_iff` / `payout_le_of_imp`,
which live in their family files). -/

/-- `∼χ`-worlds falsify `χ` (Foundation: `∼χ = χ 🡒 ⊥`). -/
lemma PCWorld.holds_neg (v : PCWorld) (χ : Sentence) : v.Holds (∼χ) ↔ ¬ v.Holds χ := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]


lemma PCWorld.holds_or (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋎ ψ) ↔ v.Holds φ ∨ v.Holds ψ := Iff.rfl


lemma PCWorld.holds_and (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋏ ψ) ↔ v.Holds φ ∧ v.Holds ψ := Iff.rfl


/-! ## Exploitation engines

The two lemmas every family's exploiting trader routes through. `exploits_of_nonneg_partialSums`
is for **world-neutral** traders (day-`i` value equals a fixed nonneg sequence `w i` in every
plausible world); `exploits_of_ge_partialSums` (below) weakens `=` to `≥` for **world-dependent**
traders whose value is only bounded below by a world-independent quantity. In both, `w` being
frequently `≥ ε` forces unbounded upside off bounded (`≥ 0`) downside. -/

/-- Reusable exploitation: a trader whose day-`i` value in every plausible world equals a fixed
nonnegative sequence `w i`, with `w n ≥ ε` frequently, exploits. -/
lemma exploits_of_nonneg_partialSums (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (w : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hnonneg : ∀ i, 0 ≤ w i)
    (hval : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      Tr.netWorth P v n = ∑ i ∈ Finset.range (n+1), w i)
    (hfreq : ∃ᶠ n in atTop, ε ≤ w n)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tr.Exploits P DP := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro x ⟨m, v, hv, rfl⟩
    rw [hval m v hv]; exact Finset.sum_nonneg (fun i _ => hnonneg i)
  · rintro ⟨B, hB⟩
    obtain ⟨g, hg_mono, hg⟩ := extraction_of_frequently_atTop hfreq
    obtain ⟨M, hM⟩ := exists_nat_gt (B / ε)
    obtain ⟨v, hv⟩ := hcons (g M)
    have hsub : (Finset.range (M+1)).image g ⊆ Finset.range (g M + 1) := by
      intro i hi; simp only [Finset.mem_image, Finset.mem_range] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact Finset.mem_range.mpr (by have := hg_mono.monotone (Nat.lt_succ_iff.mp hk); omega)
    have hge : (M+1 : ℝ) * ε ≤ Tr.netWorth P v (g M) := by
      rw [hval (g M) v hv]
      calc (M+1:ℝ)*ε = ∑ _k ∈ Finset.range (M+1), ε := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ k ∈ Finset.range (M+1), w (g k) := Finset.sum_le_sum (fun k _ => hg k)
        _ = ∑ i ∈ (Finset.range (M+1)).image g, w i :=
            (Finset.sum_image (hg_mono.injective.injOn)).symm
        _ ≤ ∑ i ∈ Finset.range (g M + 1), w i :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnonneg i)
    have hmem : Tr.netWorth P v (g M) ∈ Tr.plausibleAssessments P DP := ⟨g M, v, hv, rfl⟩
    have hBm : B < (M+1:ℝ)*ε := by rw [div_lt_iff₀ hε] at hM; nlinarith
    exact absurd (le_trans hge (hB hmem)) (by linarith)


/-! ### The `≥` variant — for world-dependent traders. -/

/-- Generalized exploitation: if each plausible-world net worth is **at least** the partial sum
of a nonnegative sequence `w` that is `≥ ε` frequently, the trader exploits. (Covers
world-dependent traders whose value is only bounded below by a world-independent quantity.) -/
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

/-! ### The definitional engine — for traders whose growth is world-*dependent*.

The partial-sums engines above force world-independent growth. The non-dogmatism trader
grows only in `φ`-worlds (its unboundedness witnesses come from the plausible `φ`-worlds
the hypothesis supplies), so the engine is `Exploits`' definition itself: bounded below
everywhere, unbounded along some witness family. -/

/-- Definitional exploitation: plausible assessments bounded below by `−C` and reaching
above every bound. -/
lemma exploits_of_bddBelow_of_unbounded (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (C : ℝ) (h1 : ∀ x ∈ Tr.plausibleAssessments P DP, -C ≤ x)
    (h2 : ∀ B : ℝ, ∃ x ∈ Tr.plausibleAssessments P DP, B < x) :
    Tr.Exploits P DP := by
  refine ⟨⟨-C, fun x hx => h1 x hx⟩, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨x, hx, hBx⟩ := h2 B
  exact absurd (hB hx) (not_le.mpr hBx)

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
