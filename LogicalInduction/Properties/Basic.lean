/-
# Part III — shared substrate for the property tail

World/payout boolean lemmas and the two exploitation engines (`exploits_of_nonneg_partialSums`
for world-neutral traders, `exploits_of_ge_partialSums` for world-dependent ones bounded below
by a world-independent quantity). Every family file below builds on these.
-/
import LogicalInduction.Criterion
import LogicalInduction.Asymptotics
import LogicalInduction.Computable
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.LiminfLimsup

namespace LogicalInduction

open Filter Topology


/-! ### Boolean payout lemmas

A p.c. world evaluates compound sentences by Boolean algebra (Foundation's `val`), so its
`{0,1}` payouts compose the way a coherent probability must. These `Holds`-connective lemmas are
the shared substrate the coherence and logical-relationship traders' payout cancellations rest
on (additivity uses `payout_or_of_excl`; `thm:lex` uses `payout_eq_of_iff` / `payout_le_of_imp`,
which live in their family files). -/

/-- `∼χ`-worlds falsify `χ` (Foundation: `∼χ = χ 🡒 ⊥`). -/
theorem PCWorld.holds_neg (v : PCWorld) (χ : Sentence) : v.Holds (∼χ) ↔ ¬ v.Holds χ := by
  simp [PCWorld.Holds, LO.Propositional.Formula.Boolean.val]


theorem PCWorld.holds_or (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋎ ψ) ↔ v.Holds φ ∨ v.Holds ψ := Iff.rfl


theorem PCWorld.holds_and (v : PCWorld) (φ ψ : Sentence) :
    v.Holds (φ ⋏ ψ) ↔ v.Holds φ ∧ v.Holds ψ := Iff.rfl


/-! ## Exploitation engines

The two lemmas every family's exploiting trader routes through. `exploits_of_nonneg_partialSums`
is for **world-neutral** traders (day-`i` value equals a fixed nonneg sequence `w i` in every
plausible world); `exploits_of_ge_partialSums` (below) weakens `=` to `≥` for **world-dependent**
traders whose value is only bounded below by a world-independent quantity. In both, `w` being
frequently `≥ ε` forces unbounded upside off bounded (`≥ 0`) downside. -/

/-- Reusable exploitation: a trader whose day-`i` value in every plausible world equals a fixed
nonnegative sequence `w i`, with `w n ≥ ε` frequently, exploits. -/
theorem exploits_of_nonneg_partialSums (Tr : Trader) (P : History) (DP : DeductiveProcess)
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
theorem exploits_of_ge_partialSums (Tr : Trader) (P : History) (DP : DeductiveProcess)
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

end LogicalInduction
