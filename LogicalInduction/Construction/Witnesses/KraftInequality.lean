import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field

/-!
# Kraft's inequality (finite, binary) — the mathematical core of `M7-PREFIX-MACHINE`

Mathlib-only. A prefix-free finite set of binary codewords has total Kraft weight
`∑ 2^{-|w|} ≤ 1`. Mathlib has no Kraft inequality (checked 2026-07-20); this is the one
sub-obligation of the `M7-PREFIX-MACHINE` boundary that is mathematics rather than
repository plumbing (`notes/m7-prefix-machine-scope.md`, step 1).

Proof: the counting argument. Let `L` be the maximum codeword length. A codeword `w` of
length `ℓ` is the common prefix of exactly `2^(L-ℓ)` binary strings of length `L`;
prefix-freeness makes these blocked sets pairwise disjoint inside the `2^L` strings of
length `L`, so `∑ 2^(L-ℓᵢ) ≤ 2^L`, i.e. `∑ 2^(-ℓᵢ) ≤ 1`.

Provenance: proof body produced by Aristotle (run `2d017ff6-0c3b-49a7-8a6e-fe32202cc75a`,
job `65eaafaa-2ba0-4501-8002-8e9e2043f4d8`, 2026-07-25) against the statement validated
in-repo; re-elaborated and kernel-checked in this repository (the kernel is the gate,
never Aristotle's word). Kind `P` proved; hypotheses provenance `(b)` Mathlib only.
Axioms: `propext`, `Classical.choice`, `Quot.sound` (see `#print axioms` below and the
`AxiomAudit` entry).
-/

namespace LogicalInduction

open scoped BigOperators

/-- **Kraft's inequality (finite, binary).** A prefix-free finite set of binary
codewords has total Kraft weight at most one. Prefix-free is phrased as an antichain
under the list-prefix order `<+:`: if one codeword is a prefix of another, they are
equal. Paper node: `thm:ob` (the Kraft budget behind the Occam risk allocation). -/
theorem kraft_inequality {S : Finset (List Bool)}
    (hpf : ∀ a ∈ S, ∀ b ∈ S, a <+: b → a = b) :
    ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  classical
  -- Every list of length `n` is `List.ofFn` of some function `Fin n → Bool`.
  have key : ∀ (n : ℕ) (u : List Bool), u.length = n →
      ∃ f : Fin n → Bool, List.ofFn f = u := by
    intro n u h; subst h; exact ⟨fun i => u.get i, by simp⟩
  -- `L` is the maximal codeword length.
  set L : ℕ := S.sup List.length with hL
  have hlen : ∀ w ∈ S, w.length ≤ L := fun w hw => Finset.le_sup (f := List.length) hw
  -- `ext w` is the finset of all length-`L` extensions of the codeword `w`.
  set ext : List Bool → Finset (List Bool) :=
    fun w => (Finset.univ : Finset (Fin (L - w.length) → Bool)).image
      (fun f => w ++ List.ofFn f) with hext
  -- `ext w` has exactly `2 ^ (L - |w|)` elements.
  have hcard : ∀ w ∈ S, (ext w).card = 2 ^ (L - w.length) := by
    intro w hw
    rw [hext, Finset.card_image_of_injective]
    · simp
    · intro f g hfg
      simp only at hfg
      exact List.ofFn_inj.mp (List.append_cancel_left hfg)
  -- Each element of `ext w` has `w` as a prefix.
  have hpref_of_mem : ∀ w u, u ∈ ext w → w <+: u := by
    intro w u hu
    rw [hext] at hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨f, rfl⟩ := hu
    exact List.prefix_append _ _
  -- Each element of `ext w` has length `L`.
  have hlenL_of_mem : ∀ w, w.length ≤ L → ∀ u, u ∈ ext w → u.length = L := by
    intro w hwL u hu
    rw [hext] at hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu
    obtain ⟨f, rfl⟩ := hu
    simp only [List.length_append, List.length_ofFn]
    omega
  -- `allL` is the finset of all length-`L` binary strings; it has `2 ^ L` elements.
  set allL : Finset (List Bool) :=
    (Finset.univ : Finset (Fin L → Bool)).image (fun f => List.ofFn f) with hallL
  have hallL_card : allL.card = 2 ^ L := by
    rw [hallL, Finset.card_image_of_injective]
    · simp
    · intro f g hfg
      exact List.ofFn_inj.mp hfg
  have hmem_allL : ∀ u : List Bool, u.length = L → u ∈ allL := by
    intro u hu
    rw [hallL]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact key L u hu
  -- Prefix-freeness makes the extension sets pairwise disjoint.
  have hdisj : (S : Set (List Bool)).PairwiseDisjoint ext := by
    intro a ha b hb hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u hua hub
    have h1 : a <+: u := hpref_of_mem a u hua
    have h2 : b <+: u := hpref_of_mem b u hub
    rcases le_total a.length b.length with hle | hle
    · exact hab (hpf a ha b hb (List.prefix_of_prefix_length_le h1 h2 hle))
    · exact hab ((hpf b hb a ha (List.prefix_of_prefix_length_le h2 h1 hle)).symm)
  -- All extensions live inside the `2 ^ L` length-`L` strings.
  have hsub : S.biUnion ext ⊆ allL := by
    intro u hu
    simp only [Finset.mem_biUnion] at hu
    obtain ⟨w, hw, hwu⟩ := hu
    exact hmem_allL u (hlenL_of_mem w (hlen w hw) u hwu)
  -- Hence `∑ 2 ^ (L - |w|) ≤ 2 ^ L` as naturals.
  have hsum_nat : ∑ w ∈ S, 2 ^ (L - w.length) ≤ 2 ^ L := by
    calc ∑ w ∈ S, 2 ^ (L - w.length)
        = ∑ w ∈ S, (ext w).card := by
          apply Finset.sum_congr rfl; intro w hw; rw [hcard w hw]
      _ = (S.biUnion ext).card := (Finset.card_biUnion hdisj).symm
      _ ≤ allL.card := Finset.card_le_card hsub
      _ = 2 ^ L := hallL_card
  -- Cast to `ℝ` and divide by `2 ^ L` to conclude `∑ (1/2) ^ |w| ≤ 1`.
  have hcast : (∑ w ∈ S, ((2:ℝ) ^ (L - w.length))) ≤ (2:ℝ) ^ L := by
    have h2 : ((∑ w ∈ S, 2 ^ (L - w.length) : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
      exact_mod_cast hsum_nat
    push_cast at h2
    exact h2
  have hterm : ∀ w ∈ S, (1/2:ℝ)^w.length = (2:ℝ)^(L - w.length) / 2^L := by
    intro w hw
    have hk := hlen w hw
    have hsplit : (2:ℝ)^(L-w.length) * 2^(w.length) = 2^L := by
      rw [← pow_add]; congr 1; omega
    have h2L : (2:ℝ)^L ≠ 0 := by positivity
    rw [div_pow, one_pow, eq_div_iff h2L]
    field_simp
    linarith [hsplit]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  rw [div_le_one (by positivity)]
  exact hcast

#print axioms kraft_inequality

end LogicalInduction
