/-
# Spike: *Condensation: A Theory of Concepts* (Sam Eisenstat, July 2025) — feasibility probe.

The paper is written entirely in the vocabulary of Shannon entropy: `H(X)`, `H(X | Y)`,
`I(X; Y | Z)`, and the interaction information `I(X; Y; Z)`.  **Mathlib has none of it.**
`Mathlib/InformationTheory/` is `Coding`, `Hamming`, and `KullbackLeibler`; the only
`entropy` in the library is *topological* entropy in `Dynamics/`.  So the question this
spike has to answer is not "how hard are the theorems" but "how big is the substrate that
does not exist yet".

This file builds the minimum needed to state and prove **Proposition 2.5** — the bridge
`H(X | Y) = 0  ↔  X is almost everywhere a function of Y` — because that bridge is what
converts every entropy inequality in §4 into the paper's "is a function of" conclusions
(Lemma 4.5, Corollary 4.6, Theorem 4.9, Theorem 4.15).  If that is expensive, the paper
is expensive.

Result: it is *not* expensive, and the load is carried by one elementary lemma about
`Real.negMulLog` (`negMulLog_sum_le` below) which Mathlib does not have but which needs
no convexity machinery.  See `Condensation/SPIKE-REPORT.md` for what that implies for the
size of the missing library as a whole.
-/
import Mathlib

namespace CondSpike

open Finset Real

/-! ## A finite discrete probability space

The paper assumes "countable and discrete with finite entropy" throughout.  A bespoke
real-valued finite pmf (the `FiniteFactoredSets/Probability.lean` pattern) is far more
workable here than `PMF`, which is valued in `ℝ≥0∞` and fights entropy arithmetic. -/

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A finitely supported probability distribution, real-valued. -/
structure FinPMF (Ω : Type*) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  total : ∑ ω, p ω = 1

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `P(X = a)`. -/
noncomputable def pr (P : FinPMF Ω) (X : Ω → α) (a : α) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => X ω = a), P.p ω

theorem pr_nonneg (P : FinPMF Ω) (X : Ω → α) (a : α) : 0 ≤ pr P X a :=
  Finset.sum_nonneg fun ω _ => P.nonneg ω

/-- **Definition 2.3**, entropy.  (Natural-log units; the paper never fixes a base and
nothing in it depends on the choice.) -/
noncomputable def H (P : FinPMF Ω) (X : Ω → α) : ℝ :=
  ∑ a : α, negMulLog (pr P X a)

/-! ## The one missing analytic lemma

Everything the determinism bridge needs reduces to this, and — usefully — it needs no
concavity, no Jensen, no Gibbs.  Mathlib supplies `negMulLog` and its basic algebra;
this superadditivity statement it does not have. -/

/-- `negMulLog (∑ tᵢ) ≤ ∑ negMulLog tᵢ` for nonnegative `t`.  Superadditivity of
`negMulLog` on the nonnegative orthant. -/
theorem negMulLog_sum_le {ι : Type*} (s : Finset ι) (t : ι → ℝ) (ht : ∀ i ∈ s, 0 ≤ t i) :
    negMulLog (∑ i ∈ s, t i) ≤ ∑ i ∈ s, negMulLog (t i) := by
  have key : ∀ i ∈ s, -(t i) * Real.log (∑ j ∈ s, t j) ≤ negMulLog (t i) := by
    intro i hi
    rcases eq_or_lt_of_le (ht i hi) with h0 | hpos
    · simp [negMulLog, ← h0]
    · have hle : t i ≤ ∑ j ∈ s, t j := Finset.single_le_sum ht hi
      have hlog : Real.log (t i) ≤ Real.log (∑ j ∈ s, t j) := Real.log_le_log hpos hle
      simp only [negMulLog]
      nlinarith [hpos.le]
  have hsplit : ∑ i ∈ s, -(t i) * Real.log (∑ j ∈ s, t j) = negMulLog (∑ i ∈ s, t i) := by
    rw [negMulLog, ← Finset.sum_mul]
    congr 1
    simp
  rw [← hsplit]
  exact Finset.sum_le_sum key

/-- The equality case: `negMulLog` is *strictly* superadditive unless at most one summand
is nonzero.  This is the half that gives Proposition 2.5 its forward direction. -/
theorem negMulLog_sum_eq_iff {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) :
    negMulLog (∑ i ∈ s, t i) = ∑ i ∈ s, negMulLog (t i) ↔
      ∀ i ∈ s, t i = 0 ∨ t i = ∑ j ∈ s, t j := by
  have key : ∀ i ∈ s, -(t i) * Real.log (∑ j ∈ s, t j) ≤ negMulLog (t i) := by
    intro i hi
    rcases eq_or_lt_of_le (ht i hi) with h0 | hpos
    · simp [negMulLog, ← h0]
    · have hle : t i ≤ ∑ j ∈ s, t j := Finset.single_le_sum ht hi
      have hlog : Real.log (t i) ≤ Real.log (∑ j ∈ s, t j) := Real.log_le_log hpos hle
      simp only [negMulLog]
      nlinarith [hpos.le]
  have hsplit : ∑ i ∈ s, -(t i) * Real.log (∑ j ∈ s, t j) = negMulLog (∑ i ∈ s, t i) := by
    rw [negMulLog, ← Finset.sum_mul]
    congr 1
    simp
  constructor
  · intro heq i hi
    have hall : ∀ j ∈ s, -(t j) * Real.log (∑ k ∈ s, t k) = negMulLog (t j) :=
      (Finset.sum_eq_sum_iff_of_le key).mp (by rw [hsplit, heq])
    have hi' := hall i hi
    rcases eq_or_lt_of_le (ht i hi) with h0 | hpos
    · exact Or.inl h0.symm
    · right
      have hne : -(t i) ≠ 0 := by simpa using ne_of_gt hpos
      have hlog : Real.log (t i) = Real.log (∑ j ∈ s, t j) := by
        have h2 : -(t i) * Real.log (∑ j ∈ s, t j) = -(t i) * Real.log (t i) := by
          simpa [negMulLog] using hi'
        exact (mul_left_cancel₀ hne h2).symm
      have hSpos : 0 < ∑ j ∈ s, t j := lt_of_lt_of_le hpos (Finset.single_le_sum ht hi)
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hSpos) hlog
  · intro hdich
    refine le_antisymm (negMulLog_sum_le s t ht) ?_
    rw [← hsplit]
    refine Finset.sum_le_sum fun i hi => ?_
    rcases hdich i hi with h0 | hfull
    · simp [negMulLog, h0]
    · rw [hfull]; simp [negMulLog]

/-! ## Proposition 2.5, the determinism bridge

Stated as `H(X, Y) = H(Y)` rather than `H(X | Y) = 0`; with `H(X | Y) := H(X,Y) - H(Y)`
these are the same statement, and this form avoids committing to a `condEntropy`
definition inside a spike. -/

/-- `P(Y = b)` is the sum of `P(X = a, Y = b)` over `a`. -/
theorem pr_snd_eq_sum (P : FinPMF Ω) (X : Ω → α) (Y : Ω → β) (b : β) :
    pr P Y b = ∑ a : α, pr P (fun ω => (X ω, Y ω)) (a, b) := by
  classical
  simp only [pr]
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset α))
      (fun a => univ.filter (fun ω => (X ω, Y ω) = (a, b))) := by
    intro a _ a' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ,
      true_and, Prod.mk.injEq]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (h1.symm.trans h2)
  rw [← Finset.sum_biUnion hdisj]
  congr 1
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    Prod.mk.injEq]
  exact ⟨fun h => ⟨X ω, rfl, h⟩, fun ⟨_, _, h2⟩ => h2⟩

/-- **Conditioning cannot increase entropy**, in the form `H(X, Y) ≥ H(Y)`. -/
theorem H_pair_ge (P : FinPMF Ω) (X : Ω → α) (Y : Ω → β) :
    H P Y ≤ H P (fun ω => (X ω, Y ω)) := by
  classical
  have hjoint : H P (fun ω => (X ω, Y ω))
      = ∑ b : β, ∑ a : α, negMulLog (pr P (fun ω => (X ω, Y ω)) (a, b)) := by
    simp only [H]
    rw [Fintype.sum_prod_type_right]
  rw [hjoint, H]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [pr_snd_eq_sum P X Y b]
  exact negMulLog_sum_le _ _ fun a _ => pr_nonneg P _ (a, b)

/-- **Proposition 2.5.**  `H(X | Y) = 0` iff `X` is almost everywhere a function of `Y`.

The "almost everywhere" is spelled as "on every jointly-positive-probability pair": if
`(a,b)` and `(a',b)` both have positive probability then `a = a'`. -/
theorem H_pair_eq_iff (P : FinPMF Ω) (X : Ω → α) (Y : Ω → β) :
    H P (fun ω => (X ω, Y ω)) = H P Y ↔
      ∀ a a' : α, ∀ b : β,
        pr P (fun ω => (X ω, Y ω)) (a, b) ≠ 0 →
        pr P (fun ω => (X ω, Y ω)) (a', b) ≠ 0 → a = a' := by
  classical
  set q := fun (a : α) (b : β) => pr P (fun ω => (X ω, Y ω)) (a, b) with hq
  have hjoint : H P (fun ω => (X ω, Y ω)) = ∑ b : β, ∑ a : α, negMulLog (q a b) := by
    simp only [H, hq]
    rw [Fintype.sum_prod_type_right]
  have hmarg : ∀ b, pr P Y b = ∑ a : α, q a b := fun b => pr_snd_eq_sum P X Y b
  have hterm : ∀ b : β, negMulLog (pr P Y b) ≤ ∑ a : α, negMulLog (q a b) := by
    intro b
    rw [hmarg b]
    exact negMulLog_sum_le _ _ fun a _ => pr_nonneg P _ (a, b)
  constructor
  · intro heq a a' b ha ha'
    -- equality of the sums forces equality of each `b`-term
    have hbterm : ∀ b ∈ (univ : Finset β), negMulLog (pr P Y b) = ∑ a : α, negMulLog (q a b) :=
      (Finset.sum_eq_sum_iff_of_le fun b _ => hterm b).mp (by rw [← hjoint, ← H, heq])
    have := (negMulLog_sum_eq_iff (univ : Finset α) (fun a => q a b)
      (fun a _ => pr_nonneg P _ (a, b))).mp (by rw [← hmarg b, hbterm b (Finset.mem_univ b)])
    rcases this a (Finset.mem_univ a) with h | h
    · exact absurd h ha
    · rcases this a' (Finset.mem_univ a') with h' | h'
      · exact absurd h' ha'
      · -- both equal the full sum; if `a ≠ a'` the sum would exceed itself
        by_contra hne
        have hpos : 0 < q a b := lt_of_le_of_ne (pr_nonneg P _ (a, b)) (Ne.symm ha)
        have hsub : q a b + q a' b ≤ ∑ c : α, q c b := by
          have := Finset.sum_le_sum_of_subset_of_nonneg
            (s := ({a, a'} : Finset α)) (t := (univ : Finset α)) (f := fun c => q c b)
            (Finset.subset_univ _) (fun c _ _ => pr_nonneg P _ (c, b))
          rwa [Finset.sum_pair hne] at this
        rw [← h] at hsub
        have hpos' : 0 < q a' b := lt_of_le_of_ne (pr_nonneg P _ (a', b)) (Ne.symm ha')
        linarith
  · intro hfun
    refine le_antisymm ?_ (H_pair_ge P X Y)
    rw [hjoint, H]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [hmarg b]
    refine le_of_eq ((negMulLog_sum_eq_iff (univ : Finset α) (fun a => q a b)
      (fun a _ => pr_nonneg P _ (a, b))).mpr ?_).symm
    intro a _
    by_cases ha : q a b = 0
    · exact Or.inl ha
    · right
      -- `a` is the unique value with positive mass at `b`, so the sum collapses to it
      refine (Finset.sum_eq_single (s := (univ : Finset α)) (f := fun c => q c b)
        a ?_ ?_).symm
      · intro c _ hca
        by_contra hc
        exact hca (hfun c a b hc ha)
      · intro h; exact absurd (Finset.mem_univ a) h

/-! ## §5's combinatorial layer is free

Definition 5.5's polar, and the fact that it lands in the upward-closed sets — which is
what Theorem 5.8's intersection tree ranges over.  Pure `Set`/`Finset` combinatorics;
no analysis, no probability. -/

/-- **Definition 5.5** (polar).  `I` here is the index type; `P⁺ I` is rendered as the
nonempty subsets. -/
def polar {I : Type*} (F : Set (Set I)) : Set (Set I) :=
  {B | B.Nonempty ∧ ∀ A ∈ F, (A ∩ B).Nonempty}

/-- The polar is upward-closed, so Theorem 5.8's `G = F°` really does live in the lattice
its intersection tree is built over. -/
theorem polar_upward_closed {I : Type*} (F : Set (Set I)) {B C : Set I}
    (hB : B ∈ polar F) (hBC : B ⊆ C) : C ∈ polar F := by
  refine ⟨hB.1.mono hBC, fun A hA => ?_⟩
  obtain ⟨x, hxA, hxB⟩ := hB.2 A hA
  exact ⟨x, hxA, hBC hxB⟩

/-- Polarity is antitone, the other half of the Galois-connection behaviour §5.3 leans on
when it enlarges `F` to make `G` approximate `{C | C ⊇ A}` more closely. -/
theorem polar_antitone {I : Type*} {F G : Set (Set I)} (h : F ⊆ G) :
    polar G ⊆ polar F :=
  fun _ hB => ⟨hB.1, fun A hA => hB.2 A (h hA)⟩

end CondSpike

/-! ## Axiom audit -/

section Audit
#print axioms CondSpike.negMulLog_sum_le
#print axioms CondSpike.negMulLog_sum_eq_iff
#print axioms CondSpike.H_pair_ge
#print axioms CondSpike.H_pair_eq_iff
#print axioms CondSpike.polar_upward_closed
end Audit
