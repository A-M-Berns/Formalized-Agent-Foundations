/-
Copyright (c) 2026 Formalized Agent Foundations contributors.
Released under Apache 2.0 license.

This module is **FAF-authored**, mathematics included; see the header of
`ShannonInformation/FiniteEntropy/Summable.lean`.
-/
module

public import PFR.ForMathlib.Entropy.Basic
public import ShannonInformation.FiniteEntropy.Defs
public import ShannonInformation.FiniteEntropy.ChainRule
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import PFR.ForMathlib.ConditionalIndependence

/-!
# Subadditivity, mutual information, and the independence equality case

This module restates PFR's entropy inequalities over `FiniteEntropyOf` in place of
`FiniteRange`.  Nothing here is a new *definition*: `H`, `I` and `CondIndepFun` are the
vendored ones, and every statement below is the vendored statement with its finiteness
hypothesis weakened.  See `Condensation/notes/finite-range-generalization-plan.md` §7,
Phase 3.

## The one inequality that does all the work

Phase 1 proved the termwise pair bound `negMulLog_le_add_of_le` in
`ShannonInformation/FiniteEntropy/Summable.lean` and used it, *as a bound*, to close finite
entropy under pairing.  Summed over `S × T` and **evaluated** rather than bounded, the same
inequality is subadditivity: its left side is the joint entropy series and its right side sums
to `H[X] + H[Y] + (1 · 1 − 1)`.  Its pointwise gap is `prodGap`, and the whole module is that
gap read three ways:

* the gap is nonnegative, so `H[⟨X, Y⟩] ≤ H[X] + H[Y]`;
* the gap sums to `I[X : Y]`, so `0 ≤ I[X : Y]`;
* the gap vanishes at a cell exactly when the joint mass there is the product of the marginal
  masses (`negMulLog_eq_add_iff`, from the equality case of `Real.log_lt_sub_one_of_pos`), and
  a nonnegative summable family sums to `0` only if every term is `0` — so equality holds
  exactly for independent variables.  That last reading is the equality case "C4", and it
  needs no Jensen argument and no exhaustion over finite subsets.

## Layers

The file goes abstract → law → random variable, mirroring
`Summable.lean` → `Defs.lean`:

* **abstract** (`tsum_negMulLog_prod_le`, `tsum_negMulLog_prod_eq_add_iff`) — statements about
  a nonnegative family `r : S × T → ℝ` of total mass `1` and its two marginals.  No measure
  theory.
* **law** (`measureEntropy_prod_le_add`, `measureEntropy_prod_eq_add_iff`) — the same, for a
  probability measure on `S × T` and its two pushforwards, the second concluding
  `ρ = (ρ.map Prod.fst).prod (ρ.map Prod.snd)`.
* **random variable** (`entropy_pair_le_add`, `mutualInfo_nonneg`, `mutualInfo_eq_zero`,
  `entropy_pair_eq_add`) — the PFR-facing forms, and their conditional companions
  (`condMutualInfo_nonneg`, `condMutualInfo_eq_zero`, `condEntropy_le_entropy`,
  `condEntropy_pair_le_add`, `entropy_submodular`, `entropy_triple_add_entropy_le`).

## Conditioning

`finiteEntropyOf_cond` is the closure lemma the conditional statements rest on: conditioning
on an event keeps a variable inside the class (at a null fibre the conditioned measure is `0`,
which `finiteEntropyMeasure_zero` covers).  Since `condMutualInfo` is *defined* as the integral
over `Z`'s law of the conditioned mutual information, `condMutualInfo_nonneg` is then
`mutualInfo_nonneg` applied fibrewise, with **no chain rule anywhere** — and likewise
`condMutualInfo_eq_zero`, whose only extra input is integrability of
`z ↦ I[X : Y ; μ[|Z ← z]]`.

The remaining conditional statements — `condEntropy_le_entropy`, `condEntropy_pair_le_add`,
`entropy_submodular`, `entropy_triple_add_entropy_le` — *do* need the chain rule
`H[X | Y] = H[⟨X, Y⟩] - H[Y]` at `FiniteEntropyOf`.  That is
`ShannonInformation.chain_rule''` of `ShannonInformation/FiniteEntropy/ChainRule.lean`,
which this module imports; the private `ChainRuleLocal` duplicate that stood in for it
while the two phases were in flight was deleted in Phase 4a.  Given the chain rule,
submodularity is three rewrites and a `linarith` off conditional subadditivity plus
`ProbabilityTheory.entropy_assoc`, with no kernel layer.

## Two conditioning lemmas that look like duplicates and are not

`ShannonInformation.measureReal_map_cond_singleton` (here) and
`ShannonInformation.map_cond_measureReal_singleton` (`ChainRule.lean`) have the *same* left
side, `((μ[|Z ⁻¹' {z}]).map X).real {x}`, and different right sides: the preimage form
`μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) / μ.real (Z ⁻¹' {z})` here, needing no hypothesis on the
conditioning variable at all, versus the joint-law form
`(μ.map ⟨Z, X⟩).real {(z, x)} / (μ.map Z).real {z}` there, needing `Measurable Z` and
`MeasurableSingletonClass` on its value type.  Neither subsumes the other at the level of
hypotheses and both are used; do not "consolidate" them.

## Namespace note

`ShannonInformation.entropy_pair_le_add`, `.mutualInfo_nonneg`, `.mutualInfo_eq_zero`,
`.entropy_pair_eq_add`, `.condMutualInfo_nonneg`, `.condMutualInfo_eq_zero`,
`.condEntropy_le_entropy`, `.entropy_submodular`, `.entropy_triple_add_entropy_le`
deliberately shadow the same-named
`ProbabilityTheory` declarations, which are the `FiniteRange` versions.  A client that has
`open ProbabilityTheory ShannonInformation` must disambiguate — and note that ambiguous
overloads are resolved by *elaboration success*, not by the enclosing namespace, so a bare
`condMutualInfo_eq` inside `namespace ShannonInformation` can still silently pick PFR's
`FiniteRange` version.  Write the fully qualified name when both exist.  See
`ShannonInformation/API.lean`'s "which version to cite" table.

## Measure hypothesis

Every user-facing statement below is stated over `[IsZeroOrProbabilityMeasure μ]`, matching
PFR wherever PFR carries a measure hypothesis at all.  (`ProbabilityTheory.mutualInfo_nonneg`,
`.entropy_pair_le_add` and `.condMutualInfo_nonneg` carry *none* — they route through
`measureMutualInfo_nonneg`, which normalises internally.  Reaching that generality here would
mean restating the whole abstract layer for an unnormalised family; it is not done, and the
`IsZeroOrProbabilityMeasure` form is what every consumer in this repository needs.)  The
internal `MeasureLayer` section stays at `[IsProbabilityMeasure ρ]`, since its statements are
about a law of total mass `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace ShannonInformation

/-! ### The strict form of the termwise pair bound -/

private lemma negMulLog_lt_add_of_le {r a b : ℝ} (hr : 0 < r) (hra : r ≤ a) (hrb : r ≤ b)
    (hne : r ≠ a * b) :
    negMulLog r < -(r * Real.log a) + -(r * Real.log b) + (a * b - r) := by
  have ha : 0 < a := lt_of_lt_of_le hr hra
  have hb : 0 < b := lt_of_lt_of_le hr hrb
  have ht : (0 : ℝ) < a * b / r := by positivity
  have htne : a * b / r ≠ 1 := by
    intro h
    have : a * b = r := by field_simp at h; linarith
    exact hne this.symm
  have h1 : Real.log (a * b / r) < a * b / r - 1 := Real.log_lt_sub_one_of_pos ht htne
  have h2 : Real.log (a * b / r) = Real.log a + Real.log b - Real.log r := by
    rw [Real.log_div (by positivity) (ne_of_gt hr), Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]
  rw [h2] at h1
  have h3 := mul_lt_mul_of_pos_left h1 hr
  have h4 : r * (a * b / r - 1) = a * b - r := by field_simp
  rw [h4] at h3
  simp only [negMulLog]
  nlinarith

private lemma negMulLog_eq_add_iff {r a b : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) (hrb : r ≤ b) :
    negMulLog r = -(r * Real.log a) + -(r * Real.log b) + (a * b - r) ↔ r = a * b := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hr with h0 | hpos
    · rw [← h0] at h ⊢
      simp only [negMulLog, neg_zero, zero_mul, sub_zero, zero_add] at h ⊢
      linarith
    · by_contra hne
      exact absurd h (ne_of_lt (negMulLog_lt_add_of_le hpos hra hrb hne))
  · intro h
    rcases eq_or_lt_of_le hr with h0 | hpos
    · rw [← h0] at h ⊢
      simp only [negMulLog, neg_zero, zero_mul, sub_zero, zero_add]
      linarith
    · have ha : 0 < a := lt_of_lt_of_le hpos hra
      have hb : 0 < b := lt_of_lt_of_le hpos hrb
      have hlog : Real.log r = Real.log a + Real.log b := by
        rw [h, Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]
      simp only [negMulLog]
      rw [hlog, ← h]
      ring

/-! ### The abstract pair layer

Everything below is a statement about families of nonnegative reals; the measure-side
instantiation comes after.  `r` is the joint family on `S × T`, `a` and `b` its two
marginals. -/

section Abstract

variable {S T : Type*}

/-- The pointwise gap in `negMulLog_le_add_of_le`. -/
private noncomputable def prodGap (r : S × T → ℝ) (a : S → ℝ) (b : T → ℝ) (q : S × T) : ℝ :=
  (-(r q * Real.log (a q.1)) + -(r q * Real.log (b q.2)) + (a q.1 * b q.2 - r q))
    - negMulLog (r q)

private lemma hasSum_swap {α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : S × T → α}
    {v : α} (h : HasSum (fun p : T × S ↦ f (p.2, p.1)) v) : HasSum f v :=
  (Equiv.prodComm T S).hasSum_iff.mp h

private lemma tsum_swap {α : Type*} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]
    (f : S × T → α) : (∑' p : T × S, f (p.2, p.1)) = ∑' q : S × T, f q :=
  (Equiv.prodComm T S).tsum_eq f

private lemma prod_le_marg_fst {r : S × T → ℝ} {a : S → ℝ} (h0 : ∀ q, 0 ≤ r q) (hr : Summable r)
    (ha : ∀ x, a x = ∑' y, r (x, y)) (q : S × T) : r q ≤ a q.1 := by
  rw [ha q.1]
  exact (hr.prod_factor q.1).le_tsum q.2 (fun j _ ↦ h0 (q.1, j))

private lemma hasSum_prod_neg_mul_log_fst {r : S × T → ℝ} {a : S → ℝ} (h0 : ∀ q, 0 ≤ r q)
    (hr : Summable r) (ha : ∀ x, a x = ∑' y, r (x, y)) (ha1 : ∀ x, a x ≤ 1)
    (henta : Summable fun x ↦ negMulLog (a x)) :
    HasSum (fun q : S × T ↦ -(r q * Real.log (a q.1))) (∑' x, negMulLog (a x)) := by
  have ha0 : ∀ x, 0 ≤ a x := fun x ↦ (ha x) ▸ tsum_nonneg fun y ↦ h0 (x, y)
  have hfib : ∀ x, Summable fun y ↦ -(r (x, y) * Real.log (a x)) :=
    fun x ↦ ((hr.prod_factor x).mul_right (Real.log (a x))).neg
  have hval : ∀ x, (∑' y, -(r (x, y) * Real.log (a x))) = negMulLog (a x) := by
    intro x
    rw [tsum_neg, (hr.prod_factor x).tsum_mul_right, ← ha x, negMulLog]
    ring
  have hs : Summable fun q : S × T ↦ -(r q * Real.log (a q.1)) := by
    refine (summable_prod_of_nonneg fun q ↦ ?_).mpr ⟨fun x ↦ hfib x, ?_⟩
    · exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (h0 q)
        (Real.log_nonpos (ha0 _) (ha1 _)))
    · simpa only [hval] using henta
  have hsum : ∑' q : S × T, -(r q * Real.log (a q.1)) = ∑' x, negMulLog (a x) := by
    rw [hs.tsum_prod' fun x ↦ hfib x]
    exact tsum_congr hval
  exact hsum ▸ hs.hasSum

private lemma hasSum_marg_fst {r : S × T → ℝ} {a : S → ℝ} (h0 : ∀ q, 0 ≤ r q) (hr : Summable r)
    (hr1 : ∑' q, r q = 1) (ha : ∀ x, a x = ∑' y, r (x, y)) : HasSum a 1 := by
  have hs : Summable a := by
    have h := (summable_prod_of_nonneg h0).mp hr
    exact (funext ha : a = _) ▸ h.2
  have hval : ∑' x, a x = 1 := by
    rw [tsum_congr ha, ← hr.tsum_prod' fun x ↦ hr.prod_factor x, hr1]
  exact hval ▸ hs.hasSum

/-- The swapped joint family, used to derive the second-marginal statements from the
first-marginal ones. -/
private lemma swap_hyps {r : S × T → ℝ} (h0 : ∀ q, 0 ≤ r q) (hr : Summable r)
    (hr1 : ∑' q, r q = 1) :
    (∀ p : T × S, 0 ≤ r (p.2, p.1)) ∧ (Summable fun p : T × S ↦ r (p.2, p.1)) ∧
      (∑' p : T × S, r (p.2, p.1)) = 1 :=
  ⟨fun p ↦ h0 _, hr.prod_symm, by rw [tsum_swap]; exact hr1⟩

private lemma hasSum_prod_neg_mul_log_snd {r : S × T → ℝ} {b : T → ℝ} (h0 : ∀ q, 0 ≤ r q)
    (hr : Summable r) (hb : ∀ y, b y = ∑' x, r (x, y)) (hb1 : ∀ y, b y ≤ 1)
    (hentb : Summable fun y ↦ negMulLog (b y)) :
    HasSum (fun q : S × T ↦ -(r q * Real.log (b q.2))) (∑' y, negMulLog (b y)) := by
  have hsymm : Summable fun p : T × S ↦ r (p.2, p.1) := hr.prod_symm
  exact hasSum_swap
    (hasSum_prod_neg_mul_log_fst (r := fun p : T × S ↦ r (p.2, p.1)) (a := b)
      (fun p ↦ h0 _) hsymm hb hb1 hentb)

private lemma hasSum_marg_snd {r : S × T → ℝ} {b : T → ℝ} (h0 : ∀ q, 0 ≤ r q) (hr : Summable r)
    (hr1 : ∑' q, r q = 1) (hb : ∀ y, b y = ∑' x, r (x, y)) : HasSum b 1 := by
  obtain ⟨h0', hr', hr1'⟩ := swap_hyps h0 hr hr1
  exact hasSum_marg_fst (r := fun p : T × S ↦ r (p.2, p.1)) h0' hr' hr1' hb


private lemma prodGap_nonneg {r : S × T → ℝ} {a : S → ℝ} {b : T → ℝ} (h0 : ∀ q, 0 ≤ r q)
    (hr : Summable r) (ha : ∀ x, a x = ∑' y, r (x, y)) (hb : ∀ y, b y = ∑' x, r (x, y))
    (q : S × T) : 0 ≤ prodGap r a b q := by
  have hsymm : Summable fun p : T × S ↦ r (p.2, p.1) := hr.prod_symm
  have h2 : r q ≤ b q.2 :=
    prod_le_marg_fst (r := fun p : T × S ↦ r (p.2, p.1)) (fun p ↦ h0 _) hsymm hb (q.2, q.1)
  exact sub_nonneg.2 (negMulLog_le_add_of_le (h0 q) (prod_le_marg_fst h0 hr ha q) h2)

private lemma hasSum_prodGap {r : S × T → ℝ} {a : S → ℝ} {b : T → ℝ} (h0 : ∀ q, 0 ≤ r q)
    (hr : Summable r) (hr1 : ∑' q, r q = 1) (hent : Summable fun q ↦ negMulLog (r q))
    (ha : ∀ x, a x = ∑' y, r (x, y)) (ha1 : ∀ x, a x ≤ 1)
    (henta : Summable fun x ↦ negMulLog (a x))
    (hb : ∀ y, b y = ∑' x, r (x, y)) (hb1 : ∀ y, b y ≤ 1)
    (hentb : Summable fun y ↦ negMulLog (b y)) :
    HasSum (prodGap r a b)
      ((∑' x, negMulLog (a x)) + (∑' y, negMulLog (b y)) - ∑' q, negMulLog (r q)) := by
  have ha0 : ∀ x, 0 ≤ a x := fun x ↦ (ha x) ▸ tsum_nonneg fun y ↦ h0 (x, y)
  have hb0 : ∀ y, 0 ≤ b y := fun y ↦ (hb y) ▸ tsum_nonneg fun x ↦ h0 (x, y)
  have hA := hasSum_prod_neg_mul_log_fst h0 hr ha ha1 henta
  have hB := hasSum_prod_neg_mul_log_snd h0 hr hb hb1 hentb
  have hMa := hasSum_marg_fst h0 hr hr1 ha
  have hMb := hasSum_marg_snd h0 hr hr1 hb
  have hAB : HasSum (fun q : S × T ↦ a q.1 * b q.2) (1 * 1) :=
    hMa.mul hMb (hMa.summable.mul_of_nonneg hMb.summable ha0 hb0)
  have hR : HasSum r 1 := hr1 ▸ hr.hasSum
  have h := ((hA.add hB).add (hAB.sub hR)).sub hent.hasSum
  have hval : (∑' x, negMulLog (a x)) + (∑' y, negMulLog (b y)) + ((1 : ℝ) * 1 - 1)
        - ∑' q, negMulLog (r q)
      = (∑' x, negMulLog (a x)) + (∑' y, negMulLog (b y)) - ∑' q, negMulLog (r q) := by ring
  rw [hval] at h
  exact h

/-- **Subadditivity, abstract form.**  The entropy of a joint family is at most the sum of
the entropies of its two marginals. -/
lemma tsum_negMulLog_prod_le {r : S × T → ℝ} {a : S → ℝ} {b : T → ℝ} (h0 : ∀ q, 0 ≤ r q)
    (hr : Summable r) (hr1 : ∑' q, r q = 1) (hent : Summable fun q ↦ negMulLog (r q))
    (ha : ∀ x, a x = ∑' y, r (x, y)) (ha1 : ∀ x, a x ≤ 1)
    (henta : Summable fun x ↦ negMulLog (a x))
    (hb : ∀ y, b y = ∑' x, r (x, y)) (hb1 : ∀ y, b y ≤ 1)
    (hentb : Summable fun y ↦ negMulLog (b y)) :
    (∑' q, negMulLog (r q)) ≤ (∑' x, negMulLog (a x)) + ∑' y, negMulLog (b y) := by
  have hgap := hasSum_prodGap h0 hr hr1 hent ha ha1 henta hb hb1 hentb
  have hnn : 0 ≤ ∑' q, prodGap r a b q := tsum_nonneg (prodGap_nonneg h0 hr ha hb)
  rw [hgap.tsum_eq] at hnn
  linarith

/-- **The equality case, abstract form.**  Subadditivity is an equality exactly when the
joint family is the product of its marginals. -/
lemma tsum_negMulLog_prod_eq_add_iff {r : S × T → ℝ} {a : S → ℝ} {b : T → ℝ}
    (h0 : ∀ q, 0 ≤ r q) (hr : Summable r) (hr1 : ∑' q, r q = 1)
    (hent : Summable fun q ↦ negMulLog (r q))
    (ha : ∀ x, a x = ∑' y, r (x, y)) (ha1 : ∀ x, a x ≤ 1)
    (henta : Summable fun x ↦ negMulLog (a x))
    (hb : ∀ y, b y = ∑' x, r (x, y)) (hb1 : ∀ y, b y ≤ 1)
    (hentb : Summable fun y ↦ negMulLog (b y)) :
    ((∑' q, negMulLog (r q)) = (∑' x, negMulLog (a x)) + ∑' y, negMulLog (b y))
      ↔ ∀ q : S × T, r q = a q.1 * b q.2 := by
  have hsymm : Summable fun p : T × S ↦ r (p.2, p.1) := hr.prod_symm
  have hle2 : ∀ q : S × T, r q ≤ b q.2 := fun q ↦
    prod_le_marg_fst (r := fun p : T × S ↦ r (p.2, p.1)) (fun p ↦ h0 _) hsymm hb (q.2, q.1)
  have hgap := hasSum_prodGap h0 hr hr1 hent ha ha1 henta hb hb1 hentb
  have hnn := prodGap_nonneg h0 hr ha hb
  have hiff : ∀ q : S × T, prodGap r a b q = 0 ↔ r q = a q.1 * b q.2 := by
    intro q
    rw [prodGap, sub_eq_zero, eq_comm]
    exact negMulLog_eq_add_iff (h0 q) (prod_le_marg_fst h0 hr ha q) (hle2 q)
  constructor
  · intro h q
    have hzero : ∑' q, prodGap r a b q = 0 := by rw [hgap.tsum_eq]; linarith
    have hle : prodGap r a b q ≤ ∑' q', prodGap r a b q' :=
      hgap.summable.le_tsum q fun j _ ↦ hnn j
    exact (hiff q).mp (le_antisymm (by linarith) (hnn q))
  · intro h
    have hzero : ∀ q, prodGap r a b q = 0 := fun q ↦ (hiff q).mpr (h q)
    have ht := hgap.tsum_eq
    rw [tsum_congr hzero, tsum_zero] at ht
    linarith

end Abstract


/-! ### The measure layer -/

section MeasureLayer

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

private lemma tsum_measureReal_singleton_eq_one {I : Type*} [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I] (ρ : Measure I) [IsProbabilityMeasure ρ] :
    ∑' i, ρ.real {i} = 1 := by
  have h := integral_countable (μ := ρ) (f := fun _ : I ↦ (1 : ℝ)) (integrable_const 1)
  simpa using h.symm

variable [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  (ρ : Measure (S × T)) [IsProbabilityMeasure ρ]

variable [FiniteEntropyMeasure (ρ.map Prod.fst)] [FiniteEntropyMeasure (ρ.map Prod.snd)]

/-- **Subadditivity at the level of laws.** -/
lemma measureEntropy_prod_le_add :
    Hm[ρ] ≤ Hm[ρ.map Prod.fst] + Hm[ρ.map Prod.snd] := by
  haveI : IsProbabilityMeasure (ρ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (ρ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : FiniteEntropyMeasure ρ := finiteEntropyMeasure_prod ρ
  rw [measureEntropy_of_isProbabilityMeasure, measureEntropy_of_isProbabilityMeasure,
    measureEntropy_of_isProbabilityMeasure]
  exact tsum_negMulLog_prod_le (fun _ ↦ measureReal_nonneg)
    (summable_measureReal_singleton ρ) (tsum_measureReal_singleton_eq_one ρ)
    (FiniteEntropyMeasure.summable_real ρ)
    (fun x ↦ measureReal_map_fst_singleton ρ x)
    (fun x ↦ measureReal_singleton_le_one _ x) (FiniteEntropyMeasure.summable_real _)
    (fun y ↦ measureReal_map_snd_singleton ρ y)
    (fun y ↦ measureReal_singleton_le_one _ y) (FiniteEntropyMeasure.summable_real _)

/-- **The equality case at the level of laws**: subadditivity is an equality exactly when the
law is the product of its two marginals. -/
lemma measureEntropy_prod_eq_add_iff :
    Hm[ρ] = Hm[ρ.map Prod.fst] + Hm[ρ.map Prod.snd]
      ↔ ρ = (ρ.map Prod.fst).prod (ρ.map Prod.snd) := by
  haveI : IsProbabilityMeasure (ρ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (ρ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : FiniteEntropyMeasure ρ := finiteEntropyMeasure_prod ρ
  rw [measureEntropy_of_isProbabilityMeasure, measureEntropy_of_isProbabilityMeasure,
    measureEntropy_of_isProbabilityMeasure]
  rw [tsum_negMulLog_prod_eq_add_iff (fun _ ↦ measureReal_nonneg)
    (summable_measureReal_singleton ρ) (tsum_measureReal_singleton_eq_one ρ)
    (FiniteEntropyMeasure.summable_real ρ)
    (fun x ↦ measureReal_map_fst_singleton ρ x)
    (fun x ↦ measureReal_singleton_le_one _ x) (FiniteEntropyMeasure.summable_real _)
    (fun y ↦ measureReal_map_snd_singleton ρ y)
    (fun y ↦ measureReal_singleton_le_one _ y) (FiniteEntropyMeasure.summable_real _)]
  have hprod : ∀ q : S × T, ((ρ.map Prod.fst).prod (ρ.map Prod.snd)).real {q}
      = (ρ.map Prod.fst).real {q.1} * (ρ.map Prod.snd).real {q.2} := by
    intro q
    rw [show ({q} : Set (S × T)) = {q.1} ×ˢ {q.2} from Set.singleton_prod_singleton.symm,
      measureReal_prod_prod]
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  exact forall_congr' fun q ↦ by rw [hprod q]

end MeasureLayer


/-! ### Conditioning preserves finite entropy -/

section Conditioning

variable {Ω S U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]

/-- The zero measure has finite entropy. -/
lemma finiteEntropyMeasure_zero : FiniteEntropyMeasure (0 : Measure S) := by
  constructor
  simp

/-- The domination bound.  If `0 ≤ r ≤ a ≤ 1` then `negMulLog r ≤ negMulLog a + a`. -/
private lemma negMulLog_le_add_of_le_one {r a : ℝ} (hr : 0 ≤ r) (hra : r ≤ a) (ha : a ≤ 1) :
    negMulLog r ≤ negMulLog a + a := by
  have ha0 : 0 ≤ a := hr.trans hra
  have hlog : Real.log a ≤ 0 := Real.log_nonpos ha0 ha
  have h := negMulLog_le_add_of_le hr hra (hra.trans ha)
  simp only [Real.log_one, mul_zero, neg_zero, mul_one, add_zero] at h
  simp only [negMulLog] at h ⊢
  nlinarith [mul_nonneg (sub_nonneg.2 hra) (neg_nonneg.2 hlog)]

omit [MeasurableSpace U] in
/-- The law of `X` under `μ` conditioned on `Z = z`, at a point. -/
lemma measureReal_map_cond_singleton [MeasurableSingletonClass S]
    {X : Ω → S} {Z : Ω → U} {μ : Measure Ω} (hX : Measurable X) (z : U) (x : S) :
    ((μ[|Z ⁻¹' {z}]).map X).real {x}
      = μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) / μ.real (Z ⁻¹' {z}) := by
  rw [map_measureReal_apply hX (measurableSet_singleton x)]
  simp only [Measure.real]
  rw [cond_apply' (hX (measurableSet_singleton x)), ENNReal.toReal_mul, ENNReal.toReal_inv,
    Set.inter_comm, div_eq_inv_mul]

omit [MeasurableSpace U] in
/-- Conditioning on an event preserves finite entropy. -/
lemma finiteEntropyOf_cond [MeasurableSingletonClass S]
    {X : Ω → S} {Z : Ω → U} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) [FiniteEntropyOf X μ] (z : U) :
    FiniteEntropyOf X (μ[|Z ⁻¹' {z}]) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · rw [FiniteEntropyOf, cond_eq_zero_of_meas_eq_zero (by simp), Measure.map_zero]
    exact finiteEntropyMeasure_zero
  by_cases hz : μ (Z ⁻¹' {z}) = 0
  · rw [FiniteEntropyOf, cond_eq_zero_of_meas_eq_zero hz, Measure.map_zero]
    exact finiteEntropyMeasure_zero
  · haveI : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure hz
    haveI : IsProbabilityMeasure ((μ[|Z ⁻¹' {z}]).map X) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
    refine FiniteEntropyMeasure.of_summable_real ?_
    have hP : 0 < μ.real (Z ⁻¹' {z}) := ENNReal.toReal_pos hz (measure_ne_top _ _)
    have hq : ∀ x, (μ.map X).real {x} = μ.real (X ⁻¹' {x}) := fun x ↦
      map_measureReal_apply hX (measurableSet_singleton x)
    have hsumq : Summable fun x ↦ μ.real (X ⁻¹' {x}) := by
      simpa only [hq] using summable_measureReal_singleton (μ.map X)
    have hentq : Summable fun x ↦ negMulLog (μ.real (X ⁻¹' {x})) := by
      simpa only [hq] using FiniteEntropyMeasure.summable_real (μ.map X)
    have hq1 : ∀ x, μ.real (X ⁻¹' {x}) ≤ 1 := fun x ↦ by
      simpa only [hq] using measureReal_singleton_le_one (μ.map X) x
    have hpq : ∀ x, μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) ≤ μ.real (X ⁻¹' {x}) := fun x ↦
      measureReal_mono Set.inter_subset_left
    have hsump : Summable fun x ↦ μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) :=
      Summable.of_nonneg_of_le (fun _ ↦ measureReal_nonneg) hpq hsumq
    have hentp : Summable fun x ↦ negMulLog (μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z})) :=
      Summable.of_nonneg_of_le
        (fun x ↦ negMulLog_nonneg measureReal_nonneg ((hpq x).trans (hq1 x)))
        (fun x ↦ negMulLog_le_add_of_le_one measureReal_nonneg (hpq x) (hq1 x))
        (hentq.add hsumq)
    have hid : ∀ x, (μ.real (Z ⁻¹' {z}))⁻¹ * negMulLog (μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}))
          + μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) * (Real.log (μ.real (Z ⁻¹' {z}))
            * (μ.real (Z ⁻¹' {z}))⁻¹)
        = negMulLog (μ.real (X ⁻¹' {x} ∩ Z ⁻¹' {z}) / μ.real (Z ⁻¹' {z})) := fun x ↦
      (negMulLog_div _ _ measureReal_nonneg hP).symm
    have := ((hentp.mul_left (μ.real (Z ⁻¹' {z}))⁻¹).add
      (hsump.mul_right (Real.log (μ.real (Z ⁻¹' {z})) * (μ.real (Z ⁻¹' {z}))⁻¹))).congr hid
    simpa only [measureReal_map_cond_singleton hX z] using this

end Conditioning

/-! ### The random-variable layer -/

section RandomVariable

variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]

omit [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  [IsZeroOrProbabilityMeasure μ] in
private lemma map_pair_fst (hX : Measurable X) (hY : Measurable Y) :
    (μ.map (⟨X, Y⟩ : Ω → S × T)).map Prod.fst = μ.map X := by
  rw [Measure.map_map measurable_fst (hX.prodMk hY)]; rfl

omit [Countable S] [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
  [IsZeroOrProbabilityMeasure μ] in
private lemma map_pair_snd (hX : Measurable X) (hY : Measurable Y) :
    (μ.map (⟨X, Y⟩ : Ω → S × T)).map Prod.snd = μ.map Y := by
  rw [Measure.map_map measurable_snd (hX.prodMk hY)]; rfl

/-- **Subadditivity of entropy** for finite-entropy variables: `H[X, Y] ≤ H[X] + H[Y]`.

This is `ProbabilityTheory.entropy_pair_le_add` with `[FiniteRange X] [FiniteRange Y]` replaced
by `[FiniteEntropyOf X μ] [FiniteEntropyOf Y μ]`. -/
lemma entropy_pair_le_add (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[⟨X, Y⟩ ; μ] ≤ H[X ; μ] + H[Y ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [entropy_zero_measure]
  haveI : IsProbabilityMeasure (μ.map (⟨X, Y⟩ : Ω → S × T)) :=
    Measure.isProbabilityMeasure_map (hX.prodMk hY).aemeasurable
  haveI : FiniteEntropyMeasure ((μ.map (⟨X, Y⟩ : Ω → S × T)).map Prod.fst) :=
    by rw [map_pair_fst hX hY]; infer_instance
  haveI : FiniteEntropyMeasure ((μ.map (⟨X, Y⟩ : Ω → S × T)).map Prod.snd) :=
    by rw [map_pair_snd hX hY]; infer_instance
  have h := measureEntropy_prod_le_add (μ.map (⟨X, Y⟩ : Ω → S × T))
  rwa [map_pair_fst hX hY, map_pair_snd hX hY] at h

/-- **Mutual information is nonnegative** for finite-entropy variables. -/
lemma mutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    0 ≤ I[X : Y ; μ] :=
  sub_nonneg.2 (entropy_pair_le_add hX hY)

/-- **The equality case (C4).**  `I[X : Y] = 0` exactly when `X` and `Y` are independent.

This is `ProbabilityTheory.mutualInfo_eq_zero` with `FiniteRange` replaced by
`FiniteEntropyOf`. -/
lemma mutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    I[X : Y ; μ] = 0 ↔ IndepFun X Y μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp only [mutualInfo_def, entropy_zero_measure, add_zero, sub_zero, true_iff]
    rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    simp
  haveI : IsProbabilityMeasure (μ.map (⟨X, Y⟩ : Ω → S × T)) :=
    Measure.isProbabilityMeasure_map (hX.prodMk hY).aemeasurable
  haveI : FiniteEntropyMeasure ((μ.map (⟨X, Y⟩ : Ω → S × T)).map Prod.fst) :=
    by rw [map_pair_fst hX hY]; infer_instance
  haveI : FiniteEntropyMeasure ((μ.map (⟨X, Y⟩ : Ω → S × T)).map Prod.snd) :=
    by rw [map_pair_snd hX hY]; infer_instance
  have h := measureEntropy_prod_eq_add_iff (μ.map (⟨X, Y⟩ : Ω → S × T))
  rw [map_pair_fst hX hY, map_pair_snd hX hY] at h
  rw [mutualInfo_def, sub_eq_zero, eq_comm,
    indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
  exact h

/-- **`H[X, Y] = H[X] + H[Y]` iff `X` and `Y` are independent**, for finite-entropy
variables. -/
lemma entropy_pair_eq_add (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y ; μ] ↔ IndepFun X Y μ := by
  rw [← mutualInfo_eq_zero hX hY, mutualInfo_def, sub_eq_zero, eq_comm]

end RandomVariable

/-! ### Conditional mutual information -/

section Conditional

variable {Ω S T U : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace U] [Countable S] [MeasurableSingletonClass S] [Countable T]
  [MeasurableSingletonClass T] {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
  [IsZeroOrProbabilityMeasure μ]

/-- **Conditional mutual information is nonnegative** for finite-entropy variables.

`condMutualInfo` is by definition the integral over `Z`'s law of the mutual information of the
conditioned variables, so this is `mutualInfo_nonneg` applied fibrewise; the conditioned
variables stay inside the class by `finiteEntropyOf_cond`, and the null fibres contribute `0`. -/
lemma condMutualInfo_nonneg (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] :
    0 ≤ I[X : Y | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rw [condMutualInfo_eq_integral_mutualInfo]
  refine integral_nonneg fun z ↦ ?_
  by_cases hz : μ (Z ⁻¹' {z}) = 0
  · simp [cond_eq_zero_of_meas_eq_zero hz, mutualInfo_def]
  · haveI : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure hz
    haveI := finiteEntropyOf_cond (μ := μ) (Z := Z) hX z
    haveI := finiteEntropyOf_cond (μ := μ) (Z := Z) hY z
    exact mutualInfo_nonneg hX hY

/-- **`H[X | Y] ≤ H[X]`** for finite-entropy variables: conditioning does not increase
entropy. -/
lemma condEntropy_le_entropy (hX : Measurable X) (hY : Measurable Y)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] : H[X | Y ; μ] ≤ H[X ; μ] := by
  rw [chain_rule'' μ hX hY]
  have := entropy_pair_le_add (μ := μ) hX hY
  linarith

section CondU

variable [Countable U] [MeasurableSingletonClass U]

/-- **Conditional subadditivity**: `H[⟨X, Y⟩ | Z] ≤ H[X | Z] + H[Y | Z]`. -/
lemma condEntropy_pair_le_add (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    H[⟨X, Y⟩ | Z ; μ] ≤ H[X | Z ; μ] + H[Y | Z ; μ] := by
  have h1 := ShannonInformation.condMutualInfo_eq hX hY hZ μ
  have h2 : (0 : ℝ) ≤ I[X : Y | Z ; μ] := condMutualInfo_nonneg hX hY
  linarith

/-- **Submodularity**: `H[X | ⟨Y, Z⟩] ≤ H[X | Z]`.

This is `ProbabilityTheory.entropy_submodular` with `FiniteRange` replaced by
`FiniteEntropyOf`.  PFR proves it through the conditional-kernel layer; here it is conditional
subadditivity plus the chain rule and `ProbabilityTheory.entropy_assoc`. -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    H[X | ⟨Y, Z⟩ ; μ] ≤ H[X | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condEntropy_zero_measure]
  haveI := finiteEntropyOf_pair (μ := μ) hY hZ
  haveI := finiteEntropyOf_pair (μ := μ) hX hY
  have e1 : H[X | ⟨Y, Z⟩ ; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ] - H[⟨Y, Z⟩ ; μ] :=
    chain_rule'' μ hX (hY.prodMk hZ)
  have e2 : H[⟨X, Y⟩ | Z ; μ] = H[⟨⟨X, Y⟩, Z⟩ ; μ] - H[Z ; μ] :=
    chain_rule'' μ (hX.prodMk hY) hZ
  have e3 : H[Y | Z ; μ] = H[⟨Y, Z⟩ ; μ] - H[Z ; μ] := chain_rule'' μ hY hZ
  have e4 := entropy_assoc hX hY hZ μ
  have e5 := condEntropy_pair_le_add (μ := μ) hX hY hZ
  linarith

/-- **The submodularity inequality**: `H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]`.

This is `ProbabilityTheory.entropy_triple_add_entropy_le` with `FiniteRange` replaced by
`FiniteEntropyOf`. -/
lemma entropy_triple_add_entropy_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    H[⟨X, ⟨Y, Z⟩⟩ ; μ] + H[Z ; μ] ≤ H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [entropy_zero_measure]
  haveI := finiteEntropyOf_pair (μ := μ) hY hZ
  have e1 : H[X | ⟨Y, Z⟩ ; μ] = H[⟨X, ⟨Y, Z⟩⟩ ; μ] - H[⟨Y, Z⟩ ; μ] :=
    chain_rule'' μ hX (hY.prodMk hZ)
  have e2 : H[X | Z ; μ] = H[⟨X, Z⟩ ; μ] - H[Z ; μ] := chain_rule'' μ hX hZ
  have e4 := entropy_submodular (μ := μ) hX hY hZ
  linarith

/-- **The conditional equality case**: `I[X : Y | Z] = 0` exactly when `X` and `Y` are
conditionally independent given `Z`.

This is `ProbabilityTheory.condMutualInfo_eq_zero` with `FiniteRange` replaced by
`FiniteEntropyOf`; the fibrewise structure of PFR's proof carries over unchanged, with the
integrability of `z ↦ I[X : Y ; μ[|Z ← z]]` now a consequence of the class rather than of
finite support. -/
lemma condMutualInfo_eq_zero (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteEntropyOf X μ] [FiniteEntropyOf Y μ] [FiniteEntropyOf Z μ] :
    I[X : Y | Z ; μ] = 0 ↔ CondIndepFun X Y Z μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [condIndepFun_iff]
  haveI := finiteEntropyOf_pair (μ := μ) hX hY
  have hnn : ∀ z, 0 ≤ I[X : Y ; μ[|Z ⁻¹' {z}]] := by
    intro z
    by_cases hz : μ (Z ⁻¹' {z}) = 0
    · simp [cond_eq_zero_of_meas_eq_zero hz, mutualInfo_def]
    · haveI : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure hz
      haveI := finiteEntropyOf_cond (μ := μ) (Z := Z) hX z
      haveI := finiteEntropyOf_cond (μ := μ) (Z := Z) hY z
      exact mutualInfo_nonneg hX hY
  have hint : Integrable (fun z ↦ I[X : Y ; μ[|Z ⁻¹' {z}]]) (μ.map Z) := by
    have h1 := integrable_entropy_cond hX hZ μ
    have h2 := integrable_entropy_cond hY hZ μ
    have h3 := integrable_entropy_cond (hX.prodMk hY) hZ μ
    exact (h1.add h2).sub h3
  rw [condIndepFun_iff, condMutualInfo_eq_integral_mutualInfo,
    integral_eq_zero_iff_of_nonneg hnn hint]
  have hae : (fun z ↦ I[X : Y ; μ[|Z ⁻¹' {z}]]) =ᵐ[μ.map Z] 0 ↔
      ∀ᵐ z ∂(μ.map Z), I[X : Y ; μ[|Z ⁻¹' {z}]] = 0 := by rfl
  rw [hae]
  apply Filter.eventually_congr
  rw [ae_iff_of_countable]
  intro z hz
  have hz' : μ (Z ⁻¹' {z}) ≠ 0 := by rwa [Measure.map_apply hZ (measurableSet_singleton z)] at hz
  haveI : IsProbabilityMeasure (μ[|Z ⁻¹' {z}]) := cond_isProbabilityMeasure hz'
  haveI := finiteEntropyOf_cond (μ := μ) (Z := Z) hX z
  haveI := finiteEntropyOf_cond (μ := μ) (Z := Z) hY z
  exact mutualInfo_eq_zero hX hY

end CondU

end Conditional

end ShannonInformation
