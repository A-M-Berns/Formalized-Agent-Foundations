/-
# Part II — Shared engines (`LogicalInduction.Engine`)

The workhorses every property proof routes through. Build the ROI bound before any
property. Nodes hosted here (see roadmap §3, Part II):

* `def:roi` / `app:roi` → `ReturnOnInvestment`, `roi_bound` — bounds a trader's return;
  nearly every property proof routes through it.
* `def:tradermag` → `Trader.magnitude` — used by ROI and budgeting.
* `def:emulatabletraders` → `EmulatableTraders` — the concrete clocked enumeration shape
  (`dd:abstract`).
* `thm:affpolymax` / `app:affpolymax` → `affine_preemptive_learning` — the **affine
  master theorem**; one of the two "lift" hubs.
* `lem:conluvapprox`, `lem:mesh`, `lem:limexpapprox` → `LUV.*_approx` — the **expectation
  bridge** that lifts probability results to expectation results; the second "lift" hub.

Status (M2): `def:tradermag` (magnitude) and `def:roi` (ε-return-on-investment) are
defined here, with the magnitude bound on a trade's value proved. The **ROI lemma**
(ε-ROI + boundedness ⇒ exploitation) and `def:emulatabletraders` are the reusable hubs the
affine/expectation families need; they are M4 work and are not yet stated.
-/
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace LogicalInduction

open Filter Topology

/-! ## `def:tradermag` — Magnitude

The magnitude of a trade is the total number of shares it moves, `∑_φ |T[φ](𝓥)|` — the
constant (cash) term omitted. It is the "investment" against which return is measured. -/

namespace Strategy

/-- The magnitude of an `n`-strategy against a history `𝓥`: the total absolute share
volume `∑ᵢ |eᵢ(𝓥)|`. (For a strategy in which a sentence occurs once, this is exactly
`∑_φ |T[φ]|`; with repeats it is an upper bound, which is all the value bound needs.) -/
noncomputable def magnitude {n : ℕ} (T : Strategy n) (V : History) : ℝ :=
  (T.trades.map (fun p => |p.1.denote V|)).sum

theorem magnitude_nonneg {n : ℕ} (T : Strategy n) (V : History) : 0 ≤ T.magnitude V :=
  List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx; obtain ⟨p, _, rfl⟩ := hx; exact abs_nonneg _)

end Strategy

/-- Triangle-inequality bound for a `List.sum` of mapped terms: if `|f x| ≤ g x` pointwise,
then `|∑ f| ≤ ∑ g`. -/
private theorem abs_map_sum_le {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, |f x| ≤ g x) : |(l.map f).sum| ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := h a (List.mem_cons_self ..)
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      calc |f a + (t.map f).sum| ≤ |f a| + |(t.map f).sum| := abs_add_le _ _
        _ ≤ g a + (t.map g).sum := by linarith

/-- **Magnitude bound** (`def:tradermag`). In a market with prices in `[0,1]`, a strategy's
value in any `{0,1}`-world is bounded by its magnitude: a share is worth at most 1 and costs
at least 0, so `|value| ≤ Σ|shares| = magnitude`. The basic tool behind return-on-investment
estimates. -/
theorem Strategy.abs_value_le_magnitude {n : ℕ} (T : Strategy n) (V : History)
    (w : Sentence → ℝ) (hw : ∀ φ, w φ = 0 ∨ w φ = 1)
    (hV : ∀ φ, 0 ≤ V n φ ∧ V n φ ≤ 1) :
    |T.value V w| ≤ T.magnitude V := by
  simp only [Strategy.value, Strategy.magnitude]
  refine abs_map_sum_le T.trades _ _ (fun p _ => ?_)
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rcases hw p.2 with h | h <;> rcases hV p.2 with ⟨h0, h1⟩ <;> rw [h, abs_le] <;>
    constructor <;> linarith

/-- The total magnitude of a trader against `𝓥`: `∑ₙ |Tₙ(𝓥)|` (`def:tradermag`). As a
possibly-divergent series it is a `tsum`, meaningful for *bounded* traders (finite total
magnitude); the `def:roi` predicate below is what consumes it. -/
noncomputable def Trader.magnitude (Tr : Trader) (V : History) : ℝ :=
  ∑' n, (Tr.strat n).magnitude V

/-! ## `def:roi` — ε-Return on Investment -/

/-- `def:roi`. A trader has **ε return on investment** against `V` relative to `DP` when
its total share magnitude is finite and, uniformly over worlds still plausible at late
times, its net worth is eventually at least `(ε-η)` times that magnitude for every `η>0`.

The paper states the limit inequality over all worlds consistent with the completed theory
and derives this operational form by compactness plus enumeration of `DP`. Our propositional
substrate does not package the completed theory or a computability witness for `DP`, so the
uniform plausible-world form is carried explicitly. It is exactly the form the repeatable-ROI
maturity search consumes, and avoids silently assuming an unavailable uniformization lemma. -/
def HasROI (Tr : Trader) (V : History) (DP : DeductiveProcess) (ε : ℝ) : Prop :=
  Summable (fun n => (Tr.strat n).magnitude V) ∧
    ∀ η : ℝ, 0 < η → ∃ N, ∀ n, N ≤ n → ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) → (ε - η) * Tr.magnitude V ≤ Tr.netWorth V v n

/-! ### Finite-magnitude risk bound

The summability clause above is load-bearing. In Mathlib, `tsum` of a non-summable real
series is defined as `0`; omitting summability would therefore let an infinite-risk trader
claim zero magnitude. The following lemmas turn genuine finite magnitude into the uniform
lower bound required by `Exploits`. -/

theorem Trader.partial_magnitude_le (Tr : Trader) (V : History)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V ≤ Tr.magnitude V := by
  exact hmag.sum_le_tsum _ (fun i _ => Strategy.magnitude_nonneg (Tr.strat i) V)

/-- Magnitude is nonnegative (including Mathlib's zero value for a divergent nonnegative
series; finiteness is still required everywhere that magnitude represents actual risk). -/
theorem Trader.magnitude_nonneg (Tr : Trader) (V : History) : 0 ≤ Tr.magnitude V := by
  exact tsum_nonneg (fun n => Strategy.magnitude_nonneg (Tr.strat n) V)

/-- Partial magnitudes eventually contain any prescribed `(1-η)` fraction of the total
magnitude. -/
theorem Trader.eventually_partial_magnitude_ge (Tr : Trader) (V : History)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) {η : ℝ} (hη : 0 < η) :
    ∃ N, ∀ n, N ≤ n →
      (1 - η) * Tr.magnitude V ≤
        ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V := by
  by_cases hzero : Tr.magnitude V = 0
  · refine ⟨0, fun n _ => ?_⟩
    rw [hzero, mul_zero]
    exact Finset.sum_nonneg (fun i _ => Strategy.magnitude_nonneg (Tr.strat i) V)
  · have htot : 0 < Tr.magnitude V := lt_of_le_of_ne
      (Tr.magnitude_nonneg V) (Ne.symm hzero)
    have htend : Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (Tr.strat i).magnitude V)
        atTop (𝓝 (Tr.magnitude V)) := hmag.hasSum.tendsto_sum_nat
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (η * Tr.magnitude V)
      (mul_pos hη htot)
    refine ⟨N, fun n hn => ?_⟩
    have hclose := hN (n + 1) (by omega)
    rw [Real.dist_eq] at hclose
    have hlo : Tr.magnitude V - η * Tr.magnitude V <
        ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V := by
      rw [abs_lt] at hclose
      linarith [hclose.1]
    nlinarith

/-- Operational maturity used by the repeatable-ROI budgeter: almost all magnitude has
already been traded, and the current holdings are uniformly profitable in every plausible
world. -/
def Trader.Matured (Tr : Trader) (V : History) (DP : DeductiveProcess)
    (ε η : ℝ) (m : ℕ) : Prop :=
  (1 - η) * Tr.magnitude V ≤
      ∑ i ∈ Finset.range (m + 1), (Tr.strat i).magnitude V ∧
    ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      (ε - η) * Tr.magnitude V ≤ Tr.netWorth V v m

/-- Every positive-ROI trader matures at some finite stage, for any positive tolerance. -/
theorem HasROI.exists_matured {Tr : Trader} {V : History} {DP : DeductiveProcess}
    {ε η : ℝ} (hroi : HasROI Tr V DP ε) (hη : 0 < η) :
    ∃ m, Tr.Matured V DP ε η m := by
  obtain ⟨hmag, hprofit⟩ := hroi
  obtain ⟨Nmag, hNmag⟩ := Tr.eventually_partial_magnitude_ge V hmag hη
  obtain ⟨Nprofit, hNprofit⟩ := hprofit η hη
  refine ⟨max Nmag Nprofit, hNmag _ (le_max_left _ _), ?_⟩
  exact hNprofit _ (le_max_right _ _)

/-- At every finite day, a finite-magnitude trader's net worth in any Boolean world is
bounded in absolute value by its total magnitude. -/
theorem Trader.abs_netWorth_le_magnitude (Tr : Trader) (V : History) (v : PCWorld)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) (n : ℕ) :
    |Tr.netWorth V v n| ≤ Tr.magnitude V := by
  calc
    |Tr.netWorth V v n|
        ≤ ∑ i ∈ Finset.range (n + 1), |(Tr.strat i).value V v.payout| := by
          simpa [Trader.netWorth] using
            (Finset.abs_sum_le_sum_abs (s := Finset.range (n + 1))
              (f := fun i => (Tr.strat i).value V v.payout))
    _ ≤ ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V := by
          exact Finset.sum_le_sum (fun i _ => Strategy.abs_value_le_magnitude
            (Tr.strat i) V v.payout (fun φ => by
              by_cases hφ : v.Holds φ
              · exact Or.inr (by simp [PCWorld.payout, hφ])
              · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP i))
    _ ≤ Tr.magnitude V := Tr.partial_magnitude_le V hmag n

/-- Finite total magnitude supplies the bounded-downside half of exploitation uniformly
over all plausible worlds. -/
theorem Trader.bddBelow_plausible_of_finiteMagnitude (Tr : Trader) (V : History)
    (DP : DeductiveProcess) (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) :
    BddBelow (Tr.plausibleAssessments V DP) := by
  refine ⟨-Tr.magnitude V, ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  have h := Tr.abs_netWorth_le_magnitude V v hP hmag n
  exact (neg_le_of_abs_le h)

#print axioms Trader.abs_netWorth_le_magnitude

end LogicalInduction
