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
import LogicalInduction.Criterion
import LogicalInduction.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace LogicalInduction

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

/-- `def:roi`. A trader has **ε return on investment** against `𝓥`, over a set of `worlds`,
if in every such world its net worth converges to a value at least `ε` times its total
magnitude — the value gained is an `ε` fraction of the amount invested, guaranteed in every
consistent world (not merely recouped on average). Stated with the project's limit
vocabulary (`dd:asymp`, `ConvergesTo`). -/
def HasROI (Tr : Trader) (V : History) (ε : ℝ) (worlds : Set PCWorld) : Prop :=
  ∀ v ∈ worlds, ∃ L : ℝ, ConvergesTo (Tr.netWorth V v) L ∧ ε * Tr.magnitude V ≤ L

end LogicalInduction
