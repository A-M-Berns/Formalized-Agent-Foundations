import LogicalInduction.Framework.Compactness
import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Properties.Basic

/-!
# A refutation of the unrestricted finite-day perturbation theorem

`Properties/FinitePerturbations.lean` records that the appendix proof of `thm:ifp` has a
gap.  This file develops the *semantic* refutation: the unrestricted statement

    ∀ P P' DP N, IsMachineLogicalInductor P DP → ComputableMarket P' →
      (∀ n ≥ N, P n = P' n) → IsMachineLogicalInductor P' DP

is false, because a day-`0` perturbation may publish, as prices of otherwise inert advice
atoms, the very bits that separate the computable from the efficiently computable.

The engine is the repo's diagonal price sequence `χ`.  In every world consistent with the
completed theory, `χ n` holds exactly when `P n (χ n) < 1/2`, so a trader that knows the
single bit `[P n (χ n) < 1/2]` earns a *certain* `≥ 1/2` on day `n` once that day's
sentence has settled.  Computing the bit is computable but (for the constructed inductor)
not polynomial-time, which is why `P` itself survives.  Publishing the bits on day `0`
hands them to an efficient trader.

Everything below the assembly section is a complete, unconditional development of that
bookkeeping over an *abstract* history, diagonal family and trader.  The assembly section
records what remains.

This file is deliberately **not** annotated with a `Paper node:` line: it refutes a paper
statement rather than rendering one.
-/

namespace LogicalInduction
namespace FinitePerturbationCounterexample

open Classical

/-! ## Settlement

The diagonal dichotomy is a statement about worlds consistent with the *completed* theory.
Propositional compactness (`DeductiveProcess.exists_stage_entails`) turns it into a
statement about one finite stage, which is what a net-worth assessment can see.
-/

/-- The day-`m` diagonal dichotomy, read off the completed theory. -/
def Dichotomy (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (m : ℕ) : Prop :=
  ∀ v : PCWorld, v.ConsistentWithTheory DP → (v.Holds (χ m) ↔ V m (χ m) < 1 / 2)

/-- The same dichotomy already forced by the finite stage `k`. -/
def SettledAt (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (m k : ℕ) : Prop :=
  ∀ v : PCWorld, v.ConsistentWith (DP.D k) → (v.Holds (χ m) ↔ V m (χ m) < 1 / 2)

/-- Settlement is inherited by every later stage.
Kind `P`; hypotheses `(a)`. -/
lemma SettledAt.mono {V : History} {DP : DeductiveProcess} {χ : ℕ → Sentence} {m k k' : ℕ}
    (h : SettledAt V DP χ m k) (hk : k ≤ k') : SettledAt V DP χ m k' :=
  fun v hv => h v (fun φ hφ => hv φ (DP.mono_le hk hφ))

/-- **Compactness closes the settlement gap.**  A diagonal day settles at some finite
stage: the completed-theory dichotomy is decided by one `DP.D k`.
Kind `P`; hypotheses `(a)` from `Dichotomy`, `(b)` `DeductiveProcess.exists_stage_entails`
and `PCWorld.holds_neg`. -/
lemma exists_settled {V : History} {DP : DeductiveProcess} {χ : ℕ → Sentence} {m : ℕ}
    (h : Dichotomy V DP χ m) : ∃ k, SettledAt V DP χ m k := by
  by_cases hlt : V m (χ m) < 1 / 2
  · obtain ⟨k, hk⟩ := DP.exists_stage_entails (χ m) (fun v hv => (h v hv).2 hlt)
    exact ⟨k, fun v hv => iff_of_true (hk v hv) hlt⟩
  · obtain ⟨k, hk⟩ := DP.exists_stage_entails (∼(χ m))
      (fun v hv => (PCWorld.holds_neg v (χ m)).2 (fun hH => hlt ((h v hv).1 hH)))
    exact ⟨k, fun v hv => iff_of_false ((PCWorld.holds_neg v (χ m)).1 (hk v hv)) hlt⟩

/-- A chosen settlement stage for day `m`; `0` on days with no dichotomy. -/
noncomputable def settleStage (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (m : ℕ) : ℕ :=
  if h : ∃ k, SettledAt V DP χ m k then h.choose else 0

/-- Kind `P`; hypotheses `(a)`. -/
lemma settleStage_spec {V : History} {DP : DeductiveProcess} {χ : ℕ → Sentence} {m : ℕ}
    (h : Dichotomy V DP χ m) : SettledAt V DP χ m (settleStage V DP χ m) := by
  have hex : ∃ k, SettledAt V DP χ m k := exists_settled h
  rw [settleStage, dif_pos hex]
  exact hex.choose_spec

/-! ## The sparse schedule

Round `j` opens its position on day `sched j` and holds it until settlement.  The schedule
steps past the previous round's settlement stage, so at most one position is ever
unsettled — which is what bounds the downside by `1`.  Day `0` is never scheduled: it is
the perturbed day, where the dichotomy need not hold.
-/

/-- The trading days: `sched 0 = 1`, and each later day strictly exceeds both its
predecessor and that predecessor's settlement stage. -/
noncomputable def sched (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) :
    ℕ → ℕ
  | 0 => 1
  | j + 1 => max (sched V DP χ j) (settleStage V DP χ (sched V DP χ j)) + 1

variable {V : History} {DP : DeductiveProcess} {χ : ℕ → Sentence}

/-- Kind `P`. -/
lemma one_le_sched (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (j : ℕ) :
    1 ≤ sched V DP χ j := by
  cases j with
  | zero => exact Nat.le_refl 1
  | succ j => exact Nat.succ_le_succ (Nat.zero_le _)

/-- Kind `P`. -/
lemma sched_lt_succ (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (j : ℕ) :
    sched V DP χ j < sched V DP χ (j + 1) := by
  show sched V DP χ j < max (sched V DP χ j) (settleStage V DP χ (sched V DP χ j)) + 1
  exact Nat.lt_succ_of_le (le_max_left _ _)

/-- Kind `C`. -/
lemma sched_strictMono (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) :
    StrictMono (sched V DP χ) :=
  strictMono_nat_of_lt_succ (sched_lt_succ V DP χ)

/-- **Sparseness.**  Round `j` has settled before round `j + 1` opens.
Kind `P`. -/
lemma settleStage_sched_lt (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (j : ℕ) :
    settleStage V DP χ (sched V DP χ j) < sched V DP χ (j + 1) := by
  show settleStage V DP χ (sched V DP χ j) <
    max (sched V DP χ j) (settleStage V DP χ (sched V DP χ j)) + 1
  exact Nat.lt_succ_of_le (le_max_right _ _)

/-- The rounds open by day `n` form an initial segment.
Kind `P`; hypotheses `(a)`. -/
lemma exists_roundCount (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (n : ℕ) :
    ∃ c : ℕ, ∀ j, sched V DP χ j ≤ n ↔ j < c := by
  induction n with
  | zero =>
      refine ⟨0, fun j => ?_⟩
      have := one_le_sched V DP χ j
      exact iff_of_false (by omega) (by omega)
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      by_cases hcut : sched V DP χ c = n + 1
      · refine ⟨c + 1, fun j => ?_⟩
        constructor
        · intro hj
          by_contra hjc
          have hlt : c < j := by omega
          have := sched_strictMono V DP χ hlt
          omega
        · intro hj
          rcases Nat.lt_or_ge j c with h | h
          · have := (hc j).2 h; omega
          · have hjc : j = c := by omega
            subst hjc; omega
      · have hcgt : n + 1 < sched V DP χ c := by
          have hnle : ¬ sched V DP χ c ≤ n := fun h => absurd ((hc c).1 h) (by omega)
          omega
        refine ⟨c, fun j => ?_⟩
        constructor
        · intro hj
          by_contra hjc
          have hcj : c ≤ j := by omega
          have := (sched_strictMono V DP χ).monotone hcj
          omega
        · intro hj
          have := (hc j).2 hj
          omega

/-- The number of rounds open by day `n`. -/
noncomputable def roundCount (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (n : ℕ) : ℕ := (exists_roundCount V DP χ n).choose

/-- Kind `P`; hypotheses `(a)`. -/
lemma roundCount_spec (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (n j : ℕ) :
    sched V DP χ j ≤ n ↔ j < roundCount V DP χ n :=
  (exists_roundCount V DP χ n).choose_spec j

/-- By day `sched (J+1)` at least `J + 2` rounds have opened.
Kind `C`. -/
lemma le_roundCount_sched (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (J : ℕ) :
    J + 2 ≤ roundCount V DP χ (sched V DP χ (J + 1)) := by
  have := (roundCount_spec V DP χ (sched V DP χ (J + 1)) (J + 1)).1 (le_refl _)
  omega

/-! ## The per-round margin

Exact, not asymptotic: no convergence statement is used anywhere below.
-/

/-- The sign the advice bits publish on day `m`: buy below the diagonal threshold, short
at or above it. -/
noncomputable def signCoeff (V : History) (χ : ℕ → Sentence) (m : ℕ) : ℝ :=
  if V m (χ m) < 1 / 2 then 1 else -1

/-- The value of the day-`m` diagonal position in the world `v`. -/
noncomputable def roundValue (V : History) (χ : ℕ → Sentence) (v : PCWorld) (m : ℕ) : ℝ :=
  signCoeff V χ m * (v.payout (χ m) - V m (χ m))

/-- **The margin.**  Once day `m` has settled, the position is worth at least `1/2` in
*every* world consistent with the stage — certain profit, not an expectation.
Kind `P`; hypotheses `(a)`. -/
lemma half_le_roundValue {m k k' : ℕ} (h : SettledAt V DP χ m k) (hk : k ≤ k')
    (v : PCWorld) (hv : v.ConsistentWith (DP.D k')) :
    (1 : ℝ) / 2 ≤ roundValue V χ v m := by
  have hset := h.mono hk v hv
  by_cases hlt : V m (χ m) < 1 / 2
  · have hH : v.Holds (χ m) := hset.2 hlt
    have hpay : v.payout (χ m) = 1 := by simp [PCWorld.payout, hH]
    simp only [roundValue, signCoeff, if_pos hlt, hpay]
    linarith
  · have hH : ¬ v.Holds (χ m) := fun hH => hlt (hset.1 hH)
    have hpay : v.payout (χ m) = 0 := by simp [PCWorld.payout, hH]
    simp only [roundValue, signCoeff, if_neg hlt, hpay]
    push_neg at hlt
    linarith

/-- **The bounded downside.**  An unsettled position is worth at least `-1`.
Kind `P`; hypotheses `(a)` price range. -/
lemma neg_one_le_roundValue (hV : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1) (v : PCWorld) (m : ℕ) :
    (-1 : ℝ) ≤ roundValue V χ v m := by
  obtain ⟨hlo, hhi⟩ := hV m (χ m)
  have hpay : v.payout (χ m) = 1 ∨ v.payout (χ m) = 0 := by
    by_cases hH : v.Holds (χ m)
    · exact Or.inl (by simp [PCWorld.payout, hH])
    · exact Or.inr (by simp [PCWorld.payout, hH])
  simp only [roundValue, signCoeff]
  by_cases hlt : V m (χ m) < 1 / 2
  · rw [if_pos hlt]; rcases hpay with hp | hp <;> rw [hp] <;> linarith
  · rw [if_neg hlt]; push_neg at hlt
    rcases hpay with hp | hp <;> rw [hp] <;> linarith

end FinitePerturbationCounterexample
end LogicalInduction
