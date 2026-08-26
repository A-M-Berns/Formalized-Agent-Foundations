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
    push Not at hlt
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
  · rw [if_neg hlt]; push Not at hlt
    rcases hpay with hp | hp <;> rw [hp] <;> linarith

/-! ## Exploitation bookkeeping

The trader's net worth on day `n` is exactly the sum of its open rounds' values, of which
all but the last have settled.  So `netWorth ≥ (#settled)/2 − 1`: bounded below by `−3/2`
uniformly, and unbounded above along the schedule.  That is `def:exploitation`.

`hzero` and `hval` are the interface to the trader's *construction*: it trades nothing off
schedule, and on day `sched j` it holds exactly the advice-signed unit position in
`χ (sched j)`.
-/

/-- Off-schedule days contribute nothing, so net worth collapses to the open rounds.
Kind `P`; hypotheses `(a)`, `(b)` `Finset.sum_subset` / `Finset.sum_image`. -/
lemma netWorth_eq_sum (Tr : Trader) (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (v : PCWorld)
    (hzero : ∀ i, (∀ j, sched V DP χ j ≠ i) → (Tr.strat i).value V v.payout = 0)
    (hval : ∀ j, (Tr.strat (sched V DP χ j)).value V v.payout
      = roundValue V χ v (sched V DP χ j))
    (n : ℕ) :
    Tr.netWorth V v n
      = ∑ j ∈ Finset.range (roundCount V DP χ n), roundValue V χ v (sched V DP χ j) := by
  classical
  have hsub : (Finset.range (roundCount V DP χ n)).image (sched V DP χ)
      ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    have := (roundCount_spec V DP χ n j).2 hj
    omega
  have hvanish : ∀ i ∈ Finset.range (n + 1),
      i ∉ (Finset.range (roundCount V DP χ n)).image (sched V DP χ) →
        (Tr.strat i).value V v.payout = 0 := by
    intro i hin hi
    simp only [Finset.mem_range] at hin
    refine hzero i (fun j hj => hi ?_)
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨j, (roundCount_spec V DP χ n j).1 (by omega), hj⟩
  have hsum := Finset.sum_subset hsub hvanish
  simp only [Trader.netWorth]
  rw [← hsum, Finset.sum_image (fun a _ b _ h => (sched_strictMono V DP χ).injective h)]
  exact Finset.sum_congr rfl (fun j _ => hval j)

/-- **Net worth `≥ (#settled)/2 − 1`.**  At most the newest round is unsettled, by
sparseness, so all earlier rounds contribute `≥ 1/2` and the newest `≥ −1`.
Kind `P`; hypotheses `(a)`. -/
lemma netWorth_ge (Tr : Trader) (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (hdicho : ∀ j, Dichotomy V DP χ (sched V DP χ j))
    (hV : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (v : PCWorld) (n : ℕ) (hv : v.ConsistentWith (DP.D n))
    (hzero : ∀ i, (∀ j, sched V DP χ j ≠ i) → (Tr.strat i).value V v.payout = 0)
    (hval : ∀ j, (Tr.strat (sched V DP χ j)).value V v.payout
      = roundValue V χ v (sched V DP χ j)) :
    ((roundCount V DP χ n : ℝ) - 1) / 2 - 1 ≤ Tr.netWorth V v n := by
  rw [netWorth_eq_sum Tr V DP χ v hzero hval n]
  rcases Nat.eq_zero_or_pos (roundCount V DP χ n) with h0 | hpos
  · rw [h0]
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    norm_num
  · obtain ⟨d, hd⟩ : ∃ d, roundCount V DP χ n = d + 1 := ⟨roundCount V DP χ n - 1, by omega⟩
    have hsettled : ∀ j ∈ Finset.range d,
        (1 : ℝ) / 2 ≤ roundValue V χ v (sched V DP χ j) := by
      intro j hj
      simp only [Finset.mem_range] at hj
      have hopen : sched V DP χ (j + 1) ≤ n :=
        (roundCount_spec V DP χ n (j + 1)).2 (by omega)
      have hstage : settleStage V DP χ (sched V DP χ j) ≤ n :=
        le_of_lt (lt_of_lt_of_le (settleStage_sched_lt V DP χ j) hopen)
      exact half_le_roundValue (settleStage_spec (hdicho j)) hstage v hv
    have hlow : (d : ℝ) * (1 / 2)
        ≤ ∑ j ∈ Finset.range d, roundValue V χ v (sched V DP χ j) := by
      calc (d : ℝ) * (1 / 2)
          = ∑ _j ∈ Finset.range d, (1 / 2 : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum hsettled
    have hlast : (-1 : ℝ) ≤ roundValue V χ v (sched V DP χ d) :=
      neg_one_le_roundValue hV v _
    rw [hd, Finset.sum_range_succ]
    push_cast
    linarith

/-- **The trader exploits `V`** (`def:exploitation`): plausible assessments bounded below
by `−3/2`, unbounded above along the schedule.
Kind `C`; hypotheses `(a)`. -/
lemma exploits (Tr : Trader) (V : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (hdicho : ∀ j, Dichotomy V DP χ (sched V DP χ j))
    (hV : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hzero : ∀ (v : PCWorld) i, (∀ j, sched V DP χ j ≠ i) →
      (Tr.strat i).value V v.payout = 0)
    (hval : ∀ (v : PCWorld) j, (Tr.strat (sched V DP χ j)).value V v.payout
      = roundValue V χ v (sched V DP χ j)) :
    Tr.Exploits V DP := by
  have hbound : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      ((roundCount V DP χ n : ℝ) - 1) / 2 - 1 ≤ Tr.netWorth V v n :=
    fun n v hv => netWorth_ge Tr V DP χ hdicho hV v n hv (hzero v) (hval v)
  refine ⟨⟨-(3 / 2), ?_⟩, ?_⟩
  · rintro x ⟨n, v, hv, rfl⟩
    have hc : (0 : ℝ) ≤ (roundCount V DP χ n : ℝ) := Nat.cast_nonneg _
    have := hbound n v hv
    linarith
  · rintro ⟨B, hB⟩
    obtain ⟨J, hJ⟩ := exists_nat_gt (2 * (B + 1))
    obtain ⟨v, hv⟩ := hworld (sched V DP χ (J + 1))
    have hcount : (J : ℝ) + 2 ≤ (roundCount V DP χ (sched V DP χ (J + 1)) : ℝ) := by
      have := le_roundCount_sched V DP χ J
      exact_mod_cast this
    have hge := hbound (sched V DP χ (J + 1)) v hv
    have hmem : Tr.netWorth V v (sched V DP χ (J + 1))
        ∈ Tr.plausibleAssessments V DP := ⟨_, v, hv, rfl⟩
    have := hB hmem
    linarith

/-! ## Assembly

What remains is the *construction* of the perturbed market and the advice-reading trader.
Both are recorded as explicit obligations rather than assumed: the conditional refutation
below is unconditional given them, and the witness lemma is the single `sorry`.
-/

/-- **The refutation, modulo the advice construction.**  Given a machine logical inductor
`P`, a computable market `P'` agreeing with it from day `1` on, and a machine-efficient
trader whose day-`n` position is the advice-signed unit position in `χ n` on schedule and
empty off it, the unrestricted finite-perturbation statement is false.

Refutes, rather than renders, the paper's `thm:ifp`: it carries no `Paper node:` line and
is not an inventory endpoint.
Kind `C`; hypotheses `(a)`. -/
theorem not_overgeneral_ifp_of_advice
    (P P' : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (Tr : Trader)
    (hLI : IsMachineLogicalInductor P DP)
    (hP' : ComputableMarket P')
    (hagree : ∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ)
    (hTr : MachineEfficientTrader Tr)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hdicho : ∀ j, Dichotomy P' DP χ (sched P' DP χ j))
    (hzero : ∀ (v : PCWorld) i, (∀ j, sched P' DP χ j ≠ i) →
      (Tr.strat i).value P' v.payout = 0)
    (hval : ∀ (v : PCWorld) j, (Tr.strat (sched P' DP χ j)).value P' v.payout
      = roundValue P' χ v (sched P' DP χ j)) :
    ¬ ∀ (Q Q' : History) (DQ : DeductiveProcess) (N : ℕ),
        IsMachineLogicalInductor Q DQ → ComputableMarket Q' →
        (∀ n, N ≤ n → ∀ φ, Q n φ = Q' n φ) → IsMachineLogicalInductor Q' DQ := by
  intro hifp
  have hLI' : IsMachineLogicalInductor P' DP := hifp P P' DP 1 hLI hP' hagree
  exact hLI'.noExploit Tr hTr
    (exploits Tr P' DP χ hdicho hP'.1 hworld hzero hval)

/-- The advice construction itself.  `P'` perturbs day `0` of a machine logical inductor
`P` by publishing, as the prices of disjoint advice atoms, the schedule bit and the sign
bit `[P n (χ n) < 1/2]` of the repo's diagonal family `χ`; `Tr` is the trader whose day-`n`
coefficient is the rank-`0` expression `price (schedAtom n) 0 * (2 * price (signAtom n) 0
- 1)` and whose traded sentence is `χ n`.

**Not proved.**  This is the whole remaining content of the counterexample, and it is the
only `sorry` in this development.  Nothing here may be read as refuting the paper's
`thm:ifp` until it is discharged. -/
theorem exists_advice_perturbation :
    ∃ (P P' : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (Tr : Trader),
      IsMachineLogicalInductor P DP ∧ ComputableMarket P' ∧
      (∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) ∧ MachineEfficientTrader Tr ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
      (∀ j, Dichotomy P' DP χ (sched P' DP χ j)) ∧
      (∀ (v : PCWorld) i, (∀ j, sched P' DP χ j ≠ i) →
        (Tr.strat i).value P' v.payout = 0) ∧
      (∀ (v : PCWorld) j, (Tr.strat (sched P' DP χ j)).value P' v.payout
        = roundValue P' χ v (sched P' DP χ j)) := by
  -- TODO(thm:ifp): need the perturbed market `P'` (day `0` republished as advice atom
  -- prices, days `≥ 1` equal to `P`) together with `ComputableMarket P'` — a rational
  -- quote table whose day-`0` row searches for the settlement stage of `χ n` by
  -- `Nat.rfindOpt`, terminating by `DeductiveProcess.exists_stage_entails`, in the style
  -- of `liaEntries_computable`.  The decidable finite-stage entailment test that search
  -- needs already exists: `stageEntails` with `stageEntails_primrec` and
  -- `DeductiveProcess.stageEntails_complete_of_semantic`
  -- (`Construction/Witnesses/FiniteEntailment.lean`).
  -- TODO(thm:ifp): need the advice trader together with `MachineEfficientTrader Tr`, via
  -- `EfficientlyComputable.ofTokenEmitter` / `ec_of_rawEmission` and
  -- `EfficientlyComputable.toMachine`, with the `PolySequence` certificate carrying both
  -- `coefficient_rank ≤ n` and the `RpnSentenceCodes` for `χ`.
  -- TODO(thm:ifp): need `Dichotomy P' DP χ m` for every `m ≥ 1`, i.e. transport of
  -- `ParadoxResistanceQuote.diagonal_reflected` at `p = 1/2` across `hagree`.
  sorry

/-- **The unrestricted finite-day perturbation statement is false** — the negation of the
paper's `thm:ifp` as printed, at the paper's own quantifier.

**Depends on `sorryAx`** through `exists_advice_perturbation`.  The reduction below is
kernel-checked; the witness is not built.  Refutes rather than renders, so no
`Paper node:` line.
Kind `C` on `exists_advice_perturbation`; hypotheses `(a)`. -/
theorem not_overgeneral_ifp :
    ¬ ∀ (P P' : History) (DP : DeductiveProcess) (N : ℕ),
        IsMachineLogicalInductor P DP → ComputableMarket P' →
        (∀ n, N ≤ n → ∀ φ, P n φ = P' n φ) → IsMachineLogicalInductor P' DP := by
  obtain ⟨P, P', DP, χ, Tr, hLI, hP', hagree, hTr, hworld, hdicho, hzero, hval⟩ :=
    exists_advice_perturbation
  exact not_overgeneral_ifp_of_advice P P' DP χ Tr hLI hP' hagree hTr hworld hdicho
    hzero hval

end FinitePerturbationCounterexample
end LogicalInduction

