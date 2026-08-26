import LogicalInduction.Framework.Compactness
import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Properties.Basic
import LogicalInduction.Properties.Introspection

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
  if h : ∃ k, SettledAt V DP χ m k then Nat.find h else 0

/-- Kind `P`; hypotheses `(a)`. -/
lemma settleStage_spec {V : History} {DP : DeductiveProcess} {χ : ℕ → Sentence} {m : ℕ}
    (h : Dichotomy V DP χ m) : SettledAt V DP χ m (settleStage V DP χ m) := by
  have hex : ∃ k, SettledAt V DP χ m k := exists_settled h
  rw [settleStage, dif_pos hex]
  exact Nat.find_spec hex

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

/-! ## Transport across the day-`0` perturbation

The schedule and its settlement stages are defined against the *perturbed* market `P'`,
but they only ever inspect days `≥ 1`, where `P'` agrees with `P`.  So they are the very
same objects computed from `P` alone.  That is what removes the apparent circularity in
the construction: the day-`0` advice table publishes bits about a schedule that does not
depend on day `0`.

`settleStage` is the *least* settling stage rather than an arbitrary one, which is both
what makes this transport a two-line `Nat.find_mono` and what keeps the schedule within
reach of a search-based computable quote table.
-/

/-- Settlement is insensitive to a day-`0` perturbation, on days `≥ 1`.
Kind `P`; hypotheses `(a)`. -/
lemma settledAt_congr {P P' : History} {DP : DeductiveProcess} {χ : ℕ → Sentence}
    (hagree : ∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    SettledAt P DP χ m k ↔ SettledAt P' DP χ m k := by
  simp only [SettledAt, hagree m hm]

/-- The chosen settlement stage transports too, discharged by minimality rather than by
rewriting under a dependent motive.
Kind `C`; hypotheses `(a)`, `(b)` `Nat.find_mono`. -/
lemma settleStage_congr {P P' : History} {DP : DeductiveProcess} {χ : ℕ → Sentence}
    (hagree : ∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) {m : ℕ} (hm : 1 ≤ m) :
    settleStage P DP χ m = settleStage P' DP χ m := by
  by_cases hex : ∃ k, SettledAt P DP χ m k
  · have hex' : ∃ k, SettledAt P' DP χ m k :=
      hex.imp (fun k hk => (settledAt_congr hagree hm k).1 hk)
    rw [settleStage, settleStage, dif_pos hex, dif_pos hex']
    exact le_antisymm
      (Nat.find_mono (fun k hk => (settledAt_congr hagree hm k).2 hk))
      (Nat.find_mono (fun k hk => (settledAt_congr hagree hm k).1 hk))
  · have hex' : ¬ ∃ k, SettledAt P' DP χ m k :=
      fun h => hex (h.imp (fun k hk => (settledAt_congr hagree hm k).2 hk))
    rw [settleStage, settleStage, dif_neg hex, dif_neg hex']

/-- The schedule is insensitive to the day-`0` perturbation: no circularity.
Kind `C`; hypotheses `(a)`. -/
lemma sched_congr {P P' : History} {DP : DeductiveProcess} {χ : ℕ → Sentence}
    (hagree : ∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) (j : ℕ) :
    sched P DP χ j = sched P' DP χ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show max (sched P DP χ j) (settleStage P DP χ (sched P DP χ j)) + 1
        = max (sched P' DP χ j) (settleStage P' DP χ (sched P' DP χ j)) + 1
      rw [ih, settleStage_congr hagree (one_le_sched P' DP χ j)]

/-- **The repo's diagonal plugs in.**  A `ParadoxResistanceQuote` at threshold `1/2` is
exactly the dichotomy this development runs on (`thm:lp` supplies it), and it survives the
day-`0` perturbation on every day `≥ 1`.
Kind `C`; hypotheses `(a)`, `(b)` `ParadoxResistanceQuote.diagonal_reflected`. -/
lemma dichotomy_of_paradoxQuote {P P' : History} {DP : DeductiveProcess}
    (q : ParadoxResistanceQuote P DP (1 / 2))
    (hagree : ∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) {m : ℕ} (hm : 1 ≤ m) :
    Dichotomy P' DP q.sentence m := by
  intro v hv
  have hcast : (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
  rw [← hagree m hm, ← hcast]
  exact q.diagonal_reflected m v hv

/-- Every scheduled day carries the dichotomy, which is the hypothesis the exploitation
bookkeeping consumes.
Kind `C`; hypotheses `(a)`. -/
lemma dichotomy_sched_of_paradoxQuote {P P' : History} {DP : DeductiveProcess}
    (q : ParadoxResistanceQuote P DP (1 / 2))
    (hagree : ∀ n, 1 ≤ n → ∀ φ, P n φ = P' n φ) (j : ℕ) :
    Dichotomy P' DP q.sentence (sched P' DP q.sentence j) :=
  dichotomy_of_paradoxQuote q hagree (one_le_sched P' DP q.sentence j)

/-! ## The advice atoms

`P' 0` is defined by decoding its argument, so the two advice families must be injective
with disjoint ranges — that, and nothing more, is what the construction needs of them.

Freshness with respect to the deductive process is **not** required here, which is worth
saying explicitly because it is the first thing one expects to need.  `ComputableMarket`
imposes no coherence between a market and its process; `DP` is untouched by the
perturbation; the exploitation bookkeeping quantifies over worlds consistent with `DP.D n`
and never reads `P' 0` at a process atom; and `χ`'s reflection is transported across
`hagree`, which constrains only days `≥ 1`.  Even a hypothetical collision `sa n = χ m`
would be harmless, since nothing reads `P' 0 (χ m)`.

Tags `6`/`7` are nevertheless chosen disjoint from every tag this repo's processes emit —
computation claims `0`–`3` (`ComputationClaimKind.godelCode`), quotation claims `4`
(`quotationClaimCode`), quoted products `5` (`productTag`) — so the advice layer is inert
everywhere, not merely where the proof happens to look.
-/

/-- The schedule-gate advice atom for day `n`, on the fresh tag `6`. -/
def schedAtom (n : ℕ) : Sentence := LO.Propositional.Formula.atom (Nat.pair 6 n)

/-- The sign advice atom for day `n`, on the fresh tag `7`. -/
def signAtom (n : ℕ) : Sentence := LO.Propositional.Formula.atom (Nat.pair 7 n)

@[simp] lemma schedAtom_inj {m n : ℕ} : schedAtom m = schedAtom n ↔ m = n := by
  simp [schedAtom, Nat.pair_eq_pair]

@[simp] lemma signAtom_inj {m n : ℕ} : signAtom m = signAtom n ↔ m = n := by
  simp [signAtom, Nat.pair_eq_pair]

@[simp] lemma schedAtom_ne_signAtom (m n : ℕ) : schedAtom m ≠ signAtom n := by
  simp [schedAtom, signAtom, Nat.pair_eq_pair]

lemma rpn_schedAtom (n : ℕ) : rpn (schedAtom n) = [Nat.pair 6 n + 5] := rfl

lemma rpn_signAtom (n : ℕ) : rpn (signAtom n) = [Nat.pair 7 n + 5] := rfl

/-- Kind `C`; hypotheses `(b)` the `Computable`/`RpnSplice` emitter suite. -/
lemma rpnSentenceCodes_schedAtom : RpnSentenceCodes schedAtom := by
  obtain ⟨c, hc⟩ := ((PolyFueled.const 6).pair PolyFueled.id).addConst 5
  exact RpnSentenceCodes.ofCanonical
    ((PolySegStream.ofTokenStream (PolyTokenStream.polyTok hc)).of_eq
      (fun n => (rpn_schedAtom n).symm))

/-- Kind `C`; hypotheses `(b)` the `Computable`/`RpnSplice` emitter suite. -/
lemma rpnSentenceCodes_signAtom : RpnSentenceCodes signAtom := by
  obtain ⟨c, hc⟩ := ((PolyFueled.const 7).pair PolyFueled.id).addConst 5
  exact RpnSentenceCodes.ofCanonical
    ((PolySegStream.ofTokenStream (PolyTokenStream.polyTok hc)).of_eq
      (fun n => (rpn_signAtom n).symm))

/-! ## The perturbed market

`P'` republishes day `0` as the advice table and leaves every later day alone.  Nothing
below needs the advice bits to be *correct* — that is the next section's job — so the
day-`0` row is taken as two arbitrary bit families and the agreement, lookup and range
laws are proved once and for all.

The row is defined by a decidable-in-principle case split on which advice family the
argument belongs to, using only the injectivity and disjointness of `schedAtom`/`signAtom`.
It is a `Classical` definition rather than an executable one; `ComputableMarket` asks for a
rational quote table and a `Nat.Partrec.Code`, not for the history to be a computable Lean
function, so nothing is lost.
-/

/-- The day-`0` advice row over a base valuation. -/
noncomputable def adviceRow (base : Valuation) (gate sign : ℕ → ℝ) : Valuation :=
  fun φ =>
    if h : ∃ n, φ = schedAtom n then gate h.choose
    else if h : ∃ n, φ = signAtom n then sign h.choose
    else base φ

@[simp] lemma adviceRow_schedAtom (base : Valuation) (gate sign : ℕ → ℝ) (n : ℕ) :
    adviceRow base gate sign (schedAtom n) = gate n := by
  have hex : ∃ m, schedAtom n = schedAtom m := ⟨n, rfl⟩
  rw [adviceRow, dif_pos hex]
  congr 1
  exact (schedAtom_inj.mp hex.choose_spec).symm

@[simp] lemma adviceRow_signAtom (base : Valuation) (gate sign : ℕ → ℝ) (n : ℕ) :
    adviceRow base gate sign (signAtom n) = sign n := by
  have hno : ¬ ∃ m, signAtom n = schedAtom m := by
    rintro ⟨m, hm⟩
    exact schedAtom_ne_signAtom m n hm.symm
  have hex : ∃ m, signAtom n = signAtom m := ⟨n, rfl⟩
  rw [adviceRow, dif_neg hno, dif_pos hex]
  congr 1
  exact (signAtom_inj.mp hex.choose_spec).symm

/-- Kind `P`; hypotheses `(a)`. -/
lemma adviceRow_mem_Icc {base : Valuation} {gate sign : ℕ → ℝ}
    (hbase : ∀ φ, 0 ≤ base φ ∧ base φ ≤ 1)
    (hgate : ∀ n, 0 ≤ gate n ∧ gate n ≤ 1)
    (hsign : ∀ n, 0 ≤ sign n ∧ sign n ≤ 1) (φ : Sentence) :
    0 ≤ adviceRow base gate sign φ ∧ adviceRow base gate sign φ ≤ 1 := by
  rw [adviceRow]
  split_ifs
  · exact hgate _
  · exact hsign _
  · exact hbase φ

/-- The market `P` with day `0` replaced by the advice row. -/
noncomputable def advicePerturb (P : History) (gate sign : ℕ → ℝ) : History :=
  fun n => if n = 0 then adviceRow (P 0) gate sign else P n

/-- **The perturbation is confined to day `0`** — the `hagree` hypothesis of the refutation,
at `N = 1`.
Kind `P`. -/
lemma advicePerturb_agree (P : History) (gate sign : ℕ → ℝ) :
    ∀ n, 1 ≤ n → ∀ φ, P n φ = advicePerturb P gate sign n φ := by
  intro n hn φ
  rw [advicePerturb, if_neg (by omega)]

@[simp] lemma advicePerturb_zero_schedAtom (P : History) (gate sign : ℕ → ℝ) (n : ℕ) :
    advicePerturb P gate sign 0 (schedAtom n) = gate n := by
  rw [advicePerturb, if_pos rfl, adviceRow_schedAtom]

@[simp] lemma advicePerturb_zero_signAtom (P : History) (gate sign : ℕ → ℝ) (n : ℕ) :
    advicePerturb P gate sign 0 (signAtom n) = sign n := by
  rw [advicePerturb, if_pos rfl, adviceRow_signAtom]

/-- Kind `C`; hypotheses `(a)`. -/
lemma advicePerturb_mem_Icc {P : History} {gate sign : ℕ → ℝ}
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hgate : ∀ n, 0 ≤ gate n ∧ gate n ≤ 1)
    (hsign : ∀ n, 0 ≤ sign n ∧ sign n ≤ 1) (n : ℕ) (φ : Sentence) :
    0 ≤ advicePerturb P gate sign n φ ∧ advicePerturb P gate sign n φ ≤ 1 := by
  rw [advicePerturb]
  split_ifs
  · exact adviceRow_mem_Icc (hP 0) hgate hsign φ
  · exact hP n φ

/-! ### The advice bits

Both bits are computed from `P`, never from `P'`.  For the sign bit that is forced: day
`0`'s own price of `χ 0` is one of the things the perturbation overwrites, so a sign bit
required to be correct about `P' 0 (χ 0)` would be self-referential.  It never arises,
because `sched j ≥ 1` — day `0` is not scheduled.  For the gate bit it is `sched_congr`
that licenses it, and that is what keeps the day-`0` row a function of `P` alone.
-/

/-- The schedule gate bit for day `n`. -/
noncomputable def gateBit (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (n : ℕ) :
    ℝ := if ∃ j, sched P DP χ j = n then 1 else 0

/-- The advice sign bit for day `n`. -/
noncomputable def signBit (P : History) (χ : ℕ → Sentence) (n : ℕ) : ℝ :=
  if P n (χ n) < 1 / 2 then 1 else 0

lemma gateBit_mem_Icc (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) (n : ℕ) :
    0 ≤ gateBit P DP χ n ∧ gateBit P DP χ n ≤ 1 := by
  rw [gateBit]; split_ifs <;> norm_num

lemma signBit_mem_Icc (P : History) (χ : ℕ → Sentence) (n : ℕ) :
    0 ≤ signBit P χ n ∧ signBit P χ n ≤ 1 := by
  rw [signBit]; split_ifs <;> norm_num

/-- The perturbed market of the counterexample. -/
noncomputable def advicePerturbed (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) :
    History := advicePerturb P (gateBit P DP χ) (signBit P χ)

lemma advicePerturbed_agree (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence) :
    ∀ n, 1 ≤ n → ∀ φ, P n φ = advicePerturbed P DP χ n φ :=
  advicePerturb_agree P _ _

lemma advicePerturbed_mem_Icc {P : History} (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) (φ : Sentence) :
    0 ≤ advicePerturbed P DP χ n φ ∧ advicePerturbed P DP χ n φ ≤ 1 :=
  advicePerturb_mem_Icc hP (gateBit_mem_Icc P DP χ) (signBit_mem_Icc P χ) n φ

/-- **Gate closed off schedule** — the `hgateOff` conjunct.
Kind `C`; hypotheses `(a)`. -/
lemma advicePerturbed_schedAtom_off (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (i : ℕ) (hi : ∀ j, sched (advicePerturbed P DP χ) DP χ j ≠ i) :
    advicePerturbed P DP χ 0 (schedAtom i) = 0 := by
  rw [advicePerturbed, advicePerturb_zero_schedAtom, gateBit, if_neg]
  rintro ⟨j, hj⟩
  exact hi j ((sched_congr (advicePerturbed_agree P DP χ) j).symm.trans hj)

/-- **Gate open on schedule** — the `hgateOn` conjunct.
Kind `C`; hypotheses `(a)`. -/
lemma advicePerturbed_schedAtom_on (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (j : ℕ) :
    advicePerturbed P DP χ 0 (schedAtom (sched (advicePerturbed P DP χ) DP χ j)) = 1 := by
  rw [advicePerturbed, advicePerturb_zero_schedAtom, gateBit, if_pos]
  exact ⟨j, sched_congr (advicePerturbed_agree P DP χ) j⟩

/-- **The published sign bit is the market's own** — the `hsign` conjunct, at the scheduled
days, which are the only ones the trader reads.
Kind `C`; hypotheses `(a)`. -/
lemma advicePerturbed_signAtom_on (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence)
    (j : ℕ) :
    advicePerturbed P DP χ 0 (signAtom (sched (advicePerturbed P DP χ) DP χ j))
      = if advicePerturbed P DP χ (sched (advicePerturbed P DP χ) DP χ j)
            (χ (sched (advicePerturbed P DP χ) DP χ j)) < 1 / 2 then 1 else 0 := by
  set P' := advicePerturbed P DP χ with hP'
  set m := sched P' DP χ j with hm
  rw [hP', advicePerturbed, advicePerturb_zero_signAtom, signBit,
    advicePerturbed_agree P DP χ m (one_le_sched P' DP χ j) (χ m)]
  rfl

/-! ## The advice trader

An `EF` coefficient can carry a number but cannot name a sentence, so the traded sentence
is always `χ n`, emitted by the trader itself; the two day-`0` advice prices only gate
*whether* to trade and with *which* sign.  `EF` has no subtraction, so `2 * b - 1` is
spelled `add (mul (const 2) (price (si n) 0)) (const (-1))`.

Every price leaf sits on day `0`, so the coefficient has rank `0` and is legal on every
day (`EF.rank_price` puts no constraint on the sentence).
-/

/-- The day-`n` coefficient: the schedule gate `sa n` times the advice sign `si n`, both
read off day `0`. -/
def adviceCoefficient (sa si : ℕ → Sentence) (n : ℕ) : EF :=
  .mul (.price (sa n) 0) (.add (.mul (.const 2) (.price (si n) 0)) (.const (-1)))

@[simp] lemma adviceCoefficient_denote (sa si : ℕ → Sentence) (n : ℕ) (V : History) :
    (adviceCoefficient sa si n).denote V = V 0 (sa n) * (2 * V 0 (si n) - 1) := by
  show (adviceCoefficient sa si n).denoteWith [] V = _
  simp only [adviceCoefficient, EF.denoteWith_mul, EF.denoteWith_add, EF.denoteWith_const,
    EF.denoteWith_price]
  push_cast
  ring

/-- The advice trader: a single unit position in `χ n` on day `n`, gated and signed by the
two day-`0` advice prices. -/
def adviceTrader (sa si χ : ℕ → Sentence) : Trader where
  strat n :=
    { trades := [(adviceCoefficient sa si n, χ n)]
      rank_le := by
        intro p hp
        rw [List.mem_singleton] at hp
        subst hp
        show (adviceCoefficient sa si n).rank ≤ n
        simp [adviceCoefficient] }

@[simp] lemma adviceTrader_trades (sa si χ : ℕ → Sentence) (n : ℕ) :
    ((adviceTrader sa si χ).strat n).trades = [(adviceCoefficient sa si n, χ n)] := rfl

/-- Kind `P`; hypotheses `(a)`. -/
lemma adviceTrader_value (sa si χ : ℕ → Sentence) (V : History) (v : PCWorld) (n : ℕ) :
    ((adviceTrader sa si χ).strat n).value V v.payout
      = V 0 (sa n) * (2 * V 0 (si n) - 1) * (v.payout (χ n) - V n (χ n)) := by
  simp only [Strategy.value, adviceTrader_trades, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, adviceCoefficient_denote]
  ring

/-- Off schedule the gate is closed, so the trader holds nothing — this is `hzero`.
Kind `C`; hypotheses `(a)`. -/
lemma adviceTrader_value_off_sched (sa si χ : ℕ → Sentence) (V : History)
    (DP : DeductiveProcess) (hgateOff : ∀ i, (∀ j, sched V DP χ j ≠ i) → V 0 (sa i) = 0)
    (v : PCWorld) (i : ℕ) (hi : ∀ j, sched V DP χ j ≠ i) :
    ((adviceTrader sa si χ).strat i).value V v.payout = 0 := by
  rw [adviceTrader_value, hgateOff i hi]
  ring

/-- On schedule the gate is open and the published sign bit is exactly `signCoeff`, so the
day's strategy value is the round value the bookkeeping expects — this is `hval`.
Kind `C`; hypotheses `(a)`. -/
lemma adviceTrader_value_on_sched (sa si χ : ℕ → Sentence) (V : History)
    (DP : DeductiveProcess) (hgateOn : ∀ j, V 0 (sa (sched V DP χ j)) = 1)
    (hsign : ∀ j, V 0 (si (sched V DP χ j))
      = if V (sched V DP χ j) (χ (sched V DP χ j)) < 1 / 2 then 1 else 0)
    (v : PCWorld) (j : ℕ) :
    ((adviceTrader sa si χ).strat (sched V DP χ j)).value V v.payout
      = roundValue V χ v (sched V DP χ j) := by
  rw [adviceTrader_value, hgateOn j, hsign j, roundValue, signCoeff]
  by_cases h : V (sched V DP χ j) (χ (sched V DP χ j)) < 1 / 2
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-- **The advice trader is machine-efficient**, given `RpnSentenceCodes` certificates for
the two advice-atom families and for the traded diagonal.

Route note: the coefficient carries *price* leaves, which is the whole point of the
construction, so the price-free entry points
(`EfficientlyComputable.ofSingleTradeBlocks` / `ofTradeBlocks`, both of which demand
`EF.priceFree`) do not apply.  The general splice capstone `RpnSpliceStream.ec` does, with
`RpnSpliceStream.serialize_price` supplying each price leaf's sentence slot from the
corresponding advice-atom code stream.
Kind `C`; hypotheses `(a)`, `(b)` the `RpnSplice` combinator suite. -/
lemma adviceTrader_efficient {sa si χ : ℕ → Sentence}
    (hsa : RpnSentenceCodes sa) (hsi : RpnSentenceCodes si) (hχ : RpnSentenceCodes χ) :
    MachineEfficientTrader (adviceTrader sa si χ) := by
  have hday : PolyFueled (Nat.Partrec.Code.const 0) (fun _ : ℕ => 0) := PolyFueled.const 0
  have hgate : RpnSpliceStream (fun n => (EF.price (sa n) 0).serialize) :=
    RpnSpliceStream.serialize_price hsa PolyFueled.id hday
  have hsign : RpnSpliceStream (fun n => (EF.price (si n) 0).serialize) :=
    RpnSpliceStream.serialize_price hsi PolyFueled.id hday
  have hcoef : RpnSpliceStream (fun n => (adviceCoefficient sa si n).serialize) :=
    RpnSpliceStream.serialize_mul hgate
      (RpnSpliceStream.serialize_add
        (RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_const 2) hsign)
        (RpnSpliceStream.serialize_const (-1)))
  have htrade : RpnSpliceStream (fun n => [6, Encodable.encode (χ n)]) :=
    RpnSpliceStream.tradeSlot hχ PolyFueled.id
  refine EfficientlyComputable.toMachine
    (RpnSpliceStream.ec _ ((hcoef.append htrade).of_eq (fun n => ?_)))
  simp [adviceTrader, serializeTrades]

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
  obtain ⟨P, DP, χ, hLI, hworld, hχ, hdicho, hcomp⟩ :
      ∃ (P : History) (DP : DeductiveProcess) (χ : ℕ → Sentence),
        IsMachineLogicalInductor P DP ∧
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) ∧
        RpnSentenceCodes χ ∧
        (∀ m, 1 ≤ m → Dichotomy (advicePerturbed P DP χ) DP χ m) ∧
        ComputableMarket (advicePerturbed P DP χ) := by
    -- TODO(thm:ifp): need the concrete witness.  `P := liaHistory (theoremDP T)` with
    -- `LIA_isMachineLogicalInductor` and `theoremDP_hworld`; `χ` the canonical `p = 1/2`
    -- diagonal `(theoremDiagonalQuoteCode T (1/2)).toBooleanQuoteCode.sentence`, whose
    -- `sentence_codes` field is `RpnSentenceCodes χ` and whose `diagonal_reflected` gives
    -- the dichotomy through `dichotomy_of_paradoxQuote` applied to
    -- `paradoxResistanceQuoteOfDiagonal … (theoremMarketComputation T) (1/2) …`.
    -- Note the `MarketComputation` must be the one for the **unperturbed** `P`: `χ n`
    -- asserts a fact about `P`'s own quote program, and `dichotomy_of_paradoxQuote`
    -- transports it to `P'` across `advicePerturbed_agree`.
    --
    -- **Blocked here by module layering, not by mathematics.**  `theoremDP` and the whole
    -- quotation layer live in `Construction/Witnesses/ComputationDP.lean`, which imports
    -- `ComputationSyntax` → `BoundedEvaluation` → `LogicalInduction.Properties` → this
    -- file.  Naming them here is an import cycle.  This existential (and only it) belongs
    -- in a module downstream of `ComputationDP`, exactly as
    -- `lic_paradox_resistance_ofDiagonal_unconditional` does.
    --
    -- TODO(thm:ifp): need `ComputableMarket (advicePerturbed P DP χ)`.  All three
    -- ingredients are import-safe from here (`Construction/Witnesses/FiniteEntailment.lean`
    -- imports only `LIACompiler` and `Framework/Compactness`):
    --   * `sentencePrimcodable` (`Construction/LIACompiler.lean:225`) for decoding a
    --     sentence code and recognising the tag-`6`/`7` advice atoms;
    --   * `settleStage` is `Nat.find` over `SettledAt`, which `stageEntails` decides
    --     (`stageEntails_primrec`) and `DeductiveProcess.stageEntails_complete_of_semantic`
    --     shows is eventually true, so `Nat.rfindOpt` + `Partrec.of_eq_tot` computes it in
    --     the `liaEntries_computable` style — the totality side condition is a plain
    --     existence statement, so the compactness proof of `exists_stage_entails` suffices
    --     and no constructive stage bound is needed;
    --   * `sched` is strictly monotone with `sched 0 = 1`, so `∃ j, sched j = n` is the
    --     bounded search `∃ j ≤ n, sched j = n`.
    sorry
  exact ⟨P, advicePerturbed P DP χ, DP, χ, adviceTrader schedAtom signAtom χ,
    hLI, hcomp, advicePerturbed_agree P DP χ,
    adviceTrader_efficient rpnSentenceCodes_schedAtom rpnSentenceCodes_signAtom hχ,
    hworld,
    fun j => hdicho _ (one_le_sched _ DP χ j),
    fun v i hi => adviceTrader_value_off_sched schedAtom signAtom χ _ DP
      (advicePerturbed_schedAtom_off P DP χ) v i hi,
    fun v j => adviceTrader_value_on_sched schedAtom signAtom χ _ DP
      (advicePerturbed_schedAtom_on P DP χ) (advicePerturbed_signAtom_on P DP χ) v j⟩

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



