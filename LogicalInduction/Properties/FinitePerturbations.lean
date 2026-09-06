import LogicalInduction.Framework.Affine
import LogicalInduction.Framework.Emission.Computable
import LogicalInduction.Framework.Emission.FreezeTransducer
import LogicalInduction.Framework.MachineEfficiency

/-!
# §4.6 Closure under finite perturbations (`thm:ifp`, `app:ifp`)

The paper transports an exploiting trader across a finite change of market history by
replacing every old price leaf in its feature syntax with the corresponding rational
constant.  This module renders that syntax freeze, proves its rank, size, semantic,
net-worth and exploitation laws, and states the corrected closure theorem at both
efficiency classes.

## The paper erratum

The printed theorem is false, and its printed proof is separately invalid.  `app:ifp`
justifies efficiency of the transported trader thus:

> "Note that `F` is efficiently computable: by the assumption that `pt_n = pt'_n` for all
> `n ≥ N`, only finitely many constants `pt_i(phi)` are needed, and can be hard-coded
> into `F`."

Finitely many *days* `i < N` are involved, but `phi` still ranges over **all** sentences: a
day-`n` trade expression may reference `phi^{*i}` for any `phi` of rank `≤ n`, so the
constant set `{pt_i(phi) : i < N, phi ∈ Sentences}` is infinite.  `F` must therefore
*compute* `pt_i(phi)` rather than hard-code it, and `def:marketprocess` — a market is any
computable sequence of pricings, with no finite support and no time bound — bounds neither
that computation's runtime nor the bit-size of the rational it returns.  So `F` is not
efficiently computable for the class of markets the theorem quantifies over.
`FinitePerturbationCounterexample.not_overgeneral_ifp` refutes the printed statement;
`notes/paper-errata.md`, PE1, is the ledger.

The gap is not pedantic.  Let `P'` agree with the constructed inductor's market from day `1`
on, with `P' 0 phi = 1 - 1/2^(2^(encode phi))` — a legal market by `def:marketprocess`.  A
trader whose day-`n` strategy prices a sentence of code `~n` at day `0` freezes to a
`.const` whose numeral is `~2^(2^n)`, which no polynomial clock can emit
(`codeEvaln_result_le` and `codeEvalBound_poly` give a fixed-code polynomial *output* bound,
not an output-`≤`-fuel bound).  For that `P'`, `EfficientPrefixPatch P' 1` is uninhabited:
the hypothesis is unsatisfiable, not merely unproved.  Neither this market nor the step it
rests on — that no polynomial clock emits a numeral of magnitude `2^(2^n)` — is formalized.

The paper knows that its own construction has finite support per day (`sec:construct`, the
remark following the belief-sequence definition) and deliberately generalizes the property
tail to arbitrary markets.  Finite support is exactly what rescues the hard-coding step, so
the gap is a cost of that generalization rather than an oversight about the construction.

## The freeze

The freeze recursion `EF.freezeOn quote sel` on the feature syntax, and the flat-token
transducer `EF.freezeTokenRunOn` that a machine-class trader runs in its place, are
`Framework/Emission/FreezeTransducer.lean`.  This module lifts them: `Strategy.freezeOn` and
`Trader.freezeOn` are the coefficient-wise and day-wise liftings, `Strategy.freezeBefore` and
`Trader.freezeBefore` their `day < cutoff` instances (each `freezeBefore_eq_freezeOn` is
`rfl`, so every day-cutoff law is a transport rather than a parallel induction).  The laws
proved here are strategy value on an unselected day (`Strategy.freezeOn_value`) and the
explicit finite net-worth error bound `Trader.freezeOnErrorBound` together with
`Trader.freezeOn_netWorth_difference_le`.

`Trader.Exploits.of_boundedDifference` is the abstract finite-prefix accounting step that
both directions of every form below use: a uniform bounded net-worth difference preserves
exploitation.

## The corrected statement

`FiniteSupportPerturbation P P'` asks that only finitely many `(day, sentence)` price
coordinates move.  That hypothesis is strictly stronger than the paper's tail agreement —
`FiniteSupportPerturbation.tail_agree` proves one direction and
`tailAgree_not_finiteSupport` refutes the other — and it is exactly the case in which the
appendix's hard-coding step is literally valid, the constant table being a finite list of
`(day, sentence, price)` rows.  `machine_lic_iff_of_finiteSupportPerturbation` is the
machine-class form.  The client-facing statement, with the patch compiled from each market's
own computability certificate and no condition on the moved sentences, is
`FreezeOracle.machine_lic_iff_of_finiteSupport`, re-exported as
`API.lic_iff_of_finiteSupportPerturbation_machine`.

The fuel-class carriers `lic_iff_of_finitePerturbation` and
`lic_iff_of_finiteSupportPerturbation` keep the paper's own hypothesis shape, and their
certificates `EfficientPrefixPatch` and `FiniteSupportPatch` are uninhabited: the fuel digit
model is closed under the forward big-value operations and open under their inverses, and
the escape-leaf decode the frozen lookup needs is such an inverse (`dd:fuel`; see
`Construction/Freeze/Compiler.lean`).  The token-model content that does exist for the
constructed inductor is `liaFreezeBefore_preserves_ecTok`
(`Construction/Freeze/Prefix.lean`).

`FreezeStreamRewriter` isolates the one `Complexity.FP` fact the machine-class patch turns
on, and `FreezeStep.freezeStreamRewriter_of_runOracle` discharges it.  Non-vacuity is
`FreezeOracle.machine_lic_iff_twoPoint`, a concrete pair of genuinely different computable
markets, so the antecedent is satisfiable; content is
`LIAPerturbation.machineLogicalInductor_liaPerturbed`, which moves one price of the
constructed inductor `liaHistory` and concludes that the result is still a machine logical
inductor, with `LIAPerturbation.liaPerturbed_ne` proving the price change nonzero.  That
instance inherits `Construction/LIA.lean`'s own two hypotheses — the market program and a
computable deductive process — which nothing here discharges.
-/

namespace LogicalInduction

open scoped BigOperators

/-! ## Strategy and trader freezes, and the net-worth error bound

The freeze lifts coefficient-wise to strategies and day-wise to traders.  On a day whose
whole sentence fibre is unselected the value transports exactly; on the finitely many
affected days it is estimated, giving the explicit net-worth bounds
`Trader.freezeBeforeErrorBound` and `Trader.freezeOnErrorBound`. -/

namespace Strategy

/-- Apply the selector freeze to every coefficient of a strategy. -/
def freezeOn {day : ℕ} (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (T : Strategy day) : Strategy day where
  trades := T.trades.map fun p => (p.1.freezeOn quote sel, p.2)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (q.1.freezeOn_rank_le quote sel).trans (T.rank_le q hq)

/-- Apply the old-price freeze to every coefficient of a strategy: the `day < cutoff`
instance of `Strategy.freezeOn`. -/
def freezeBefore {day : ℕ} (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (T : Strategy day) : Strategy day :=
  T.freezeOn quote (fun d _ => decide (d < cutoff))

lemma freezeBefore_eq_freezeOn {day : ℕ} (T : Strategy day)
    (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    T.freezeBefore quote cutoff = T.freezeOn quote (fun d _ => decide (d < cutoff)) := rfl

/-- On an unchanged tail day, a frozen strategy against `P'` has exactly the value of the
original strategy against `P`. -/
lemma freezeBefore_value
    {day : ℕ} (T : Strategy day) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History) (w : Valuation)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    (hday : cutoff ≤ day) :
    (T.freezeBefore quote cutoff).value P' w = T.value P w := by
  simp only [Strategy.value, freezeBefore, freezeOn, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [show (EF.freezeOn quote (fun d _ => decide (d < cutoff)) p.1).denote P'
        = p.1.denote P from p.1.freezeBefore_denote quote cutoff P P' hprefix htail]
  rw [← htail day hday p.2]

/-- **The settlement term is the obstruction to exact transport at strategy level.**
`Strategy.value` contains `- V day p.2`, which is *not* a syntactic leaf and so cannot be
frozen.  Exact equality therefore needs the whole day-`day` fiber to be unselected. -/
lemma freezeOn_value {day : ℕ} (T : Strategy day) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (P P' : History) (w : Valuation)
    (hin : ∀ d φ, sel d φ = true → P d φ = (quote d φ : ℝ))
    (hout : ∀ d φ, sel d φ = false → P d φ = P' d φ)
    (hday : ∀ φ, sel day φ = false) :
    (T.freezeOn quote sel).value P' w = T.value P w := by
  simp only [Strategy.value, freezeOn, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [p.1.freezeOn_denote quote sel P P' hin hout]
  rw [← hout day p.2 (hday p.2)]

end Strategy

namespace Trader

/-- Apply the selector freeze to every day's strategy. -/
def freezeOn (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool) (Tr : Trader) :
    Trader where
  strat day := (Tr.strat day).freezeOn quote sel

/-- The paper's false-report trader: coefficients see the frozen old prefix.  The
`day < cutoff` instance of `Trader.freezeOn`. -/
def freezeBefore (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (Tr : Trader) : Trader :=
  Tr.freezeOn quote (fun d _ => decide (d < cutoff))

lemma freezeBefore_eq_freezeOn (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    Tr.freezeBefore quote cutoff = Tr.freezeOn quote (fun d _ => decide (d < cutoff)) :=
  rfl

lemma freezeBefore_value_tail
    (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History) (w : Valuation)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    {day : ℕ} (hday : cutoff ≤ day) :
    ((Tr.freezeBefore quote cutoff).strat day).value P' w =
      (Tr.strat day).value P w := by
  exact (Tr.strat day).freezeBefore_value quote cutoff P P' w hprefix htail hday

/-- A concrete finite bound for the discrepancy contributed by the finitely many days
before `cutoff`. -/
noncomputable def freezeBeforeErrorBound
    (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History) : ℝ :=
  ∑ day ∈ Finset.range cutoff,
    ((Tr.strat day).magnitude P +
      (((Tr.freezeBefore quote cutoff).strat day).magnitude P'))

/-- The original and frozen traders' net worths differ by at most the explicit finite
prefix bound.  Every tail summand cancels exactly; the only estimate is the standard
`|strategy value| ≤ magnitude` bound on the finitely many early days. -/
lemma freezeBefore_netWorth_difference_le
    (Tr : Trader) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    (hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1)
    (hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1)
    (v : PCWorld) (n : ℕ) :
    |Tr.netWorth P v n - (Tr.freezeBefore quote cutoff).netWorth P' v n| ≤
      Tr.freezeBeforeErrorBound quote cutoff P P' := by
  let g : ℕ → ℝ := fun day ↦
    (Tr.strat day).magnitude P +
      (((Tr.freezeBefore quote cutoff).strat day).magnitude P')
  have hw : ∀ φ, v.payout φ = 0 ∨ v.payout φ = 1 := by
    intro φ
    by_cases hφ : v.Holds φ
    · exact Or.inr (by simp [PCWorld.payout, hφ])
    · exact Or.inl (by simp [PCWorld.payout, hφ])
  have hterm : ∀ day,
      |(Tr.strat day).value P v.payout -
          ((Tr.freezeBefore quote cutoff).strat day).value P' v.payout| ≤
        if day < cutoff then g day else 0 := by
    intro day
    by_cases hday : day < cutoff
    · rw [if_pos hday]
      exact (abs_sub _ _).trans (add_le_add
        (Strategy.abs_value_le_magnitude (Tr.strat day) P v.payout hw (hP day))
        (Strategy.abs_value_le_magnitude
          ((Tr.freezeBefore quote cutoff).strat day) P' v.payout hw (hP' day)))
    · rw [if_neg hday]
      have heq := Tr.freezeBefore_value_tail quote cutoff P P' v.payout
        hprefix htail (Nat.le_of_not_gt hday)
      rw [heq]
      simp
  have hg : ∀ day, 0 ≤ g day := by
    intro day
    exact add_nonneg (Strategy.magnitude_nonneg _ _) (Strategy.magnitude_nonneg _ _)
  calc
    |Tr.netWorth P v n - (Tr.freezeBefore quote cutoff).netWorth P' v n| =
        |∑ day ∈ Finset.range (n + 1),
          ((Tr.strat day).value P v.payout -
            ((Tr.freezeBefore quote cutoff).strat day).value P' v.payout)| := by
          simp only [Trader.netWorth]
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ day ∈ Finset.range (n + 1),
          |(Tr.strat day).value P v.payout -
            ((Tr.freezeBefore quote cutoff).strat day).value P' v.payout| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ day ∈ Finset.range (n + 1),
          if day < cutoff then g day else 0 :=
          Finset.sum_le_sum (fun day _ ↦ hterm day)
    _ = ∑ day ∈ (Finset.range (n + 1)).filter (fun day ↦ day < cutoff),
          g day := by rw [Finset.sum_filter]
    _ ≤ ∑ day ∈ Finset.range cutoff, g day := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro day hday
            simp only [Finset.mem_filter, Finset.mem_range] at hday ⊢
            exact hday.2
          · intro day _ _
            exact hg day
    _ = Tr.freezeBeforeErrorBound quote cutoff P P' := rfl

/-- The finite set of days on which the perturbation is felt. -/
def freezeDays (S : Finset (ℕ × Sentence)) : Finset ℕ := S.image Prod.fst

/-- The explicit bound on the net-worth discrepancy between a trader and its freeze,
supported on the finitely many affected days `D`. -/
noncomputable def freezeOnErrorBound (Tr : Trader) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (D : Finset ℕ) (P P' : History) : ℝ :=
  ∑ day ∈ D, ((Tr.strat day).magnitude P +
    ((Tr.freezeOn quote sel).strat day).magnitude P')

/-- Net worths differ by at most an explicit bound supported on the finitely many
*affected days*.  Every unaffected day cancels exactly. -/
lemma freezeOn_netWorth_difference_le (Tr : Trader) (quote : ℕ → Sentence → ℚ)
    (sel : ℕ → Sentence → Bool) (D : Finset ℕ) (P P' : History)
    (hin : ∀ d φ, sel d φ = true → P d φ = (quote d φ : ℝ))
    (hout : ∀ d φ, sel d φ = false → P d φ = P' d φ)
    (hD : ∀ d, d ∉ D → ∀ φ, sel d φ = false)
    (hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1)
    (hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1)
    (v : PCWorld) (n : ℕ) :
    |Tr.netWorth P v n - (Tr.freezeOn quote sel).netWorth P' v n| ≤
      Tr.freezeOnErrorBound quote sel D P P' := by
  classical
  let g : ℕ → ℝ := fun day ↦
    (Tr.strat day).magnitude P + ((Tr.freezeOn quote sel).strat day).magnitude P'
  have hw : ∀ φ, v.payout φ = 0 ∨ v.payout φ = 1 := by
    intro φ
    by_cases hφ : v.Holds φ
    · exact Or.inr (by simp [PCWorld.payout, hφ])
    · exact Or.inl (by simp [PCWorld.payout, hφ])
  have hterm : ∀ day,
      |(Tr.strat day).value P v.payout -
          ((Tr.freezeOn quote sel).strat day).value P' v.payout| ≤
        if day ∈ D then g day else 0 := by
    intro day
    by_cases hday : day ∈ D
    · rw [if_pos hday]
      exact (abs_sub _ _).trans (add_le_add
        (Strategy.abs_value_le_magnitude (Tr.strat day) P v.payout hw (hP day))
        (Strategy.abs_value_le_magnitude
          ((Tr.freezeOn quote sel).strat day) P' v.payout hw (hP' day)))
    · rw [if_neg hday]
      have heq := (Tr.strat day).freezeOn_value quote sel P P' v.payout hin hout
        (hD day hday)
      change |(Tr.strat day).value P v.payout -
        ((Tr.strat day).freezeOn quote sel).value P' v.payout| ≤ 0
      rw [heq]
      simp
  have hg : ∀ day, 0 ≤ g day := fun day ↦
    add_nonneg (Strategy.magnitude_nonneg _ _) (Strategy.magnitude_nonneg _ _)
  calc
    |Tr.netWorth P v n - (Tr.freezeOn quote sel).netWorth P' v n| =
        |∑ day ∈ Finset.range (n + 1),
          ((Tr.strat day).value P v.payout -
            ((Tr.freezeOn quote sel).strat day).value P' v.payout)| := by
          simp only [Trader.netWorth]
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ day ∈ Finset.range (n + 1),
          |(Tr.strat day).value P v.payout -
            ((Tr.freezeOn quote sel).strat day).value P' v.payout| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ day ∈ Finset.range (n + 1), if day ∈ D then g day else 0 :=
          Finset.sum_le_sum (fun day _ ↦ hterm day)
    _ = ∑ day ∈ (Finset.range (n + 1)).filter (fun day ↦ day ∈ D), g day := by
          rw [Finset.sum_filter]
    _ ≤ ∑ day ∈ D, g day := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro day hday
            simp only [Finset.mem_filter] at hday
            exact hday.2
          · intro day _ _
            exact hg day
    _ = Tr.freezeOnErrorBound quote sel D P P' := rfl

end Trader

/-! ### Why the error bound is not an equality

The freeze cannot transport exactly on an affected day, so every net-worth statement in this
module carries a bound rather than an equality.  The lemma below computes the residual. -/

/-- The settlement term `- V day φ` in `Strategy.value` is not syntax, so the frozen
strategy's value on an *affected* day differs from the original's by exactly
`coefficient * (P' day φ - P day φ)`.  Concretely, with a single unit trade the
discrepancy is the price gap itself. -/
lemma freezeOn_value_gap_on_selected_day
    (day : ℕ) (φ : Sentence) (P P' : History) (w : Valuation)
    (quote : ℕ → Sentence → ℚ) (sel : ℕ → Sentence → Bool)
    (T : Strategy day) (hT : T.trades = [(EF.const 1, φ)]) :
    (T.freezeOn quote sel).value P' w - T.value P w = P day φ - P' day φ := by
  simp [Strategy.value, Strategy.freezeOn, hT, EF.freezeOn, EF.denote, EF.denoteWith]

/-! ## Bounded difference preserves exploitation -/

/-- **Uniform bounded net-worth error preserves exploitation.**  If `Tr` exploits `P` and
`Tr'`'s net worth against `P'` stays within a constant `C` of `Tr`'s against `P` on every
day and every consistent world, then `Tr'` exploits `P'`.  This is the abstract
finite-prefix accounting step both directions of every closure theorem below run through. -/
lemma Trader.Exploits.of_boundedDifference
    {Tr Tr' : Trader} {P P' : History} {DP : DeductiveProcess}
    (h : Tr.Exploits P DP) (C : ℝ)
    (hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
      |Tr.netWorth P v n - Tr'.netWorth P' v n| ≤ C) :
    Tr'.Exploits P' DP := by
  rcases h with ⟨⟨L, hL⟩, hnotAbove⟩
  refine ⟨⟨L - C, ?_⟩, ?_⟩
  · rintro x ⟨n, v, hv, rfl⟩
    have hbase := hL ⟨n, v, hv, rfl⟩
    have herr := hdiff n v hv
    rw [abs_le] at herr
    linarith
  · intro hUpper
    apply hnotAbove
    rcases hUpper with ⟨U, hU⟩
    refine ⟨U + C, ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have hpatched := hU ⟨n, v, hv, rfl⟩
    have herr := hdiff n v hv
    rw [abs_le] at herr
    linarith

/-! ## The fuel-class forms

`EfficientPrefixPatch` and `FiniteSupportPatch` are the fuel-class freeze certificates, and
the two theorems below are the compatibility carriers that keep the paper's own hypothesis
shape at that class.  Both certificates are uninhabited, for the reason recorded at
`EfficientPrefixPatch`; the discharged form of the theorem is at the machine class. -/

/-- The narrowly computational boundary in finite-prefix closure: the administrative syntax
freeze above preserves token-indexed polynomial emission.  It contains no semantic market
claim and no exploitation or convergence conclusion.

**This is a paper erratum, not a modeling substitution** (see the module docstring).
`app:ifp` asserts this closure is immediate because "only finitely many constants are
needed"; that is false — finitely many *days*, but unboundedly many sentences.  This
structure is **not inhabited for every `ComputableMarket P`**: a market with huge-encoding
day-`0` quotes admits no such patch at all.  Do not read it as a routine obligation awaiting
labor; instantiating it is a real claim about `P`.

For the constructed inductor that obstruction is absent — each day's quote table is a finite
`RationalBeliefState` entry list, so the freeze is a finite lookup with constant-size tokens
— but the structure has no inhabitant there either, for the fuel-model reason recorded in
the module docstring: the escape-leaf decode the frozen lookup needs is an inverse of a
big-value operation, and the digit model is open under those (`dd:fuel`).  The token-model
content that does exist is `liaFreezeBefore_preserves_ecTok`
(`Construction/Freeze/Prefix.lean`).
Paper node: `app:ifp` -/
structure EfficientPrefixPatch (P : History) (cutoff : ℕ) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ)
  preserves_ec : ∀ Tr : Trader, EfficientlyComputable Tr →
    EfficientlyComputable (Tr.freezeBefore quote cutoff)

/-- **Closure under Finite Perturbations** (`thm:ifp`), with the computational
qualification forced by the clocked efficiency model (`dd:fuel`).  The two histories agree
from `cutoff` onward, and each supplies the efficient-freeze certificate above.  The
conclusion is the paper's biconditional, not merely one direction.
Paper node: `thm:ifp` -/
theorem lic_iff_of_finitePerturbation
    (P P' : History) (DP : DeductiveProcess) (cutoff : ℕ)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ)
    (patchP : EfficientPrefixPatch P cutoff)
    (patchP' : EfficientPrefixPatch P' cutoff) :
    IsLogicalInductor P DP ↔ IsLogicalInductor P' DP := by
  have hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1 := hPcomp.price_mem_Icc
  have hP' : ∀ day φ, 0 ≤ P' day φ ∧ P' day φ ≤ 1 := hP'comp.price_mem_Icc
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        let frozen := Tr.freezeBefore patchP'.quote cutoff
        have hfrozenEC : EfficientlyComputable frozen :=
          patchP'.preserves_ec Tr hTr
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P' v n - frozen.netWorth P v n| ≤
              Tr.freezeBeforeErrorBound patchP'.quote cutoff P' P := by
          intro n v hv
          exact Tr.freezeBefore_netWorth_difference_le patchP'.quote cutoff P' P
            patchP'.quote_exact
            (fun day hday φ ↦ (htail day hday φ).symm)
            hP' hP v n
        have hfrozenExploits : frozen.Exploits P DP :=
          hExploits.of_boundedDifference
            (Tr.freezeBeforeErrorBound patchP'.quote cutoff P' P) hdiff
        exact hLI.noExploit frozen hfrozenEC hfrozenExploits }
  · intro hLI'
    exact {
      marketComputable := hPcomp
      processComputable := hLI'.processComputable
      noExploit := by
        intro Tr hTr hExploits
        let frozen := Tr.freezeBefore patchP.quote cutoff
        have hfrozenEC : EfficientlyComputable frozen :=
          patchP.preserves_ec Tr hTr
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P v n - frozen.netWorth P' v n| ≤
              Tr.freezeBeforeErrorBound patchP.quote cutoff P P' := by
          intro n v hv
          exact Tr.freezeBefore_netWorth_difference_le patchP.quote cutoff P P'
            patchP.quote_exact htail hP hP' v n
        have hfrozenExploits : frozen.Exploits P' DP :=
          hExploits.of_boundedDifference
            (Tr.freezeBeforeErrorBound patchP.quote cutoff P P') hdiff
        exact hLI'.noExploit frozen hfrozenEC hfrozenExploits }

/-- The efficiency certificate for the **finite-support** freeze.  Unlike
`EfficientPrefixPatch`, the quote table here is genuinely finite: `quote` is only read at
the finitely many coordinates in `S`, so the paper's "hard-code the constants" step is
literally valid.  It is nevertheless **uninhabited**, for the same fuel-model reason as
`EfficientPrefixPatch`: the digit model is open under the escape-leaf decode the lookup
needs (`dd:fuel`).  Its machine counterpart `MachineFiniteSupportPatch` *is* inhabited; see
there.
Paper node: `app:ifp` -/
structure FiniteSupportPatch (P : History) (S : Finset (ℕ × Sentence)) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ d φ, (d, φ) ∈ S → P d φ = (quote d φ : ℝ)
  preserves_ec : ∀ Tr : Trader, EfficientlyComputable Tr →
    EfficientlyComputable (Tr.freezeOn quote (fun d φ => decide ((d, φ) ∈ S)))

/-- **Closure under finite-support perturbations** — the *corrected* `thm:ifp`, at the
fuel class.

**This is not the paper's `thm:ifp`.**  Its hypothesis is **strictly stronger**: finite
support of the price difference implies the paper's tail agreement
(`FiniteSupportPerturbation.tail_agree`) and is not implied by it — the day-`0`
huge-numeral market in the module docstring agrees with the constructed inductor's market
from day `1` and is not finitely supported.  What this repairs is the appendix's efficiency
step, which is valid exactly when the constant table is finite: `quote` is read only at the
finitely many coordinates in `S`, so "hard-code the constants" is literally true here and
false in general.  `lic_iff_of_finitePerturbation` above keeps the paper's own hypothesis
shape, as a compatibility carrier; neither theorem reaches the unrestricted node, which is
refuted rather than open.

Kind `C`; hypotheses `(a)` except `preserves_ec`, which is the appendix's own obligation.
Paper node: `thm:ifp` -/
theorem lic_iff_of_finiteSupportPerturbation
    (P P' : History) (DP : DeductiveProcess) (S : Finset (ℕ × Sentence))
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ)
    (patchP : FiniteSupportPatch P S) (patchP' : FiniteSupportPatch P' S) :
    IsLogicalInductor P DP ↔ IsLogicalInductor P' DP := by
  classical
  have hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1 := hPcomp.price_mem_Icc
  have hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1 := hP'comp.price_mem_Icc
  set sel : ℕ → Sentence → Bool := fun d φ => decide ((d, φ) ∈ S) with hsel
  have hselF : ∀ d φ, sel d φ = false ↔ (d, φ) ∉ S := by
    intro d φ; simp [hsel]
  have hselT : ∀ d φ, sel d φ = true ↔ (d, φ) ∈ S := by
    intro d φ; simp [hsel]
  set D : Finset ℕ := Trader.freezeDays S with hD
  have hDays : ∀ d, d ∉ D → ∀ φ, sel d φ = false := by
    intro d hd φ
    rw [hselF]
    intro hmem
    refine hd ?_
    rw [hD, Trader.freezeDays, Finset.mem_image]
    exact ⟨(d, φ), hmem, rfl⟩
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P' v n - (Tr.freezeOn patchP'.quote sel).netWorth P v n| ≤
              Tr.freezeOnErrorBound patchP'.quote sel D P' P := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP'.quote sel D P' P
            (fun d φ h => patchP'.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => (hagree d φ ((hselF d φ).1 h)).symm)
            hDays hP' hP v n
        exact hLI.noExploit _ (patchP'.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }
  · intro hLI'
    exact {
      marketComputable := hPcomp
      processComputable := hLI'.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P v n - (Tr.freezeOn patchP.quote sel).netWorth P' v n| ≤
              Tr.freezeOnErrorBound patchP.quote sel D P P' := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP.quote sel D P P'
            (fun d φ h => patchP.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => hagree d φ ((hselF d φ).1 h))
            hDays hP hP' v n
        exact hLI'.noExploit _ (patchP.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }

/-! ## The finite-support hypothesis and its separation from tail agreement -/

/-- `P` and `P'` differ on only finitely many `(day, sentence)` price coordinates. -/
def FiniteSupportPerturbation (P P' : History) : Prop :=
  ∃ S : Finset (ℕ × Sentence), ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ

/-- Finite support is *strictly stronger* than the paper's tail-agreement hypothesis.

Half of the separation that keeps the corrected `thm:ifp` honest; the other half, that the
converse fails, is `tailAgree_not_finiteSupport` below.

Proof kind: `P` proved.  Provenance: (b) `Finset.le_sup`.
Paper node: `app:ifp` -/
lemma FiniteSupportPerturbation.tail_agree {P P' : History}
    (h : FiniteSupportPerturbation P P') :
    ∃ N : ℕ, ∀ d, N ≤ d → ∀ φ, P d φ = P' d φ := by
  obtain ⟨S, hS⟩ := h
  refine ⟨(S.image Prod.fst).sup id + 1, ?_⟩
  intro d hd φ
  refine hS d φ (fun hmem => ?_)
  have : d ≤ (S.image Prod.fst).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image.2 ⟨(d, φ), hmem, rfl⟩)
  omega

/-- **And it is *strictly* stronger: the converse fails.**  Two markets can agree from day
one onward and still differ at infinitely many `(day, sentence)` coordinates — a single
rewritten pricing row already does it, because a day's fibre is infinite.

This is the separation that keeps the corrected `thm:ifp` honest.  The published theorem
hypothesises *eventual day agreement*; that statement is refuted by
`FinitePerturbationCounterexample.not_overgeneral_ifp`.  What is proved instead assumes
finite **coordinate** support, and the implication runs one way only:

```
finite coordinate support  ⇒  eventual day agreement   (tail_agree)
eventual day agreement     ⇏  finite coordinate support (this lemma)
```

So the corrected theorem cannot accidentally re-derive the false one.  It also locates
exactly where the paper's own "only finitely many constants are needed, and can be
hard-coded" argument becomes valid: under finite coordinate support the frozen table really
is a finite list of `(day, sentence, price)` rows, whereas under mere day agreement the
rewritten row carries infinitely many prices and no such table exists.

Proof kind: `N-` negative witness.  Provenance: (a) `Infinite.exists_notMem_finset`;
(b) `LO.Propositional.Formula.atom` injective.
Paper node: `app:ifp` -/
lemma tailAgree_not_finiteSupport :
    ∃ P P' : History, (∀ d, 1 ≤ d → ∀ φ, P d φ = P' d φ) ∧
      ¬ FiniteSupportPerturbation P P' := by
  classical
  haveI : Infinite Sentence :=
    Infinite.of_injective (LO.Propositional.Formula.atom (α := ℕ))
      (fun _ _ h => LO.Propositional.Formula.atom.inj h)
  refine ⟨fun _ _ => 0, fun d _ => if d = 0 then 1 else 0, ?_, ?_⟩
  · intro d hd _
    show (0 : ℝ) = if d = 0 then 1 else 0
    rw [if_neg (by omega)]
  · rintro ⟨S, hS⟩
    obtain ⟨φ, hφ⟩ := Infinite.exists_notMem_finset (S.image Prod.snd)
    have hmem : (0, φ) ∉ S := fun hc => hφ (Finset.mem_image.mpr ⟨(0, φ), hc, rfl⟩)
    have h0 := hS 0 φ hmem
    simp at h0

/-! ## The corrected theorem at the machine class -/

/-- The machine-class efficiency certificate for the finite-support freeze.  This is the
version whose obligation is dischargeable: `Nat.unpair` is polynomial time, so the
escape-leaf decode that blocks the fuel model is available here.

**This structure is implementation machinery, not a hypothesis.**  It is inhabited —
unlike the fuel-class `EfficientPrefixPatch` and `FiniteSupportPatch` — and it is inhabited
*without a caller-supplied witness*: `FreezeOracle.machineFiniteSupportPatch` compiles one
from the market's own `ComputableMarket` certificate and the coordinate set alone, with
`FreezeOracle.machineFiniteSupportPatch_ofRecognizable` the narrower constructor that also
takes a syntactic recognizability hypothesis on the moved sentences.  So the public
corrected theorem does not mention this structure.  Read it as the compiler's interface, and
`FreezeOracle.machine_lic_iff_of_finiteSupport` as the statement: that theorem asks for
finite `(day, sentence)` support and computability of both markets, and carries no condition
on the moved sentences.

Non-vacuity and content: `FreezeOracle.machine_lic_iff_twoPoint` exhibits a concrete pair of
genuinely different computable markets, so the antecedent is satisfiable, and
`LIAPerturbation.machineLogicalInductor_liaPerturbed` derives that a one-price perturbation
of the constructed inductor is still an inductor — which no other result here gives.

`machineFiniteSupportPatch_of_rewriter` below reduces the certificate to one named
`Complexity.FP` fact, `FreezeStreamRewriter`, which `FreezeOracle` then discharges from a
`RunOracle`.
Paper node: `app:ifp` -/
structure MachineFiniteSupportPatch (P : History) (S : Finset (ℕ × Sentence)) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ d φ, (d, φ) ∈ S → P d φ = (quote d φ : ℝ)
  preserves_ec : ∀ Tr : Trader, MachineEfficientTrader Tr →
    MachineEfficientTrader (Tr.freezeOn quote (fun d φ => decide ((d, φ) ∈ S)))

/-! ### The efficiency step, isolated

`FreezeStreamRewriter` isolates the one `Complexity.FP` fact the machine-class patch turns
on: exhibit the freeze transducer as a polynomial-time rewrite of the machine's own output
word.  It is deliberately phrased over the **contracted** stream `unRpn` reads, because that
is the granularity `strategyOfTokens` parses.

It is not a hypothesis of anything public.  `RpnFreeze.freezeStreamRewriter_of_flatPass`
carries it to the *flat* stream — the one a machine actually holds — and
`FreezeStep.freezeStreamRewriter_of_runOracle` discharges it from the run-level lookup,
which `FreezeOracle.runOracleOf` supplies for any finite table.  It is the seam between the
economic argument and the compiler, which is why it is named rather than inlined. -/

/-- **The `Complexity.FP` step the machine-class patch turns on.**  Every polynomial-time
output word can be rewritten, in polynomial time, into one whose contracted token stream is
the freeze transducer's output on the original's.

Discharged by `FreezeStep.freezeStreamRewriter_of_runOracle`. -/
def FreezeStreamRewriter (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ) : Prop :=
  ∀ F : List Bool → List Bool, F ∈ Complexity.FP →
    ∃ G : List Bool → List Bool, G ∈ Complexity.FP ∧ ∀ x : List Bool,
      unRpn (undigitize (bitsToDigits (G x)))
        = (EF.freezeTokenRunOn selCode quoteCode (0, 0)
            (unRpn (undigitize (bitsToDigits (F x))))).2

/-- **The freeze preserves machine efficiency, given the stream rewriter.**  This is the
whole of `preserves_ec` except the `FP` fact: the token model transports the decoded
strategy (`EF.strategyOfTokens_freezeTokenRunOn_trades`), `Strategy.ext` upgrades the trade
list to the strategy, and `Trader.freezeOn` is that strategy-wise.

Kind `C`; hypotheses `(a)` except `hrewrite`, which is the named obligation above.
Paper node: `app:ifp` -/
lemma MachineEfficientTrader.freezeOn
    {quote : ℕ → Sentence → ℚ} {sel : ℕ → Sentence → Bool}
    {selCode : ℕ → ℕ → Bool} {quoteCode : ℕ → ℕ → ℕ}
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = sel day φ)
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (hrewrite : FreezeStreamRewriter selCode quoteCode)
    {Tr : Trader} (hTr : MachineEfficientTrader Tr) :
    MachineEfficientTrader (Tr.freezeOn quote sel) := by
  obtain ⟨F, hF, hFspec⟩ := hTr
  obtain ⟨G, hG, hGspec⟩ := hrewrite F hF
  refine ⟨G, hG, fun n => ?_⟩
  apply Strategy.ext
  have htok := EF.strategyOfTokens_freezeTokenRunOn_trades quote sel selCode quoteCode n
    hsel hquote (unRpn (undigitize (bitsToDigits (F (unaryDay n)))))
  simp only at htok
  have hFtok : strategyOfTokens n (unRpn (undigitize (bitsToDigits (F (unaryDay n)))))
      = Tr.strat n := hFspec n
  show (strategyOfTokens n (unRpn (undigitize (bitsToDigits (G (unaryDay n)))))).trades = _
  rw [hGspec (unaryDay n), htok, hFtok]
  rfl

/-- **The machine-class patch, reduced to the stream rewriter.**  Given the finite quote
table, its code-level presentation, and the one `FP` fact, the patch exists.  Nothing here
assumes anything about the market beyond `quote_exact`.

Kind `C`; hypotheses `(a)` except `hrewrite`.
Paper node: `app:ifp` -/
def machineFiniteSupportPatch_of_rewriter
    (P : History) (S : Finset (ℕ × Sentence)) (quote : ℕ → Sentence → ℚ)
    (hexact : ∀ d φ, (d, φ) ∈ S → P d φ = (quote d φ : ℝ))
    (selCode : ℕ → ℕ → Bool) (quoteCode : ℕ → ℕ → ℕ)
    (hsel : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      selCode day code = decide ((day, φ) ∈ S))
    (hquote : ∀ day code φ, Encodable.decode (α := Sentence) code = some φ →
      quoteCode day code = Encodable.encode (quote day φ))
    (hrewrite : FreezeStreamRewriter selCode quoteCode) :
    MachineFiniteSupportPatch P S where
  quote := quote
  quote_exact := hexact
  preserves_ec := fun _ hTr =>
    MachineEfficientTrader.freezeOn hsel hquote hrewrite hTr

/-- **Closure under finite-support perturbations, at the paper's own quantifier.**  The
same corrected statement as `lic_iff_of_finiteSupportPerturbation`, over
`MachineEfficientTrader` rather than the fuel-certified class, and it is the primary one:
the whole economic argument is class-agnostic, so only the freeze certificate changes.
Read that theorem's docstring for what "corrected" means here — the hypothesis is strictly
stronger than the paper's, and this is not the unrestricted `thm:ifp`.

Kind `C`; hypotheses `(a)` except `preserves_ec`.
Paper node: `thm:ifp` -/
theorem machine_lic_iff_of_finiteSupportPerturbation
    (P P' : History) (DP : DeductiveProcess) (S : Finset (ℕ × Sentence))
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hagree : ∀ d φ, (d, φ) ∉ S → P d φ = P' d φ)
    (patchP : MachineFiniteSupportPatch P S) (patchP' : MachineFiniteSupportPatch P' S) :
    IsMachineLogicalInductor P DP ↔ IsMachineLogicalInductor P' DP := by
  classical
  have hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1 := hPcomp.price_mem_Icc
  have hP' : ∀ d φ, 0 ≤ P' d φ ∧ P' d φ ≤ 1 := hP'comp.price_mem_Icc
  set sel : ℕ → Sentence → Bool := fun d φ => decide ((d, φ) ∈ S) with hsel
  have hselF : ∀ d φ, sel d φ = false ↔ (d, φ) ∉ S := by intro d φ; simp [hsel]
  have hselT : ∀ d φ, sel d φ = true ↔ (d, φ) ∈ S := by intro d φ; simp [hsel]
  set D : Finset ℕ := Trader.freezeDays S with hD
  have hDays : ∀ d, d ∉ D → ∀ φ, sel d φ = false := by
    intro d hd φ
    rw [hselF]
    intro hmem
    refine hd ?_
    rw [hD, Trader.freezeDays, Finset.mem_image]
    exact ⟨(d, φ), hmem, rfl⟩
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P' v n - (Tr.freezeOn patchP'.quote sel).netWorth P v n| ≤
              Tr.freezeOnErrorBound patchP'.quote sel D P' P := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP'.quote sel D P' P
            (fun d φ h => patchP'.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => (hagree d φ ((hselF d φ).1 h)).symm)
            hDays hP' hP v n
        exact hLI.noExploit _ (patchP'.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }
  · intro hLI'
    exact {
      marketComputable := hPcomp
      processComputable := hLI'.processComputable
      noExploit := by
        intro Tr hTr hExploits
        have hdiff : ∀ n v, v.ConsistentWith (DP.D n) →
            |Tr.netWorth P v n - (Tr.freezeOn patchP.quote sel).netWorth P' v n| ≤
              Tr.freezeOnErrorBound patchP.quote sel D P P' := by
          intro n v _
          exact Tr.freezeOn_netWorth_difference_le patchP.quote sel D P P'
            (fun d φ h => patchP.quote_exact d φ ((hselT d φ).1 h))
            (fun d φ h => hagree d φ ((hselF d φ).1 h))
            hDays hP hP' v n
        exact hLI'.noExploit _ (patchP.preserves_ec Tr hTr)
          (hExploits.of_boundedDifference _ hdiff) }

end LogicalInduction
