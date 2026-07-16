/-
# Closure under finite perturbations (`thm:ifp`)

The paper transports an exploiting trader across a finite change of market history by
replacing every old price leaf in its feature syntax with the corresponding rational
constant.  This file makes that transformation literal and proves its rank, semantic,
net-worth, and exploitation laws.

## PAPER ERRATUM — the appendix proof of `thm:ifp` has a gap (see PROGRESS.md "Paper errata")

This is **not** a modeling artifact of our substrate.  The paper's proof (`app:ifp`)
transports the trader by hard-coding the old prices, and justifies efficiency thus:

> "Note that `F` is efficiently computable: by the assumption that `pt_n = pt'_n` for all
> `n ≥ N`, only finitely many constants `pt_i(phi)` are needed, and can be hard-coded
> into `F`."

That sentence is false.  Finitely many *days* `i < N` are involved, but `phi` still ranges
over **all** sentences: a day-`n` trade expression may reference `phi^{*i}` for any `phi` of
rank `≤ n`, so the constant set `{pt_i(phi) : i < N, phi ∈ Sentences}` is infinite.  `F`
must therefore *compute* `pt_i(phi)` rather than hard-code it, and `def:marketprocess`
(a market is any computable sequence of pricings — no finite support, no time bound)
guarantees only that this is computable, with no bound on its runtime or on the bit-size of
the resulting rational.  So `F` is not efficiently computable in general, and the paper's
proof does not go through for the class of markets it quantifies over.

The gap is real, not merely pedantic.  Let `P'` agree with `LIA` from day 1 on, with
`P' 0 phi = 1 - 1/2^(2^(encode phi))` — a legal market by `def:marketprocess`.  A trader
whose day-`n` strategy prices a sentence of code `~n` at day 0 freezes to a `.const` whose
numeral is `~2^(2^n)`, which no polynomial clock can emit.  For such a `P'`,
`EfficientPrefixPatch P' 1` is **uninhabited** — the hypothesis is not merely unproved but
unsatisfiable.  (This argument is *not* formalized; see the "Paper errata" entry for the
one unformalized fact it rests on, and for what remains open.)

Note the paper is aware `LIA` itself has finite support per day (`sec:construct`, remark
following the belief-sequence definition) and *deliberately* generalizes the property tail
to arbitrary markets.  Finite support is exactly what would rescue the hard-coding step, so
the gap is a genuine cost of that generalization, not an oversight about `LIA`.

**What this file does about it.**  We keep the theorem to what is actually provable:
`EfficientPrefixPatch` states the missing closure fact for the concrete syntax
transformation, and `lic_iff_of_finitePerturbation` takes it as a hypothesis for each
market.  The structure contains no trading, exploitation, or logical-inductor conclusion.
Consequently `lic_iff_of_finitePerturbation` is **strictly weaker than the paper's
`thm:ifp`**: it does not cover every finite perturbation of a computable market, only those
whose frozen prefix admits an efficient presentation.  It is not vacuous — for `LIA` the
per-day quote table is a finite entry list (`RationalBeliefState`, `MarketMaker.lean`), so
the patch is a hardcodable finite lookup and `M7-PREFIX-PATCH` can discharge it — but the
restriction must be stated whenever this theorem is cited as the paper's.
-/
import LogicalInduction.Engine
import LogicalInduction.Computable

namespace LogicalInduction

open scoped BigOperators

namespace EF

/-- Replace every price leaf strictly before `cutoff` by its exact rational quote. -/
def freezeBefore (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) : EF → EF
  | .price φ day => if day < cutoff then .const (quote day φ) else .price φ day
  | .const q => .const q
  | .add a b => .add (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff)
  | .mul a b => .mul (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff)
  | .max a b => .max (a.freezeBefore quote cutoff) (b.freezeBefore quote cutoff)
  | .safeRecip a => .safeRecip (a.freezeBefore quote cutoff)
  | .var i => .var i
  | .letE value body =>
      .letE (value.freezeBefore quote cutoff) (body.freezeBefore quote cutoff)

/-- Freezing old leaves never increases the feature's information horizon. -/
theorem freezeBefore_rank_le (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).rank ≤ e.rank := by
  induction e with
  | price φ day =>
      simp only [freezeBefore]
      split <;> simp
  | const q => simp [freezeBefore]
  | add a b iha ihb => simpa [freezeBefore] using max_le_max iha ihb
  | mul a b iha ihb => simpa [freezeBefore] using max_le_max iha ihb
  | max a b iha ihb => simpa [freezeBefore] using max_le_max iha ihb
  | safeRecip a iha => simpa [freezeBefore] using iha
  | var i => simp [freezeBefore]
  | letE value body ihv ihb => simpa [freezeBefore] using max_le_max ihv ihb

/-- The syntax transformation is size-preserving at the structural-node level. -/
@[simp] theorem freezeBefore_cost (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) :
    (e.freezeBefore quote cutoff).cost = e.cost := by
  induction e with
  | price φ day => simp only [freezeBefore]; split <;> rfl
  | const q => rfl
  | add a b iha ihb => simp only [freezeBefore, cost, iha, ihb]
  | mul a b iha ihb => simp only [freezeBefore, cost, iha, ihb]
  | max a b iha ihb => simp only [freezeBefore, cost, iha, ihb]
  | safeRecip a iha => simp only [freezeBefore, cost, iha]
  | var i => rfl
  | letE value body ihv ihb => simp only [freezeBefore, cost, ihv, ihb]

/-- If `quote` is the old prefix of `P` and `P'` agrees with `P` after the cutoff,
the frozen feature sees exactly what the original feature saw against `P`. -/
theorem freezeBefore_denoteWith
    (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History)
    (hprefix : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ))
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ) :
    ∀ ρ : List ℝ,
      (e.freezeBefore quote cutoff).denoteWith ρ P' = e.denoteWith ρ P := by
  induction e with
  | price φ day =>
      intro ρ
      simp only [freezeBefore]
      by_cases hday : day < cutoff
      · simp [hday, hprefix day hday φ]
      · simp [hday, htail day (Nat.le_of_not_gt hday) φ]
  | const q => intro ρ; rfl
  | add a b iha ihb => intro ρ; simp [freezeBefore, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [freezeBefore, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [freezeBefore, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [freezeBefore, iha ρ]
  | var i => intro ρ; rfl
  | letE value body ihv ihb =>
      intro ρ
      simp only [freezeBefore, denoteWith_letE]
      rw [ihv ρ, ihb]

theorem freezeBefore_denote
    (e : EF) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (P P' : History)
    (hprefix : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ))
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ) :
    (e.freezeBefore quote cutoff).denote P' = e.denote P := by
  exact e.freezeBefore_denoteWith quote cutoff P P' hprefix htail []

end EF

namespace Strategy

/-- Apply the old-price freeze to every coefficient of a strategy. -/
def freezeBefore {day : ℕ} (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (T : Strategy day) : Strategy day where
  trades := T.trades.map fun p => (p.1.freezeBefore quote cutoff, p.2)
  rank_le := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (q.1.freezeBefore_rank_le quote cutoff).trans (T.rank_le q hq)

/-- On an unchanged tail day, a frozen strategy against `P'` has exactly the value of the
original strategy against `P`. -/
theorem freezeBefore_value
    {day : ℕ} (T : Strategy day) (quote : ℕ → Sentence → ℚ) (cutoff : ℕ)
    (P P' : History) (w : Valuation)
    (hprefix : ∀ d < cutoff, ∀ φ, P d φ = (quote d φ : ℝ))
    (htail : ∀ d, cutoff ≤ d → ∀ φ, P d φ = P' d φ)
    (hday : cutoff ≤ day) :
    (T.freezeBefore quote cutoff).value P' w = T.value P w := by
  simp only [Strategy.value, freezeBefore, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply]
  rw [p.1.freezeBefore_denote quote cutoff P P' hprefix htail]
  rw [← htail day hday p.2]

end Strategy

namespace Trader

/-- The paper's false-report trader: coefficients see the frozen old prefix. -/
def freezeBefore (quote : ℕ → Sentence → ℚ) (cutoff : ℕ) (Tr : Trader) : Trader where
  strat day := (Tr.strat day).freezeBefore quote cutoff

theorem freezeBefore_value_tail
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
theorem freezeBefore_netWorth_difference_le
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

end Trader

/-- Uniform bounded net-worth error preserves exploitation.  This is the abstract finite-
prefix accounting step used in both directions of `thm:ifp`. -/
theorem Trader.Exploits.of_boundedDifference
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

/-- The narrowly computational boundary in finite-prefix closure: the literal syntax
freeze above preserves token-indexed polynomial emission.  It contains no semantic market
claim and no exploitation or convergence conclusion.

**This is a paper erratum, not a modeling substitution** (see the file header and
PROGRESS.md "Paper errata").  `app:ifp` asserts this closure is immediate because "only
finitely many constants are needed"; that is false — finitely many *days*, but unboundedly
many sentences.  This structure is **not inhabited for every `ComputableMarket P`**: a
market with huge-encoding day-`0` quotes admits no such patch at all.  Do not read it as a
routine obligation awaiting labor; instantiating it is a real claim about `P`.

For `LIA` it *is* inhabitable — each day's quote table is a finite `RationalBeliefState`
entry list, so the freeze is a hardcodable finite lookup with constant-size tokens.  That
is `M7-PREFIX-PATCH`. -/
structure EfficientPrefixPatch (P : History) (cutoff : ℕ) where
  quote : ℕ → Sentence → ℚ
  quote_exact : ∀ day < cutoff, ∀ φ, P day φ = (quote day φ : ℝ)
  preserves_ec : ∀ Tr : Trader, EfficientlyComputableTok Tr →
    EfficientlyComputableTok (Tr.freezeBefore quote cutoff)

/-- **Closure under Finite Perturbations** (`thm:ifp`), with the exact computational
qualification forced by this repository's clocked model.  The two histories agree from
`cutoff` onward, and each finite prefix supplies the concrete efficient-freeze certificate
above.  The conclusion is the paper's biconditional, not merely one direction. -/
theorem lic_iff_of_finitePerturbation
    (P P' : History) (DP : DeductiveProcess) (cutoff : ℕ)
    (hPcomp : ComputableMarket P) (hP'comp : ComputableMarket P')
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1)
    (hP' : ∀ day φ, 0 ≤ P' day φ ∧ P' day φ ≤ 1)
    (htail : ∀ day, cutoff ≤ day → ∀ φ, P day φ = P' day φ)
    (patchP : EfficientPrefixPatch P cutoff)
    (patchP' : EfficientPrefixPatch P' cutoff) :
    IsLogicalInductor P DP ↔ IsLogicalInductor P' DP := by
  constructor
  · intro hLI
    exact {
      marketComputable := hP'comp
      processComputable := hLI.processComputable
      noExploit := by
        intro Tr hTr hExploits
        let frozen := Tr.freezeBefore patchP'.quote cutoff
        have hfrozenEC : EfficientlyComputableTok frozen :=
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
        have hfrozenEC : EfficientlyComputableTok frozen :=
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

end LogicalInduction

#print axioms LogicalInduction.EF.freezeBefore_denote
#print axioms LogicalInduction.Strategy.freezeBefore_value
#print axioms LogicalInduction.Trader.freezeBefore_netWorth_difference_le
#print axioms LogicalInduction.Trader.Exploits.of_boundedDifference
#print axioms LogicalInduction.lic_iff_of_finitePerturbation
