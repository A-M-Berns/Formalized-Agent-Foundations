/-
# Affine Provability Induction (§4.5, `thm:affprovind`, `app:affprovind`)

The affine analogue of provability induction, stated semantically: if every sufficiently
late plausible world values a polynomially generated affine bundle at least `c`, then the
bundle's diagonal market price cannot stay below `c`. `affine_tendsto_zero` is the
two-sided form obtained by applying it to the family and its negation.
-/
import LogicalInduction.Properties.AffinePreemptiveLearning
import LogicalInduction.Framework.WriteOut

namespace LogicalInduction

open Filter Topology

namespace AffineCombination

/-- Buy the day-`n` affine bundle with a continuous coefficient which is zero before
`start`, one below `low`, and ramps to zero by `low + δ`. -/
noncomputable def PolySequence.buyBelowTrader {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) : Trader where
  strat n :=
    let entry := gateFeature start (gradualEntry As low δ) n
    (As n).scale entry |>.buy n
      ((As n).scale_terms_rank_le entry (by
        by_cases hs : start ≤ n
        · simpa [entry, gateFeature, hs] using h.gradualEntry_rank_le low δ n
        · simp [entry, gateFeature, hs]) (h.terms_rank n))

lemma PolySequence.buyBelowTrader_trades {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (n : ℕ) :
    ((h.buyBelowTrader start low δ).strat n).trades =
      (List.range (h.termCount n)).map (fun j =>
        (EF.mul (gateFeature start (gradualEntry As low δ) n)
          (h.coefficient (Nat.pair n j)), h.sentence (Nat.pair n j))) := by
  rw [PolySequence.buyBelowTrader, AffineCombination.buy_trades,
    AffineCombination.scale, h.terms_eq]
  simp [List.map_map, Function.comp_def]

lemma PolySequence.buyBelowTrader_ec {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) :
    EfficientlyComputable (h.buyBelowTrader start low δ) := by
  have hentry : BigSpliceStream (fun n =>
      (gateFeature start (gradualEntry As low δ) n).serialize) :=
    BigSpliceStream.gateFeature (h.gradualEntry_polySeg low δ) start
  have hcoeff : BigSpliceStream (fun z =>
      (EF.mul (gateFeature start (gradualEntry As low δ) z.unpair.1)
        (h.coefficient z)).serialize) :=
    BigSpliceStream.serialize_mul (hentry.comp PolyFueled.left) h.coefficient_poly
  have hframe := BigSpliceStream.tradeSlot h.sentence_poly PolyFueled.id
  have hone : BigSpliceStream (fun z => serializeTrades
      [(EF.mul (gateFeature start (gradualEntry As low δ) z.unpair.1)
          (h.coefficient z), h.sentence z)]) := by
    refine BigSpliceStream.of_eq (hcoeff.append hframe) ?_
    intro z
    simp [serializeTrades]
  refine BigSpliceStream.ec _ (BigSpliceStream.of_eq
    (BigSpliceStream.concatVar hone (Classical.choose_spec h.termCount_poly)) ?_)
  intro n
  rw [h.buyBelowTrader_trades start low δ, serializeTrades_map_singleton]
  simp only [Nat.unpair_pair]

lemma PolySequence.buyBelowTrader_value {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (V : History)
    (w : Valuation) (n : ℕ) :
    ((h.buyBelowTrader start low δ).strat n).value V w =
      (gateFeature start (gradualEntry As low δ) n).denote V *
        ((As n).value V w - (As n).price V n) := by
  rw [PolySequence.buyBelowTrader, AffineCombination.buy_value,
    AffineCombination.scale_value, AffineCombination.scale_price]
  ring

/-- **Affine Provability Induction.**  An eventually uniform plausible-world lower bound
on a normalized polynomial affine family is learned on the diagonal. -/
lemma PolySequence.affine_provind {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      c ≤ (As n).value P v.payout) :
    AsympGE (fun n => (As n).price P n) (fun _ => c) := by
  intro ε hε
  obtain ⟨start, hstart⟩ := Filter.eventually_atTop.mp hval
  obtain ⟨low, hlowL, hlowU⟩ := exists_rat_btwn (show c - ε < c - ε / 2 by linarith)
  obtain ⟨δ, hδ0, hδU⟩ := exists_rat_btwn (show (0 : ℝ) < c - (low : ℝ) by linarith)
  have hδ : 0 < (δ : ℝ) := hδ0
  have hsafe : (low : ℝ) + δ < c := by linarith
  by_contra hbad
  rw [not_eventually] at hbad
  have hfreq : ∃ᶠ n in atTop, (As n).price P n + ε < c := by
    simpa only [not_le] using hbad
  let entry : ℕ → EF := fun n => gateFeature start (gradualEntry As low δ) n
  let w : ℕ → ℝ := fun n => (entry n).denote P * (c - (As n).price P n)
  have hnonneg : ∀ n, 0 ≤ w n := by
    intro n
    by_cases hs : start ≤ n
    swap
    · simp [w, entry, gateFeature, hs]
    have he0 := (buyIndF_mem ((As n).priceFeature n) low δ P).1
    by_cases he : (entry n).denote P = 0
    · simp [w, he]
    have hepos : 0 < (entry n).denote P := lt_of_le_of_ne (by
      simpa [entry, gateFeature, hs, gradualEntry] using he0) (Ne.symm he)
    have hp := buyIndF_pos_imp hδ (by
      simpa [entry, gateFeature, hs, gradualEntry] using hepos)
    rw [(As n).priceFeature_denote] at hp
    exact mul_nonneg hepos.le (by linarith)
  have hfreqW : ∃ᶠ n in atTop, ε ≤ w n := by
    refine (hfreq.and_eventually (Filter.eventually_ge_atTop start)).mono ?_
    intro n hn
    have hs : start ≤ n := hn.2
    have hone : (entry n).denote P = 1 := by
      simp only [entry, gateFeature, hs, if_true, gradualEntry]
      apply buyIndF_eq_one hδ
      rw [(As n).priceFeature_denote]
      linarith [hn.1]
    simp only [w, hone, one_mul]
    linarith [hn.1]
  have hnet : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∑ i ∈ Finset.range (n + 1), w i ≤
        (h.buyBelowTrader start low δ).netWorth P v n := by
    intro n v hv
    rw [Trader.netWorth]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases his : start ≤ i
    swap
    · simp [w, entry, gateFeature, his, h.buyBelowTrader_value]
    have hsub : DP.D i ⊆ DP.D n := Finset.le_iff_subset.mp
      (monotone_nat_of_le_succ (fun k => Finset.le_iff_subset.mpr (DP.mono k)) hin)
    have hv' : v.ConsistentWith (DP.D i) := fun φ hφ => hv φ (hsub hφ)
    have hvi := hstart i his v hv'
    rw [h.buyBelowTrader_value]
    dsimp only [w, entry]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hvi _) (by
      simpa [gateFeature, his, gradualEntry] using
        (buyIndF_mem ((As i).priceFeature i) low δ P).1)
  exact hLI.noExploit _ (h.buyBelowTrader_ec start low δ)
    (exploits_of_ge_partialSums _ P DP w ε hε hnonneg hnet hfreqW hcons)

/-- Two-sided affine provability: if every late plausible world values the family
uniformly near zero, then its diagonal market price converges to zero. -/
lemma PolySequence.affine_tendsto_zero {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) → |(As n).value P v.payout| ≤ ε) :
    AsympEq (fun n => (As n).price P n) (fun _ => 0) := by
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  have hnear := hval (ε / 4) (by linarith)
  have hloSem : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      -ε / 4 ≤ (As n).value P v.payout := hnear.mono (fun n hn v hv => by
    have := hn v hv
    rw [abs_le] at this
    linarith)
  have hhiSem : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      -ε / 4 ≤ ((As n).neg).value P v.payout := hnear.mono (fun n hn v hv => by
    have := hn v hv
    rw [abs_le] at this
    rw [neg_value]
    linarith)
  have hlo := h.affine_provind P DP hcons (-ε / 4) hloSem (ε / 4) (by linarith)
  have hhi := h.neg.affine_provind P DP hcons (-ε / 4) hhiSem (ε / 4) (by linarith)
  filter_upwards [hlo, hhi] with n hnlo hnhi
  rw [neg_price] at hnhi
  simp only [sub_zero]
  rw [abs_le]
  constructor <;> linarith

end AffineCombination

end LogicalInduction
