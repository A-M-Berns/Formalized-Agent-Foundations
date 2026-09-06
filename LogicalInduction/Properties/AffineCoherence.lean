import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Properties.TimelyLearning
import LogicalInduction.Framework.BooleanWorlds
import LogicalInduction.Framework.Emission.WriteOut

/-!
# Affine Coherence

Renders §4.5: `thm:affcoh` (Affine Coherence, appendix `app:affcoh`), all three comparison
forms of `thm:affprovind`, and the sentence-level `thm:provind` of §4.2 as the one-share
special case of the affine equality form.

The Boolean-world toolkit and the compactness bridge it carries —
`eventually_affineValue_gt_of_theory`, which pulls a bound holding in every completed-theory
world back to a uniform bound from some finite stage on — are
`Framework/BooleanWorlds.lean`. The completed-theory value set is `completedAffineValues`,
with extrema `completedAffineLow` / `completedAffineHigh` and their uniform filter bounds.

The semantic engine is `PolySequence.affine_provind` (`app:affprovind`): if every
sufficiently late plausible world values a polynomially generated affine bundle at least `c`,
the bundle's diagonal market price cannot stay below `c`.  Its trader
`PolySequence.buyBelowTrader` buys the day-`n` bundle with a continuous coefficient that is
zero before `start`, one below `low`, and ramps to zero by `low + δ` — the entry gate
`gateFeature` and the buy signal `gradualEntry` of `AffinePreemptiveLearning.lean` — and is
certified in the write-out class through `BigSpliceStream`, one trade slot per bundle term.
`PolySequence.affine_tendsto_zero` is the two-sided form, obtained by applying
`affine_provind` to the family and to its negation; `ExpectationAffine.lean` reaches both for
the expectation analogues.

`PolySequence.eventualMember` is the legal fixed-portfolio progression: a polynomial affine
sequence can uniformly emit any one of its members forever after that member's own index.
It carries the first half of affine coherence. The two pointwise bridges
`completedTheoryLow_le_limitingValue` and `limitingValue_le_completedTheoryHigh` — the
latter by applying the former to the negated family — assemble into `PolySequence.affcoh`.

`affine_provind_theory_ge` / `_le` / `_eq` are `thm:affprovind`. The vanishing-error
variants `_tendsto_zero`, `_le_const` and `_ge_const` are what quoted `[0,1]` values and
the `dd:mesh` slack need, since a finite threshold sum approximates its real value only
within `O(1/n)`.

`lic_provind_true` / `lic_provind_false` / `lic_provind` are the paper-facing
`thm:provind`: efficient theorem and disprovable-sentence sequences need only appear
somewhere in the completed process, not by their own index. §4.2's sentence-level theorem
lands in this §4.5 module because it is the `k = 1`, `b ∈ {0,1}` special case of
`affine_provind_theory_eq`.

Limit vocabulary is `dd:asymp`'s; the reified features the portfolios are built from are
`dd:dsl`'s.
-/

namespace LogicalInduction

open Filter Topology

namespace AffineCombination

/-! ## The gated buy-below trader -/

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

/-! ## The one-sided conclusion -/

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

/-! ## The two-sided form -/

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

/-! ## Completed-theory affine values -/

/-- Values of `A` over all worlds consistent with the completed theory. -/
def completedAffineValues (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) : Set ℝ :=
  {x | ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ x = A.value P v.payout}

/-- Completed-theory affine values are nonempty when every finite stage is plausible. -/
lemma completedAffineValues_nonempty (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (completedAffineValues DP A P).Nonempty := by
  obtain ⟨v, hv⟩ := exists_consistentWithTheory DP hworld
  exact ⟨A.value P v.payout, v, hv, rfl⟩

namespace AffineCombination

/-! ## The fixed-member progression -/

/-- The empty affine combination used before a fixed member's coefficients become
rank-legal. -/
def empty : AffineCombination where
  const := .const 0
  terms := []

/-- Member `i` of a polynomial affine sequence, padded by zero until day `i`. -/
def eventualMember (As : ℕ → AffineCombination) (i n : ℕ) : AffineCombination :=
  if i ≤ n then As i else empty

@[simp] lemma eventualMember_eq (As : ℕ → AffineCombination) (i n : ℕ) (h : i ≤ n) :
    eventualMember As i n = As i := by simp [eventualMember, h]

@[simp] lemma eventualMember_eq_empty (As : ℕ → AffineCombination) (i n : ℕ)
    (h : ¬i ≤ n) : eventualMember As i n = empty := by simp [eventualMember, h]

/-- A fixed threshold between two fixed natural outputs is polynomially fueled. -/
lemma polyFueled_if_lt_const (i a b : ℕ) :
    ∃ c, PolyFueled c (fun n => if n < i then a else b) := by
  have htest := subc_polyFueled.comp ((PolyFueled.const i).pair PolyFueled.id)
  have hpick := ifzSel_polyFueled.comp
    (((PolyFueled.const b).pair (PolyFueled.const a)).pair htest)
  exact ⟨_, hpick.of_eq (fun n => by
    simp only [Nat.unpair_pair, ifzSelFn]
    by_cases h : n < i
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega)])⟩

/-- A polynomial affine sequence can uniformly emit any one of its members forever after
that member's own index. This is the legal fixed-portfolio progression used by the first
half of affine coherence. -/
noncomputable def PolySequence.eventualMember {As : ℕ → AffineCombination}
    (h : PolySequence As) (i : ℕ) : PolySequence (eventualMember As i) := by
  let idx : ℕ → ℕ := fun z => Nat.pair i z.unpair.2
  have hidx : ∃ c, PolyFueled c idx :=
    ⟨_, (PolyFueled.const i).pair PolyFueled.right⟩
  let cidx := Classical.choose hidx
  have hcidx := Classical.choose_spec hidx
  let hconst := h.const_poly.comp (PolyFueled.const i)
  let hconstGated := BigSpliceStream.gateFeature hconst i
  let hcoeff := h.coefficient_poly.comp hcidx
  exact {
    termCount := fun n => if n < i then 0 else h.termCount i
    coefficient := fun z => h.coefficient (idx z)
    sentence := fun z => h.sentence (idx z)
    termCount_poly := polyFueled_if_lt_const i 0 (h.termCount i)
    const_poly := by
      refine BigSpliceStream.of_eq hconstGated ?_
      intro n
      by_cases hin : i ≤ n
      · simp [AffineCombination.eventualMember, hin, gateFeature]
      · simp [AffineCombination.eventualMember, hin, gateFeature, AffineCombination.empty]
    coefficient_poly := hcoeff
    sentence_poly := h.sentence_poly.comp hcidx
    terms_eq := by
      intro n
      by_cases hin : i ≤ n
      · simp only [AffineCombination.eventualMember, hin, if_true, not_lt.mpr hin]
        rw [h.terms_eq]
        apply List.map_congr_left
        intro j hj
        simp [idx]
      · have hni : n < i := Nat.lt_of_not_ge hin
        simp [AffineCombination.eventualMember, hin, hni, AffineCombination.empty]
    const_rank := by
      intro n
      by_cases hin : i ≤ n
      · simpa [AffineCombination.eventualMember, hin] using (h.const_rank i).trans hin
      · simp [AffineCombination.eventualMember, hin, AffineCombination.empty]
    coefficient_rank := by
      intro n j hj
      have hin : i ≤ n := by
        by_contra hni
        have hlt : n < i := Nat.lt_of_not_ge hni
        simp [hlt] at hj
      simpa [idx] using (h.coefficient_rank i j (by simpa [not_lt.mpr hin] using hj)).trans hin
    const_closed := by
      intro n ρ V
      by_cases hin : i ≤ n
      · simpa [AffineCombination.eventualMember, hin] using h.const_closed i ρ V
      · simp [AffineCombination.eventualMember, hin, AffineCombination.empty]
    coefficient_closed := by
      intro z ρ V
      exact h.coefficient_closed (idx z) ρ V
  }

/-- A day-`n` member of a bounded normalized affine family takes values in `[-(B+C), B+C]`
in every world: its day-`n` price is within `B`, and its value differs from that price by
at most its share magnitude `C`. -/
lemma PolySequence.abs_value_le_of_bounded {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) {B C : ℝ}
    (hB : ∀ n m, |(As n).price P m| ≤ B) (hC : ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) (v : PCWorld) :
    |(As n).value P v.payout| ≤ B + C := by
  have hdifference := (As n).abs_value_sub_price_le_magnitude P v.payout n
    (h.terms_rank n)
    (fun φ => by
      by_cases hφ : v.Holds φ
      · exact Or.inr (by simp [PCWorld.payout, hφ])
      · exact Or.inl (by simp [PCWorld.payout, hφ]))
    (hP n)
  have hprice := hB n n
  have hmagnitude := hC n
  rw [abs_le] at hdifference hprice ⊢
  constructor <;> linarith

/-- Completed-theory values of a normalized bounded affine family have uniform real
bounds. -/
lemma PolySequence.completedAffineValues_bdd {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    BddBelow (completedAffineValues DP (As n) P) ∧
      BddAbove (completedAffineValues DP (As n) P) := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  obtain ⟨C, hC⟩ := hmag
  have hC0 : 0 ≤ C := (As 0).magnitude_nonneg P |>.trans (hC 0)
  have hvalue : ∀ v : PCWorld, |(As n).value P v.payout| ≤ B + C :=
    h.abs_value_le_of_bounded P hB hC hP n
  constructor
  · refine ⟨-(B + C), ?_⟩
    rintro x ⟨v, _, rfl⟩
    exact (abs_le.mp (hvalue v)).1
  · refine ⟨B + C, ?_⟩
    rintro x ⟨v, _, rfl⟩
    exact (abs_le.mp (hvalue v)).2

/-- Pointwise first bridge of affine coherence: the infimum over completed-theory worlds
is no greater than the limiting-belief value of each fixed member. -/
lemma PolySequence.completedTheoryLow_le_limitingValue
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i : ℕ) :
    sInf (completedAffineValues DP (As i) P) ≤
      (As i).value P (limitingBelief P) := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  by_contra hnot
  have hlt : (As i).value P (limitingBelief P) <
      sInf (completedAffineValues DP (As i) P) := lt_of_not_ge hnot
  obtain ⟨q, hLq, qhInf⟩ := exists_between hlt
  have hbdd := h.completedAffineValues_bdd P DP hbounded hmag hP i
  have hcompact := eventually_affineValue_gt_of_theory DP (As i) P q (fun v hv => by
    have hinf : sInf (completedAffineValues DP (As i) P) ≤ (As i).value P v.payout := by
      apply csInf_le hbdd.1
      exact ⟨v, hv, rfl⟩
    linarith)
  have hfixedVal : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        q ≤ (AffineCombination.eventualMember As i n).value P v.payout := by
    filter_upwards [hcompact, Filter.eventually_ge_atTop i] with n hn hni
    intro v hv
    rw [eventualMember_eq As i n hni]
    exact (hn v hv).le
  have hfixedPoly := h.eventualMember i
  have hprov := hfixedPoly.affine_provind P DP hworld q hfixedVal
  let L := (As i).value P (limitingBelief P)
  let ε := (q - L) / 4
  have hε : 0 < ε := by dsimp [ε, L]; linarith
  have hprovNear := hprov ε hε
  have htend := (As i).price_tendsto_limitingValue P DP hworld
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend ε hε
  have hpriceNear : ∀ᶠ n in atTop, |(As i).price P n - L| < ε :=
    Filter.eventually_atTop.mpr ⟨N, fun n hn => by
      simpa [Real.dist_eq, L] using hN n hn⟩
  obtain ⟨Np, hNp⟩ := Filter.eventually_atTop.mp hprovNear
  obtain ⟨Nx, hNx⟩ := Filter.eventually_atTop.mp hpriceNear
  let n := max i (max Np Nx)
  have hni : i ≤ n := by simp [n]
  have hnNp : Np ≤ n := by simp [n]
  have hnNx : Nx ≤ n := by simp [n]
  have hnprov := hNp n hnNp
  have hnprice := hNx n hnNx
  change q ≤ (AffineCombination.eventualMember As i n).price P n + ε at hnprov
  rw [AffineCombination.eventualMember_eq As i n hni] at hnprov
  rw [abs_lt] at hnprice
  dsimp [ε, L] at hnprov hnprice
  linarith

/-- Negating an affine combination negates its completed-theory value set. -/
lemma completedAffineValues_neg (DP : DeductiveProcess) (A : AffineCombination)
    (P : History) :
    completedAffineValues DP A.neg P = -(completedAffineValues DP A P) := by
  ext x
  simp only [completedAffineValues, Set.mem_setOf_eq, neg_value, Set.mem_neg]
  constructor
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, hv, by linarith⟩
  · rintro ⟨v, hv, hx⟩
    exact ⟨v, hv, by linarith⟩

/-- Pointwise upper bridge, by applying the lower bridge to the uniformly emitted
negated progression. -/
lemma PolySequence.limitingValue_le_completedTheoryHigh
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (i : ℕ) :
    (As i).value P (limitingBelief P) ≤
      sSup (completedAffineValues DP (As i) P) := by
  have hneg := h.neg.completedTheoryLow_le_limitingValue P DP hbounded.neg
    (exists_magnitude_bound_neg hmag) hworld i
  rw [completedAffineValues_neg, Real.sInf_neg, neg_value] at hneg
  linarith

end AffineCombination

/-- Completed-theory lower affine value at index `n`. -/
noncomputable def completedAffineLow (As : ℕ → AffineCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sInf (completedAffineValues DP (As n) P)

/-- Completed-theory upper affine value at index `n`. -/
noncomputable def completedAffineHigh (As : ℕ → AffineCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sSup (completedAffineValues DP (As n) P)

namespace AffineCombination

/-- Uniform bounds on the completed-theory extrema of a normalized bounded family. -/
lemma PolySequence.completedAffineExtrema_filterBounds
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess)
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsBoundedUnder (· ≥ ·) atTop (completedAffineLow As P DP) ∧
      IsBoundedUnder (· ≤ ·) atTop (completedAffineLow As P DP) ∧
      IsBoundedUnder (· ≥ ·) atTop (completedAffineHigh As P DP) ∧
      IsBoundedUnder (· ≤ ·) atTop (completedAffineHigh As P DP) := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  obtain ⟨C, hC⟩ := hmag
  have hvalue : ∀ n (v : PCWorld), |(As n).value P v.payout| ≤ B + C :=
    h.abs_value_le_of_bounded P hB hC hP
  have hextrema : ∀ n,
      -(B + C) ≤ completedAffineLow As P DP n ∧
        completedAffineLow As P DP n ≤ B + C ∧
        -(B + C) ≤ completedAffineHigh As P DP n ∧
        completedAffineHigh As P DP n ≤ B + C := by
    intro n
    have hnonempty := completedAffineValues_nonempty DP (As n) P hworld
    have hbdd := h.completedAffineValues_bdd P DP
      (show BoundedAffinePrices As P from ⟨B, hB0, hB⟩) ⟨C, hC⟩ hP n
    have hmem : ∀ x ∈ completedAffineValues DP (As n) P,
        -(B + C) ≤ x ∧ x ≤ B + C := by
      rintro x ⟨v, _, rfl⟩
      exact abs_le.mp (hvalue n v)
    constructor
    · apply le_csInf hnonempty
      intro x hx
      exact (hmem x hx).1
    constructor
    · obtain ⟨x, hx⟩ := hnonempty
      exact (csInf_le hbdd.1 hx).trans (hmem x hx).2
    constructor
    · obtain ⟨x, hx⟩ := hnonempty
      exact (hmem x hx).1.trans (le_csSup hbdd.2 hx)
    · apply csSup_le hnonempty
      intro x hx
      exact (hmem x hx).2
  exact ⟨
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => (hextrema n).1)),
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => (hextrema n).2.1)),
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun n => (hextrema n).2.2.1)),
    isBoundedUnder_of_eventually_le (Eventually.of_forall (fun n => (hextrema n).2.2.2))⟩

/-! ## Affine Coherence (`thm:affcoh`) -/

/-- Paper-facing **Affine Coherence** (`thm:affcoh`). The limiting affine value lies
between completed-theory extrema in liminf/limsup, and persistence transports it to the
main diagonal.
Paper node: `thm:affcoh` -/
theorem PolySequence.affcoh {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedAffineLow As P DP) atTop ≤
        liminf (fun n => (As n).value P (limitingBelief P)) atTop ∧
      liminf (fun n => (As n).value P (limitingBelief P)) atTop ≤
        liminf (fun n => (As n).price P n) atTop) ∧
      (limsup (fun n => (As n).price P n) atTop ≤
          limsup (fun n => (As n).value P (limitingBelief P)) atTop ∧
        limsup (fun n => (As n).value P (limitingBelief P)) atTop ≤
          limsup (completedAffineHigh As P DP) atTop) := by
  let hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  obtain ⟨hdlo, hdhi, hhlo, hhhi, hllo, hlhi⟩ := hbounded.filterBounds
  obtain ⟨hlimlo, hlimhi⟩ :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      hbounded DP hworld
  obtain ⟨htllo, htlhi, hthlo, hthhi⟩ :=
    h.completedAffineExtrema_filterBounds P DP hbounded hmag hP hworld
  have hper := h.peraffkno P DP hbounded hmag hworld
  have htheoryLow : ∀ n, completedAffineLow As P DP n ≤
      (As n).value P (limitingBelief P) :=
    fun n => h.completedTheoryLow_le_limitingValue P DP hbounded hmag hworld n
  have htheoryHigh : ∀ n, (As n).value P (limitingBelief P) ≤
      completedAffineHigh As P DP n :=
    fun n => h.limitingValue_le_completedTheoryHigh P DP hbounded hmag hworld n
  have hfutureLowDiag : ∀ n,
      affineFutureLow As P n ≤ (As n).price P n :=
    hbounded.futureLow_le_diagonal
  have hdiagFutureHigh : ∀ n,
      (As n).price P n ≤ affineFutureHigh As P n :=
    hbounded.diagonal_le_futureHigh
  constructor
  · constructor
    · exact liminf_le_liminf (Eventually.of_forall htheoryLow)
        htllo hlimhi.isCobounded_flip
    · calc
        liminf (fun n => (As n).value P (limitingBelief P)) atTop =
            liminf (affineFutureLow As P) atTop := hper.1.symm
        _ ≤ liminf (fun n => (As n).price P n) atTop :=
          liminf_le_liminf (Eventually.of_forall hfutureLowDiag)
            hllo hdhi.isCobounded_flip
  · constructor
    · calc
        limsup (fun n => (As n).price P n) atTop ≤
            limsup (affineFutureHigh As P) atTop :=
          limsup_le_limsup (Eventually.of_forall hdiagFutureHigh)
            hdlo.isCobounded_flip hhhi
        _ = limsup (fun n => (As n).value P (limitingBelief P)) atTop := hper.2
    · exact limsup_le_limsup (Eventually.of_forall htheoryHigh)
        hlimlo.isCobounded_flip hthhi

/-! ## Affine Provability Induction (`thm:affprovind`) -/

/-- Lower form of **Affine Provability Induction**: for `⟨A⟩` a bounded combination
sequence and `b : ℝ`, a uniform lower bound `b ≤ W(Aₙ)` in every completed-theory world
`W ∈ cworlds(Θ)` is learned on the main diagonal.
Paper node: `thm:affprovind` -/
theorem PolySequence.affine_provind_theory_ge
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      b ≤ (As n).value P v.payout) :
    (fun n => (As n).price P n) ≳ₙ fun _ => b := by
  let hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  obtain ⟨_, hdhi, _, _, _, _⟩ := hbounded.filterBounds
  obtain ⟨_, htlhi, _, _⟩ :=
    h.completedAffineExtrema_filterBounds P DP hbounded hmag hP hworld
  have hlow : ∀ n, b ≤ completedAffineLow As P DP n := by
    intro n
    apply le_csInf (completedAffineValues_nonempty DP (As n) P hworld)
    rintro x ⟨v, hv, rfl⟩
    exact hval n v hv
  have hcoh := h.affcoh P DP hbounded hmag hworld
  have hbTheory : b ≤ liminf (completedAffineLow As P DP) atTop :=
    le_liminf_of_le htlhi.isCobounded_flip (Eventually.of_forall hlow)
  have hbDiag : b ≤ liminf (fun n => (As n).price P n) atTop :=
    hbTheory.trans (hcoh.1.1.trans hcoh.1.2)
  intro ε hε
  have hevent := eventually_lt_of_lt_liminf
    (show b - ε < liminf (fun n => (As n).price P n) atTop by linarith)
    (by
      obtain ⟨hdlo, _, _, _, _, _⟩ := hbounded.filterBounds
      exact hdlo)
  filter_upwards [hevent] with n hn
  linarith

/-- Upper form of **Affine Provability Induction**: the `≤` variant, by negation.
Paper node: `thm:affprovind` -/
theorem PolySequence.affine_provind_theory_le
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (As n).value P v.payout ≤ b) :
    (fun n => (As n).price P n) ≲ₙ fun _ => b := by
  have hneg := h.neg.affine_provind_theory_ge P DP hbounded.neg
    (exists_magnitude_bound_neg hmag) hworld (-b)
    (fun n v hv => by rw [neg_value]; linarith [hval n v hv])
  intro ε hε
  filter_upwards [hneg ε hε] with n hn
  rw [neg_price] at hn
  linarith

/-- Equality form of **Affine Provability Induction**: the `=` variant, from the two
one-sided forms.
Paper node: `thm:affprovind` -/
theorem PolySequence.affine_provind_theory_eq
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (As n).value P v.payout = b) :
    (fun n => (As n).price P n) ≈ₙ fun _ => b := by
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨h.affine_provind_theory_le P DP hbounded hmag hworld b
      (fun n v hv => (hval n v hv).le),
    h.affine_provind_theory_ge P DP hbounded hmag hworld b
      (fun n v hv => (hval n v hv).ge)⟩

/-! ## Vanishing-error forms -/

/-- Vanishing-error form of paper-facing affine provability induction.  This is the form
needed by quoted `[0,1]` values: the finite threshold sum approximates its represented real
value within `O(1/n)`, so completed-theory values tend uniformly to zero rather than being
definitionally zero on every index. -/
lemma PolySequence.affine_provind_theory_tendsto_zero
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory DP → |(As n).value P v.payout| ≤ ε) :
    (fun n => (As n).price P n) ≈ₙ fun _ => 0 := by
  let hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  obtain ⟨hdlo, hdhi, _, _, _, _⟩ := hbounded.filterBounds
  obtain ⟨_, htlhi, hthlo, _⟩ :=
    h.completedAffineExtrema_filterBounds P DP hbounded hmag hP hworld
  have hcoh := h.affcoh P DP hbounded hmag hworld
  have hnear := hval (ε / 2) (by linarith)
  have hlow : ∀ᶠ n in atTop, -ε / 2 ≤ completedAffineLow As P DP n := by
    filter_upwards [hnear] with n hn
    apply le_csInf (completedAffineValues_nonempty DP (As n) P hworld)
    rintro x ⟨v, hv, rfl⟩
    have hx := hn v hv
    rw [abs_le] at hx
    linarith
  have hhigh : ∀ᶠ n in atTop, completedAffineHigh As P DP n ≤ ε / 2 := by
    filter_upwards [hnear] with n hn
    apply csSup_le (completedAffineValues_nonempty DP (As n) P hworld)
    rintro x ⟨v, hv, rfl⟩
    have hx := hn v hv
    rw [abs_le] at hx
    linarith
  have hliminfLow : -ε / 2 ≤ liminf (completedAffineLow As P DP) atTop :=
    le_liminf_of_le htlhi.isCobounded_flip hlow
  have hliminfPrice : -ε / 2 ≤ liminf (fun n => (As n).price P n) atTop :=
    hliminfLow.trans (hcoh.1.1.trans hcoh.1.2)
  have hlower : ∀ᶠ n in atTop, -ε < (As n).price P n :=
    eventually_lt_of_lt_liminf (by linarith) hdlo
  have hlimsupHigh : limsup (completedAffineHigh As P DP) atTop ≤ ε / 2 :=
    limsup_le_of_le hthlo.isCobounded_flip hhigh
  have hlimsupPrice : limsup (fun n => (As n).price P n) atTop ≤ ε / 2 :=
    (hcoh.2.1.trans hcoh.2.2).trans hlimsupHigh
  have hupper : ∀ᶠ n in atTop, (As n).price P n < ε :=
    eventually_lt_of_limsup_lt (by linarith) hdhi
  filter_upwards [hlower, hupper] with n hnlo hnhi
  rw [sub_zero, abs_le]
  exact ⟨hnlo.le, hnhi.le⟩

/-- One-sided (`≤`) paper-facing affine provability induction with **vanishing error**: if the
completed-theory value stays below `c` up to a vanishing slack, the diagonal price is `≲ₙ c`.
This is the one-sided analogue of `affine_provind_theory_tendsto_zero`, needed by the mesh of a
LUV-combination whose value is determined only up to the mesh's `O(1/n)` error. -/
lemma PolySequence.affine_provind_theory_le_const
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (c : ℝ)
    (hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory DP → (As n).value P v.payout ≤ c + ε) :
    (fun n => (As n).price P n) ≲ₙ fun _ => c := by
  let hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  intro ε hε
  obtain ⟨_, hdhi, _, _, _, _⟩ := hbounded.filterBounds
  obtain ⟨_, _, hthlo, _⟩ :=
    h.completedAffineExtrema_filterBounds P DP hbounded hmag hP hworld
  have hcoh := h.affcoh P DP hbounded hmag hworld
  have hnear := hval (ε / 2) (by linarith)
  have hhigh : ∀ᶠ n in atTop, completedAffineHigh As P DP n ≤ c + ε / 2 := by
    filter_upwards [hnear] with n hn
    apply csSup_le (completedAffineValues_nonempty DP (As n) P hworld)
    rintro x ⟨v, hv, rfl⟩
    exact hn v hv
  have hlimsupHigh : limsup (completedAffineHigh As P DP) atTop ≤ c + ε / 2 :=
    limsup_le_of_le hthlo.isCobounded_flip hhigh
  have hlimsupPrice : limsup (fun n => (As n).price P n) atTop ≤ c + ε / 2 :=
    (hcoh.2.1.trans hcoh.2.2).trans hlimsupHigh
  have hupper : ∀ᶠ n in atTop, (As n).price P n < c + ε :=
    eventually_lt_of_limsup_lt (by linarith) hdhi
  filter_upwards [hupper] with n hnhi
  linarith [hnhi]

/-- One-sided (`≥`) vanishing-error affine provability induction, dual to
`affine_provind_theory_le_const` through the negated sequence. -/
lemma PolySequence.affine_provind_theory_ge_const
    {As : ℕ → AffineCombination} (h : PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ C : ℝ, ∀ n, (As n).magnitude P ≤ C)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (c : ℝ)
    (hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory DP → c - ε ≤ (As n).value P v.payout) :
    (fun n => (As n).price P n) ≳ₙ fun _ => c := by
  have hneg := h.neg.affine_provind_theory_le_const P DP hbounded.neg
    (exists_magnitude_bound_neg hmag) hworld (-c)
    (fun ε hε => by
      filter_upwards [hval ε hε] with n hn v hv
      rw [neg_value]; linarith [hn v hv])
  intro ε hε
  filter_upwards [hneg ε hε] with n hn
  rw [neg_price] at hn
  linarith

end AffineCombination

/-! ## Provability Induction (`thm:provind`) -/

/-- One-sided paper-facing provability induction for an efficiently codeable sequence of
completed-theory theorems. Individual proofs may appear arbitrarily later than their
sequence indices.
Paper node: `thm:provind` -/
theorem lic_provind_true (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hthm : ∀ n, ∃ k, φ n ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (φ n)) ≈ₙ fun _ => 1 := by
  let hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hφpoly := AffineCombination.sentenceAffine_polySequence φ hφ
  have hφeq := hφpoly.affine_provind_theory_eq P DP
    (AffineCombination.sentenceAffine_bounded φ P hP)
    ⟨1, fun n => by simp⟩ hworld 1 (fun n v hv => by
      obtain ⟨k, hk⟩ := hthm n
      have hholds := hv k (φ n) hk
      simp [AffineCombination.sentenceAffine, AffineCombination.value,
        PCWorld.payout, hholds])
  simpa using hφeq

/-- One-sided paper-facing provability induction for an efficiently codeable sequence
whose negations are completed-theory theorems.
Paper node: `thm:provind` -/
theorem lic_provind_false (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (hψ : BigSentenceCodes ψ)
    (hdis : ∀ n, ∃ k, (∼ψ n) ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => P n (ψ n)) ≈ₙ fun _ => 0 := by
  let hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hψpoly := AffineCombination.sentenceAffine_polySequence ψ hψ
  have hψeq := hψpoly.affine_provind_theory_eq P DP
    (AffineCombination.sentenceAffine_bounded ψ P hP)
    ⟨1, fun n => by simp⟩ hworld 0 (fun n v hv => by
      obtain ⟨k, hk⟩ := hdis n
      have hneg := hv k (∼ψ n) hk
      have hfalse : ¬v.Holds (ψ n) := (PCWorld.holds_neg v (ψ n)).mp hneg
      simp [AffineCombination.sentenceAffine, AffineCombination.value,
        PCWorld.payout, hfalse])
  simpa using hψeq

/-- Faithful paper-facing **Provability Induction** (`thm:provind`). Efficient theorem
and disprovable-sentence sequences need only appear somewhere in the completed deductive
process; they need not be present by their own index.
Paper node: `thm:provind` -/
theorem lic_provind (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ ψ : ℕ → Sentence)
    (hφ : BigSentenceCodes φ) (hψ : BigSentenceCodes ψ)
    (hthm : ∀ n, ∃ k, φ n ∈ DP.D k)
    (hdis : ∀ n, ∃ k, (∼ψ n) ∈ DP.D k)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ((fun n => P n (φ n)) ≈ₙ fun _ => 1) ∧
      ((fun n => P n (ψ n)) ≈ₙ fun _ => 0) :=
  ⟨lic_provind_true P DP φ hφ hthm hworld,
    lic_provind_false P DP ψ hψ hdis hworld⟩

end LogicalInduction
