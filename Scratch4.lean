import LogicalInduction.Construction.Witnesses.QuotationAffine

namespace LogicalInduction
namespace DeferralFibre

open Filter Topology

/-- Only finitely many days are scheduled from below `N`, so past the largest of them every
element of every fibre is at or above `N`.  Injectivity-free: the constraint is only that
`f 0, …, f (N-1)` are finitely many days. -/
lemma exists_fibre_floor (f : DeferralFunction) (N : ℕ) :
    ∃ M, ∀ m, M ≤ m → ∀ k, f k = m → N ≤ k := by
  refine ⟨(Finset.range N).sup (fun k ↦ f k) + 1, fun m hm k hk ↦ ?_⟩
  by_contra hnot
  have hlt : k < N := Nat.lt_of_not_ge hnot
  have hle : f k ≤ (Finset.range N).sup (fun j ↦ f j) :=
    Finset.le_sup (f := fun j ↦ f j) (Finset.mem_range.2 hlt)
  omega

/-- **Fibre-gated deferred coherence, one precision.**  For a single gate width `δ` the
first-violator selector packages the whole fibre into one day-`m` portfolio of unit
magnitude, so affine coherence forces the day-`m` price to zero; a saturated gate would
keep that price at `δ/(2C)`, so eventually no fibre element's gap reaches `2δ`. -/
lemma fibre_price_eventually_small
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    {Bs : ℕ → AffineCombination} (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1)
    {width : ℕ → ℕ} (hwidth : ∃ c, PolyFueled c width) (hwidthPos : ∀ m, 0 < width m)
    (hwide : ∀ m k, k < m → (Bs (Nat.pair m k)).terms.length ≤ width m)
    {C : ℚ} (hC : 0 < C)
    (hmag : ∀ z, (Bs z).magnitude P ≤ (C : ℝ))
    (hbdd : ∀ z day, |(Bs z).price P day| ≤ (C : ℝ))
    (hsmall : ∀ ε > 0, ∃ N, ∀ m k, N ≤ k → k < m → f k = m →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        |(Bs (Nat.pair m k)).value P v.payout| ≤ ε)
    {δ : ℚ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, ∀ k, k < m → f k = m →
      |(Bs (Nat.pair m k)).price P m| < 2 * (δ : ℝ) := by
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδinv : PolyRatCodes (fun _ : ℕ ↦ 1 / δ) :=
    ⟨_, PolyFueled.const (Encodable.encode (1 / δ))⟩
  have hnorm : (0 : ℝ) < ((1 / (2 * C) : ℚ) : ℝ) := by
    have : (0 : ℚ) < 1 / (2 * C) := by positivity
    exact_mod_cast this
  -- the two gate families and the affine coefficient
  set gP : ℕ → EF := gateBase f a degree δ (gapPos Bs) with hgPdef
  set gN : ℕ → EF := gateBase f a degree δ (gapNeg Bs) with hgNdef
  set coeff : ℕ → EF := gateCoeff f a degree δ C Bs with hcoeffdef
  have hcoeffP : PairedWeighting coeff :=
    gateCoeff_paired f a degree hδinv hB hconstRank htermRank
  -- real-valued shorthands
  set pr : ℕ → ℕ → ℝ := fun m k ↦ (Bs (Nat.pair m k)).price P m with hprdef
  set pos : ℕ → ℕ → ℝ := fun m k ↦ Max.max (pr m k) 0 with hposdef
  set neg : ℕ → ℕ → ℝ := fun m k ↦ Max.max (-(pr m k)) 0 with hnegdef
  set bP : ℕ → ℕ → ℝ := fun m k ↦ (gP (Nat.pair m k)).denote P with hbPdef
  set bN : ℕ → ℕ → ℝ := fun m k ↦ (gN (Nat.pair m k)).denote P with hbNdef
  set wP : ℕ → ℕ → ℝ := fun m k ↦ bP m k * ∏ j ∈ Finset.range k, (1 - bP m j) with hwPdef
  set wN : ℕ → ℕ → ℝ := fun m k ↦ bN m k * ∏ j ∈ Finset.range k, (1 - bN m j) with hwNdef
  have hpr : ∀ m k, pr m k = (Bs (Nat.pair m k)).price P m := fun _ _ ↦ rfl
  have hpos : ∀ m k, pos m k = Max.max (pr m k) 0 := fun _ _ ↦ rfl
  have hneg : ∀ m k, neg m k = Max.max (-(pr m k)) 0 := fun _ _ ↦ rfl
  have hgapPos : ∀ m k, (gapPos Bs (Nat.pair m k)).denote P = pos m k := by
    intro m k; rw [gapPos_denote, hpos m k, hpr m k]; simp
  have hgapNeg : ∀ m k, (gapNeg Bs (Nat.pair m k)).denote P = neg m k := by
    intro m k; rw [gapNeg_denote, hneg m k, hpr m k]; simp
  have hbPeq : ∀ m k, bP m k = (gP (Nat.pair m k)).denote P := fun _ _ ↦ rfl
  have hbNeq : ∀ m k, bN m k = (gN (Nat.pair m k)).denote P := fun _ _ ↦ rfl
  have hwP : ∀ m k, wP m k = bP m k * ∏ j ∈ Finset.range k, (1 - bP m j) := fun _ _ ↦ rfl
  have hwN : ∀ m k, wN m k = bN m k * ∏ j ∈ Finset.range k, (1 - bN m j) := fun _ _ ↦ rfl
  have hbPmem : ∀ m k, 0 ≤ bP m k ∧ bP m k ≤ 1 := fun m k ↦
    gateBase_mem f a degree δ hδ _ _ P
  have hbNmem : ∀ m k, 0 ≤ bN m k ∧ bN m k ≤ 1 := fun m k ↦
    gateBase_mem f a degree δ hδ _ _ P
  have hwPnonneg : ∀ m k, 0 ≤ wP m k := fun m k ↦
    firstSuccess_weight_nonneg (hbPmem m) k
  have hwNnonneg : ∀ m k, 0 ≤ wN m k := fun m k ↦
    firstSuccess_weight_nonneg (hbNmem m) k
  have hwPsum : ∀ m, ∑ k ∈ Finset.range m, wP m k ≤ 1 := fun m ↦
    firstSuccess_sum_le_one (hbPmem m) m
  have hwNsum : ∀ m, ∑ k ∈ Finset.range m, wN m k ≤ 1 := fun m ↦
    firstSuccess_sum_le_one (hbNmem m) m
  have hcoeffDen : ∀ m k, (coeff (Nat.pair m k)).denote P =
      ((1 / (2 * C) : ℚ) : ℝ) * (wP m k - wN m k) := by
    intro m k
    rw [hwP m k, hwN m k, hbPeq m k, hbNeq m k, hcoeffdef]
    simp only [gateCoeff, EF.denote_mul, EF.denote_add, EF.denote_const,
      Pi.mul_apply, Pi.add_apply, hgPdef, hgNdef, selectorFeature_denote]
    push_cast
    ring
  -- gates only fire inside the fibre
  have hbP_match : ∀ m k, FeedbackEmission.scheduledMatch f a degree (Nat.pair m k) = 0 →
      bP m k = 0 := by
    intro m k h
    rw [hbPeq m k, hgPdef, gateBase_denote f a degree δ hδ _ _ P, h]
    simp
  have hbN_match : ∀ m k, FeedbackEmission.scheduledMatch f a degree (Nat.pair m k) = 0 →
      bN m k = 0 := by
    intro m k h
    rw [hbNeq m k, hgNdef, gateBase_denote f a degree δ hδ _ _ P, h]
    simp
  have hcoeff_fibre : ∀ m k, (coeff (Nat.pair m k)).denote P ≠ 0 → f k = m := by
    intro m k hne
    rcases FeedbackEmission.scheduledMatch_zero_or_one f a degree (Nat.pair m k) with h | h
    · exfalso
      rw [hcoeffDen m k, hwP m k, hwN m k, hbP_match m k h, hbN_match m k h] at hne
      simp at hne
    · exact (FeedbackEmission.scheduledMatch_eq_one_iff f hspec m k).1 h
  -- gate positivity forces the gap past δ
  have hbP_forces : ∀ m k, 0 < bP m k → (δ : ℝ) ≤ pos m k := by
    intro m k h
    have := gateBase_pos f a degree δ hδ (gapPos Bs) (Nat.pair m k) P h
    rw [hgapPos m k] at this
    exact this.le
  have hbN_forces : ∀ m k, 0 < bN m k → (δ : ℝ) ≤ neg m k := by
    intro m k h
    have := gateBase_pos f a degree δ hδ (gapNeg Bs) (Nat.pair m k) P h
    rw [hgapNeg m k] at this
    exact this.le
  -- signed summand splits into two non-cancelling halves
  have hsplit : ∀ m k, (wP m k - wN m k) * pr m k = wP m k * pos m k + wN m k * neg m k := by
    intro m k
    by_cases hge : 0 ≤ pr m k
    · have e1 : pos m k = pr m k := by rw [hpos m k]; exact max_eq_left hge
      have e2 : neg m k = 0 := by rw [hneg m k]; exact max_eq_right (by linarith)
      have hwN0 : wN m k = 0 := by
        rcases eq_or_lt_of_le (hbNmem m k).1 with h0 | h0
        · rw [hwN m k, ← h0, zero_mul]
        · exact absurd (hbN_forces m k h0) (by rw [e2]; linarith)
      rw [e1, e2, hwN0]; ring
    · have hlt : pr m k < 0 := by linarith [not_le.mp hge]
      have e1 : pos m k = 0 := by rw [hpos m k]; exact max_eq_right hlt.le
      have e2 : neg m k = -(pr m k) := by rw [hneg m k]; exact max_eq_left (by linarith)
      have hwP0 : wP m k = 0 := by
        rcases eq_or_lt_of_le (hbPmem m k).1 with h0 | h0
        · rw [hwP m k, ← h0, zero_mul]
        · exact absurd (hbP_forces m k h0) (by rw [e1]; linarith)
      rw [e1, e2, hwP0]; ring
  -- the day-indexed portfolio
  have hBconstRank : ∀ m k, (Bs (Nat.pair m k)).const.rank ≤ m := fun m k ↦ by
    simpa using hconstRank (Nat.pair m k)
  have hBcoeffRank : ∀ m k o, o < hB.termCount (Nat.pair m k) →
      (hB.coefficient (Nat.pair (Nat.pair m k) o)).rank ≤ m := by
    intro m k o ho
    have hmem : (hB.coefficient (Nat.pair (Nat.pair m k) o),
        hB.sentence (Nat.pair (Nat.pair m k) o)) ∈ (Bs (Nat.pair m k)).terms := by
      rw [hB.terms_eq]
      exact List.mem_map.2 ⟨o, List.mem_range.2 ho, rfl⟩
    simpa using htermRank (Nat.pair m k) _ hmem
  set family : ℕ → AffineCombination :=
    AffineCombination.blockSum Bs coeff (fun m ↦ m) width (hB.sentence 0) with hfamdef
  have hfamilyPoly : AffineCombination.PolySequence family :=
    hB.blockSum hcoeffP.polySeg hcoeffP.closed
      (fun m k ↦ by simpa using hcoeffP.rank_le (Nat.pair m k))
      ⟨_, PolyFueled.id⟩ hwidth hwidthPos hBconstRank hBcoeffRank
      (hB.sentence 0) (hB.sentence_poly.comp (PolyFueled.const 0))
  have hwq : ∀ m, ∀ k < m, (Bs (Nat.pair m k)).terms.length ≤ width m :=
    fun m k hk ↦ hwide m k hk
  have hfamPrice : ∀ m day, (family m).price P day =
      ∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
        (Bs (Nat.pair m k)).price P day := by
    intro m day
    rw [hfamdef, AffineCombination.blockSum_price _ _ _ _ _ _ _ _ (hwq m),
      list_sum_range]
  have hfamMag : ∀ m, (family m).magnitude P =
      ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| *
        (Bs (Nat.pair m k)).magnitude P := by
    intro m
    rw [hfamdef, AffineCombination.blockSum_magnitude _ _ _ _ _ _ _ (hwq m),
      list_sum_range]
  have hfamValue : ∀ m (w : Valuation), (family m).value P w =
      ∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
        (Bs (Nat.pair m k)).value P w := by
    intro m w
    rw [hfamdef, AffineCombination.blockSum_value _ _ _ _ _ _ _ _ (hwq m),
      list_sum_range]
  have hcoeffAbs : ∀ m k, |(coeff (Nat.pair m k)).denote P| ≤
      ((1 / (2 * C) : ℚ) : ℝ) * (wP m k + wN m k) := by
    intro m k
    rw [hcoeffDen m k, abs_mul, abs_of_pos hnorm]
    refine mul_le_mul_of_nonneg_left ?_ hnorm.le
    rw [abs_sub_le_iff]
    constructor <;> [linarith [hwNnonneg m k]; linarith [hwPnonneg m k]]
  have hcoeffSum : ∀ m, ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| ≤
      ((1 / (2 * C) : ℚ) : ℝ) * 2 := by
    intro m
    calc ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|
        ≤ ∑ k ∈ Finset.range m, ((1 / (2 * C) : ℚ) : ℝ) * (wP m k + wN m k) :=
          Finset.sum_le_sum fun k _ ↦ hcoeffAbs m k
      _ = ((1 / (2 * C) : ℚ) : ℝ) *
            ((∑ k ∈ Finset.range m, wP m k) + ∑ k ∈ Finset.range m, wN m k) := by
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith [hwPsum m, hwNsum m]) hnorm.le
  have hnorm2 : ((1 / (2 * C) : ℚ) : ℝ) * 2 * (C : ℝ) = 1 := by
    have : ((1 / (2 * C) : ℚ) : ℝ) = 1 / (2 * (C : ℝ)) := by push_cast; ring
    rw [this]; field_simp
  have q : CompletedAffineQuoteApprox P DP (fun m ↦ (family m).price P m) :=
    { family := family
      poly := hfamilyPoly
      scale := 1
      scale_pos := by norm_num
      current_price := fun m ↦ by norm_num
      bounded := ⟨1, zero_le_one, fun m day ↦ by
        rw [hfamPrice m day]
        calc |∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).price P day|
            ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).price P day| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| * (C : ℝ) := by
              refine Finset.sum_le_sum fun k _ ↦ ?_
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hbdd _ day) (abs_nonneg _)
          _ = (∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|) * (C : ℝ) := by
              rw [Finset.sum_mul]
          _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 * (C : ℝ) :=
              mul_le_mul_of_nonneg_right (hcoeffSum m) hCR.le
          _ = 1 := hnorm2⟩
      magnitude_le_one := fun m ↦ by
        rw [hfamMag m]
        calc ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| *
              (Bs (Nat.pair m k)).magnitude P
            ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P| * (C : ℝ) :=
              Finset.sum_le_sum fun k _ ↦
                mul_le_mul_of_nonneg_left (hmag _) (abs_nonneg _)
          _ = (∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|) * (C : ℝ) := by
              rw [Finset.sum_mul]
          _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 * (C : ℝ) :=
              mul_le_mul_of_nonneg_right (hcoeffSum m) hCR.le
          _ = 1 := hnorm2
      theory_coherent := by
        intro ε hε
        obtain ⟨N, hN⟩ := hsmall ((C : ℝ) * ε) (by positivity)
        obtain ⟨M, hM⟩ := exists_fibre_floor f N
        refine eventually_atTop.2 ⟨M, fun m hm v hv ↦ ?_⟩
        rw [hfamValue m v.payout]
        calc |∑ k ∈ Finset.range m, (coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).value P v.payout|
            ≤ ∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P *
                (Bs (Nat.pair m k)).value P v.payout| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range m,
                |(coeff (Nat.pair m k)).denote P| * ((C : ℝ) * ε) := by
              refine Finset.sum_le_sum fun k hk ↦ ?_
              rw [abs_mul]
              by_cases hz : (coeff (Nat.pair m k)).denote P = 0
              · simp [hz]
              · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                have hfk := hcoeff_fibre m k hz
                exact hN m k (hM m hm k hfk) (Finset.mem_range.1 hk) hfk v hv
          _ = (∑ k ∈ Finset.range m, |(coeff (Nat.pair m k)).denote P|) *
                ((C : ℝ) * ε) := by rw [Finset.sum_mul]
          _ ≤ ((1 / (2 * C) : ℚ) : ℝ) * 2 * ((C : ℝ) * ε) :=
              mul_le_mul_of_nonneg_right (hcoeffSum m) (by positivity)
          _ = ε := by rw [← mul_assoc, hnorm2, one_mul] }
  -- the gated day-`m` price converges, and a saturated gate would keep it at `δ/(2C)`
  have hgap : Tendsto (fun m ↦ (family m).price P m) atTop (𝓝 0) := by
    simpa only [AsympEq, _root_.sub_zero] using q.gap_asympEq_zero hworld
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hgap
    (((1 / (2 * C) : ℚ) : ℝ) * (δ : ℝ)) (by positivity)
  refine eventually_atTop.2 ⟨M, fun m hm k hk hfk ↦ ?_⟩
  by_contra hbig
  rw [not_lt] at hbig
  have hmatch : FeedbackEmission.scheduledMatch f a degree (Nat.pair m k) = 1 :=
    (FeedbackEmission.scheduledMatch_eq_one_iff f hspec m k).2 hfk
  have hsum_eq : (family m).price P m =
      ((1 / (2 * C) : ℚ) : ℝ) *
        ((∑ j ∈ Finset.range m, wP m j * pos m j) +
          ∑ j ∈ Finset.range m, wN m j * neg m j) := by
    rw [hfamPrice m m, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hcoeffDen m j, show (Bs (Nat.pair m j)).price P m = pr m j from rfl, mul_assoc,
      hsplit m j]
    ring
  have hlarge : ((1 / (2 * C) : ℚ) : ℝ) * (δ : ℝ) ≤ (family m).price P m := by
    rw [hsum_eq]
    refine mul_le_mul_of_nonneg_left ?_ hnorm.le
    have hbig' : 2 * (δ : ℝ) ≤ |pr m k| := hbig
    rcases le_abs.mp hbig' with hup | hdown
    · have hposk : pos m k = pr m k := by
        rw [hpos m k]; exact max_eq_left (by linarith)
      have hhit : bP m k = 1 := by
        rw [hbPeq m k, hgPdef]
        exact gateBase_eq_one f a degree δ hδ _ _ P hmatch
          (by rw [hgapPos m k, hposk]; linarith)
      have h1 : (δ : ℝ) ≤ ∑ j ∈ Finset.range m, wP m j * pos m j :=
        firstSuccess_forces hk (hbPmem m) hhit (fun j _ hj ↦ hbP_forces m j hj)
      have h2 : 0 ≤ ∑ j ∈ Finset.range m, wN m j * neg m j :=
        Finset.sum_nonneg fun j _ ↦ mul_nonneg (hwNnonneg m j) (le_max_right _ _)
      linarith
    · have hnegk : neg m k = -(pr m k) := by
        rw [hneg m k]; exact max_eq_left (by linarith)
      have hhit : bN m k = 1 := by
        rw [hbNeq m k, hgNdef]
        exact gateBase_eq_one f a degree δ hδ _ _ P hmatch
          (by rw [hgapNeg m k, hnegk]; linarith)
      have h1 : (δ : ℝ) ≤ ∑ j ∈ Finset.range m, wN m j * neg m j :=
        firstSuccess_forces hk (hbNmem m) hhit (fun j _ hj ↦ hbN_forces m j hj)
      have h2 : 0 ≤ ∑ j ∈ Finset.range m, wP m j * pos m j :=
        Finset.sum_nonneg fun j _ ↦ mul_nonneg (hwPnonneg m j) (le_max_right _ _)
      linarith
  have hclose := hM m hm
  rw [Real.dist_eq, _root_.sub_zero, abs_lt] at hclose
  linarith [hclose.2]

/-- **`def:deferralfunc`-faithful deferred price coherence.**  For every deferral function
satisfying only `f n > n` plus poly-clocked emission — no injectivity, no monotonicity —
a uniformly small completed-theory block family has vanishing deferred price along the
diagonal `n ↦ ⟨f n, n⟩`. -/
theorem deferred_block_price_tendsto_zero
    {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction) {a degree : ℕ}
    (hspec : ∀ k, Nat.Partrec.Code.evaln
      (PrefixPatchCompile.ecClock a degree (f k)) f.code k = some (f k))
    {Bs : ℕ → AffineCombination} (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1)
    {width : ℕ → ℕ} (hwidth : ∃ c, PolyFueled c width) (hwidthPos : ∀ m, 0 < width m)
    (hwide : ∀ m k, k < m → (Bs (Nat.pair m k)).terms.length ≤ width m)
    {C : ℚ} (hC : 0 < C)
    (hmag : ∀ z, (Bs z).magnitude P ≤ (C : ℝ))
    (hbdd : ∀ z day, |(Bs z).price P day| ≤ (C : ℝ))
    (hsmall : ∀ ε > 0, ∃ N, ∀ m k, N ≤ k → k < m → f k = m →
      ∀ v : PCWorld, v.ConsistentWithTheory DP →
        |(Bs (Nat.pair m k)).value P v.payout| ≤ ε) :
    Tendsto (fun n ↦ (Bs (Nat.pair (f n) n)).price P (f n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδpos, hδsmall⟩ : ∃ δ : ℚ, 0 < δ ∧ 2 * (δ : ℝ) < ε := by
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (show (0:ℝ) < ε / 3 from by linarith)
    refine ⟨q, by exact_mod_cast hq0, ?_⟩
    have : (q : ℝ) < ε / 3 := hqε
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (fibre_price_eventually_small hworld f hspec hB hconstRank htermRank hwidth
      hwidthPos hwide hC hmag hbdd hsmall hδpos)
  refine ⟨M, fun n hn ↦ ?_⟩
  have hfn : M ≤ f n := le_trans hn (f.lt n).le
  have := hM (f n) hfn n (f.lt n) rfl
  rw [Real.dist_eq, _root_.sub_zero]
  linarith

end DeferralFibre
end LogicalInduction
