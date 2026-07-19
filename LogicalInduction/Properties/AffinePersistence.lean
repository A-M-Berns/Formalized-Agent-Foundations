/-
# Affine persistence infrastructure (`thm:peraffkno`)

The paper's persistence theorem compares every fixed affine combination `A n` with the
limiting belief state `P∞`. This file constructs that limiting valuation, proves fixed
finite affine convergence, and implements the uniform-in-`n` prefix portfolio from
Appendix `app:peraffkno`. The portfolio has an explicit polynomial affine-sequence
certificate and reduces the economic contradiction to the already verified affine
round-trip/ROI hub.
-/
import LogicalInduction.Properties.AffinePreemptiveLearning
import LogicalInduction.Properties.Convergence

namespace LogicalInduction

open Filter Topology

/-- The limiting valuation `P∞`, represented canonically by the limsup of each price
sequence. Under the logical-inductor market hypotheses, `lic_limitingBelief_tendsto` proves
that this limsup is the actual limit. -/
noncomputable def limitingBelief (P : History) : Valuation :=
  fun φ => limsup (fun n => P n φ) atTop

/-- Every sentence price converges to its coordinate in `limitingBelief`. -/
theorem lic_limitingBelief_tendsto (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence) :
    ConvergesTo (fun n => P n φ) (limitingBelief P φ) := by
  obtain ⟨L, hL⟩ := lic_price_convergesTo P DP φ (fun n => hP n φ) hworld
  have hlim : limitingBelief P φ = L := by
    exact hL.limsup_eq
  rwa [hlim]

namespace AffineCombination

/-- A fixed finite affine combination is continuous along the converging price sequence:
its cross-day market prices converge to its value under `P∞`. Feature coefficients are
evaluated against the fixed full history `P`, exactly as in `AffineCombination.price`. -/
theorem price_tendsto_limitingValue (A : AffineCombination)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun m => A.price P m) (A.value P (limitingBelief P)) := by
  have hterms : ∀ l : List (EF × Sentence),
      Tendsto (fun m => (l.map (fun p => p.1.denote P * P m p.2)).sum) atTop
        (𝓝 ((l.map (fun p => p.1.denote P * limitingBelief P p.2)).sum)) := by
    intro l
    induction l with
    | nil => simp
    | cons p ps ih =>
        have hp := lic_limitingBelief_tendsto P DP hP hworld p.2
        have hmul : Tendsto (fun m => p.1.denote P * P m p.2) atTop
            (𝓝 (p.1.denote P * limitingBelief P p.2)) :=
          hp.const_mul (p.1.denote P)
        simpa using hmul.add ih
  rw [show (fun m => A.price P m) =
      fun m => A.const.denote P +
        (A.terms.map (fun p => p.1.denote P * P m p.2)).sum by
    funext m; rfl]
  rw [show A.value P (limitingBelief P) =
      A.const.denote P +
        (A.terms.map (fun p => p.1.denote P * limitingBelief P p.2)).sum by rfl]
  exact tendsto_const_nhds.add (hterms A.terms)

/-- Every tail infimum is below every later price. -/
theorem BoundedAffinePrices.futureLow_le_price
    {As : ℕ → AffineCombination} {P : History} (h : BoundedAffinePrices As P)
    {n m : ℕ} (hnm : n ≤ m) :
    affineFutureLow As P n ≤ (As n).price P m := by
  obtain ⟨B, _, hB⟩ := h
  apply csInf_le
  · refine ⟨-B, ?_⟩
    rintro x ⟨j, rfl⟩
    linarith [neg_abs_le ((As n).price P (n + j)), hB n (n + j)]
  · refine ⟨m - n, ?_⟩
    change (As n).price P (n + (m - n)) = (As n).price P m
    rw [Nat.add_sub_of_le hnm]

/-- Every later price is below the corresponding tail supremum. -/
theorem BoundedAffinePrices.price_le_futureHigh
    {As : ℕ → AffineCombination} {P : History} (h : BoundedAffinePrices As P)
    {n m : ℕ} (hnm : n ≤ m) :
    (As n).price P m ≤ affineFutureHigh As P n := by
  obtain ⟨B, _, hB⟩ := h
  apply le_csSup
  · refine ⟨B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans (hB n (n + j))
  · refine ⟨m - n, ?_⟩
    change (As n).price P (n + (m - n)) = (As n).price P m
    rw [Nat.add_sub_of_le hnm]

/-- The fixed-combination limit lies between its entire post-`n` price extrema. -/
theorem futureLow_le_limitingValue_le_futureHigh
    (As : ℕ → AffineCombination) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hbounded : BoundedAffinePrices As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    affineFutureLow As P n ≤ (As n).value P (limitingBelief P) ∧
      (As n).value P (limitingBelief P) ≤ affineFutureHigh As P n := by
  have ht := (As n).price_tendsto_limitingValue P DP hP hworld
  constructor
  · exact ge_of_tendsto ht (Filter.eventually_atTop.mpr
      ⟨n, fun m hm =>
        AffineCombination.BoundedAffinePrices.futureLow_le_price hbounded hm⟩)
  · exact le_of_tendsto ht (Filter.eventually_atTop.mpr
      ⟨n, fun m hm =>
        AffineCombination.BoundedAffinePrices.price_le_futureHigh hbounded hm⟩)

/-- Uniform bounds on the limiting values of a bounded affine sequence. -/
theorem BoundedAffinePrices.limitingValue_filterBounds
    {As : ℕ → AffineCombination} {P : History} (hbounded : BoundedAffinePrices As P)
    (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsBoundedUnder (· ≥ ·) atTop (fun n => (As n).value P (limitingBelief P)) ∧
      IsBoundedUnder (· ≤ ·) atTop (fun n => (As n).value P (limitingBelief P)) := by
  obtain ⟨B, _, hB⟩ := hbounded
  have hlo : ∀ n, -B ≤ (As n).value P (limitingBelief P) := by
    intro n
    exact ge_of_tendsto ((As n).price_tendsto_limitingValue P DP hP hworld)
      (Eventually.of_forall (fun m => by
        linarith [neg_abs_le ((As n).price P m), hB n m]))
  have hhi : ∀ n, (As n).value P (limitingBelief P) ≤ B := by
    intro n
    exact le_of_tendsto ((As n).price_tendsto_limitingValue P DP hP hworld)
      (Eventually.of_forall (fun m => (le_abs_self _).trans (hB n m)))
  exact ⟨isBoundedUnder_of_eventually_ge (Eventually.of_forall hlo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hhi)⟩

end AffineCombination

/-! ## Polynomial prefix portfolios

The paper's `app:peraffkno` component launched on day `k` buys every earlier member
which is then underpriced.  We package that finite mixture as one normalized affine
combination.  This lets the already verified `affpolymax` round-trip family supply the
economic contradiction, while the definitions below expose the whole polynomial
emission boundary rather than hiding it in a computability certificate.

The normalizer is the safe reciprocal of the sum of entry weights, not of the number of
prefix members.  Thus the portfolio has magnitude at most one, and whenever even one
entry signal is fully on, its total normalized entry weight is exactly one.
-/

namespace AffineCombination

/-- Length of member `j` in the day-`k` flattened affine prefix. -/
def persistenceMemberLength {As : ℕ → AffineCombination} (h : PolySequence As)
    (z : ℕ) : ℕ :=
  h.termCount z.unpair.2

/-- Total number of sentence terms in `A₀,…,Aₖ`. -/
def persistenceTermCount {As : ℕ → AffineCombination} (h : PolySequence As)
    (k : ℕ) : ℕ :=
  segPrefix (persistenceMemberLength h) k (k + 1)

/-- Prefix member containing flattened term `j`. -/
def persistenceMember {As : ℕ → AffineCombination} (h : PolySequence As)
    (k j : ℕ) : ℕ :=
  segLocate (persistenceMemberLength h) k j (k + 1)

/-- Offset within the prefix member containing flattened term `j`. -/
def persistenceOffset {As : ℕ → AffineCombination} (h : PolySequence As)
    (k j : ℕ) : ℕ :=
  j - segPrefix (persistenceMemberLength h) k (persistenceMember h k j)

/-- Continuous buy signal for prefix member `n` as assessed on day `k`.  Members at or
before `start` are suppressed; those finitely many members need not satisfy the eventual
limiting-value separation used in the contradiction. -/
def persistenceEntry (As : ℕ → AffineCombination) (start : ℕ) (low δ : ℚ)
    (k n : ℕ) : EF :=
  if start < n then buyIndF ((As n).priceFeature k) low δ else EF.const 0

/-- Sum of all prefix entry weights on day `k`. -/
def persistenceEntrySum (As : ℕ → AffineCombination) (start : ℕ) (low δ : ℚ)
    (k : ℕ) : EF :=
  (List.range (k + 1)).foldr
    (fun n acc => EF.add (persistenceEntry As start low δ k n) acc) (EF.const 0)

/-- Unnormalized constant term of the prefix portfolio. -/
def persistenceRawConst (As : ℕ → AffineCombination) (start : ℕ) (low δ : ℚ)
    (k : ℕ) : EF :=
  (List.range (k + 1)).foldr
    (fun n acc => EF.add
      (EF.mul (persistenceEntry As start low δ k n) (As n).const) acc)
    (EF.const 0)

/-- Safe portfolio normalizer `1 / max(1, sum entry weights)`. -/
def persistenceNorm (As : ℕ → AffineCombination) (start : ℕ) (low δ : ℚ)
    (k : ℕ) : EF :=
  EF.safeRecip (persistenceEntrySum As start low δ k)

/-- Normalized coefficient at a flattened prefix index. -/
def persistenceCoefficient {As : ℕ → AffineCombination} (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (z : ℕ) : EF :=
  let k := z.unpair.1
  let j := z.unpair.2
  let n := persistenceMember h k j
  let r := persistenceOffset h k j
  EF.mul (persistenceNorm As start low δ k)
    (EF.mul (persistenceEntry As start low δ k n)
      (h.coefficient (Nat.pair n r)))

/-- Sentence at a flattened prefix index. -/
def persistenceSentence {As : ℕ → AffineCombination} (h : PolySequence As)
    (z : ℕ) : Sentence :=
  let k := z.unpair.1
  let j := z.unpair.2
  h.sentence (Nat.pair (persistenceMember h k j) (persistenceOffset h k j))

/-- The normalized day-`k` portfolio of all prefix members whose day-`k` prices trigger
the continuous underpricing signal. -/
def persistencePortfolio {As : ℕ → AffineCombination} (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (k : ℕ) : AffineCombination where
  const := EF.mul (persistenceNorm As start low δ k)
    (persistenceRawConst As start low δ k)
  terms := (List.range (persistenceTermCount h k)).map (fun j =>
    (persistenceCoefficient h start low δ (Nat.pair k j),
      persistenceSentence h (Nat.pair k j)))

theorem persistenceEntry_serialize (As : ℕ → AffineCombination)
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) :
    PolySegStream (fun z =>
      (persistenceEntry As start low δ z.unpair.1 z.unpair.2).serialize) := by
  have hprice := h.priceFeature_polySeg.comp (PolyFueled.right.pair PolyFueled.left)
  have hbuy := PolySegStream.serialize_buyIndF hprice low δ
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have htest := subc_polyFueled.comp
    (PolyFueled.right.pair (PolyFueled.const start))
  refine PolySegStream.of_eq (PolySegStream.ifZero hzero hbuy htest) ?_
  intro z
  simp only [Function.comp_apply, Nat.unpair_pair]
  by_cases hs : start < z.unpair.2
  · rw [if_neg (by omega), persistenceEntry, if_pos hs]
  · rw [if_pos (by omega), persistenceEntry, if_neg hs]

theorem persistenceEntrySum_serialize (As : ℕ → AffineCombination)
    (start : ℕ) (low δ : ℚ) (k : ℕ) :
    (persistenceEntrySum As start low δ k).serialize =
      (List.range (k + 1)).flatMap
          (fun n => (persistenceEntry As start low δ k n).serialize) ++
        (EF.const 0).serialize ++ List.replicate (k + 1) 2 := by
  simp only [persistenceEntrySum]
  have aux : ∀ l : List ℕ,
      (l.foldr (fun n acc => EF.add
        (persistenceEntry As start low δ k n) acc) (EF.const 0)).serialize =
        l.flatMap (fun n => (persistenceEntry As start low δ k n).serialize) ++
          (EF.const 0).serialize ++ List.replicate l.length 2 := by
    intro l
    induction l with
    | nil => simp [EF.serialize]
    | cons a l ih =>
        simp only [List.foldr_cons, List.flatMap_cons, List.length_cons]
        rw [show (EF.add (persistenceEntry As start low δ k a)
            (l.foldr (fun n acc => EF.add
              (persistenceEntry As start low δ k n) acc) (EF.const 0))).serialize =
            (persistenceEntry As start low δ k a).serialize ++
              (l.foldr (fun n acc => EF.add
                (persistenceEntry As start low δ k n) acc) (EF.const 0)).serialize ++ [2] by
          simp [EF.serialize]]
        rw [ih]
        simp [List.replicate_succ', List.append_assoc]
  simpa using aux (List.range (k + 1))

theorem persistenceEntrySum_polySeg (As : ℕ → AffineCombination)
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) :
    PolySegStream (fun k => (persistenceEntrySum As start low δ k).serialize) := by
  have hentries := PolySegStream.concatVar
    (persistenceEntry_serialize As h start low δ) PolyFueled.id.succ_comp
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have htags := PolySegStream.repeatTag 2 PolyFueled.id.succ_comp
  refine PolySegStream.of_eq ((hentries.append hzero).append htags) ?_
  intro k
  rw [persistenceEntrySum_serialize]
  simp only [Nat.unpair_pair]

theorem persistenceNorm_polySeg (As : ℕ → AffineCombination)
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) :
    PolySegStream (fun k => (persistenceNorm As start low δ k).serialize) := by
  refine PolySegStream.of_eq
    ((persistenceEntrySum_polySeg As h start low δ).append
      (PolySegStream.ofTokenStream (PolyTokenStream.const 5))) ?_
  intro k
  simp [persistenceNorm, EF.serialize]

theorem persistenceRawConst_serialize (As : ℕ → AffineCombination)
    (start : ℕ) (low δ : ℚ) (k : ℕ) :
    (persistenceRawConst As start low δ k).serialize =
      (List.range (k + 1)).flatMap (fun n =>
          (EF.mul (persistenceEntry As start low δ k n) (As n).const).serialize) ++
        (EF.const 0).serialize ++ List.replicate (k + 1) 2 := by
  simp only [persistenceRawConst]
  have aux : ∀ l : List ℕ,
      (l.foldr (fun n acc => EF.add
        (EF.mul (persistenceEntry As start low δ k n) (As n).const) acc)
        (EF.const 0)).serialize =
        l.flatMap (fun n =>
          (EF.mul (persistenceEntry As start low δ k n) (As n).const).serialize) ++
          (EF.const 0).serialize ++ List.replicate l.length 2 := by
    intro l
    induction l with
    | nil => simp [EF.serialize]
    | cons a l ih =>
        simp only [List.foldr_cons, List.flatMap_cons, List.length_cons]
        rw [show (EF.add
            (EF.mul (persistenceEntry As start low δ k a) (As a).const)
            (l.foldr (fun n acc => EF.add
              (EF.mul (persistenceEntry As start low δ k n) (As n).const) acc)
              (EF.const 0))).serialize =
            (EF.mul (persistenceEntry As start low δ k a) (As a).const).serialize ++
              (l.foldr (fun n acc => EF.add
                (EF.mul (persistenceEntry As start low δ k n) (As n).const) acc)
                (EF.const 0)).serialize ++ [2] by simp [EF.serialize]]
        rw [ih]
        simp [List.replicate_succ', List.append_assoc]
  simpa using aux (List.range (k + 1))

theorem persistenceRawConst_polySeg (As : ℕ → AffineCombination)
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) :
    PolySegStream (fun k => (persistenceRawConst As start low δ k).serialize) := by
  have hblock := PolySegStream.serialize_mul
    (persistenceEntry_serialize As h start low δ)
    (h.const_poly.comp PolyFueled.right)
  have hblocks := PolySegStream.concatVar hblock PolyFueled.id.succ_comp
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have htags := PolySegStream.repeatTag 2 PolyFueled.id.succ_comp
  refine PolySegStream.of_eq ((hblocks.append hzero).append htags) ?_
  intro k
  rw [persistenceRawConst_serialize]
  simp only [Nat.unpair_pair]

theorem PolySequence.persistenceTermCount_poly {As : ℕ → AffineCombination}
    (h : PolySequence As) : ∃ c, PolyFueled c (persistenceTermCount h) := by
  obtain ⟨ccount, hcount⟩ := h.termCount_poly
  have hlen : PolyFueled (ccount.comp Nat.Partrec.Code.right)
      (persistenceMemberLength h) := by
    exact (hcount.comp PolyFueled.right).of_eq (fun z => rfl)
  obtain ⟨cprefix, hprefix⟩ := segPrefix_polyFueled hlen
  exact ⟨cprefix.comp
      ((Nat.Partrec.Code.left.pair Nat.Partrec.Code.right).pair
        (Nat.Partrec.Code.succ.comp
          (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right))),
    (hprefix.comp (PolyFueled.id.pair PolyFueled.id.succ_comp)).of_eq
      (fun k => by simp [persistenceTermCount])⟩

attribute [local irreducible] Nat.sqrt in
theorem prefixMember_poly (count : ℕ → ℕ)
    (hcount : ∃ c, PolyFueled c count) : ∃ c, PolyFueled c (fun z =>
      segLocate (fun q => count q.unpair.2) z.unpair.1 z.unpair.2
        (z.unpair.1 + 1)) := by
  obtain ⟨ccount, hcount⟩ := hcount
  have hlen : PolyFueled (ccount.comp Nat.Partrec.Code.right)
      (fun z => count z.unpair.2) := hcount.comp PolyFueled.right
  obtain ⟨clocate, hlocate⟩ := segLocate_polyFueled hlen
  have hinput := (PolyFueled.left.pair PolyFueled.right).pair
    PolyFueled.left.succ_comp
  refine ⟨clocate.comp
    (((Nat.Partrec.Code.left.pair Nat.Partrec.Code.right).pair
      (Nat.Partrec.Code.succ.comp Nat.Partrec.Code.left))), ?_⟩
  simpa only [Function.comp_apply, Nat.unpair_pair] using hlocate.comp hinput

attribute [local irreducible] Nat.sqrt in
theorem prefixOffset_poly (count : ℕ → ℕ)
    (hcount : ∃ c, PolyFueled c count) : ∃ c, PolyFueled c (fun z =>
      z.unpair.2 - segPrefix (fun q => count q.unpair.2) z.unpair.1
        (segLocate (fun q => count q.unpair.2) z.unpair.1 z.unpair.2
          (z.unpair.1 + 1))) := by
  obtain ⟨ccount, hcountPF⟩ := hcount
  have hlen : PolyFueled (ccount.comp Nat.Partrec.Code.right)
      (fun z => count z.unpair.2) := hcountPF.comp PolyFueled.right
  obtain ⟨cprefix, hprefix⟩ := segPrefix_polyFueled hlen
  obtain ⟨cmember, hmember⟩ := prefixMember_poly count ⟨ccount, hcountPF⟩
  have hp := hprefix.comp (PolyFueled.left.pair hmember)
  refine ⟨subc.comp (Nat.Partrec.Code.right.pair
    (cprefix.comp (Nat.Partrec.Code.left.pair cmember))), ?_⟩
  simpa only [Function.comp_apply, Nat.unpair_pair] using
    subc_polyFueled.comp (PolyFueled.right.pair hp)

theorem PolySequence.persistenceMember_poly {As : ℕ → AffineCombination}
    (h : PolySequence As) : ∃ c, PolyFueled c (fun z =>
      persistenceMember h z.unpair.1 z.unpair.2) := by
  simpa [persistenceMember, persistenceMemberLength] using
    prefixMember_poly h.termCount h.termCount_poly

theorem PolySequence.persistenceOffset_poly {As : ℕ → AffineCombination}
    (h : PolySequence As) : ∃ c, PolyFueled c (fun z =>
      persistenceOffset h z.unpair.1 z.unpair.2) := by
  simpa [persistenceOffset, persistenceMember, persistenceMemberLength] using
    prefixOffset_poly h.termCount h.termCount_poly

theorem PolySequence.persistenceMember_lt {As : ℕ → AffineCombination} (h : PolySequence As)
    {k j : ℕ} (hj : j < persistenceTermCount h k) :
    persistenceMember h k j < k + 1 := by
  let lenFn := persistenceMemberLength h
  let n := segLocate lenFn k j (k + 1)
  have hnle : n ≤ k + 1 := segLocate_le lenFn k j (k + 1)
  have hnstart : segPrefix lenFn k n ≤ j := (segLocate_spec lenFn k j (k + 1)).1
  have hj' : j < segPrefix lenFn k (k + 1) := by
    simpa [persistenceTermCount, lenFn] using hj
  have hnne : n ≠ k + 1 := by
    intro heq
    rw [heq] at hnstart
    exact (not_le_of_gt hj') hnstart
  change n < k + 1
  omega

theorem PolySequence.persistenceOffset_lt {As : ℕ → AffineCombination} (h : PolySequence As)
    {k j : ℕ} (hj : j < persistenceTermCount h k) :
    persistenceOffset h k j < h.termCount (persistenceMember h k j) := by
  let lenFn := persistenceMemberLength h
  let n := segLocate lenFn k j (k + 1)
  have hnlt : n < k + 1 := by
    simpa [persistenceMember, lenFn] using h.persistenceMember_lt hj
  have hmax := (segLocate_spec lenFn k j (k + 1)).2
  have hstart : segPrefix lenFn k n ≤ j :=
    (segLocate_spec lenFn k j (k + 1)).1
  have hnext : j < segPrefix lenFn k (n + 1) := by
    by_contra hnot
    have hle : segPrefix lenFn k (n + 1) ≤ j := le_of_not_gt hnot
    have := hmax (n + 1) (by omega) hle
    omega
  rw [segPrefix_succ] at hnext
  have hoff : j - segPrefix lenFn k n < lenFn (Nat.pair k n) := by omega
  simpa [persistenceOffset, persistenceMember, lenFn, n,
    persistenceMemberLength] using hoff

theorem PolySequence.persistenceEntry_rank {As : ℕ → AffineCombination}
    (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) {k n : ℕ} (hn : n ≤ k) :
    (persistenceEntry As start low δ k n).rank ≤ k := by
  by_cases hs : start < n
  · simp only [persistenceEntry, hs, if_true, buyIndF_rank]
    exact (As n).priceFeature_rank hn (h.const_rank n) (h.terms_rank n)
  · simp [persistenceEntry, hs, EF.rank]

theorem PolySequence.persistenceEntry_closed {As : ℕ → AffineCombination}
    (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (k n : ℕ) (ρ : List ℝ) (V : History) :
    (persistenceEntry As start low δ k n).denoteWith ρ V =
      (persistenceEntry As start low δ k n).denote V := by
  by_cases hs : start < n
  · simp only [persistenceEntry, hs, if_true, buyIndF, clip01, efMin,
      EF.denoteWith, EF.denote_max, EF.denote_mul, EF.denote_add, EF.denote_const,
      Pi.mul_apply, Pi.add_apply]
    rw [h.priceFeature_closed n k ρ V]
  · simp [persistenceEntry, hs, EF.denoteWith]

theorem PolySequence.persistenceEntrySum_rank {As : ℕ → AffineCombination}
    (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (k : ℕ) :
    (persistenceEntrySum As start low δ k).rank ≤ k := by
  simp only [persistenceEntrySum]
  have aux : ∀ l : List ℕ, (∀ n ∈ l, n ≤ k) →
      (l.foldr (fun n acc => EF.add (persistenceEntry As start low δ k n) acc)
        (EF.const 0)).rank ≤ k := by
    intro l hl
    induction l with
    | nil => simp [EF.rank]
    | cons n l ih =>
        simp only [List.foldr_cons, EF.rank]
        exact Nat.max_le.mpr ⟨h.persistenceEntry_rank start low δ (hl n (by simp)),
          ih (fun m hm => hl m (by simp [hm]))⟩
  exact aux (List.range (k + 1)) (fun n hn => by simp only [List.mem_range] at hn; omega)

theorem PolySequence.persistenceRawConst_rank {As : ℕ → AffineCombination}
    (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (k : ℕ) :
    (persistenceRawConst As start low δ k).rank ≤ k := by
  simp only [persistenceRawConst]
  have aux : ∀ l : List ℕ, (∀ n ∈ l, n ≤ k) →
      (l.foldr (fun n acc => EF.add
        (EF.mul (persistenceEntry As start low δ k n) (As n).const) acc)
        (EF.const 0)).rank ≤ k := by
    intro l hl
    induction l with
    | nil => simp [EF.rank]
    | cons n l ih =>
        simp only [List.foldr_cons, EF.rank]
        exact Nat.max_le.mpr ⟨Nat.max_le.mpr
          ⟨h.persistenceEntry_rank start low δ (hl n (by simp)),
            (h.const_rank n).trans (hl n (by simp))⟩,
          ih (fun m hm => hl m (by simp [hm]))⟩
  exact aux (List.range (k + 1)) (fun n hn => by simp only [List.mem_range] at hn; omega)

theorem PolySequence.persistenceEntrySum_closed {As : ℕ → AffineCombination}
    (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (k : ℕ) (ρ : List ℝ) (V : History) :
    (persistenceEntrySum As start low δ k).denoteWith ρ V =
      (persistenceEntrySum As start low δ k).denote V := by
  simp only [persistenceEntrySum]
  induction List.range (k + 1) with
  | nil => rfl
  | cons n l ih =>
      simp only [List.foldr_cons, EF.denoteWith, EF.denote_add, Pi.add_apply]
      rw [h.persistenceEntry_closed start low δ k n ρ V, ih]

theorem PolySequence.persistenceRawConst_closed {As : ℕ → AffineCombination}
    (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (k : ℕ) (ρ : List ℝ) (V : History) :
    (persistenceRawConst As start low δ k).denoteWith ρ V =
      (persistenceRawConst As start low δ k).denote V := by
  simp only [persistenceRawConst]
  induction List.range (k + 1) with
  | nil => rfl
  | cons n l ih =>
      simp only [List.foldr_cons, EF.denoteWith, EF.denote_add, EF.denote_mul,
        Pi.add_apply, Pi.mul_apply]
      rw [h.persistenceEntry_closed start low δ k n ρ V, h.const_closed n ρ V, ih]

theorem PolySequence.persistenceNorm_closed {As : ℕ → AffineCombination}
    (h : PolySequence As)
    (start : ℕ) (low δ : ℚ) (k : ℕ) (ρ : List ℝ) (V : History) :
    (persistenceNorm As start low δ k).denoteWith ρ V =
      (persistenceNorm As start low δ k).denote V := by
  simp only [persistenceNorm, EF.denoteWith, EF.denote_safeRecip]
  rw [h.persistenceEntrySum_closed start low δ k ρ V]

/-- The normalized prefix portfolios are themselves a polynomial affine sequence.  This
is the efficient-emission certificate consumed by `affpolymax`; it explicitly emits the
flattened prefix term count, coefficient syntax, and sentence codes. -/
noncomputable def PolySequence.persistencePortfolioPoly {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) :
    PolySequence (persistencePortfolio h start low δ) := by
  let ccount := Classical.choose h.persistenceTermCount_poly
  have hcount := Classical.choose_spec h.persistenceTermCount_poly
  let cmember := Classical.choose h.persistenceMember_poly
  have hmember := Classical.choose_spec h.persistenceMember_poly
  let coffset := Classical.choose h.persistenceOffset_poly
  have hoffset := Classical.choose_spec h.persistenceOffset_poly
  let memberPF := hmember
  let offsetPF := hoffset
  let canonicalPF := memberPF.pair offsetPF
  have hentry := (persistenceEntry_serialize As h start low δ).comp
    (PolyFueled.left.pair memberPF)
  have hcoeff := h.coefficient_poly.comp canonicalPF
  have hnorm := (persistenceNorm_polySeg As h start low δ).comp PolyFueled.left
  have hcoefficient := PolySegStream.serialize_mul hnorm
    (PolySegStream.serialize_mul hentry hcoeff)
  let csentence := Classical.choose h.sentence_poly
  have hsentence := Classical.choose_spec h.sentence_poly
  have hsentencePF := hsentence.comp canonicalPF
  refine
    { termCount := persistenceTermCount h
      coefficient := persistenceCoefficient h start low δ
      sentence := persistenceSentence h
      termCount_poly := ⟨ccount, hcount⟩
      const_poly := PolySegStream.serialize_mul
        (persistenceNorm_polySeg As h start low δ)
        (persistenceRawConst_polySeg As h start low δ)
      coefficient_poly := ?_
      sentence_poly := ⟨csentence.comp (cmember.pair coffset), ?_⟩
      terms_eq := fun k => rfl
      const_rank := ?_
      coefficient_rank := ?_
      const_closed := ?_
      coefficient_closed := ?_ }
  · simpa [persistenceCoefficient] using hcoefficient
  · simpa [persistenceSentence] using hsentencePF
  · intro k
    simp only [persistencePortfolio, EF.rank, persistenceNorm, EF.rank_safeRecip]
    exact Nat.max_le.mpr ⟨h.persistenceEntrySum_rank start low δ k,
      h.persistenceRawConst_rank start low δ k⟩
  · intro k j hj
    have hnlt := h.persistenceMember_lt hj
    have hn : persistenceMember h k j ≤ k := by omega
    have hr := h.persistenceOffset_lt hj
    simp only [persistenceCoefficient, Nat.unpair_pair, EF.rank, persistenceNorm,
      EF.rank_safeRecip]
    exact Nat.max_le.mpr ⟨h.persistenceEntrySum_rank start low δ k,
      Nat.max_le.mpr ⟨h.persistenceEntry_rank start low δ hn,
        (h.coefficient_rank (persistenceMember h k j) (persistenceOffset h k j) hr).trans hn⟩⟩
  · intro k ρ V
    simp only [persistencePortfolio, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [h.persistenceNorm_closed start low δ k ρ V,
      h.persistenceRawConst_closed start low δ k ρ V]
  · intro z ρ V
    simp only [persistenceCoefficient, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [h.persistenceNorm_closed start low δ z.unpair.1 ρ V,
      h.persistenceEntry_closed start low δ z.unpair.1
        (persistenceMember h z.unpair.1 z.unpair.2) ρ V,
      h.coefficient_closed
        (Nat.pair (persistenceMember h z.unpair.1 z.unpair.2)
          (persistenceOffset h z.unpair.1 z.unpair.2)) ρ V]

/-- Type-generic form of the prefix-length lemma used by the serialized token emitter. -/
theorem length_flatMap_eq_segPrefix_any {α : Type*} (seg : ℕ → List α)
    (lenFn : ℕ → ℕ) (n : ℕ)
    (hlen : ∀ j, (seg (Nat.pair n j)).length = lenFn (Nat.pair n j)) : ∀ k,
    ((List.range k).flatMap (fun j => seg (Nat.pair n j))).length =
      segPrefix lenFn n k
  | 0 => by simp
  | k + 1 => by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.length_append, length_flatMap_eq_segPrefix_any seg lenFn n hlen k,
        hlen, segPrefix_succ]

/-- Locate an element in a variable-width flattened prefix, for arbitrary element type. -/
theorem getD_flatMap_of_prefix_any {α : Type*} (seg : ℕ → List α)
    (lenFn : ℕ → ℕ) (d : α) (n cnt i j : ℕ)
    (hlen : ∀ k, (seg (Nat.pair n k)).length = lenFn (Nat.pair n k))
    (hj : j < cnt) (hlo : segPrefix lenFn n j ≤ i)
    (hhi : i < segPrefix lenFn n (j + 1)) :
    ((List.range cnt).flatMap (fun k => seg (Nat.pair n k))).getD i d =
      (seg (Nat.pair n j)).getD (i - segPrefix lenFn n j) d := by
  induction cnt generalizing j i with
  | zero => omega
  | succ cnt ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      rcases Nat.eq_or_lt_of_le (show j ≤ cnt by omega) with rfl | hjlt
      · rw [List.getD_append_right]
        · rw [length_flatMap_eq_segPrefix_any seg lenFn n hlen]
        · rw [length_flatMap_eq_segPrefix_any seg lenFn n hlen]
          exact hlo
      · rw [List.getD_append]
        · exact ih i j hjlt hlo hhi
        · rw [length_flatMap_eq_segPrefix_any seg lenFn n hlen]
          exact lt_of_lt_of_le hhi (segPrefix_mono lenFn n (by omega))

/-- The flattened representation used by `persistencePortfolio` is exactly the nested
prefix mixture from the paper. -/
theorem persistencePortfolio_terms_flatMap {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (k : ℕ) :
    (persistencePortfolio h start low δ k).terms =
      (List.range (k + 1)).flatMap (fun n => (As n).terms.map (fun p =>
        (EF.mul (persistenceNorm As start low δ k)
          (EF.mul (persistenceEntry As start low δ k n) p.1), p.2))) := by
  let lenFn := persistenceMemberLength h
  let seg : ℕ → List (EF × Sentence) := fun z =>
    (As z.unpair.2).terms.map (fun p =>
      (EF.mul (persistenceNorm As start low δ k)
        (EF.mul (persistenceEntry As start low δ k z.unpair.2) p.1), p.2))
  have hlen : ∀ n, (seg (Nat.pair k n)).length = lenFn (Nat.pair k n) := by
    intro n
    simp [seg, lenFn, persistenceMemberLength, h.terms_eq]
  have hlength :
      ((List.range (k + 1)).flatMap (fun n => seg (Nat.pair k n))).length =
        persistenceTermCount h k := by
    simpa [persistenceTermCount, lenFn] using
      length_flatMap_eq_segPrefix_any seg lenFn k hlen (k + 1)
  change (List.range (persistenceTermCount h k)).map (fun j =>
      (persistenceCoefficient h start low δ (Nat.pair k j),
        persistenceSentence h (Nat.pair k j))) = _
  rw [show (List.range (k + 1)).flatMap (fun n => (As n).terms.map (fun p =>
      (EF.mul (persistenceNorm As start low δ k)
        (EF.mul (persistenceEntry As start low δ k n) p.1), p.2))) =
      (List.range (k + 1)).flatMap (fun n => seg (Nat.pair k n)) by
    simp [seg]]
  apply List.ext_get
  · simpa using hlength.symm
  · intro j hjleft hjright
    have hj : j < persistenceTermCount h k := by simpa using hjleft
    let n := persistenceMember h k j
    let r := persistenceOffset h k j
    have hnlt : n < k + 1 := by simpa [n] using h.persistenceMember_lt hj
    have hrlt : r < h.termCount n := by simpa [n, r] using h.persistenceOffset_lt hj
    have hlo : segPrefix lenFn k n ≤ j := by
      simpa [n, persistenceMember] using
        (segLocate_spec lenFn k j (k + 1)).1
    have hhi : j < segPrefix lenFn k (n + 1) := by
      by_contra hnot
      have hle := le_of_not_gt hnot
      have hmax := (segLocate_spec lenFn k j (k + 1)).2
      have hn := hmax (n + 1) (by omega) hle
      have hnid : n = segLocate lenFn k j (k + 1) := by
        simp [n, persistenceMember, lenFn]
      omega
    let d : EF × Sentence := (EF.const 0, h.sentence 0)
    have hget := getD_flatMap_of_prefix_any seg lenFn d k (k + 1) j n
      hlen hnlt hlo hhi
    have hright :
        ((List.range (k + 1)).flatMap (fun q => seg (Nat.pair k q))).getD j d =
          (seg (Nat.pair k n)).getD r d := by
      simpa [r, persistenceOffset, n, lenFn] using hget
    have hgetD := List.getD_eq_get
      (l := (List.range (k + 1)).flatMap (fun q => seg (Nat.pair k q)))
      (d := d) ⟨j, hjright⟩
    rw [← hgetD, hright]
    rw [show (seg (Nat.pair k n)).getD r d =
        (EF.mul (persistenceNorm As start low δ k)
          (EF.mul (persistenceEntry As start low δ k n)
            (h.coefficient (Nat.pair n r))),
          h.sentence (Nat.pair n r)) by
      simp only [seg, Nat.unpair_pair, h.terms_eq, List.getD_map]
      rw [List.getD_eq_getElem]
      · simp
      · simpa using hrlt]
    simp [persistenceCoefficient, persistenceSentence, n, r]

/-- Add a rational constant to an affine combination without changing its share risk. -/
def addConst (q : ℚ) (A : AffineCombination) : AffineCombination where
  const := EF.add A.const (EF.const q)
  terms := A.terms

theorem addConst_value (q : ℚ) (A : AffineCombination) (V : History) (w : Valuation) :
    (A.addConst q).value V w = A.value V w + q := by
  simp [addConst, value]
  ring

theorem addConst_price (q : ℚ) (A : AffineCombination) (V : History) (n : ℕ) :
    (A.addConst q).price V n = A.price V n + q := by
  simp [price, addConst_value]

theorem addConst_magnitude (q : ℚ) (A : AffineCombination) (V : History) :
    (A.addConst q).magnitude V = A.magnitude V := rfl

theorem BoundedAffinePrices.addConst {As : ℕ → AffineCombination} {V : History}
    (h : BoundedAffinePrices As V) (q : ℚ) :
    BoundedAffinePrices (fun n => (As n).addConst q) V := by
  obtain ⟨B, hB0, hB⟩ := h
  refine ⟨B + |(q : ℝ)|, add_nonneg hB0 (abs_nonneg _), fun n m => ?_⟩
  rw [addConst_price]
  exact (abs_add_le _ _).trans (add_le_add (hB n m) le_rfl)

/-- Polynomial affine sequences are closed under a fixed rational translation. -/
def PolySequence.addConst {As : ℕ → AffineCombination} (h : PolySequence As) (q : ℚ) :
    PolySequence (fun n => (As n).addConst q) where
  termCount := h.termCount
  coefficient := h.coefficient
  sentence := h.sentence
  termCount_poly := h.termCount_poly
  const_poly := PolySegStream.serialize_add h.const_poly
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const q))
  coefficient_poly := h.coefficient_poly
  sentence_poly := h.sentence_poly
  terms_eq := h.terms_eq
  const_rank := by
    intro n
    change (EF.add (As n).const (EF.const q)).rank ≤ n
    simp only [EF.rank]
    exact Nat.max_le.mpr ⟨h.const_rank n, by simp⟩
  coefficient_rank := h.coefficient_rank
  const_closed := by
    intro n ρ V
    change (EF.add (As n).const (EF.const q)).denoteWith ρ V =
      (EF.add (As n).const (EF.const q)).denote V
    simp only [EF.denoteWith, EF.denote_add, EF.denote_const, Pi.add_apply]
    rw [h.const_closed n ρ V]
  coefficient_closed := h.coefficient_closed

theorem persistenceEntry_nonneg (As : ℕ → AffineCombination) (start : ℕ)
    (low δ : ℚ) (V : History) (k n : ℕ) :
    0 ≤ (persistenceEntry As start low δ k n).denote V := by
  by_cases hs : start < n
  · simpa [persistenceEntry, hs] using
      (buyIndF_mem ((As n).priceFeature k) low δ V).1
  · simp [persistenceEntry, hs]

theorem persistenceEntry_le_one (As : ℕ → AffineCombination) (start : ℕ)
    (low δ : ℚ) (V : History) (k n : ℕ) :
    (persistenceEntry As start low δ k n).denote V ≤ 1 := by
  by_cases hs : start < n
  · simpa [persistenceEntry, hs] using
      (buyIndF_mem ((As n).priceFeature k) low δ V).2
  · simp [persistenceEntry, hs]

theorem persistenceEntrySum_denote (As : ℕ → AffineCombination) (start : ℕ)
    (low δ : ℚ) (V : History) (k : ℕ) :
    (persistenceEntrySum As start low δ k).denote V =
      ((List.range (k + 1)).map (fun n =>
        (persistenceEntry As start low δ k n).denote V)).sum := by
  simp only [persistenceEntrySum]
  induction List.range (k + 1) with
  | nil => simp
  | cons n l ih =>
      simp only [List.foldr_cons, EF.denote_add, Pi.add_apply, List.map_cons,
        List.sum_cons, ih]

theorem persistenceRawConst_denote (As : ℕ → AffineCombination) (start : ℕ)
    (low δ : ℚ) (V : History) (k : ℕ) :
    (persistenceRawConst As start low δ k).denote V =
      ((List.range (k + 1)).map (fun n =>
        (persistenceEntry As start low δ k n).denote V * (As n).const.denote V)).sum := by
  simp only [persistenceRawConst]
  induction List.range (k + 1) with
  | nil => simp
  | cons n l ih =>
      simp only [List.foldr_cons, EF.denote_add, EF.denote_mul, Pi.add_apply,
        Pi.mul_apply, List.map_cons, List.sum_cons, ih]

theorem persistenceEntrySum_nonneg (As : ℕ → AffineCombination) (start : ℕ)
    (low δ : ℚ) (V : History) (k : ℕ) :
    0 ≤ (persistenceEntrySum As start low δ k).denote V := by
  rw [persistenceEntrySum_denote]
  exact List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨n, _, rfl⟩ := hx
    exact persistenceEntry_nonneg As start low δ V k n)

theorem persistenceNorm_pos (As : ℕ → AffineCombination) (start : ℕ)
    (low δ : ℚ) (V : History) (k : ℕ) :
    0 < (persistenceNorm As start low δ k).denote V := by
  rw [persistenceNorm, EF.denote_safeRecip]
  positivity

theorem persistenceNorm_mul_entrySum_le_one (As : ℕ → AffineCombination)
    (start : ℕ) (low δ : ℚ) (V : History) (k : ℕ) :
    (persistenceNorm As start low δ k).denote V *
      (persistenceEntrySum As start low δ k).denote V ≤ 1 := by
  let s := (persistenceEntrySum As start low δ k).denote V
  have hs0 : 0 ≤ s := persistenceEntrySum_nonneg As start low δ V k
  rw [persistenceNorm, EF.denote_safeRecip]
  change (max 1 s)⁻¹ * s ≤ 1
  by_cases hs : s ≤ 1
  · rw [max_eq_left hs]
    simpa using hs
  · have hs1 : 1 ≤ s := le_of_not_ge hs
    rw [max_eq_right hs1, inv_mul_cancel₀ (by linarith : s ≠ 0)]

theorem persistenceNorm_mul_entrySum_eq_one_of_entry_one
    (As : ℕ → AffineCombination) (start : ℕ) (low δ : ℚ) (V : History)
    {k n : ℕ} (hn : n < k + 1)
    (hone : (persistenceEntry As start low δ k n).denote V = 1) :
    (persistenceNorm As start low δ k).denote V *
      (persistenceEntrySum As start low δ k).denote V = 1 := by
  let s := (persistenceEntrySum As start low δ k).denote V
  have hs1 : 1 ≤ s := by
    dsimp only [s]
    rw [persistenceEntrySum_denote]
    have hnmem : n ∈ List.range (k + 1) := by simp [hn]
    calc
      1 = (persistenceEntry As start low δ k n).denote V := hone.symm
      _ ≤ ((List.range (k + 1)).map (fun q =>
          (persistenceEntry As start low δ k q).denote V)).sum := by
        apply List.single_le_sum
        · intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨q, _, rfl⟩ := hx
          exact persistenceEntry_nonneg As start low δ V k q
        · exact List.mem_map.mpr ⟨n, hnmem, rfl⟩
  rw [persistenceNorm, EF.denote_safeRecip]
  change (max 1 s)⁻¹ * s = 1
  rw [max_eq_right hs1, inv_mul_cancel₀ (by linarith : s ≠ 0)]

/-- Exact denotation of the normalized prefix portfolio. -/
theorem persistencePortfolio_value {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (V : History)
    (w : Valuation) (k : ℕ) :
    (persistencePortfolio h start low δ k).value V w =
      (persistenceNorm As start low δ k).denote V *
        ((List.range (k + 1)).map (fun n =>
          (persistenceEntry As start low δ k n).denote V *
            (As n).value V w)).sum := by
  rw [value, persistencePortfolio_terms_flatMap]
  simp only [persistencePortfolio, EF.denote_mul, Pi.mul_apply]
  rw [persistenceRawConst_denote]
  let N := (persistenceNorm As start low δ k).denote V
  let e : ℕ → ℝ := fun n => (persistenceEntry As start low δ k n).denote V
  let termValue : ℕ → ℝ := fun n =>
    ((As n).terms.map (fun p => p.1.denote V * w p.2)).sum
  let scaledTerms : ℕ → List (EF × Sentence) := fun n => (As n).terms.map (fun p =>
    (EF.mul (persistenceNorm As start low δ k)
      (EF.mul (persistenceEntry As start low δ k n) p.1), p.2))
  have hone : ∀ n,
      ((scaledTerms n).map (fun p => p.1.denote V * w p.2)).sum =
        N * (e n * termValue n) := by
    intro n
    simp only [scaledTerms, List.map_map, Function.comp_def, EF.denote_mul,
      Pi.mul_apply, N, e]
    rw [show (As n).terms.map (fun p =>
        ((persistenceNorm As start low δ k).denote V *
          ((persistenceEntry As start low δ k n).denote V * p.1.denote V)) * w p.2) =
        (As n).terms.map (fun p =>
          ((persistenceNorm As start low δ k).denote V *
            (persistenceEntry As start low δ k n).denote V) *
              (p.1.denote V * w p.2)) by
      apply List.map_congr_left
      intro p hp
      ring]
    rw [List.sum_map_mul_left]
    ring
  have hterms : ∀ l : List ℕ,
      (((l.flatMap scaledTerms).map (fun p => p.1.denote V * w p.2)).sum =
        N * (l.map (fun n => e n * termValue n)).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons n l ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons, hone n, ih]
        ring
  change N * ((List.range (k + 1)).map
      (fun n => e n * (As n).const.denote V)).sum +
      (((List.range (k + 1)).flatMap scaledTerms).map
        (fun p => p.1.denote V * w p.2)).sum =
      N * ((List.range (k + 1)).map (fun n => e n * (As n).value V w)).sum
  rw [hterms]
  have hcombine : ∀ l : List ℕ,
      ((List.range (k + 1)).map (fun n => e n * (As n).const.denote V)).sum +
          ((List.range (k + 1)).map (fun n => e n * termValue n)).sum =
        ((List.range (k + 1)).map (fun n => e n * (As n).value V w)).sum := by
    intro l
    clear l
    induction List.range (k + 1) with
    | nil => simp
    | cons n l ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [← ih]
        simp only [value, termValue]
        ring
  rw [← mul_add, hcombine (List.range (k + 1))]

theorem persistencePortfolio_price {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (V : History)
    (k m : ℕ) :
    (persistencePortfolio h start low δ k).price V m =
      (persistenceNorm As start low δ k).denote V *
        ((List.range (k + 1)).map (fun n =>
          (persistenceEntry As start low δ k n).denote V *
            (As n).price V m)).sum := by
  exact persistencePortfolio_value h start low δ V (V m) k

theorem persistencePortfolio_magnitude {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (V : History) (k : ℕ) :
    (persistencePortfolio h start low δ k).magnitude V =
      (persistenceNorm As start low δ k).denote V *
        ((List.range (k + 1)).map (fun n =>
          (persistenceEntry As start low δ k n).denote V *
            (As n).magnitude V)).sum := by
  rw [magnitude, persistencePortfolio_terms_flatMap]
  let N := (persistenceNorm As start low δ k).denote V
  let e : ℕ → ℝ := fun n => (persistenceEntry As start low δ k n).denote V
  have hN0 : 0 ≤ N := le_of_lt (persistenceNorm_pos As start low δ V k)
  have he0 : ∀ n, 0 ≤ e n := fun n => persistenceEntry_nonneg As start low δ V k n
  let scaledTerms : ℕ → List (EF × Sentence) := fun n => (As n).terms.map (fun p =>
    (EF.mul (persistenceNorm As start low δ k)
      (EF.mul (persistenceEntry As start low δ k n) p.1), p.2))
  have hone : ∀ n,
      ((scaledTerms n).map (fun p => |p.1.denote V|)).sum =
        N * (e n * (As n).magnitude V) := by
    intro n
    simp only [scaledTerms, List.map_map, Function.comp_def, EF.denote_mul,
      Pi.mul_apply, abs_mul, abs_of_nonneg hN0, abs_of_nonneg (he0 n), N, e,
      magnitude]
    rw [show (As n).terms.map (fun p =>
        (persistenceNorm As start low δ k).denote V *
          ((persistenceEntry As start low δ k n).denote V * |p.1.denote V|)) =
        (As n).terms.map (fun p =>
          ((persistenceNorm As start low δ k).denote V *
            (persistenceEntry As start low δ k n).denote V) * |p.1.denote V|) by
      apply List.map_congr_left
      intro p hp
      ring]
    rw [List.sum_map_mul_left]
    ring
  change (((List.range (k + 1)).flatMap scaledTerms).map
      (fun p => |p.1.denote V|)).sum =
    N * ((List.range (k + 1)).map (fun n => e n * (As n).magnitude V)).sum
  induction List.range (k + 1) with
  | nil => simp
  | cons n l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, hone n, ih]
      ring

theorem persistencePortfolio_magnitude_le_one {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (V : History)
    (hmag : ∀ n, (As n).magnitude V ≤ 1) (k : ℕ) :
    (persistencePortfolio h start low δ k).magnitude V ≤ 1 := by
  rw [persistencePortfolio_magnitude]
  have hN0 := le_of_lt (persistenceNorm_pos As start low δ V k)
  calc
    (persistenceNorm As start low δ k).denote V *
        ((List.range (k + 1)).map (fun n =>
          (persistenceEntry As start low δ k n).denote V * (As n).magnitude V)).sum
      ≤ (persistenceNorm As start low δ k).denote V *
          ((List.range (k + 1)).map (fun n =>
            (persistenceEntry As start low δ k n).denote V)).sum := by
        apply mul_le_mul_of_nonneg_left _ hN0
        have hsum : ∀ l : List ℕ,
            (l.map (fun n => (persistenceEntry As start low δ k n).denote V *
              (As n).magnitude V)).sum ≤
            (l.map (fun n => (persistenceEntry As start low δ k n).denote V)).sum := by
          intro l
          induction l with
          | nil => simp
          | cons n l ih =>
              simp only [List.map_cons, List.sum_cons]
              exact add_le_add
                (mul_le_of_le_one_right
                  (persistenceEntry_nonneg As start low δ V k n) (hmag n)) ih
        exact hsum (List.range (k + 1))
    _ = (persistenceNorm As start low δ k).denote V *
          (persistenceEntrySum As start low δ k).denote V := by
        rw [persistenceEntrySum_denote]
    _ ≤ 1 := persistenceNorm_mul_entrySum_le_one As start low δ V k

/-- Uniform price boundedness is preserved by normalized prefix portfolios. -/
theorem persistencePortfolio_bounded {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (V : History)
    (hbounded : BoundedAffinePrices As V) :
    BoundedAffinePrices (persistencePortfolio h start low δ) V := by
  obtain ⟨B, hB0, hB⟩ := hbounded
  refine ⟨B, hB0, fun k m => ?_⟩
  rw [persistencePortfolio_price]
  let N := (persistenceNorm As start low δ k).denote V
  let e : ℕ → ℝ := fun n => (persistenceEntry As start low δ k n).denote V
  have hN0 : 0 ≤ N := le_of_lt (persistenceNorm_pos As start low δ V k)
  have he0 : ∀ n, 0 ≤ e n := fun n => persistenceEntry_nonneg As start low δ V k n
  have hsum : ∀ l : List ℕ,
      |(l.map (fun n => e n * (As n).price V m)).sum| ≤
        B * (l.map e).sum := by
    intro l
    induction l with
    | nil => simp [hB0]
    | cons n l ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          |e n * (As n).price V m + (l.map (fun q => e q * (As q).price V m)).sum|
              ≤ |e n * (As n).price V m| +
                  |(l.map (fun q => e q * (As q).price V m)).sum| := abs_add_le _ _
          _ ≤ e n * B + B * (l.map e).sum := by
            apply add_le_add _ ih
            rw [abs_mul, abs_of_nonneg (he0 n)]
            exact mul_le_mul_of_nonneg_left (hB n m) (he0 n)
          _ = B * (e n + (l.map e).sum) := by ring
  rw [abs_mul, abs_of_nonneg hN0]
  calc
    N * |((List.range (k + 1)).map (fun n => e n * (As n).price V m)).sum|
        ≤ N * (B * ((List.range (k + 1)).map e).sum) :=
      mul_le_mul_of_nonneg_left (hsum (List.range (k + 1))) hN0
    _ = B * (N * (persistenceEntrySum As start low δ k).denote V) := by
      rw [persistenceEntrySum_denote]
      ring
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left
      (persistenceNorm_mul_entrySum_le_one As start low δ V k) hB0
    _ = B := mul_one B

theorem persistencePortfolio_limitingValue_nonneg {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (P : History) (k : ℕ)
    (hlim : ∀ n, start < n → 0 ≤ (As n).value P (limitingBelief P)) :
    0 ≤ (persistencePortfolio h start low δ k).value P (limitingBelief P) := by
  rw [persistencePortfolio_value]
  apply mul_nonneg (le_of_lt (persistenceNorm_pos As start low δ P k))
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨n, hn, rfl⟩ := hx
  have he0 := persistenceEntry_nonneg As start low δ P k n
  by_cases hs : start < n
  · exact mul_nonneg he0 (hlim n hs)
  · simp [persistenceEntry, hs]

/-- If one prefix member has a full buy signal, the normalized portfolio's current
price is at most the upper edge of the buy ramp. -/
theorem persistencePortfolio_price_le_of_entry_one {As : ℕ → AffineCombination}
    (h : PolySequence As) (start : ℕ) (low δ : ℚ) (P : History)
    (hδ : 0 < (δ : ℝ)) {k n : ℕ} (hn : n < k + 1)
    (hone : (persistenceEntry As start low δ k n).denote P = 1) :
    (persistencePortfolio h start low δ k).price P k ≤ (low : ℝ) + δ := by
  rw [persistencePortfolio_price]
  let N := (persistenceNorm As start low δ k).denote P
  let e : ℕ → ℝ := fun q => (persistenceEntry As start low δ k q).denote P
  let q : ℝ := (low : ℝ) + δ
  have hN0 : 0 ≤ N := le_of_lt (persistenceNorm_pos As start low δ P k)
  have hpoint : ∀ i, e i * (As i).price P k ≤ e i * q := by
    intro i
    have he0 := persistenceEntry_nonneg As start low δ P k i
    by_cases he : e i = 0
    · simp [he]
    · have hep : 0 < e i := lt_of_le_of_ne he0 (Ne.symm he)
      have hs : start < i := by
        by_contra hsi
        simp [e, persistenceEntry, hsi] at he
      have hopen := buyIndF_pos_imp hδ (by simpa [e, persistenceEntry, hs] using hep)
      rw [(As i).priceFeature_denote] at hopen
      exact mul_le_mul_of_nonneg_left (le_of_lt hopen) he0
  have hsum :
      ((List.range (k + 1)).map (fun i => e i * (As i).price P k)).sum ≤
        q * ((List.range (k + 1)).map e).sum := by
    calc
      ((List.range (k + 1)).map (fun i => e i * (As i).price P k)).sum
          ≤ ((List.range (k + 1)).map (fun i => e i * q)).sum := by
        have aux : ∀ l : List ℕ,
            (l.map (fun i => e i * (As i).price P k)).sum ≤
              (l.map (fun i => e i * q)).sum := by
          intro l
          induction l with
          | nil => simp
          | cons i l ih =>
              simp only [List.map_cons, List.sum_cons]
              exact add_le_add (hpoint i) ih
        exact aux (List.range (k + 1))
      _ = q * ((List.range (k + 1)).map e).sum := by
        rw [show (List.range (k + 1)).map (fun i => e i * q) =
            (List.range (k + 1)).map (fun i => q * e i) by
          apply List.map_congr_left
          intro i hi
          ring]
        rw [List.sum_map_mul_left]
  calc
    N * ((List.range (k + 1)).map (fun i => e i * (As i).price P k)).sum
        ≤ N * (q * ((List.range (k + 1)).map e).sum) :=
      mul_le_mul_of_nonneg_left hsum hN0
    _ = q * (N * (persistenceEntrySum As start low δ k).denote P) := by
      rw [persistenceEntrySum_denote]
      ring
    _ = q := by
      rw [persistenceNorm_mul_entrySum_eq_one_of_entry_one
        As start low δ P hn hone]
      ring

/-- The Appendix `app:peraffkno` underpricing contradiction.  A day-`k` portfolio
contains every earlier member whose day-`k` price is below the chosen threshold.  The
portfolio is translated so its limiting value is nonnegative, while every full signal
makes its current price uniformly negative.  The verified affine round-trip family then
rules out infinitely many such launch days. -/
theorem PolySequence.noPersistenceUnderpricing {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    NoPreemptiveUnderpricing
      (affineFutureLow As P) (fun n => (As n).value P (limitingBelief P)) := by
  intro a b hab hfuture hcurrent
  obtain ⟨low, halow, hlowb⟩ := exists_rat_btwn hab
  obtain ⟨anchor, hlowanchor, hanchorb⟩ := exists_rat_btwn hlowb
  have hgap0 : 0 < (anchor : ℝ) - low := by linarith
  obtain ⟨δ, hδ0, hδgap⟩ := exists_rat_btwn hgap0
  have hδ : 0 < (δ : ℝ) := hδ0
  obtain ⟨start, hstart⟩ := Filter.eventually_atTop.mp hfuture
  let shifted : ℕ → AffineCombination := fun n => (As n).addConst (-anchor)
  let hshift : PolySequence shifted := h.addConst (-anchor)
  let lowShift : ℚ := low - anchor
  let portfolios : ℕ → AffineCombination :=
    persistencePortfolio hshift start lowShift δ
  let hport : PolySequence portfolios := hshift.persistencePortfolioPoly start lowShift δ
  have hshiftBound : BoundedAffinePrices shifted P := by
    simpa [shifted] using BoundedAffinePrices.addConst hbounded (-anchor)
  have hportBound : BoundedAffinePrices portfolios P := by
    simpa [portfolios] using
      persistencePortfolio_bounded hshift start lowShift δ P hshiftBound
  have hshiftMag : ∀ n, (shifted n).magnitude P ≤ 1 := by
    intro n
    simpa [shifted, addConst_magnitude] using hmag n
  have hportMag : ∀ k, (portfolios k).magnitude P ≤ 1 := by
    intro k
    simpa [portfolios] using
      persistencePortfolio_magnitude_le_one hshift start lowShift δ P hshiftMag k
  have hshiftLim : ∀ n, start < n →
      0 ≤ (shifted n).value P (limitingBelief P) := by
    intro n hn
    have hnlim := hstart n (Nat.le_of_lt hn)
    dsimp only [shifted]
    rw [addConst_value]
    push_cast
    linarith
  have hportFuture : ∀ k, 0 ≤ affineFutureHigh portfolios P k := by
    intro k
    have hlim0 : 0 ≤ (portfolios k).value P (limitingBelief P) := by
      simpa [portfolios] using
        persistencePortfolio_limitingValue_nonneg hshift start lowShift δ P k hshiftLim
    have hbetween := futureLow_le_limitingValue_le_futureHigh
      portfolios P DP hportBound hP hworld k
    exact hlim0.trans hbetween.2
  have hnogap := hport.noPreemptiveUnderpricing P DP hportMag hP hworld
  let q : ℝ := (lowShift : ℝ) + δ
  have hq0 : q < 0 := by
    dsimp only [q, lowShift]
    push_cast
    linarith
  obtain ⟨x, hqx, hx0⟩ := exists_between hq0
  obtain ⟨y, hxy, hy0⟩ := exists_between hx0
  apply hnogap x y hxy
  · exact Eventually.of_forall (fun k => hy0.trans_le (hportFuture k))
  · refine Filter.frequently_atTop.mpr (fun K => ?_)
    obtain ⟨n, hnlarge, hnlow⟩ :=
      (Filter.frequently_atTop.mp hcurrent) (max (start + 1) K)
    have hnstart : start < n := by omega
    have hnK : K ≤ n := by omega
    have hninf : affineFutureLow As P n < (low : ℝ) := hnlow.trans halow
    obtain ⟨price, ⟨j, rfl⟩, hjprice⟩ :=
      exists_lt_of_csInf_lt (Set.range_nonempty
        (fun j => (As n).price P (n + j))) hninf
    have hone :
        (persistenceEntry shifted start lowShift δ (n + j) n).denote P = 1 := by
      simp only [persistenceEntry, hnstart, if_true]
      apply buyIndF_eq_one hδ
      rw [(shifted n).priceFeature_denote]
      dsimp only [shifted, lowShift]
      rw [addConst_price]
      push_cast
      linarith
    have hprice := persistencePortfolio_price_le_of_entry_one
      hshift start lowShift δ P hδ (show n < n + j + 1 by omega) hone
    refine ⟨n + j, hnK.trans (by omega), ?_⟩
    change (portfolios (n + j)).price P (n + j) < x
    have hprice' : (portfolios (n + j)).price P (n + j) ≤ q := by
      simpa [portfolios, q] using hprice
    exact hprice'.trans_lt hqx

theorem affineFutureLow_neg (As : ℕ → AffineCombination) (P : History) (n : ℕ) :
    affineFutureLow (fun i => (As i).neg) P n = -affineFutureHigh As P n := by
  simp only [affineFutureLow, affineFutureHigh, neg_price]
  rw [show Set.range (fun j => -(As n).price P (n + j)) =
      -(Set.range (fun j => (As n).price P (n + j))) by
    ext x
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, by linarith⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by linarith⟩]
  exact Real.sInf_neg _

/-- Positive rational rescaling transports a strict tail-infimum upper bound.  This is
the persistence analogue of `BoundedAffinePrices.mul_lt_scaledFutureHigh`. -/
theorem BoundedAffinePrices.scaledFutureLow_lt_mul
    {As : ℕ → AffineCombination} {P : History}
    (h : BoundedAffinePrices As P) (q : ℚ) (hq : 0 < (q : ℝ))
    (n : ℕ) {b : ℝ} (hb : affineFutureLow As P n < b) :
    affineFutureLow (fun i => (As i).scale (.const q)) P n < (q : ℝ) * b := by
  obtain ⟨x, ⟨j, rfl⟩, hx⟩ :=
    exists_lt_of_csInf_lt (Set.range_nonempty
      (fun j => (As n).price P (n + j))) hb
  have hscaledBound := h.scaleRat q
  obtain ⟨B, _, hB⟩ := hscaledBound
  have hmember :
      affineFutureLow (fun i => (As i).scale (.const q)) P n ≤
        ((As n).scale (.const q)).price P (n + j) := by
    apply csInf_le
    · refine ⟨-B, ?_⟩
      rintro y ⟨k, rfl⟩
      linarith [neg_abs_le (((As n).scale (.const q)).price P (n + k)),
        hB n (n + k)]
    · exact ⟨j, rfl⟩
  rw [scale_price, EF.denote_const] at hmember
  exact hmember.trans_lt (mul_lt_mul_of_pos_left hx hq)

/-- The paper permits arbitrary uniformly bounded affine families.  Normalize once by a
positive rational, invoke the unit-risk persistence portfolio, and transport the strict
tail-infimum and limiting-value gaps back to the original scale. -/
theorem PolySequence.noPersistenceUnderpricing_of_boundedMagnitude
    {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ B : ℝ, ∀ n, (As n).magnitude P ≤ B)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    NoPreemptiveUnderpricing
      (affineFutureLow As P) (fun n => (As n).value P (limitingBelief P)) := by
  obtain ⟨B, hB⟩ := hmag
  obtain ⟨C, hC⟩ := exists_rat_gt (max B 0)
  have hC0 : 0 < (C : ℝ) := lt_of_le_of_lt (le_max_right B 0) hC
  let q : ℚ := 1 / C
  have hq0 : 0 < (q : ℝ) := by
    dsimp only [q]
    rw [Rat.cast_div, Rat.cast_one]
    exact one_div_pos.mpr hC0
  have hscaledMag : ∀ n,
      ((As n).scale (.const q)).magnitude P ≤ 1 := by
    intro n
    rw [scale_magnitude, EF.denote_const, abs_of_pos hq0]
    have hn : (As n).magnitude P < (C : ℝ) :=
      (hB n).trans_lt ((le_max_left B 0).trans_lt hC)
    have hdiv : (As n).magnitude P / (C : ℝ) ≤ 1 :=
      (div_le_one hC0).mpr hn.le
    simpa [q, div_eq_mul_inv, mul_comm] using hdiv
  have hscaled := (h.scaleRat q).noPersistenceUnderpricing P DP
    (hbounded.scaleRat q) hscaledMag hP hworld
  intro a b hab hfuture hcurrent
  apply hscaled ((q : ℝ) * a) ((q : ℝ) * b)
  · exact mul_lt_mul_of_pos_left hab hq0
  · filter_upwards [hfuture] with n hn
    rw [scale_value, EF.denote_const]
    exact mul_lt_mul_of_pos_left hn hq0
  · exact hcurrent.mono (fun n hn =>
      AffineCombination.BoundedAffinePrices.scaledFutureLow_lt_mul
        hbounded q hq0 n hn)

/-- The overpricing half of persistence is the underpricing construction applied to the
uniformly emitted negated affine family. -/
theorem PolySequence.noPersistenceOverpricing {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    NoPreemptiveOverpricing
      (affineFutureHigh As P) (fun n => (As n).value P (limitingBelief P)) := by
  have hnegBound : BoundedAffinePrices (fun n => (As n).neg) P := by
    obtain ⟨B, hB0, hB⟩ := hbounded
    exact ⟨B, hB0, fun n m => by simpa [neg_price] using hB n m⟩
  have hneg := h.neg.noPersistenceUnderpricing P DP hnegBound
    (fun n => by simpa [neg_magnitude] using hmag n) hP hworld
  intro a b hab hfuture hcurrent
  apply hneg (-b) (-a) (by linarith)
  · filter_upwards [hfuture] with n hn
    rw [neg_value]
    linarith
  · exact hcurrent.mono (fun n hn => by
      rw [affineFutureLow_neg]
      linarith)

/-- Arbitrary bounded-magnitude overpricing, obtained by applying the normalized
underpricing theorem to the uniformly emitted negated family. -/
theorem PolySequence.noPersistenceOverpricing_of_boundedMagnitude
    {As : ℕ → AffineCombination}
    (h : PolySequence As) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ B : ℝ, ∀ n, (As n).magnitude P ≤ B)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    NoPreemptiveOverpricing
      (affineFutureHigh As P) (fun n => (As n).value P (limitingBelief P)) := by
  have hnegMag : ∃ B : ℝ, ∀ n, ((As n).neg).magnitude P ≤ B := by
    obtain ⟨B, hB⟩ := hmag
    exact ⟨B, fun n => by simpa only [neg_magnitude] using hB n⟩
  have hneg := h.neg.noPersistenceUnderpricing_of_boundedMagnitude P DP
    hbounded.neg hnegMag hP hworld
  intro a b hab hfuture hcurrent
  apply hneg (-b) (-a) (by linarith)
  · filter_upwards [hfuture] with n hn
    rw [neg_value]
    linarith
  · exact hcurrent.mono (fun n hn => by
      rw [affineFutureLow_neg]
      linarith)

end AffineCombination

/-- The two operational persistence conditions supplied by the Appendix `app:peraffkno`
prefix-portfolio reduction. They say that the full future tail cannot remain
separated from the limiting value on infinitely many sequence members. -/
structure AffineNoPersistenceGaps (As : ℕ → AffineCombination) (P : History) : Prop where
  underpriced : NoPreemptiveUnderpricing
    (affineFutureLow As P) (fun n => (As n).value P (limitingBelief P))
  overpriced : NoPreemptiveOverpricing
    (affineFutureHigh As P) (fun n => (As n).value P (limitingBelief P))

/-- Operational Appendix `app:peraffkno` result: neither future-tail extremum can stay
separated from the corresponding limiting affine value. -/
theorem AffineCombination.PolySequence.noPersistenceGaps
    {As : ℕ → AffineCombination} (h : AffineCombination.PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∀ n, (As n).magnitude P ≤ 1)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AffineNoPersistenceGaps As P :=
  ⟨h.noPersistenceUnderpricing P DP hbounded hmag hP hworld,
    h.noPersistenceOverpricing P DP hbounded hmag hP hworld⟩

/-- Operational persistence for an arbitrary uniformly bounded affine family. -/
theorem AffineCombination.PolySequence.noPersistenceGaps_of_boundedMagnitude
    {As : ℕ → AffineCombination} (h : AffineCombination.PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ B : ℝ, ∀ n, (As n).magnitude P ≤ B)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AffineNoPersistenceGaps As P :=
  ⟨h.noPersistenceUnderpricing_of_boundedMagnitude P DP hbounded hmag hP hworld,
    h.noPersistenceOverpricing_of_boundedMagnitude P DP hbounded hmag hP hworld⟩

/-- Analytic capstone for **Persistence of Affine Knowledge** (`thm:peraffkno`). Once the
operational no-gap result is supplied, the two exact paper equalities follow from generic
liminf/limsup order theory and fixed-combination convergence. -/
theorem peraffkno_of_noPersistenceGaps
    (As : ℕ → AffineCombination) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hbounded : BoundedAffinePrices As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hgap : AffineNoPersistenceGaps As P) :
    liminf (affineFutureLow As P) atTop =
        liminf (fun n => (As n).value P (limitingBelief P)) atTop ∧
      limsup (affineFutureHigh As P) atTop =
        limsup (fun n => (As n).value P (limitingBelief P)) atTop := by
  obtain ⟨_hdlo, _hdhi, hhlo, hhhi, hllo, hlhi⟩ := hbounded.filterBounds
  obtain ⟨hlimlo, hlimhi⟩ :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      hbounded DP hP hworld
  have hbetween : ∀ n,
      affineFutureLow As P n ≤ (As n).value P (limitingBelief P) ∧
        (As n).value P (limitingBelief P) ≤ affineFutureHigh As P n :=
    fun n => AffineCombination.futureLow_le_limitingValue_le_futureHigh
      As P DP hbounded hP hworld n
  constructor
  · exact liminf_eq_of_noPreemptiveUnderpricing _ _ hllo hlhi hlimlo hlimhi
      (fun n => (hbetween n).1) hgap.underpriced
  · exact limsup_eq_of_noPreemptiveOverpricing _ _ hhlo hhhi hlimlo hlimhi
      (fun n => (hbetween n).2) hgap.overpriced

/-- Paper-facing **Persistence of Affine Knowledge** (`thm:peraffkno`). This is the exact
pair of future-tail/limiting-belief equalities for a normalized polynomial affine family. -/
theorem AffineCombination.PolySequence.peraffkno
    {As : ℕ → AffineCombination} (h : AffineCombination.PolySequence As)
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hbounded : BoundedAffinePrices As P)
    (hmag : ∃ B : ℝ, ∀ n, (As n).magnitude P ≤ B)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (affineFutureLow As P) atTop =
        liminf (fun n => (As n).value P (limitingBelief P)) atTop ∧
      limsup (affineFutureHigh As P) atTop =
        limsup (fun n => (As n).value P (limitingBelief P)) atTop :=
  peraffkno_of_noPersistenceGaps As P DP hbounded hP hworld
    (h.noPersistenceGaps_of_boundedMagnitude P DP hbounded hmag hP hworld)

#print axioms lic_limitingBelief_tendsto
#print axioms AffineCombination.price_tendsto_limitingValue
#print axioms AffineCombination.PolySequence.persistencePortfolioPoly
#print axioms AffineCombination.PolySequence.noPersistenceUnderpricing
#print axioms AffineCombination.PolySequence.noPersistenceOverpricing
#print axioms peraffkno_of_noPersistenceGaps
#print axioms AffineCombination.PolySequence.peraffkno

end LogicalInduction
