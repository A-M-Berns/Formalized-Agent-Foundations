import LogicalInduction.Construction.Witnesses.QuotationAffine

namespace LogicalInduction

open Filter Topology Finset

/-! ## First-violator selector: analytic core -/

/-- First-success telescoping: the total weight a first-violator selector spends is
`1 - Π (1 - g j)`, so no normalization (no `safeRecip`, no division) is needed to keep
the day's magnitude budget. -/
lemma firstSuccess_sum (g : ℕ → ℝ) (c : ℕ) :
    ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) =
      1 - ∏ j ∈ Finset.range c, (1 - g j) := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
      ring

lemma firstSuccess_weight_nonneg {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (k : ℕ) :
    0 ≤ g k * ∏ j ∈ Finset.range k, (1 - g j) :=
  mul_nonneg (hg k).1 (Finset.prod_nonneg fun j _ => by have := (hg j).2; linarith)

lemma firstSuccess_sum_le_one {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (c : ℕ) :
    ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) ≤ 1 := by
  rw [firstSuccess_sum]
  have : (0:ℝ) ≤ ∏ j ∈ Finset.range c, (1 - g j) :=
    Finset.prod_nonneg (fun j _ => by have := (hg j).2; linarith)
  linarith

lemma firstSuccess_sum_nonneg {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (c : ℕ) :
    0 ≤ ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) :=
  Finset.sum_nonneg fun k _ => firstSuccess_weight_nonneg hg k

/-- **Forcing.**  Once *some* gate in the window saturates, the selector's total weight is
exactly `1`; since every summand carrying positive weight is at least `δ`, the gated sum
is at least `δ`.  This is the step that makes the terms non-cancelling, and it needs no
minimality of the violator — only the telescoping identity above. -/
lemma firstSuccess_forces {g d : ℕ → ℝ} {δ : ℝ} {c k₀ : ℕ} (hk₀ : k₀ < c)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) (hhit : g k₀ = 1)
    (hδ : ∀ k < c, 0 < g k → δ ≤ d k) :
    δ ≤ ∑ k ∈ Finset.range c, (g k * ∏ j ∈ Finset.range k, (1 - g j)) * d k := by
  have hzero : ∏ j ∈ Finset.range c, (1 - g j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.2 hk₀) (by rw [hhit]; ring)
  have htotal : ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) = 1 := by
    rw [firstSuccess_sum, hzero, sub_zero]
  calc δ = δ * ∑ k ∈ Finset.range c, g k * ∏ j ∈ Finset.range k, (1 - g j) := by
        rw [htotal, mul_one]
    _ = ∑ k ∈ Finset.range c, (g k * ∏ j ∈ Finset.range k, (1 - g j)) * δ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun k hk => ?_
        rcases eq_or_lt_of_le (hg k).1 with hk0 | hk0
        · simp [← hk0]
        · exact mul_le_mul_of_nonneg_left (hδ k (Finset.mem_range.1 hk) hk0)
            (firstSuccess_weight_nonneg hg k)

/-! ## First-violator selector: syntax -/

/-- One factor `1 - g j` of the selector product. -/
private def selectorFactor (g : ℕ → EF) (j : ℕ) : EF :=
  EF.add (EF.const 1) (EF.mul (EF.const (-1)) (g j))

/-- The selector product `Π_{j < k} (1 - g⟨m,j⟩)` for `z = ⟨m,k⟩`. -/
private def selectorProd (g : ℕ → EF) (z : ℕ) : EF :=
  (List.range z.unpair.2).foldr
    (fun j acc ↦ EF.mul (selectorFactor g (Nat.pair z.unpair.1 j)) acc) (EF.const 1)

/-- **First-violator selector weight** `gate⟨m,k⟩ = g⟨m,k⟩ · Π_{j<k} (1 - g⟨m,j⟩)`.  A
division-free device that spreads a *unit* total weight across an unboundedly large
deferral fibre: by `firstSuccess_sum` the weights over a fibre sum to `1 - Π(1-g) ≤ 1`
with no normalization, and by `firstSuccess_forces` a single saturated gate already forces
the whole gated sum. -/
def selectorFeature (g : ℕ → EF) (z : ℕ) : EF :=
  EF.mul (g z) (selectorProd g z)

private lemma list_prod_range {M : Type*} [CommMonoid M] (n : ℕ) (F : ℕ → M) :
    ((List.range n).map F).prod = ∏ j ∈ Finset.range n, F j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih,
        Finset.prod_range_succ]
      simp

private lemma foldr_mul_denoteWith (L : List ℕ) (u : ℕ → EF) (ρ : List ℝ) (V : History) :
    (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).denoteWith ρ V =
      (L.map fun j ↦ (u j).denoteWith ρ V).prod := by
  induction L with
  | nil => simp [EF.denoteWith]
  | cons j L ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, ← ih]
      rfl

private lemma foldr_mul_serialize (L : List ℕ) (u : ℕ → EF) :
    (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).serialize =
      (L.flatMap fun j ↦ (u j).serialize) ++ (EF.const 1).serialize ++
        List.replicate L.length 3 := by
  induction L with
  | nil => simp
  | cons j L ih =>
      simp only [List.foldr_cons, List.flatMap_cons, List.length_cons]
      rw [show (EF.mul (u j)
            (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1))).serialize =
          (u j).serialize ++
            (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).serialize ++ [3] by
        simp [EF.serialize, List.append_assoc]]
      rw [ih]
      simp [List.replicate_succ', List.append_assoc]

private lemma foldr_mul_rank (L : List ℕ) (u : ℕ → EF) (n : ℕ)
    (hu : ∀ j ∈ L, (u j).rank ≤ n) :
    (L.foldr (fun j acc ↦ EF.mul (u j) acc) (EF.const 1)).rank ≤ n := by
  induction L with
  | nil => simp [EF.rank]
  | cons j L ih =>
      simp only [List.foldr_cons, EF.rank]
      exact Nat.max_le.mpr ⟨hu j (by simp), ih fun i hi ↦ hu i (by simp [hi])⟩

@[simp] private lemma selectorFactor_rank (g : ℕ → EF) (j : ℕ) :
    (selectorFactor g j).rank = (g j).rank := by
  simp [selectorFactor, EF.rank]

private lemma selectorFactor_denoteWith (g : ℕ → EF) (j : ℕ) (ρ : List ℝ) (V : History) :
    (selectorFactor g j).denoteWith ρ V = 1 - (g j).denoteWith ρ V := by
  simp only [selectorFactor, EF.denoteWith, Rat.cast_one, Rat.cast_neg, neg_mul, one_mul]
  ring

private lemma selectorFactor_serialize (g : ℕ → EF) (j : ℕ) :
    (selectorFactor g j).serialize =
      (EF.const 1).serialize ++ (EF.const (-1)).serialize ++ (g j).serialize ++ [3, 2] := by
  simp [selectorFactor, EF.serialize, List.append_assoc]

private lemma selectorProd_denoteWith (g : ℕ → EF) (z : ℕ) (ρ : List ℝ) (V : History) :
    (selectorProd g z).denoteWith ρ V =
      ∏ j ∈ Finset.range z.unpair.2, (1 - (g (Nat.pair z.unpair.1 j)).denoteWith ρ V) := by
  rw [selectorProd, foldr_mul_denoteWith, list_prod_range]
  exact Finset.prod_congr rfl fun j _ ↦ selectorFactor_denoteWith _ _ ρ V

lemma selectorFeature_denote (g : ℕ → EF) (m k : ℕ) (V : History) :
    (selectorFeature g (Nat.pair m k)).denote V =
      (g (Nat.pair m k)).denote V *
        ∏ j ∈ Finset.range k, (1 - (g (Nat.pair m j)).denote V) := by
  simp only [selectorFeature, EF.denote, EF.denoteWith]
  rw [show (selectorProd g (Nat.pair m k)).denoteWith [] V =
      ∏ j ∈ Finset.range k, (1 - (g (Nat.pair m j)).denoteWith [] V) by
    simpa using selectorProd_denoteWith g (Nat.pair m k) [] V]

lemma selectorFeature_closed {g : ℕ → EF}
    (hg : ∀ z ρ V, (g z).denoteWith ρ V = (g z).denote V) (z : ℕ) (ρ : List ℝ)
    (V : History) :
    (selectorFeature g z).denoteWith ρ V = (selectorFeature g z).denote V := by
  simp only [selectorFeature, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
  rw [show (g z).denoteWith ρ V = (g z).denote V from hg z ρ V,
    selectorProd_denoteWith g z ρ V,
    show (selectorProd g z).denote V =
      ∏ j ∈ Finset.range z.unpair.2, (1 - (g (Nat.pair z.unpair.1 j)).denote V) from
      selectorProd_denoteWith g z [] V]
  exact congrArg _ (Finset.prod_congr rfl fun j _ ↦ by rw [hg])

lemma selectorFeature_rank {g : ℕ → EF} {m k : ℕ}
    (hg : ∀ j, j ≤ k → (g (Nat.pair m j)).rank ≤ m) :
    (selectorFeature g (Nat.pair m k)).rank ≤ m := by
  simp only [selectorFeature, EF.rank]
  refine Nat.max_le.mpr ⟨hg k le_rfl, ?_⟩
  rw [selectorProd]
  simp only [Nat.unpair_pair]
  exact foldr_mul_rank _ _ _ fun j hj ↦ by
    rw [selectorFactor_rank]
    exact hg j (le_of_lt (List.mem_range.1 hj))

/-- Uniform emission of the selector weights. -/
lemma selectorFeature_polySeg {g : ℕ → EF}
    (hg : RpnSpliceStream fun z ↦ (g z).serialize) :
    RpnSpliceStream fun z ↦ (selectorFeature g z).serialize := by
  have hidx : PolyFueled _ (fun q : ℕ ↦ Nat.pair q.unpair.1.unpair.1 q.unpair.2) :=
    (PolyFueled.left.comp PolyFueled.left).pair PolyFueled.right
  have hfactor : RpnSpliceStream fun q ↦
      (selectorFactor g (Nat.pair q.unpair.1.unpair.1 q.unpair.2)).serialize := by
    refine RpnSpliceStream.of_eq
      ((((RpnSpliceStream.serialize_const 1).append
        (RpnSpliceStream.serialize_const (-1))).append (hg.comp hidx)).append
        ((RpnSpliceStream.tag 3 (by norm_num)).append
          (RpnSpliceStream.tag 2 (by norm_num)))) (fun q ↦ ?_)
    rw [selectorFactor_serialize]
    simp [List.append_assoc]
  have hprod : RpnSpliceStream fun z ↦ (selectorProd g z).serialize := by
    refine RpnSpliceStream.of_eq
      (((hfactor.concatVar PolyFueled.right).append
        ((RpnSpliceStream.serialize_const 1).append
          (RpnSpliceStream.repeatTag 3 (by norm_num) PolyFueled.right)))) (fun z ↦ ?_)
    rw [selectorProd, foldr_mul_serialize]
    simp [List.append_assoc]
  exact RpnSpliceStream.serialize_mul hg hprod

private lemma list_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    ((List.range n).map F).sum = ∑ j ∈ Finset.range n, F j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

/-! ## Deferral-fibre gating

A day-`m` portfolio that is to settle a *deferred* obligation must carry one term per
source day in the fibre `f⁻¹(m)`, whose size is unbounded when `f` is not injective.  The
day's magnitude budget is one unit, and the gap convergence carries no rate, so no
violation-independent weighting of the fibre can force its individual terms.  The device
that does work is the division-free first-violator selector of `selectorFeature`: gate the
source-`k` block by `ctsInd(δ; |dₖ|, δ)` damped by `Π_{j<k}(1 - …)`, take the whole
package as a `δ`-indexed tower, and read the pointwise conclusion off the union of the
towers' eventual bounds. -/

/-- Emission certificate for a *paired-index* feature family: the member at `z = ⟨m,k⟩` is
legal on the evaluation day `m` — rank `≤ z.unpair.1`, not merely `≤ z` — as well as
polynomially emitted and environment-closed.  The day-indexed `PGenerableWeighting` cannot
state that refinement, and it is exactly what a fibre gate needs in order to be a legal
day-`m` affine coefficient. -/
structure PairedWeighting (A : ℕ → EF) : Prop where
  polySeg : RpnSpliceStream fun z ↦ (A z).serialize
  rank_le : ∀ z, (A z).rank ≤ z.unpair.1
  closed : ∀ z ρ V, (A z).denoteWith ρ V = (A z).denote V

namespace PairedWeighting

lemma ofRatCodes {q : ℕ → ℚ} (hq : PolyRatCodes q) :
    PairedWeighting (fun z ↦ EF.const (q z)) where
  polySeg := RpnSpliceStream.serialize_const_comp hq
  rank_le := by intro z; simp [EF.rank]
  closed := by intro z ρ V; simp [EF.denoteWith]

lemma const (q : ℚ) : PairedWeighting (fun _ ↦ EF.const q) where
  polySeg := RpnSpliceStream.serialize_const q
  rank_le := by intro z; simp [EF.rank]
  closed := by intro z ρ V; simp [EF.denoteWith]

lemma mul {A B : ℕ → EF} (hA : PairedWeighting A) (hB : PairedWeighting B) :
    PairedWeighting (fun z ↦ EF.mul (A z) (B z)) where
  polySeg := RpnSpliceStream.serialize_mul hA.polySeg hB.polySeg
  rank_le := fun z ↦ Nat.max_le.mpr ⟨hA.rank_le z, hB.rank_le z⟩
  closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, Pi.mul_apply]
    rw [hA.closed z ρ V, hB.closed z ρ V]

lemma add {A B : ℕ → EF} (hA : PairedWeighting A) (hB : PairedWeighting B) :
    PairedWeighting (fun z ↦ EF.add (A z) (B z)) where
  polySeg := RpnSpliceStream.serialize_add hA.polySeg hB.polySeg
  rank_le := fun z ↦ Nat.max_le.mpr ⟨hA.rank_le z, hB.rank_le z⟩
  closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_add, Pi.add_apply]
    rw [hA.closed z ρ V, hB.closed z ρ V]

lemma max {A B : ℕ → EF} (hA : PairedWeighting A) (hB : PairedWeighting B) :
    PairedWeighting (fun z ↦ EF.max (A z) (B z)) where
  polySeg := RpnSpliceStream.serialize_max hA.polySeg hB.polySeg
  rank_le := fun z ↦ Nat.max_le.mpr ⟨hA.rank_le z, hB.rank_le z⟩
  closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_max]
    rw [hA.closed z ρ V, hB.closed z ρ V]

lemma clip01 {A : ℕ → EF} (hA : PairedWeighting A) :
    PairedWeighting (fun z ↦ _root_.LogicalInduction.clip01 (A z)) := by
  have h := ((PairedWeighting.const 0).max
    (((PairedWeighting.const (-1)).mul (((PairedWeighting.const (-1)).mul
      (PairedWeighting.const 1)).max ((PairedWeighting.const (-1)).mul hA)))))
  exact h

lemma ctsInd {δ : ℚ} (hδinv : PolyRatCodes (fun _ : ℕ ↦ 1 / δ))
    {x y : ℕ → EF} (hx : PairedWeighting x) (hy : PairedWeighting y) :
    PairedWeighting (ctsIndFeature (fun _ ↦ δ) x y) :=
  PairedWeighting.clip01
    ((hx.add ((PairedWeighting.const (-1)).mul hy)).mul (PairedWeighting.ofRatCodes hδinv))

lemma selector {A : ℕ → EF} (hA : PairedWeighting A) :
    PairedWeighting (selectorFeature A) where
  polySeg := selectorFeature_polySeg hA.polySeg
  rank_le := by
    intro z
    have := selectorFeature_rank (g := A) (m := z.unpair.1) (k := z.unpair.2)
      (fun j _ ↦ by simpa using hA.rank_le (Nat.pair z.unpair.1 j))
    simpa using this
  closed := selectorFeature_closed hA.closed

end PairedWeighting

namespace DeferralFibre

/-- Day-`m` price feature of the source-`k` block, for `z = ⟨m,k⟩`. -/
def priceFeat (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  (Bs z).priceFeature z.unpair.1

/-- Positive part of the block's day-`m` price. -/
def gapPos (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  EF.max (priceFeat Bs z) (EF.const 0)

/-- Negative part of the block's day-`m` price. -/
def gapNeg (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  EF.max (EF.mul (EF.const (-1)) (priceFeat Bs z)) (EF.const 0)

/-- The `[f k = m]` fibre-membership flag as a closed constant feature. -/
def matchFeat (f : DeferralFunction) (a degree z : ℕ) : EF :=
  EF.const ((FeedbackEmission.scheduledMatch f a degree z : ℕ) : ℚ)

/-- Fibre-gated continuous threshold on one side of the gap. -/
def gateBase (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (d : ℕ → EF) (z : ℕ) : EF :=
  EF.mul (matchFeat f a degree z)
    (ctsIndFeature (fun _ ↦ δ) d (fun _ ↦ EF.const δ) z)

/-- Two-sided first-violator coefficient: the positive-side selector minus the
negative-side selector, normalised by `1/(2C)`. -/
def gateCoeff (f : DeferralFunction) (a degree : ℕ) (δ C : ℚ)
    (Bs : ℕ → AffineCombination) (z : ℕ) : EF :=
  EF.mul (EF.const (1 / (2 * C)))
    (EF.add (selectorFeature (gateBase f a degree δ (gapPos Bs)) z)
      (EF.mul (EF.const (-1))
        (selectorFeature (gateBase f a degree δ (gapNeg Bs)) z)))

variable {Bs : ℕ → AffineCombination}

lemma priceFeat_denote (Bs : ℕ → AffineCombination) (z : ℕ) (V : History) :
    (priceFeat Bs z).denote V = (Bs z).price V z.unpair.1 :=
  AffineCombination.priceFeature_denote _ _ _

lemma priceFeat_paired (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1) :
    PairedWeighting (priceFeat Bs) where
  polySeg := (hB.priceFeature_polySeg.comp
    (PolyFueled.id.pair PolyFueled.left)).of_eq (fun z ↦ by simp [priceFeat])
  rank_le := fun z ↦ AffineCombination.priceFeature_rank (Bs z) le_rfl
    (hconstRank z) (htermRank z)
  closed := fun z ρ V ↦ hB.priceFeature_closed z z.unpair.1 ρ V

lemma gapPos_denote (Bs : ℕ → AffineCombination) (z : ℕ) (V : History) :
    (gapPos Bs z).denote V = Max.max ((Bs z).price V z.unpair.1) 0 := by
  simp [gapPos, priceFeat_denote]

lemma gapNeg_denote (Bs : ℕ → AffineCombination) (z : ℕ) (V : History) :
    (gapNeg Bs z).denote V = Max.max (-((Bs z).price V z.unpair.1)) 0 := by
  simp [gapNeg, priceFeat_denote]

lemma matchFeat_denote (f : DeferralFunction) (a degree z : ℕ) (V : History) :
    (matchFeat f a degree z).denote V =
      ((FeedbackEmission.scheduledMatch f a degree z : ℕ) : ℝ) := by
  simp [matchFeat]

lemma matchFeat_paired (f : DeferralFunction) (a degree : ℕ) :
    PairedWeighting (matchFeat f a degree) :=
  PairedWeighting.ofRatCodes
    (ratNatCast_codes_of_polyFueled
      (Classical.choose_spec (FeedbackEmission.scheduledMatch_polyFueled f a degree)))

lemma gateBase_denote (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History) :
    (gateBase f a degree δ d z).denote V =
      ((FeedbackEmission.scheduledMatch f a degree z : ℕ) : ℝ) *
        ctsInd δ ((d z).denote V) (δ : ℝ) := by
  simp only [gateBase, EF.denote_mul, Pi.mul_apply, matchFeat_denote]
  rw [ctsIndFeature_denote (fun _ ↦ δ) d _ (fun _ ↦ hδ) V z]
  simp

lemma gateBase_mem (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History) :
    0 ≤ (gateBase f a degree δ d z).denote V ∧
      (gateBase f a degree δ d z).denote V ≤ 1 := by
  rw [gateBase_denote f a degree δ hδ d z V]
  have hI := ctsInd_mem_Icc δ ((d z).denote V) (δ : ℝ)
  rcases FeedbackEmission.scheduledMatch_zero_or_one f a degree z with h | h
  · rw [h]; simp
  · rw [h]; simpa using ⟨hI.1, hI.2⟩

lemma gateBase_pos (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History)
    (h : 0 < (gateBase f a degree δ d z).denote V) :
    (δ : ℝ) < (d z).denote V := by
  rw [gateBase_denote f a degree δ hδ d z V] at h
  by_contra hle
  rw [ctsInd_eq_zero_of_le δ _ _ hδ (not_lt.1 hle), mul_zero] at h
  exact absurd h (lt_irrefl 0)

lemma gateBase_eq_one (f : DeferralFunction) (a degree : ℕ) (δ : ℚ) (hδ : 0 < δ)
    (d : ℕ → EF) (z : ℕ) (V : History)
    (hmatch : FeedbackEmission.scheduledMatch f a degree z = 1)
    (hbig : 2 * (δ : ℝ) ≤ (d z).denote V) :
    (gateBase f a degree δ d z).denote V = 1 := by
  rw [gateBase_denote f a degree δ hδ d z V, hmatch,
    ctsInd_eq_one_of_le_sub δ _ _ hδ (by linarith)]
  simp

lemma gateBase_paired (f : DeferralFunction) (a degree : ℕ) {δ : ℚ}
    (hδinv : PolyRatCodes (fun _ : ℕ ↦ 1 / δ)) {d : ℕ → EF} (hd : PairedWeighting d) :
    PairedWeighting (gateBase f a degree δ d) :=
  (matchFeat_paired f a degree).mul
    (PairedWeighting.ctsInd hδinv hd (PairedWeighting.const δ))

lemma gateCoeff_paired (f : DeferralFunction) (a degree : ℕ) {δ C : ℚ}
    (hδinv : PolyRatCodes (fun _ : ℕ ↦ 1 / δ))
    (hB : AffineCombination.PolySequence Bs)
    (hconstRank : ∀ z, (Bs z).const.rank ≤ z.unpair.1)
    (htermRank : ∀ z, ∀ p ∈ (Bs z).terms, p.1.rank ≤ z.unpair.1) :
    PairedWeighting (gateCoeff f a degree δ C Bs) := by
  have hprice := priceFeat_paired hB hconstRank htermRank
  have hpos : PairedWeighting (gapPos Bs) := hprice.max (PairedWeighting.const 0)
  have hneg : PairedWeighting (gapNeg Bs) :=
    ((PairedWeighting.const (-1)).mul hprice).max (PairedWeighting.const 0)
  exact (PairedWeighting.const (1 / (2 * C))).mul
    (((gateBase_paired f a degree hδinv hpos).selector).add
      ((PairedWeighting.const (-1)).mul
        ((gateBase_paired f a degree hδinv hneg).selector)))

end DeferralFibre

end LogicalInduction
