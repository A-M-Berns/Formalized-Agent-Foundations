/-
# Collected expectation-property lifts

This file builds the concrete mesh-affine presentation used by the six collected
expectation theorems.  A LUV combination is not collapsed to a synthetic LUV: each term
is expanded into the paper's `n` threshold shares, so the affine master theorems continue
to see the actual traded sentences.
-/
import LogicalInduction.Properties.ExpectationAffine
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.Pseudorandomness
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace LogicalInduction

open Filter Topology

namespace LUV

/-- Cross-day version of `expectAffine_price`: precision is `k`, while the threshold
bundle is priced on market day `m`. -/
lemma expectAffine_priceAt (X : LUV) (P : History) (k m : ℕ) :
    (X.expectAffine k).price P m = X.expectApprox (P m) k := by
  rw [expectAffine, AffineCombination.price, AffineCombination.value,
    LUV.expectApprox]
  simp only [EF.denote, EF.denoteWith, List.map_map, Function.comp_def]
  push_cast
  rw [zero_add, List.sum_map_mul_left, one_div]
  congr 1

end LUV

/-- An affine combination of `[0,1]`-LUVs with expressible-feature coefficients.  This is
the direct propositional rendering of the paper's LUV combinations.  Paper node: `def:luv`. -/
structure LUVCombination where
  const : EF
  terms : List (EF × LUV)

namespace AffineCombination

/-- Pointwise sum of two affine combinations. -/
def add (A B : AffineCombination) : AffineCombination where
  const := .add A.const B.const
  terms := A.terms ++ B.terms

lemma add_value (A B : AffineCombination) (P : History) (w : Valuation) :
    (A.add B).value P w = A.value P w + B.value P w := by
  simp only [add, value, EF.denote_add, Pi.add_apply, List.map_append, List.sum_append]
  ring

lemma add_price (A B : AffineCombination) (P : History) (n : ℕ) :
    (A.add B).price P n = A.price P n + B.price P n := by
  simp only [price, add_value]

lemma add_magnitude (A B : AffineCombination) (P : History) :
    (A.add B).magnitude P = A.magnitude P + B.magnitude P := by
  simp [add, magnitude, List.map_append]

/-- Pointwise difference of affine combinations. -/
def sub (A B : AffineCombination) : AffineCombination := A.add B.neg

lemma sub_value (A B : AffineCombination) (P : History) (w : Valuation) :
    (A.sub B).value P w = A.value P w - B.value P w := by
  rw [sub, add_value, neg_value]
  ring

lemma sub_price (A B : AffineCombination) (P : History) (n : ℕ) :
    (A.sub B).price P n = A.price P n - B.price P n := by
  rw [sub, add_price, neg_price]
  ring

lemma sub_magnitude (A B : AffineCombination) (P : History) :
    (A.sub B).magnitude P = A.magnitude P + B.magnitude P := by
  rw [sub, add_magnitude, neg_magnitude]

end AffineCombination

namespace LUVCombination

/-- Evaluate a LUV combination using precision `k` and prices from market day `m`. -/
noncomputable def expectAt (A : LUVCombination) (P : History) (k m : ℕ) : ℝ :=
  A.const.denote P +
    (A.terms.map (fun p => p.1.denote P * p.2.expectApprox (P m) k)).sum

/-- The paper's diagonal expectation of a LUV combination. -/
noncomputable def expect (A : LUVCombination) (P : History) (n : ℕ) : ℝ :=
  A.expectAt P n n

/-- Evaluate the combination under an arbitrary LUV valuation. -/
noncomputable def value (A : LUVCombination) (P : History) (ν : LUV → ℝ) : ℝ :=
  A.const.denote P + (A.terms.map (fun p => p.1.denote P * ν p.2)).sum

/-- A possible world assigns the advertised value to every LUV occurring in the
combination.  This is the collected-LUV analogue of `PCWorld.ValuesAt`. -/
def ValuesAt (v : PCWorld) (A : LUVCombination) (ν : LUV → ℝ) : Prop :=
  ∀ p ∈ A.terms, v.ValuesAt p.2 (ν p.2)

/-- Representation-of-computations premise: each completed-theory world coherently
values every LUV appearing in every sequence member. -/
def WorldValued (As : ℕ → LUVCombination) (DP : DeductiveProcess) : Prop :=
  ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    ∃ ν : LUV → ℝ, (As n).ValuesAt v ν

/-- Strong, first-order-style representation boundary: every completed world agrees on
the strict-threshold truth of each LUV in a sequence member, relative to one canonical
value assignment for that member.  Unlike `WorldValued`, this records that the represented
computations are individually determined, which is exactly what the statistical lifts
need in order to apply affine determined-sequence theorems to the threshold mesh.
Paper node: completed-theory values for `def:luv`. -/
structure ExactTheoryPresentation (As : ℕ → LUVCombination)
    (DP : DeductiveProcess) where
  value : ℕ → LUV → ℝ
  value_mem : ∀ n p, p ∈ (As n).terms → 0 ≤ value n p.2 ∧ value n p.2 ≤ 1
  threshold_iff : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
    ∀ p, p ∈ (As n).terms → ∀ r : ℚ,
      v.Holds (p.2.gt r) ↔ (r : ℝ) < value n p.2

lemma ExactTheoryPresentation.valuesAt
    {As : ℕ → LUVCombination} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) : (As n).ValuesAt v (h.value n) := by
  intro p hp
  refine ⟨(h.value_mem n p hp).1, (h.value_mem n p hp).2, ?_⟩
  intro r
  constructor
  · intro hr
    exact (h.threshold_iff n v hv p hp r).2 hr
  · intro hr hholds
    have hlt := (h.threshold_iff n v hv p hp r).1 hholds
    linarith

lemma ExactTheoryPresentation.toWorldValued
    {As : ℕ → LUVCombination} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP) : WorldValued As DP := by
  intro n v hv
  exact ⟨h.value n, h.valuesAt n v hv⟩

lemma ExactTheoryPresentation.expectApprox_eq
    {As : ℕ → LUVCombination} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP) {n : ℕ}
    (v u : PCWorld) (hv : v.ConsistentWithTheory DP)
    (hu : u.ConsistentWithTheory DP) {p : EF × LUV}
    (hp : p ∈ (As n).terms) (k : ℕ) :
    p.2.expectApprox v.payout k = p.2.expectApprox u.payout k := by
  unfold LUV.expectApprox
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have heq : v.Holds (p.2.gt ((i : ℚ) / (k : ℚ))) ↔
      u.Holds (p.2.gt ((i : ℚ) / (k : ℚ))) :=
    (h.threshold_iff n v hv p hp _).trans (h.threshold_iff n u hu p hp _).symm
  rw [PCWorld.payout, PCWorld.payout]
  by_cases hvh : v.Holds (p.2.gt ((i : ℚ) / (k : ℚ)))
  · rw [if_pos hvh, if_pos (heq.mp hvh)]
  · rw [if_neg hvh, if_neg (fun huh => hvh (heq.mpr huh))]

/-- A canonical completed world, used only to name the common mesh truth stream. -/
noncomputable def theoryWorld (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : PCWorld :=
  Classical.choose (exists_consistentWithTheory DP hworld)

lemma theoryWorld_consistent (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (theoryWorld DP hworld).ConsistentWithTheory DP :=
  Classical.choose_spec (exists_consistentWithTheory DP hworld)

/-- Share-coefficient norm, omitting the trailing constant exactly as affine trader
magnitude does. -/
noncomputable def shareNorm (A : LUVCombination) (P : History) : ℝ :=
  (A.terms.map (fun p => |p.1.denote P|)).sum

/-- The paper's LUV-combination `L¹` norm, including the trailing constant. -/
noncomputable def l1Norm (A : LUVCombination) (P : History) : ℝ :=
  |A.const.denote P| + A.shareNorm P

/-- Expand every LUV term into its precision-`k` threshold bundle. -/
def meshAffine (A : LUVCombination) (k : ℕ) : AffineCombination where
  const := A.const
  terms := A.terms.flatMap (fun p =>
    ((p.2.expectAffine k).scale p.1).terms)

/-- Add a closed feature to the constant coordinate of an affine combination.  Unlike
`addConst`, this preserves the operational expression tree of a generated rational. -/
def addConstEF (A : AffineCombination) (e : EF) : AffineCombination where
  const := EF.add A.const e
  terms := A.terms

lemma addConstEF_value (A : AffineCombination) (e : EF)
    (V : History) (w : Valuation) :
    (addConstEF A e).value V w = A.value V w + e.denote V := by
  simp [addConstEF, AffineCombination.value]
  ring

lemma addConstEF_price (A : AffineCombination) (e : EF)
    (V : History) (n : ℕ) :
    (addConstEF A e).price V n = A.price V n + e.denote V := by
  simp [AffineCombination.price, addConstEF_value]

@[simp] theorem addConstEF_magnitude (A : AffineCombination) (e : EF)
    (V : History) :
    (addConstEF A e).magnitude V = A.magnitude V := rfl

def meshErrorFeature (n : ℕ) (b : ℚ) : EF :=
  EF.mul (EF.const (-(2 * b))) (EF.const (1 / (n : ℚ)))

@[simp] theorem meshErrorFeature_denote (n : ℕ) (b : ℚ) (P : History) :
    (meshErrorFeature n b).denote P = (-(2 * b / n) : ℚ) := by
  simp [meshErrorFeature]
  ring

/-- Appendix `lem:mesh`'s cross-precision gap.  It compares precision `n` with precision
`m` and subtracts the completed-world error allowance `2b/n`. -/
def meshGap (A : LUVCombination) (n m : ℕ) (b : ℚ) : AffineCombination :=
  addConstEF ((A.meshAffine n).sub (A.meshAffine m)) (meshErrorFeature n b)

/-- Reverse cross-precision gap for the lower half of `lem:mesh`. -/
def meshGapLower (A : LUVCombination) (n m : ℕ) (b : ℚ) : AffineCombination :=
  addConstEF ((A.meshAffine m).sub (A.meshAffine n)) (meshErrorFeature n b)

/-- Positive rational normalization used to feed an arbitrary bounded LUV mesh into
the unit-magnitude statistical affine hubs. -/
def meshNormScale (b : ℚ) : ℚ := 1 / (|b| + 1)

lemma meshNormScale_cast (b : ℚ) :
    ((meshNormScale b : ℚ) : ℝ) = 1 / (|(b : ℝ)| + 1) := by
  simp [meshNormScale]

lemma meshNormScale_pos (b : ℚ) : 0 < ((meshNormScale b : ℚ) : ℝ) := by
  rw [meshNormScale_cast]
  positivity

lemma meshNormScale_mul_le_one (b : ℚ) :
    ((meshNormScale b : ℚ) : ℝ) * (b : ℝ) ≤ 1 := by
  rw [meshNormScale_cast]
  have hden : 0 < |(b : ℝ)| + 1 := by positivity
  calc
    1 / (|(b : ℝ)| + 1) * (b : ℝ) ≤
        1 / (|(b : ℝ)| + 1) * |(b : ℝ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ = |(b : ℝ)| / (|(b : ℝ)| + 1) := by ring
    _ ≤ 1 := (div_le_one hden).2 (by linarith [abs_nonneg (b : ℝ)])

/-- The normalized diagonal threshold mesh. -/
def normalizedMesh (As : ℕ → LUVCombination) (b : ℚ) (n : ℕ) :
    AffineCombination :=
  ((As n).meshAffine n).scale (.const (meshNormScale b))

private lemma meshBlock_price
    (α : EF) (X : LUV) (P : History) (k m : ℕ) :
    ((((X.expectAffine k).scale α).terms.map
      (fun p => p.1.denote P * P m p.2)).sum) =
      α.denote P * X.expectApprox (P m) k := by
  have h := AffineCombination.scale_price α (X.expectAffine k) P m
  rw [LUV.expectAffine_priceAt] at h
  rw [AffineCombination.price, AffineCombination.value] at h
  simpa [AffineCombination.scale, LUV.expectAffine] using h

private lemma meshBlock_value
    (α : EF) (X : LUV) (P : History) (w : Valuation) (k : ℕ) :
    ((((X.expectAffine k).scale α).terms.map
      (fun p => p.1.denote P * w p.2)).sum) =
      α.denote P * X.expectApprox w k := by
  have h := AffineCombination.scale_value α (X.expectAffine k) P w
  rw [LUV.expectAffine_value] at h
  rw [AffineCombination.value] at h
  simpa [AffineCombination.scale, LUV.expectAffine] using h

/-- The lifted affine price is exactly the cross-day approximate expectation. -/
lemma meshAffine_price (A : LUVCombination) (P : History) (k m : ℕ) :
    (A.meshAffine k).price P m = A.expectAt P k m := by
  rw [AffineCombination.price, AffineCombination.value]
  simp only [meshAffine, expectAt]
  congr 1
  induction A.terms with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, meshBlock_price, ih]

@[simp] theorem meshAffine_price_diagonal
    (A : LUVCombination) (P : History) (n : ℕ) :
    (A.meshAffine n).price P n = A.expect P n := by
  rw [meshAffine_price]
  rfl

/-- In a world, the lifted affine value is the combination evaluated at the precision-`k`
threshold-bundle valuations. -/
lemma meshAffine_value (A : LUVCombination) (P : History)
    (w : Valuation) (k : ℕ) :
    (A.meshAffine k).value P w =
      A.value P (fun X => X.expectApprox w k) := by
  rw [AffineCombination.value]
  simp only [meshAffine, value]
  congr 1
  induction A.terms with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, meshBlock_value, ih]

/-- The common completed-theory value of the diagonal threshold mesh. -/
noncomputable def meshTheoryTruth (As : ℕ → LUVCombination) (P : History)
    (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) : ℝ :=
  ((As n).meshAffine n).value P (theoryWorld DP hworld).payout

lemma ExactTheoryPresentation.meshAffine_value_eq
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    ((As n).meshAffine n).value P v.payout = meshTheoryTruth As P DP hworld n := by
  rw [meshAffine_value]
  rw [meshTheoryTruth, meshAffine_value]
  unfold LUVCombination.value
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  change p.1.denote P * p.2.expectApprox v.payout n =
    p.1.denote P * p.2.expectApprox (theoryWorld DP hworld).payout n
  rw [h.expectApprox_eq v (theoryWorld DP hworld) hv
    (theoryWorld_consistent DP hworld) hp n]

private lemma meshValue_near_list
    (l : List (EF × LUV)) (P : History) (v : PCWorld) (ν : LUV → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hvals : ∀ p ∈ l, v.ValuesAt p.2 (ν p.2)) :
    |(l.map (fun p => p.1.denote P * p.2.expectApprox v.payout k)).sum -
        (l.map (fun p => p.1.denote P * ν p.2)).sum| ≤
      (l.map (fun p => |p.1.denote P|)).sum * (1 / (k : ℝ)) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      have hp := (hvals p (by simp)).expectApprox_near hk
      have hrest : ∀ q ∈ rest, v.ValuesAt q.2 (ν q.2) := by
        intro q hq
        exact hvals q (by simp [hq])
      have ht := ih hrest
      simp only [List.map_cons, List.sum_cons]
      calc
        |p.1.denote P * p.2.expectApprox v.payout k +
              (rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
            (p.1.denote P * ν p.2 +
              (rest.map (fun q => q.1.denote P * ν q.2)).sum)| =
            |p.1.denote P * (p.2.expectApprox v.payout k - ν p.2) +
              ((rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
                (rest.map (fun q => q.1.denote P * ν q.2)).sum)| := by ring_nf
        _ ≤ |p.1.denote P * (p.2.expectApprox v.payout k - ν p.2)| +
              |(rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
                (rest.map (fun q => q.1.denote P * ν q.2)).sum| := abs_add_le _ _
        _ = |p.1.denote P| * |p.2.expectApprox v.payout k - ν p.2| +
              |(rest.map (fun q => q.1.denote P * q.2.expectApprox v.payout k)).sum -
                (rest.map (fun q => q.1.denote P * ν q.2)).sum| := by rw [abs_mul]
        _ ≤ |p.1.denote P| * (1 / (k : ℝ)) +
              (rest.map (fun q => |q.1.denote P|)).sum * (1 / (k : ℝ)) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hp (abs_nonneg _)) ht
        _ = (|p.1.denote P| +
              (rest.map (fun q => |q.1.denote P|)).sum) * (1 / (k : ℝ)) := by ring

/-- Quantitative bridge from completed-world LUV values to the affine threshold mesh.
The approximation error is the share norm divided by the mesh precision. -/
lemma meshAffine_value_near (A : LUVCombination) (P : History)
    (v : PCWorld) (ν : LUV → ℝ) {k : ℕ} (hk : 0 < k)
    (hvals : A.ValuesAt v ν) :
    |(A.meshAffine k).value P v.payout - A.value P ν| ≤
      A.shareNorm P * (1 / (k : ℝ)) := by
  rw [meshAffine_value]
  simpa only [value, shareNorm, add_sub_add_left_eq_sub] using
    meshValue_near_list A.terms P v ν hk hvals

lemma shareNorm_nonneg (A : LUVCombination) (P : History) :
    0 ≤ A.shareNorm P :=
  List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact abs_nonneg _)

lemma l1Norm_nonneg (A : LUVCombination) (P : History) :
    0 ≤ A.l1Norm P :=
  add_nonneg (abs_nonneg _) (A.shareNorm_nonneg P)

lemma meshGap_price (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) (day : ℕ) :
    (A.meshGap n m b).price P day =
      A.expectAt P n day - A.expectAt P m day - (2 * (b : ℝ) / n) := by
  rw [meshGap, addConstEF_price, AffineCombination.sub_price,
    meshAffine_price, meshAffine_price]
  rw [meshErrorFeature_denote]
  push_cast
  ring

lemma meshGap_value_nonpos
    (A : LUVCombination) (P : History) (v : PCWorld) (ν : LUV → ℝ)
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) {b : ℚ}
    (hshare : A.shareNorm P ≤ (b : ℝ)) (hvals : A.ValuesAt v ν) :
    (A.meshGap n m b).value P v.payout ≤ 0 := by
  have hm : 0 < m := hn.trans_le hnm
  have hnnear := A.meshAffine_value_near P v ν hn hvals
  have hmnear := A.meshAffine_value_near P v ν hm hvals
  rw [abs_le] at hnnear hmnear
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hinv : (1 / (m : ℝ)) ≤ 1 / (n : ℝ) := by
    exact one_div_le_one_div_of_le hnR hnmR
  have hshare0 := A.shareNorm_nonneg P
  have hinvN : 0 ≤ 1 / (n : ℝ) := (one_div_pos.mpr hnR).le
  have hnerr : A.shareNorm P * (1 / (n : ℝ)) ≤ (b : ℝ) / n := by
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hshare hinvN)
  have hmerr : A.shareNorm P * (1 / (m : ℝ)) ≤ (b : ℝ) / n := by
    calc
      A.shareNorm P * (1 / (m : ℝ)) ≤ A.shareNorm P * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv hshare0
      _ ≤ (b : ℝ) / n := hnerr
  have hgap :
      (A.meshAffine n).value P v.payout - (A.meshAffine m).value P v.payout ≤
        2 * ((b : ℝ) / n) := by
    linarith [hnnear.2, hmnear.1]
  rw [meshGap, addConstEF_value, AffineCombination.sub_value]
  rw [meshErrorFeature_denote]
  push_cast
  ring_nf at hgap ⊢
  linarith

lemma meshGapLower_price (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) (day : ℕ) :
    (A.meshGapLower n m b).price P day =
      A.expectAt P m day - A.expectAt P n day - (2 * (b : ℝ) / n) := by
  rw [meshGapLower, addConstEF_price, AffineCombination.sub_price,
    meshAffine_price, meshAffine_price]
  rw [meshErrorFeature_denote]
  push_cast
  ring

lemma meshGapLower_value_nonpos
    (A : LUVCombination) (P : History) (v : PCWorld) (ν : LUV → ℝ)
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) {b : ℚ}
    (hshare : A.shareNorm P ≤ (b : ℝ)) (hvals : A.ValuesAt v ν) :
    (A.meshGapLower n m b).value P v.payout ≤ 0 := by
  have hm : 0 < m := hn.trans_le hnm
  have hnnear := A.meshAffine_value_near P v ν hn hvals
  have hmnear := A.meshAffine_value_near P v ν hm hvals
  rw [abs_le] at hnnear hmnear
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hinv : (1 / (m : ℝ)) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hnR hnmR
  have hshare0 := A.shareNorm_nonneg P
  have hinvN : 0 ≤ 1 / (n : ℝ) := (one_div_pos.mpr hnR).le
  have hnerr : A.shareNorm P * (1 / (n : ℝ)) ≤ (b : ℝ) / n := by
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hshare hinvN)
  have hmerr : A.shareNorm P * (1 / (m : ℝ)) ≤ (b : ℝ) / n := by
    calc
      A.shareNorm P * (1 / (m : ℝ)) ≤ A.shareNorm P * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv hshare0
      _ ≤ (b : ℝ) / n := hnerr
  have hgap :
      (A.meshAffine m).value P v.payout - (A.meshAffine n).value P v.payout ≤
        2 * ((b : ℝ) / n) := by
    linarith [hmnear.2, hnnear.1]
  rw [meshGapLower, addConstEF_value, AffineCombination.sub_value]
  rw [meshErrorFeature_denote]
  push_cast
  ring_nf at hgap ⊢
  linarith

/-! ### The concrete softmax used by `lem:mesh` -/

/-- Remaining unallocated softmax mass after scanning a list of affine gaps. -/
def softmaxRemainder (gaps : List AffineCombination) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) : EF :=
  match gaps with
  | [] => remaining
  | A :: rest =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      softmaxRemainder rest day threshold pad (.mul remaining (oneMinus signal))

/-- Continuous first-active softmax portfolio.  Each gap receives its threshold signal
times the mass not allocated to earlier gaps. -/
def softmaxAffine (gaps : List AffineCombination) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) : AffineCombination :=
  match gaps with
  | [] => AffineCombination.empty
  | A :: rest =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      let weight := EF.mul remaining signal
      (A.scale weight).add
        (softmaxAffine rest day threshold pad (.mul remaining (oneMinus signal)))

/-- Total allocated mass, stated semantically to keep the recursive syntax transparent. -/
noncomputable def softmaxMass (gaps : List AffineCombination) (P : History)
    (day : ℕ) (threshold pad : ℚ) (remaining : EF) : ℝ :=
  match gaps with
  | [] => 0
  | A :: rest =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      remaining.denote P * signal.denote P +
        softmaxMass rest P day threshold pad (.mul remaining (oneMinus signal))

lemma oneMinus_denote (e : EF) (P : History) :
    (oneMinus e).denote P = 1 - e.denote P := by
  simp [oneMinus, EF.denote_add, EF.denote_mul]
  ring

lemma softmax_mass_add_remainder
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) :
    softmaxMass gaps P day threshold pad remaining +
        (softmaxRemainder gaps day threshold pad remaining).denote P =
      remaining.denote P := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxMass, softmaxRemainder]
  | cons A rest ih =>
      simp only [softmaxMass, softmaxRemainder]
      rw [add_assoc, ih]
      simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
      ring

lemma softmaxRemainder_nonneg
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (hrem : 0 ≤ remaining.denote P) :
    0 ≤ (softmaxRemainder gaps day threshold pad remaining).denote P := by
  induction gaps generalizing remaining with
  | nil => simpa [softmaxRemainder]
  | cons A rest ih =>
      simp only [softmaxRemainder]
      apply ih
      simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
      exact mul_nonneg hrem (sub_nonneg.mpr (sellIndF_mem _ _ _ P).2)

lemma softmaxMass_nonneg
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (hrem : 0 ≤ remaining.denote P) :
    0 ≤ softmaxMass gaps P day threshold pad remaining := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxMass]
  | cons A rest ih =>
      simp only [softmaxMass]
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hnew : 0 ≤ (EF.mul remaining
          (oneMinus (sellIndF (A.priceFeature day) threshold pad))).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      exact add_nonneg (mul_nonneg hrem hsig.1) (ih _ hnew)

/-- A first-active softmax of uniformly magnitude-bounded inputs has the same magnitude
bound: its nonnegative allocation weights have total mass at most the initial mass. -/
lemma softmaxAffine_magnitude_le
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (C : ℝ)
    (hrem : 0 ≤ remaining.denote P) (hC : 0 ≤ C)
    (hgaps : ∀ A ∈ gaps, A.magnitude P ≤ C) :
    (softmaxAffine gaps day threshold pad remaining).magnitude P ≤
      remaining.denote P * C := by
  induction gaps generalizing remaining with
  | nil =>
      simp only [softmaxAffine, AffineCombination.empty, AffineCombination.magnitude,
        List.map_nil, List.sum_nil]
      exact mul_nonneg hrem hC
  | cons A rest ih =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hnew : 0 ≤ (EF.mul remaining (oneMinus signal)).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih (.mul remaining (oneMinus signal)) hnew
        (fun B hB ↦ hgaps B (by simp [hB]))
      have hA := hgaps A (by simp)
      have hweight :
          |(EF.mul remaining signal).denote P| =
            remaining.denote P * signal.denote P := by
        rw [EF.denote_mul, Pi.mul_apply,
          abs_of_nonneg (mul_nonneg hrem hsig.1)]
      simp only [softmaxAffine]
      rw [AffineCombination.add_magnitude, AffineCombination.scale_magnitude, hweight]
      simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote] at htail
      have hheadMul := mul_le_mul_of_nonneg_left hA
        (mul_nonneg hrem hsig.1)
      have htailMul := mul_le_mul_of_nonneg_left hC
        (mul_nonneg hrem (sub_nonneg.mpr hsig.2))
      nlinarith

/-- Price analogue of `softmaxAffine_magnitude_le`. -/
lemma abs_softmaxAffine_price_le
    (gaps : List AffineCombination) (P : History) (day priceDay : ℕ)
    (threshold pad : ℚ) (remaining : EF) (C : ℝ)
    (hrem : 0 ≤ remaining.denote P) (hC : 0 ≤ C)
    (hgaps : ∀ A ∈ gaps, |A.price P priceDay| ≤ C) :
    |(softmaxAffine gaps day threshold pad remaining).price P priceDay| ≤
      remaining.denote P * C := by
  induction gaps generalizing remaining with
  | nil =>
      simp only [softmaxAffine, AffineCombination.empty, AffineCombination.price,
        AffineCombination.value, List.map_nil, List.sum_nil, add_zero, EF.denote_const,
        Rat.cast_zero, abs_zero]
      exact mul_nonneg hrem hC
  | cons A rest ih =>
      let signal := sellIndF (A.priceFeature day) threshold pad
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hnew : 0 ≤ (EF.mul remaining (oneMinus signal)).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih (.mul remaining (oneMinus signal)) hnew
        (fun B hB ↦ hgaps B (by simp [hB]))
      have hA := hgaps A (by simp)
      simp only [softmaxAffine, AffineCombination.add_price,
        AffineCombination.scale_price, EF.denote_mul, Pi.mul_apply]
      calc
        |remaining.denote P * signal.denote P * A.price P priceDay +
            (softmaxAffine rest day threshold pad
              (remaining.mul (oneMinus signal))).price P priceDay| ≤
            |remaining.denote P * signal.denote P * A.price P priceDay| +
              |(softmaxAffine rest day threshold pad
                (remaining.mul (oneMinus signal))).price P priceDay| := by
          exact abs_add_le _ _
        _ = remaining.denote P * signal.denote P * |A.price P priceDay| +
              |(softmaxAffine rest day threshold pad
                (remaining.mul (oneMinus signal))).price P priceDay| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hrem, abs_of_nonneg hsig.1]
        _ ≤ remaining.denote P * signal.denote P * C +
              (remaining.mul (oneMinus signal)).denote P * C :=
          add_le_add
            (mul_le_mul_of_nonneg_left hA (mul_nonneg hrem hsig.1)) htail
        _ = remaining.denote P * C := by
          simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
          ring

lemma softmaxAffine_value_nonpos
    (gaps : List AffineCombination) (P : History) (w : Valuation) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (hrem : 0 ≤ remaining.denote P)
    (hgaps : ∀ A ∈ gaps, A.value P w ≤ 0) :
    (softmaxAffine gaps day threshold pad remaining).value P w ≤ 0 := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxAffine, AffineCombination.empty, AffineCombination.value]
  | cons A rest ih =>
      simp only [softmaxAffine, AffineCombination.add_value,
        AffineCombination.scale_value]
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hweight : 0 ≤ remaining.denote P *
          (sellIndF (A.priceFeature day) threshold pad).denote P :=
        mul_nonneg hrem hsig.1
      have hnew : 0 ≤ (EF.mul remaining
          (oneMinus (sellIndF (A.priceFeature day) threshold pad))).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih _ hnew (fun B hB => hgaps B (by simp [hB]))
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hweight (hgaps A (by simp))) htail

lemma softmaxRemainder_eq_zero_of_signal_one
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF)
    (hdet : ∃ A ∈ gaps,
      (sellIndF (A.priceFeature day) threshold pad).denote P = 1) :
    (softmaxRemainder gaps day threshold pad remaining).denote P = 0 := by
  induction gaps generalizing remaining with
  | nil => simp at hdet
  | cons A rest ih =>
      obtain ⟨B, hB, hsignal⟩ := hdet
      simp only [List.mem_cons] at hB
      simp only [softmaxRemainder]
      rcases hB with hBA | hB
      · subst B
        have hzero : (EF.mul remaining
            (oneMinus (sellIndF (A.priceFeature day) threshold pad))).denote P = 0 := by
          rw [EF.denote_mul, Pi.mul_apply, oneMinus_denote, hsignal]
          ring
        have hz : ∀ l : List AffineCombination, ∀ e : EF, e.denote P = 0 →
            (softmaxRemainder l day threshold pad e).denote P = 0 := by
          intro l
          induction l with
          | nil => intro e he; simpa [softmaxRemainder] using he
          | cons C tail iht =>
              intro e he
              simp only [softmaxRemainder]
              apply iht
              simp [EF.denote_mul, he]
        exact hz rest _ hzero
      · exact ih _ ⟨B, hB, hsignal⟩

lemma softmaxMass_eq_remaining_of_signal_one
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF)
    (hdet : ∃ A ∈ gaps,
      (sellIndF (A.priceFeature day) threshold pad).denote P = 1) :
    softmaxMass gaps P day threshold pad remaining = remaining.denote P := by
  have hzero := softmaxRemainder_eq_zero_of_signal_one
    gaps P day threshold pad remaining hdet
  have hid := softmax_mass_add_remainder gaps P day threshold pad remaining
  linarith

lemma softmaxAffine_price_ge_mass
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (remaining : EF) (hrem : 0 ≤ remaining.denote P)
    (q : ℝ)
    (hactive : ∀ A ∈ gaps,
      0 < (sellIndF (A.priceFeature day) threshold pad).denote P →
        q ≤ A.price P day) :
    q * softmaxMass gaps P day threshold pad remaining ≤
      (softmaxAffine gaps day threshold pad remaining).price P day := by
  induction gaps generalizing remaining with
  | nil => simp [softmaxMass, softmaxAffine, AffineCombination.empty,
      AffineCombination.price, AffineCombination.value]
  | cons A rest ih =>
      simp only [softmaxMass, softmaxAffine, AffineCombination.add_price,
        AffineCombination.scale_price, EF.denote_mul, Pi.mul_apply]
      let signal := sellIndF (A.priceFeature day) threshold pad
      have hsig := sellIndF_mem (A.priceFeature day) threshold pad P
      have hweight : 0 ≤ remaining.denote P * signal.denote P :=
        mul_nonneg hrem hsig.1
      have hhead : q * (remaining.denote P * signal.denote P) ≤
          remaining.denote P * signal.denote P * A.price P day := by
        by_cases hz : signal.denote P = 0
        · simp [hz]
        · have hspos : 0 < signal.denote P := lt_of_le_of_ne hsig.1 (Ne.symm hz)
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left (hactive A (by simp) hspos) hweight)
      have hnew : 0 ≤ (EF.mul remaining (oneMinus signal)).denote P := by
        simp only [EF.denote_mul, Pi.mul_apply, oneMinus_denote]
        exact mul_nonneg hrem (sub_nonneg.mpr hsig.2)
      have htail := ih (.mul remaining (oneMinus signal)) hnew
        (fun B hB hs => hactive B (by simp [hB]) hs)
      dsimp only [signal] at hhead hnew htail ⊢
      linarith

lemma softmaxAffine_price_ge_threshold_sub_pad_of_detected
    (gaps : List AffineCombination) (P : History) (day : ℕ)
    (threshold pad : ℚ) (hpad : 0 < (pad : ℝ))
    (hdet : ∃ A ∈ gaps, (threshold : ℝ) < A.price P day) :
    (threshold : ℝ) - pad ≤
      (softmaxAffine gaps day threshold pad (.const 1)).price P day := by
  have hsignal : ∃ A ∈ gaps,
      (sellIndF (A.priceFeature day) threshold pad).denote P = 1 := by
    obtain ⟨A, hA, hprice⟩ := hdet
    refine ⟨A, hA, ?_⟩
    apply sellIndF_eq_one hpad
    rw [A.priceFeature_denote]
    exact hprice
  have hmass := softmaxMass_eq_remaining_of_signal_one
    gaps P day threshold pad (.const 1) hsignal
  have hlower := softmaxAffine_price_ge_mass gaps P day threshold pad (.const 1)
    (by simp) ((threshold : ℝ) - pad) (by
      intro A hA hpos
      have h := sellIndF_pos_imp hpad hpos
      rw [A.priceFeature_denote] at h
      exact h.le)
  simp only [EF.denote_const] at hmass hlower
  rw [hmass] at hlower
  simpa using hlower

/-- All cross-precision gaps considered by the day-`m` softmax (`n = 1, …, m`). -/
def meshGaps (As : ℕ → LUVCombination) (m : ℕ) (b : ℚ) :
    List AffineCombination :=
  (List.range m).map (fun i => (As (i + 1)).meshGap (i + 1) m b)

/-- The actual Appendix softmax sequence for the upper half of `lem:mesh`. -/
def meshSoftmax (As : ℕ → LUVCombination) (b ε : ℚ) (m : ℕ) :
    AffineCombination :=
  softmaxAffine (meshGaps As m b) m (ε / 2) (ε / 4) (.const 1)

def meshGapsLower (As : ℕ → LUVCombination) (m : ℕ) (b : ℚ) :
    List AffineCombination :=
  (List.range m).map (fun i => (As (i + 1)).meshGapLower (i + 1) m b)

/-- Reverse-gap softmax for the lower half of `lem:mesh`. -/
def meshSoftmaxLower (As : ℕ → LUVCombination) (b ε : ℚ) (m : ℕ) :
    AffineCombination :=
  softmaxAffine (meshGapsLower As m b) m (ε / 2) (ε / 4) (.const 1)

lemma meshSoftmax_value_nonpos
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (hvalued : WorldValued As DP) {b ε : ℚ}
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    (meshSoftmax As b ε m).value P v.payout ≤ 0 := by
  apply softmaxAffine_value_nonpos
  · simp
  · intro A hA
    simp only [meshGaps, List.mem_map, List.mem_range] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    obtain ⟨ν, hvals⟩ := hvalued (i + 1) v hv
    apply meshGap_value_nonpos (As (i + 1)) P v ν (by omega) (by omega)
      (hshare (i + 1)) hvals

lemma meshSoftmax_detects_upper_gap
    {As : ℕ → LUVCombination} {P : History} {b ε : ℚ}
    (hε : 0 < (ε : ℝ)) {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hgap : (ε : ℝ) <
      (As n).expectAt P n m - (As n).expectAt P m m - 2 * (b : ℝ) / n) :
    (ε : ℝ) / 4 ≤ (meshSoftmax As b ε m).price P m := by
  have hdet : ∃ A ∈ meshGaps As m b,
      (((ε / 2 : ℚ) : ℝ)) < A.price P m := by
    let i := n - 1
    have hi : i < m := by dsimp [i]; omega
    have hin : i + 1 = n := by dsimp [i]; omega
    refine ⟨(As n).meshGap n m b, ?_, ?_⟩
    · simp only [meshGaps, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [hin]⟩
    · rw [meshGap_price]
      push_cast
      linarith
  have hsoft := softmaxAffine_price_ge_threshold_sub_pad_of_detected
    (meshGaps As m b) P m (ε / 2) (ε / 4) (by
      push_cast
      linarith) hdet
  dsimp only [meshSoftmax]
  push_cast at hsoft ⊢
  linarith

lemma meshSoftmaxLower_value_nonpos
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (hvalued : WorldValued As DP) {b ε : ℚ}
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory DP) :
    (meshSoftmaxLower As b ε m).value P v.payout ≤ 0 := by
  apply softmaxAffine_value_nonpos
  · simp
  · intro A hA
    simp only [meshGapsLower, List.mem_map, List.mem_range] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    obtain ⟨ν, hvals⟩ := hvalued (i + 1) v hv
    apply meshGapLower_value_nonpos (As (i + 1)) P v ν (by omega) (by omega)
      (hshare (i + 1)) hvals

lemma meshSoftmaxLower_detects_gap
    {As : ℕ → LUVCombination} {P : History} {b ε : ℚ}
    (hε : 0 < (ε : ℝ)) {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hgap : (ε : ℝ) <
      (As n).expectAt P m m - (As n).expectAt P n m - 2 * (b : ℝ) / n) :
    (ε : ℝ) / 4 ≤ (meshSoftmaxLower As b ε m).price P m := by
  have hdet : ∃ A ∈ meshGapsLower As m b,
      (((ε / 2 : ℚ) : ℝ)) < A.price P m := by
    let i := n - 1
    have hi : i < m := by dsimp [i]; omega
    have hin : i + 1 = n := by dsimp [i]; omega
    refine ⟨(As n).meshGapLower n m b, ?_, ?_⟩
    · simp only [meshGapsLower, List.mem_map, List.mem_range]
      exact ⟨i, hi, by rw [hin]⟩
    · rw [meshGapLower_price]
      push_cast
      linarith
  have hsoft := softmaxAffine_price_ge_threshold_sub_pad_of_detected
    (meshGapsLower As m b) P m (ε / 2) (ε / 4) (by
      push_cast
      linarith) hdet
  dsimp only [meshSoftmaxLower]
  push_cast at hsoft ⊢
  linarith

/-- Narrow operational boundary for the concrete softmax syntax.  It certifies only
uniform emission and structural boundedness of `meshSoftmax`; all completed-world
semantics, gap detection, and market conclusions are proved outside this structure.
Paper node: the finite soft-max mesh of App. `mesh`, serving `thm:wubexp`. -/
structure MeshSoftmaxOperationalWitness
    (As : ℕ → LUVCombination) (P : History) where
  poly : ∀ b ε : ℚ,
    AffineCombination.PolySequence (meshSoftmax As b ε)
  bounded : ∀ b ε : ℚ,
    BoundedAffinePrices (meshSoftmax As b ε) P
  magnitude : ∀ b ε : ℚ,
    ∃ C : ℝ, ∀ m, (meshSoftmax As b ε m).magnitude P ≤ C
  lower_poly : ∀ b ε : ℚ,
    AffineCombination.PolySequence (meshSoftmaxLower As b ε)
  lower_bounded : ∀ b ε : ℚ,
    BoundedAffinePrices (meshSoftmaxLower As b ε) P
  lower_magnitude : ∀ b ε : ℚ,
    ∃ C : ℝ, ∀ m, (meshSoftmaxLower As b ε m).magnitude P ≤ C

/-- Upper half of Appendix `lem:mesh`: after the softmax compiler has emitted the
concrete sequence, no cross-precision upper discrepancy can exceed `2b/n + ε`
infinitely often. -/
theorem mesh_upper_eventually
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP) (b ε : ℚ) (hε : 0 < (ε : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ m in atTop, ∀ n, 0 < n → n ≤ m →
      (As n).expectAt P n m - (As n).expectAt P m m ≤
        2 * (b : ℝ) / n + (ε : ℝ) := by
  have hlearn := (ops.poly b ε).affine_provind_theory_le P DP
    (ops.bounded b ε) (ops.magnitude b ε) hP hworld 0
    (fun m v hv => meshSoftmax_value_nonpos hvalued hshare m v hv)
  have hevent := hlearn ((ε : ℝ) / 8) (by positivity)
  filter_upwards [hevent] with m hm
  intro n hn hnm
  by_contra hnot
  have hgap : (ε : ℝ) <
      (As n).expectAt P n m - (As n).expectAt P m m - 2 * (b : ℝ) / n := by
    push_neg at hnot
    linarith
  have hdetect := meshSoftmax_detects_upper_gap hε hn hnm hgap
  change (meshSoftmax As b ε m).price P m ≤ 0 + (ε : ℝ) / 8 at hm
  linarith

lemma mesh_lower_eventually
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP) (b ε : ℚ) (hε : 0 < (ε : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ m in atTop, ∀ n, 0 < n → n ≤ m →
      (As n).expectAt P m m - (As n).expectAt P n m ≤
        2 * (b : ℝ) / n + (ε : ℝ) := by
  have hlearn := (ops.lower_poly b ε).affine_provind_theory_le P DP
    (ops.lower_bounded b ε) (ops.lower_magnitude b ε) hP hworld 0
    (fun m v hv => meshSoftmaxLower_value_nonpos hvalued hshare m v hv)
  have hevent := hlearn ((ε : ℝ) / 8) (by positivity)
  filter_upwards [hevent] with m hm
  intro n hn hnm
  by_contra hnot
  have hgap : (ε : ℝ) <
      (As n).expectAt P m m - (As n).expectAt P n m - 2 * (b : ℝ) / n := by
    push_neg at hnot
    linarith
  have hdetect := meshSoftmaxLower_detects_gap hε hn hnm hgap
  change (meshSoftmaxLower As b ε m).price P m ≤ 0 + (ε : ℝ) / 8 at hm
  linarith

/-- Two-sided finite form of Appendix `lem:mesh`. -/
theorem mesh_close_eventually
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP) (b ε : ℚ) (hε : 0 < (ε : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ᶠ m in atTop, ∀ n, 0 < n → n ≤ m →
      |(As n).expectAt P n m - (As n).expectAt P m m| ≤
        2 * (b : ℝ) / n + (ε : ℝ) := by
  filter_upwards [mesh_upper_eventually ops hvalued b ε hε hshare hP hworld,
    mesh_lower_eventually ops hvalued b ε hε hshare hP hworld] with m hu hl
  intro n hn hnm
  rw [abs_le]
  constructor
  · linarith [hl n hn hnm]
  · exact hu n hn hnm

/-- Operational certificate for a polynomial LUV-combination sequence.  The field is
the exact compiled threshold mesh consumed by the affine theorems; it contains no market,
world-value, convergence, or learning conclusion.
Paper node: a `def:ec`-style polynomial certificate for a `def:luv` sequence. -/
structure PolySequence (As : ℕ → LUVCombination) where
  mesh_poly : AffineCombination.PolySequence (fun n => (As n).meshAffine n)

/-- `def:blcp`: a polynomially generated LUV-combination sequence with one uniform full
coefficient `L¹` bound. -/
structure BoundedSequence (As : ℕ → LUVCombination) (P : History) where
  poly : PolySequence As
  bounded : ∃ B : ℝ, ∀ n, (As n).l1Norm P ≤ B

/-- Propositional representation boundary needed to invoke `thm:ec` on every LUV
appearing in a combination sequence.  It records only compact threshold codeability and
daily world valuation; it does not assume convergence or any expectation theorem. -/
structure ConvergencePresentation (As : ℕ → LUVCombination)
    (DP : DeductiveProcess) where
  threshold_code : ∀ n p, p ∈ (As n).terms → p.2.PolyThresholdCodes
  daily_value : ∀ n p, p ∈ (As n).terms → ∀ m (v : PCWorld),
    v.ConsistentWith (DP.D m) → ∃ x : ℝ, v.ValuesAt p.2 x

/-- The paper's future expectation extrema use each future day's own mesh. -/
noncomputable def futureLow (As : ℕ → LUVCombination)
    (P : History) (n : ℕ) : ℝ :=
  sInf (Set.range (fun j => (As n).expect P (n + j)))

noncomputable def futureHigh (As : ℕ → LUVCombination)
    (P : History) (n : ℕ) : ℝ :=
  sSup (Set.range (fun j => (As n).expect P (n + j)))

private lemma meshBlock_magnitude_le
    (α : EF) (X : LUV) (P : History) (k : ℕ) :
    ((X.expectAffine k).scale α).magnitude P ≤ |α.denote P| := by
  rw [AffineCombination.scale_magnitude]
  have hX := X.expectAffine_magnitude_le_one P k
  exact mul_le_of_le_one_right (abs_nonneg _) hX

/-- Mesh expansion does not increase share magnitude. -/
lemma meshAffine_magnitude_le_shareNorm
    (A : LUVCombination) (P : History) (k : ℕ) :
    (A.meshAffine k).magnitude P ≤ A.shareNorm P := by
  simp only [AffineCombination.magnitude, meshAffine, shareNorm]
  induction A.terms with
  | nil => simp
  | cons p rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      have hp := meshBlock_magnitude_le p.1 p.2 P k
      simp only [AffineCombination.magnitude] at hp
      linarith

lemma meshGap_magnitude_le (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) :
    (A.meshGap n m b).magnitude P ≤ 2 * A.shareNorm P := by
  rw [meshGap, addConstEF_magnitude, AffineCombination.sub_magnitude]
  linarith [A.meshAffine_magnitude_le_shareNorm P n,
    A.meshAffine_magnitude_le_shareNorm P m]

lemma meshGapLower_magnitude_le (A : LUVCombination) (P : History)
    (n m : ℕ) (b : ℚ) :
    (A.meshGapLower n m b).magnitude P ≤ 2 * A.shareNorm P := by
  rw [meshGapLower, addConstEF_magnitude, AffineCombination.sub_magnitude]
  linarith [A.meshAffine_magnitude_le_shareNorm P n,
    A.meshAffine_magnitude_le_shareNorm P m]

/-- Mesh expansion does not increase the full `L¹` norm. -/
lemma meshAffine_l1Norm_le (A : LUVCombination) (P : History) (k : ℕ) :
    (A.meshAffine k).l1Norm P ≤ A.l1Norm P := by
  simp only [AffineCombination.l1Norm, l1Norm, meshAffine]
  exact add_le_add le_rfl (A.meshAffine_magnitude_le_shareNorm P k)

lemma abs_expectAt_le_l1Norm
    (A : LUVCombination) (P : History) (k m : ℕ)
    (hP : ∀ φ, 0 ≤ P m φ ∧ P m φ ≤ 1) :
    |A.expectAt P k m| ≤ A.l1Norm P := by
  rw [← meshAffine_price]
  exact ((A.meshAffine k).abs_price_le_l1Norm P m hP).trans
    (A.meshAffine_l1Norm_le P k)

lemma abs_meshGap_price_le (A : LUVCombination) (P : History)
    {n m day : ℕ} (hn : 0 < n) (b : ℚ) (B : ℝ)
    (hB : A.l1Norm P ≤ B) (hP : ∀ φ, 0 ≤ P day φ ∧ P day φ ≤ 1) :
    |(A.meshGap n m b).price P day| ≤ 2 * B + 2 * |(b : ℝ)| := by
  have hnExp := A.abs_expectAt_le_l1Norm P n day hP
  have hmExp := A.abs_expectAt_le_l1Norm P m day hP
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact hnR
  have hz : |2 * (b : ℝ) / n| ≤ 2 * |(b : ℝ)| := by
    rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact div_le_self (mul_nonneg (by norm_num) (abs_nonneg _)) hden
  rw [meshGap_price]
  calc
    |A.expectAt P n day - A.expectAt P m day - 2 * (b : ℝ) / n| ≤
        |A.expectAt P n day| + |A.expectAt P m day| + |2 * (b : ℝ) / n| := by
      linarith [abs_sub (A.expectAt P n day) (A.expectAt P m day),
        abs_sub (A.expectAt P n day - A.expectAt P m day) (2 * (b : ℝ) / n)]
    _ ≤ 2 * B + 2 * |(b : ℝ)| := by linarith

lemma abs_meshGapLower_price_le (A : LUVCombination) (P : History)
    {n m day : ℕ} (hn : 0 < n) (b : ℚ) (B : ℝ)
    (hB : A.l1Norm P ≤ B) (hP : ∀ φ, 0 ≤ P day φ ∧ P day φ ≤ 1) :
    |(A.meshGapLower n m b).price P day| ≤ 2 * B + 2 * |(b : ℝ)| := by
  have hnExp := A.abs_expectAt_le_l1Norm P n day hP
  have hmExp := A.abs_expectAt_le_l1Norm P m day hP
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact hnR
  have hz : |2 * (b : ℝ) / n| ≤ 2 * |(b : ℝ)| := by
    rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    exact div_le_self (mul_nonneg (by norm_num) (abs_nonneg _)) hden
  rw [meshGapLower_price]
  calc
    |A.expectAt P m day - A.expectAt P n day - 2 * (b : ℝ) / n| ≤
        |A.expectAt P m day| + |A.expectAt P n day| + |2 * (b : ℝ) / n| := by
      linarith [abs_sub (A.expectAt P m day) (A.expectAt P n day),
        abs_sub (A.expectAt P m day - A.expectAt P n day) (2 * (b : ℝ) / n)]
    _ ≤ 2 * B + 2 * |(b : ℝ)| := by linarith

/-- Tail supremum appearing literally in Appendix `lem:mesh`. -/
noncomputable def meshTailError (As : ℕ → LUVCombination)
    (P : History) (n : ℕ) : ℝ :=
  sSup (Set.range (fun j =>
    |(As n).expectAt P n (n + j) - (As n).expectAt P (n + j) (n + j)|))

lemma BoundedSequence.meshTailError_bddAbove
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    BddAbove (Set.range (fun j =>
      |(As n).expectAt P n (n + j) - (As n).expectAt P (n + j) (n + j)|)) := by
  obtain ⟨B, hB⟩ := h.bounded
  have hB0 : 0 ≤ B := (As 0).l1Norm_nonneg P |>.trans (hB 0)
  refine ⟨2 * B, ?_⟩
  rintro x ⟨j, rfl⟩
  have hcoarse := (As n).abs_expectAt_le_l1Norm P n (n + j) (hP (n + j))
  have hfine := (As n).abs_expectAt_le_l1Norm P (n + j) (n + j) (hP (n + j))
  calc
    |(As n).expectAt P n (n + j) - (As n).expectAt P (n + j) (n + j)|
        ≤ |(As n).expectAt P n (n + j)| +
          |(As n).expectAt P (n + j) (n + j)| := abs_sub _ _
    _ ≤ B + B := add_le_add (hcoarse.trans (hB n)) (hfine.trans (hB n))
    _ = 2 * B := by ring

lemma BoundedSequence.meshTailError_nonneg
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    0 ≤ meshTailError As P n := by
  apply le_csSup (h.meshTailError_bddAbove hP n)
  exact ⟨0, by simp⟩

lemma meshTailError_le
    {As : ℕ → LUVCombination} {P : History}
    {n : ℕ} {δ : ℝ}
    (hδ : ∀ m, n ≤ m →
      |(As n).expectAt P n m - (As n).expectAt P m m| ≤ δ) :
    meshTailError As P n ≤ δ := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨j, rfl⟩
  exact hδ (n + j) (by omega)

private lemma abs_sSup_range_sub_sSup_range_le
    (f g : ℕ → ℝ)
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (he : BddAbove (Set.range (fun j => |f j - g j|))) :
    |sSup (Set.range f) - sSup (Set.range g)| ≤
      sSup (Set.range (fun j => |f j - g j|)) := by
  let E := sSup (Set.range (fun j => |f j - g j|))
  have hfg : sSup (Set.range f) ≤ sSup (Set.range g) + E := by
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hgj := le_csSup hg ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [le_abs_self (f j - g j)]
  have hgf : sSup (Set.range g) ≤ sSup (Set.range f) + E := by
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hfj := le_csSup hf ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [neg_le_abs (f j - g j)]
  rw [abs_le]
  constructor <;> dsimp only [E] at * <;> linarith

private lemma abs_sInf_range_sub_sInf_range_le
    (f g : ℕ → ℝ)
    (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g))
    (he : BddAbove (Set.range (fun j => |f j - g j|))) :
    |sInf (Set.range f) - sInf (Set.range g)| ≤
      sSup (Set.range (fun j => |f j - g j|)) := by
  let E := sSup (Set.range (fun j => |f j - g j|))
  have hgf : sInf (Set.range g) - E ≤ sInf (Set.range f) := by
    apply le_csInf (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hgj := csInf_le hg ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [neg_le_abs (f j - g j)]
  have hfg : sInf (Set.range f) - E ≤ sInf (Set.range g) := by
    apply le_csInf (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    have hfj := csInf_le hf ⟨j, rfl⟩
    have hej := le_csSup he ⟨j, rfl⟩
    dsimp only [E] at hej ⊢
    linarith [le_abs_self (f j - g j)]
  rw [abs_le]
  constructor <;> dsimp only [E] at * <;> linarith

private lemma abs_sInf_sub_sInf_le_of_mutually_near
    (S T : Set ℝ) (E : ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSb : BddBelow S) (hTb : BddBelow T)
    (hST : ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ E)
    (hTS : ∀ y ∈ T, ∃ x ∈ S, |x - y| ≤ E) :
    |sInf S - sInf T| ≤ E := by
  have hTSinf : sInf T - E ≤ sInf S := by
    apply le_csInf hS
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hST x hx
    have hyinf := csInf_le hTb hy
    rw [abs_le] at hxy
    linarith
  have hSTinf : sInf S - E ≤ sInf T := by
    apply le_csInf hT
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hTS y hy
    have hxinf := csInf_le hSb hx
    rw [abs_le] at hxy
    linarith
  rw [abs_le]
  constructor <;> linarith

private lemma abs_sSup_sub_sSup_le_of_mutually_near
    (S T : Set ℝ) (E : ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSb : BddAbove S) (hTb : BddAbove T)
    (hST : ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ E)
    (hTS : ∀ y ∈ T, ∃ x ∈ S, |x - y| ≤ E) :
    |sSup S - sSup T| ≤ E := by
  have hSTsup : sSup S ≤ sSup T + E := by
    apply csSup_le hS
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hST x hx
    have hysup := le_csSup hTb hy
    rw [abs_le] at hxy
    linarith
  have hTSsup : sSup T ≤ sSup S + E := by
    apply csSup_le hT
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hTS y hy
    have hxsup := le_csSup hSb hx
    rw [abs_le] at hxy
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Bounded real sequences with a vanishing pointwise difference have the same lower
and upper limits.  This is the analytic transfer used after Appendix `lem:mesh`. -/
private theorem liminf_limsup_eq_of_abs_sub_tendsto_zero
    (f g : ℕ → ℝ)
    (hglo : IsBoundedUnder (· ≥ ·) atTop g)
    (hghi : IsBoundedUnder (· ≤ ·) atTop g)
    (hnear : Tendsto (fun n => |f n - g n|) atTop (𝓝 0)) :
    liminf f atTop = liminf g atTop ∧ limsup f atTop = limsup g atTop := by
  let d : ℕ → ℝ := fun n => f n - g n
  have hdabs : Tendsto (abs ∘ d) atTop (𝓝 0) := by
    simpa only [d, Function.comp_apply] using hnear
  have hd : Tendsto d atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero d).2 hdabs
  have hdsmall : ∀ᶠ n in atTop, |d n| < 1 := by
    have hball := hd.eventually (Metric.ball_mem_nhds 0 zero_lt_one)
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hball
  have hdlo : IsBoundedUnder (· ≥ ·) atTop d :=
    isBoundedUnder_of_eventually_ge (a := (-1 : ℝ))
      (hdsmall.mono fun n hn => by linarith [neg_le_abs (d n)])
  have hdhi : IsBoundedUnder (· ≤ ·) atTop d :=
    isBoundedUnder_of_eventually_le (a := (1 : ℝ))
      (hdsmall.mono fun n hn => by linarith [le_abs_self (d n)])
  have hdinf : liminf d atTop = 0 := hd.liminf_eq
  have hdsup : limsup d atTop = 0 := hd.limsup_eq
  constructor
  · have hlo : liminf g atTop + liminf d atTop ≤ liminf f atTop :=
      (le_liminf_add hglo hghi hdlo hdhi.isCobounded_flip).trans_eq
        (liminf_congr (Eventually.of_forall fun n => by
          change g n + d n = f n
          dsimp only [d]
          ring))
    have hhi : liminf f atTop ≤ limsup d atTop + liminf g atTop :=
      (liminf_congr (Eventually.of_forall fun n => by
        change f n = d n + g n
        dsimp only [d]
        ring)).trans_le
        (liminf_add_le hdlo hdhi hglo hghi.isCobounded_flip)
    rw [hdinf, add_zero] at hlo
    rw [hdsup, zero_add] at hhi
    exact le_antisymm hhi hlo
  · have hlo : limsup g atTop + liminf d atTop ≤ limsup f atTop :=
      (le_limsup_add hghi hglo.isCobounded_flip hdhi hdlo).trans_eq
        (limsup_congr (Eventually.of_forall fun n => by
          change g n + d n = f n
          dsimp only [d]
          ring))
    have hhi : limsup f atTop ≤ limsup g atTop + limsup d atTop :=
      (limsup_congr (Eventually.of_forall fun n => by
        change f n = g n + d n
        dsimp only [d]
        ring)).trans_le
        (limsup_add_le hglo hghi hdlo.isCobounded_flip hdhi)
    rw [hdinf, add_zero] at hlo
    rw [hdsup, add_zero] at hhi
    exact le_antisymm hhi hlo

lemma BoundedSequence.futureHigh_mesh_near
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    |affineFutureHigh (fun i => (As i).meshAffine i) P n - futureHigh As P n| ≤
      meshTailError As P n := by
  obtain ⟨B, hB⟩ := h.bounded
  have hcoarse : BddAbove (Set.range (fun j => (As n).expectAt P n (n + j))) := by
    refine ⟨B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans
      ((As n).abs_expectAt_le_l1Norm P n (n + j) (hP (n + j)) |>.trans (hB n))
  have hfine : BddAbove (Set.range (fun j => (As n).expectAt P (n + j) (n + j))) := by
    refine ⟨B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans
      ((As n).abs_expectAt_le_l1Norm P (n + j) (n + j) (hP (n + j)) |>.trans (hB n))
  simpa only [affineFutureHigh, meshAffine_price, futureHigh, meshTailError] using
    abs_sSup_range_sub_sSup_range_le
      (fun j => (As n).expectAt P n (n + j))
      (fun j => (As n).expectAt P (n + j) (n + j)) hcoarse hfine
      (h.meshTailError_bddAbove hP n)

lemma BoundedSequence.futureLow_mesh_near
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) (n : ℕ) :
    |affineFutureLow (fun i => (As i).meshAffine i) P n - futureLow As P n| ≤
      meshTailError As P n := by
  obtain ⟨B, hB⟩ := h.bounded
  have hcoarse : BddBelow (Set.range (fun j => (As n).expectAt P n (n + j))) := by
    refine ⟨-B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (neg_le_neg ((As n).abs_expectAt_le_l1Norm P n (n + j)
      (hP (n + j)) |>.trans (hB n))).trans (neg_abs_le _)
  have hfine : BddBelow (Set.range (fun j => (As n).expectAt P (n + j) (n + j))) := by
    refine ⟨-B, ?_⟩
    rintro x ⟨j, rfl⟩
    exact (neg_le_neg ((As n).abs_expectAt_le_l1Norm P (n + j) (n + j)
      (hP (n + j)) |>.trans (hB n))).trans (neg_abs_le _)
  simpa only [affineFutureLow, meshAffine_price, futureLow, meshTailError] using
    abs_sInf_range_sub_sInf_range_le
      (fun j => (As n).expectAt P n (n + j))
      (fun j => (As n).expectAt P (n + j) (n + j)) hcoarse hfine
      (h.meshTailError_bddAbove hP n)

/-- A BLCS uniformly bounds both future expectation extrema, supplying the finite
liminf/limsup hypotheses used by the mesh transfer. -/
lemma BoundedSequence.futureExtrema_filterBounds
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    IsBoundedUnder (· ≥ ·) atTop (futureHigh As P) ∧
    IsBoundedUnder (· ≤ ·) atTop (futureHigh As P) ∧
    IsBoundedUnder (· ≥ ·) atTop (futureLow As P) ∧
    IsBoundedUnder (· ≤ ·) atTop (futureLow As P) := by
  obtain ⟨B, hB⟩ := h.bounded
  have habs : ∀ n m, |(As n).expect P m| ≤ B := fun n m =>
    ((As n).abs_expectAt_le_l1Norm P m m (hP m)).trans (hB n)
  have hhighLo : ∀ n, -B ≤ futureHigh As P n := fun n => by
    have hdiagLo : -B ≤ (As n).expect P n := by
      linarith [neg_le_abs ((As n).expect P n), habs n n]
    exact hdiagLo.trans (le_csSup (by
      refine ⟨B, ?_⟩
      rintro x ⟨j, rfl⟩
      exact (le_abs_self _).trans (habs n (n + j))) ⟨0, by simp⟩)
  have hhighHi : ∀ n, futureHigh As P n ≤ B := fun n => by
    apply csSup_le (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    exact (le_abs_self _).trans (habs n (n + j))
  have hlowLo : ∀ n, -B ≤ futureLow As P n := fun n => by
    apply le_csInf (Set.range_nonempty _)
    rintro x ⟨j, rfl⟩
    linarith [neg_le_abs ((As n).expect P (n + j)), habs n (n + j)]
  have hlowHi : ∀ n, futureLow As P n ≤ B := fun n => by
    have hbdd : BddBelow (Set.range (fun j => (As n).expect P (n + j))) := by
      refine ⟨-B, ?_⟩
      rintro x ⟨j, rfl⟩
      linarith [neg_le_abs ((As n).expect P (n + j)), habs n (n + j)]
    exact (csInf_le hbdd (show (As n).expect P n ∈
      Set.range (fun j => (As n).expect P (n + j)) from ⟨0, by simp⟩)).trans
        ((le_abs_self _).trans (habs n n))
  exact ⟨isBoundedUnder_of_eventually_ge (Eventually.of_forall hhighLo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hhighHi),
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hlowLo),
    isBoundedUnder_of_eventually_le (Eventually.of_forall hlowHi)⟩

/-- Appendix `lem:mesh`: uniformly over all future market days, the fixed day-`n`
threshold mesh and the future day's own mesh become indistinguishable. -/
theorem BoundedSequence.mesh_independence
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (meshTailError As P) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro δ hδ
  obtain ⟨ε, hε0, hεδ⟩ : ∃ ε : ℚ,
      (0 : ℝ) < ε ∧ (ε : ℝ) < δ / 2 := exists_rat_btwn (half_pos hδ)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (b : ℝ) / δ)
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (mesh_close_eventually ops hvalued b ε hε0 hshare hP hworld)
  refine ⟨max 1 (max N M), fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hNn : 4 * (b : ℝ) / δ < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast (le_trans (le_max_left N M)
      (le_trans (le_max_right 1 (max N M)) hn)))
  have hsmall : 2 * (b : ℝ) / n < δ / 2 := by
    by_cases hb0 : (b : ℝ) = 0
    · rw [hb0]
      simp [hδ]
    · have hbpos : 0 < (b : ℝ) := lt_of_le_of_ne hb (Ne.symm hb0)
      have hδ0 := hδ
      rw [div_lt_iff₀ hδ] at hNn
      rw [div_lt_iff₀ hnR]
      nlinarith
  have hnM : M ≤ n :=
    (le_max_right N M).trans (le_max_right 1 (max N M) |>.trans hn)
  have hpair : ∀ m, n ≤ m →
      |(As n).expectAt P n m - (As n).expectAt P m m| ≤
        2 * (b : ℝ) / n + (ε : ℝ) := by
    intro m hnm
    exact hM m (hnM.trans hnm) n hn0 hnm
  have hsup := meshTailError_le hpair
  have hnonneg := h.meshTailError_nonneg hP n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hsup.trans_lt (by linarith)

/-- Rank preservation for the mesh lift. -/
lemma meshAffine_rank
    (A : LUVCombination) {day k : ℕ}
    (hconst : A.const.rank ≤ day)
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ day) :
    (A.meshAffine k).const.rank ≤ day ∧
      ∀ p ∈ (A.meshAffine k).terms, p.1.rank ≤ day := by
  refine ⟨hconst, ?_⟩
  intro p hp
  simp only [meshAffine, List.mem_flatMap] at hp
  obtain ⟨q, hq, hp⟩ := hp
  simp only [AffineCombination.scale, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  simp only [EF.rank_mul]
  apply Nat.max_le.mpr
  refine ⟨hterms q hq, ?_⟩
  simp only [LUV.expectAffine, List.mem_map] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  simp [EF.rank]

/-! ## Polynomial and bounded LUV-combination consequences -/

/-- A BLCS compiles to the paper's affine BCS at the diagonal mesh precision. -/
def BoundedSequence.affineBCS {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) :
    AffineCombination.BoundedCombinationSequence
      (fun n => (As n).meshAffine n) P where
  poly := h.poly.mesh_poly
  bounded := by
    obtain ⟨B, hB⟩ := h.bounded
    exact ⟨B, fun n => ((As n).meshAffine_l1Norm_le P n).trans (hB n)⟩

lemma BoundedSequence.mesh_magnitudeBounded
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) :
    ∃ B : ℝ, ∀ n, ((As n).meshAffine n).magnitude P ≤ B :=
  h.affineBCS.magnitudeBounded

lemma BoundedSequence.mesh_boundedPrices
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    BoundedAffinePrices (fun n => (As n).meshAffine n) P :=
  h.affineBCS.boundedPrices hP

noncomputable def BoundedSequence.normalizedMesh_poly
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (b : ℚ) :
    AffineCombination.PolySequence (normalizedMesh As b) := by
  simpa only [normalizedMesh] using h.poly.mesh_poly.scaleRat (meshNormScale b)

lemma BoundedSequence.normalizedMesh_boundedPrices
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (b : ℚ)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1) :
    BoundedAffinePrices (normalizedMesh As b) P := by
  simpa only [normalizedMesh] using
    (h.mesh_boundedPrices hP).scaleRat (meshNormScale b)

lemma normalizedMesh_magnitude_le_one
    {As : ℕ → LUVCombination} {P : History}
    (b : ℚ)
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ)) (n : ℕ) :
    (normalizedMesh As b n).magnitude P ≤ 1 := by
  have hq0 : 0 ≤ ((meshNormScale b : ℚ) : ℝ) := (meshNormScale_pos b).le
  rw [normalizedMesh, AffineCombination.scale_magnitude, EF.denote_const,
    abs_of_nonneg hq0]
  exact (mul_le_mul_of_nonneg_left
    ((As n).meshAffine_magnitude_le_shareNorm P n) hq0).trans
    ((mul_le_mul_of_nonneg_left (hshare n) hq0).trans
      (meshNormScale_mul_le_one b))

/-- The completed-theory values of a LUV combination, using actual coherent LUV values
rather than its finite threshold mesh. -/
def completedValues (DP : DeductiveProcess) (A : LUVCombination)
    (P : History) : Set ℝ :=
  {x | ∃ (v : PCWorld) (ν : LUV → ℝ), v.ConsistentWithTheory DP ∧
      A.ValuesAt v ν ∧ A.value P ν = x}

noncomputable def completedLow (As : ℕ → LUVCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sInf (completedValues DP (As n) P)

noncomputable def completedHigh (As : ℕ → LUVCombination)
    (P : History) (DP : DeductiveProcess) (n : ℕ) : ℝ :=
  sSup (completedValues DP (As n) P)

/-- Canonical limiting expectation of a fixed combination.  Subsequent mesh-independence
theorems identify this limsup with the actual limit. -/
noncomputable def expectInf (A : LUVCombination) (P : History) : ℝ :=
  limsup (fun m => A.expect P m) atTop

private lemma expectTerms_converge
    (l : List (EF × LUV)) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hcode : ∀ p ∈ l, p.2.PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hval : ∀ p ∈ l, ∀ m (v : PCWorld),
      v.ConsistentWith (DP.D m) → ∃ x : ℝ, v.ValuesAt p.2 x) :
    ∃ L : ℝ, Tendsto (fun m =>
      (l.map (fun p => p.1.denote P * p.2.expect P m)).sum) atTop (𝓝 L) := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons p rest ih =>
      obtain ⟨LX, hLX⟩ := p.2.expect_converges P DP (hcode p (by simp)) hP hworld
        (fun m v hv => hval p (by simp) m v hv)
      have hcodeRest : ∀ q ∈ rest, q.2.PolyThresholdCodes := by
        intro q hq
        exact hcode q (by simp [hq])
      have hvalRest : ∀ q ∈ rest, ∀ m (v : PCWorld),
          v.ConsistentWith (DP.D m) → ∃ x : ℝ, v.ValuesAt q.2 x := by
        intro q hq m v hv
        exact hval q (by simp [hq]) m v hv
      obtain ⟨LR, hLR⟩ := ih hcodeRest hvalRest
      refine ⟨p.1.denote P * LX + LR, ?_⟩
      simpa only [List.map_cons, List.sum_cons] using
        (tendsto_const_nhds.mul hLX).add hLR

/-- Each represented fixed LUV combination really converges to the canonical
`expectInf`; the definition by `limsup` merely avoids carrying a chosen witness. -/
lemma ConvergencePresentation.expect_tendsto_expectInf
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (hc : ConvergencePresentation As DP)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    Tendsto (fun m => (As n).expect P m) atTop (𝓝 ((As n).expectInf P)) := by
  obtain ⟨L, hL⟩ := expectTerms_converge (As n).terms P DP
    (hc.threshold_code n) hP hworld (hc.daily_value n)
  have hfull : Tendsto (fun m => (As n).expect P m) atTop
      (𝓝 ((As n).const.denote P + L)) := by
    simpa only [expect, expectAt] using tendsto_const_nhds.add hL
  have heq : (As n).expectInf P = (As n).const.denote P + L := by
    simpa only [expectInf] using hfull.limsup_eq
  simpa only [heq] using hfull

/-- `lem:limexpapprox`, pointwise quantitative form: the fixed precision-`n` affine
valuation at the market's limiting beliefs differs from the actual limiting expectation
by at most the literal mesh-tail error. -/
theorem BoundedSequence.mesh_limitingValue_near_expectInf
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hc : ConvergencePresentation As DP)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    |((As n).meshAffine n).value P (limitingBelief P) - (As n).expectInf P| ≤
      meshTailError As P n := by
  have hmeshLim := ((As n).meshAffine n).price_tendsto_limitingValue P DP hP hworld
  have hexpectLim := hc.expect_tendsto_expectInf hP hworld n
  have hdiffLim := (hmeshLim.sub hexpectLim).abs
  apply le_of_tendsto hdiffLim
  apply eventually_atTop.2
  refine ⟨n, fun m hnm => ?_⟩
  have hrange : |(As n).expectAt P n m - (As n).expectAt P m m| ≤
      meshTailError As P n := by
    apply le_csSup (h.meshTailError_bddAbove hP n)
    refine ⟨m - n, ?_⟩
    simp only [Nat.add_sub_of_le hnm]
  simpa only [meshAffine_price, expect] using hrange

/-- `lem:limexpapprox`: limiting-belief evaluation of the diagonal threshold mesh and
the true limiting expectation are asymptotically equal. -/
theorem BoundedSequence.limexpapprox
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hc : ConvergencePresentation As DP)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n =>
      |((As n).meshAffine n).value P (limitingBelief P) - (As n).expectInf P|)
      atTop (𝓝 0) := by
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n => h.mesh_limitingValue_near_expectInf hc hP hworld n)
    (h.mesh_independence ops hvalued b hb hshare hP hworld)

/-- A LUV-combination sequence is determined when every completed-theory world and every
coherent assignment to its LUVs gives the same advertised value. -/
def DeterminedViaTheory (As : ℕ → LUVCombination) (P : History)
    (DP : DeductiveProcess) (truth : ℕ → ℝ) : Prop :=
  ∀ n (v : PCWorld) (ν : LUV → ℝ), v.ConsistentWithTheory DP →
    (As n).ValuesAt v ν → (As n).value P ν = truth n

/-- Exact representation turns the diagonal threshold mesh into an affine sequence
determined by the explicitly named `meshTheoryTruth` stream. -/
lemma ExactTheoryPresentation.mesh_determined
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AffineCombination.DeterminedViaTheory
      (fun n => (As n).meshAffine n) P DP (meshTheoryTruth As P DP hworld) := by
  intro n v hv
  exact h.meshAffine_value_eq hworld n v hv

noncomputable def normalizedMeshTruth (As : ℕ → LUVCombination) (P : History)
    (DP : DeductiveProcess)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (n : ℕ) : ℝ :=
  ((meshNormScale b : ℚ) : ℝ) * meshTheoryTruth As P DP hworld n

lemma ExactTheoryPresentation.normalizedMesh_determined
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (b : ℚ) :
    AffineCombination.DeterminedViaTheory (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) := by
  intro n v hv
  rw [normalizedMesh, AffineCombination.scale_value, EF.denote_const,
    h.meshAffine_value_eq hworld n v hv]
  rfl

/-- The mesh's common completed-theory truth differs from the exact determined
LUV-combination truth by at most `shareNorm / n`. -/
lemma ExactTheoryPresentation.meshTheoryTruth_near
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {n : ℕ} (hn : 0 < n) :
    |meshTheoryTruth As P DP hworld n - truth n| ≤
      (As n).shareNorm P * (1 / (n : ℝ)) := by
  let v := theoryWorld DP hworld
  have hv : v.ConsistentWithTheory DP := theoryWorld_consistent DP hworld
  have hnear := (As n).meshAffine_value_near P v (h.value n) hn
    (h.valuesAt n v hv)
  have htruth := hdet n v (h.value n) hv (h.valuesAt n v hv)
  simpa only [meshTheoryTruth, v, htruth] using hnear

lemma ExactTheoryPresentation.meshTheoryTruth_sub_truth_tendsto
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ)) :
    Tendsto (fun n => meshTheoryTruth As P DP hworld n - truth n)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    (tendsto_const_div_atTop_nhds_zero_nat (b : ℝ))
  have hnear := h.meshTheoryTruth_near hdet hworld (Nat.zero_lt_of_lt hn)
  exact hnear.trans (by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right (hshare n) (inv_nonneg.mpr (by positivity)))

/-- A Toeplitz-style transfer for the repository's inclusive weighted averages:
nonnegative weights with divergent total mass send every null sequence to zero. -/
lemma weightedAverage_tendsto_zero_of_tendsto_zero
    {w e : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (weightedAverage w e) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 he (ε / 2) (half_pos hε)
  let C : ℝ := ∑ i ∈ Finset.range N, w i * |e i|
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw0 i) (abs_nonneg _)
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (hdiv.eventually (eventually_gt_atTop (2 * C / ε)))
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left N M).trans hn
  have hnM : M ≤ n := (le_max_right N M).trans hn
  have hdenLarge : 2 * C / ε < prefixSum w n := hM n hnM
  have hdenPos : 0 < prefixSum w n := by
    have hleft : 0 ≤ 2 * C / ε := div_nonneg (mul_nonneg (by norm_num) hC0) hε.le
    linarith
  have htail : ∀ i ∈ Finset.Ico N (n + 1), |e i| < ε / 2 := by
    intro i hi
    simpa only [Real.dist_eq, sub_zero] using hN i (Finset.mem_Ico.mp hi).1
  have habsNum : |prefixSum (fun i => w i * e i) n| ≤
      C + (ε / 2) * prefixSum w n := by
    calc
      |prefixSum (fun i => w i * e i) n| ≤
          ∑ i ∈ Finset.range (n + 1), |w i * e i| := by
        rw [prefixSum]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range (n + 1), w i * |e i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw0 i)]
      _ = C + ∑ i ∈ Finset.Ico N (n + 1), w i * |e i| := by
        dsimp only [C]
        exact (Finset.sum_range_add_sum_Ico
          (fun i => w i * |e i|) (by omega : N ≤ n + 1)).symm
      _ ≤ C + ∑ i ∈ Finset.Ico N (n + 1), w i * (ε / 2) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (le_of_lt (htail i hi)) (hw0 i)
      _ ≤ C + ∑ i ∈ Finset.range (n + 1), w i * (ε / 2) := by
        apply add_le_add_right
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
        · intro i hi hnot
          exact mul_nonneg (hw0 i) (half_pos hε).le
      _ = C + (ε / 2) * prefixSum w n := by
        rw [prefixSum]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [Real.dist_eq, sub_zero, weightedAverage_eq_div (ne_of_gt hdenPos),
    abs_div, abs_of_pos hdenPos]
  have hCsmall : C / prefixSum w n < ε / 2 := by
    rw [div_lt_iff₀ hdenPos]
    rw [div_lt_iff₀ hε] at hdenLarge
    nlinarith
  calc
    |prefixSum (fun i => w i * e i) n| / prefixSum w n ≤
        (C + (ε / 2) * prefixSum w n) / prefixSum w n :=
      div_le_div_of_nonneg_right habsNum hdenPos.le
    _ = C / prefixSum w n + ε / 2 := by field_simp
    _ < ε := by linarith

/-- Consequently, replacing a stream by a pointwise asymptotically equal stream does
not change its divergent weighted average. -/
lemma weightedAverage_sub_tendsto_zero_of_sub_tendsto_zero
    {w x y : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n)
    (hdiv : Tendsto (prefixSum w) atTop atTop)
    (hxy : Tendsto (fun n => x n - y n) atTop (𝓝 0)) :
    Tendsto (fun n => weightedAverage w x n - weightedAverage w y n)
      atTop (𝓝 0) := by
  have hbase := weightedAverage_tendsto_zero_of_tendsto_zero hw0 hdiv hxy
  apply hbase.congr'
  filter_upwards [hdiv.eventually (eventually_gt_atTop 0)] with n hn
  exact weightedAverage_sub w x y (ne_of_gt hn)

lemma hasLimitPoint_add_tendsto_zero
    {f d : ℕ → ℝ} (hf : HasLimitPoint f 0)
    (hd : Tendsto d atTop (𝓝 0)) :
    HasLimitPoint (fun n => f n + d n) 0 := by
  obtain ⟨ψ, hψmono, hfψ⟩ := hf.exists_subseq
  have hdψ : Tendsto (d ∘ ψ) atTop (𝓝 0) := hd.comp hψmono.tendsto_atTop
  have hsum : Tendsto ((fun n => f n + d n) ∘ ψ) atTop (𝓝 0) := by
    convert hfψ.add hdψ using 1
    simp
  exact MapClusterPt.of_comp hψmono.tendsto_atTop hsum.mapClusterPt

lemma completedValues_to_mesh
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ completedValues DP (As n) P) :
    ∃ y ∈ completedAffineValues DP ((As n).meshAffine n) P,
      |y - x| ≤ (As n).shareNorm P * (1 / (n : ℝ)) := by
  obtain ⟨v, ν, hv, hvals, rfl⟩ := hx
  refine ⟨((As n).meshAffine n).value P v.payout, ⟨v, hv, rfl⟩, ?_⟩
  exact (As n).meshAffine_value_near P v ν hn hvals

lemma mesh_completedValue_to_exact
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (hvalued : WorldValued As DP) {n : ℕ} (hn : 0 < n) {y : ℝ}
    (hy : y ∈ completedAffineValues DP ((As n).meshAffine n) P) :
    ∃ x ∈ completedValues DP (As n) P,
      |y - x| ≤ (As n).shareNorm P * (1 / (n : ℝ)) := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨ν, hvals⟩ := hvalued n v hv
  refine ⟨(As n).value P ν, ⟨v, ν, hv, hvals, rfl⟩, ?_⟩
  exact (As n).meshAffine_value_near P v ν hn hvals

/-- Completed-world extrema of the finite threshold mesh approximate the exact
LUV-combination extrema within the same `shareNorm / n` bound. -/
lemma BoundedSequence.completedExtrema_mesh_near
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {n : ℕ} (hn : 0 < n) :
    |completedAffineLow (fun i => (As i).meshAffine i) P DP n -
        completedLow As P DP n| ≤ (As n).shareNorm P * (1 / (n : ℝ)) ∧
      |completedAffineHigh (fun i => (As i).meshAffine i) P DP n -
        completedHigh As P DP n| ≤ (As n).shareNorm P * (1 / (n : ℝ)) := by
  let S := completedAffineValues DP ((As n).meshAffine n) P
  let T := completedValues DP (As n) P
  let E := (As n).shareNorm P * (1 / (n : ℝ))
  have hS : S.Nonempty := completedAffineValues_nonempty DP ((As n).meshAffine n) P hworld
  have hST : ∀ y ∈ S, ∃ x ∈ T, |y - x| ≤ E := by
    intro y hy
    exact mesh_completedValue_to_exact hvalued hn hy
  have hTS : ∀ x ∈ T, ∃ y ∈ S, |y - x| ≤ E := by
    intro x hx
    exact completedValues_to_mesh hn hx
  have hT : T.Nonempty := by
    obtain ⟨y, hy⟩ := hS
    obtain ⟨x, hx, _⟩ := hST y hy
    exact ⟨x, hx⟩
  obtain ⟨hSb, hSa⟩ := h.poly.mesh_poly.completedAffineValues_bdd P DP
    (h.mesh_boundedPrices hP) h.mesh_magnitudeBounded hP n
  have hTb : BddBelow T := by
    obtain ⟨L, hL⟩ := hSb
    refine ⟨L - E, ?_⟩
    intro x hx
    obtain ⟨y, hy, hnear⟩ := hTS x hx
    have hyL := hL hy
    rw [abs_le] at hnear
    linarith
  have hTa : BddAbove T := by
    obtain ⟨U, hU⟩ := hSa
    refine ⟨U + E, ?_⟩
    intro x hx
    obtain ⟨y, hy, hnear⟩ := hTS x hx
    have hyU := hU hy
    rw [abs_le] at hnear
    linarith
  change |sInf S - sInf T| ≤ E ∧ |sSup S - sSup T| ≤ E
  exact ⟨abs_sInf_sub_sInf_le_of_mutually_near S T E hS hT hSb hTb hST hTS,
    abs_sSup_sub_sSup_le_of_mutually_near S T E hS hT hSa hTa hST hTS⟩

/-- Exact and mesh completed-world extrema have identical asymptotic lower and upper
limits because their Hausdorff error is bounded by `b / n`. -/
lemma BoundedSequence.completedExtrema_mesh_tendsto
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : BoundedSequence As P)
    (hvalued : WorldValued As DP)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n =>
        |completedAffineLow (fun i => (As i).meshAffine i) P DP n -
          completedLow As P DP n|) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        |completedAffineHigh (fun i => (As i).meshAffine i) P DP n -
          completedHigh As P DP n|) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => (b : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (b : ℝ)
  constructor
  · apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) hdiv
    have hnear := (h.completedExtrema_mesh_near hvalued hP hworld
      (Nat.zero_lt_of_lt hn)).1
    exact hnear.trans (by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right (hshare n) (inv_nonneg.mpr (by positivity)))
  · apply squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _)
      (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) hdiv
    have hnear := (h.completedExtrema_mesh_near hvalued hP hworld
      (Nat.zero_lt_of_lt hn)).2
    exact hnear.trans (by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right (hshare n) (inv_nonneg.mpr (by positivity)))

/-! The three affine master theorems applied to the literal diagonal threshold mesh.
The remaining expectation-specific step is `lem:mesh`, which replaces fixed precision
`n` at future market days by each future day's own precision. -/

theorem BoundedSequence.mesh_affpolymax
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (affineFutureHigh (fun n => (As n).meshAffine n) P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (affineFutureLow (fun n => (As n).meshAffine n) P) atTop := by
  simpa only [meshAffine_price_diagonal] using
    h.affineBCS.affpolymax DP hP hworld

/-- `thm:exppolymax`: the market's diagonal expectation has the same lower/upper
limits as the corresponding future-day expectation extrema.  The only operational
boundary is the concrete mesh-softmax compiler certificate used by `lem:mesh`. -/
theorem BoundedSequence.exppolymax
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (fun n => (As n).expect P n) atTop =
        liminf (futureHigh As P) atTop ∧
      limsup (fun n => (As n).expect P n) atTop =
        limsup (futureLow As P) atTop := by
  have hmesh := h.mesh_independence ops hvalued b hb hshare hP hworld
  have hhighNear : Tendsto (fun n =>
      |affineFutureHigh (fun i => (As i).meshAffine i) P n - futureHigh As P n|)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureHigh_mesh_near hP n) hmesh
  have hlowNear : Tendsto (fun n =>
      |affineFutureLow (fun i => (As i).meshAffine i) P n - futureLow As P n|)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureLow_mesh_near hP n) hmesh
  obtain ⟨hhlo, hhhi, hllo, hlhi⟩ := h.futureExtrema_filterBounds hP
  have hhighLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (affineFutureHigh (fun i => (As i).meshAffine i) P)
    (futureHigh As P) hhlo hhhi hhighNear
  have hlowLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (affineFutureLow (fun i => (As i).meshAffine i) P)
    (futureLow As P) hllo hlhi hlowNear
  have haff := h.mesh_affpolymax DP hP hworld
  exact ⟨haff.1.trans hhighLimits.1, haff.2.trans hlowLimits.2⟩

lemma BoundedSequence.mesh_peraffkno
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (affineFutureLow (fun n => (As n).meshAffine n) P) atTop =
        liminf (fun n => ((As n).meshAffine n).value P (limitingBelief P)) atTop ∧
      limsup (affineFutureHigh (fun n => (As n).meshAffine n) P) atTop =
        limsup (fun n => ((As n).meshAffine n).value P (limitingBelief P)) atTop :=
  h.poly.mesh_poly.peraffkno P DP (h.mesh_boundedPrices hP) h.mesh_magnitudeBounded
    hP hworld

/-- `thm:perexpkno`: persistence of expectation knowledge for represented bounded
LUV-combination sequences. -/
theorem BoundedSequence.perexpkno
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hc : ConvergencePresentation As DP)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    liminf (futureLow As P) atTop =
        liminf (fun n => (As n).expectInf P) atTop ∧
      limsup (futureHigh As P) atTop =
        limsup (fun n => (As n).expectInf P) atTop := by
  let Ms : ℕ → AffineCombination := fun n => (As n).meshAffine n
  let Mlim : ℕ → ℝ := fun n => (Ms n).value P (limitingBelief P)
  have hmesh := h.mesh_independence ops hvalued b hb hshare hP hworld
  have hlowNear : Tendsto (fun n =>
      |futureLow As P n - affineFutureLow Ms P n|) atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureLow_mesh_near hP n) hmesh
  have hhighNear : Tendsto (fun n =>
      |futureHigh As P n - affineFutureHigh Ms P n|) atTop (𝓝 0) := by
    simpa only [abs_sub_comm] using squeeze_zero (fun n => abs_nonneg _)
      (fun n => h.futureHigh_mesh_near hP n) hmesh
  obtain ⟨_, _, hhlo, hhhi, hllo, hlhi⟩ := (h.mesh_boundedPrices hP).filterBounds
  have hlowLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (futureLow As P) (affineFutureLow Ms P) hllo hlhi hlowNear
  have hhighLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (futureHigh As P) (affineFutureHigh Ms P) hhlo hhhi hhighNear
  have hlimNear : Tendsto (fun n => |(As n).expectInf P - Mlim n|)
      atTop (𝓝 0) := by
    simpa only [Mlim, Ms, abs_sub_comm] using
      h.limexpapprox ops hvalued hc b hb hshare hP hworld
  obtain ⟨hmlLo, hmlHi⟩ :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      (h.mesh_boundedPrices hP) DP hP hworld
  have hlimLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (fun n => (As n).expectInf P) Mlim hmlLo hmlHi hlimNear
  have hper := h.mesh_peraffkno DP hP hworld
  change liminf (futureLow As P) atTop =
      liminf (fun n => (As n).expectInf P) atTop ∧
    limsup (futureHigh As P) atTop =
      limsup (fun n => (As n).expectInf P) atTop
  exact ⟨hlowLimits.1.trans (hper.1.trans hlimLimits.1.symm),
    hhighLimits.2.trans (hper.2.trans hlimLimits.2.symm)⟩

lemma BoundedSequence.mesh_affcoh
    {As : ℕ → LUVCombination} {P : History}
    (h : BoundedSequence As P) (DP : DeductiveProcess)
    [IsLogicalInductor P DP]
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedAffineLow (fun n => (As n).meshAffine n) P DP) atTop ≤
        liminf (fun n => ((As n).meshAffine n).value P (limitingBelief P)) atTop ∧
      liminf (fun n => ((As n).meshAffine n).value P (limitingBelief P)) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => ((As n).meshAffine n).value P (limitingBelief P)) atTop ∧
        limsup (fun n => ((As n).meshAffine n).value P (limitingBelief P)) atTop ≤
          limsup (completedAffineHigh (fun n => (As n).meshAffine n) P DP) atTop) := by
  simpa only [meshAffine_price_diagonal] using
    h.poly.mesh_poly.affcoh P DP (h.mesh_boundedPrices hP) h.mesh_magnitudeBounded
      hP hworld

/-- `thm:expcoh`: exact completed-world LUV values bound the true limiting expectation,
which in turn coheres with the market's diagonal expectations. -/
theorem BoundedSequence.expcoh
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (ops : MeshSoftmaxOperationalWitness As P)
    (hvalued : WorldValued As DP)
    (hc : ConvergencePresentation As DP)
    (b : ℚ) (hb : 0 ≤ (b : ℝ))
    (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (liminf (completedLow As P DP) atTop ≤
        liminf (fun n => (As n).expectInf P) atTop ∧
      liminf (fun n => (As n).expectInf P) atTop ≤
        liminf (fun n => (As n).expect P n) atTop) ∧
      (limsup (fun n => (As n).expect P n) atTop ≤
          limsup (fun n => (As n).expectInf P) atTop ∧
        limsup (fun n => (As n).expectInf P) atTop ≤
          limsup (completedHigh As P DP) atTop) := by
  let Ms : ℕ → AffineCombination := fun n => (As n).meshAffine n
  let Mlim : ℕ → ℝ := fun n => (Ms n).value P (limitingBelief P)
  have hcompNear := h.completedExtrema_mesh_tendsto hvalued b hshare hP hworld
  obtain ⟨hallo, halhi, hahlo, hahhi⟩ :=
    h.poly.mesh_poly.completedAffineExtrema_filterBounds P DP
      (h.mesh_boundedPrices hP) h.mesh_magnitudeBounded hP hworld
  have hlowLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (completedLow As P DP) (completedAffineLow Ms P DP) hallo halhi (by
      simpa only [Ms, abs_sub_comm] using hcompNear.1)
  have hhighLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (completedHigh As P DP) (completedAffineHigh Ms P DP) hahlo hahhi (by
      simpa only [Ms, abs_sub_comm] using hcompNear.2)
  have hlimNear : Tendsto (fun n => |(As n).expectInf P - Mlim n|)
      atTop (𝓝 0) := by
    simpa only [Mlim, Ms, abs_sub_comm] using
      h.limexpapprox ops hvalued hc b hb hshare hP hworld
  obtain ⟨hmlLo, hmlHi⟩ :=
    AffineCombination.BoundedAffinePrices.limitingValue_filterBounds
      (h.mesh_boundedPrices hP) DP hP hworld
  have hlimLimits := liminf_limsup_eq_of_abs_sub_tendsto_zero
    (fun n => (As n).expectInf P) Mlim hmlLo hmlHi hlimNear
  have haff := h.mesh_affcoh DP hP hworld
  change (liminf (completedLow As P DP) atTop ≤
      liminf (fun n => (As n).expectInf P) atTop ∧
    liminf (fun n => (As n).expectInf P) atTop ≤
      liminf (fun n => (As n).expect P n) atTop) ∧
    (limsup (fun n => (As n).expect P n) atTop ≤
      limsup (fun n => (As n).expectInf P) atTop ∧
    limsup (fun n => (As n).expectInf P) atTop ≤
      limsup (completedHigh As P DP) atTop)
  constructor
  · constructor
    · calc
        liminf (completedLow As P DP) atTop =
            liminf (completedAffineLow Ms P DP) atTop := hlowLimits.1
        _ ≤ liminf Mlim atTop := haff.1.1
        _ = liminf (fun n => (As n).expectInf P) atTop := hlimLimits.1.symm
    · calc
        liminf (fun n => (As n).expectInf P) atTop =
            liminf Mlim atTop := hlimLimits.1
        _ ≤ liminf (fun n => (As n).expect P n) atTop := haff.1.2
  · constructor
    · calc
        limsup (fun n => (As n).expect P n) atTop ≤ limsup Mlim atTop := haff.2.1
        _ = limsup (fun n => (As n).expectInf P) atTop := hlimLimits.2.symm
    · calc
        limsup (fun n => (As n).expectInf P) atTop =
            limsup Mlim atTop := hlimLimits.2
        _ ≤ limsup (completedAffineHigh Ms P DP) atTop := haff.2.2
        _ = limsup (completedHigh As P DP) atTop := hhighLimits.2.symm

/-! ## Statistical expectation lifts -/

/-- A pointwise null perturbation is invisible to every legal divergent weighted
average, so it preserves pseudorandom nonnegativity. -/
lemma PseudorandomAbove.congr_of_sub_tendsto_zero
    {x y : ℕ → ℝ} {f : DeferralFunction} {P : History}
    (hx : PseudorandomAbove x f P)
    (hsub : Tendsto (fun n => y n - x n) atTop (𝓝 0)) :
    PseudorandomAbove y f P := by
  intro W hWgen hWdiv hpatient ε hε
  let w : ℕ → ℝ := fun i => (W i).denote P
  have hbase := hx W hWgen hWdiv hpatient (ε / 2) (half_pos hε)
  have havg : Tendsto (weightedAverage w (fun i => y i - x i)) atTop (𝓝 0) :=
    weightedAverage_tendsto_zero_of_tendsto_zero
      (fun n => (hWdiv.1 n).1) hWdiv.2 hsub
  have herr : ∀ᶠ n in atTop,
      dist (weightedAverage w (fun i => y i - x i) n) 0 < ε / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 havg (ε / 2) (half_pos hε)
    exact eventually_atTop.2 ⟨N, hN⟩
  filter_upwards [hbase, herr, hWdiv.eventually_prefixSum_pos] with n hn he hnpos
  have hy : weightedAverage w y n = weightedAverage w x n +
      weightedAverage w (fun i => y i - x i) n := by
    rw [← weightedAverage_add w x (fun i => y i - x i) (ne_of_gt hnpos)]
    congr 1
    funext i
    ring
  rw [hy]
  rw [Real.dist_eq, sub_zero] at he
  linarith [neg_abs_le (weightedAverage w (fun i => y i - x i) n)]

/-- The corresponding null-perturbation transfer for pseudorandom nonpositivity. -/
lemma PseudorandomBelow.congr_of_sub_tendsto_zero
    {x y : ℕ → ℝ} {f : DeferralFunction} {P : History}
    (hx : PseudorandomBelow x f P)
    (hsub : Tendsto (fun n => y n - x n) atTop (𝓝 0)) :
    PseudorandomBelow y f P := by
  intro W hWgen hWdiv hpatient ε hε
  let w : ℕ → ℝ := fun i => (W i).denote P
  have hbase := hx W hWgen hWdiv hpatient (ε / 2) (half_pos hε)
  have havg : Tendsto (weightedAverage w (fun i => y i - x i)) atTop (𝓝 0) :=
    weightedAverage_tendsto_zero_of_tendsto_zero
      (fun n => (hWdiv.1 n).1) hWdiv.2 hsub
  have herr : ∀ᶠ n in atTop,
      dist (weightedAverage w (fun i => y i - x i) n) 0 < ε / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 havg (ε / 2) (half_pos hε)
    exact eventually_atTop.2 ⟨N, hN⟩
  filter_upwards [hbase, herr, hWdiv.eventually_prefixSum_pos] with n hn he hnpos
  have hy : weightedAverage w y n = weightedAverage w x n +
      weightedAverage w (fun i => y i - x i) n := by
    rw [← weightedAverage_add w x (fun i => y i - x i) (ne_of_gt hnpos)]
    congr 1
    funext i
    ring
  rw [hy]
  rw [Real.dist_eq, sub_zero] at he
  linarith [le_abs_self (weightedAverage w (fun i => y i - x i) n)]

/-- Exact LUV truth pseudorandomness transfers to the normalized threshold mesh used by
the affine statistical hubs. -/
lemma ExactTheoryPresentation.normalizedMeshTruth_pseudorandomAbove
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {f : DeferralFunction} (hpseudo : PseudorandomAbove truth f P) :
    PseudorandomAbove (normalizedMeshTruth As P DP hworld b) f P := by
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hscaled := PseudorandomAbove.const_mul_pos hpseudo (meshNormScale_pos b)
  apply PseudorandomAbove.congr_of_sub_tendsto_zero hscaled
  have herr := h.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare
  have hscaledErr := herr.const_mul q
  simpa only [normalizedMeshTruth, q, mul_sub, mul_zero] using hscaledErr

lemma ExactTheoryPresentation.normalizedMeshTruth_pseudorandomBelow
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    (h : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {f : DeferralFunction} (hpseudo : PseudorandomBelow truth f P) :
    PseudorandomBelow (normalizedMeshTruth As P DP hworld b) f P := by
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hscaled := PseudorandomBelow.const_mul_pos hpseudo (meshNormScale_pos b)
  apply PseudorandomBelow.congr_of_sub_tendsto_zero hscaled
  have herr := h.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare
  have hscaledErr := herr.const_mul q
  simpa only [normalizedMeshTruth, q, mul_sub, mul_zero] using hscaledErr

/-- `thm:recurringunbiasednessexp`: exact determined LUV-combination truth is recurrently
unbiased under every represented divergent weighting.  The two verifier premises are
the same conclusion-free historical-maturity boundaries exposed by `recunbiasedaff`,
instantiated on the concretely normalized threshold mesh. -/
theorem BoundedSequence.recurringunbiasednessexp
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hverify : AffineCombination.BiasRunHistoricallyVerifiable
      (normalizedMesh As b) (h.normalizedMesh_poly b) W hWgen P DP)
    (hverifyNeg : AffineCombination.BiasRunHistoricallyVerifiable
      (fun n => (normalizedMesh As b n).neg)
      (h.normalizedMesh_poly b).neg W hWgen P DP) :
    HasLimitPoint
      (weightedBias (fun i => (W i).denote P)
        (fun i => (As i).expect P i) truth) 0 := by
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).expect P i
  let meshTruth : ℕ → ℝ := meshTheoryTruth As P DP hworld
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : q ≠ 0 := ne_of_gt (meshNormScale_pos b)
  have haff := (hexact.normalizedMesh_determined hworld b).recunbiasedaff_of_historicalVerifiers
    (h.normalizedMesh_poly b) hWgen hWdiv
      (normalizedMesh_magnitude_le_one b hshare) hworld hP hverify hverifyNeg
  have hscaled : HasLimitPoint
      (fun n => q * weightedBias w market meshTruth n) 0 := by
    have haff' : HasLimitPoint
        (weightedBias w (fun i => q * market i) (fun i => q * meshTruth i)) 0 := by
      simpa only [w, market, meshTruth, q, normalizedMesh, normalizedMeshTruth,
        AffineCombination.scale_price, EF.denote_const, meshAffine_price_diagonal] using haff
    have heq : weightedBias w (fun i => q * market i) (fun i => q * meshTruth i) =
        fun n => q * weightedBias w market meshTruth n := by
      funext n
      exact weightedBias_const_mul w market meshTruth q n
    rwa [heq] at haff'
  have hmeshBias : HasLimitPoint (weightedBias w market meshTruth) 0 :=
    hasLimitPoint_zero_of_const_mul hq hscaled
  let d : ℕ → ℝ := fun n => weightedAverage w (fun i => meshTruth i - truth i) n
  have herr : Tendsto (fun n => meshTruth n - truth n) atTop (𝓝 0) := by
    simpa only [meshTruth] using
      hexact.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare
  have hd : Tendsto d atTop (𝓝 0) := by
    exact weightedAverage_tendsto_zero_of_tendsto_zero
      (fun n => (hWdiv.1 n).1) hWdiv.2 herr
  have hsum : HasLimitPoint (fun n => weightedBias w market meshTruth n + d n) 0 :=
    hasLimitPoint_add_tendsto_zero hmeshBias hd
  apply hsum.congrFun
  filter_upwards [hWdiv.eventually_prefixSum_pos] with n hn
  dsimp only [d]
  rw [weightedBias, weightedBias]
  rw [← weightedAverage_add w (fun i => market i - meshTruth i)
    (fun i => meshTruth i - truth i) (ne_of_gt hn)]
  congr 1
  funext i
  ring

/-- `thm:wubexp`: exact determined LUV-combination truth is weighted-unbiased under
every represented divergent weighting supported on a strictly increasing feedback
schedule.  The feedback emitter and delayed-truth bridge are the same conclusion-free
`M7-FEEDBACK-EMIT` and `M7-FEEDBACK-TRUTH` boundaries as in `wubaff`, instantiated on
the concretely normalized threshold mesh. -/
theorem BoundedSequence.wubexp
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    {W : ℕ → EF} (hWgen : PGenerableWeighting W)
    (hWdiv : DivergentWeighting W P)
    {f : DeferralFunction} (hstrict : StrictlyIncreasingDeferral f)
    (hsupport : WeightingSupportedOnDeferralImage W P f)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (emit : AffineCombination.FeedbackTraderEmissionSigns
      (h.normalizedMesh_poly b) hWgen hstrict)
    (bridge : AffineCombination.FeedbackTruthSequence
      (normalizedMesh As b) (normalizedMeshTruth As P DP hworld b) P DP f) :
    weightedBias (fun i => (W i).denote P)
      (fun i => (As i).expect P i) truth ≈ₙ (fun _ => 0) := by
  let w : ℕ → ℝ := fun i => (W i).denote P
  let market : ℕ → ℝ := fun i => (As i).expect P i
  let meshTruth : ℕ → ℝ := meshTheoryTruth As P DP hworld
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : q ≠ 0 := ne_of_gt (meshNormScale_pos b)
  have haff := AffineCombination.lic_wubaff
    (h.normalizedMesh_poly b) hWgen hstrict hsupport emit bridge hWdiv
      (normalizedMesh_magnitude_le_one b hshare) hP hworld
  have hscaled : (fun n => q * weightedBias w market meshTruth n) ≈ₙ
      (fun _ => 0) := by
    have haff' : weightedBias w (fun i => q * market i) (fun i => q * meshTruth i) ≈ₙ
        (fun _ => 0) := by
      simpa only [w, market, meshTruth, q, normalizedMesh, normalizedMeshTruth,
        AffineCombination.scale_price, EF.denote_const, meshAffine_price_diagonal] using haff
    have heq : weightedBias w (fun i => q * market i) (fun i => q * meshTruth i) =
        fun n => q * weightedBias w market meshTruth n := by
      funext n
      exact weightedBias_const_mul w market meshTruth q n
    rwa [heq] at haff'
  have hscaledT : Tendsto (fun n => q * weightedBias w market meshTruth n)
      atTop (𝓝 0) := by
    simpa only [AsympEq, sub_zero] using hscaled
  have hmeshT : Tendsto (weightedBias w market meshTruth) atTop (𝓝 0) := by
    have hu := hscaledT.const_mul q⁻¹
    convert hu using 1 <;> simp [hq]
  let d : ℕ → ℝ := fun n => weightedAverage w (fun i => meshTruth i - truth i) n
  have herr : Tendsto (fun n => meshTruth n - truth n) atTop (𝓝 0) := by
    simpa only [meshTruth] using
      hexact.meshTheoryTruth_sub_truth_tendsto hdet hworld b hshare
  have hd : Tendsto d atTop (𝓝 0) := by
    exact weightedAverage_tendsto_zero_of_tendsto_zero
      (fun n => (hWdiv.1 n).1) hWdiv.2 herr
  have hsum : Tendsto (fun n => weightedBias w market meshTruth n + d n)
      atTop (𝓝 0) := by
    simpa using hmeshT.add hd
  have hfinal : Tendsto (weightedBias w market truth) atTop (𝓝 0) := by
    apply hsum.congr'
    filter_upwards [hWdiv.eventually_prefixSum_pos] with n hn
    dsimp only [d]
    rw [weightedBias, weightedBias]
    rw [← weightedAverage_add w (fun i => market i - meshTruth i)
      (fun i => meshTruth i - truth i) (ne_of_gt hn)]
    congr 1
    funext i
    ring
  simpa only [AsympEq, sub_zero, w, market] using hfinal

/-- `thm:prandexp`, paper-facing nonnegative branch.  Pseudorandom exact LUV truth is
transferred through the vanishing threshold-mesh error, the affine `prandaff` theorem is
applied to the normalized mesh, and its positive normalization is cancelled. -/
theorem BoundedSequence.prandexp
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (clock : PatientSettlementClock (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) f)
    (hpseudo : PseudorandomAbove truth f P)
    (hverify : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (normalizedMesh As b) (h.normalizedMesh_poly b) W hWgen P DP)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (normalizedMesh As b n).neg)
        (h.normalizedMesh_poly b).neg W hWgen P DP) :
    (fun n => (As n).expect P n) ≳ₙ (fun _ => 0) := by
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : 0 < q := meshNormScale_pos b
  have hpseudoMesh := hexact.normalizedMeshTruth_pseudorandomAbove
    hdet hworld b hshare hpseudo
  have haff :=
    AffineCombination.DeterminedViaTheory.lic_prandaff_above_of_historicalVerifiers
      (h.normalizedMesh_poly b) (hexact.normalizedMesh_determined hworld b)
      (h.normalizedMesh_boundedPrices b hP)
      (normalizedMesh_magnitude_le_one b hshare) hworld hP f clock
      hpseudoMesh hverify hverifyNeg
  have hscaled : (fun n => q * (As n).expect P n) ≳ₙ (fun _ => 0) := by
    simpa only [q, normalizedMesh, AffineCombination.scale_price, EF.denote_const,
      meshAffine_price_diagonal] using haff
  exact asympGE_zero_of_const_mul_pos hq hscaled

/-- The nonpositive comparison direction of `thm:prandexp`. -/
theorem BoundedSequence.prandexp_below
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (clock : PatientSettlementClock (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) f)
    (hpseudo : PseudorandomBelow truth f P)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (normalizedMesh As b n).neg)
        (h.normalizedMesh_poly b).neg W hWgen P DP)
    (hverifyNegNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => ((normalizedMesh As b n).neg).neg)
        (h.normalizedMesh_poly b).neg.neg W hWgen P DP) :
    (fun n => (As n).expect P n) ≲ₙ (fun _ => 0) := by
  let q : ℝ := ((meshNormScale b : ℚ) : ℝ)
  have hq : 0 < q := meshNormScale_pos b
  have hpseudoMesh := hexact.normalizedMeshTruth_pseudorandomBelow
    hdet hworld b hshare hpseudo
  have haff :=
    AffineCombination.DeterminedViaTheory.lic_prandaff_below_of_historicalVerifiers
      (h.normalizedMesh_poly b) (hexact.normalizedMesh_determined hworld b)
      (h.normalizedMesh_boundedPrices b hP)
      (normalizedMesh_magnitude_le_one b hshare) hworld hP f clock
      hpseudoMesh hverifyNeg hverifyNegNeg
  have hscaled : (fun n => q * (As n).expect P n) ≲ₙ (fun _ => 0) := by
    simpa only [q, normalizedMesh, AffineCombination.scale_price, EF.denote_const,
      meshAffine_price_diagonal] using haff
  exact asympLE_zero_of_const_mul_pos hq hscaled

/-- The equality direction mentioned in the paper immediately after `thm:prandexp`. -/
theorem BoundedSequence.prandexp_eq
    {As : ℕ → LUVCombination} {P : History} {DP : DeductiveProcess}
    [IsLogicalInductor P DP]
    (h : BoundedSequence As P)
    (hexact : ExactTheoryPresentation As DP)
    {truth : ℕ → ℝ} (hdet : DeterminedViaTheory As P DP truth)
    (b : ℚ) (hshare : ∀ n, (As n).shareNorm P ≤ (b : ℝ))
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (f : DeferralFunction)
    (clock : PatientSettlementClock (normalizedMesh As b) P DP
      (normalizedMeshTruth As P DP hworld b) f)
    (hpseudo : Pseudorandom truth f P)
    (hverify : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (normalizedMesh As b) (h.normalizedMesh_poly b) W hWgen P DP)
    (hverifyNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => (normalizedMesh As b n).neg)
        (h.normalizedMesh_poly b).neg W hWgen P DP)
    (hverifyNegNeg : ∀ (W : ℕ → EF) (hWgen : PGenerableWeighting W),
      AffineCombination.BiasRunHistoricallyVerifiable
        (fun n => ((normalizedMesh As b n).neg).neg)
        (h.normalizedMesh_poly b).neg.neg W hWgen P DP) :
    (fun n => (As n).expect P n) ≈ₙ (fun _ => 0) := by
  rw [asympEq_iff_asympLE_asympGE]
  exact ⟨
    h.prandexp_below hexact hdet b hshare hP hworld f clock hpseudo.2
      hverifyNeg hverifyNegNeg,
    h.prandexp hexact hdet b hshare hP hworld f clock hpseudo.1
      hverify hverifyNeg⟩

#print axioms LUV.expectAffine_priceAt
#print axioms meshAffine_price
#print axioms meshAffine_value
#print axioms meshAffine_value_near
#print axioms meshAffine_magnitude_le_shareNorm
#print axioms BoundedSequence.affineBCS
#print axioms BoundedSequence.mesh_affpolymax
#print axioms BoundedSequence.exppolymax
#print axioms BoundedSequence.mesh_peraffkno
#print axioms BoundedSequence.perexpkno
#print axioms BoundedSequence.mesh_affcoh
#print axioms BoundedSequence.expcoh
#print axioms BoundedSequence.recurringunbiasednessexp
#print axioms BoundedSequence.wubexp
#print axioms BoundedSequence.prandexp
#print axioms BoundedSequence.prandexp_below
#print axioms BoundedSequence.prandexp_eq

end LUVCombination

end LogicalInduction
