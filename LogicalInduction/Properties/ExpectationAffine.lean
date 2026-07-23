/-
# Affine expectation lift

Polynomial affine presentations of the growing threshold bundles used by `def:e`, followed
by the expectation-level consequences of affine provability induction.
-/
import LogicalInduction.Properties.AffineProvability

namespace LogicalInduction

open Filter Topology

namespace LUV

/-- The affine bundle whose market price is the day-`n` expectation of `X`. -/
def expectAffine (X : LUV) (n : ℕ) : AffineCombination where
  const := .const 0
  terms := (List.range n).map (fun (i : ℕ) =>
    (.const (1 / (n : ℚ)), X.gt ((i : ℚ) / (n : ℚ))))

lemma expectAffine_price (X : LUV) (P : History) (n : ℕ) :
    (X.expectAffine n).price P n = X.expect P n := by
  rw [expectAffine, AffineCombination.price, AffineCombination.value,
    LUV.expect, LUV.expectApprox]
  simp only [EF.denote, EF.denoteWith, List.map_map, Function.comp_def]
  push_cast
  rw [zero_add, List.sum_map_mul_left, one_div]
  congr 1

lemma expectAffine_value (X : LUV) (P : History) (w : Valuation) (n : ℕ) :
    (X.expectAffine n).value P w = X.expectApprox w n := by
  rw [expectAffine, AffineCombination.value, LUV.expectApprox]
  simp only [EF.denote, EF.denoteWith, List.map_map, Function.comp_def]
  push_cast
  rw [zero_add, List.sum_map_mul_left, one_div]
  congr 1

def expectAffine_polySequence (X : LUV) (hcode : X.PolyThresholdCodes) :
    AffineCombination.PolySequence X.expectAffine := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  exact {
  termCount := fun n => n
  coefficient := fun z => .const (1 / (z.unpair.1 : ℚ))
  sentence := fun z => X.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
  termCount_poly := ⟨Nat.Partrec.Code.id, PolyFueled.id⟩
  const_poly := PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  coefficient_poly := PolySegStream.ofTokenStream
    (PolyTokenStream.serialize_const_comp ⟨cinv.comp Nat.Partrec.Code.left,
      hinv.comp PolyFueled.left⟩)
  sentence_poly := hcode
  terms_eq := by intro n; simp [expectAffine]
  const_rank := by intro n; simp [expectAffine]
  coefficient_rank := by intro n j hj; simp [EF.rank]
  const_closed := by intro n ρ V; simp [expectAffine]
  coefficient_closed := by intro z ρ V; simp [EF.denoteWith]
  }

lemma expectAffine_magnitude_le_one (X : LUV) (P : History) (n : ℕ) :
    (X.expectAffine n).magnitude P ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [expectAffine, AffineCombination.magnitude]
  · simp only [expectAffine, AffineCombination.magnitude, List.map_map]
    change ((List.range n).map (fun _ => |(((1 / (n : ℚ) : ℚ) : ℝ))|)).sum ≤ 1
    simp
    field_simp
    norm_num

/-- Affine discrepancy between an indicator LUV's expectation and the price of its
underlying sentence. -/
def indicatorAffine (Y : LUV) (φ : Sentence) (n : ℕ) : AffineCombination where
  const := .const 0
  terms := (List.range (n + 1)).map (fun j =>
    if j < n then
      (.const (1 / (n : ℚ)), Y.gt ((j : ℚ) / (n : ℚ)))
    else (.const (-1), φ))

noncomputable def indicatorAffine_polySequence (Y : LUV) (φ : Sentence)
    (hcode : Y.PolyThresholdCodes) :
    AffineCombination.PolySequence (Y.indicatorAffine φ) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  let cy := Classical.choose hcode
  have hy := Classical.choose_spec hcode
  have htest := subc_polyFueled.comp (PolyFueled.left.pair PolyFueled.right)
  have hInvSeg : PolySegStream (fun z => (EF.const (1 / (z.unpair.1 : ℚ))).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp
      ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩)
  have hNegSeg : PolySegStream (fun _ => (EF.const (-1)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
  have hsentence : PolyFueled
      (ifzSel.comp (((Nat.Partrec.Code.const (Encodable.encode φ)).pair cy).pair
        (subc.comp (Nat.Partrec.Code.left.pair Nat.Partrec.Code.right))))
      (fun z => Encodable.encode (if z.unpair.2 < z.unpair.1 then
        Y.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ)) else φ)) := by
    apply PolyFueled.of_eq
      (ifzSel_polyFueled.comp (((PolyFueled.const (Encodable.encode φ)).pair hy).pair htest))
    intro z
    simp only [Nat.unpair_pair, ifzSelFn]
    by_cases hj : z.unpair.2 < z.unpair.1
    · rw [if_pos hj, if_neg (by omega)]
    · rw [if_neg hj, if_pos (by omega)]
  exact {
    termCount := fun n => n + 1
    coefficient := fun z => if z.unpair.2 < z.unpair.1
      then .const (1 / (z.unpair.1 : ℚ)) else .const (-1)
    sentence := fun z => if z.unpair.2 < z.unpair.1
      then Y.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ)) else φ
    termCount_poly := ⟨_, PolyFueled.id.succ_comp⟩
    const_poly := PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
    coefficient_poly := PolySegStream.of_eq (PolySegStream.ifZero hNegSeg hInvSeg htest) (by
      intro z
      simp only [Nat.unpair_pair]
      by_cases hj : z.unpair.2 < z.unpair.1
      · rw [if_pos hj, if_neg (by omega)]
      · rw [if_neg hj, if_pos (by omega)])
    sentence_poly := ⟨_, hsentence⟩
    terms_eq := by
      intro n
      simp only [indicatorAffine]
      apply List.map_congr_left
      intro j hj
      simp only [Nat.unpair_pair]
      split <;> rfl
    const_rank := by intro n; simp [indicatorAffine]
    coefficient_rank := by intro n j hj; split <;> simp [EF.rank]
    const_closed := by intro n ρ V; simp [indicatorAffine]
    coefficient_closed := by intro z ρ V; split <;> simp [EF.denoteWith]
  }

lemma indicatorAffine_terms (Y : LUV) (φ : Sentence) (n : ℕ) :
    (Y.indicatorAffine φ n).terms =
      (Y.expectAffine n).terms ++ [(EF.const (-1), φ)] := by
  simp only [indicatorAffine, expectAffine]
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp [hj]
  · simp

lemma indicatorAffine_price (Y : LUV) (φ : Sentence) (P : History) (n : ℕ) :
    (Y.indicatorAffine φ n).price P n = Y.expect P n - P n φ := by
  rw [AffineCombination.price, AffineCombination.value, indicatorAffine_terms,
    List.map_append, List.map_singleton, List.sum_append]
  have hbase := Y.expectAffine_price P n
  rw [AffineCombination.price, AffineCombination.value] at hbase
  simp only [indicatorAffine, expectAffine, EF.denote_const, List.sum_singleton,
    Rat.cast_neg, Rat.cast_one] at hbase ⊢
  linarith

lemma indicatorAffine_value (Y : LUV) (φ : Sentence) (P : History)
    (w : Valuation) (n : ℕ) :
    (Y.indicatorAffine φ n).value P w = Y.expectApprox w n - w φ := by
  rw [AffineCombination.value, indicatorAffine_terms, List.map_append,
    List.map_singleton, List.sum_append]
  have hbase := Y.expectAffine_value P w n
  rw [AffineCombination.value] at hbase
  simp only [indicatorAffine, expectAffine, EF.denote_const, List.sum_singleton,
    Rat.cast_neg, Rat.cast_one] at hbase ⊢
  linarith

/-- The affine discrepancy witnessing linearity of expectation. -/
def linearityAffine (a b : ℚ) (X Y Z : LUV) (n : ℕ) : AffineCombination where
  const := .const 0
  terms := (List.range (n * 3)).map (fun j =>
    if j < n then
      (.mul (.const a) (.const (1 / (n : ℚ))), X.gt ((j : ℚ) / (n : ℚ)))
    else if j < n * 2 then
      (.mul (.const b) (.const (1 / (n : ℚ))),
        Y.gt (((j - n : ℕ) : ℚ) / (n : ℚ)))
    else
      (.mul (.const (-1)) (.const (1 / (n : ℚ))),
        Z.gt (((j - n * 2 : ℕ) : ℚ) / (n : ℚ))))

noncomputable def linearityAffine_polySequence (a b : ℚ) (X Y Z : LUV)
    (hX : X.PolyThresholdCodes) (hY : Y.PolyThresholdCodes)
    (hZ : Z.PolyThresholdCodes) :
    AffineCombination.PolySequence (linearityAffine a b X Y Z) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  let cx := Classical.choose hX
  have hcx := Classical.choose_spec hX
  let cy := Classical.choose hY
  have hcy := Classical.choose_spec hY
  let cz := Classical.choose hZ
  have hcz := Classical.choose_spec hZ
  let cmul2 := Classical.choose (mulc_polyFueled 2)
  have hmul2 := Classical.choose_spec (mulc_polyFueled 2)
  let cmul3 := Classical.choose (mulc_polyFueled 3)
  have hmul3 := Classical.choose_spec (mulc_polyFueled 3)
  have hn := PolyFueled.left
  have hj := PolyFueled.right
  have h2n := hmul2.comp hn
  have hidxY := hn.pair (subc_polyFueled.comp (hj.pair hn))
  have hidxZ := hn.pair (subc_polyFueled.comp (hj.pair h2n))
  have htestX := subc_polyFueled.comp (hj.succ_comp.pair hn)
  have htestY := subc_polyFueled.comp (hj.succ_comp.pair h2n)
  have hInv : PolySegStream (fun z => (EF.const (1 / (z.unpair.1 : ℚ))).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const_comp
      ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩)
  have hcoeff (q : ℚ) : PolySegStream (fun z =>
      (EF.mul (EF.const q) (EF.const (1 / (z.unpair.1 : ℚ)))).serialize) :=
    PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const q)) hInv
  have hcoeffAll : PolySegStream (fun z =>
      (if z.unpair.2 < z.unpair.1 then
        EF.mul (EF.const a) (EF.const (1 / (z.unpair.1 : ℚ)))
      else if z.unpair.2 < z.unpair.1 * 2 then
        EF.mul (EF.const b) (EF.const (1 / (z.unpair.1 : ℚ)))
      else EF.mul (EF.const (-1)) (EF.const (1 / (z.unpair.1 : ℚ)))).serialize) := by
    refine PolySegStream.of_eq
      (PolySegStream.ifZero (hcoeff a)
        (PolySegStream.ifZero (hcoeff b) (hcoeff (-1)) htestY) htestX) ?_
    intro z
    simp only [Nat.unpair_pair]
    by_cases hx : z.unpair.2 < z.unpair.1
    · rw [if_pos hx, if_pos (by omega)]
    · rw [if_neg hx, if_neg (by omega)]
      by_cases hy : z.unpair.2 < z.unpair.1 * 2
      · rw [if_pos hy, if_pos (by omega)]
      · rw [if_neg hy, if_neg (by omega)]
  have hsX := hcx
  have hsY := hcy.comp hidxY
  have hsZ := hcz.comp hidxZ
  have hsAll : ∃ c, PolyFueled c (fun z => Encodable.encode
      (if z.unpair.2 < z.unpair.1 then
        X.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
      else if z.unpair.2 < z.unpair.1 * 2 then
        Y.gt (((z.unpair.2 - z.unpair.1 : ℕ) : ℚ) / (z.unpair.1 : ℚ))
      else Z.gt (((z.unpair.2 - z.unpair.1 * 2 : ℕ) : ℚ) / (z.unpair.1 : ℚ)))) := by
    let inner := ifzSel_polyFueled.comp ((hsY.pair hsZ).pair htestY)
    let outer := ifzSel_polyFueled.comp ((hsX.pair inner).pair htestX)
    refine ⟨_, outer.of_eq (fun z => ?_)⟩
    simp only [Nat.unpair_pair, ifzSelFn]
    by_cases hx : z.unpair.2 < z.unpair.1
    · rw [if_pos hx, if_pos (by omega)]
    · rw [if_neg hx, if_neg (by omega)]
      by_cases hy : z.unpair.2 < z.unpair.1 * 2
      · rw [if_pos hy, if_pos (by omega)]
      · rw [if_neg hy, if_neg (by omega)]
  exact {
    termCount := fun n => n * 3
    coefficient := fun z =>
      if z.unpair.2 < z.unpair.1 then
        .mul (.const a) (.const (1 / (z.unpair.1 : ℚ)))
      else if z.unpair.2 < z.unpair.1 * 2 then
        .mul (.const b) (.const (1 / (z.unpair.1 : ℚ)))
      else .mul (.const (-1)) (.const (1 / (z.unpair.1 : ℚ)))
    sentence := fun z =>
      if z.unpair.2 < z.unpair.1 then
        X.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
      else if z.unpair.2 < z.unpair.1 * 2 then
        Y.gt (((z.unpair.2 - z.unpair.1 : ℕ) : ℚ) / (z.unpair.1 : ℚ))
      else Z.gt (((z.unpair.2 - z.unpair.1 * 2 : ℕ) : ℚ) / (z.unpair.1 : ℚ))
    termCount_poly := ⟨cmul3, hmul3⟩
    const_poly := PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
    coefficient_poly := hcoeffAll
    sentence_poly := hsAll
    terms_eq := by
      intro n
      simp only [linearityAffine]
      apply List.map_congr_left
      intro j hj
      simp only [Nat.unpair_pair]
      by_cases h1 : j < n
      · simp [h1]
      · by_cases h2 : j < n * 2 <;> simp [h1, h2]
    const_rank := by intro n; simp [linearityAffine]
    coefficient_rank := by
      intro n j hj
      simp only [Nat.unpair_pair]
      by_cases h1 : j < n
      · simp [h1, EF.rank]
      · by_cases h2 : j < n * 2 <;> simp [h1, h2, EF.rank]
    const_closed := by intro n ρ V; simp [linearityAffine]
    coefficient_closed := by
      intro z ρ V
      by_cases h1 : z.unpair.2 < z.unpair.1
      · simp [h1, EF.denote, EF.denoteWith]
      · by_cases h2 : z.unpair.2 < z.unpair.1 * 2 <;>
          simp [h1, h2, EF.denote, EF.denoteWith]
  }

lemma linearityAffine_terms (a b : ℚ) (X Y Z : LUV) (n : ℕ) :
    (linearityAffine a b X Y Z n).terms =
      ((X.expectAffine n).terms.map (fun p => (.mul (.const a) p.1, p.2))) ++
      ((Y.expectAffine n).terms.map (fun p => (.mul (.const b) p.1, p.2))) ++
      ((Z.expectAffine n).terms.map (fun p => (.mul (.const (-1)) p.1, p.2))) := by
  simp only [linearityAffine, expectAffine, List.map_map, Function.comp_def]
  rw [show n * 3 = n + n * 2 by omega, List.range_add, List.map_append]
  rw [List.append_assoc]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp [hj]
  · rw [show n * 2 = n + n by omega, List.range_add, List.map_append,
      List.map_append]
    apply congrArg₂ (· ++ ·)
    · rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      have h1 : ¬n + j < n := by omega
      have h2 : n + j < n + n := by omega
      simp only [Function.comp_apply]
      rw [if_neg h1, if_pos h2]
      simp
    · rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      have h1 : ¬n + (n + j) < n := by omega
      have h2 : ¬n + (n + j) < n + n := by omega
      simp only [Function.comp_apply]
      rw [if_neg h1, if_neg h2]
      simp

lemma linearityAffine_price (a b : ℚ) (X Y Z : LUV) (P : History) (n : ℕ) :
    (linearityAffine a b X Y Z n).price P n =
      (a : ℝ) * X.expect P n + (b : ℝ) * Y.expect P n - Z.expect P n := by
  rw [AffineCombination.price, AffineCombination.value, linearityAffine_terms]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
    EF.denote_mul, EF.denote_const, Pi.mul_apply]
  simp_rw [mul_assoc]
  simp only [List.sum_map_mul_left]
  have hX := X.expectAffine_price P n
  have hY := Y.expectAffine_price P n
  have hZ := Z.expectAffine_price P n
  rw [AffineCombination.price, AffineCombination.value] at hX hY hZ
  simp only [expectAffine, linearityAffine, EF.denote_const] at hX hY hZ ⊢
  push_cast
  norm_num at hX hY hZ ⊢
  rw [hX, hY, hZ]
  ring

lemma linearityAffine_value (a b : ℚ) (X Y Z : LUV) (P : History)
    (w : Valuation) (n : ℕ) :
    (linearityAffine a b X Y Z n).value P w =
      (a : ℝ) * X.expectApprox w n + (b : ℝ) * Y.expectApprox w n -
        Z.expectApprox w n := by
  rw [AffineCombination.value, linearityAffine_terms]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
    EF.denote_mul, EF.denote_const, Pi.mul_apply]
  simp_rw [mul_assoc]
  simp only [List.sum_map_mul_left]
  have hX := X.expectAffine_value P w n
  have hY := Y.expectAffine_value P w n
  have hZ := Z.expectAffine_value P w n
  rw [AffineCombination.value] at hX hY hZ
  simp only [expectAffine, linearityAffine, EF.denote_const] at hX hY hZ ⊢
  push_cast
  norm_num at hX hY hZ ⊢
  rw [hX, hY, hZ]
  ring

end LUV

/-- **Expectations of indicators** (`thm:ei`).
Paper node: `thm:ei` -/
theorem lic_expectation_indicator (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (Y : LUV) (hcode : Y.PolyThresholdCodes)
    (_hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hY : Y.IsIndicator φ DP) :
    AsympEq (Y.expectSeq P) (fun n => P n φ) := by
  have hsemantic : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        |(Y.indicatorAffine φ n).value P v.payout| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine Filter.eventually_atTop.mpr ⟨max 1 N, fun n hnlarge v hv => ?_⟩
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hNn : (1 : ℝ) / ε < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hnlarge))
    have hsmall : 1 / (n : ℝ) < ε := by
      rw [div_lt_iff₀ hε] at hNn
      rw [div_lt_iff₀ hnR]
      nlinarith
    have hnear := (hY.valuesAt hv).expectApprox_near hn
    rw [LUV.indicatorAffine_value]
    exact hnear.trans hsmall.le
  have hzero := (Y.indicatorAffine_polySequence φ hcode).affine_tendsto_zero
    P DP hcons hsemantic
  simpa only [LUV.indicatorAffine_price, LUV.expectSeq, AsympEq, sub_zero] using hzero

#print axioms lic_expectation_indicator

/-- **Linearity of expectation** (`thm:loe`, fixed `X, Y, Z` form), finite-precision hypothesis.

The world hypothesis is the **finite-precision agreement** the trader argument actually consumes:
in every day-`n` plausible world, `X`, `Y`, `Z` have exact values `x, y, z` with `z = a x + b y`,
and the day-`n` approximate expectations sit within `1/n` of them.  This is *satisfiable* at a
finite stage (unlike the full `PCWorld.ValuesAt` cut, which pins infinitely many thresholds); the
`…_ofValuesAt` corollary recovers the `ValuesAt` form via `expectApprox_near`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (a b : ℚ) (X Y Z : LUV)
    (hcodeX : X.PolyThresholdCodes) (hcodeY : Y.PolyThresholdCodes)
    (hcodeZ : Z.PolyThresholdCodes)
    (_hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hvals : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x y z : ℝ, z = (a : ℝ) * x + (b : ℝ) * y ∧
        |X.expectApprox v.payout n - x| ≤ 1 / n ∧
        |Y.expectApprox v.payout n - y| ≤ 1 / n ∧
        |Z.expectApprox v.payout n - z| ≤ 1 / n) :
    AsympEq (fun n => (a : ℝ) * X.expect P n + (b : ℝ) * Y.expect P n)
      (Z.expectSeq P) := by
  let C : ℝ := |(a : ℝ)| + |(b : ℝ)| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hsemantic : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        |(LUV.linearityAffine a b X Y Z n).value P v.payout| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
    filter_upwards [hvals, Filter.eventually_ge_atTop (max 1 N)] with n hvals_n hnlarge v hv
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hNn : C / ε < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hnlarge))
    have hsmall : C * (1 / (n : ℝ)) < ε := by
      have hNn' : C < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hNn
      calc
        C * (1 / (n : ℝ)) = C / (n : ℝ) := by ring
        _ < ε := (div_lt_iff₀ hnR).2 (by nlinarith)
    obtain ⟨x, y, z, hrelation, hnearX, hnearY, hnearZ⟩ := hvals_n v hv
    rw [LUV.linearityAffine_value]
    have hrearrange :
        (a : ℝ) * X.expectApprox v.payout n + (b : ℝ) * Y.expectApprox v.payout n -
            Z.expectApprox v.payout n =
          (a : ℝ) * (X.expectApprox v.payout n - x) +
            (b : ℝ) * (Y.expectApprox v.payout n - y) -
              (Z.expectApprox v.payout n - z) := by
      rw [hrelation]
      ring
    rw [hrearrange]
    calc
      |(a : ℝ) * (X.expectApprox v.payout n - x) +
          (b : ℝ) * (Y.expectApprox v.payout n - y) -
            (Z.expectApprox v.payout n - z)|
          ≤ |(a : ℝ) * (X.expectApprox v.payout n - x)| +
              |(b : ℝ) * (Y.expectApprox v.payout n - y)| +
                |Z.expectApprox v.payout n - z| := by
            exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |(a : ℝ)| * |X.expectApprox v.payout n - x| +
            |(b : ℝ)| * |Y.expectApprox v.payout n - y| +
              |Z.expectApprox v.payout n - z| := by rw [abs_mul, abs_mul]
      _ ≤ |(a : ℝ)| * (1 / (n : ℝ)) + |(b : ℝ)| * (1 / (n : ℝ)) +
            1 / (n : ℝ) := by gcongr
      _ = C * (1 / (n : ℝ)) := by dsimp [C]; ring
      _ ≤ ε := hsmall.le
  have hzero := (LUV.linearityAffine_polySequence a b X Y Z hcodeX hcodeY hcodeZ).affine_tendsto_zero
    P DP hcons hsemantic
  simpa only [LUV.linearityAffine_price, LUV.expectSeq, AsympEq, sub_zero] using hzero

#print axioms lic_linearity_of_expectation

/-- **Linearity of expectation** (`thm:loe`), full `PCWorld.ValuesAt` form.  Recovers the
original statement as a corollary of the finite-precision form: `ValuesAt` implies the day-`n`
approximation bound via `expectApprox_near`, and the world's linear relation on exact values
supplies `z = a x + b y`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation_ofValuesAt (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (a b : ℚ) (X Y Z : LUV)
    (hcodeX : X.PolyThresholdCodes) (hcodeY : Y.PolyThresholdCodes)
    (hcodeZ : Z.PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hvals : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x y z, v.ValuesAt X x ∧ v.ValuesAt Y y ∧ v.ValuesAt Z z)
    (hlin : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ x y z,
      v.ValuesAt X x → v.ValuesAt Y y → v.ValuesAt Z z → z = a * x + b * y) :
    AsympEq (fun n => (a : ℝ) * X.expect P n + (b : ℝ) * Y.expect P n)
      (Z.expectSeq P) :=
  lic_linearity_of_expectation P DP a b X Y Z hcodeX hcodeY hcodeZ hP hcons
    ((Filter.eventually_gt_atTop 0).mono (fun n hn v hv => by
      obtain ⟨x, y, z, hx, hy, hz⟩ := hvals n v hv
      exact ⟨x, y, z, hlin n v hv x y z hx hy hz,
        hx.expectApprox_near hn, hy.expectApprox_near hn, hz.expectApprox_near hn⟩))

#print axioms lic_linearity_of_expectation_ofValuesAt

/-- **Expectation Provability Induction** (`thm:expprovind`), finite-precision form.

The world hypothesis is the day-`n` approximation bound `|𝔼_n^v(X) − x| ≤ 1/n` with `c ≤ x` — the
satisfiable, finite-stage content the trader argument consumes.  The `…_ofValuesAt` corollary
recovers the full `PCWorld.ValuesAt` statement.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.PolyThresholdCodes)
    (_hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x : ℝ, c ≤ x ∧ |X.expectApprox v.payout n - x| ≤ 1 / n) :
    AsympGE (X.expectSeq P) (fun _ => c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hsemantic : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        c - ε / 2 ≤ (X.expectAffine n).value P v.payout := by
    filter_upwards [hval, Filter.eventually_ge_atTop (max 1 N)] with n hval_n hnlarge v hv
    have hn : 0 < n := by omega
    have hNn : (2 : ℝ) / ε < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hnlarge))
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsmall : 1 / (n : ℝ) < ε / 2 := by
      rw [div_lt_iff₀ hε] at hNn
      rw [div_lt_iff₀ hnR]
      nlinarith
    obtain ⟨x, hcx, hnear⟩ := hval_n v hv
    rw [LUV.expectAffine_value]
    rw [abs_le] at hnear
    linarith
  have hprov := (X.expectAffine_polySequence hcode).affine_provind P DP hcons
    (c - ε / 2) hsemantic
  have hevent := hprov (ε / 2) (by linarith)
  filter_upwards [hevent] with n hn
  rw [LUV.expectAffine_price] at hn
  simpa [LUV.expectSeq] using (show c ≤ X.expect P n + ε by linarith)

#print axioms lic_expectation_provind

/-- **Expectation Provability Induction** (`thm:expprovind`), full `PCWorld.ValuesAt` form.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_ofValuesAt (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x, c ≤ x ∧ v.ValuesAt X x) :
    AsympGE (X.expectSeq P) (fun _ => c) :=
  lic_expectation_provind P DP X hcode hP hcons c
    ((Filter.eventually_gt_atTop 0).mono (fun n hn v hv => by
      obtain ⟨x, hcx, hx⟩ := hval n v hv
      exact ⟨x, hcx, hx.expectApprox_near hn⟩))

#print axioms lic_expectation_provind_ofValuesAt

/-- **Expectation Provability Induction** (`thm:expprovind`), upper (`≤`) form.  Dual of the
lower form through the negated affine mesh.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_le (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.PolyThresholdCodes)
    (_hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x : ℝ, x ≤ c ∧ |X.expectApprox v.payout n - x| ≤ 1 / n) :
    AsympLE (X.expectSeq P) (fun _ => c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hsemantic : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        -c - ε / 2 ≤ ((X.expectAffine n).neg).value P v.payout := by
    filter_upwards [hval, Filter.eventually_ge_atTop (max 1 N)] with n hval_n hnlarge v hv
    have hn : 0 < n := by omega
    have hNn : (2 : ℝ) / ε < (n : ℝ) :=
      hN.trans_le (by exact_mod_cast (le_trans (le_max_right 1 N) hnlarge))
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsmall : 1 / (n : ℝ) < ε / 2 := by
      rw [div_lt_iff₀ hε] at hNn; rw [div_lt_iff₀ hnR]; nlinarith
    obtain ⟨x, hxc, hnear⟩ := hval_n v hv
    rw [AffineCombination.neg_value, LUV.expectAffine_value]
    rw [abs_le] at hnear
    linarith
  have hprov := (X.expectAffine_polySequence hcode).neg.affine_provind P DP hcons
    (-c - ε / 2) hsemantic
  have hevent := hprov (ε / 2) (by linarith)
  filter_upwards [hevent] with n hn
  rw [AffineCombination.neg_price, LUV.expectAffine_price] at hn
  simpa [LUV.expectSeq] using (show X.expect P n ≤ c + ε by linarith)

#print axioms lic_expectation_provind_le

/-- **Expectation Provability Induction** (`thm:expprovind`), equality (`=`) form.  Combines the
lower and upper forms: a determined LUV value forces the expectation sequence to it.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_eq (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.PolyThresholdCodes)
    (hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      |X.expectApprox v.payout n - c| ≤ 1 / n) :
    AsympEq (X.expectSeq P) (fun _ => c) := by
  have hge : AsympGE (X.expectSeq P) (fun _ => c) :=
    lic_expectation_provind P DP X hcode hP hcons c
      (hval.mono (fun n hn v hv => ⟨c, le_rfl, hn v hv⟩))
  have hle : AsympLE (X.expectSeq P) (fun _ => c) :=
    lic_expectation_provind_le P DP X hcode hP hcons c
      (hval.mono (fun n hn v hv => ⟨c, le_rfl, hn v hv⟩))
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [hle ε hε, hge ε hε] with n hnle hnge
  rw [abs_le]; constructor <;> [linarith; linarith]

#print axioms lic_expectation_provind_eq

end LogicalInduction
