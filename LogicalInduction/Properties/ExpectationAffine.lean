/-
# Expectations — §4.8: `thm:ei`, `thm:loe`, `thm:expprovind`

Polynomial affine presentations of the growing threshold bundles of `def:e`, followed by
the expectation-level consequences of affine provability induction: expectations of
indicators, linearity of expectation, and expectation provability induction (in `≥`, `≤`
and `=` forms).
-/
import LogicalInduction.Properties.AffineCoherence

namespace LogicalInduction

open Filter Topology

namespace LUV

/-- The precision-`k` threshold bundle of `X`: `∑_{i<k} (1/k)·⌜X > i/k⌝` (`def:e`).  Priced
on day `n` at the day's own grid `k = n + 1` it is the day-`n` expectation. -/
def expectAffine (X : LUV) (k : ℕ) : AffineCombination where
  const := .const 0
  terms := (List.range k).map (fun (i : ℕ) =>
    (.const (1 / (k : ℚ)), X.gt ((i : ℚ) / (k : ℚ))))

lemma expectAffine_price (X : LUV) (P : History) (n : ℕ) :
    (X.expectAffine (n + 1)).price P n = X.expect P n := by
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

def expectAffine_polySequence (X : LUV) (hcode : X.RpnThresholdCodes) :
    AffineCombination.PolySequence X.expectAffine := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  exact {
  termCount := fun n => n
  coefficient := fun z => .const (1 / (z.unpair.1 : ℚ))
  sentence := fun z => X.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
  termCount_poly := ⟨Nat.Partrec.Code.id, PolyFueled.id⟩
  const_poly := RpnSpliceStream.serialize_const 0
  coefficient_poly := RpnSpliceStream.serialize_const_comp
    ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩
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

/-- Affine discrepancy between an indicator LUV's precision-`k` expectation and the price
of its underlying sentence. -/
def indicatorAffine (Y : LUV) (φ : Sentence) (k : ℕ) : AffineCombination where
  const := .const 0
  terms := (List.range (k + 1)).map (fun j =>
    if j < k then
      (.const (1 / (k : ℚ)), Y.gt ((j : ℚ) / (k : ℚ)))
    else (.const (-1), φ))

lemma indicatorAffine_terms (Y : LUV) (φ : Sentence) (k : ℕ) :
    (Y.indicatorAffine φ k).terms =
      (Y.expectAffine k).terms ++ [(EF.const (-1), φ)] := by
  simp only [indicatorAffine, expectAffine]
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp [hj]
  · simp

lemma indicatorAffine_price (Y : LUV) (φ : Sentence) (P : History) (n : ℕ) :
    (Y.indicatorAffine φ (n + 1)).price P n = Y.expect P n - P n φ := by
  rw [AffineCombination.price, AffineCombination.value, indicatorAffine_terms,
    List.map_append, List.map_singleton, List.sum_append]
  have hbase := Y.expectAffine_price P n
  rw [AffineCombination.price, AffineCombination.value] at hbase
  simp only [indicatorAffine, expectAffine, EF.denote_const, List.sum_singleton,
    Rat.cast_neg, Rat.cast_one] at hbase ⊢
  linarith

lemma indicatorAffine_value (Y : LUV) (φ : Sentence) (P : History)
    (w : Valuation) (k : ℕ) :
    (Y.indicatorAffine φ k).value P w = Y.expectApprox w k - w φ := by
  rw [AffineCombination.value, indicatorAffine_terms, List.map_append,
    List.map_singleton, List.sum_append]
  have hbase := Y.expectAffine_value P w k
  rw [AffineCombination.value] at hbase
  simp only [indicatorAffine, expectAffine, EF.denote_const, List.sum_singleton,
    Rat.cast_neg, Rat.cast_one] at hbase ⊢
  linarith

lemma indicatorAffine_magnitude_le_two (Y : LUV) (φ : Sentence) (P : History) (k : ℕ) :
    (Y.indicatorAffine φ k).magnitude P ≤ 2 := by
  have hbase := Y.expectAffine_magnitude_le_one P k
  rw [AffineCombination.magnitude, indicatorAffine_terms, List.map_append, List.sum_append]
  rw [AffineCombination.magnitude] at hbase
  simp only [List.map_singleton, List.sum_singleton, EF.denote_const, Rat.cast_neg,
    Rat.cast_one, abs_neg, abs_one]
  linarith

/-! ### Varying indicator families

`thm:ei` is stated in the paper for an **ec sequence** of sentences `⟨φ⟩`, so the affine
family it needs is indexed by the day: at day `n`, the precision-`n+1` discrepancy between
`𝔼ₙ(Yₙ)` and `Pₙ(φₙ)`.  The constant case is the `Y n = Y`, `φ n = φ` instance. -/

/-- Day-`n` indicator discrepancy of a varying indicator family. -/
def indicatorAffineSeq (Y : ℕ → LUV) (φ : ℕ → Sentence) (n : ℕ) : AffineCombination :=
  (Y n).indicatorAffine (φ n) (n + 1)

lemma indicatorAffineSeq_price (Y : ℕ → LUV) (φ : ℕ → Sentence) (P : History) (n : ℕ) :
    (indicatorAffineSeq Y φ n).price P n = (Y n).expect P n - P n (φ n) :=
  indicatorAffine_price _ _ P n

lemma indicatorAffineSeq_value (Y : ℕ → LUV) (φ : ℕ → Sentence) (P : History)
    (w : Valuation) (n : ℕ) :
    (indicatorAffineSeq Y φ n).value P w = (Y n).expectApprox w (n + 1) - w (φ n) :=
  indicatorAffine_value _ _ P w (n + 1)

noncomputable def indicatorAffineSeq_polySequence (Y : ℕ → LUV) (φ : ℕ → Sentence)
    (hY : LUV.RpnThresholdCodeSeq Y) (hφ : RpnSentenceCodes φ) :
    AffineCombination.PolySequence (indicatorAffineSeq Y φ) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  have htest := subc_polyFueled.comp
    (PolyFueled.left.succ_comp.pair PolyFueled.right)
  have hInvSeg : RpnSpliceStream
      (fun z => (EF.const (1 / ((z.unpair.1 + 1 : ℕ) : ℚ))).serialize) :=
    RpnSpliceStream.serialize_const_comp
      ⟨cinv.comp (Nat.Partrec.Code.succ.comp Nat.Partrec.Code.left),
        hinv.comp PolyFueled.left.succ_comp⟩
  have hNegSeg : RpnSpliceStream (fun _ : ℕ => (EF.const (-1)).serialize) :=
    RpnSpliceStream.serialize_const (-1)
  have hthr : RpnSentenceCodes (fun z => (Y z.unpair.1).gt
      ((z.unpair.2 : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ))) :=
    (hY.comp (PolyFueled.left.pair
      (PolyFueled.left.succ_comp.pair PolyFueled.right))).of_eq (fun z => by simp)
  have hsen : RpnSentenceCodes (fun z => φ z.unpair.1) := hφ.comp PolyFueled.left
  exact {
    termCount := fun n => n + 2
    coefficient := fun z => if z.unpair.2 < z.unpair.1 + 1
      then .const (1 / ((z.unpair.1 + 1 : ℕ) : ℚ)) else .const (-1)
    sentence := fun z => if z.unpair.2 < z.unpair.1 + 1
      then (Y z.unpair.1).gt ((z.unpair.2 : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ))
      else φ z.unpair.1
    termCount_poly := ⟨_, PolyFueled.id.succ_comp.succ_comp⟩
    const_poly := RpnSpliceStream.serialize_const 0
    coefficient_poly := RpnSpliceStream.of_eq
      (RpnSpliceStream.ifZero hNegSeg hInvSeg htest) (by
        intro z
        simp only [Nat.unpair_pair]
        by_cases hj : z.unpair.2 < z.unpair.1 + 1
        · rw [if_pos hj, if_neg (by omega)]
        · rw [if_neg hj, if_pos (by omega)])
    sentence_poly := (RpnSentenceCodes.ifZero hsen hthr htest).of_eq (by
      intro z
      simp only [Nat.unpair_pair]
      by_cases hj : z.unpair.2 < z.unpair.1 + 1
      · rw [if_pos hj, if_neg (by omega)]
      · rw [if_neg hj, if_pos (by omega)])
    terms_eq := by
      intro n
      simp only [indicatorAffineSeq, indicatorAffine]
      apply List.map_congr_left
      intro j hj
      simp only [Nat.unpair_pair]
      split <;> rfl
    const_rank := by intro n; simp [indicatorAffineSeq, indicatorAffine]
    coefficient_rank := by intro n j hj; split <;> simp [EF.rank]
    const_closed := by intro n ρ V; simp [indicatorAffineSeq, indicatorAffine]
    coefficient_closed := by intro z ρ V; split <;> simp [EF.denoteWith]
  }

/-- The affine discrepancy witnessing linearity of expectation, at precision `k`. -/
def linearityAffine (a b : ℚ) (X Y Z : LUV) (k : ℕ) : AffineCombination where
  const := .const 0
  terms := (List.range (k * 3)).map (fun j =>
    if j < k then
      (.mul (.const a) (.const (1 / (k : ℚ))), X.gt ((j : ℚ) / (k : ℚ)))
    else if j < k * 2 then
      (.mul (.const b) (.const (1 / (k : ℚ))),
        Y.gt (((j - k : ℕ) : ℚ) / (k : ℚ)))
    else
      (.mul (.const (-1)) (.const (1 / (k : ℚ))),
        Z.gt (((j - k * 2 : ℕ) : ℚ) / (k : ℚ))))

noncomputable def linearityAffine_polySequence (a b : ℚ) (X Y Z : LUV)
    (hX : X.RpnThresholdCodes) (hY : Y.RpnThresholdCodes)
    (hZ : Z.RpnThresholdCodes) :
    AffineCombination.PolySequence (linearityAffine a b X Y Z) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
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
  have hInv : RpnSpliceStream (fun z => (EF.const (1 / (z.unpair.1 : ℚ))).serialize) :=
    RpnSpliceStream.serialize_const_comp
      ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩
  have hcoeff (q : ℚ) : RpnSpliceStream (fun z =>
      (EF.mul (EF.const q) (EF.const (1 / (z.unpair.1 : ℚ)))).serialize) :=
    RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_const q) hInv
  have hcoeffAll : RpnSpliceStream (fun z =>
      (if z.unpair.2 < z.unpair.1 then
        EF.mul (EF.const a) (EF.const (1 / (z.unpair.1 : ℚ)))
      else if z.unpair.2 < z.unpair.1 * 2 then
        EF.mul (EF.const b) (EF.const (1 / (z.unpair.1 : ℚ)))
      else EF.mul (EF.const (-1)) (EF.const (1 / (z.unpair.1 : ℚ)))).serialize) := by
    refine RpnSpliceStream.of_eq
      (RpnSpliceStream.ifZero (hcoeff a)
        (RpnSpliceStream.ifZero (hcoeff b) (hcoeff (-1)) htestY) htestX) ?_
    intro z
    simp only [Nat.unpair_pair]
    by_cases hx : z.unpair.2 < z.unpair.1
    · rw [if_pos hx, if_pos (by omega)]
    · rw [if_neg hx, if_neg (by omega)]
      by_cases hy : z.unpair.2 < z.unpair.1 * 2
      · rw [if_pos hy, if_pos (by omega)]
      · rw [if_neg hy, if_neg (by omega)]
  have hsX := hX
  have hsY := hY.comp hidxY
  have hsZ := hZ.comp hidxZ
  have hsAll : RpnSentenceCodes (fun z =>
      if z.unpair.2 < z.unpair.1 then
        X.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
      else if z.unpair.2 < z.unpair.1 * 2 then
        Y.gt (((z.unpair.2 - z.unpair.1 : ℕ) : ℚ) / (z.unpair.1 : ℚ))
      else Z.gt (((z.unpair.2 - z.unpair.1 * 2 : ℕ) : ℚ) / (z.unpair.1 : ℚ))) := by
    refine (RpnSentenceCodes.ifZero hsX
      (RpnSentenceCodes.ifZero hsY hsZ htestY) htestX).of_eq (fun z => ?_)
    simp only [Nat.unpair_pair]
    by_cases hx : z.unpair.2 < z.unpair.1
    · rw [if_pos (show z.unpair.2 + 1 - z.unpair.1 = 0 from by omega), if_pos hx]
    · rw [if_neg (show ¬ z.unpair.2 + 1 - z.unpair.1 = 0 from by omega), if_neg hx]
      by_cases hy : z.unpair.2 < z.unpair.1 * 2
      · rw [if_pos (show z.unpair.2 + 1 - z.unpair.1 * 2 = 0 from by omega), if_pos hy]
      · rw [if_neg (show ¬ z.unpair.2 + 1 - z.unpair.1 * 2 = 0 from by omega), if_neg hy]
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
    const_poly := RpnSpliceStream.serialize_const 0
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

lemma linearityAffine_terms (a b : ℚ) (X Y Z : LUV) (k : ℕ) :
    (linearityAffine a b X Y Z k).terms =
      ((X.expectAffine k).terms.map (fun p => (.mul (.const a) p.1, p.2))) ++
      ((Y.expectAffine k).terms.map (fun p => (.mul (.const b) p.1, p.2))) ++
      ((Z.expectAffine k).terms.map (fun p => (.mul (.const (-1)) p.1, p.2))) := by
  simp only [linearityAffine, expectAffine, List.map_map, Function.comp_def]
  rw [show k * 3 = k + k * 2 by omega, List.range_add, List.map_append]
  rw [List.append_assoc]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    simp [hj]
  · rw [show k * 2 = k + k by omega, List.range_add, List.map_append,
      List.map_append]
    apply congrArg₂ (· ++ ·)
    · rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      have h1 : ¬k + j < k := by omega
      have h2 : k + j < k + k := by omega
      simp only [Function.comp_apply]
      rw [if_neg h1, if_pos h2]
      simp
    · rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      have h1 : ¬k + (k + j) < k := by omega
      have h2 : ¬k + (k + j) < k + k := by omega
      simp only [Function.comp_apply]
      rw [if_neg h1, if_neg h2]
      simp

lemma linearityAffine_price (a b : ℚ) (X Y Z : LUV) (P : History) (n : ℕ) :
    (linearityAffine a b X Y Z (n + 1)).price P n =
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
    (w : Valuation) (k : ℕ) :
    (linearityAffine a b X Y Z k).value P w =
      (a : ℝ) * X.expectApprox w k + (b : ℝ) * Y.expectApprox w k -
        Z.expectApprox w k := by
  rw [AffineCombination.value, linearityAffine_terms]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
    EF.denote_mul, EF.denote_const, Pi.mul_apply]
  simp_rw [mul_assoc]
  simp only [List.sum_map_mul_left]
  have hX := X.expectAffine_value P w k
  have hY := Y.expectAffine_value P w k
  have hZ := Z.expectAffine_value P w k
  rw [AffineCombination.value] at hX hY hZ
  simp only [expectAffine, linearityAffine, EF.denote_const] at hX hY hZ ⊢
  push_cast
  norm_num at hX hY hZ ⊢
  rw [hX, hY, hZ]
  ring

end LUV

/-- **Expectations of indicators** (`thm:ei`).  For an efficiently computable sequence of
sentences `⟨φ⟩` and an indicator family `Yₙ` for `φₙ` (the paper's `1(φₙ)`, rendered
relationally over `cworlds(Θ)` by `LUV.IsIndicator`), the day-`n` expectation of the
indicator tracks the day-`n` price of the sentence: `𝔼ₙ(1(φₙ)) ≈ₙ Pₙ(φₙ)`.

The sequence — not a fixed sentence — is the paper's statement (tex:1719); the constant
case is the instance `φ n = φ`, `Y n = Y`.
Paper node: `thm:ei` -/
theorem lic_expectation_indicator (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (hφ : RpnSentenceCodes φ)
    (Y : ℕ → LUV) (hcode : LUV.RpnThresholdCodeSeq Y)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hY : ∀ n, (Y n).IsIndicator (φ n) DP) :
    AsympEq (fun n => (Y n).expect P n) (fun n => P n (φ n)) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    fun n ψ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n ψ
  have hmagn : ∀ n, (LUV.indicatorAffineSeq Y φ n).magnitude P ≤ 2 :=
    fun n => LUV.indicatorAffine_magnitude_le_two _ _ P _
  have hbounded : BoundedAffinePrices (LUV.indicatorAffineSeq Y φ) P :=
    ⟨2, by norm_num, fun n m =>
      ((LUV.indicatorAffineSeq Y φ n).abs_price_le_l1Norm P m (fun ψ => hP m ψ)).trans (by
        simp only [AffineCombination.l1Norm, LUV.indicatorAffineSeq, LUV.indicatorAffine,
          EF.denote_const, Rat.cast_zero, abs_zero, zero_add]
        exact hmagn n)⟩
  have hsemantic : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWithTheory DP →
        |(LUV.indicatorAffineSeq Y φ n).value P v.payout| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hnlarge v hv => ?_⟩
    have hnR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hNn : (1 : ℝ) / ε < ((n + 1 : ℕ) : ℝ) :=
      hN.trans_le (by push_cast; exact_mod_cast (Nat.le_succ_of_le hnlarge))
    have hsmall : 1 / ((n + 1 : ℕ) : ℝ) < ε := by
      rw [div_lt_iff₀ hε] at hNn
      rw [div_lt_iff₀ hnR]
      nlinarith
    have hnear := ((hY n).valuesAt hv).expectApprox_near n.succ_pos
    rw [LUV.indicatorAffineSeq_value]
    exact hnear.trans hsmall.le
  have hzero := (LUV.indicatorAffineSeq_polySequence Y φ hcode
    hφ).affine_provind_theory_tendsto_zero P DP hbounded ⟨2, hmagn⟩ hcons hsemantic
  simpa only [LUV.indicatorAffineSeq_price, AsympEq, sub_zero] using hzero

#print axioms lic_expectation_indicator

/-- **Linearity of expectation** (`thm:loe`, fixed `X, Y, Z` form), finite-precision hypothesis.

The world hypothesis is the finite-precision agreement the trader argument consumes: in
every day-`n` plausible world, `X`, `Y`, `Z` have values `x, y, z` with `z = a x + b y`, and
the day-`n` approximate expectations (grid `n + 1`) sit within `1/(n+1)` of them.  This is
satisfiable at a finite stage, unlike the full `PCWorld.ValuesAt` cut, which pins infinitely
many thresholds; `lic_linearity_of_expectation_ofValuesAt` recovers the `ValuesAt` form via
`expectApprox_near`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (a b : ℚ) (X Y Z : LUV)
    (hcodeX : X.RpnThresholdCodes) (hcodeY : Y.RpnThresholdCodes)
    (hcodeZ : Z.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hvals : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x y z : ℝ, z = (a : ℝ) * x + (b : ℝ) * y ∧
        |X.expectApprox v.payout (n + 1) - x| ≤ 1 / ((n : ℝ) + 1) ∧
        |Y.expectApprox v.payout (n + 1) - y| ≤ 1 / ((n : ℝ) + 1) ∧
        |Z.expectApprox v.payout (n + 1) - z| ≤ 1 / ((n : ℝ) + 1)) :
    AsympEq (fun n => (a : ℝ) * X.expect P n + (b : ℝ) * Y.expect P n)
      (Z.expectSeq P) := by
  let C : ℝ := |(a : ℝ)| + |(b : ℝ)| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hsemantic : ∀ ε > 0, ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        |(LUV.linearityAffine a b X Y Z (n + 1)).value P v.payout| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
    filter_upwards [hvals, Filter.eventually_ge_atTop N] with n hvals_n hnlarge v hv
    have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hNn : C / ε < (n : ℝ) + 1 :=
      hN.trans_le (by have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlarge
                      linarith)
    have hsmall : C * (1 / ((n : ℝ) + 1)) < ε := by
      have hNn' : C < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hNn
      calc
        C * (1 / ((n : ℝ) + 1)) = C / ((n : ℝ) + 1) := by ring
        _ < ε := (div_lt_iff₀ hnR).2 (by nlinarith)
    obtain ⟨x, y, z, hrelation, hnearX, hnearY, hnearZ⟩ := hvals_n v hv
    rw [LUV.linearityAffine_value]
    have hrearrange :
        (a : ℝ) * X.expectApprox v.payout (n + 1) +
              (b : ℝ) * Y.expectApprox v.payout (n + 1) -
            Z.expectApprox v.payout (n + 1) =
          (a : ℝ) * (X.expectApprox v.payout (n + 1) - x) +
            (b : ℝ) * (Y.expectApprox v.payout (n + 1) - y) -
              (Z.expectApprox v.payout (n + 1) - z) := by
      rw [hrelation]
      ring
    rw [hrearrange]
    calc
      |(a : ℝ) * (X.expectApprox v.payout (n + 1) - x) +
          (b : ℝ) * (Y.expectApprox v.payout (n + 1) - y) -
            (Z.expectApprox v.payout (n + 1) - z)|
          ≤ |(a : ℝ) * (X.expectApprox v.payout (n + 1) - x)| +
              |(b : ℝ) * (Y.expectApprox v.payout (n + 1) - y)| +
                |Z.expectApprox v.payout (n + 1) - z| := by
            exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |(a : ℝ)| * |X.expectApprox v.payout (n + 1) - x| +
            |(b : ℝ)| * |Y.expectApprox v.payout (n + 1) - y| +
              |Z.expectApprox v.payout (n + 1) - z| := by rw [abs_mul, abs_mul]
      _ ≤ |(a : ℝ)| * (1 / ((n : ℝ) + 1)) + |(b : ℝ)| * (1 / ((n : ℝ) + 1)) +
            1 / ((n : ℝ) + 1) := by gcongr
      _ = C * (1 / ((n : ℝ) + 1)) := by dsimp [C]; ring
      _ ≤ ε := hsmall.le
  have hzero := ((LUV.linearityAffine_polySequence a b X Y Z hcodeX hcodeY hcodeZ).shift
      (fun n => by simp [LUV.linearityAffine])
      (fun n p hp => by
        simp only [LUV.linearityAffine, List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        split <;> [skip; split] <;> simp [EF.rank])).affine_tendsto_zero
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
    (hcodeX : X.RpnThresholdCodes) (hcodeY : Y.RpnThresholdCodes)
    (hcodeZ : Z.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hvals : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x y z, v.ValuesAt X x ∧ v.ValuesAt Y y ∧ v.ValuesAt Z z)
    (hlin : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ x y z,
      v.ValuesAt X x → v.ValuesAt Y y → v.ValuesAt Z z → z = a * x + b * y) :
    AsympEq (fun n => (a : ℝ) * X.expect P n + (b : ℝ) * Y.expect P n)
      (Z.expectSeq P) :=
  lic_linearity_of_expectation P DP a b X Y Z hcodeX hcodeY hcodeZ hcons
    (Filter.Eventually.of_forall (fun n v hv => by
      obtain ⟨x, y, z, hx, hy, hz⟩ := hvals n v hv
      exact ⟨x, y, z, hlin n v hv x y z hx hy hz,
        by simpa using hx.expectApprox_near n.succ_pos,
        by simpa using hy.expectApprox_near n.succ_pos,
        by simpa using hz.expectApprox_near n.succ_pos⟩))

#print axioms lic_linearity_of_expectation_ofValuesAt

/-- **Expectation Provability Induction** (`thm:expprovind`), finite-precision form.

The world hypothesis is the day-`n` approximation bound `|𝔼_{n+1}^v(X) − x| ≤ 1/(n+1)` with
`c ≤ x` (day `n` carries grid `n + 1`, `def:e`) — the satisfiable, finite-stage content the
trader argument consumes.  `lic_expectation_provind_ofValuesAt` recovers the full
`PCWorld.ValuesAt` statement.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x : ℝ, c ≤ x ∧ |X.expectApprox v.payout (n + 1) - x| ≤ 1 / ((n : ℝ) + 1)) :
    AsympGE (X.expectSeq P) (fun _ => c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hsemantic : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        c - ε / 2 ≤ (X.expectAffine (n + 1)).value P v.payout := by
    filter_upwards [hval, Filter.eventually_ge_atTop N] with n hval_n hnlarge v hv
    have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hNn : (2 : ℝ) / ε < (n : ℝ) + 1 :=
      hN.trans_le (by have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlarge
                      linarith)
    have hsmall : 1 / ((n : ℝ) + 1) < ε / 2 := by
      rw [div_lt_iff₀ hε] at hNn
      rw [div_lt_iff₀ hnR]
      nlinarith
    obtain ⟨x, hcx, hnear⟩ := hval_n v hv
    rw [LUV.expectAffine_value]
    rw [abs_le] at hnear
    linarith
  have hprov := ((X.expectAffine_polySequence hcode).shift
      (fun n => by simp [LUV.expectAffine])
      (fun n p hp => by
        simp only [LUV.expectAffine, List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [EF.rank])).affine_provind P DP hcons
    (c - ε / 2) hsemantic
  have hevent := hprov (ε / 2) (by linarith)
  filter_upwards [hevent] with n hn
  rw [LUV.expectAffine_price] at hn
  simpa [LUV.expectSeq] using (show c ≤ X.expect P n + ε by linarith)

#print axioms lic_expectation_provind

/-- **Expectation Provability Induction** (`thm:expprovind`), full `PCWorld.ValuesAt` form.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_ofValuesAt (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x, c ≤ x ∧ v.ValuesAt X x) :
    AsympGE (X.expectSeq P) (fun _ => c) :=
  lic_expectation_provind P DP X hcode hcons c
    (Filter.Eventually.of_forall (fun n v hv => by
      obtain ⟨x, hcx, hx⟩ := hval n v hv
      exact ⟨x, hcx, by simpa using hx.expectApprox_near n.succ_pos⟩))

#print axioms lic_expectation_provind_ofValuesAt

/-- **Expectation Provability Induction** (`thm:expprovind`), upper (`≤`) form.  Dual of the
lower form through the negated affine mesh.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_le (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x : ℝ, x ≤ c ∧ |X.expectApprox v.payout (n + 1) - x| ≤ 1 / ((n : ℝ) + 1)) :
    AsympLE (X.expectSeq P) (fun _ => c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  have hsemantic : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        -c - ε / 2 ≤ ((X.expectAffine (n + 1)).neg).value P v.payout := by
    filter_upwards [hval, Filter.eventually_ge_atTop N] with n hval_n hnlarge v hv
    have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hNn : (2 : ℝ) / ε < (n : ℝ) + 1 :=
      hN.trans_le (by have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlarge
                      linarith)
    have hsmall : 1 / ((n : ℝ) + 1) < ε / 2 := by
      rw [div_lt_iff₀ hε] at hNn; rw [div_lt_iff₀ hnR]; nlinarith
    obtain ⟨x, hxc, hnear⟩ := hval_n v hv
    rw [AffineCombination.neg_value, LUV.expectAffine_value]
    rw [abs_le] at hnear
    linarith
  have hprov := ((X.expectAffine_polySequence hcode).shift
      (fun n => by simp [LUV.expectAffine])
      (fun n p hp => by
        simp only [LUV.expectAffine, List.mem_map] at hp
        obtain ⟨j, _, rfl⟩ := hp
        simp [EF.rank])).neg.affine_provind P DP hcons
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
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.RpnThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      |X.expectApprox v.payout (n + 1) - c| ≤ 1 / ((n : ℝ) + 1)) :
    AsympEq (X.expectSeq P) (fun _ => c) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hge : AsympGE (X.expectSeq P) (fun _ => c) :=
    lic_expectation_provind P DP X hcode hcons c
      (hval.mono (fun n hn v hv => ⟨c, le_rfl, hn v hv⟩))
  have hle : AsympLE (X.expectSeq P) (fun _ => c) :=
    lic_expectation_provind_le P DP X hcode hcons c
      (hval.mono (fun n hn v hv => ⟨c, le_rfl, hn v hv⟩))
  rw [asympEq_iff_eventuallyWithin]
  intro ε hε
  filter_upwards [hle ε hε, hge ε hε] with n hnle hnge
  rw [abs_le]; constructor <;> [linarith; linarith]

#print axioms lic_expectation_provind_eq

end LogicalInduction
