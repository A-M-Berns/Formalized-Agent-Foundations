import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Framework.Emission.WriteOut
import LogicalInduction.Framework.Machine.ThresholdMachine

/-!
# Expectations as affine combinations

Renders §4.8 *Expectations*: `thm:ei` (Expectations of Indicators), `thm:loe` (Linearity of
Expectation) and `thm:expprovind` (Expectation Provability Induction).

§4.8 is carried by three modules, in import order, cut by *what an expectation is presented
as*.  This one presents a single LUV's expectation as an affine combination of its threshold
shares and proves the three nodes above off the affine master theorems.
`Properties/ExpectationConvergence.lean` then proves `thm:ec` — that the day-`n` expectation
converges — from `thm:affcoh` and `thm:lc` over the same presentation.
`Properties/ExpectationProperties.lean` lifts both to `LUVCombination` (`def:luv`, `def:blcp`)
and carries `lem:mesh`, `thm:expcoh`, `thm:exppolymax`, `thm:perexpkno` and `thm:wubexp`.

The growing threshold bundles of `def:e` are presented as affine combinations:
`LUV.expectAffine X k = Σ_{i<k} (1/k)·⌜X > i/k⌝`, priced on day `n` at that day's own grid
`k = n + 1`, so `expectAffine_price` is the day-`n` expectation.

`indicatorAffine` / `indicatorAffineSeq` is the day-`n` discrepancy between `𝔼ₙ(Yₙ)` and
`Pₙ(φₙ)`. The family is indexed by the day because `thm:ei` is stated for an e.c. *sequence*
of sentences; the constant case is the `Y n = Y`, `φ n = φ` instance.
`linearityAffine a b X Y Z k` is the affine discrepancy `a·𝔼X + b·𝔼Y − 𝔼Z` at precision `k`.

Each carries an explicit `AffineCombination.PolySequence` emission certificate built from
the LUV threshold-code classes. The single-LUV certificates take the *write-out* class
`LUV.BigThresholdCodes`, which is `def:ec`'s own metering: it bounds how many symbols the
threshold sentences take to write and leaves their values alone. The day-indexed indicator
certificate still takes the token-metered `LUV.RpnThresholdCodeSeq`; `dd:luv-arith` and the
README's *LUV-threshold metering* note record why that is a rendering sensitivity rather
than a narrowing of `def:ec`.

The world hypotheses are the *finite-precision* ones the trader argument actually consumes
(`|𝔼ⱽ_{n+1}(X) − x| ≤ 1/(n+1)`), which are satisfiable at a finite stage unlike the full
`PCWorld.ValuesAt` cut. `lic_linearity_of_expectation_ofValuesAt` and
`lic_expectation_provind_ofValuesAt` recover the `ValuesAt` statements from them via
`expectApprox_near`, and `exists_eventually_const_div_lt` is the `dd:mesh` shrinking step
they share.

The endpoints are `lic_expectation_indicator` and its constructed-indicator form
`lic_expectation_indicator_unconditional`; `lic_linearity_of_expectation(_ofValuesAt)`;
and `lic_expectation_provind`, `_ofValuesAt`, `_le` (the dual, through the negated mesh) and
`_eq`. Everything routes through
`AffineCombination.PolySequence.affine_provind_theory_tendsto_zero` / `.affine_provind` from
`Properties/AffineCoherence.lean`, and the endpoints are consumed by
`Construction/LUV/{Endpoints,ArithmeticSource}.lean`.

Limit vocabulary is `dd:asymp`'s and is never redefined here.
**The criterion binder below is `def:lic` at the paper's own quantifier.**  Every result here that consumes an
exploiting trader takes `[IsLogicalInductor P DP]`, and the trader is certified at `EfficientlyComputable`:
it is assembled from `AffineCombination.PolySequence`'s machine-metered emission fields
through `PolySequence.buyBelowTrader_ec` (`Properties/AffineCoherence.lean`), which has no
fuel-class form: the bridge `BigSpliceStream.toMachine` runs fuel to machine, and no map
back is proved or claimed.  The
calibration is stated at `def:ec` in `Framework/Affine.lean`, and the `_unconditional`
endpoints discharge the criterion through `LIA_is_logical_inductor`.

-/

namespace LogicalInduction

open Filter Topology

/-- The `dd:mesh` shrinking step: a fixed constant over the day-`n` grid width eventually
falls below any positive `ε`. Every endpoint here turns a `1/(n+1)`-accurate world
hypothesis into an `ε`-accurate one through this lemma. -/
lemma exists_eventually_const_div_lt (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (1 / ((n : ℝ) + 1)) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hNn : C / ε < (n : ℝ) + 1 :=
    hN.trans_le (by have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
                    linarith)
  have hC : C < ((n : ℝ) + 1) * ε := (div_lt_iff₀ hε).mp hNn
  calc
    C * (1 / ((n : ℝ) + 1)) = C / ((n : ℝ) + 1) := by ring
    _ < ε := (div_lt_iff₀ hnR).2 (by nlinarith)

namespace LUV

/-! ## Threshold bundles (`def:e`) -/

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

/-- Uniform emission certificate for the growing threshold bundles of `X`. It consumes
`BigThresholdCodes`, the write-out threshold-code class of `dd:luv-arith` — `def:ec`'s own
metering — which is what discharges the paper's "the LUV's threshold sentences are
efficiently codeable" hypothesis. The certificate *is* the hypothesis: the class unfolds to
exactly the `sentence_poly` field this builds. Consumed by
`Properties/ExpectationConvergence.lean` and by `lic_expectation_provind` / `_le` here. -/
noncomputable def expectAffine_polySequence (X : LUV) (hcode : X.MachineThresholdCodes) :
    AffineCombination.PolySequence X.expectAffine := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  exact {
  termCount := fun n => n
  coefficient := fun z => .const (1 / (z.unpair.1 : ℚ))
  sentence := fun z => X.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
  termCount_poly := UnaryRuler.id
  const_poly := MachineSpliceStream.serialize_const 0
  coefficient_poly := (BigSpliceStream.serialize_const_comp
    ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩).toMachine
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

/-! ## Indicator discrepancies -/

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

`thm:ei` is stated in the paper for an e.c. *sequence* of sentences `⟨φ⟩`, so the affine
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

/-- Uniform emission certificate for the day-indexed indicator discrepancies. It consumes
the sequence-level threshold-code class `RpnThresholdCodeSeq` (`dd:luv-arith`) together with
sentence codes for `⟨φ⟩`, discharging both efficient-sequence hypotheses `thm:ei` states.
Consumed by `lic_expectation_indicator`. -/
noncomputable def indicatorAffineSeq_polySequence (Y : ℕ → LUV) (φ : ℕ → Sentence)
    (hY : LUV.MachineThresholdCodeSeq Y) (hφ : MachineSentenceCodes φ) :
    AffineCombination.PolySequence (indicatorAffineSeq Y φ) := by
  let cinv := Classical.choose encode_inv_nat_polyFueled
  have hinv := Classical.choose_spec encode_inv_nat_polyFueled
  have htest := subc_polyFueled.comp
    (PolyFueled.left.succ_comp.pair PolyFueled.right)
  have hInvSeg : BigSpliceStream
      (fun z => (EF.const (1 / ((z.unpair.1 + 1 : ℕ) : ℚ))).serialize) :=
    BigSpliceStream.serialize_const_comp
      ⟨cinv.comp (Nat.Partrec.Code.succ.comp Nat.Partrec.Code.left),
        hinv.comp PolyFueled.left.succ_comp⟩
  have hNegSeg : BigSpliceStream (fun _ : ℕ => (EF.const (-1)).serialize) :=
    BigSpliceStream.serialize_const (-1)
  have hthr : MachineSentenceCodes (fun z => (Y z.unpair.1).gt
      ((z.unpair.2 : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ))) :=
    (MachineSentenceCodes.comp hY (UnaryRuler.unpairFst.pair
      (UnaryRuler.unpairFst.succ.pair UnaryRuler.unpairSnd))).of_eq (fun z => by simp)
  have hsen : MachineSentenceCodes (fun z => φ z.unpair.1) :=
    hφ.comp (UnaryRuler.unpairFst)
  exact {
    termCount := fun n => n + 2
    coefficient := fun z => if z.unpair.2 < z.unpair.1 + 1
      then .const (1 / ((z.unpair.1 + 1 : ℕ) : ℚ)) else .const (-1)
    sentence := fun z => if z.unpair.2 < z.unpair.1 + 1
      then (Y z.unpair.1).gt ((z.unpair.2 : ℚ) / ((z.unpair.1 + 1 : ℕ) : ℚ))
      else φ z.unpair.1
    termCount_poly := UnaryRuler.id.succ.succ
    const_poly := MachineSpliceStream.serialize_const 0
    coefficient_poly := BigSpliceStream.toMachine <| BigSpliceStream.of_eq
      (BigSpliceStream.ifZero hNegSeg hInvSeg htest) (by
        intro z
        simp only [Nat.unpair_pair]
        by_cases hj : z.unpair.2 < z.unpair.1 + 1
        · rw [if_pos hj, if_neg (by omega)]
        · rw [if_neg hj, if_pos (by omega)])
    sentence_poly :=
      (MachineSentenceCodes.ifZero hsen hthr (UnaryRuler.of_polyFueled htest)).of_eq (by
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

/-! ## The linearity discrepancy -/

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

/-- Uniform emission certificate for the linearity discrepancy `a·𝔼X + b·𝔼Y − 𝔼Z`. It
consumes one `BigThresholdCodes` per LUV (`dd:luv-arith`), which is what discharges
`thm:loe`'s efficient-codeability hypothesis. Consumed by
`lic_linearity_of_expectation`. -/
noncomputable def linearityAffine_polySequence (a b : ℚ) (X Y Z : LUV)
    (hX : X.MachineThresholdCodes) (hY : Y.MachineThresholdCodes)
    (hZ : Z.MachineThresholdCodes) :
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
  have hInv : BigSpliceStream (fun z => (EF.const (1 / (z.unpair.1 : ℚ))).serialize) :=
    BigSpliceStream.serialize_const_comp
      ⟨cinv.comp Nat.Partrec.Code.left, hinv.comp PolyFueled.left⟩
  have hcoeff (q : ℚ) : BigSpliceStream (fun z =>
      (EF.mul (EF.const q) (EF.const (1 / (z.unpair.1 : ℚ)))).serialize) :=
    BigSpliceStream.serialize_mul (BigSpliceStream.serialize_const q) hInv
  have hcoeffAll : BigSpliceStream (fun z =>
      (if z.unpair.2 < z.unpair.1 then
        EF.mul (EF.const a) (EF.const (1 / (z.unpair.1 : ℚ)))
      else if z.unpair.2 < z.unpair.1 * 2 then
        EF.mul (EF.const b) (EF.const (1 / (z.unpair.1 : ℚ)))
      else EF.mul (EF.const (-1)) (EF.const (1 / (z.unpair.1 : ℚ)))).serialize) := by
    refine BigSpliceStream.of_eq
      (BigSpliceStream.ifZero (hcoeff a)
        (BigSpliceStream.ifZero (hcoeff b) (hcoeff (-1)) htestY) htestX) ?_
    intro z
    simp only [Nat.unpair_pair]
    by_cases hx : z.unpair.2 < z.unpair.1
    · rw [if_pos hx, if_pos (by omega)]
    · rw [if_neg hx, if_neg (by omega)]
      by_cases hy : z.unpair.2 < z.unpair.1 * 2
      · rw [if_pos hy, if_pos (by omega)]
      · rw [if_neg hy, if_neg (by omega)]
  have hsX := hX
  have hsY := MachineSentenceCodes.comp hY (UnaryRuler.of_polyFueled hidxY)
  have hsZ := MachineSentenceCodes.comp hZ (UnaryRuler.of_polyFueled hidxZ)
  have hsAll : MachineSentenceCodes (fun z =>
      if z.unpair.2 < z.unpair.1 then
        X.gt ((z.unpair.2 : ℚ) / (z.unpair.1 : ℚ))
      else if z.unpair.2 < z.unpair.1 * 2 then
        Y.gt (((z.unpair.2 - z.unpair.1 : ℕ) : ℚ) / (z.unpair.1 : ℚ))
      else Z.gt (((z.unpair.2 - z.unpair.1 * 2 : ℕ) : ℚ) / (z.unpair.1 : ℚ))) := by
    refine (MachineSentenceCodes.ifZero (hsX)
      (MachineSentenceCodes.ifZero (hsY)
        (hsZ) (UnaryRuler.of_polyFueled htestY))
      (UnaryRuler.of_polyFueled htestX)).of_eq (fun z => ?_)
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
    termCount_poly := UnaryRuler.id.mul (UnaryRuler.const 3)
    const_poly := MachineSpliceStream.serialize_const 0
    coefficient_poly := hcoeffAll.toMachine
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

/-! ## Expectations of indicators (`thm:ei`) -/

/-- **Expectations of indicators** (`thm:ei`).  For an efficiently computable sequence of
sentences `⟨φ⟩` and an indicator family `Yₙ` for `φₙ` (the paper's `1(φₙ)`, rendered
relationally over `cworlds(Θ)` by `LUV.IsIndicator`), the day-`n` expectation of the
indicator tracks the day-`n` price of the sentence: `𝔼ₙ(1(φₙ)) ≈ₙ Pₙ(φₙ)`.

The sequence — not a fixed sentence — is the paper's statement (tex:1719); the constant
case is the instance `φ n = φ`, `Y n = Y`.

*What the arithmetic form costs.*  The paper's indicator is the literal formula
`1(φ) := ⌜(⌜φ⌝ ∧ ν = 1) ∨ (¬⌜φ⌝ ∧ ν = 0)⌝` over an arithmetic LUV (tex:1711-1713), whose
`[0,1)` thresholds are arithmetic sentences `Θ` proves equivalent to `φ` and that are not
`φ`.  The propositional substrate has no arithmetic LUVs, so what it renders is that
observable content: `LUV.indicatorOf` (`Framework/Expectations.lean`) takes the `[0,1)`
threshold to be `φ ⋏ ∼∼φ`, equivalent to `φ` in every world and distinct from it as a term,
and `lic_expectation_indicator_unconditional` below is this theorem at that family, with
both data premises discharged.  Clients with a different `1(φ)` supply it here as `Y`
together with its threshold codes.

The interface is inhabited more widely than by that representative:
`indicatorWitness_isIndicator` (`Framework/Expectations.lean`) is the exhibit whose threshold
sentences are equivalent to `φ` only in completed-theory worlds — the paper's own situation,
which no propositional tautology reproduces — and
`semanticValuedDiagonalLUVSeq_isIndicator` (`Construction/SemanticExtension/Prime.lean`)
also inhabits it, though there the thresholds in `[0,1)` are the indicated sentence itself
and the family is consumed for its `ValuesAt` corollary in the `thm:ccee` lane rather than
as a carrier of this node.

No family whose thresholds are literally `φ` is offered as a witness *for `thm:ei`*, and
that is deliberate.  At such a family every sampled threshold `i/(n+1)` with `i < n + 1`
lies in `[0,1)`, so `𝔼ₙ(Yₙ) = (1/(n+1))·∑_{i<n+1} Pₙ(φₙ) = Pₙ(φₙ)` by arithmetic alone,
for every market: the conclusion would be an identity in which `[IsLogicalInductor]` does
no work, and the theorem's content — the market learning the growing bundle of threshold
equivalences uniformly — would be gone.
Paper node: `thm:ei` -/
theorem lic_expectation_indicator (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (Y : ℕ → LUV) (hcode : LUV.MachineThresholdCodeSeq Y)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hY : ∀ n, (Y n).IsIndicator (φ n) DP) :
    AsympEq (fun n => (Y n).expect P n) (fun n => P n (φ n)) := by
  have hP : ∀ n ψ, 0 ≤ P n ψ ∧ P n ψ ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
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
    filter_upwards [exists_eventually_const_div_lt 1 ε hε] with n hraw v hv
    have hsmall : 1 / ((n + 1 : ℕ) : ℝ) < ε := by push_cast; linarith [hraw]
    have hnear := ((hY n).valuesAt hv).expectApprox_near n.succ_pos
    rw [LUV.indicatorAffineSeq_value]
    exact hnear.trans hsmall.le
  have hzero := (LUV.indicatorAffineSeq_polySequence Y φ hcode
    hφ).affine_provind_theory_tendsto_zero P DP hbounded ⟨2, hmagn⟩ hcons hsemantic
  simpa only [LUV.indicatorAffineSeq_price, AsympEq, sub_zero] using hzero

/-- **Expectations of indicators** (`thm:ei`) at the paper's own quantifier: for an
efficiently computable sequence of sentences `⟨φ⟩` and nothing else,
`𝔼ₙ(1(φₙ)) ≈ₙ Pₙ(φₙ)`, where `1(φ)` is the paper's indicator LUV rendered at a
*non-degenerate* threshold family (`LUV.indicatorOf`, tex:1712): its `[0,1)` thresholds are
`φ ⋏ ∼∼φ`, propositionally equivalent to `φ` in every world and not the term `φ`
(`LUV.indicatorOf_gt_ne`).  The threshold certificate is *derived* from `hφ`
(`LUV.indicatorOf_machineThresholdCodeSeq`) rather than assumed, and the indicator
hypothesis is discharged by construction (`LUV.indicatorOf_isIndicator`), so the only data
premise left is the paper's e.c. sentence sequence.

The conclusion is not an identity: `expectation_indicator_not_identity` below exhibits a
market pricing `φ` and `φ ⋏ ∼∼φ` apart, so `[IsLogicalInductor]` is what forces the two
together.  The relational `lic_expectation_indicator` above stays the engine and the more
general statement — it holds of every indicator family, including those whose threshold
links only `Θ` reveals, which is the paper's own arithmetic situation.
Paper node: `thm:ei` -/
theorem lic_expectation_indicator_unconditional (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    AsympEq (fun n => (LUV.indicatorOf (φ n)).expect P n) (fun n => P n (φ n)) :=
  lic_expectation_indicator P DP φ hφ (fun n => LUV.indicatorOf (φ n))
    (LUV.indicatorOf_machineThresholdCodeSeq hφ) hcons
    (fun n => LUV.indicatorOf_isIndicator (φ n) DP)

/-- The thresholds the endpoint above averages are not the sentence it prices. -/
example (φ : Sentence) : (LUV.indicatorOf φ).gt (1 / 2) ≠ φ :=
  LUV.indicatorOf_gt_ne φ (by norm_num) (by norm_num)

/-- **`thm:ei`'s conclusion is not an identity** (kind `N+`).  A market is a bare
`ℕ → Sentence → ℝ`, so nothing stops one pricing `φ` at `0` and the equivalent `φ ⋏ ∼∼φ` at
`1`; at such a market the day-`0` expectation of `1(φ)` — the single grid point `0`, whose
threshold is `φ ⋏ ∼∼φ` — and the price of `φ` differ by the whole unit interval.  So
`lic_expectation_indicator_unconditional` says something about `[IsLogicalInductor]` markets
that is false of markets in general: the criterion is what closes the gap. -/
lemma expectation_indicator_not_identity :
    ∃ (P : History) (n : ℕ) (φ : Sentence), (LUV.indicatorOf φ).expect P n ≠ P n φ := by
  classical
  refine ⟨fun _ ψ => if ψ = (LO.Propositional.Formula.atom 0 : Sentence) then 0 else 1, 0,
    LO.Propositional.Formula.atom 0, ?_⟩
  have hne : (LUV.indicatorOf (LO.Propositional.Formula.atom 0 : Sentence)).gt 0
      ≠ (LO.Propositional.Formula.atom 0 : Sentence) :=
    LUV.indicatorOf_gt_ne _ le_rfl (by norm_num)
  simp [LUV.expect, LUV.expectApprox, hne]

/-! ## Linearity of expectation (`thm:loe`) -/

/-- **Linearity of expectation** (`thm:loe`, fixed `X, Y, Z` form), finite-precision
hypothesis.

The world hypothesis is the finite-precision agreement the trader argument consumes: in
every day-`n` plausible world, `X`, `Y`, `Z` have values `x, y, z` with `z = a x + b y`, and
the day-`n` approximate expectations (grid `n + 1`) sit within `1/(n+1)` of them.  This is
satisfiable at a finite stage, unlike the full `PCWorld.ValuesAt` cut, which pins infinitely
many thresholds; `lic_linearity_of_expectation_ofValuesAt` recovers the `ValuesAt` form via
`expectApprox_near`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (a b : ℚ) (X Y Z : LUV)
    (hcodeX : X.MachineThresholdCodes) (hcodeY : Y.MachineThresholdCodes)
    (hcodeZ : Z.MachineThresholdCodes)
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
    filter_upwards [hvals, exists_eventually_const_div_lt C ε hε]
      with n hvals_n hsmall v hv
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

/-- **Linearity of expectation** (`thm:loe`), full `PCWorld.ValuesAt` form.  Recovers the
original statement as a corollary of the finite-precision form: `ValuesAt` implies the day-`n`
approximation bound via `expectApprox_near`, and the world's linear relation on exact values
supplies `z = a x + b y`.
Paper node: `thm:loe` -/
theorem lic_linearity_of_expectation_ofValuesAt (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (a b : ℚ) (X Y Z : LUV)
    (hcodeX : X.MachineThresholdCodes) (hcodeY : Y.MachineThresholdCodes)
    (hcodeZ : Z.MachineThresholdCodes)
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

/-! ## Expectation provability induction (`thm:expprovind`) -/

/-- **Expectation Provability Induction** (`thm:expprovind`), finite-precision form.

The world hypothesis is the day-`n` approximation bound `|𝔼_{n+1}^v(X) − x| ≤ 1/(n+1)` with
`c ≤ x` (day `n` carries grid `n + 1`, `def:e`) — the satisfiable, finite-stage content the
trader argument consumes.  `lic_expectation_provind_ofValuesAt` recovers the full
`PCWorld.ValuesAt` statement.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.MachineThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x : ℝ, c ≤ x ∧ |X.expectApprox v.payout (n + 1) - x| ≤ 1 / ((n : ℝ) + 1)) :
    AsympGE (X.expectSeq P) (fun _ => c) := by
  intro ε hε
  have hsemantic : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        c - ε / 2 ≤ (X.expectAffine (n + 1)).value P v.payout := by
    filter_upwards [hval, exists_eventually_const_div_lt 1 (ε / 2) (by linarith)]
      with n hval_n hraw v hv
    have hsmall : 1 / ((n : ℝ) + 1) < ε / 2 := by linarith [hraw]
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

/-- **Expectation Provability Induction** (`thm:expprovind`), full `PCWorld.ValuesAt` form.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_ofValuesAt (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.MachineThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x, c ≤ x ∧ v.ValuesAt X x) :
    AsympGE (X.expectSeq P) (fun _ => c) :=
  lic_expectation_provind P DP X hcode hcons c
    (Filter.Eventually.of_forall (fun n v hv => by
      obtain ⟨x, hcx, hx⟩ := hval n v hv
      exact ⟨x, hcx, by simpa using hx.expectApprox_near n.succ_pos⟩))

/-- **Expectation Provability Induction** (`thm:expprovind`), upper (`≤`) form.  Dual of the
lower form through the negated affine mesh.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_le (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.MachineThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∃ x : ℝ, x ≤ c ∧ |X.expectApprox v.payout (n + 1) - x| ≤ 1 / ((n : ℝ) + 1)) :
    AsympLE (X.expectSeq P) (fun _ => c) := by
  intro ε hε
  have hsemantic : ∀ᶠ n in atTop, ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) →
        -c - ε / 2 ≤ ((X.expectAffine (n + 1)).neg).value P v.payout := by
    filter_upwards [hval, exists_eventually_const_div_lt 1 (ε / 2) (by linarith)]
      with n hval_n hraw v hv
    have hsmall : 1 / ((n : ℝ) + 1) < ε / 2 := by linarith [hraw]
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

/-- **Expectation Provability Induction** (`thm:expprovind`), equality (`=`) form.  Combines the
lower and upper forms: a determined LUV value forces the expectation sequence to it.
Paper node: `thm:expprovind` -/
theorem lic_expectation_provind_eq (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (X : LUV) (hcode : X.MachineThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (c : ℝ)
    (hval : ∀ᶠ n in atTop, ∀ (v : PCWorld), v.ConsistentWith (DP.D n) →
      |X.expectApprox v.payout (n + 1) - c| ≤ 1 / ((n : ℝ) + 1)) :
    AsympEq (X.expectSeq P) (fun _ => c) := by
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

end LogicalInduction
