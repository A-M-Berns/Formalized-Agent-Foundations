/-
# Uniform Non-Dogmatism — §4.6, `thm:obu`

The varying-sentence form of the non-dogmatism scale ladder: rung `j` buys from the
currently enumerated sentence whenever its price falls below `1/j³`, spends at most `1/j²`
over its lifetime, and permanently disarms after one full trigger.  A world satisfying the
whole enumerated theory values every purchased share at one, so the ladder is bounded below
while a single rung firing already yields profit `j − 1`.
-/
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Framework.WriteOut

namespace LogicalInduction

open Filter Topology

/-- Every member of an enumeration reappears arbitrarily late.  This is the paper's
triangular repetition preprocessing, stated independently of any market. -/
def RepeatsEveryMember (φ : ℕ → Sentence) : Prop :=
  ∀ i N, ∃ n, N ≤ n ∧ φ n = φ i

/-- Rung-`j`, day-`i` signal for the current member `φ i`. -/
def obuBuySig (φ : ℕ → Sentence) (j i : ℕ) : EF :=
  ndBuySig (φ i) j i

@[simp] lemma obuBuySig_rank (φ : ℕ → Sentence) (j i : ℕ) :
    (obuBuySig φ j i).rank = i := ndBuySig_rank (φ i) j i

lemma obuBuySig_denote_pad (φ : ℕ → Sentence) (P : History)
    {j i : ℕ} (h : i < j) :
    (obuBuySig φ j i).denote P = 0 :=
  ndBuySig_denote_pad (φ i) P h

lemma obuBuySig_mem (φ : ℕ → Sentence) (P : History) (j i : ℕ) :
    0 ≤ (obuBuySig φ j i).denote P ∧ (obuBuySig φ j i).denote P ≤ 1 :=
  ndBuySig_mem (φ i) P j i

lemma obuBuySig_pos_imp (φ : ℕ → Sentence) (P : History)
    {j i : ℕ} (hj : 1 ≤ j) (h : 0 < (obuBuySig φ j i).denote P) :
    P i (φ i) < 1 / (j : ℝ) ^ 3 :=
  ndBuySig_pos_imp (φ i) P hj h

lemma obuBuySig_eq_one (φ : ℕ → Sentence) (P : History)
    {j i : ℕ} (hj : 1 ≤ j) (hlive : j ≤ i)
    (h : P i (φ i) < ((ndThr j : ℚ) : ℝ)) :
    (obuBuySig φ j i).denote P = 1 :=
  ndBuySig_eq_one (φ i) P hj hlive h

/-- Per-unit day-`n` purchase made by varying-sentence rung `j`. -/
noncomputable def obuShares (φ : ℕ → Sentence) (P : History) (j n : ℕ) : ℝ :=
  (armChain (obuBuySig φ j) n).denote P * (obuBuySig φ j n).denote P

lemma obuShares_nonneg (φ : ℕ → Sentence) (P : History) (j n : ℕ) :
    0 ≤ obuShares φ P j n :=
  mul_nonneg (armChain_mem _ P (fun i ↦ obuBuySig_mem φ P j i) n).1
    (obuBuySig_mem φ P j n).1

lemma obuShares_pos_sig {φ : ℕ → Sentence} {P : History} {j n : ℕ}
    (h : 0 < obuShares φ P j n) : 0 < (obuBuySig φ j n).denote P := by
  rcases (obuBuySig_mem φ P j n).1.lt_or_eq with hs | hs
  · exact hs
  · rw [obuShares, ← hs, mul_zero] at h
    exact absurd h (lt_irrefl 0)

lemma obuShares_sum (φ : ℕ → Sentence) (P : History)
    {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, obuShares φ P j n =
      1 - (armChain (obuBuySig φ j) N).denote P := by
  simp only [obuShares]
  rw [armChain_shares_sum (obuBuySig φ j) P h,
    armChain_denote_of_le (obuBuySig φ j) P
      (fun i hi ↦ obuBuySig_denote_pad φ P hi) j le_rfl]

lemma obuShares_sum_le_one (φ : ℕ → Sentence) (P : History)
    {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, obuShares φ P j n ≤ 1 := by
  rw [obuShares_sum φ P h]
  have := (armChain_mem (obuBuySig φ j) P
    (fun i ↦ obuBuySig_mem φ P j i) N).1
  linarith

/-- Day-`n` coefficient of varying-sentence rung `j`. -/
def obuCoef (φ : ℕ → Sentence) (j n : ℕ) : EF :=
  .mul (.const (j : ℚ))
    (.mul (armChain (obuBuySig φ j) n) (obuBuySig φ j n))

lemma obuCoef_denote (φ : ℕ → Sentence) (P : History) (j n : ℕ) :
    (obuCoef φ j n).denote P = (j : ℝ) * obuShares φ P j n := by
  simp only [obuCoef, EF.denote_mul, EF.denote_const, Pi.mul_apply, obuShares]
  push_cast
  ring

lemma obuCoef_rank (φ : ℕ → Sentence) (j n : ℕ) :
    (obuCoef φ j n).rank ≤ n := by
  have h1 := armChain_rank (obuBuySig φ j)
    (fun i ↦ (obuBuySig_rank φ j i).le) n
  have h2 := (obuBuySig_rank φ j n).le
  simp only [obuCoef, EF.rank, max_le_iff]
  omega

/-- Sum of all live rungs on day `n`. -/
def obuLadderEF (φ : ℕ → Sentence) (n : ℕ) : ℕ → EF
  | 0 => .const 0
  | (m + 1) => .add (obuLadderEF φ n m) (obuCoef φ (m + 1) n)

lemma obuLadderEF_denote (φ : ℕ → Sentence) (P : History) (n : ℕ) : ∀ m,
    (obuLadderEF φ n m).denote P =
      ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * obuShares φ P (k + 1) n
  | 0 => by simp [obuLadderEF]
  | (m + 1) => by
      rw [obuLadderEF]
      simp only [EF.denote_add, Pi.add_apply]
      rw [obuLadderEF_denote φ P n m, Finset.sum_range_succ, obuCoef_denote]

lemma obuLadderEF_rank (φ : ℕ → Sentence) (n : ℕ) : ∀ m,
    (obuLadderEF φ n m).rank ≤ n
  | 0 => by simp [obuLadderEF]
  | (m + 1) => by
      have h1 := obuLadderEF_rank φ n m
      have h2 := obuCoef_rank φ (m + 1) n
      simp only [obuLadderEF, EF.rank, max_le_iff]
      omega

/-- The varying-sentence scale-ladder trader used by Uniform Non-Dogmatism. -/
def obuTrader (φ : ℕ → Sentence) : Trader where
  strat n := {
    trades := [(obuLadderEF φ n n, φ n)]
    rank_le := by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact obuLadderEF_rank φ n n }

@[simp] lemma obuTrader_value (φ : ℕ → Sentence) (P : History)
    (w : Valuation) (n : ℕ) :
    ((obuTrader φ).strat n).value P w =
      (obuLadderEF φ n n).denote P * (w (φ n) - P n (φ n)) := by
  simp [obuTrader, Strategy.value]

lemma obuTrader_netWorth (φ : ℕ → Sentence) (P : History)
    (v : PCWorld) (m : ℕ) :
    (obuTrader φ).netWorth P v m =
      ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range n,
        ((k + 1 : ℕ) : ℝ) * obuShares φ P (k + 1) n *
          (v.payout (φ n) - P n (φ n)) := by
  simp only [Trader.netWorth, obuTrader_value, obuLadderEF_denote, Finset.sum_mul]

/-- Swap the day/rung triangle in the ladder's finite accounting sum. -/
private lemma obu_sum_range_triangle_comm (f : ℕ → ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ k ∈ Finset.range n, f k n =
      ∑ k ∈ Finset.range N, ∑ n ∈ Finset.Ico (k + 1) N, f k n := by
  simp only [Finset.range_eq_Ico]
  exact (Finset.sum_Ico_Ico_comm' 0 N (fun k n ↦ f k n)).symm

lemma obuTerm_ge (φ : ℕ → Sentence) (P : History) (v : PCWorld)
    {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    -(obuShares φ P j n * (1 / (j : ℝ) ^ 2)) ≤
      (j : ℝ) * obuShares φ P j n * (v.payout (φ n) - P n (φ n)) := by
  have hb := obuShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hprice := obuBuySig_pos_imp φ P hj (obuShares_pos_sig hb')
    have hpay : 0 ≤ v.payout (φ n) := by rw [PCWorld.payout]; split <;> norm_num
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hjb : 0 < (j : ℝ) * obuShares φ P j n := mul_pos (by linarith) hb'
    have hge : -(1 / (j : ℝ) ^ 3) ≤ v.payout (φ n) - P n (φ n) := by linarith
    calc
      -(obuShares φ P j n * (1 / (j : ℝ) ^ 2)) =
          (j : ℝ) * obuShares φ P j n * (-(1 / (j : ℝ) ^ 3)) := by
            rw [← ndWeight_mul hj]
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hge hjb.le
  · rw [← hb']
    norm_num

lemma obuTerm_nonneg (φ : ℕ → Sentence) (P : History) (v : PCWorld)
    (hv : ∀ i, v.Holds (φ i)) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    0 ≤ (j : ℝ) * obuShares φ P j n * (v.payout (φ n) - P n (φ n)) := by
  have hb := obuShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hprice := obuBuySig_pos_imp φ P hj (obuShares_pos_sig hb')
    have hpay : v.payout (φ n) = 1 := by rw [PCWorld.payout, if_pos (hv n)]
    have hle := ndCube_le_one hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    rw [hpay]
    exact mul_nonneg (mul_nonneg (by linarith) hb'.le) (by linarith)
  · rw [← hb']
    norm_num

lemma obuTerm_profit (φ : ℕ → Sentence) (P : History) (v : PCWorld)
    (hv : ∀ i, v.Holds (φ i)) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    (j : ℝ) * obuShares φ P j n * (1 - 1 / (j : ℝ) ^ 3) ≤
      (j : ℝ) * obuShares φ P j n * (v.payout (φ n) - P n (φ n)) := by
  have hpay : v.payout (φ n) = 1 := by rw [PCWorld.payout, if_pos (hv n)]
  rw [hpay]
  have hb := obuShares_nonneg φ P j n
  rcases hb.lt_or_eq with hb' | hb'
  · have hprice := obuBuySig_pos_imp φ P hj (obuShares_pos_sig hb')
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    exact mul_le_mul_of_nonneg_left (by linarith)
      (mul_nonneg (by linarith) hb'.le)
  · rw [← hb']
    norm_num

/-- The varying ladder exploits if every rung receives one full trigger and
every finite deductive stage has a world satisfying the whole enumerated theory. -/
lemma obuTrader_exploits
    (P : History) (DP : DeductiveProcess) (φ : ℕ → Sentence)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (φ i))
    (hfire : ∀ j, 1 ≤ j → ∃ n, j ≤ n ∧ P n (φ n) < ((ndThr j : ℚ) : ℝ)) :
    (obuTrader φ).Exploits P DP := by
  refine exploits_of_bddBelow_of_unbounded _ _ _ 2 ?_ ?_
  · rintro x ⟨m, v, hv, rfl⟩
    rw [obuTrader_netWorth, obu_sum_range_triangle_comm]
    have hk : ∀ k ∈ Finset.range (m + 1),
        -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) ≤
          ∑ n ∈ Finset.Ico (k + 1) (m + 1),
            ((k + 1 : ℕ) : ℝ) * obuShares φ P (k + 1) n *
              (v.payout (φ n) - P n (φ n)) := by
      intro k hkm
      have hj : 1 ≤ k + 1 := by omega
      have hsum := obuShares_sum_le_one φ P
        (j := k + 1) (N := m + 1)
        (by simp only [Finset.mem_range] at hkm; omega)
      have hw2 : (0 : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
      calc
        -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) ≤
            -((∑ n ∈ Finset.Ico (k + 1) (m + 1), obuShares φ P (k + 1) n) *
              (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
                have h1 := mul_le_mul_of_nonneg_right hsum hw2
                rw [one_mul] at h1
                linarith
        _ = ∑ n ∈ Finset.Ico (k + 1) (m + 1),
              -(obuShares φ P (k + 1) n *
                (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) := by
              rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
        _ ≤ _ := Finset.sum_le_sum (fun n _ ↦ obuTerm_ge φ P v hj n)
    calc
      (-2 : ℝ) ≤ -∑ k ∈ Finset.range (m + 1),
          (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 := by
            have := sum_inv_sq_le_two (m + 1)
            linarith
      _ = ∑ k ∈ Finset.range (m + 1),
          -((1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) := by
            rw [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum hk
  · intro B
    obtain ⟨j', hj'⟩ := exists_nat_gt B
    have hj : 1 ≤ j' + 1 := by omega
    obtain ⟨n₀, hn₀, hdip⟩ := hfire (j' + 1) hj
    obtain ⟨v, hv, hvφ⟩ := hjoint n₀
    refine ⟨(obuTrader φ).netWorth P v n₀, ⟨n₀, v, hv, rfl⟩, ?_⟩
    rw [obuTrader_netWorth, obu_sum_range_triangle_comm]
    have hterm : ∀ k ∈ Finset.range (n₀ + 1),
        0 ≤ ∑ n ∈ Finset.Ico (k + 1) (n₀ + 1),
          ((k + 1 : ℕ) : ℝ) * obuShares φ P (k + 1) n *
            (v.payout (φ n) - P n (φ n)) :=
      fun k _ ↦ Finset.sum_nonneg
        (fun n _ ↦ obuTerm_nonneg φ P v hvφ (by omega) n)
    have hjmem : j' ∈ Finset.range (n₀ + 1) := Finset.mem_range.mpr (by omega)
    have harm0 : (armChain (obuBuySig φ (j' + 1)) (n₀ + 1)).denote P = 0 := by
      rw [armChain_denote_succ, obuBuySig_eq_one φ P hj hn₀ hdip]
      ring
    have hsum1 : ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
        obuShares φ P (j' + 1) n = 1 := by
      rw [obuShares_sum φ P (by omega), harm0, sub_zero]
    have hj1 : (1 : ℝ) ≤ ((j' + 1 : ℕ) : ℝ) := by exact_mod_cast hj
    have hslice : ((j' + 1 : ℕ) : ℝ) - 1 ≤
        ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
          ((j' + 1 : ℕ) : ℝ) * obuShares φ P (j' + 1) n *
            (v.payout (φ n) - P n (φ n)) := by
      calc
        ((j' + 1 : ℕ) : ℝ) - 1 ≤
            ((j' + 1 : ℕ) : ℝ) *
              (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3) := by
                have hsq : 1 / ((j' + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
                  rw [div_le_one (by positivity)]
                  nlinarith
                nlinarith [ndWeight_mul (j := j' + 1) hj]
        _ = ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
              ((j' + 1 : ℕ) : ℝ) * obuShares φ P (j' + 1) n *
                (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3) := by
              have hfac : ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
                    ((j' + 1 : ℕ) : ℝ) * obuShares φ P (j' + 1) n *
                      (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3) =
                  (((j' + 1 : ℕ) : ℝ) *
                    (1 - 1 / ((j' + 1 : ℕ) : ℝ) ^ 3)) *
                    ∑ n ∈ Finset.Ico (j' + 1) (n₀ + 1),
                      obuShares φ P (j' + 1) n := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun n _ ↦ by ring)
              rw [hfac, hsum1, mul_one]
        _ ≤ _ := Finset.sum_le_sum
          (fun n _ ↦ obuTerm_profit φ P v hvφ hj n)
    have hB : B < ((j' + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
    have hsingle := Finset.single_le_sum hterm hjmem
    linarith

#print axioms obuTrader_exploits

/-! ## Uniform token emission -/

/-- Serialization block for one historical varying-sentence arm update. -/
def obuArmBlock (φ : ℕ → Sentence) (j i : ℕ) : List ℕ :=
  (oneMinus (obuBuySig φ j i)).serialize ++ [3]

lemma serialize_armChain_obuBuy (φ : ℕ → Sentence) (j : ℕ) : ∀ n,
    (armChain (obuBuySig φ j) n).serialize =
      [1, Encodable.encode ((1 : ℚ))] ++
        (List.range n).flatMap (fun i ↦ obuArmBlock φ j i)
  | 0 => by simp [armChain, EF.serialize]
  | (n + 1) => by
      rw [armChain]
      simp only [EF.serialize]
      rw [serialize_armChain_obuBuy φ j n, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, obuArmBlock]
      simp [List.append_assoc]

lemma serialize_obuCoef (φ : ℕ → Sentence) (j n : ℕ) :
    (obuCoef φ j n).serialize =
      [1, Encodable.encode ((j : ℚ))] ++
        (armChain (obuBuySig φ j) n).serialize ++
        (obuBuySig φ j n).serialize ++ [3, 3] := by
  simp [obuCoef, EF.serialize, List.append_assoc]

lemma serialize_obuLadderEF (φ : ℕ → Sentence) (n : ℕ) : ∀ m,
    (obuLadderEF φ n m).serialize =
      [1, Encodable.encode ((0 : ℚ))] ++
        (List.range m).flatMap
          (fun j' ↦ (obuCoef φ (j' + 1) n).serialize ++ [2])
  | 0 => by simp [obuLadderEF, EF.serialize]
  | (m + 1) => by
      rw [obuLadderEF]
      simp only [EF.serialize]
      rw [serialize_obuLadderEF φ n m, List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      simp [List.append_assoc]

/-- Spliced varying-sentence buy-signal emitter: the sentence slot draws blocks from
an `BigSentenceCodes` certificate, admitting deep enumerations. -/
lemma obuBuySig_spliceStream_comp
    {φ : ℕ → Sentence} (hφ : BigSentenceCodes φ)
    {af δf : ℕ → ℚ} {cj : Nat.Partrec.Code} {jf : ℕ → ℕ}
    (hj : PolyFueled cj jf)
    (ha : ∃ c, PolyFueled c (fun m ↦ Encodable.encode (af m + δf m)))
    (hd : ∃ c, PolyFueled c (fun m ↦ Encodable.encode (1 / δf m))) :
    BigSpliceStream (fun m ↦
      (buyIndEF (φ (jf m)) (af m) (δf m) (jf m)).serialize) :=
  BigSpliceStream.serialize_clip01 (BigSpliceStream.serialize_mul
    (BigSpliceStream.serialize_add (BigSpliceStream.serialize_const_comp ha)
      (BigSpliceStream.serialize_mul (BigSpliceStream.serialize_const (-1))
        (BigSpliceStream.serialize_price hφ hj hj)))
    (BigSpliceStream.serialize_const_comp hd))

/-- Spliced arm-update block. -/
lemma obuArmBlock_spliceStream (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    BigSpliceStream
      (fun x ↦ obuArmBlock φ (x.unpair.1.unpair.2 + 1) x.unpair.2) := by
  have hbuy : BigSpliceStream (fun x ↦
      (obuBuySig φ (x.unpair.1.unpair.2 + 1) x.unpair.2).serialize) := by
    simpa only [obuBuySig, ndBuySig] using
      obuBuySig_spliceStream_comp hφ
        (af := fun x ↦ ndThr (x.unpair.1.unpair.2 + 1))
        (δf := fun x ↦ ndPadThr (x.unpair.1.unpair.2 + 1) x.unpair.2)
        PolyFueled.right
        (encode_thrSum_polyFueled
          (PolyFueled.right.comp PolyFueled.left) PolyFueled.right)
        (encode_thrRecip_polyFueled
          (PolyFueled.right.comp PolyFueled.left) PolyFueled.right)
  exact (BigSpliceStream.serialize_oneMinus hbuy).append
    (BigSpliceStream.tag 3 (by norm_num))

/-- Spliced coefficient chunk (`obuCoef` + the ladder `add` tag): the arm blocks are
variable-length once sentence slots carry blocks, so this uses `concatVar` rather than the
fixed-width `blocks` combinator. -/
lemma obuChunkSeg_spliceStream
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    BigSpliceStream (fun m ↦
      (obuCoef φ (m.unpair.2 + 1) m.unpair.1).serialize ++ [2]) := by
  have segA : BigSpliceStream (fun m ↦
      (EF.const (((m.unpair.2 + 1 : ℕ) : ℚ))).serialize) :=
    BigSpliceStream.serialize_const_comp
      (encode_ratCast_polyFueled PolyFueled.right)
  have segB : BigSpliceStream (fun _ : ℕ ↦ [1, Encodable.encode ((1 : ℚ))]) :=
    BigSpliceStream.payload 1 (Or.inl rfl)
      (PolyFueled.const (Encodable.encode ((1 : ℚ))))
  have segC := (obuArmBlock_spliceStream φ hφ).concatVar PolyFueled.left
  have segD : BigSpliceStream (fun m ↦
      (obuBuySig φ (m.unpair.2 + 1) m.unpair.1).serialize) := by
    simpa only [obuBuySig, ndBuySig] using
      obuBuySig_spliceStream_comp hφ
        (af := fun m ↦ ndThr (m.unpair.2 + 1))
        (δf := fun m ↦ ndPadThr (m.unpair.2 + 1) m.unpair.1)
        PolyFueled.left
        (encode_thrSum_polyFueled PolyFueled.right PolyFueled.left)
        (encode_thrRecip_polyFueled PolyFueled.right PolyFueled.left)
  have segE : BigSpliceStream (fun _ : ℕ ↦ [3, 3, 2]) :=
    ((BigSpliceStream.tag 3 (by norm_num)).append
      (BigSpliceStream.tag 3 (by norm_num))).append
        (BigSpliceStream.tag 2 (by norm_num))
  refine BigSpliceStream.of_eq
    ((((segA.append segB).append segC).append segD).append segE) (fun m ↦ ?_)
  rw [serialize_obuCoef, serialize_armChain_obuBuy]
  simp [EF.serialize, Nat.unpair_pair, List.append_assoc]

/-- The varying-sentence scale ladder is efficiently computable in the symbol-metered
class, from an 𝓔𝓒 enumeration certificate.
Paper node: `def:ec` -/
lemma obuTrader_ec (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ) :
    EfficientlyComputable (obuTrader φ) := by
  have segChunks := (obuChunkSeg_spliceStream φ hφ).concatVar PolyFueled.id
  have seg1 : BigSpliceStream (fun _ : ℕ ↦ [1, Encodable.encode ((0 : ℚ))]) :=
    BigSpliceStream.payload 1 (Or.inl rfl)
      (PolyFueled.const (Encodable.encode ((0 : ℚ))))
  have seg3 := BigSpliceStream.tradeSlot hφ PolyFueled.id
  refine BigSpliceStream.ec _
    (BigSpliceStream.of_eq ((seg1.append segChunks).append seg3) ?_)
  intro n
  show _ = serializeTrades ((obuTrader φ).strat n).trades
  rw [show ((obuTrader φ).strat n).trades = [(obuLadderEF φ n n, φ n)] from rfl,
    serializeTrades, serializeTrades, serialize_obuLadderEF]
  simp [Nat.unpair_pair]

#print axioms obuTrader_ec

/-! ## Uniform lower bound -/

/-- If one member of a repeating enumeration has limiting probability below rung `j`'s
threshold, then that rung eventually receives a full trigger on a day when the same member
is enumerated.  This is the analytic link between fixed-sentence convergence and the
varying-sentence ladder. -/
lemma exists_obu_fire_of_low_limit
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hrepeat : RepeatsEveryMember φ)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {j : ℕ}
    (hlow : ∃ i, limitingBelief P (φ i) < ((ndThr j : ℚ) : ℝ)) :
    ∃ n, j ≤ n ∧ P n (φ n) < ((ndThr j : ℚ) : ℝ) := by
  obtain ⟨i, hi⟩ := hlow
  have hconv := lic_limitingBelief_tendsto P DP hworld (φ i)
  have hevent : ∀ᶠ n in atTop, P n (φ i) < ((ndThr j : ℚ) : ℝ) :=
    (tendsto_order.1 hconv).2 _ hi
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  obtain ⟨n, hn, hφn⟩ := hrepeat i (max j N)
  refine ⟨n, le_trans (le_max_left j N) hn, ?_⟩
  rw [hφn]
  exact hN n (le_trans (le_max_right j N) hn)

/-- Uniform Non-Dogmatism for the efficiently padded, infinitely repeating enumeration
used in the paper's proof.  Joint consistency means that every finite deductive stage has
a propositional world satisfying the entire enumerated theory.
Paper node: `thm:obu` -/
theorem lic_uniform_nonDogmatism_repeating
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (φ : ℕ → Sentence) (hφ : BigSentenceCodes φ)
    (hrepeat : RepeatsEveryMember φ)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (φ i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ limitingBelief P (φ i) := by
  have hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) := by
    intro n
    obtain ⟨v, hv, _⟩ := hjoint n
    exact ⟨v, hv⟩
  by_contra hbound
  have hlow : ∀ ε : ℝ, 0 < ε →
      ∃ i, limitingBelief P (φ i) < ε := by
    intro ε hε
    by_contra hnone
    apply hbound
    refine ⟨ε, hε, fun i ↦ ?_⟩
    exact le_of_not_gt (fun hi ↦ hnone ⟨i, hi⟩)
  have hfire : ∀ j, 1 ≤ j →
      ∃ n, j ≤ n ∧ P n (φ n) < ((ndThr j : ℚ) : ℝ) := by
    intro j hj
    exact exists_obu_fire_of_low_limit P DP φ hrepeat hworld
      (hlow _ (ndThr_pos hj))
  exact IsLogicalInductor.noExploit (P := P) (DP := DP)
    (obuTrader φ) (obuTrader_ec φ hφ)
    (obuTrader_exploits P DP φ hjoint hfire)

/-- A concrete witness for the paper's preprocessing of a c.e. sentence stream into an
efficiently emitted stream in which every member repeats infinitely often.  `sound` and
`covers` say that preprocessing changes only order and multiplicity.  This structure is
purely syntactic: it contains neither prices nor a non-dogmatism conclusion.
Paper node: `thm:obu` -/
structure EfficientRepeatedEnumeration (source : ℕ → Sentence) where
  sequence : ℕ → Sentence
  sequence_poly : BigSentenceCodes sequence
  repeats : RepeatsEveryMember sequence
  sound : ∀ j, ∃ i, sequence j = source i
  covers : ∀ i, ∃ j, sequence j = source i

/-- Paper-facing Uniform Non-Dogmatism.  Given the explicit efficient-repetition witness
for the source c.e. stream, every member of a jointly consistent theory receives one
common positive limiting-probability lower bound.
Paper node: `thm:obu` -/
theorem lic_uniform_nonDogmatism
    (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (source : ℕ → Sentence) (rep : EfficientRepeatedEnumeration source)
    (hjoint : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ i, v.Holds (source i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ limitingBelief P (source i) := by
  have hjointRep : ∀ n, ∃ v : PCWorld,
      v.ConsistentWith (DP.D n) ∧ ∀ j, v.Holds (rep.sequence j) := by
    intro n
    obtain ⟨v, hv, hvsource⟩ := hjoint n
    refine ⟨v, hv, fun j ↦ ?_⟩
    obtain ⟨i, hi⟩ := rep.sound j
    rw [hi]
    exact hvsource i
  obtain ⟨ε, hε, hrep⟩ := lic_uniform_nonDogmatism_repeating
    P DP rep.sequence rep.sequence_poly rep.repeats hjointRep
  refine ⟨ε, hε, fun i ↦ ?_⟩
  obtain ⟨j, hj⟩ := rep.covers i
  simpa only [hj] using hrep j

#print axioms exists_obu_fire_of_low_limit
#print axioms lic_uniform_nonDogmatism_repeating
#print axioms lic_uniform_nonDogmatism

end LogicalInduction
