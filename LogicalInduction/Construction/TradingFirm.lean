/-
# Trading firm (`def:tradingfirm`, `lem:tfdom`)

The paper writes the firm as a doubly-infinite geometric mixture.  Its day action is
nevertheless a finite strategy: only traders whose gate has opened can trade, and all
sufficiently large budgets reproduce the raw gated trader.  This file makes the uniform
cutoff used by that compression executable from the expressible-feature syntax.
-/
import LogicalInduction.Construction.Budgeter
import LogicalInduction.Framework.MachineEfficiency
import LogicalInduction.Properties.FinitePerturbations

namespace LogicalInduction

open Classical

namespace EF

/-- Shift a De Bruijn bound environment under one `letE`. -/
def pushBound (x : ℚ) (rho : ℕ → ℚ) : ℕ → ℚ
  | 0 => x
  | i + 1 => rho i

/-- A computable absolute bound for an expressible feature on `[0,1]` histories.
The auxiliary environment bounds De Bruijn variables.  `max` deliberately uses the
sum of its branch bounds; this is coarse but compositional and sufficient for the firm.
-/
def absBoundWith : EF → (ℕ → ℚ) → ℚ
  | .price _ _, _ => 1
  | .const q, _ => |q|
  | .add a b, rho => a.absBoundWith rho + b.absBoundWith rho
  | .mul a b, rho => a.absBoundWith rho * b.absBoundWith rho
  | .max a b, rho => a.absBoundWith rho + b.absBoundWith rho
  | .safeRecip _, _ => 1
  | .var i, rho => rho i
  | .letE x body, rho =>
      body.absBoundWith (pushBound (x.absBoundWith rho) rho)

/-- Closed-feature absolute bound. -/
def absBound (e : EF) : ℚ := e.absBoundWith (fun _ => 0)

lemma absBoundWith_nonneg (e : EF) (rho : ℕ → ℚ)
    (hrho : ∀ i, 0 ≤ rho i) : 0 ≤ e.absBoundWith rho := by
  induction e generalizing rho with
  | price => norm_num [absBoundWith]
  | const q => exact abs_nonneg q
  | add a b iha ihb =>
      exact add_nonneg (iha rho hrho) (ihb rho hrho)
  | mul a b iha ihb =>
      exact mul_nonneg (iha rho hrho) (ihb rho hrho)
  | max a b iha ihb =>
      exact add_nonneg (iha rho hrho) (ihb rho hrho)
  | safeRecip => norm_num [absBoundWith]
  | var i => exact hrho i
  | letE x body ihx ihbody =>
      apply ihbody
      intro i
      cases i with
      | zero => simpa [pushBound] using ihx rho hrho
      | succ i => simpa [pushBound] using hrho i

lemma absBound_nonneg (e : EF) : 0 ≤ e.absBound := by
  apply e.absBoundWith_nonneg
  simp

/-- Soundness of the syntactic bound.  The statement is environment-parametric so the
`letE` case does not expand shared syntax. -/
lemma abs_denoteWith_le (e : EF) (rhoR : List ℝ) (rhoB : ℕ → ℚ)
    (P : History)
    (hP : ∀ day phi, |P day phi| ≤ 1)
    (hrho : ∀ i, |rhoR.getD i 0| ≤ (rhoB i : ℝ))
    (hrho0 : ∀ i, 0 ≤ rhoB i) :
    |e.denoteWith rhoR P| ≤ (e.absBoundWith rhoB : ℝ) := by
  induction e generalizing rhoR rhoB with
  | price phi day => simpa [denoteWith, absBoundWith] using hP day phi
  | const q => simp [denoteWith, absBoundWith]
  | add a b iha ihb =>
      calc
        |(EF.add a b).denoteWith rhoR P| ≤
            |a.denoteWith rhoR P| + |b.denoteWith rhoR P| := by
              simpa [denoteWith] using
                (abs_add_le (a.denoteWith rhoR P) (b.denoteWith rhoR P))
        _ ≤ (a.absBoundWith rhoB : ℝ) + (b.absBoundWith rhoB : ℝ) :=
          add_le_add (iha rhoR rhoB hrho hrho0) (ihb rhoR rhoB hrho hrho0)
        _ = ((EF.add a b).absBoundWith rhoB : ℝ) := by
          simp [absBoundWith]
  | mul a b iha ihb =>
      rw [denoteWith, abs_mul]
      simpa only [absBoundWith, Rat.cast_mul] using
        (mul_le_mul
          (iha rhoR rhoB hrho hrho0) (ihb rhoR rhoB hrho hrho0)
          (abs_nonneg _) (by exact_mod_cast a.absBoundWith_nonneg rhoB hrho0))
  | max a b iha ihb =>
      have ha := iha rhoR rhoB hrho hrho0
      have hb := ihb rhoR rhoB hrho hrho0
      have ha0 : 0 ≤ (a.absBoundWith rhoB : ℝ) := by
        exact_mod_cast a.absBoundWith_nonneg rhoB hrho0
      have hb0 : 0 ≤ (b.absBoundWith rhoB : ℝ) := by
        exact_mod_cast b.absBoundWith_nonneg rhoB hrho0
      rw [denoteWith]
      rw [show ((EF.max a b).absBoundWith rhoB : ℝ) =
          (a.absBoundWith rhoB : ℝ) + (b.absBoundWith rhoB : ℝ) by
        simp [absBoundWith]]
      apply (abs_le).2
      constructor
      · have hlow : -(a.absBoundWith rhoB : ℝ) ≤ a.denoteWith rhoR P :=
          (abs_le.mp ha).1
        exact le_trans (by linarith) (le_trans hlow (le_max_left _ _))
      · apply max_le
        · exact le_trans (abs_le.mp ha).2 (by linarith)
        · exact le_trans (abs_le.mp hb).2 (by linarith)
  | safeRecip a iha =>
      have hbase : (1 : ℝ) ≤ Max.max 1 (a.denoteWith rhoR P) := le_max_left _ _
      have hpos : (0 : ℝ) < Max.max 1 (a.denoteWith rhoR P) := zero_lt_one.trans_le hbase
      rw [denoteWith, abs_of_pos (inv_pos.mpr hpos)]
      simpa [absBoundWith] using (inv_le_one₀ hpos).2 hbase
  | var i => simpa [denoteWith, absBoundWith] using hrho i
  | letE x body ihx ihbody =>
      simp only [denoteWith, absBoundWith]
      apply ihbody (x.denoteWith rhoR P :: rhoR)
        (pushBound (x.absBoundWith rhoB) rhoB)
      · intro i
        cases i with
        | zero => simpa [pushBound] using ihx rhoR rhoB hrho hrho0
        | succ i => simpa [pushBound] using hrho i
      · intro i
        cases i with
        | zero => simpa [pushBound] using x.absBoundWith_nonneg rhoB hrho0
        | succ i => simpa [pushBound] using hrho0 i

lemma abs_denote_le (e : EF) (P : History)
    (hP : ∀ day phi, |P day phi| ≤ 1) :
    |e.denote P| ≤ (e.absBound : ℝ) := by
  apply e.abs_denoteWith_le [] (fun _ => 0) P hP
  · simp
  · simp

end EF

namespace Strategy

private lemma cast_map_sum {α : Type*} (xs : List α) (f : α → ℚ) :
    (((xs.map f).sum : ℚ) : ℝ) = (xs.map fun x => (f x : ℝ)).sum := by
  induction xs with
  | nil => simp
  | cons q xs ih => simp [ih]

/-- Uniform rational bound on the absolute value of a strategy in a `[0,1]` market
against a `[0,1]` payout table. -/
def absBound {n : ℕ} (T : Strategy n) : ℚ :=
  (T.trades.map fun p => p.1.absBound).sum

def tradeListAbsBound (trades : List (EF × Sentence)) : ℚ :=
  (trades.map fun p => p.1.absBound).sum

@[simp] lemma tradeListAbsBound_strategy {n : ℕ} (T : Strategy n) :
    tradeListAbsBound T.trades = T.absBound := by
  rfl

lemma absBound_nonneg {n : ℕ} (T : Strategy n) : 0 ≤ T.absBound := by
  unfold absBound
  exact List.sum_nonneg (fun q hq => by
    simp only [List.mem_map] at hq
    obtain ⟨p, _hp, rfl⟩ := hq
    exact p.1.absBound_nonneg)

lemma abs_value_le {n : ℕ} (T : Strategy n) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (w : Sentence → ℝ) (hw : ∀ phi, 0 ≤ w phi ∧ w phi ≤ 1) :
    |T.value P w| ≤ (T.absBound : ℝ) := by
  have hPabs : ∀ day phi, |P day phi| ≤ 1 := by
    intro day phi
    rw [abs_of_nonneg (hP day phi).1]
    exact (hP day phi).2
  unfold Strategy.value absBound
  rw [cast_map_sum]
  induction T.trades with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hdiff : |w p.2 - P n p.2| ≤ 1 := by
        apply (abs_le).2
        constructor <;> linarith [(hw p.2).1, (hw p.2).2,
          (hP n p.2).1, (hP n p.2).2]
      have hterm : |p.1.denote P * (w p.2 - P n p.2)| ≤
          (p.1.absBound : ℝ) := by
        rw [abs_mul]
        have he := p.1.abs_denote_le P hPabs
        have hb0 : 0 ≤ (p.1.absBound : ℝ) := by
          exact_mod_cast p.1.absBound_nonneg
        simpa using mul_le_mul he hdiff (abs_nonneg _) hb0
      calc
        |p.1.denote P * (w p.2 - P n p.2) +
            (rest.map fun p => p.1.denote P * (w p.2 - P n p.2)).sum| ≤
            |p.1.denote P * (w p.2 - P n p.2)| +
              |(rest.map fun p => p.1.denote P * (w p.2 - P n p.2)).sum| :=
          abs_add_le _ _
        _ ≤ (p.1.absBound : ℝ) +
            (rest.map fun p => (p.1.absBound : ℝ)).sum :=
          add_le_add hterm ih
        _ = ((p :: rest).map fun p => (p.1.absBound : ℝ)).sum := by simp

/-- Scale by a rational constant; constants have rank zero. -/
def scaleConst {n : ℕ} (q : ℚ) (T : Strategy n) : Strategy n :=
  T.scaleBy (.const q) (by simp [EF.rank])

lemma scaleConst_value {n : ℕ} (q : ℚ) (T : Strategy n)
    (P : History) (w : Valuation) :
    (T.scaleConst q).value P w = (q : ℝ) * T.value P w := by
  simp [scaleConst, Strategy.scaleBy_value]

end Strategy

namespace Trader

/-- The paper's gated trader `S^k`: it is silent before its enumeration index opens. -/
def gate (start : ℕ) (Tr : Trader) : Trader where
  strat n := if start ≤ n then Tr.strat n else Trader.zero.strat n

@[simp] lemma gate_strat_of_le (Tr : Trader) {start n : ℕ} (h : start ≤ n) :
    (Tr.gate start).strat n = Tr.strat n := by simp [gate, h]

@[simp] lemma gate_strat_of_lt (Tr : Trader) {start n : ℕ} (h : n < start) :
    (Tr.gate start).strat n = Trader.zero.strat n := by
  simp [gate, Nat.not_le_of_lt h]

/-- Uniform finite-prefix bound between a trader and its launch gate. -/
lemma gate_netWorth_difference_le (Tr : Trader) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (start : ℕ) (v : PCWorld) (n : ℕ) :
    |Tr.netWorth P v n - (Tr.gate start).netWorth P v n| ≤
      (∑ i ∈ Finset.range start, (Tr.strat i).absBound : ℚ) := by
  have hw : ∀ phi, 0 ≤ v.payout phi ∧ v.payout phi ≤ 1 := by
    intro phi
    rw [PCWorld.payout]
    split <;> norm_num
  rw [Trader.netWorth, Trader.netWorth, ← Finset.sum_sub_distrib]
  calc
    |(∑ i ∈ Finset.range (n + 1),
        ((Tr.strat i).value P v.payout -
          ((Tr.gate start).strat i).value P v.payout))| ≤
        ∑ i ∈ Finset.range (n + 1),
          |(Tr.strat i).value P v.payout -
            ((Tr.gate start).strat i).value P v.payout| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          if i < start then ((Tr.strat i).absBound : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases his : i < start
      · rw [if_pos his, Tr.gate_strat_of_lt his]
        simpa [Trader.zero, Strategy.value] using
          Strategy.abs_value_le (Tr.strat i) P hP v.payout hw
      · rw [if_neg his, Tr.gate_strat_of_le (Nat.le_of_not_gt his)]
        simp
    _ = ∑ i ∈ (Finset.range (n + 1)).filter (fun i => i < start),
          ((Tr.strat i).absBound : ℝ) := by rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ Finset.range start, ((Tr.strat i).absBound : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact hi.2
      · intro i hi hnot
        exact_mod_cast Strategy.absBound_nonneg (Tr.strat i)
    _ = (∑ i ∈ Finset.range start, (Tr.strat i).absBound : ℚ) := by
      norm_cast

lemma Exploits.gate (Tr : Trader) (P : History) (DP : DeductiveProcess)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (hEx : Tr.Exploits P DP) (start : ℕ) :
    (Tr.gate start).Exploits P DP := by
  apply hEx.of_boundedDifference
    ((∑ i ∈ Finset.range start, (Tr.strat i).absBound : ℚ) : ℝ)
  intro n v hv
  exact Tr.gate_netWorth_difference_le P hP start v n

end Trader

/-- The gated `j`th trader in the concrete redundant enumeration. -/
def firmRawTrader (j : ℕ) : Trader := (enumeratedTrader j).gate j

/-- A uniform rational bound for every prefix of every gate opened by day `n`.  Summing
all candidates and all days is intentionally redundant: it makes each individual bound
an immediate summand and remains a completely executable finite calculation. -/
def tradingFirmTotalBound (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    ∑ i ∈ Finset.range (n + 1), ((firmRawTrader j).strat i).absBound

/-- Paper cutoff `C_n`, chosen strictly above the uniform rational wealth bound. -/
def tradingFirmCutoff (n : ℕ) : ℕ :=
  ⌈tradingFirmTotalBound n⌉₊ + 1

def tradingFirmTotalBoundTradeLists (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    ∑ i ∈ Finset.range (n + 1),
      Strategy.tradeListAbsBound ((firmRawTrader j).strat i).trades

def tradingFirmCutoffTradeLists (n : ℕ) : ℕ :=
  ⌈tradingFirmTotalBoundTradeLists n⌉₊ + 1

@[simp] lemma tradingFirmTotalBoundTradeLists_eq (n : ℕ) :
    tradingFirmTotalBoundTradeLists n = tradingFirmTotalBound n := by
  rfl

@[simp] lemma tradingFirmCutoffTradeLists_eq (n : ℕ) :
    tradingFirmCutoffTradeLists n = tradingFirmCutoff n := by
  rfl

lemma tradingFirmTotalBound_nonneg (n : ℕ) : 0 ≤ tradingFirmTotalBound n := by
  unfold tradingFirmTotalBound
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro i hi
  exact Strategy.absBound_nonneg _

lemma tradingFirmTotalBound_lt_cutoff (n : ℕ) :
    tradingFirmTotalBound n < (tradingFirmCutoff n : ℚ) := by
  unfold tradingFirmCutoff
  have hceil := Nat.le_ceil (tradingFirmTotalBound n)
  exact lt_of_le_of_lt hceil
    (by exact_mod_cast Nat.lt_succ_self ⌈tradingFirmTotalBound n⌉₊)

/-- The 0-based form of the paper's weight `2^{-k-b}`: enumeration index `j`
corresponds to paper index `k=j+1`, while budgets remain positive integers. -/
def tradingFirmWeight (j b : ℕ) : ℚ :=
  1 / (2 : ℚ) ^ (j + 1 + b)

lemma tradingFirmWeight_pos (j b : ℕ) : 0 < tradingFirmWeight j b := by
  unfold tradingFirmWeight
  positivity

lemma tradingFirmWeight_cast (j b : ℕ) :
    (tradingFirmWeight j b : ℝ) = (1 / 2 : ℝ) ^ (j + 1 + b) := by
  norm_num [tradingFirmWeight, div_pow]

/-- Exact closed form of the high-budget geometric tail. -/
lemma tradingFirmWeight_tail_hasSum (j C : ℕ) :
    HasSum (fun r : ℕ => (tradingFirmWeight j (C + 1 + r) : ℝ))
      (tradingFirmWeight j C : ℝ) := by
  have hg := hasSum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have hm := hg.mul_left ((1 / 2 : ℝ) ^ (j + 1 + (C + 1)))
  convert hm using 1
  any_goals rfl
  · funext r
    rw [tradingFirmWeight_cast,
      show j + 1 + (C + 1 + r) = (j + 1 + (C + 1)) + r by omega,
      pow_add]
  · rw [tradingFirmWeight_cast,
      show j + 1 + (C + 1) = (j + 1 + C) + 1 by omega, pow_succ]
    norm_num
    ring

/-- Exact downside mass assigned to all positive budgets for enumeration index `j`. -/
lemma tradingFirmBudgetCost_hasSum (j : ℕ) :
    HasSum (fun r : ℕ =>
      (tradingFirmWeight j (r + 1) : ℝ) * (r + 1 : ℝ))
      ((1 / 2 : ℝ) ^ j) := by
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num)
  have hg := hasSum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
  have hplus := hn.add hg
  have hm := hplus.mul_left ((1 / 2 : ℝ) ^ (j + 2))
  convert hm using 1
  any_goals rfl
  · funext r
    rw [tradingFirmWeight_cast,
      show j + 1 + (r + 1) = (j + 2) + r by omega, pow_add]
    ring
  · norm_num
    rw [pow_add]
    norm_num
    ring

lemma strategyBound_le_total {j i n : ℕ} (hj : j ≤ n) (hi : i ≤ n) :
    ((firmRawTrader j).strat i).absBound ≤ tradingFirmTotalBound n := by
  have hiMem : i ∈ Finset.range (n + 1) := by simp; omega
  have hjMem : j ∈ Finset.range (n + 1) := by simp; omega
  have hinner : ((firmRawTrader j).strat i).absBound ≤
      ∑ d ∈ Finset.range (n + 1), ((firmRawTrader j).strat d).absBound :=
    Finset.single_le_sum
      (fun d _ => Strategy.absBound_nonneg ((firmRawTrader j).strat d)) hiMem
  have houter : (∑ d ∈ Finset.range (n + 1),
      ((firmRawTrader j).strat d).absBound) ≤ tradingFirmTotalBound n := by
    unfold tradingFirmTotalBound
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun d _ =>
      Strategy.absBound_nonneg ((firmRawTrader k).strat d))) hjMem
  exact hinner.trans houter

lemma firmRaw_netWorth_abs_lt_cutoff (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    {j m n : ℕ} (hj : j ≤ n) (hm : m ≤ n) (v : PCWorld) :
    |(firmRawTrader j).netWorth P v m| < (tradingFirmCutoff n : ℝ) := by
  have hw : ∀ phi, 0 ≤ v.payout phi ∧ v.payout phi ≤ 1 := by
    intro phi
    rw [PCWorld.payout]
    split <;> norm_num
  have hprefix :
      ∑ i ∈ Finset.range (m + 1), (((firmRawTrader j).strat i).absBound : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), (((firmRawTrader j).strat i).absBound : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_subset_range.mpr (by omega)
    · intro i hi hnot
      exact_mod_cast Strategy.absBound_nonneg ((firmRawTrader j).strat i)
  have hinnerRat :
      (∑ i ∈ Finset.range (n + 1), ((firmRawTrader j).strat i).absBound) ≤
        tradingFirmTotalBound n := by
    unfold tradingFirmTotalBound
    have hjMem : j ∈ Finset.range (n + 1) := by simp; omega
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun d _ =>
      Strategy.absBound_nonneg ((firmRawTrader k).strat d))) hjMem
  have hinner :
      ∑ i ∈ Finset.range (n + 1), (((firmRawTrader j).strat i).absBound : ℝ) ≤
        (tradingFirmTotalBound n : ℝ) := by
    exact_mod_cast hinnerRat
  calc
    |(firmRawTrader j).netWorth P v m| ≤
        ∑ i ∈ Finset.range (m + 1),
          |((firmRawTrader j).strat i).value P v.payout| := by
      unfold Trader.netWorth
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1),
          (((firmRawTrader j).strat i).absBound : ℝ) := by
      exact Finset.sum_le_sum (fun i _ =>
        Strategy.abs_value_le ((firmRawTrader j).strat i) P hP v.payout hw)
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          (((firmRawTrader j).strat i).absBound : ℝ) := hprefix
    _ ≤ (tradingFirmTotalBound n : ℝ) := hinner
    _ < (tradingFirmCutoff n : ℝ) := by
      exact_mod_cast tradingFirmTotalBound_lt_cutoff n

/-- The finite list of explicitly retained positive-budget components for `(j,n)`. -/
def tradingFirmBudgetComponents (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ) : List (Strategy n) :=
  (List.range (tradingFirmCutoff n)).map fun r =>
    (BudgeterAt DP (firmRawTrader j) (r + 1) Q n).scaleConst
      (tradingFirmWeight j (r + 1))

/-- One enumerated trader's exact finite day contribution: explicit budgets up through
`C_n`, followed by the closed-form geometric tail multiplying the raw gated action. -/
def tradingFirmComponentAt (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ) : Strategy n :=
  Strategy.join (tradingFirmBudgetComponents DP Q n j ++
    [((firmRawTrader j).strat n).scaleConst
      (tradingFirmWeight j (tradingFirmCutoff n))])

/-- Operational finite-stage counterpart of `tradingFirmBudgetComponents`. -/
def tradingFirmBudgetComponentsFromStages (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ) : List (Strategy n) :=
  (List.range (tradingFirmCutoff n)).map fun r =>
    (BudgeterAtFromStages D (firmRawTrader j) (r + 1) Q n).scaleConst
      (tradingFirmWeight j (r + 1))

/-- Operational finite-stage counterpart of one TradingFirm enumeration component. -/
def tradingFirmComponentAtFromStages (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ) : Strategy n :=
  Strategy.join (tradingFirmBudgetComponentsFromStages D Q n j ++
    [((firmRawTrader j).strat n).scaleConst
      (tradingFirmWeight j (tradingFirmCutoff n))])

lemma tradingFirmBudgetComponents_eq_of_eq_prefix
    (DP : DeductiveProcess) (Q R : ℕ → Sentence → ℚ) (n j : ℕ)
    (hQR : ∀ day, day < n → ∀ phi, Q day phi = R day phi) :
    tradingFirmBudgetComponents DP Q n j =
      tradingFirmBudgetComponents DP R n j := by
  unfold tradingFirmBudgetComponents
  apply List.map_congr_left
  intro r _hr
  rw [BudgeterAt_eq_of_eq_prefix DP (firmRawTrader j) (r + 1) Q R n hQR]

lemma tradingFirmComponentAt_eq_of_eq_prefix
    (DP : DeductiveProcess) (Q R : ℕ → Sentence → ℚ) (n j : ℕ)
    (hQR : ∀ day, day < n → ∀ phi, Q day phi = R day phi) :
    tradingFirmComponentAt DP Q n j = tradingFirmComponentAt DP R n j := by
  unfold tradingFirmComponentAt
  rw [tradingFirmBudgetComponents_eq_of_eq_prefix DP Q R n j hQR]

/-- `def:tradingfirm`: the finite exact day strategy corresponding to the paper's
doubly-infinite geometric mixture. -/
def TradingFirmAt (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ)
    (n : ℕ) : Strategy n :=
  Strategy.join ((List.range (n + 1)).map fun j =>
    tradingFirmComponentAt DP Q n j)

/-- Executable day action parameterized by an explicit finite-stage table. -/
def TradingFirmAtFromStages (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Strategy n :=
  Strategy.join ((List.range (n + 1)).map fun j =>
    tradingFirmComponentAtFromStages D Q n j)

/-! Fully first-order Boolean-list counterparts used by the concrete compiler. -/

def tradingFirmBudgetComponentsFromStageLists (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ) : List (Strategy n) :=
  (List.range (tradingFirmCutoff n)).map fun r =>
    (BudgeterAtFromStageLists D (firmRawTrader j) (r + 1) Q n).scaleConst
      (tradingFirmWeight j (r + 1))

def tradingFirmComponentAtFromStageLists (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ) : Strategy n :=
  Strategy.join (tradingFirmBudgetComponentsFromStageLists D Q n j ++
    [((firmRawTrader j).strat n).scaleConst
      (tradingFirmWeight j (tradingFirmCutoff n))])

def TradingFirmAtFromStageLists (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Strategy n :=
  Strategy.join ((List.range (n + 1)).map fun j =>
    tradingFirmComponentAtFromStageLists D Q n j)

def scaleConstTradeList (q : ℚ) (trades : List (EF × Sentence)) :
    List (EF × Sentence) :=
  trades.map fun p => (.mul (.const q) p.1, p.2)

def tradingFirmComponentTradesFromStageTradeLists
    (D : ℕ → Finset Sentence) (Q : ℕ → Sentence → ℚ)
    (n j : ℕ) : List (EF × Sentence) :=
  ((List.range (tradingFirmCutoffTradeLists n)).flatMap fun r =>
    scaleConstTradeList (tradingFirmWeight j (r + 1))
      (budgeterTradesFromStageTradeLists D
        (fun i => ((firmRawTrader j).strat i).trades) (r + 1) Q n)) ++
    scaleConstTradeList (tradingFirmWeight j (tradingFirmCutoffTradeLists n))
      ((firmRawTrader j).strat n).trades

def tradingFirmTradesFromStageTradeLists
    (D : ℕ → Finset Sentence) (Q : ℕ → Sentence → ℚ)
    (n : ℕ) : List (EF × Sentence) :=
  (List.range (n + 1)).flatMap fun j =>
    tradingFirmComponentTradesFromStageTradeLists D Q n j

lemma scaleConstTradeList_strategy {n : ℕ} (q : ℚ) (T : Strategy n) :
    scaleConstTradeList q T.trades = (T.scaleConst q).trades := by
  rfl

lemma tradingFirmComponentTradesFromStageTradeLists_eq
    (D : ℕ → Finset Sentence) (Q : ℕ → Sentence → ℚ)
    (n j : ℕ) :
    tradingFirmComponentTradesFromStageTradeLists D Q n j =
      (tradingFirmComponentAtFromStageLists D Q n j).trades := by
  unfold tradingFirmComponentTradesFromStageTradeLists
    tradingFirmComponentAtFromStageLists tradingFirmBudgetComponentsFromStageLists
    Strategy.join
  rw [tradingFirmCutoffTradeLists_eq]
  simp only [List.flatMap_map, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  congr 1
  · apply List.flatMap_congr
    intro r hr
    rw [budgeterTradesFromStageTradeLists_trader, scaleConstTradeList_strategy]

lemma tradingFirmTradesFromStageTradeLists_eq
    (D : ℕ → Finset Sentence) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    tradingFirmTradesFromStageTradeLists D Q n =
      (TradingFirmAtFromStageLists D Q n).trades := by
  unfold tradingFirmTradesFromStageTradeLists TradingFirmAtFromStageLists Strategy.join
  change
    List.flatMap (fun j => tradingFirmComponentTradesFromStageTradeLists D Q n j)
        (List.range (n + 1)) =
      List.flatMap Strategy.trades
        (List.map (fun j => tradingFirmComponentAtFromStageLists D Q n j)
          (List.range (n + 1)))
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro j hj
  exact tradingFirmComponentTradesFromStageTradeLists_eq D Q n j

lemma tradingFirmBudgetComponentsFromStageLists_eq
    (D : ℕ → Finset Sentence) (Q : ℕ → Sentence → ℚ) (n j : ℕ) :
    tradingFirmBudgetComponentsFromStageLists D Q n j =
      tradingFirmBudgetComponentsFromStages D Q n j := by
  unfold tradingFirmBudgetComponentsFromStageLists tradingFirmBudgetComponentsFromStages
  apply List.map_congr_left
  intro r hr
  rw [BudgeterAtFromStageLists_eq]

lemma tradingFirmComponentAtFromStageLists_eq
    (D : ℕ → Finset Sentence) (Q : ℕ → Sentence → ℚ) (n j : ℕ) :
    tradingFirmComponentAtFromStageLists D Q n j =
      tradingFirmComponentAtFromStages D Q n j := by
  unfold tradingFirmComponentAtFromStageLists tradingFirmComponentAtFromStages
  rw [tradingFirmBudgetComponentsFromStageLists_eq]

lemma TradingFirmAtFromStageLists_eq (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    TradingFirmAtFromStageLists D Q n = TradingFirmAtFromStages D Q n := by
  unfold TradingFirmAtFromStageLists TradingFirmAtFromStages
  congr 1
  apply List.map_congr_left
  intro j hj
  exact tradingFirmComponentAtFromStageLists_eq D Q n j

lemma tradingFirmBudgetComponentsFromStages_eq_of_eq_prefix
    (DP : DeductiveProcess) (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    tradingFirmBudgetComponentsFromStages D Q n j =
      tradingFirmBudgetComponents DP Q n j := by
  unfold tradingFirmBudgetComponentsFromStages tradingFirmBudgetComponents
  apply List.map_congr_left
  intro r _hr
  rw [BudgeterAtFromStages_eq_of_eq_prefix DP D (firmRawTrader j)
    (r + 1) Q n hD]

lemma tradingFirmComponentAtFromStages_eq_of_eq_prefix
    (DP : DeductiveProcess) (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    tradingFirmComponentAtFromStages D Q n j =
      tradingFirmComponentAt DP Q n j := by
  unfold tradingFirmComponentAtFromStages tradingFirmComponentAt
  rw [tradingFirmBudgetComponentsFromStages_eq_of_eq_prefix DP D Q n j hD]

lemma TradingFirmAtFromStages_eq_of_eq_prefix
    (DP : DeductiveProcess) (D : ℕ → Finset Sentence)
    (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    TradingFirmAtFromStages D Q n = TradingFirmAt DP Q n := by
  unfold TradingFirmAtFromStages TradingFirmAt
  congr 1
  apply List.map_congr_left
  intro j _hj
  exact tradingFirmComponentAtFromStages_eq_of_eq_prefix DP D Q n j hD

lemma TradingFirmAt_eq_of_eq_prefix
    (DP : DeductiveProcess) (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ phi, Q day phi = R day phi) :
    TradingFirmAt DP Q n = TradingFirmAt DP R n := by
  unfold TradingFirmAt
  congr 1
  apply List.map_congr_left
  intro j _hj
  exact tradingFirmComponentAt_eq_of_eq_prefix DP Q R n j hQR

/-- Adaptive form consumed by the recursive LIA construction. -/
def TradingFirm (DP : DeductiveProcess) : AdaptiveTrader where
  action n past := TradingFirmAt DP (rationalHistory past) n

/-- Static realization against a supplied complete rational market table. -/
def tradingFirmTrader (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) : Trader where
  strat n := TradingFirmAt DP Q n

/-- One gated enumeration index's contribution to the realized firm. -/
def tradingFirmComponentTrader (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (j : ℕ) : Trader where
  strat n := if j ≤ n then tradingFirmComponentAt DP Q n j else Trader.zero.strat n

lemma TradingFirmAt_value_eq_sum (DP : DeductiveProcess)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) (P : History) (w : Sentence → ℝ) :
    (TradingFirmAt DP Q n).value P w =
      ∑ j ∈ Finset.range (n + 1),
        (tradingFirmComponentAt DP Q n j).value P w := by
  rw [TradingFirmAt, Strategy.join_value]
  simp only [List.map_map, Function.comp_def]
  congr 1

lemma tradingFirmTrader_netWorth_eq_component_sum
    (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ)
    (P : History) (v : PCWorld) (n : ℕ) :
    (tradingFirmTrader DP Q).netWorth P v n =
      ∑ j ∈ Finset.range (n + 1),
        (tradingFirmComponentTrader DP Q j).netWorth P v n := by
  unfold Trader.netWorth
  change (∑ d ∈ Finset.range (n + 1),
      (TradingFirmAt DP Q d).value P v.payout) = _
  simp_rw [TradingFirmAt_value_eq_sum]
  calc
    (∑ d ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (d + 1),
        (tradingFirmComponentAt DP Q d j).value P v.payout) =
        ∑ d ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          if j ≤ d then (tradingFirmComponentAt DP Q d j).value P v.payout else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdn : d ≤ n := by simp only [Finset.mem_range] at hd; omega
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro j hj
        simp only [Finset.mem_filter] at hj
        simp
    _ = ∑ j ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1),
          if j ≤ d then (tradingFirmComponentAt DP Q d j).value P v.payout else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (n + 1),
        (tradingFirmComponentTrader DP Q j).netWorth P v n := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold Trader.netWorth
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hjd : j ≤ d
      · simp [tradingFirmComponentTrader, hjd]
      · simp [tradingFirmComponentTrader, hjd, Trader.zero, Strategy.value]

/-- Above the uniform cutoff, every budgeted component is exactly its raw gated action,
uniformly over the still-variable current price vector.  This is the key fact justifying
the closed-form tail in `tradingFirmComponentAt`. -/
lemma BudgeterAt_firmRaw_value_eq_of_cutoff
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ) (n j b : ℕ)
    (hQ : ∀ day, day < n → ∀ phi, P day phi = (Q day phi : ℝ))
    (hj : j ≤ n) (hb : tradingFirmCutoff n < b)
    (w : Sentence → ℝ) :
    (BudgeterAt DP (firmRawTrader j) b Q n).value P w =
      ((firmRawTrader j).strat n).value P w := by
  apply BudgeterAt_value_eq_of_safe_prefix DP (firmRawTrader j) b (by omega)
    P Q n hQ
  intro m hm v hv
  have habs := firmRaw_netWorth_abs_lt_cutoff P hP hj hm v
  have hbR : (tradingFirmCutoff n : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hlow := neg_abs_le ((firmRawTrader j).netWorth P v m)
  linarith

lemma firmRaw_netWorth_eq_zero_of_lt (P : History) (v : PCWorld)
    {j m : ℕ} (hmj : m < j) :
    (firmRawTrader j).netWorth P v m = 0 := by
  unfold Trader.netWorth
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i < j := by
    simp only [Finset.mem_range] at hi
    omega
  rw [firmRawTrader, Trader.gate_strat_of_lt (enumeratedTrader j) hij]
  simp [Trader.zero, Strategy.value]

/-- Before gate `j` opens, every one of its budgeted components has zero value. -/
lemma BudgeterAt_firmRaw_value_eq_zero_of_lt
    (DP : DeductiveProcess) (P : History) (Q : ℕ → Sentence → ℚ)
    (n j b : ℕ) (hb : 0 < b) (hnj : n < j)
    (hQ : ∀ day, day < n → ∀ phi, P day phi = (Q day phi : ℝ))
    (w : Sentence → ℝ) :
    (BudgeterAt DP (firmRawTrader j) b Q n).value P w = 0 := by
  rw [BudgeterAt_value_eq_of_safe_prefix DP (firmRawTrader j) b hb P Q n hQ]
  · rw [firmRawTrader, Trader.gate_strat_of_lt (enumeratedTrader j) hnj]
    simp [Trader.zero, Strategy.value]
  · intro m hm v hv
    rw [firmRaw_netWorth_eq_zero_of_lt P v (by omega)]
    exact_mod_cast (neg_neg_of_pos (by exact_mod_cast hb) : -(b : ℝ) < 0)

/-- For one open enumeration index, the finite component has exactly the value of the
paper's infinite sum over all positive budgets. -/
lemma tradingFirmComponentAt_value_hasSum
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ) (n j : ℕ)
    (hQ : ∀ day, day < n → ∀ phi, P day phi = (Q day phi : ℝ))
    (hj : j ≤ n) (w : Sentence → ℝ) :
    HasSum (fun r : ℕ =>
      (tradingFirmWeight j (r + 1) : ℝ) *
        (BudgeterAt DP (firmRawTrader j) (r + 1) Q n).value P w)
      ((tradingFirmComponentAt DP Q n j).value P w) := by
  let C := tradingFirmCutoff n
  let raw := ((firmRawTrader j).strat n).value P w
  have hweights := tradingFirmWeight_tail_hasSum j C
  have hraw : HasSum (fun r : ℕ =>
      (tradingFirmWeight j (C + 1 + r) : ℝ) * raw)
      ((tradingFirmWeight j C : ℝ) * raw) := by
    convert hweights.mul_left raw using 1 <;> first | rfl | simp [mul_comm]
  have hbudget : HasSum (fun r : ℕ =>
      (tradingFirmWeight j (C + 1 + r) : ℝ) *
        (BudgeterAt DP (firmRawTrader j) (C + 1 + r) Q n).value P w)
      ((tradingFirmWeight j C : ℝ) * raw) := by
    convert hraw using 1
    funext r
    rw [BudgeterAt_firmRaw_value_eq_of_cutoff DP P hP Q n j (C + 1 + r)
      hQ hj (by dsimp [C]; omega) w]
  let f : ℕ → ℝ := fun r =>
    (tradingFirmWeight j (r + 1) : ℝ) *
      (BudgeterAt DP (firmRawTrader j) (r + 1) Q n).value P w
  have htail : HasSum (fun r => f (r + C))
      ((tradingFirmWeight j C : ℝ) * raw) := by
    first
      | exact hbudget
      | simpa only [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbudget
  have hfull := (hasSum_nat_add_iff C).mp htail
  convert hfull using 1
  any_goals rfl
  simp only [tradingFirmComponentAt, Strategy.join_value,
    tradingFirmBudgetComponents, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, Strategy.scaleConst_value, List.map_singleton,
    List.sum_cons, List.sum_nil, add_zero, f, raw, C]
  rw [add_comm]
  change (tradingFirmWeight j C : ℝ) * raw + ((List.range C).map f).sum =
    (tradingFirmWeight j C : ℝ) * raw + ∑ x ∈ Finset.range C, f x
  congr 1

/-- Net-worth form of the exact component identity.  The finite time sum commutes with
the absolutely geometric budget series via `hasSum_sum`. -/
lemma tradingFirmComponentTrader_netWorth_hasSum
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (j n : ℕ) (v : PCWorld) :
    HasSum (fun r : ℕ =>
      (tradingFirmWeight j (r + 1) : ℝ) *
        (budgetedTrader DP (firmRawTrader j) (r + 1) Q).netWorth P v n)
      ((tradingFirmComponentTrader DP Q j).netWorth P v n) := by
  have hday : ∀ d ∈ Finset.range (n + 1), HasSum (fun r : ℕ =>
      (tradingFirmWeight j (r + 1) : ℝ) *
        (BudgeterAt DP (firmRawTrader j) (r + 1) Q d).value P v.payout)
      (((tradingFirmComponentTrader DP Q j).strat d).value P v.payout) := by
    intro d hd
    by_cases hjd : j ≤ d
    · simpa [tradingFirmComponentTrader, hjd] using
        tradingFirmComponentAt_value_hasSum DP P hP Q d j
          (fun day hday phi => hQ day phi) hjd v.payout
    · have hdj : d < j := Nat.lt_of_not_ge hjd
      have hz : ∀ r : ℕ,
          (BudgeterAt DP (firmRawTrader j) (r + 1) Q d).value P v.payout = 0 := by
        intro r
        exact BudgeterAt_firmRaw_value_eq_zero_of_lt DP P Q d j (r + 1)
          (by omega) hdj (fun day hday phi => hQ day phi) v.payout
      convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
      · funext r
        rw [hz r]
        simp
      · simp [tradingFirmComponentTrader, hjd, Trader.zero, Strategy.value]
  have hs := hasSum_sum hday
  convert hs using 1
  any_goals rfl
  · funext r
    unfold Trader.netWorth budgetedTrader
    rw [Finset.mul_sum]

/-- Each fixed enumerated-trader component has downside at most its total geometric
budget mass `2^{-j}`. -/
lemma tradingFirmComponentTrader_netWorth_floor
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (j n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    -((1 / 2 : ℝ) ^ j) ≤
      (tradingFirmComponentTrader DP Q j).netWorth P v n := by
  have hactual := tradingFirmComponentTrader_netWorth_hasSum DP P hP Q hQ j n v
  have hcost := tradingFirmBudgetCost_hasSum j
  have hnonneg : ∀ r : ℕ, 0 ≤
      (tradingFirmWeight j (r + 1) : ℝ) *
          (budgetedTrader DP (firmRawTrader j) (r + 1) Q).netWorth P v n +
        (tradingFirmWeight j (r + 1) : ℝ) * (r + 1 : ℝ) := by
    intro r
    have hfloor := budgetedTrader_netWorth_floor DP (firmRawTrader j) (r + 1)
      (by omega) P Q hQ n v hv
    have hw0 : 0 ≤ (tradingFirmWeight j (r + 1) : ℝ) := by
      exact_mod_cast (tradingFirmWeight_pos j (r + 1)).le
    have hm := mul_le_mul_of_nonneg_left hfloor hw0
    push_cast at hm
    calc
      0 = (tradingFirmWeight j (r + 1) : ℝ) * (-(r + 1 : ℝ)) +
          (tradingFirmWeight j (r + 1) : ℝ) * (r + 1 : ℝ) := by ring
      _ ≤ (tradingFirmWeight j (r + 1) : ℝ) *
          (budgetedTrader DP (firmRawTrader j) (r + 1) Q).netWorth P v n +
          (tradingFirmWeight j (r + 1) : ℝ) * (r + 1 : ℝ) :=
        add_le_add hm le_rfl
  have hsum0 := (hactual.add hcost).nonneg hnonneg
  linarith

lemma finite_half_pow_sum_lt_two (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j) < 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  norm_num
  have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  linarith

/-- The whole firm has the paper's uniform downside bound `-2`. -/
lemma tradingFirmTrader_netWorth_floor
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    -2 ≤ (tradingFirmTrader DP Q).netWorth P v n := by
  rw [tradingFirmTrader_netWorth_eq_component_sum]
  have hsum := finite_half_pow_sum_lt_two n
  calc
    (-2 : ℝ) ≤ -(∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j) := by
      linarith
    _ = ∑ j ∈ Finset.range (n + 1), -((1 / 2 : ℝ) ^ j) := by
      rw [Finset.sum_neg_distrib]
    _ ≤ ∑ j ∈ Finset.range (n + 1),
        (tradingFirmComponentTrader DP Q j).netWorth P v n := by
      exact Finset.sum_le_sum (fun j _ =>
        tradingFirmComponentTrader_netWorth_floor DP P hP Q hQ j n v hv)

/-- Removing any one positive-budget component leaves the corresponding enumerated
component with the same coarse geometric floor. -/
lemma tradingFirmComponentTrader_residual_floor
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (j r n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    -((1 / 2 : ℝ) ^ j) ≤
      (tradingFirmComponentTrader DP Q j).netWorth P v n -
        (tradingFirmWeight j (r + 1) : ℝ) *
          (budgetedTrader DP (firmRawTrader j) (r + 1) Q).netWorth P v n := by
  let actual : ℕ → ℝ := fun s =>
    (tradingFirmWeight j (s + 1) : ℝ) *
      (budgetedTrader DP (firmRawTrader j) (s + 1) Q).netWorth P v n
  let cost : ℕ → ℝ := fun s =>
    (tradingFirmWeight j (s + 1) : ℝ) * (s + 1 : ℝ)
  have ha : HasSum actual ((tradingFirmComponentTrader DP Q j).netWorth P v n) :=
    tradingFirmComponentTrader_netWorth_hasSum DP P hP Q hQ j n v
  have hc : HasSum cost ((1 / 2 : ℝ) ^ j) := tradingFirmBudgetCost_hasSum j
  have har := ha.update r 0
  have hcr := hc.update r 0
  have hnonneg : ∀ s, 0 ≤ Function.update actual r 0 s +
      Function.update cost r 0 s := by
    intro s
    by_cases hsr : s = r
    · subst s
      simp
    · simp only [Function.update, hsr]
      have hfloor := budgetedTrader_netWorth_floor DP (firmRawTrader j) (s + 1)
        (by omega) P Q hQ n v hv
      have hw0 : 0 ≤ (tradingFirmWeight j (s + 1) : ℝ) := by
        exact_mod_cast (tradingFirmWeight_pos j (s + 1)).le
      have hm := mul_le_mul_of_nonneg_left hfloor hw0
      push_cast at hm
      dsimp [actual, cost]
      calc
        0 = (tradingFirmWeight j (s + 1) : ℝ) * (-(s + 1 : ℝ)) +
            (tradingFirmWeight j (s + 1) : ℝ) * (s + 1 : ℝ) := by ring
        _ ≤ _ := add_le_add hm le_rfl
  have hsum0 := (har.add hcr).nonneg hnonneg
  have hcost0 : 0 ≤ cost r := by
    dsimp [cost]
    apply mul_nonneg
    · exact_mod_cast (tradingFirmWeight_pos j (r + 1)).le
    · positivity
  dsimp [actual, cost] at hsum0 ⊢
  linarith

lemma budgetedFirmRaw_netWorth_eq_zero_of_lt
    (DP : DeductiveProcess) (P : History)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (j b n : ℕ) (hb : 0 < b) (hnj : n < j) (v : PCWorld) :
    (budgetedTrader DP (firmRawTrader j) b Q).netWorth P v n = 0 := by
  unfold Trader.netWorth budgetedTrader
  apply Finset.sum_eq_zero
  intro d hd
  have hdj : d < j := by simp only [Finset.mem_range] at hd; omega
  exact BudgeterAt_firmRaw_value_eq_zero_of_lt DP P Q d j b hb hdj
    (fun day hday phi => hQ day phi) v.payout

/-- Uniform downside of the firm after removing any one weighted positive-budget
component.  This is the quantitative engine of Trading Firm Dominance. -/
lemma tradingFirmTrader_residual_floor
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (j r n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    -2 ≤ (tradingFirmTrader DP Q).netWorth P v n -
      (tradingFirmWeight j (r + 1) : ℝ) *
        (budgetedTrader DP (firmRawTrader j) (r + 1) Q).netWorth P v n := by
  by_cases hjn : j ≤ n
  · rw [tradingFirmTrader_netWorth_eq_component_sum]
    let S := Finset.range (n + 1)
    let component : ℕ → ℝ := fun k =>
      (tradingFirmComponentTrader DP Q k).netWorth P v n
    have hjS : j ∈ S := by simp [S]; omega
    have htarget := tradingFirmComponentTrader_residual_floor
      DP P hP Q hQ j r n v hv
    have hrest : ∑ k ∈ S.erase j, -((1 / 2 : ℝ) ^ k) ≤
        ∑ k ∈ S.erase j, component k := by
      exact Finset.sum_le_sum (fun k hk =>
        tradingFirmComponentTrader_netWorth_floor DP P hP Q hQ k n v hv)
    have hsplit := Finset.sum_erase_add S component hjS
    have hpowsplit := Finset.sum_erase_add S (fun k => (1 / 2 : ℝ) ^ k) hjS
    have hsum := finite_half_pow_sum_lt_two n
    dsimp [S, component] at hsplit hpowsplit hrest ⊢
    rw [← hsplit]
    rw [Finset.sum_neg_distrib] at hrest
    linarith
  · have hnj : n < j := Nat.lt_of_not_ge hjn
    rw [budgetedFirmRaw_netWorth_eq_zero_of_lt DP P Q hQ j (r + 1) n
      (by omega) hnj v, mul_zero, sub_zero]
    exact tradingFirmTrader_netWorth_floor DP P hP Q hQ n v hv

/-- **Trading Firm Dominance, covered-index core** (`lem:tfdom`).  On any rational
`[0,1]` market, if a trader *occurring in the enumeration* exploits the market, the
concrete finite TradingFirm also exploits it.  The proof selects the trader's enumerated
gate and one exploiting Budgeter, then uses the residual `-2` bound above.  The dominance
theorem below is an instance of this via the coverage clause. -/
theorem trading_firm_dominance_of_covered
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (Tr : Trader) (hcov : ∃ j : ℕ, enumeratedTrader j = Tr)
    (hEx : Tr.Exploits P DP) :
    (tradingFirmTrader DP Q).Exploits P DP := by
  obtain ⟨j, hj⟩ := hcov
  have hraw : (firmRawTrader j).Exploits P DP := by
    unfold firmRawTrader
    rw [hj]
    exact Trader.Exploits.gate Tr P DP hP hEx j
  obtain ⟨b, hb, hbudget⟩ :=
    exists_budgetedTrader_exploits DP (firmRawTrader j) P Q hQ hraw
  let r := b - 1
  have hr : r + 1 = b := by dsimp [r]; omega
  have hweight : 0 < (tradingFirmWeight j b : ℝ) := by
    exact_mod_cast tradingFirmWeight_pos j b
  refine ⟨⟨-2, ?_⟩, ?_⟩
  · rintro x ⟨n, v, hv, rfl⟩
    exact tradingFirmTrader_netWorth_floor DP P hP Q hQ n v hv
  · intro hUpper
    apply hbudget.2
    rcases hUpper with ⟨U, hU⟩
    refine ⟨(U + 2) / (tradingFirmWeight j b : ℝ), ?_⟩
    rintro x ⟨n, v, hv, rfl⟩
    have hfirm := hU ⟨n, v, hv, rfl⟩
    have hres := tradingFirmTrader_residual_floor DP P hP Q hQ j r n v hv
    rw [hr] at hres
    apply (le_div_iff₀ hweight).2
    linarith

/-- **Trading Firm Dominance** (`lem:tfdom`): an exploiting machine-efficient trader makes
the firm exploit — the enumeration covers the whole class.

The class is `MachineEfficientTrader`: ordinary machine polynomial time, through
`Complexity.FP`. Every trader the fuel calculus certifies is one of these
(`EfficientlyComputable.toMachine`), so the fuel-certified corollary is immediate; it is
stated as `trading_firm_dominance_of_ec`, immediately below.
Paper node: `lem:tfdom` -/
theorem trading_firm_dominance
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (Tr : Trader) (hTr : MachineEfficientTrader Tr)
    (hEx : Tr.Exploits P DP) :
    (tradingFirmTrader DP Q).Exploits P DP :=
  trading_firm_dominance_of_covered DP P hP Q hQ Tr
    (exists_enumeratedTrader_eq Tr hTr) hEx

/-- The fuel-certified corollary of Trading Firm Dominance. The primary statement is
`trading_firm_dominance`, over the machine class; this is the instance the fuel calculus's
certificates feed.
Paper node: `lem:tfdom` -/
theorem trading_firm_dominance_of_ec
    (DP : DeductiveProcess) (P : History)
    (hP : ∀ day phi, 0 ≤ P day phi ∧ P day phi ≤ 1)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day phi, P day phi = (Q day phi : ℝ))
    (Tr : Trader) (hTr : EfficientlyComputable Tr)
    (hEx : Tr.Exploits P DP) :
    (tradingFirmTrader DP Q).Exploits P DP :=
  trading_firm_dominance DP P hP Q hQ Tr hTr.toMachine hEx

#print axioms tradingFirmWeight_tail_hasSum
#print axioms tradingFirmComponentAt_value_hasSum
#print axioms tradingFirmTrader_residual_floor
#print axioms trading_firm_dominance

end LogicalInduction
