/-
# Budgeter (`def:budgeter`, `lem:budgeter`)

The paper's Budgeter is an adaptive strategy constructor: on day `n` it receives the
already-fixed rational market prefix, may branch on losses in that prefix, and returns an
ordinary `n`-strategy whose dependence on the as-yet-unknown current prices remains an
expressible feature.  This is deliberately distinct from a static `Trader`; the distinction
is load-bearing because the bankruptcy test is discontinuous in past prices.
-/
import LogicalInduction.Construction.MarketMaker
import LogicalInduction.Construction.MachineTraderEnumeration
import LogicalInduction.Framework.ROI

namespace LogicalInduction

open Classical

namespace Sentence

/-- The finite set of prime atoms occurring in a propositional sentence. -/
def atoms : Sentence → Finset ℕ
  | .atom a => {a}
  | .falsum => ∅
  | .and φ ψ => atoms φ ∪ atoms ψ
  | .or φ ψ => atoms φ ∪ atoms ψ
  | .imp φ ψ => atoms φ ∪ atoms ψ

end Sentence

/-- Executable Boolean evaluation of a sentence. -/
def sentenceBool (u : ℕ → Bool) : Sentence → Bool
  | .atom a => u a
  | .falsum => false
  | .and φ ψ => sentenceBool u φ && sentenceBool u ψ
  | .or φ ψ => sentenceBool u φ || sentenceBool u ψ
  | .imp φ ψ => !(sentenceBool u φ) || sentenceBool u ψ

/-- Regard a Boolean atom table as a propositionally consistent world. -/
def boolPCWorld (u : ℕ → Bool) : PCWorld := fun a => u a = true

lemma sentenceBool_eq_true_iff (u : ℕ → Bool) (φ : Sentence) :
    sentenceBool u φ = true ↔ (boolPCWorld u).Holds φ := by
  induction φ with
  | atom a => rfl
  | falsum => simp [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | and φ ψ ihφ ihψ =>
      simp [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      cases hφ : sentenceBool u φ <;> cases hψ : sentenceBool u ψ <;>
        simp_all [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

lemma sentenceBool_congr_of_atoms {u v : ℕ → Bool} {φ : Sentence}
    (h : ∀ a ∈ φ.atoms, u a = v a) : sentenceBool u φ = sentenceBool v φ := by
  induction φ with
  | atom a => exact h a (by simp [Sentence.atoms])
  | falsum => rfl
  | and φ ψ ihφ ihψ =>
      simp only [sentenceBool]
      rw [ihφ (fun a ha => h a (by simp [Sentence.atoms, ha])),
        ihψ (fun a ha => h a (by simp [Sentence.atoms, ha]))]
  | or φ ψ ihφ ihψ =>
      simp only [sentenceBool]
      rw [ihφ (fun a ha => h a (by simp [Sentence.atoms, ha])),
        ihψ (fun a ha => h a (by simp [Sentence.atoms, ha]))]
  | imp φ ψ ihφ ihψ =>
      simp only [sentenceBool]
      rw [ihφ (fun a ha => h a (by simp [Sentence.atoms, ha])),
        ihψ (fun a ha => h a (by simp [Sentence.atoms, ha]))]

namespace Strategy

/-- All atoms occurring in the traded sentences of a strategy. -/
def sentenceAtoms {n : ℕ} (T : Strategy n) : Finset ℕ :=
  T.support.biUnion Sentence.atoms

end Strategy

/-- The finite atom context sufficient to evaluate the deductive stage and every raw trade
through day `n`. -/
def budgetAtoms (DP : DeductiveProcess) (Tr : Trader) (n : ℕ) : Finset ℕ :=
  (DP.D n).biUnion Sentence.atoms ∪
    (Finset.range (n + 1)).biUnion fun i => (Tr.strat i).sentenceAtoms

lemma deductive_atoms_subset_budgetAtoms (DP : DeductiveProcess) (Tr : Trader)
    {m n : ℕ} (hmn : m ≤ n) {φ : Sentence} (hφ : φ ∈ DP.D m) :
    φ.atoms ⊆ budgetAtoms DP Tr n := by
  intro a ha
  unfold budgetAtoms
  apply Finset.mem_union_left
  apply Finset.mem_biUnion.mpr
  exact ⟨φ, DP.mono_le hmn hφ, ha⟩

lemma trade_atoms_subset_budgetAtoms (DP : DeductiveProcess) (Tr : Trader)
    {i n : ℕ} (hin : i ≤ n) {p : EF × Sentence} (hp : p ∈ (Tr.strat i).trades) :
    p.2.atoms ⊆ budgetAtoms DP Tr n := by
  intro a ha
  unfold budgetAtoms
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨i, by simp; omega, ?_⟩
  unfold Strategy.sentenceAtoms
  apply Finset.mem_biUnion.mpr
  exact ⟨p.2, (Tr.strat i).snd_mem_support hp, ha⟩

/-- Extend a finite bit assignment by `false` outside its atom context. -/
def finiteAtomTable (A : Finset ℕ) (bits : A → Bool) : ℕ → Bool := fun a =>
  if h : a ∈ A then bits ⟨a, h⟩ else false

/-- Every world has a representative finite bit assignment that agrees on `A`. -/
lemma exists_finiteAtomTable_agrees (A : Finset ℕ) (v : PCWorld) :
    ∃ bits : A → Bool, ∀ a ∈ A, finiteAtomTable A bits a = decide (v a) := by
  let bits : A → Bool := fun a => decide (v a.1)
  refine ⟨bits, ?_⟩
  intro a ha
  simp [finiteAtomTable, ha, bits]

/-- Interpret a bit list against the sorted atoms of `A`. -/
def atomAssignmentOfList (A : Finset ℕ) (xs : List Bool) : A → Bool := fun a =>
  xs.getD ((A.sort (· ≤ ·)).idxOf a.1) false

/-- The explicit executable finite enumeration used by Budgeter. -/
def finiteAtomAssignments (A : Finset ℕ) : List (A → Bool) :=
  (allBoolLists A.card).map (atomAssignmentOfList A)

/-! A first-order presentation of the same finite assignments.  Keeping the bit vector as
data avoids placing the value-dependent function type `A → Bool` at the compiler boundary. -/

def finiteAtomTableFromList (A : Finset ℕ) (xs : List Bool) : ℕ → Bool := fun a =>
  if a ∈ A then xs.getD ((A.sort (· ≤ ·)).idxOf a) false else false

lemma finiteAtomTable_atomAssignmentOfList (A : Finset ℕ) (xs : List Bool) :
    finiteAtomTable A (atomAssignmentOfList A xs) = finiteAtomTableFromList A xs := by
  funext a
  by_cases ha : a ∈ A
  · simp [finiteAtomTable, finiteAtomTableFromList, atomAssignmentOfList, ha]
  · simp [finiteAtomTable, finiteAtomTableFromList, ha]

lemma exists_mem_finiteAtomAssignments_agrees (A : Finset ℕ) (bits : A → Bool) :
    ∃ bits' ∈ finiteAtomAssignments A, bits' = bits := by
  let s := A.sort (· ≤ ·)
  let xs := s.map fun a => if h : a ∈ A then bits ⟨a, h⟩ else false
  have hlen : xs.length = A.card := by simp [xs, s]
  have hmem : xs ∈ allBoolLists A.card := mem_allBoolLists_iff.mpr hlen
  refine ⟨atomAssignmentOfList A xs, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨xs, hmem, rfl⟩
  · funext a
    unfold atomAssignmentOfList
    have haS : a.1 ∈ A.sort (· ≤ ·) := by simp
    have hidx : (A.sort (· ≤ ·)).idxOf a.1 < (A.sort (· ≤ ·)).length :=
      List.idxOf_lt_length_of_mem haS
    have hidx' : (A.sort (· ≤ ·)).idxOf a.1 < xs.length := by
      simpa [xs, s] using hidx
    rw [List.getD_eq_getElem xs false hidx']
    simp only [xs, s, List.getElem_map]
    rw [List.getElem_idxOf hidx]
    simp [a.2]

/-- Restrict an arbitrary p.c. world to a finite Boolean assignment. -/
noncomputable def restrictedAssignment (A : Finset ℕ) (v : PCWorld) : A → Bool :=
  fun a => decide (v a.1)

lemma restrictedAssignment_mem (A : Finset ℕ) (v : PCWorld) :
    restrictedAssignment A v ∈ finiteAtomAssignments A := by
  obtain ⟨bits, hbits, heq⟩ :=
    exists_mem_finiteAtomAssignments_agrees A (restrictedAssignment A v)
  simpa [heq] using hbits

lemma finiteAtomTable_restricted (A : Finset ℕ) (v : PCWorld) {a : ℕ}
    (ha : a ∈ A) :
    finiteAtomTable A (restrictedAssignment A v) a = decide (v a) := by
  simp [finiteAtomTable, restrictedAssignment, ha]

lemma sentenceBool_decide_world (v : PCWorld) (φ : Sentence) :
    sentenceBool (fun a => decide (v a)) φ = true ↔ v.Holds φ := by
  induction φ with
  | atom a => simp [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | falsum => simp [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]
  | and φ ψ ihφ ihψ =>
      simp [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val, ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      cases hφ : sentenceBool (fun a => decide (v a)) φ <;>
        cases hψ : sentenceBool (fun a => decide (v a)) ψ <;>
        simp_all [sentenceBool, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

lemma sentenceBool_restricted_world (A : Finset ℕ) (v : PCWorld) (φ : Sentence)
    (hφ : φ.atoms ⊆ A) :
    sentenceBool (finiteAtomTable A (restrictedAssignment A v)) φ = true ↔ v.Holds φ := by
  have heq := sentenceBool_congr_of_atoms
    (u := finiteAtomTable A (restrictedAssignment A v))
    (v := fun a => decide (v a)) (φ := φ)
    (fun a ha => finiteAtomTable_restricted A v (hφ ha))
  rw [heq]
  exact sentenceBool_decide_world v φ

lemma restricted_payout_eq (A : Finset ℕ) (v : PCWorld) (φ : Sentence)
    (hφ : φ.atoms ⊆ A) :
    (boolPCWorld (finiteAtomTable A (restrictedAssignment A v))).payout φ = v.payout φ := by
  have hholds :
      (boolPCWorld (finiteAtomTable A (restrictedAssignment A v))).Holds φ ↔ v.Holds φ :=
    (sentenceBool_eq_true_iff _ φ).symm.trans (sentenceBool_restricted_world A v φ hφ)
  unfold PCWorld.payout
  by_cases hv : v.Holds φ <;> simp_all

/-- Rational payout table induced by a Boolean atom valuation. -/
def boolPayoutRat (u : ℕ → Bool) (φ : Sentence) : ℚ :=
  if sentenceBool u φ then 1 else 0

lemma boolPCWorld_payout_eq (u : ℕ → Bool) (φ : Sentence) :
    (boolPCWorld u).payout φ = (boolPayoutRat u φ : ℝ) := by
  rw [PCWorld.payout]
  by_cases h : sentenceBool u φ = true
  · simp [boolPayoutRat, h, (sentenceBool_eq_true_iff u φ).mp h]
  · have hw : ¬(boolPCWorld u).Holds φ := by
      exact fun hv => h ((sentenceBool_eq_true_iff u φ).mpr hv)
    cases hs : sentenceBool u φ <;> simp_all [boolPayoutRat]

/-- Decidable finite consistency test for one Boolean atom table. -/
def tableConsistent (u : ℕ → Bool) (D : Finset Sentence) : Bool :=
  decide (∀ φ ∈ D, sentenceBool u φ = true)

lemma tableConsistent_eq_true_iff (u : ℕ → Bool) (D : Finset Sentence) :
    tableConsistent u D = true ↔ (boolPCWorld u).ConsistentWith D := by
  simp only [tableConsistent, decide_eq_true_eq, PCWorld.ConsistentWith]
  constructor
  · intro h φ hφ
    exact (sentenceBool_eq_true_iff u φ).mp (h φ hφ)
  · intro h φ hφ
    exact (sentenceBool_eq_true_iff u φ).mpr (h φ hφ)

namespace EF

/-- Additive inverse inside the expressible-feature DSL. -/
def neg (e : EF) : EF := .mul (.const (-1)) e

/-- Minimum expressed using the paper's allowed `max` and multiplication by `-1`. -/
def min (a b : EF) : EF := neg (.max (neg a) (neg b))

@[simp] lemma rank_neg (e : EF) : e.neg.rank = e.rank := by
  simp [neg, EF.rank]

@[simp] lemma rank_min (a b : EF) :
    (min a b).rank = Nat.max a.rank b.rank := by
  simp [min, neg, EF.rank]

lemma denote_neg (e : EF) (P : History) : e.neg.denote P = -e.denote P := by
  simp [neg]

lemma denote_min (a b : EF) (P : History) :
    (min a b).denote P = Min.min (a.denote P) (b.denote P) := by
  simp only [min, denote_neg, denote_max]
  rcases le_total (a.denote P) (b.denote P) with h | h
  · rw [min_eq_left h, max_eq_left (neg_le_neg h)]
    simp
  · rw [min_eq_right h, max_eq_right (neg_le_neg h)]
    simp

/-- Finite infimum, with the neutral fallback `1` used only when there is no plausible
world (in which case the relevant floor theorem is vacuous). -/
def listMin : List EF → EF := List.foldr min (.const 1)

lemma listMin_rank_le (es : List EF) (n : ℕ)
    (h : ∀ e ∈ es, e.rank ≤ n) : (listMin es).rank ≤ n := by
  induction es with
  | nil => simp [listMin]
  | cons e es ih =>
      simp only [listMin, List.foldr_cons, rank_min]
      exact Nat.max_le.mpr ⟨h e (by simp), ih (fun x hx => h x (by simp [hx]))⟩

lemma listMin_denote_le_of_mem (es : List EF) {e : EF} (he : e ∈ es) (P : History) :
    (listMin es).denote P ≤ e.denote P := by
  induction es with
  | nil => simp at he
  | cons x xs ih =>
      simp only [listMin, List.foldr_cons, denote_min]
      rcases List.mem_cons.mp he with rfl | he
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih he)

lemma listMin_denote_eq_one (es : List EF) (P : History)
    (h : ∀ e ∈ es, e.denote P = 1) : (listMin es).denote P = 1 := by
  induction es with
  | nil => simp [listMin]
  | cons e es ih =>
      simp only [listMin, List.foldr_cons, denote_min]
      change Min.min (e.denote P) ((listMin es).denote P) = 1
      rw [h e (by simp), ih (fun x hx => h x (by simp [hx]))]
      simp

lemma listMin_denote_pos (es : List EF) (P : History)
    (h : ∀ e ∈ es, 0 < e.denote P) : 0 < (listMin es).denote P := by
  induction es with
  | nil => simp [listMin]
  | cons e es ih =>
      simp only [listMin, List.foldr_cons, denote_min]
      change 0 < Min.min (e.denote P) ((listMin es).denote P)
      exact lt_min (h e (by simp)) (ih (fun x hx => h x (by simp [hx])))

lemma listMin_denote_le_one (es : List EF) (P : History) :
    (listMin es).denote P ≤ 1 := by
  induction es with
  | nil => simp [listMin]
  | cons e es ih =>
      simp only [listMin, List.foldr_cons, denote_min]
      change Min.min (e.denote P) ((listMin es).denote P) ≤ 1
      exact (min_le_right _ _).trans ih

end EF

namespace Strategy

/-- The current strategy's value in a fixed Boolean world, reified as an expressible
feature of the market history. -/
def worldValueFeature {n : ℕ} (T : Strategy n) (u : ℕ → Bool) : EF :=
  ROIBudget.sumFeatures (T.trades.map fun p =>
    .mul p.1 (.add (.const (boolPayoutRat u p.2))
      (.mul (.const (-1)) (.price p.2 n))))

def tradeListWorldValueFeature (trades : List (EF × Sentence)) (n : ℕ)
    (u : ℕ → Bool) : EF :=
  ROIBudget.sumFeatures (trades.map fun p =>
    .mul p.1 (.add (.const (boolPayoutRat u p.2))
      (.mul (.const (-1)) (.price p.2 n))))

@[simp] lemma tradeListWorldValueFeature_strategy {n : ℕ} (T : Strategy n)
    (u : ℕ → Bool) :
    tradeListWorldValueFeature T.trades n u = T.worldValueFeature u := by
  rfl

lemma worldValueFeature_rank_le {n : ℕ} (T : Strategy n) (u : ℕ → Bool) :
    (T.worldValueFeature u).rank ≤ n := by
  apply ROIBudget.sumFeatures_rank_le
  intro e he
  simp only [List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  simp only [EF.rank_mul, EF.rank_add, EF.rank_const, EF.rank_price]
  exact max_le (T.rank_le p hp) (max_le (by omega) (max_le (by omega) (by omega)))

lemma worldValueFeature_denote {n : ℕ} (T : Strategy n) (u : ℕ → Bool)
    (P : History) :
    (T.worldValueFeature u).denote P = T.value P (boolPCWorld u).payout := by
  rw [worldValueFeature, ROIBudget.sumFeatures_denote]
  unfold Strategy.value
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, EF.denote_mul, EF.denote_add, EF.denote_const,
    EF.denote_price, Pi.mul_apply, Pi.add_apply]
  rw [boolPCWorld_payout_eq]
  have hneg : ((-1 : ℚ) : ℝ) = -1 := by norm_num
  rw [hneg]
  ring

lemma value_congr_payout {n : ℕ} (T : Strategy n) (P : History)
    {w w' : Sentence → ℝ}
    (h : ∀ p ∈ T.trades, w p.2 = w' p.2) :
    T.value P w = T.value P w' := by
  unfold Strategy.value
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [h p hp]

/-- Rational expressible-feature evaluation is prefix-local at its syntactic rank. -/
lemma denoteRatWith_eq_of_eqUpTo (e : EF) (rho sigma : List ℚ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hrank : e.rank ≤ n)
    (hrho : ∀ i, rho.getD i 0 = sigma.getD i 0)
    (hQR : ∀ day, day ≤ n → ∀ φ, Q day φ = R day φ) :
    e.denoteRatWith rho Q = e.denoteRatWith sigma R := by
  induction e generalizing rho sigma with
  | price φ day => exact hQR day hrank φ
  | const q => rfl
  | add a b iha ihb =>
      simp only [EF.rank_add, max_le_iff] at hrank
      simp [EF.denoteRatWith, iha rho sigma hrank.1 hrho,
        ihb rho sigma hrank.2 hrho]
  | mul a b iha ihb =>
      simp only [EF.rank_mul, max_le_iff] at hrank
      simp [EF.denoteRatWith, iha rho sigma hrank.1 hrho,
        ihb rho sigma hrank.2 hrho]
  | max a b iha ihb =>
      simp only [EF.rank_max, max_le_iff] at hrank
      simp [EF.denoteRatWith, iha rho sigma hrank.1 hrho,
        ihb rho sigma hrank.2 hrho]
  | safeRecip a iha =>
      simp [EF.denoteRatWith, iha rho sigma hrank hrho]
  | var i => exact hrho i
  | letE x body ihx ihbody =>
      simp only [EF.rank_letE, max_le_iff] at hrank
      have hx := ihx rho sigma hrank.1 hrho
      simp only [EF.denoteRatWith]
      apply ihbody (x.denoteRatWith rho Q :: rho)
        (x.denoteRatWith sigma R :: sigma) hrank.2
      intro i
      cases i with
      | zero => simpa using hx
      | succ i => simpa using hrho i

lemma denoteRat_eq_of_eqUpTo (e : EF)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hrank : e.rank ≤ n)
    (hQR : ∀ day, day ≤ n → ∀ φ, Q day φ = R day φ) :
    e.denoteRat Q = e.denoteRat R := by
  exact denoteRatWith_eq_of_eqUpTo e [] [] Q R n hrank (by simp) hQR

lemma marketValueRat_eq_of_eqUpTo {n : ℕ} (T : Strategy n)
    (Q R : ℕ → Sentence → ℚ) (w : Sentence → ℚ)
    (hQR : ∀ day, day ≤ n → ∀ φ, Q day φ = R day φ) :
    T.marketValueRat Q w = T.marketValueRat R w := by
  unfold Strategy.marketValueRat
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [denoteRat_eq_of_eqUpTo p.1 Q R n (T.rank_le p hp) hQR,
    hQR n le_rfl p.2]

end Strategy

/-- Raw wealth through day `n-1`, evaluated exactly in rational arithmetic. -/
def rawPriorWorthRat (Tr : Trader) (Q : ℕ → Sentence → ℚ)
    (u : ℕ → Bool) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (Tr.strat i).marketValueRat Q (boolPayoutRat u)

/-- Raw wealth through day `m`. -/
def rawWorthRat (Tr : Trader) (Q : ℕ → Sentence → ℚ)
    (u : ℕ → Bool) (m : ℕ) : ℚ :=
  rawPriorWorthRat Tr Q u (m + 1)

/-- Raw wealth with the trader represented solely by its day-indexed trade lists. -/
def rawPriorWorthRatTradeLists (tradesAt : ℕ → List (EF × Sentence))
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n,
    tradeListMarketValueRat (tradesAt i) i Q (boolPayoutRat u)

def rawWorthRatTradeLists (tradesAt : ℕ → List (EF × Sentence))
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (m : ℕ) : ℚ :=
  rawPriorWorthRatTradeLists tradesAt Q u (m + 1)

@[simp] lemma rawPriorWorthRatTradeLists_trader (Tr : Trader)
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ) :
    rawPriorWorthRatTradeLists (fun i => (Tr.strat i).trades) Q u n =
      rawPriorWorthRat Tr Q u n := by
  rfl

@[simp] lemma rawWorthRatTradeLists_trader (Tr : Trader)
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (m : ℕ) :
    rawWorthRatTradeLists (fun i => (Tr.strat i).trades) Q u m =
      rawWorthRat Tr Q u m := by
  rfl

lemma rawPriorWorthRat_eq_of_eq_prefix (Tr : Trader)
    (Q R : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    rawPriorWorthRat Tr Q u n = rawPriorWorthRat Tr R u n := by
  unfold rawPriorWorthRat
  apply Finset.sum_congr rfl
  intro i hi
  apply (Tr.strat i).marketValueRat_eq_of_eqUpTo
  intro day hday φ
  exact hQR day (lt_of_le_of_lt hday (Finset.mem_range.mp hi)) φ

lemma rawWorthRat_eq_of_eq_prefix (Tr : Trader)
    (Q R : ℕ → Sentence → ℚ) (u : ℕ → Bool) (m : ℕ)
    (hQR : ∀ day, day ≤ m → ∀ φ, Q day φ = R day φ) :
    rawWorthRat Tr Q u m = rawWorthRat Tr R u m := by
  apply rawPriorWorthRat_eq_of_eq_prefix
  intro day hday φ
  exact hQR day (by omega) φ

lemma rawPriorWorthRat_cast (Tr : Trader) (P : History)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (u : ℕ → Bool) (n : ℕ) :
    (rawPriorWorthRat Tr Q u n : ℝ) =
      ∑ i ∈ Finset.range n, (Tr.strat i).value P (boolPCWorld u).payout := by
  unfold rawPriorWorthRat
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  symm
  exact (Tr.strat i).value_eq_marketRatCast P Q hQ
    (boolPCWorld u).payout (boolPayoutRat u) (boolPCWorld_payout_eq u)

lemma rawWorthRat_cast (Tr : Trader) (P : History)
    (Q : ℕ → Sentence → ℚ) (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (u : ℕ → Bool) (m : ℕ) :
    (rawWorthRat Tr Q u m : ℝ) = Tr.netWorth P (boolPCWorld u) m := by
  rw [rawWorthRat, rawPriorWorthRat_cast Tr P Q hQ]
  rfl

/-- Prefix-local form used by adaptive constructions: raw prior wealth through `n-1`
does not require a rational quote for the still-variable day `n`. -/
lemma rawPriorWorthRat_cast_of_prefix (Tr : Trader) (P : History)
    (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (u : ℕ → Bool) :
    (rawPriorWorthRat Tr Q u n : ℝ) =
      ∑ i ∈ Finset.range n, (Tr.strat i).value P (boolPCWorld u).payout := by
  let PQ : History := fun day φ => (Q day φ : ℝ)
  rw [rawPriorWorthRat, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  calc
    ((Tr.strat i).marketValueRat Q (boolPayoutRat u) : ℝ) =
        (Tr.strat i).value PQ (boolPCWorld u).payout := by
      symm
      apply (Tr.strat i).value_eq_marketRatCast PQ Q
      · intro day φ
        rfl
      · exact boolPCWorld_payout_eq u
    _ = (Tr.strat i).value P (boolPCWorld u).payout := by
      symm
      apply (Tr.strat i).value_eq_of_eqUpTo
      intro day hday φ
      exact hQ day (lt_of_le_of_lt hday hin) φ

/-- Prefix-local form for raw wealth through `m`. -/
lemma rawWorthRat_cast_of_prefix (Tr : Trader) (P : History)
    (Q : ℕ → Sentence → ℚ) (m : ℕ)
    (hQ : ∀ day, day ≤ m → ∀ φ, P day φ = (Q day φ : ℝ))
    (u : ℕ → Bool) :
    (rawWorthRat Tr Q u m : ℝ) = Tr.netWorth P (boolPCWorld u) m := by
  rw [rawWorthRat, rawPriorWorthRat_cast_of_prefix Tr P Q (m + 1)]
  · rfl
  · intro day hday φ
    exact hQ day (by omega) φ

/-- Wealth strictly before day `n`. -/
noncomputable def Trader.priorNetWorth (Tr : Trader) (P : History)
    (v : PCWorld) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (Tr.strat i).value P v.payout

lemma Trader.netWorth_eq_prior_add (Tr : Trader) (P : History)
    (v : PCWorld) (n : ℕ) :
    Tr.netWorth P v n = Tr.priorNetWorth P v n + (Tr.strat n).value P v.payout := by
  rw [Trader.netWorth, Trader.priorNetWorth, Finset.sum_range_succ]

lemma rawPriorWorthRat_restricted_cast (DP : DeductiveProcess) (Tr : Trader)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (v : PCWorld) (n : ℕ) :
    (rawPriorWorthRat Tr Q
      (finiteAtomTable (budgetAtoms DP Tr n)
        (restrictedAssignment (budgetAtoms DP Tr n) v)) n : ℝ) =
      Tr.priorNetWorth P v n := by
  let A := budgetAtoms DP Tr n
  let u := finiteAtomTable A (restrictedAssignment A v)
  rw [rawPriorWorthRat_cast Tr P Q hQ u n]
  unfold Trader.priorNetWorth
  apply Finset.sum_congr rfl
  intro i hi
  apply (Tr.strat i).value_congr_payout P
  intro p hp
  exact restricted_payout_eq A v p.2
    (trade_atoms_subset_budgetAtoms DP Tr (by simp at hi; omega) hp)

lemma rawWorthRat_restricted_cast (DP : DeductiveProcess) (Tr : Trader)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (v : PCWorld) {m n : ℕ} (hmn : m ≤ n) :
    (rawWorthRat Tr Q
      (finiteAtomTable (budgetAtoms DP Tr n)
        (restrictedAssignment (budgetAtoms DP Tr n) v)) m : ℝ) =
      Tr.netWorth P v m := by
  let A := budgetAtoms DP Tr n
  let u := finiteAtomTable A (restrictedAssignment A v)
  rw [rawWorthRat_cast Tr P Q hQ u m]
  unfold Trader.netWorth
  apply Finset.sum_congr rfl
  intro i hi
  apply (Tr.strat i).value_congr_payout P
  intro p hp
  exact restricted_payout_eq A v p.2
    (trade_atoms_subset_budgetAtoms DP Tr (by simp at hi; omega) hp)

lemma tableConsistent_restricted_iff (DP : DeductiveProcess) (Tr : Trader)
    (v : PCWorld) {m n : ℕ} (hmn : m ≤ n) :
    tableConsistent
      (finiteAtomTable (budgetAtoms DP Tr n)
        (restrictedAssignment (budgetAtoms DP Tr n) v)) (DP.D m) = true ↔
      v.ConsistentWith (DP.D m) := by
  rw [tableConsistent_eq_true_iff]
  constructor
  · intro h φ hφ
    exact ((sentenceBool_eq_true_iff _ φ).symm.trans
      (sentenceBool_restricted_world (budgetAtoms DP Tr n) v φ
        (deductive_atoms_subset_budgetAtoms DP Tr hmn hφ))).mp (h φ hφ)
  · intro h φ hφ
    exact ((sentenceBool_eq_true_iff _ φ).symm.trans
      (sentenceBool_restricted_world (budgetAtoms DP Tr n) v φ
        (deductive_atoms_subset_budgetAtoms DP Tr hmn hφ))).mpr (h φ hφ)

/-- Whether the unbudgeted trader has already reached or crossed `-b` in a plausible
world on some day before `n`.  All quantifiers are explicit finite list scans. -/
def priorBudgetBreach (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Bool :=
  let A := budgetAtoms DP Tr n
  (finiteAtomAssignments A).any fun bits =>
    (List.range n).any fun m =>
      tableConsistent (finiteAtomTable A bits) (DP.D m) &&
        decide (rawWorthRat Tr Q (finiteAtomTable A bits) m ≤ -(b : ℚ))

lemma priorBudgetBreach_eq_of_eq_prefix
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    priorBudgetBreach DP Tr b Q n = priorBudgetBreach DP Tr b R n := by
  unfold priorBudgetBreach
  apply List.any_congr rfl
  intro bits
  have hall : ∀ m ∈ List.range n, m < n := by simp
  generalize List.range n = days at hall ⊢
  induction days with
  | nil => simp
  | cons m days ih =>
      have hm : m < n := hall m (by simp)
      have hrest : ∀ d ∈ days, d < n := by
        intro d hd
        exact hall d (by simp [hd])
      simp only [List.any_cons]
      rw [rawWorthRat_eq_of_eq_prefix Tr Q R _ m
        (fun day hday φ => hQR day (lt_of_le_of_lt hday hm) φ), ih hrest]

/-- Prefix-local soundness direction for the breach scan.  This is the interface needed
when day `n` is still a symbolic price vector inside MarketMaker. -/
lemma priorBudgetBreach_eq_false_of_safe_prefix
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (hsafe : ∀ m < n, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      -(b : ℝ) < Tr.netWorth P v m) :
    priorBudgetBreach DP Tr b Q n = false := by
  unfold priorBudgetBreach
  apply List.any_eq_false.mpr
  intro bits hbits
  have hinner : ((List.range n).any fun m =>
      tableConsistent (finiteAtomTable (budgetAtoms DP Tr n) bits) (DP.D m) &&
        decide (rawWorthRat Tr Q
          (finiteAtomTable (budgetAtoms DP Tr n) bits) m ≤ -(b : ℚ))) = false := by
    apply List.any_eq_false.mpr
    intro m hm
    simp only [List.mem_range] at hm
    let A := budgetAtoms DP Tr n
    let u := finiteAtomTable A bits
    by_cases hcons : tableConsistent u (DP.D m) = true
    · have hv : (boolPCWorld u).ConsistentWith (DP.D m) :=
        (tableConsistent_eq_true_iff u (DP.D m)).mp hcons
      have hs := hsafe m hm (boolPCWorld u) hv
      have hcast := rawWorthRat_cast_of_prefix Tr P Q m
        (fun day hday φ => hQ day (lt_of_le_of_lt hday hm) φ) u
      have hrat : -(b : ℚ) < rawWorthRat Tr Q u m := by
        rw [← hcast] at hs
        exact_mod_cast hs
      simp [hcons, u, A, not_le.mpr hrat]
    · simp [hcons, u, A]
  simp [hinner]

/-- The executable breach scan is exactly the paper's semantic past-loss test. -/
lemma priorBudgetBreach_eq_false_iff (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) :
    priorBudgetBreach DP Tr b Q n = false ↔
      ∀ m < n, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
        -(b : ℝ) < Tr.netWorth P v m := by
  constructor
  · intro hfalse m hmn v hv
    let A := budgetAtoms DP Tr n
    let bits := restrictedAssignment A v
    have hbits : bits ∈ finiteAtomAssignments A := restrictedAssignment_mem A v
    have hscan := (List.any_eq_false.mp (show
      (finiteAtomAssignments A).any (fun bits =>
        (List.range n).any fun m =>
          tableConsistent (finiteAtomTable A bits) (DP.D m) &&
            decide (rawWorthRat Tr Q (finiteAtomTable A bits) m ≤ -(b : ℚ))) = false by
      simpa [priorBudgetBreach, A] using hfalse)) bits hbits
    have hscanFalse := Bool.eq_false_of_not_eq_true hscan
    have hmNot := (List.any_eq_false.mp hscanFalse) m (by simp [hmn])
    have hm := Bool.eq_false_of_not_eq_true hmNot
    have hcons : tableConsistent (finiteAtomTable A bits) (DP.D m) = true :=
      (tableConsistent_restricted_iff DP Tr v (Nat.le_of_lt hmn)).mpr hv
    have hnot : ¬rawWorthRat Tr Q (finiteAtomTable A bits) m ≤ -(b : ℚ) := by
      simpa [hcons] using hm
    have hrat : -(b : ℚ) < rawWorthRat Tr Q (finiteAtomTable A bits) m := lt_of_not_ge hnot
    have hcast := rawWorthRat_restricted_cast DP Tr P Q hQ v (Nat.le_of_lt hmn)
    rw [← hcast]
    exact_mod_cast hrat
  · intro hsafe
    unfold priorBudgetBreach
    apply List.any_eq_false.mpr
    intro bits hbits
    have hinner : ((List.range n).any fun m =>
        tableConsistent (finiteAtomTable (budgetAtoms DP Tr n) bits) (DP.D m) &&
          decide (rawWorthRat Tr Q
            (finiteAtomTable (budgetAtoms DP Tr n) bits) m ≤ -(b : ℚ))) = false := by
      apply List.any_eq_false.mpr
      intro m hm
      simp only [List.mem_range] at hm
      let A := budgetAtoms DP Tr n
      let u := finiteAtomTable A bits
      by_cases hcons : tableConsistent u (DP.D m) = true
      · have hv : (boolPCWorld u).ConsistentWith (DP.D m) :=
          (tableConsistent_eq_true_iff u (DP.D m)).mp hcons
        have hreal := hsafe m hm (boolPCWorld u) hv
        have hcast := rawWorthRat_cast Tr P Q hQ u m
        have hrat : -(b : ℚ) < rawWorthRat Tr Q u m := by
          have hreal' : -(b : ℝ) < (rawWorthRat Tr Q u m : ℝ) := by
            rw [hcast]
            exact hreal
          exact_mod_cast hreal'
        change ¬(tableConsistent u (DP.D m) &&
          decide (rawWorthRat Tr Q u m ≤ -(b : ℚ))) = true
        intro htrue
        have hdec : decide (rawWorthRat Tr Q u m ≤ -(b : ℚ)) = true := by
          simpa [hcons] using htrue
        exact (not_le_of_gt hrat) (of_decide_eq_true hdec)
      · change ¬(tableConsistent u (DP.D m) &&
          decide (rawWorthRat Tr Q u m ≤ -(b : ℚ))) = true
        simp [hcons]
    simp [hinner]

/-- One world-specific reciprocal loss cap from `def:budgeter`. -/
def budgetWorldScale (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ) : EF :=
  .safeRecip (.mul
    (.const ((b + rawPriorWorthRat Tr Q u n)⁻¹))
    (EF.neg ((Tr.strat n).worldValueFeature u)))

/-- The infimum of the world-specific caps over the explicit finite plausible-world
enumeration. -/
def budgetScaleFeature (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : EF :=
  let A := budgetAtoms DP Tr n
  EF.listMin (((finiteAtomAssignments A).filter fun bits =>
    tableConsistent (finiteAtomTable A bits) (DP.D n)).map fun bits =>
      budgetWorldScale Tr b Q (finiteAtomTable A bits) n)

lemma budgetWorldScale_eq_of_eq_prefix (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    budgetWorldScale Tr b Q u n = budgetWorldScale Tr b R u n := by
  unfold budgetWorldScale
  rw [rawPriorWorthRat_eq_of_eq_prefix Tr Q R u n hQR]

lemma budgetScaleFeature_eq_of_eq_prefix
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    budgetScaleFeature DP Tr b Q n = budgetScaleFeature DP Tr b R n := by
  unfold budgetScaleFeature
  apply congrArg EF.listMin
  apply List.map_congr_left
  intro bits hbits
  exact budgetWorldScale_eq_of_eq_prefix Tr b Q R
    (finiteAtomTable (budgetAtoms DP Tr n) bits) n hQR

lemma budgetWorldScale_rank_le {n : ℕ} (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) :
    (budgetWorldScale Tr b Q u n).rank ≤ n := by
  simp [budgetWorldScale, EF.neg]
  exact Strategy.worldValueFeature_rank_le (Tr.strat n) u

lemma budgetWorldScale_denote (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (u : ℕ → Bool) (n : ℕ) :
    (budgetWorldScale Tr b Q u n).denote P =
      (max 1
        (-((Tr.strat n).value P (boolPCWorld u).payout) /
          ((b : ℝ) + (rawPriorWorthRat Tr Q u n : ℝ))))⁻¹ := by
  simp only [budgetWorldScale, EF.denote_safeRecip, EF.denote_mul, EF.denote_const,
    Pi.mul_apply, EF.denote_neg, Strategy.worldValueFeature_denote]
  norm_cast
  rw [div_eq_mul_inv]
  congr 2
  rw [Rat.cast_inv]
  ring

/-- The scalar appearing in one Budgeter world clause. -/
noncomputable def lossCap (available current : ℝ) : ℝ :=
  (max 1 (-current / available))⁻¹

lemma lossCap_pos (available current : ℝ) : 0 < lossCap available current := by
  unfold lossCap
  exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

lemma lossCap_le_one (available current : ℝ) : lossCap available current ≤ 1 := by
  unfold lossCap
  exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    (le_max_left _ _)

lemma lossCap_eq_one_of_ratio_le {available current : ℝ}
    (h : -current / available ≤ 1) : lossCap available current = 1 := by
  simp [lossCap, max_eq_left h]

lemma lossCap_floor {available current : ℝ} (ha : 0 < available) :
    -available ≤ current * lossCap available current := by
  by_cases hratio : -current / available ≤ 1
  · rw [lossCap_eq_one_of_ratio_le hratio]
    have hbound : -current ≤ available := (div_le_one ha).mp hratio
    linarith
  · have hratio' : 1 ≤ -current / available := le_of_not_ge hratio
    have hx : current < 0 := by
      by_contra hx
      have hx0 : 0 ≤ current := le_of_not_gt hx
      have : -current / available ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0) ha.le
      linarith
    unfold lossCap
    rw [max_eq_right hratio']
    have hxne : current ≠ 0 := ne_of_lt hx
    have hane : available ≠ 0 := ne_of_gt ha
    field_simp [hxne, hane]
    norm_num

lemma budgetScaleFeature_rank_le (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (budgetScaleFeature DP Tr b Q n).rank ≤ n := by
  unfold budgetScaleFeature
  apply EF.listMin_rank_le
  intro e he
  simp only [List.mem_map, List.mem_filter] at he
  obtain ⟨bits, _, rfl⟩ := he
  exact budgetWorldScale_rank_le Tr b Q _

lemma budgetScaleFeature_denote_pos (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (_hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) :
    0 < (budgetScaleFeature DP Tr b Q n).denote P := by
  unfold budgetScaleFeature
  apply EF.listMin_denote_pos
  intro e he
  simp only [List.mem_map, List.mem_filter] at he
  obtain ⟨bits, _, rfl⟩ := he
  rw [budgetWorldScale_denote Tr b P Q]
  exact lossCap_pos _ _

lemma budgetScaleFeature_denote_le_one (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (_hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ) :
    (budgetScaleFeature DP Tr b Q n).denote P ≤ 1 := by
  unfold budgetScaleFeature
  exact EF.listMin_denote_le_one _ P

/-- The global scale is no larger than the clause for any supplied plausible world. -/
lemma budgetScaleFeature_denote_le_world (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (bits : budgetAtoms DP Tr n → Bool)
    (hbits : bits ∈ finiteAtomAssignments (budgetAtoms DP Tr n))
    (hcons : tableConsistent (finiteAtomTable (budgetAtoms DP Tr n) bits) (DP.D n) = true) :
    (budgetScaleFeature DP Tr b Q n).denote P ≤
      (budgetWorldScale Tr b Q (finiteAtomTable (budgetAtoms DP Tr n) bits) n).denote P := by
  unfold budgetScaleFeature
  apply EF.listMin_denote_le_of_mem
  apply List.mem_map.mpr
  exact ⟨bits, by simp [hbits, hcons], rfl⟩

/-- Prefix-local form of exact scale preservation.  Only prices before day `n` occur in
the available-capital denominator; the current price remains symbolic in the feature. -/
lemma budgetScaleFeature_denote_eq_one_of_safe_prefix
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ) (hb : 0 < b)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (n : ℕ) (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (hsafe : ∀ m ≤ n, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      -(b : ℝ) < Tr.netWorth P v m) :
    (budgetScaleFeature DP Tr b Q n).denote P = 1 := by
  unfold budgetScaleFeature
  apply EF.listMin_denote_eq_one
  intro e he
  simp only [List.mem_map, List.mem_filter] at he
  obtain ⟨bits, ⟨hbits, hcons⟩, rfl⟩ := he
  let u := finiteAtomTable (budgetAtoms DP Tr n) bits
  have hv : (boolPCWorld u).ConsistentWith (DP.D n) :=
    (tableConsistent_eq_true_iff u (DP.D n)).mp hcons
  have hprior : 0 < (b : ℝ) + (rawPriorWorthRat Tr Q u n : ℝ) := by
    cases n with
    | zero =>
        simp [rawPriorWorthRat]
        exact_mod_cast hb
    | succ m =>
        have hvm : (boolPCWorld u).ConsistentWith (DP.D m) := by
          intro φ hφ
          exact hv φ (DP.mono m hφ)
        have hs := hsafe m (by omega) (boolPCWorld u) hvm
        have hcast := rawWorthRat_cast_of_prefix Tr P Q m
          (fun day hday φ => hQ day (by omega) φ) u
        have heq : rawPriorWorthRat Tr Q u (m + 1) = rawWorthRat Tr Q u m := rfl
        rw [heq, hcast]
        linarith
  have htotal := hsafe n (by omega) (boolPCWorld u) hv
  rw [Tr.netWorth_eq_prior_add] at htotal
  unfold Trader.priorNetWorth at htotal
  have hpriorCast := rawPriorWorthRat_cast_of_prefix Tr P Q n hQ u
  have hloss : -((Tr.strat n).value P (boolPCWorld u).payout) <
      (b : ℝ) + (rawPriorWorthRat Tr Q u n : ℝ) := by
    rw [hpriorCast]
    linarith
  rw [budgetWorldScale_denote Tr b P Q]
  apply lossCap_eq_one_of_ratio_le
  exact (div_le_one hprior).mpr hloss.le

/-- If the raw trader has stayed strictly within budget through day `n`, every
world-specific cap and therefore their finite infimum evaluates to one. -/
lemma budgetScaleFeature_denote_eq_one_of_safe
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ) (hb : 0 < b)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ)
    (hsafe : ∀ m ≤ n, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      -(b : ℝ) < Tr.netWorth P v m) :
    (budgetScaleFeature DP Tr b Q n).denote P = 1 :=
  budgetScaleFeature_denote_eq_one_of_safe_prefix DP Tr b hb P Q n
    (fun day _ φ => hQ day φ) hsafe

/-- `def:budgeter`: the exact day action.  The past-prefix branch is executable and the
nonzero branch is an ordinary rank-legal strategy continuous in current prices. -/
def BudgeterAt (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Strategy n :=
  if priorBudgetBreach DP Tr b Q n then
    ⟨[], by simp⟩
  else
    (Tr.strat n).scaleBy (budgetScaleFeature DP Tr b Q n)
      (budgetScaleFeature_rank_le DP Tr b Q n)

/-! ### Finite-stage operational form

The recursive market program receives decoded finite stages, not a semantic
`DeductiveProcess` oracle.  These definitions are the same bounded scans as `BudgeterAt`
with the stage table made an explicit data argument. -/

def budgetAtomsFromStages (D : ℕ → Finset Sentence) (Tr : Trader)
    (n : ℕ) : Finset ℕ :=
  (D n).biUnion Sentence.atoms ∪
    (Finset.range (n + 1)).biUnion fun i => (Tr.strat i).sentenceAtoms

def tradeListSentenceAtoms (trades : List (EF × Sentence)) : Finset ℕ :=
  (tradeListSupport trades).biUnion Sentence.atoms

def budgetAtomsFromStageTradeLists (D : ℕ → Finset Sentence)
    (tradesAt : ℕ → List (EF × Sentence)) (n : ℕ) : Finset ℕ :=
  (D n).biUnion Sentence.atoms ∪
    (Finset.range (n + 1)).biUnion fun i => tradeListSentenceAtoms (tradesAt i)

@[simp] lemma budgetAtomsFromStageTradeLists_trader (D : ℕ → Finset Sentence)
    (Tr : Trader) (n : ℕ) :
    budgetAtomsFromStageTradeLists D (fun i => (Tr.strat i).trades) n =
      budgetAtomsFromStages D Tr n := by
  rfl

def priorBudgetBreachFromStages (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Bool :=
  let A := budgetAtomsFromStages D Tr n
  (finiteAtomAssignments A).any fun bits =>
    (List.range n).any fun m =>
      tableConsistent (finiteAtomTable A bits) (D m) &&
        decide (rawWorthRat Tr Q (finiteAtomTable A bits) m ≤ -(b : ℚ))

/-- First-order bit-list form of `priorBudgetBreachFromStages`. -/
def priorBudgetBreachFromStageLists (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Bool :=
  let A := budgetAtomsFromStages D Tr n
  (allBoolLists A.card).any fun xs =>
    (List.range n).any fun m =>
      tableConsistent (finiteAtomTableFromList A xs) (D m) &&
        decide (rawWorthRat Tr Q (finiteAtomTableFromList A xs) m ≤ -(b : ℚ))

lemma priorBudgetBreachFromStageLists_eq (D : ℕ → Finset Sentence)
    (Tr : Trader) (b : ℕ) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    priorBudgetBreachFromStageLists D Tr b Q n =
      priorBudgetBreachFromStages D Tr b Q n := by
  unfold priorBudgetBreachFromStageLists priorBudgetBreachFromStages
  simp only [finiteAtomAssignments, List.any_map]
  apply List.any_congr rfl
  intro xs
  simp only [Function.comp_apply, finiteAtomTable_atomAssignmentOfList]

def budgetScaleFeatureFromStages (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : EF :=
  let A := budgetAtomsFromStages D Tr n
  EF.listMin (((finiteAtomAssignments A).filter fun bits =>
    tableConsistent (finiteAtomTable A bits) (D n)).map fun bits =>
      budgetWorldScale Tr b Q (finiteAtomTable A bits) n)

/-- First-order bit-list form of `budgetScaleFeatureFromStages`. -/
def budgetScaleFeatureFromStageLists (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : EF :=
  let A := budgetAtomsFromStages D Tr n
  EF.listMin (((allBoolLists A.card).filter fun xs =>
    tableConsistent (finiteAtomTableFromList A xs) (D n)).map fun xs =>
      budgetWorldScale Tr b Q (finiteAtomTableFromList A xs) n)

lemma budgetScaleFeatureFromStageLists_eq (D : ℕ → Finset Sentence)
    (Tr : Trader) (b : ℕ) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    budgetScaleFeatureFromStageLists D Tr b Q n =
      budgetScaleFeatureFromStages D Tr b Q n := by
  unfold budgetScaleFeatureFromStageLists budgetScaleFeatureFromStages
  simp only [finiteAtomAssignments, List.filter_map, List.map_map, Function.comp_def,
    finiteAtomTable_atomAssignmentOfList]

lemma budgetScaleFeatureFromStages_rank_le (D : ℕ → Finset Sentence)
    (Tr : Trader) (b : ℕ) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (budgetScaleFeatureFromStages D Tr b Q n).rank ≤ n := by
  unfold budgetScaleFeatureFromStages
  apply EF.listMin_rank_le
  intro e he
  simp only [List.mem_map, List.mem_filter] at he
  obtain ⟨bits, _, rfl⟩ := he
  exact budgetWorldScale_rank_le Tr b Q _

lemma budgetScaleFeatureFromStageLists_rank_le (D : ℕ → Finset Sentence)
    (Tr : Trader) (b : ℕ) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    (budgetScaleFeatureFromStageLists D Tr b Q n).rank ≤ n := by
  rw [budgetScaleFeatureFromStageLists_eq]
  exact budgetScaleFeatureFromStages_rank_le D Tr b Q n

def BudgeterAtFromStages (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Strategy n :=
  if priorBudgetBreachFromStages D Tr b Q n then
    ⟨[], by simp⟩
  else
    (Tr.strat n).scaleBy (budgetScaleFeatureFromStages D Tr b Q n)
      (budgetScaleFeatureFromStages_rank_le D Tr b Q n)

def BudgeterAtFromStageLists (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Strategy n :=
  if priorBudgetBreachFromStageLists D Tr b Q n then
    ⟨[], by simp⟩
  else
    (Tr.strat n).scaleBy (budgetScaleFeatureFromStageLists D Tr b Q n)
      (budgetScaleFeatureFromStageLists_rank_le D Tr b Q n)

lemma BudgeterAtFromStageLists_eq (D : ℕ → Finset Sentence) (Tr : Trader)
    (b : ℕ) (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    BudgeterAtFromStageLists D Tr b Q n = BudgeterAtFromStages D Tr b Q n := by
  unfold BudgeterAtFromStageLists BudgeterAtFromStages
  rw [priorBudgetBreachFromStageLists_eq]
  split
  · rfl
  · unfold Strategy.scaleBy
    congr
    funext p
    rw [budgetScaleFeatureFromStageLists_eq]

/-! The fully erased Budgeter path.  All inputs and outputs here have fixed first-order
types, while the equality theorem below reconnects it to the proof-carrying strategy. -/

def priorBudgetBreachFromStageTradeLists (D : ℕ → Finset Sentence)
    (tradesAt : ℕ → List (EF × Sentence)) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : Bool :=
  let A := budgetAtomsFromStageTradeLists D tradesAt n
  (allBoolLists A.card).any fun xs =>
    (List.range n).any fun m =>
      tableConsistent (finiteAtomTableFromList A xs) (D m) &&
        decide (rawWorthRatTradeLists tradesAt Q
          (finiteAtomTableFromList A xs) m ≤ -(b : ℚ))

def budgetWorldScaleTradeLists (tradesAt : ℕ → List (EF × Sentence)) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ) : EF :=
  .safeRecip (.mul
    (.const ((b + rawPriorWorthRatTradeLists tradesAt Q u n)⁻¹))
    (EF.neg (Strategy.tradeListWorldValueFeature (tradesAt n) n u)))

def budgetScaleFeatureFromStageTradeLists (D : ℕ → Finset Sentence)
    (tradesAt : ℕ → List (EF × Sentence)) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : EF :=
  let A := budgetAtomsFromStageTradeLists D tradesAt n
  EF.listMin (((allBoolLists A.card).filter fun xs =>
    tableConsistent (finiteAtomTableFromList A xs) (D n)).map fun xs =>
      budgetWorldScaleTradeLists tradesAt b Q (finiteAtomTableFromList A xs) n)

def budgeterTradesFromStageTradeLists (D : ℕ → Finset Sentence)
    (tradesAt : ℕ → List (EF × Sentence)) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) : List (EF × Sentence) :=
  if priorBudgetBreachFromStageTradeLists D tradesAt b Q n then []
  else
    (tradesAt n).map fun p =>
      (.mul (budgetScaleFeatureFromStageTradeLists D tradesAt b Q n) p.1, p.2)

lemma priorBudgetBreachFromStageTradeLists_trader
    (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    priorBudgetBreachFromStageTradeLists D (fun i => (Tr.strat i).trades) b Q n =
      priorBudgetBreachFromStageLists D Tr b Q n := by
  rfl

lemma budgetWorldScaleTradeLists_trader (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (u : ℕ → Bool) (n : ℕ) :
    budgetWorldScaleTradeLists (fun i => (Tr.strat i).trades) b Q u n =
      budgetWorldScale Tr b Q u n := by
  unfold budgetWorldScaleTradeLists budgetWorldScale
  rw [rawPriorWorthRatTradeLists_trader,
    Strategy.tradeListWorldValueFeature_strategy]

lemma budgetScaleFeatureFromStageTradeLists_trader
    (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    budgetScaleFeatureFromStageTradeLists D (fun i => (Tr.strat i).trades) b Q n =
      budgetScaleFeatureFromStageLists D Tr b Q n := by
  unfold budgetScaleFeatureFromStageTradeLists budgetScaleFeatureFromStageLists
  rw [budgetAtomsFromStageTradeLists_trader]
  apply congrArg EF.listMin
  apply List.map_congr_left
  intro xs hxs
  exact budgetWorldScaleTradeLists_trader Tr b Q _ n

lemma budgeterTradesFromStageTradeLists_trader
    (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    budgeterTradesFromStageTradeLists D (fun i => (Tr.strat i).trades) b Q n =
      (BudgeterAtFromStageLists D Tr b Q n).trades := by
  unfold budgeterTradesFromStageTradeLists BudgeterAtFromStageLists
  rw [priorBudgetBreachFromStageTradeLists_trader]
  split
  · rfl
  · unfold Strategy.scaleBy
    rw [budgetScaleFeatureFromStageTradeLists_trader]

lemma BudgeterAtFromStages_eq (DP : DeductiveProcess)
    (D : ℕ → Finset Sentence) (hD : D = DP.D) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ) :
    BudgeterAtFromStages D Tr b Q n = BudgeterAt DP Tr b Q n := by
  subst D
  unfold BudgeterAtFromStages BudgeterAt priorBudgetBreachFromStages
    priorBudgetBreach budgetScaleFeatureFromStages budgetScaleFeature
    budgetAtomsFromStages budgetAtoms
  split
  · rfl
  · unfold Strategy.scaleBy
    congr

lemma budgetAtomsFromStages_eq_of_eq_prefix (DP : DeductiveProcess)
    (D : ℕ → Finset Sentence) (Tr : Trader) (n : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    budgetAtomsFromStages D Tr n = budgetAtoms DP Tr n := by
  unfold budgetAtomsFromStages budgetAtoms
  rw [hD n le_rfl]

lemma priorBudgetBreachFromStages_eq_of_eq_prefix (DP : DeductiveProcess)
    (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    priorBudgetBreachFromStages D Tr b Q n =
      priorBudgetBreach DP Tr b Q n := by
  unfold priorBudgetBreachFromStages priorBudgetBreach
  rw [budgetAtomsFromStages_eq_of_eq_prefix DP D Tr n hD]
  apply List.any_congr rfl
  intro bits
  have hall : ∀ m ∈ List.range n, m ≤ n := by simp; omega
  generalize List.range n = days at hall ⊢
  induction days with
  | nil => rfl
  | cons m days ih =>
      have hm : m ≤ n := hall m (by simp)
      have hrest : ∀ d ∈ days, d ≤ n := by
        intro d hd
        exact hall d (by simp [hd])
      simp only [List.any_cons]
      rw [hD m hm, ih hrest]

lemma budgetScaleFeatureFromStages_eq_of_eq_prefix (DP : DeductiveProcess)
    (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    budgetScaleFeatureFromStages D Tr b Q n =
      budgetScaleFeature DP Tr b Q n := by
  unfold budgetScaleFeatureFromStages budgetScaleFeature
  rw [budgetAtomsFromStages_eq_of_eq_prefix DP D Tr n hD, hD n le_rfl]

/-- Finite-prefix exactness: the day-`n` operational Budgeter agrees with the semantic one
as soon as decoded deductive stages `0,…,n` are exact. -/
lemma BudgeterAtFromStages_eq_of_eq_prefix (DP : DeductiveProcess)
    (D : ℕ → Finset Sentence) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hD : ∀ m, m ≤ n → D m = DP.D m) :
    BudgeterAtFromStages D Tr b Q n = BudgeterAt DP Tr b Q n := by
  unfold BudgeterAtFromStages BudgeterAt
  rw [priorBudgetBreachFromStages_eq_of_eq_prefix DP D Tr b Q n hD]
  split
  · rfl
  · have hscale := budgetScaleFeatureFromStages_eq_of_eq_prefix
      DP D Tr b Q n hD
    unfold Strategy.scaleBy
    congr 1
    rw [hscale]

lemma BudgeterAt_eq_of_eq_prefix
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q R : ℕ → Sentence → ℚ) (n : ℕ)
    (hQR : ∀ day, day < n → ∀ φ, Q day φ = R day φ) :
    BudgeterAt DP Tr b Q n = BudgeterAt DP Tr b R n := by
  unfold BudgeterAt
  rw [priorBudgetBreach_eq_of_eq_prefix DP Tr b Q R n hQR]
  split
  · rfl
  · have hscale := budgetScaleFeature_eq_of_eq_prefix DP Tr b Q R n hQR
    unfold Strategy.scaleBy
    congr 1
    rw [hscale]

/-- The realized budgeted trader against a fixed rational market table. -/
def budgetedTrader (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (Q : ℕ → Sentence → ℚ) : Trader where
  strat n := BudgeterAt DP Tr b Q n

/-- `lem:budgeter`, part 1: under the paper's strict raw-budget hypothesis, Budgeter
preserves the day-`n` trade exactly as an affine contract (equal value in every world). -/
theorem BudgeterAt_value_eq_of_safe
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ) (hb : 0 < b)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ)
    (hsafe : ∀ m ≤ n, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      -(b : ℝ) < Tr.netWorth P v m) (w : Sentence → ℝ) :
    (BudgeterAt DP Tr b Q n).value P w = (Tr.strat n).value P w := by
  have hbreach : priorBudgetBreach DP Tr b Q n = false :=
    (priorBudgetBreach_eq_false_iff DP Tr b P Q hQ n).mpr
      (fun m hm => hsafe m (Nat.le_of_lt hm))
  simp only [BudgeterAt, hbreach, Bool.false_eq_true, if_false]
  rw [Strategy.scaleBy_value,
    budgetScaleFeature_denote_eq_one_of_safe DP Tr b hb P Q hQ n hsafe, one_mul]

/-- Adaptive/prefix form of Budgeter preservation, with no current-price oracle. -/
lemma BudgeterAt_value_eq_of_safe_prefix
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ) (hb : 0 < b)
    (P : History) (Q : ℕ → Sentence → ℚ) (n : ℕ)
    (hQ : ∀ day, day < n → ∀ φ, P day φ = (Q day φ : ℝ))
    (hsafe : ∀ m ≤ n, ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      -(b : ℝ) < Tr.netWorth P v m) (w : Sentence → ℝ) :
    (BudgeterAt DP Tr b Q n).value P w = (Tr.strat n).value P w := by
  have hbreach : priorBudgetBreach DP Tr b Q n = false :=
    priorBudgetBreach_eq_false_of_safe_prefix DP Tr b P Q n hQ
      (fun m hm => hsafe m (Nat.le_of_lt hm))
  simp only [BudgeterAt, hbreach, Bool.false_eq_true, if_false]
  rw [Strategy.scaleBy_value,
    budgetScaleFeature_denote_eq_one_of_safe_prefix DP Tr b hb P Q n hQ hsafe,
    one_mul]

lemma budgetScaleFeature_denote_le_lossCap
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ)
    (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    (budgetScaleFeature DP Tr b Q n).denote P ≤
      lossCap ((b : ℝ) + Tr.priorNetWorth P v n)
        ((Tr.strat n).value P v.payout) := by
  let A := budgetAtoms DP Tr n
  let bits := restrictedAssignment A v
  let u := finiteAtomTable A bits
  have hbits : bits ∈ finiteAtomAssignments A := restrictedAssignment_mem A v
  have hcons : tableConsistent u (DP.D n) = true :=
    (tableConsistent_restricted_iff DP Tr v (le_refl n)).mpr hv
  have hle := budgetScaleFeature_denote_le_world DP Tr b P Q n bits hbits hcons
  rw [budgetWorldScale_denote Tr b P Q] at hle
  have hprior := rawPriorWorthRat_restricted_cast DP Tr P Q hQ v n
  have hcurrent : (Tr.strat n).value P (boolPCWorld u).payout =
      (Tr.strat n).value P v.payout := by
    apply (Tr.strat n).value_congr_payout P
    intro p hp
    exact restricted_payout_eq A v p.2
      (trade_atoms_subset_budgetAtoms DP Tr (le_refl n) hp)
  dsimp [u, bits, A] at hle
  rw [hprior, hcurrent] at hle
  exact hle

/-- On a non-bankrupt day, the Budgeter cannot lose more than the capital available at
the start of that day in any currently plausible world. -/
lemma BudgeterAt_value_ge_neg_available
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ) (hb : 0 < b)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) (n : ℕ)
    (hbreach : priorBudgetBreach DP Tr b Q n = false)
    (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    -((b : ℝ) + Tr.priorNetWorth P v n) ≤
      (BudgeterAt DP Tr b Q n).value P v.payout := by
  have hsafe := (priorBudgetBreach_eq_false_iff DP Tr b P Q hQ n).mp hbreach
  have havail : 0 < (b : ℝ) + Tr.priorNetWorth P v n := by
    cases n with
    | zero =>
        simp [Trader.priorNetWorth]
        exact_mod_cast hb
    | succ m =>
        have hvm : v.ConsistentWith (DP.D m) := by
          intro φ hφ
          exact hv φ (DP.mono m hφ)
        have hs := hsafe m (by omega) v hvm
        change 0 < (b : ℝ) + Tr.netWorth P v m
        linarith
  have hαpos := budgetScaleFeature_denote_pos DP Tr b P Q hQ n
  have hαcap := budgetScaleFeature_denote_le_lossCap DP Tr b P Q hQ n v hv
  have hcap := lossCap_floor
    (available := (b : ℝ) + Tr.priorNetWorth P v n)
    (current := (Tr.strat n).value P v.payout) havail
  rw [BudgeterAt]
  simp only [hbreach, Bool.false_eq_true, if_false, Strategy.scaleBy_value]
  by_cases hx : 0 ≤ (Tr.strat n).value P v.payout
  · have hmul : 0 ≤ (budgetScaleFeature DP Tr b Q n).denote P *
        (Tr.strat n).value P v.payout := mul_nonneg hαpos.le hx
    linarith
  · have hx' : (Tr.strat n).value P v.payout ≤ 0 := le_of_not_ge hx
    have hmul : (Tr.strat n).value P v.payout *
        lossCap ((b : ℝ) + Tr.priorNetWorth P v n)
          ((Tr.strat n).value P v.payout) ≤
        (Tr.strat n).value P v.payout *
          (budgetScaleFeature DP Tr b Q n).denote P :=
      mul_le_mul_of_nonpos_left hαcap hx'
    calc
      -((b : ℝ) + Tr.priorNetWorth P v n) ≤
          (Tr.strat n).value P v.payout *
            lossCap ((b : ℝ) + Tr.priorNetWorth P v n)
              ((Tr.strat n).value P v.payout) := hcap
      _ ≤ (Tr.strat n).value P v.payout *
          (budgetScaleFeature DP Tr b Q n).denote P := hmul
      _ = (budgetScaleFeature DP Tr b Q n).denote P *
          (Tr.strat n).value P v.payout := mul_comm _ _

/-- `lem:budgeter`, part 2: the realized budgeted trader has the uniform global floor
`-b` in every world plausible on every day. -/
theorem budgetedTrader_netWorth_floor
    (DP : DeductiveProcess) (Tr : Trader) (b : ℕ) (hb : 0 < b)
    (P : History) (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ)) :
    ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      -(b : ℝ) ≤ (budgetedTrader DP Tr b Q).netWorth P v n := by
  intro n
  induction n with
  | zero =>
      intro v hv
      have hbreach : priorBudgetBreach DP Tr b Q 0 = false := by
        simp [priorBudgetBreach]
      have hcur := BudgeterAt_value_ge_neg_available DP Tr b hb P Q hQ 0
        hbreach v hv
      simpa [Trader.netWorth, Trader.priorNetWorth, budgetedTrader] using hcur
  | succ n ih =>
      intro v hv
      have hvn : v.ConsistentWith (DP.D n) := by
        intro φ hφ
        exact hv φ (DP.mono n hφ)
      cases hbreach : priorBudgetBreach DP Tr b Q (n + 1) with
      | true =>
          have hprev := ih v hvn
          rw [Trader.netWorth, Finset.sum_range_succ]
          change -(b : ℝ) ≤
            (budgetedTrader DP Tr b Q).netWorth P v n +
              (BudgeterAt DP Tr b Q (n + 1)).value P v.payout
          have hzero : (BudgeterAt DP Tr b Q (n + 1)).value P v.payout = 0 := by
            simp [BudgeterAt, hbreach, Strategy.value]
          rw [hzero, add_zero]
          exact hprev
      | false =>
          have hsafe :=
            (priorBudgetBreach_eq_false_iff DP Tr b P Q hQ (n + 1)).mp hbreach
          have hpriorEq :
              (budgetedTrader DP Tr b Q).priorNetWorth P v (n + 1) =
                Tr.priorNetWorth P v (n + 1) := by
            unfold Trader.priorNetWorth
            apply Finset.sum_congr rfl
            intro i hi
            simp only [Finset.mem_range] at hi
            change (BudgeterAt DP Tr b Q i).value P v.payout =
              (Tr.strat i).value P v.payout
            apply BudgeterAt_value_eq_of_safe DP Tr b hb P Q hQ i
            intro m hmi w hw
            exact hsafe m (lt_of_le_of_lt hmi hi) w hw
          have hcur := BudgeterAt_value_ge_neg_available DP Tr b hb P Q hQ (n + 1)
            hbreach v hv
          rw [Trader.netWorth_eq_prior_add, hpriorEq]
          change -(b : ℝ) ≤ Tr.priorNetWorth P v (n + 1) +
            (BudgeterAt DP Tr b Q (n + 1)).value P v.payout
          linarith

/-- `lem:budgeter`, part 3: an exploiting trader is preserved by some positive integer
budget.  The selected Budgeter is extensionally identical to the original trader on the
given market, so both downside and unbounded upside transfer exactly. -/
theorem exists_budgetedTrader_exploits
    (DP : DeductiveProcess) (Tr : Trader) (P : History)
    (Q : ℕ → Sentence → ℚ)
    (hQ : ∀ day φ, P day φ = (Q day φ : ℝ))
    (hEx : Tr.Exploits P DP) :
    ∃ b : ℕ, 0 < b ∧ (budgetedTrader DP Tr b Q).Exploits P DP := by
  obtain ⟨a, ha⟩ := hEx.1
  obtain ⟨b₀, hb₀⟩ := exists_nat_gt (-a)
  let b := b₀ + 1
  have hb : 0 < b := by omega
  have hba : -(b : ℝ) < a := by
    have hbcast : (b : ℝ) = (b₀ : ℝ) + 1 := by simp [b]
    rw [hbcast]
    linarith
  have hsafe : ∀ n, ∀ v : PCWorld, v.ConsistentWith (DP.D n) →
      -(b : ℝ) < Tr.netWorth P v n := by
    intro n v hv
    exact hba.trans_le (ha ⟨n, v, hv, rfl⟩)
  have hday : ∀ n (w : Sentence → ℝ),
      (BudgeterAt DP Tr b Q n).value P w = (Tr.strat n).value P w := by
    intro n w
    apply BudgeterAt_value_eq_of_safe DP Tr b hb P Q hQ n
    intro m hm v hv
    exact hsafe m v hv
  have hnet : ∀ n v,
      (budgetedTrader DP Tr b Q).netWorth P v n = Tr.netWorth P v n := by
    intro n v
    unfold Trader.netWorth
    apply Finset.sum_congr rfl
    intro i hi
    exact hday i v.payout
  have hassess : (budgetedTrader DP Tr b Q).plausibleAssessments P DP =
      Tr.plausibleAssessments P DP := by
    ext x
    constructor
    · rintro ⟨n, v, hv, rfl⟩
      exact ⟨n, v, hv, by rw [hnet]⟩
    · rintro ⟨n, v, hv, rfl⟩
      exact ⟨n, v, hv, by rw [hnet]⟩
  refine ⟨b, hb, ?_⟩
  rw [Trader.Exploits, hassess]
  exact hEx

/-- Adaptive traders produce one ordinary strategy from each finite rational market prefix. -/
structure AdaptiveTrader where
  action : (n : ℕ) → List RationalBeliefState → Strategy n

/-- Executable adaptive Budgeter over MarketMaker's concrete rational history format. -/
def Budgeter (DP : DeductiveProcess) (Tr : Trader) (b : ℕ) : AdaptiveTrader where
  action n past := BudgeterAt DP Tr b (rationalHistory past) n

/-- Operational Budgeter built from a named deductive-process program.  All finite theory
queries pass through `stageSearchUpTo` at its certified stopping clock rather than through
an unexplained oracle for `DP.D`. -/
noncomputable def BudgeterFromComputation {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (Tr : Trader) (b : ℕ) : AdaptiveTrader :=
  Budgeter process.computedProcess Tr b

/-- The operational process-backed Budgeter is exactly the semantic Budgeter. -/
lemma BudgeterFromComputation_eq {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP) (Tr : Trader) (b : ℕ) :
    BudgeterFromComputation process Tr b = Budgeter DP Tr b := by
  unfold BudgeterFromComputation
  rw [process.computedProcess_eq]

#print axioms priorBudgetBreach_eq_false_iff
#print axioms BudgeterAt_value_eq_of_safe
#print axioms budgetedTrader_netWorth_floor
#print axioms exists_budgetedTrader_exploits
#print axioms BudgeterFromComputation_eq

end LogicalInduction
