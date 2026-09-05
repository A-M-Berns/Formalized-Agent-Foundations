import LogicalInduction.Properties.Basic
import LogicalInduction.Framework.WriteOut

/-!
# The hysteresis arbitrage trader

The oscillation-arbitrage trader that Convergence (`thm:con`, §4.1, appendix `app:con`)
turns on, together with the continuous threshold-indicator toolkit the whole §4 property
tail builds its traders from.

* `EF` building blocks: `oneMinus`, `efMin` — via `min x y = −max(−x, −y)`, there being no
  `min` constructor — and `clip01`, with their denotation and rank laws.
* Price-indexed signals `buyIndEF φ a δ n` and `sellIndEF φ b δ n`, the paper's continuous
  threshold indicator (`def:ctsind`) at a price leaf, and the feature-generic
  `buyIndF e a δ` / `sellIndF e b δ` at an arbitrary feature. At `δ = 0` both are
  identically zero, because `1/0 = 0` in `ℚ`; that is what makes padded-start ladders
  uniform-width.
* The arming chain `armChain sig n = Π_{i<n} (1 − sig i)`, whose update mentions its own
  previous value once, so the feature tree grows linearly (`dd:dsl` provides no sharing).
  Consumed by the rung ladders of `NonDogmatism`, `UniformNonDogmatism` and `OccamBounds`
  and by the gradual-sale component of `AffinePreemptiveLearning`.
* The holdings state `hystN`: `H 0 = 0`, `H (k+1) = max (H k · (1 − sellInd k)) (buyInd k)`,
  with the recursive branch written first so the serialization accretes fixed-width blocks in
  ascending day order on one side; the day-`n` trade is `H (n+1) − H n`.
* The accounting, which needs no per-swing induction: buys happen only below `a + δ` and
  sells only above `b − δ`, so `netWorth ≥ (b−a−2δ)·B₋ − (a+δ)` in every world
  (`hystTrader_netWorth_ge`), and each completed swing adds `1` to the downward variation
  `B₋` (`hystBneg_unbounded`).
* Efficient computability (`hystTrader_ecTok`): the day-`n` stream is five segments — fixed
  head, `n+1` fixed-width blocks, fixed mid, `n` blocks, fixed tail — emitted through
  `PolySegStream`.
* `oscillation_exploitable_hyst` is the packaged witness that `Coherence.oscillation_exploitable`
  consumes, at band `δ = (b−a)/4`.

Downstream consumers of the signal toolkit are `NonDogmatism` and `OccamBounds` (the rung
ladders) and `AffinePreemptiveLearning` and `AffineProvability` (the gradual-sale components).
-/

namespace LogicalInduction

open Filter Topology

/-! ## Feature building blocks -/

/-- `1 − e`. -/
def oneMinus (e : EF) : EF := .add (.const 1) (.mul (.const (-1)) e)

/-- `min e f`, via `min x y = −max(−x, −y)` (no `min` constructor exists). -/
def efMin (e f : EF) : EF :=
  .mul (.const (-1)) (.max (.mul (.const (-1)) e) (.mul (.const (-1)) f))

/-- Clip to `[0,1]`: `max 0 (min 1 e)`. -/
def clip01 (e : EF) : EF := .max (.const 0) (efMin (.const 1) e)

@[simp] lemma oneMinus_denote (e : EF) (V : History) :
    (oneMinus e).denote V = 1 - e.denote V := by
  simp only [oneMinus, EF.denote_add, EF.denote_mul, EF.denote_const, Pi.add_apply,
    Pi.mul_apply]
  push_cast; ring

@[simp] lemma efMin_denote (e f : EF) (V : History) :
    (efMin e f).denote V = min (e.denote V) (f.denote V) := by
  simp only [efMin, EF.denote_mul, EF.denote_max, EF.denote_const, Pi.mul_apply]
  push_cast
  rw [neg_one_mul, neg_one_mul, neg_one_mul, max_neg_neg, neg_neg]

@[simp] lemma clip01_denote (e : EF) (V : History) :
    (clip01 e).denote V = max 0 (min 1 (e.denote V)) := by
  simp only [clip01, EF.denote_max, efMin_denote, EF.denote_const]
  push_cast; rfl

@[simp] lemma oneMinus_rank (e : EF) : (oneMinus e).rank = e.rank := by
  simp [oneMinus, EF.rank]

@[simp] lemma efMin_rank (e f : EF) : (efMin e f).rank = Max.max e.rank f.rank := by
  simp [efMin, EF.rank]

@[simp] lemma clip01_rank (e : EF) : (clip01 e).rank = e.rank := by
  simp [clip01, EF.rank]

/-! ### Real-side clip facts -/

lemma clipVal_nonneg (x : ℝ) : 0 ≤ max 0 (min 1 x) := le_max_left _ _

lemma clipVal_le_one (x : ℝ) : max 0 (min 1 x) ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma clipVal_eq_one {x : ℝ} (h : 1 ≤ x) : max 0 (min 1 x) = 1 := by
  rw [min_eq_left h, max_eq_right (by norm_num)]

lemma clipVal_eq_zero {x : ℝ} (h : x ≤ 0) : max 0 (min 1 x) = 0 :=
  max_eq_left ((min_le_right 1 x).trans h)

lemma clipVal_pos_imp {x : ℝ} (h : 0 < max 0 (min 1 x)) : 0 < x := by
  by_contra hx
  push_neg at hx
  rw [clipVal_eq_zero hx] at h
  exact lt_irrefl _ h

/-! ## Continuous threshold indicators

The paper's continuous threshold indicator (`def:ctsind`) in two forms: at a price leaf, where
the priced sentence and day are fixed, and at an arbitrary feature. Both ramp linearly across a
band of width `δ` and are clipped to `[0,1]`; at `δ = 0` both collapse to the constant `0`,
since `1/0 = 0` in `ℚ`. -/

/-! ### At a price leaf -/

/-- Buy signal at day `n`: `1` when `Pₙφ ≤ a`, ramps to `0` at `a + δ`. -/
def buyIndEF (φ : Sentence) (a δ : ℚ) (n : ℕ) : EF :=
  clip01 (.mul (.add (.const (a + δ)) (.mul (.const (-1)) (.price φ n))) (.const (1/δ)))

/-- Sell signal at day `n`: `1` when `Pₙφ ≥ b`, ramps to `0` at `b − δ`. -/
def sellIndEF (φ : Sentence) (b δ : ℚ) (n : ℕ) : EF :=
  clip01 (.mul (.add (.price φ n) (.const (δ - b))) (.const (1/δ)))

lemma buyIndEF_denote (φ : Sentence) (a δ : ℚ) (n : ℕ) (V : History) :
    (buyIndEF φ a δ n).denote V
      = max 0 (min 1 (((a : ℝ) + δ - V n φ) * (1/(δ : ℝ)))) := by
  simp only [buyIndEF, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    EF.denote_price, Pi.mul_apply, Pi.add_apply]
  push_cast; ring_nf

lemma sellIndEF_denote (φ : Sentence) (b δ : ℚ) (n : ℕ) (V : History) :
    (sellIndEF φ b δ n).denote V
      = max 0 (min 1 ((V n φ - ((b : ℝ) - δ)) * (1/(δ : ℝ)))) := by
  simp only [sellIndEF, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    EF.denote_price, Pi.mul_apply, Pi.add_apply]
  push_cast; ring_nf

@[simp] lemma buyIndEF_rank (φ : Sentence) (a δ : ℚ) (n : ℕ) :
    (buyIndEF φ a δ n).rank = n := by
  simp [buyIndEF, EF.rank]

@[simp] lemma sellIndEF_rank (φ : Sentence) (b δ : ℚ) (n : ℕ) :
    (sellIndEF φ b δ n).rank = n := by
  simp [sellIndEF, EF.rank]

section Signals

variable {φ : Sentence} {a b δ : ℚ} {P : History} {n : ℕ}

lemma buyInd_mem (φ a δ n) (P : History) :
    0 ≤ (buyIndEF φ a δ n).denote P ∧ (buyIndEF φ a δ n).denote P ≤ 1 := by
  rw [buyIndEF_denote]; exact ⟨clipVal_nonneg _, clipVal_le_one _⟩

lemma sellInd_mem (φ b δ n) (P : History) :
    0 ≤ (sellIndEF φ b δ n).denote P ∧ (sellIndEF φ b δ n).denote P ≤ 1 := by
  rw [sellIndEF_denote]; exact ⟨clipVal_nonneg _, clipVal_le_one _⟩

lemma buyInd_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (buyIndEF φ a δ n).denote P) :
    P n φ < (a : ℝ) + δ := by
  rw [buyIndEF_denote] at h
  have := clipVal_pos_imp h
  nlinarith [mul_pos (show (0:ℝ) < 1/(δ:ℝ) by positivity) hδ]

lemma buyInd_eq_one (hδ : 0 < (δ : ℝ)) (h : P n φ < (a : ℝ)) :
    (buyIndEF φ a δ n).denote P = 1 := by
  rw [buyIndEF_denote]
  refine clipVal_eq_one ?_
  have h1 : (δ:ℝ) ≤ (a:ℝ) + δ - P n φ := by linarith
  calc (1:ℝ) = (δ:ℝ) * (1/(δ:ℝ)) := by field_simp
    _ ≤ ((a:ℝ) + δ - P n φ) * (1/(δ:ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1; positivity

lemma buyInd_eq_zero (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ)
    (h : (b : ℝ) < P n φ) : (buyIndEF φ a δ n).denote P = 0 := by
  rw [buyIndEF_denote]
  refine clipVal_eq_zero ?_
  have hδ' : (0:ℝ) < δ := hδ
  have : (a:ℝ) + δ - P n φ ≤ 0 := by nlinarith
  have h1δ : (0:ℝ) ≤ 1/(δ:ℝ) := by positivity
  nlinarith

lemma sellInd_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (sellIndEF φ b δ n).denote P) :
    (b : ℝ) - δ < P n φ := by
  rw [sellIndEF_denote] at h
  have := clipVal_pos_imp h
  nlinarith [mul_pos (show (0:ℝ) < 1/(δ:ℝ) by positivity) hδ]

lemma sellInd_eq_one (hδ : 0 < (δ : ℝ)) (h : (b : ℝ) < P n φ) :
    (sellIndEF φ b δ n).denote P = 1 := by
  rw [sellIndEF_denote]
  refine clipVal_eq_one ?_
  have h1 : (δ:ℝ) ≤ P n φ - ((b:ℝ) - δ) := by linarith
  calc (1:ℝ) = (δ:ℝ) * (1/(δ:ℝ)) := by field_simp
    _ ≤ (P n φ - ((b:ℝ) - δ)) * (1/(δ:ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1; positivity

end Signals

/-! ### At an arbitrary feature -/

/-- Buy signal on the feature `e`: `1` when `e ≤ a`, ramps to `0` at `a + δ`. -/
def buyIndF (e : EF) (a δ : ℚ) : EF :=
  clip01 (.mul (.add (.const (a + δ)) (.mul (.const (-1)) e)) (.const (1/δ)))

/-- Sell signal on the feature `e`: `1` when `e ≥ b`, ramps to `0` at `b − δ`. -/
def sellIndF (e : EF) (b δ : ℚ) : EF :=
  clip01 (.mul (.add e (.const (δ - b))) (.const (1/δ)))

lemma buyIndF_denote (e : EF) (a δ : ℚ) (V : History) :
    (buyIndF e a δ).denote V
      = max 0 (min 1 (((a : ℝ) + δ - e.denote V) * (1/(δ : ℝ)))) := by
  simp only [buyIndF, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    Pi.mul_apply, Pi.add_apply]
  push_cast; ring_nf

lemma sellIndF_denote (e : EF) (b δ : ℚ) (V : History) :
    (sellIndF e b δ).denote V
      = max 0 (min 1 ((e.denote V - ((b : ℝ) - δ)) * (1/(δ : ℝ)))) := by
  simp only [sellIndF, clip01_denote, EF.denote_mul, EF.denote_add, EF.denote_const,
    Pi.mul_apply, Pi.add_apply]
  push_cast; ring_nf

@[simp] lemma buyIndF_rank (e : EF) (a δ : ℚ) : (buyIndF e a δ).rank = e.rank := by
  simp [buyIndF, EF.rank]

@[simp] lemma sellIndF_rank (e : EF) (b δ : ℚ) : (sellIndF e b δ).rank = e.rank := by
  simp [sellIndF, EF.rank]

section SignalFacts

variable {e : EF} {a b δ : ℚ} {V : History}

lemma buyIndF_mem (e : EF) (a δ : ℚ) (V : History) :
    0 ≤ (buyIndF e a δ).denote V ∧ (buyIndF e a δ).denote V ≤ 1 := by
  rw [buyIndF_denote]; exact ⟨clipVal_nonneg _, clipVal_le_one _⟩

lemma sellIndF_mem (e : EF) (b δ : ℚ) (V : History) :
    0 ≤ (sellIndF e b δ).denote V ∧ (sellIndF e b δ).denote V ≤ 1 := by
  rw [sellIndF_denote]; exact ⟨clipVal_nonneg _, clipVal_le_one _⟩

lemma buyIndF_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (buyIndF e a δ).denote V) :
    e.denote V < (a : ℝ) + δ := by
  rw [buyIndF_denote] at h
  have := clipVal_pos_imp h
  nlinarith [mul_pos (show (0:ℝ) < 1/(δ:ℝ) by positivity) hδ]

lemma buyIndF_eq_one (hδ : 0 < (δ : ℝ)) (h : e.denote V < (a : ℝ)) :
    (buyIndF e a δ).denote V = 1 := by
  rw [buyIndF_denote]
  refine clipVal_eq_one ?_
  have h1 : (δ:ℝ) ≤ (a:ℝ) + δ - e.denote V := by linarith
  calc (1:ℝ) = (δ:ℝ) * (1/(δ:ℝ)) := by field_simp
    _ ≤ ((a:ℝ) + δ - e.denote V) * (1/(δ:ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1; positivity

lemma buyIndF_eq_zero (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ)
    (h : (b : ℝ) < e.denote V) : (buyIndF e a δ).denote V = 0 := by
  rw [buyIndF_denote]
  refine clipVal_eq_zero ?_
  have hδ' : (0:ℝ) < δ := hδ
  have : (a:ℝ) + δ - e.denote V ≤ 0 := by nlinarith
  have h1δ : (0:ℝ) ≤ 1/(δ:ℝ) := by positivity
  nlinarith

lemma sellIndF_pos_imp (hδ : 0 < (δ : ℝ)) (h : 0 < (sellIndF e b δ).denote V) :
    (b : ℝ) - δ < e.denote V := by
  rw [sellIndF_denote] at h
  have := clipVal_pos_imp h
  nlinarith [mul_pos (show (0:ℝ) < 1/(δ:ℝ) by positivity) hδ]

lemma sellIndF_eq_one (hδ : 0 < (δ : ℝ)) (h : (b : ℝ) < e.denote V) :
    (sellIndF e b δ).denote V = 1 := by
  rw [sellIndF_denote]
  refine clipVal_eq_one ?_
  have h1 : (δ:ℝ) ≤ e.denote V - ((b:ℝ) - δ) := by linarith
  calc (1:ℝ) = (δ:ℝ) * (1/(δ:ℝ)) := by field_simp
    _ ≤ (e.denote V - ((b:ℝ) - δ)) * (1/(δ:ℝ)) := by
        apply mul_le_mul_of_nonneg_right h1; positivity

/-- The `δ = 0` degenerate buy signal is identically `0`. -/
lemma buyIndF_denote_zero_delta (e : EF) (a : ℚ) (V : History) :
    (buyIndF e a 0).denote V = 0 := by
  rw [buyIndF_denote]
  norm_num

/-- The `δ = 0` degenerate sell signal is identically `0`. -/
lemma sellIndF_denote_zero_delta (e : EF) (b : ℚ) (V : History) :
    (sellIndF e b 0).denote V = 0 := by
  rw [sellIndF_denote]
  norm_num

end SignalFacts

/-! ## The arming chain

A trader that opens a position once and unwinds it gradually carries its state in a product
`Π_{i<n} (1 − sig i)` over a per-day disarm signal. The update mentions the previous state
exactly once, so the `EF` tree grows linearly in `n`; a state update that used its previous
value twice would grow exponentially, `dd:dsl` having no sharing. Rungs that start late are
padded with degenerate (`δ = 0`) indicators before their start day, so every rung's chain has
the same serialization width — the shape a doubly-indexed emission needs. -/

/-- Arming chain over a per-day disarm signal: `armChain sig n = Π_{i<n} (1 − sig i)`.
With `sig i ∈ [0,1]` it decays from `1` toward `0`, and the *shares telescope*: the total of
`armChain · sig` over any window is the drop in the chain's value. -/
def armChain (sig : ℕ → EF) : ℕ → EF
  | 0 => .const 1
  | (n + 1) => .mul (armChain sig n) (oneMinus (sig n))

lemma armChain_denote_zero (sig : ℕ → EF) (P : History) :
    (armChain sig 0).denote P = 1 := by simp [armChain]

lemma armChain_denote_succ (sig : ℕ → EF) (P : History) (n : ℕ) :
    (armChain sig (n + 1)).denote P
      = (armChain sig n).denote P * (1 - (sig n).denote P) := by
  simp [armChain, EF.denote_mul, Pi.mul_apply, oneMinus_denote]

/-- A chain of `[0,1]`-valued disarm signals stays in `[0,1]`. -/
lemma armChain_mem (sig : ℕ → EF) (P : History)
    (hs : ∀ i, 0 ≤ (sig i).denote P ∧ (sig i).denote P ≤ 1) :
    ∀ n, 0 ≤ (armChain sig n).denote P ∧ (armChain sig n).denote P ≤ 1
  | 0 => by rw [armChain_denote_zero]; norm_num
  | (n + 1) => by
      obtain ⟨ih0, ih1⟩ := armChain_mem sig P hs n
      obtain ⟨hs0, hs1⟩ := hs n
      rw [armChain_denote_succ]
      constructor
      · nlinarith
      · nlinarith

/-- Padded-start rungs stay fully armed until their start day. -/
lemma armChain_denote_of_le (sig : ℕ → EF) (P : History) {j : ℕ}
    (hpad : ∀ i < j, (sig i).denote P = 0) :
    ∀ n, n ≤ j → (armChain sig n).denote P = 1 := by
  intro n
  induction n with
  | zero => intro _; exact armChain_denote_zero sig P
  | succ n ih =>
      intro h
      rw [armChain_denote_succ, ih (by omega), hpad n (by omega)]
      ring

/-- The shares telescope: `Σ_{n ∈ [j, N)} armChain·sig = armChain j − armChain N`. -/
lemma armChain_shares_sum (sig : ℕ → EF) (P : History) {j N : ℕ} (h : j ≤ N) :
    ∑ n ∈ Finset.Ico j N, (armChain sig n).denote P * (sig n).denote P
      = (armChain sig j).denote P - (armChain sig N).denote P := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ih, armChain_denote_succ]
      ring

lemma armChain_rank (sig : ℕ → EF) (hs : ∀ i, (sig i).rank ≤ i) :
    ∀ n, (armChain sig n).rank ≤ n - 1
  | 0 => by simp [armChain]
  | (n + 1) => by
      have ih := armChain_rank sig hs n
      have hn := hs n
      simp only [armChain, EF.rank, oneMinus_rank, max_le_iff]
      omega

/-- The chain serializes as its initial `1` followed by one multiplication block per elapsed
day. Every ladder emission in the property tail is an instance of this shape. -/
lemma serialize_armChain (sig : ℕ → EF) : ∀ n,
    (armChain sig n).serialize
      = [1, Encodable.encode ((1 : ℚ))]
        ++ (List.range n).flatMap (fun i => (oneMinus (sig i)).serialize ++ [3])
  | 0 => by simp [armChain, EF.serialize]
  | (n + 1) => by
      rw [armChain]
      simp only [EF.serialize]
      rw [serialize_armChain sig n, List.range_succ, List.flatMap_append,
        List.flatMap_singleton]
      simp [List.append_assoc]

/-! ## The holdings state and the trader -/

/-- The `k`-block holdings state: `H 0 = 0`,
`H (k+1) = max (H k · (1 − sellInd k)) (buyInd k)`. Day-`n` holdings are `H (n+1)`.
The recursive branch is written first so the serialization accretes blocks in ascending
day order on one side. -/
def hystN (φ : Sentence) (a b δ : ℚ) : ℕ → EF
  | 0 => .const 0
  | (k + 1) => .max (.mul (hystN φ a b δ k) (oneMinus (sellIndEF φ b δ k)))
      (buyIndEF φ a δ k)

/-- The real holdings value `h k`. -/
noncomputable def hystH (φ : Sentence) (a b δ : ℚ) (P : History) (k : ℕ) : ℝ :=
  (hystN φ a b δ k).denote P

lemma hystH_zero (φ a b δ) (P : History) : hystH φ a b δ P 0 = 0 := by
  simp [hystH, hystN]

lemma hystH_succ (φ a b δ) (P : History) (k : ℕ) :
    hystH φ a b δ P (k + 1)
      = max (hystH φ a b δ P k * (1 - (sellIndEF φ b δ k).denote P))
          ((buyIndEF φ a δ k).denote P) := by
  simp only [hystH, hystN, EF.denote_max, EF.denote_mul, Pi.mul_apply,
    oneMinus_denote]

/-- `hystN k` references only days `< k`: rank ≤ `k − 1`. -/
lemma hystN_rank (φ a b δ) : ∀ k, (hystN φ a b δ k).rank ≤ k - 1
  | 0 => by simp [hystN]
  | (k + 1) => by
      have ih := hystN_rank φ a b δ k
      simp only [hystN, EF.rank, oneMinus_rank, sellIndEF_rank, buyIndEF_rank, max_le_iff]
      omega

section State

variable (φ : Sentence) (a b δ : ℚ) (P : History)

lemma hystH_mem : ∀ k, 0 ≤ hystH φ a b δ P k ∧ hystH φ a b δ P k ≤ 1
  | 0 => by rw [hystH_zero]; norm_num
  | (k + 1) => by
      obtain ⟨ih0, ih1⟩ := hystH_mem k
      obtain ⟨hs0, hs1⟩ := sellInd_mem φ b δ k P
      obtain ⟨hb0, hb1⟩ := buyInd_mem φ a δ k P
      rw [hystH_succ]
      constructor
      · exact le_max_of_le_right hb0
      · exact max_le (by nlinarith) hb1

variable {φ a b δ P}

/-- Fact 1: a net buy at day `k` means the buy signal fired, so `Pₖφ < a + δ`. -/
lemma hystH_incr_imp (hδ : 0 < (δ : ℝ)) {k : ℕ}
    (h : hystH φ a b δ P k < hystH φ a b δ P (k + 1)) : P k φ < (a : ℝ) + δ := by
  refine buyInd_pos_imp hδ ?_
  by_contra hb
  push_neg at hb
  have hb0 := (buyInd_mem φ a δ k P).1
  have hbz : (buyIndEF φ a δ k).denote P = 0 := le_antisymm hb hb0
  obtain ⟨ih0, ih1⟩ := hystH_mem φ a b δ P k
  obtain ⟨hs0, hs1⟩ := sellInd_mem φ b δ k P
  rw [hystH_succ, hbz] at h
  have hprod : hystH φ a b δ P k * (1 - (sellIndEF φ b δ k).denote P)
      ≤ hystH φ a b δ P k := by nlinarith
  have hprod0 : 0 ≤ hystH φ a b δ P k * (1 - (sellIndEF φ b δ k).denote P) := by nlinarith
  rw [max_eq_left hprod0] at h
  linarith

/-- Fact 2: a net sell at day `k` means the sell signal fired, so `b − δ < Pₖφ`. -/
lemma hystH_decr_imp (hδ : 0 < (δ : ℝ)) {k : ℕ}
    (h : hystH φ a b δ P (k + 1) < hystH φ a b δ P k) : (b : ℝ) - δ < P k φ := by
  refine sellInd_pos_imp hδ ?_
  by_contra hs
  push_neg at hs
  have hs0 := (sellInd_mem φ b δ k P).1
  have hsz : (sellIndEF φ b δ k).denote P = 0 := le_antisymm hs hs0
  have hle : hystH φ a b δ P k ≤ hystH φ a b δ P (k + 1) := by
    rw [hystH_succ, hsz]
    simp only [sub_zero, mul_one] at *
    exact le_max_left _ _
  linarith

/-- Fact 3 (buy side): a dip below `a` forces full holdings, `h (k+1) = 1`. -/
lemma hystH_eq_one (hδ : 0 < (δ : ℝ)) {k : ℕ} (h : P k φ < (a : ℝ)) :
    hystH φ a b δ P (k + 1) = 1 := by
  obtain ⟨ih0, ih1⟩ := hystH_mem φ a b δ P k
  obtain ⟨hs0, hs1⟩ := sellInd_mem φ b δ k P
  rw [hystH_succ, buyInd_eq_one hδ h]
  exact max_eq_right (by nlinarith)

/-- Fact 3 (sell side): a spike above `b` forces empty holdings, `h (k+1) = 0`. -/
lemma hystH_eq_zero (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ) {k : ℕ}
    (h : (b : ℝ) < P k φ) : hystH φ a b δ P (k + 1) = 0 := by
  rw [hystH_succ, buyInd_eq_zero hδ hab h, sellInd_eq_one hδ h]
  simp

end State

/-! ### The trader -/

/-- Day-`n` trade coefficient: the position change `H (n+1) − H n`. -/
def hystTradeEF (φ : Sentence) (a b δ : ℚ) (n : ℕ) : EF :=
  .add (hystN φ a b δ (n + 1)) (.mul (.const (-1)) (hystN φ a b δ n))

lemma hystTradeEF_rank (φ a b δ) (n : ℕ) : (hystTradeEF φ a b δ n).rank ≤ n := by
  have h1 := hystN_rank φ a b δ (n + 1)
  have h2 := hystN_rank φ a b δ n
  simp only [hystTradeEF, EF.rank, max_le_iff]
  omega

/-- The hysteresis trader: trades the position change on `φ` each day. -/
def hystTrader (φ : Sentence) (a b δ : ℚ) : Trader where
  strat n := { trades := [(hystTradeEF φ a b δ n, φ)]
               rank_le := by intro p hp; simp only [List.mem_singleton] at hp
                             subst hp; exact hystTradeEF_rank φ a b δ n }

/-- The day-`i` position change, as a real. -/
noncomputable def hystDelta (φ : Sentence) (a b δ : ℚ) (P : History) (i : ℕ) : ℝ :=
  hystH φ a b δ P (i + 1) - hystH φ a b δ P i

@[simp] lemma hystTradeEF_denote (φ a b δ) (P : History) (n : ℕ) :
    (hystTradeEF φ a b δ n).denote P = hystDelta φ a b δ P n := by
  simp only [hystTradeEF, EF.denote_add, EF.denote_mul, EF.denote_const, Pi.add_apply,
    Pi.mul_apply, hystDelta, hystH]
  push_cast; ring

lemma hystTrader_netWorth (φ a b δ) (P : History) (v : PCWorld) (n : ℕ) :
    (hystTrader φ a b δ).netWorth P v n
      = ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * (v.payout φ - P i φ) := by
  simp [Trader.netWorth, hystTrader, Strategy.value]

/-! ## The variation bookkeeping -/

/-- Positive variation `B₊ n = ∑_{i ≤ n} max Δᵢ 0`. -/
noncomputable def hystBpos (φ : Sentence) (a b δ : ℚ) (P : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), max (hystDelta φ a b δ P i) 0

/-- Negative variation `B₋ n = ∑_{i ≤ n} max (−Δᵢ) 0`. -/
noncomputable def hystBneg (φ : Sentence) (a b δ : ℚ) (P : History) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), max (-(hystDelta φ a b δ P i)) 0

/-- `x⁺ - x⁻ = x` in the `max`-form used by the affine serialization proofs.
(Mathlib's `posPart_sub_negPart` is the same fact in `⁺`/`⁻` notation.) -/
lemma max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : (0:ℝ) ≤ -x)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ (0:ℝ))]; ring

lemma hystDelta_sum (φ a b δ) (P : History) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i = hystH φ a b δ P (n + 1) := by
  rw [show (∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i)
      = ∑ i ∈ Finset.range (n + 1), (hystH φ a b δ P (i + 1) - hystH φ a b δ P i) from rfl,
    Finset.sum_range_sub (fun i => hystH φ a b δ P i), hystH_zero, sub_zero]

lemma hystBpos_eq (φ a b δ) (P : History) (n : ℕ) :
    hystBpos φ a b δ P n = hystBneg φ a b δ P n + hystH φ a b δ P (n + 1) := by
  have : hystBpos φ a b δ P n - hystBneg φ a b δ P n
      = ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i := by
    rw [hystBpos, hystBneg, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => max_sub_max_neg _)
  rw [hystDelta_sum] at this
  linarith

lemma hystBneg_nonneg (φ a b δ) (P : History) (n : ℕ) : 0 ≤ hystBneg φ a b δ P n :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

/-- **The master bound**: in *every* world, the net worth is at least
`(b−δ−(a+δ))·B₋ − (a+δ)`. Bounded below outright; unbounded once `B₋ → ∞`. -/
lemma hystTrader_netWorth_ge (φ : Sentence) (a b δ : ℚ) (P : History)
    (hδ : 0 < (δ : ℝ)) (ha : 0 ≤ (a : ℝ) + δ) (v : PCWorld) (n : ℕ) :
    ((b : ℝ) - δ - ((a : ℝ) + δ)) * hystBneg φ a b δ P n - ((a : ℝ) + δ)
      ≤ (hystTrader φ a b δ).netWorth P v n := by
  rw [hystTrader_netWorth]
  -- Split each term: Δᵢ(w − Pᵢ) = Δᵢw − ΔᵢPᵢ.
  have hsplit : ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * (v.payout φ - P i φ)
      = v.payout φ * hystH φ a b δ P (n + 1)
        - ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * P i φ := by
    rw [← hystDelta_sum φ a b δ P n, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit]
  -- Termwise: ΔᵢPᵢ ≤ (a+δ)·max Δᵢ 0 − (b−δ)·max (−Δᵢ) 0.
  have hterm : ∀ i, hystDelta φ a b δ P i * P i φ
      ≤ ((a : ℝ) + δ) * max (hystDelta φ a b δ P i) 0
        - ((b : ℝ) - δ) * max (-(hystDelta φ a b δ P i)) 0 := by
    intro i
    rcases lt_trichotomy (hystDelta φ a b δ P i) 0 with h | h | h
    · -- net sell: Pᵢ > b − δ (fact 2)
      have hp := hystH_decr_imp hδ (show hystH φ a b δ P (i+1) < hystH φ a b δ P i by
        have := h; rw [hystDelta] at this; linarith)
      rw [max_eq_right h.le, max_eq_left (by linarith : (0:ℝ) ≤ -(hystDelta φ a b δ P i))]
      nlinarith
    · rw [h]; simp
    · -- net buy: Pᵢ < a + δ (fact 1)
      have hp := hystH_incr_imp hδ (show hystH φ a b δ P i < hystH φ a b δ P (i+1) by
        have := h; rw [hystDelta] at this; linarith)
      rw [max_eq_left h.le, max_eq_right (by linarith : -(hystDelta φ a b δ P i) ≤ (0:ℝ))]
      nlinarith
  have hsum : ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * P i φ
      ≤ ((a : ℝ) + δ) * hystBpos φ a b δ P n - ((b : ℝ) - δ) * hystBneg φ a b δ P n := by
    calc ∑ i ∈ Finset.range (n + 1), hystDelta φ a b δ P i * P i φ
        ≤ ∑ i ∈ Finset.range (n + 1), (((a : ℝ) + δ) * max (hystDelta φ a b δ P i) 0
            - ((b : ℝ) - δ) * max (-(hystDelta φ a b δ P i)) 0) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = ((a : ℝ) + δ) * hystBpos φ a b δ P n - ((b : ℝ) - δ) * hystBneg φ a b δ P n := by
          rw [hystBpos, hystBneg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Assemble, using B₊ = B₋ + h(n+1), h ∈ [0,1], payout ≥ 0, a+δ ≥ 0.
  have hpay : 0 ≤ v.payout φ := by rw [PCWorld.payout]; split <;> norm_num
  obtain ⟨hh0, hh1⟩ := hystH_mem φ a b δ P (n + 1)
  have hBp := hystBpos_eq φ a b δ P n
  nlinarith [mul_nonneg hpay hh0]

/-! ### Unbounded downward variation under oscillation -/

section Unbounded

variable {φ : Sentence} {a b δ : ℚ} {P : History}

lemma hystBneg_mono (φ a b δ) (P : History) {n m : ℕ} (h : n ≤ m) :
    hystBneg φ a b δ P n ≤ hystBneg φ a b δ P m :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right h 1)) (fun _ _ _ => le_max_right _ _)

/-- The negative variation accumulated on `(n, m]` covers any drop in holdings. -/
lemma hystBneg_swing (φ a b δ) (P : History) {n m : ℕ} (h : n ≤ m) :
    hystH φ a b δ P (n + 1) - hystH φ a b δ P (m + 1)
      ≤ hystBneg φ a b δ P m - hystBneg φ a b δ P n := by
  have hsub : hystBneg φ a b δ P m - hystBneg φ a b δ P n
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), max (-(hystDelta φ a b δ P i)) 0 := by
    rw [hystBneg, hystBneg, eq_comm, Finset.sum_Ico_eq_sub _ (by omega)]
  have hdel : hystH φ a b δ P (m + 1) - hystH φ a b δ P (n + 1)
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), hystDelta φ a b δ P i := by
    rw [Finset.sum_Ico_eq_sub _ (by omega), hystDelta_sum, hystDelta_sum]
  have hge : ∑ i ∈ Finset.Ico (n + 1) (m + 1), (-(hystDelta φ a b δ P i))
      ≤ ∑ i ∈ Finset.Ico (n + 1) (m + 1), max (-(hystDelta φ a b δ P i)) 0 :=
    Finset.sum_le_sum (fun i _ => le_max_left _ _)
  rw [hsub]
  calc hystH φ a b δ P (n + 1) - hystH φ a b δ P (m + 1)
      = ∑ i ∈ Finset.Ico (n + 1) (m + 1), (-(hystDelta φ a b δ P i)) := by
        rw [Finset.sum_neg_distrib, ← hdel]; ring
    _ ≤ _ := hge

/-- Under two-sided oscillation the negative variation is unbounded — each full
swing (dip below `a`, then spike above `b`) adds at least `1`. -/
lemma hystBneg_unbounded (hδ : 0 < (δ : ℝ)) (hab : (a : ℝ) + δ ≤ (b : ℝ) - δ)
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∀ K : ℕ, ∃ n, (K : ℝ) ≤ hystBneg φ a b δ P n := by
  intro K
  induction K with
  | zero => exact ⟨0, by simpa using hystBneg_nonneg φ a b δ P 0⟩
  | succ K ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n₁, hn₁, hPn₁⟩ := (Filter.frequently_atTop.mp hA) (n + 1)
      obtain ⟨m₁, hm₁, hPm₁⟩ := (Filter.frequently_atTop.mp hB) (n₁ + 1)
      refine ⟨m₁, ?_⟩
      have h1 : hystH φ a b δ P (n₁ + 1) = 1 := hystH_eq_one hδ hPn₁
      have h0 : hystH φ a b δ P (m₁ + 1) = 0 := hystH_eq_zero hδ hab hPm₁
      have hswing := hystBneg_swing φ a b δ P (show n₁ ≤ m₁ by omega)
      have hmono := hystBneg_mono φ a b δ P (show n ≤ n₁ by omega)
      rw [h1, h0] at hswing
      push_cast
      linarith

end Unbounded

/-! ## Exploitation -/

/-- **The hysteresis trader exploits an oscillating market.** -/
lemma hystTrader_exploits (P : History) (DP : DeductiveProcess) (φ : Sentence)
    {a b δ : ℚ} (hδ : 0 < (δ : ℝ)) (ha : 0 ≤ (a : ℝ) + δ)
    (hab : (a : ℝ) + δ < (b : ℝ) - δ)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    (hystTrader φ a b δ).Exploits P DP := by
  set γ : ℝ := (b : ℝ) - δ - ((a : ℝ) + δ) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  refine exploits_of_bddBelow_of_unbounded _ _ _ ((a : ℝ) + δ) ?_ ?_
  · rintro x ⟨m, v, hv, rfl⟩
    have h := hystTrader_netWorth_ge φ a b δ P hδ ha v m
    have hB0 := hystBneg_nonneg φ a b δ P m
    nlinarith
  · intro B
    obtain ⟨K, hK⟩ := exists_nat_gt ((B + ((a : ℝ) + δ)) / γ)
    obtain ⟨n, hn⟩ := hystBneg_unbounded hδ hab.le hA hB K
    obtain ⟨v, hv⟩ := hcons n
    refine ⟨(hystTrader φ a b δ).netWorth P v n, ⟨n, v, hv, rfl⟩, ?_⟩
    have h := hystTrader_netWorth_ge φ a b δ P hδ ha v n
    rw [div_lt_iff₀ hγ0] at hK
    nlinarith

/-! ## Emission: the ramp closures at each stream class

`oneMinus`, `efMin` and `clip01` are transparent operator tails, so each of the four
emission classes — `PolySegStream`, `RpnSpliceStream`, `BigSpliceStream` and
`PolyTokenStream` — closes under them by the same `max`/negate composition, and a family
of indicators is emitted wherever its underlying feature family is. -/

lemma PolySegStream.serialize_oneMinus {e : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize)) :
    PolySegStream (fun n => (oneMinus (e n)).serialize) :=
  PolySegStream.serialize_add
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1))
    (PolySegStream.serialize_mul
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) he)

lemma PolySegStream.serialize_efMin {e f : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize))
    (hf : PolySegStream (fun n => (f n).serialize)) :
    PolySegStream (fun n => (efMin (e n) (f n)).serialize) :=
  PolySegStream.serialize_mul
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1)))
    (PolySegStream.serialize_max
      (PolySegStream.serialize_mul
        (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) he)
      (PolySegStream.serialize_mul
        (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) hf))

lemma PolySegStream.serialize_clip01 {e : ℕ → EF}
    (he : PolySegStream (fun n => (e n).serialize)) :
    PolySegStream (fun n => (clip01 (e n)).serialize) :=
  PolySegStream.serialize_max
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0))
    (PolySegStream.serialize_efMin
      (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 1)) he)

lemma RpnSpliceStream.serialize_oneMinus {e : ℕ → EF}
    (he : RpnSpliceStream (fun n => (e n).serialize)) :
    RpnSpliceStream (fun n => (oneMinus (e n)).serialize) :=
  RpnSpliceStream.serialize_add (RpnSpliceStream.serialize_const 1)
    (RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_const (-1)) he)

lemma RpnSpliceStream.serialize_efMin {e f : ℕ → EF}
    (he : RpnSpliceStream (fun n => (e n).serialize))
    (hf : RpnSpliceStream (fun n => (f n).serialize)) :
    RpnSpliceStream (fun n => (efMin (e n) (f n)).serialize) :=
  RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_const (-1))
    (RpnSpliceStream.serialize_max
      (RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_const (-1)) he)
      (RpnSpliceStream.serialize_mul (RpnSpliceStream.serialize_const (-1)) hf))

lemma RpnSpliceStream.serialize_clip01 {e : ℕ → EF}
    (he : RpnSpliceStream (fun n => (e n).serialize)) :
    RpnSpliceStream (fun n => (clip01 (e n)).serialize) :=
  RpnSpliceStream.serialize_max (RpnSpliceStream.serialize_const 0)
    (RpnSpliceStream.serialize_efMin (RpnSpliceStream.serialize_const 1) he)

lemma BigSpliceStream.serialize_oneMinus {e : ℕ → EF}
    (he : BigSpliceStream (fun n => (e n).serialize)) :
    BigSpliceStream (fun n => (oneMinus (e n)).serialize) :=
  BigSpliceStream.serialize_add (BigSpliceStream.serialize_const 1)
    (BigSpliceStream.serialize_mul (BigSpliceStream.serialize_const (-1)) he)

lemma BigSpliceStream.serialize_efMin {e f : ℕ → EF}
    (he : BigSpliceStream (fun n => (e n).serialize))
    (hf : BigSpliceStream (fun n => (f n).serialize)) :
    BigSpliceStream (fun n => (efMin (e n) (f n)).serialize) :=
  BigSpliceStream.serialize_mul (BigSpliceStream.serialize_const (-1))
    (BigSpliceStream.serialize_max
      (BigSpliceStream.serialize_mul (BigSpliceStream.serialize_const (-1)) he)
      (BigSpliceStream.serialize_mul (BigSpliceStream.serialize_const (-1)) hf))

lemma BigSpliceStream.serialize_clip01 {e : ℕ → EF}
    (he : BigSpliceStream (fun n => (e n).serialize)) :
    BigSpliceStream (fun n => (clip01 (e n)).serialize) :=
  BigSpliceStream.serialize_max (BigSpliceStream.serialize_const 0)
    (BigSpliceStream.serialize_efMin (BigSpliceStream.serialize_const 1) he)

lemma PolyTokenStream.serialize_oneMinus {e : ℕ → EF}
    (he : PolyTokenStream (fun m => (e m).serialize)) :
    PolyTokenStream (fun m => (oneMinus (e m)).serialize) :=
  PolyTokenStream.serialize_add (PolyTokenStream.serialize_const 1)
    (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const (-1)) he)

lemma PolyTokenStream.serialize_efMin {e f : ℕ → EF}
    (he : PolyTokenStream (fun m => (e m).serialize))
    (hf : PolyTokenStream (fun m => (f m).serialize)) :
    PolyTokenStream (fun m => (efMin (e m) (f m)).serialize) :=
  PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const (-1))
    (PolyTokenStream.serialize_max
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const (-1)) he)
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const (-1)) hf))

lemma PolyTokenStream.serialize_clip01 {e : ℕ → EF}
    (he : PolyTokenStream (fun m => (e m).serialize)) :
    PolyTokenStream (fun m => (clip01 (e m)).serialize) :=
  PolyTokenStream.serialize_max (PolyTokenStream.serialize_const 0)
    (PolyTokenStream.serialize_efMin (PolyTokenStream.serialize_const 1) he)

/-! ### The hysteresis trader's stream

The day-`n` stream decomposes into five segments — fixed head `[1,⌜0⌝]`, `n+1` fixed-width
blocks (the `H (n+1)` chain), fixed mid `[1,⌜−1⌝,1,⌜0⌝]`, `n` more blocks (the `H n`
chain), fixed tail `[3,2,6,⌜φ⌝]` — emitted by the segment-composition layer
(`PolySegStream`, `Framework/Computable.lean`). -/

lemma buyIndEF_tokenStream {f : ℕ → ℕ} {c : Nat.Partrec.Code} (hf : PolyFueled c f)
    (φ : Sentence) (a δ : ℚ) :
    PolyTokenStream (fun m => (buyIndEF φ a δ (f m)).serialize) :=
  PolyTokenStream.serialize_clip01 (PolyTokenStream.serialize_mul
    (PolyTokenStream.serialize_add (PolyTokenStream.serialize_const _)
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const _)
        (PolyTokenStream.serialize_price_comp hf φ)))
    (PolyTokenStream.serialize_const _))

/-- `buyIndEF` streams with **rung-varying constants**: the threshold and slope encodes
are poly-fueled functions of the input (the parametric-ladder case). -/
lemma buyIndEF_tokenStream_comp {af δf : ℕ → ℚ} {cj : Nat.Partrec.Code} {jf : ℕ → ℕ}
    (hj : PolyFueled cj jf) (φ : Sentence)
    (ha : ∃ c, PolyFueled c (fun m => Encodable.encode (af m + δf m)))
    (hd : ∃ c, PolyFueled c (fun m => Encodable.encode (1 / δf m))) :
    PolyTokenStream (fun m => (buyIndEF φ (af m) (δf m) (jf m)).serialize) :=
  PolyTokenStream.serialize_clip01 (PolyTokenStream.serialize_mul
    (PolyTokenStream.serialize_add (PolyTokenStream.serialize_const_comp ha)
      (PolyTokenStream.serialize_mul (PolyTokenStream.serialize_const _)
        (PolyTokenStream.serialize_price_comp hj φ)))
    (PolyTokenStream.serialize_const_comp hd))

/-- `sellIndEF` streams with rung-varying constants. -/
lemma sellIndEF_tokenStream_comp {bf δf : ℕ → ℚ} {cj : Nat.Partrec.Code} {jf : ℕ → ℕ}
    (hj : PolyFueled cj jf) (φ : Sentence)
    (hb : ∃ c, PolyFueled c (fun m => Encodable.encode (δf m - bf m)))
    (hd : ∃ c, PolyFueled c (fun m => Encodable.encode (1 / δf m))) :
    PolyTokenStream (fun m => (sellIndEF φ (bf m) (δf m) (jf m)).serialize) :=
  PolyTokenStream.serialize_clip01 (PolyTokenStream.serialize_mul
    (PolyTokenStream.serialize_add (PolyTokenStream.serialize_price_comp hj φ)
      (PolyTokenStream.serialize_const_comp hb))
    (PolyTokenStream.serialize_const_comp hd))

lemma sellIndEF_tokenStream {f : ℕ → ℕ} {c : Nat.Partrec.Code} (hf : PolyFueled c f)
    (φ : Sentence) (b δ : ℚ) :
    PolyTokenStream (fun m => (sellIndEF φ b δ (f m)).serialize) :=
  PolyTokenStream.serialize_clip01 (PolyTokenStream.serialize_mul
    (PolyTokenStream.serialize_add (PolyTokenStream.serialize_price_comp hf φ)
      (PolyTokenStream.serialize_const _))
    (PolyTokenStream.serialize_const _))

/-- The day-`j` block of the holdings chain's serialization. -/
def hystBlk (φ : Sentence) (a b δ : ℚ) (j : ℕ) : List ℕ :=
  (oneMinus (sellIndEF φ b δ j)).serialize ++ [3] ++ (buyIndEF φ a δ j).serialize ++ [4]

lemma hystBlk_tokenStream (φ : Sentence) (a b δ : ℚ) :
    PolyTokenStream (fun m => hystBlk φ a b δ m.unpair.2) := by
  show PolyTokenStream (fun m =>
    (oneMinus (sellIndEF φ b δ m.unpair.2)).serialize ++ [3]
      ++ (buyIndEF φ a δ m.unpair.2).serialize ++ [4])
  exact (((PolyTokenStream.serialize_oneMinus
      (sellIndEF_tokenStream PolyFueled.right φ b δ)).append
    (PolyTokenStream.const 3)).append
    (buyIndEF_tokenStream PolyFueled.right φ a δ)).append (PolyTokenStream.const 4)

/-- Block width is day-independent (only the leaf day-index token varies). -/
lemma hystBlk_length (φ : Sentence) (a b δ : ℚ) (j : ℕ) :
    (hystBlk φ a b δ j).length = (hystBlk φ a b δ 0).length := by
  simp [hystBlk, buyIndEF, sellIndEF, oneMinus, clip01, efMin, EF.serialize]

lemma serialize_hystN (φ : Sentence) (a b δ : ℚ) : ∀ k,
    (hystN φ a b δ k).serialize
      = [1, Encodable.encode (0:ℚ)] ++ (List.range k).flatMap (hystBlk φ a b δ)
  | 0 => by simp [hystN, EF.serialize]
  | (k + 1) => by
      rw [hystN]
      simp only [EF.serialize]
      rw [serialize_hystN φ a b δ k, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, hystBlk]
      simp [List.append_assoc]

/-- **The hysteresis trader is efficiently computable** — five-segment emission. -/
lemma hystTrader_ecTok (φ : Sentence) (a b δ : ℚ) :
    EfficientlyComputableTok (hystTrader φ a b δ) := by
  have hW : ∀ m : ℕ, (hystBlk φ a b δ m.unpair.2).length = (hystBlk φ a b δ 0).length :=
    fun m => hystBlk_length φ a b δ _
  have hW0 : 0 < (hystBlk φ a b δ 0).length := by
    norm_num [hystBlk, buyIndEF, sellIndEF, oneMinus, clip01, efMin, EF.serialize]
  have seg1 : PolySegStream (fun _ : ℕ => [1, Encodable.encode (0:ℚ)]) :=
    PolySegStream.ofTokenStream
      ((PolyTokenStream.const 1).append (PolyTokenStream.const _))
  have blocks1 := PolySegStream.blocks (hystBlk_tokenStream φ a b δ) _ hW hW0
    PolyFueled.id.succ_comp
  have seg3 : PolySegStream (fun _ : ℕ =>
      [1, Encodable.encode (-1:ℚ), 1, Encodable.encode (0:ℚ)]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 1).append
      ((PolyTokenStream.const _).append
        ((PolyTokenStream.const 1).append (PolyTokenStream.const _))))
  have blocks2 := PolySegStream.blocks (hystBlk_tokenStream φ a b δ) _ hW hW0
    PolyFueled.id
  have seg5 : PolySegStream (fun _ : ℕ => [3, 2, 6, Encodable.encode φ]) :=
    PolySegStream.ofTokenStream ((PolyTokenStream.const 3).append
      ((PolyTokenStream.const 2).append
        ((PolyTokenStream.const 6).append (PolyTokenStream.const _))))
  refine ecTok_of_segStream _ (PolySegStream.of_eq
    ((((seg1.append blocks1).append seg3).append blocks2).append seg5) ?_)
  intro n
  show _ = serializeTrades ((hystTrader φ a b δ).strat n).trades
  rw [show ((hystTrader φ a b δ).strat n).trades = [(hystTradeEF φ a b δ n, φ)] from rfl,
    serializeTrades, serializeTrades, hystTradeEF]
  simp only [EF.serialize]
  rw [serialize_hystN φ a b δ (n + 1), serialize_hystN φ a b δ n]
  simp [Nat.unpair_pair, List.append_assoc]

/-! ## The oscillation-arbitrage package -/

/-- **The oscillation-arbitrage package** (`app:con`): the trader witnessing
`oscillation_exploitable`. `δ := (b−a)/4`. -/
lemma oscillation_exploitable_hyst (P : History) (DP : DeductiveProcess) (φ : Sentence)
    (a b : ℚ) (hab : (a : ℝ) < b) (hb : ∀ n, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hA : ∃ᶠ n in atTop, P n φ < (a : ℝ)) (hB : ∃ᶠ n in atTop, (b : ℝ) < P n φ) :
    ∃ Tr : Trader, EfficientlyComputableTok Tr ∧ Tr.Exploits P DP := by
  set δ : ℚ := (b - a) / 4 with hδdef
  have hδR : ((δ : ℚ) : ℝ) = ((b : ℝ) - a) / 4 := by rw [hδdef]; push_cast; ring
  have hδ : 0 < (δ : ℝ) := by rw [hδR]; linarith
  have hgap : (a : ℝ) + δ < (b : ℝ) - δ := by rw [hδR]; linarith
  have ha : 0 ≤ (a : ℝ) + δ := by
    -- a dip day exists and prices are ≥ 0, so 0 ≤ a.
    obtain ⟨n, -, hn⟩ := (Filter.frequently_atTop.mp hA) 0
    have := (hb n).1
    linarith
  exact ⟨hystTrader φ a b δ, hystTrader_ecTok φ a b δ,
    hystTrader_exploits P DP φ hδ ha hgap hcons hA hB⟩

end LogicalInduction
