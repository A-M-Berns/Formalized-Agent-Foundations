/-
# Closure Under Conditioning (`thm:scon`)

This file begins with the exact capped conditional market from the paper and the semantic
combined deductive process.  The trader compiler is kept separate: it must translate an
arbitrary token-emitted trader through conditional contracts while controlling the cap
case by the paper's summable gate.
-/
import LogicalInduction.Properties.StrictSemimeasure
import LogicalInduction.Properties.FinitePerturbations
import LogicalInduction.Properties.TimelyLearning

namespace LogicalInduction

/-- The paper's capped conditional quote. It is `1` when the denominator is zero or when
the raw numerator is at least the denominator. -/
noncomputable def conditionalQuote (V : Valuation) (φ ψ : Sentence) : ℝ :=
  if V (φ ⋏ ψ) < V ψ then V (φ ⋏ ψ) / V ψ else 1

/-- Condition day `n` of a market on the day-`n` member of a condition sequence. -/
noncomputable def conditionedHistory (P : History) (ψ : ℕ → Sentence) : History :=
  fun n φ ↦ conditionalQuote (P n) φ (ψ n)

theorem conditionalQuote_eq_div {V : Valuation} {φ ψ : Sentence}
    (h : V (φ ⋏ ψ) < V ψ) :
    conditionalQuote V φ ψ = V (φ ⋏ ψ) / V ψ := by
  simp [conditionalQuote, h]

theorem conditionalQuote_eq_one {V : Valuation} {φ ψ : Sentence}
    (h : V ψ ≤ V (φ ⋏ ψ)) :
    conditionalQuote V φ ψ = 1 := by
  simp [conditionalQuote, not_lt.mpr h]

theorem conditionalQuote_eq_div_of_le
    {V : Valuation} {φ ψ : Sentence} (hden : 0 < V ψ)
    (h : V (φ ⋏ ψ) ≤ V ψ) :
    conditionalQuote V φ ψ = V (φ ⋏ ψ) / V ψ := by
  rcases h.eq_or_lt with heq | hlt
  · rw [conditionalQuote_eq_one heq.symm.le, heq]
    exact (div_self (ne_of_gt hden)).symm
  · exact conditionalQuote_eq_div hlt

/-- Capping really produces a probability whenever the underlying market cells lie in
`[0,1]`; no coherence relation between conjunction and condition is assumed. -/
theorem conditionalQuote_mem_Icc
    (V : Valuation) (hV : ∀ χ, 0 ≤ V χ ∧ V χ ≤ 1)
    (φ ψ : Sentence) :
    0 ≤ conditionalQuote V φ ψ ∧ conditionalQuote V φ ψ ≤ 1 := by
  by_cases h : V (φ ⋏ ψ) < V ψ
  · rw [conditionalQuote_eq_div h]
    have hden : 0 < V ψ := (hV (φ ⋏ ψ)).1.trans_lt h
    exact ⟨div_nonneg (hV (φ ⋏ ψ)).1 hden.le,
      (div_le_one hden).2 h.le⟩
  · rw [conditionalQuote_eq_one (le_of_not_gt h)]
    exact ⟨by norm_num, by norm_num⟩

theorem conditionedHistory_mem_Icc
    (P : History) (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (ψ : ℕ → Sentence) (n : ℕ) (φ : Sentence) :
    0 ≤ conditionedHistory P ψ n φ ∧ conditionedHistory P ψ n φ ≤ 1 :=
  conditionalQuote_mem_Icc (P n) (hP n) φ (ψ n)

/-! ### The summable cap gate

The paper uses `2⁻ⁿ` as its per-day loss budget.  Our token model charges for the
literal numerator and denominator of rational constants, so exponentially large
denominators are not polynomially writable.  The telescoping budget
`1 / ((n+1)(n+2))` has the same load-bearing properties—strict positivity and total
mass at most one—while retaining polynomial-size rational syntax. -/

/-- Polynomially writable summable budget for day `n`. -/
def conditioningBudget (n : ℕ) : ℚ :=
  1 / (((n + 1 : ℕ) : ℚ) * ((n + 2 : ℕ) : ℚ))

theorem conditioningBudget_pos (n : ℕ) :
    0 < (conditioningBudget n : ℝ) := by
  simp only [conditioningBudget]
  push_cast
  positivity

theorem sum_conditioningBudget (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (conditioningBudget i : ℝ)) =
      1 - 1 / (n + 2 : ℝ) := by
  induction n with
  | zero => norm_num [conditioningBudget]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [conditioningBudget]
      push_cast
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hn2 : (0 : ℝ) < n + 2 := by positivity
      have hn3 : (0 : ℝ) < n + 3 := by positivity
      field_simp [ne_of_gt hn1, ne_of_gt hn2, ne_of_gt hn3]
      ring

theorem sum_conditioningBudget_le_one (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (conditioningBudget i : ℝ)) ≤ 1 := by
  rw [sum_conditioningBudget]
  have : 0 ≤ 1 / (n + 2 : ℝ) := by positivity
  linarith

/-- Real denotation of the continuous gate used to attenuate positive buys when the raw
conditional ratio crosses the cap at one. -/
noncomputable def conditioningGateVal (δ r : ℝ) : ℝ :=
  max 0 (min 1 ((1 + δ - r) / δ))

theorem conditioningGateVal_nonneg (δ r : ℝ) :
    0 ≤ conditioningGateVal δ r :=
  le_max_left _ _

theorem conditioningGateVal_le_one (δ r : ℝ) :
    conditioningGateVal δ r ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem conditioningGateVal_eq_one {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ 1) :
    conditioningGateVal δ r = 1 := by
  apply clipVal_eq_one
  rw [le_div_iff₀ hδ]
  linarith

/-- The gate can only retain a cap-violating buy when its excess ratio is small enough;
this is the scalar estimate that pays for the translation error. -/
theorem conditioningGateVal_mul_excess_le
    {δ r : ℝ} (hδ : 0 < δ) :
    conditioningGateVal δ r * (r - 1) ≤ δ := by
  by_cases hsmall : r - 1 ≤ δ
  · have hg := conditioningGateVal_le_one δ r
    by_cases hexcess : 0 ≤ r - 1
    · exact (mul_le_of_le_one_left hexcess hg).trans hsmall
    · have hg0 := conditioningGateVal_nonneg δ r
      nlinarith
  · have harg : (1 + δ - r) / δ ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    rw [conditioningGateVal, clipVal_eq_zero harg]
    simpa using hδ.le

/-- Per-position economic inequality for the capped conditional contract.  Negative
positions are never attenuated; positive positions lose at most `|a| * δ`. -/
theorem gatedConditionalPosition_lower
    {a δ r w : ℝ} (hδ : 0 < δ) (hw : w = 0 ∨ w = 1) :
    let g := conditioningGateVal δ r
    let b := min a (a * g)
    a * (w - min 1 r) - |a| * δ ≤ b * (w - r) := by
  dsimp only
  by_cases hr : r ≤ 1
  · rw [min_eq_right hr, conditioningGateVal_eq_one hδ hr]
    simp
    positivity
  · have hr1 : 1 < r := lt_of_not_ge hr
    rw [min_eq_left hr1.le]
    by_cases ha : a ≤ 0
    · have hg0 := conditioningGateVal_nonneg δ r
      have hg1 := conditioningGateVal_le_one δ r
      rw [min_eq_left (by nlinarith)]
      rw [abs_of_nonpos ha]
      rcases hw with rfl | rfl <;> nlinarith
    · have ha0 : 0 ≤ a := le_of_not_ge ha
      have hg0 := conditioningGateVal_nonneg δ r
      have hg1 := conditioningGateVal_le_one δ r
      have hgate := conditioningGateVal_mul_excess_le hδ (r := r)
      rw [min_eq_right (by nlinarith), abs_of_nonneg ha0]
      rcases hw with rfl | rfl <;> nlinarith

namespace EF

/-- Express `1 / max(ε,e)` using the DSL's built-in `1 / max(1,·)` operation. -/
def lowerSafeRecip (e : EF) (ε : ℚ) : EF :=
  .mul (.const (1 / ε)) (.safeRecip (.mul (.const (1 / ε)) e))

theorem lowerSafeRecip_denote
    (e : EF) (P : History) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (he : (ε : ℝ) ≤ e.denote P) :
    (lowerSafeRecip e ε).denote P = (e.denote P)⁻¹ := by
  have hratio : (1 : ℝ) ≤ (1 / (ε : ℝ)) * e.denote P := by
    rw [one_div, le_inv_mul_iff₀ hε]
    simpa [mul_comm] using he
  simp only [lowerSafeRecip, EF.denote_mul, EF.denote_const,
    EF.denote_safeRecip, Pi.mul_apply]
  push_cast
  rw [max_eq_right hratio]
  field_simp [ne_of_gt hε]

/-- Expressible uncapped conditional ratio. -/
def conditionalRatioEF (ψ : Sentence) (ε : ℚ) (φ : Sentence) (day : ℕ) : EF :=
  .mul (.price (φ ⋏ ψ) day) (lowerSafeRecip (.price ψ day) ε)

theorem conditionalRatioEF_denote
    {day : ℕ} (P : History) (ψ : Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : (ε : ℝ) ≤ P day ψ) (φ : Sentence) :
    (conditionalRatioEF ψ ε φ day).denote P =
      P day (φ ⋏ ψ) / P day ψ := by
  rw [conditionalRatioEF, EF.denote_mul, Pi.mul_apply,
    lowerSafeRecip_denote (.price ψ day) P hε hden]
  simp only [EF.denote_price]
  rfl

/-- Expressible capped conditional price leaf, assuming the condition price is bounded
below by `ε`. -/
def conditionalPriceEF (ψ : Sentence) (ε : ℚ) (φ : Sentence) (day : ℕ) : EF :=
  efMin (.const 1) (conditionalRatioEF ψ ε φ day)

theorem conditionalPriceEF_denote
    {day : ℕ} (P : History) (ψ : Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : (ε : ℝ) ≤ P day ψ) (φ : Sentence) :
    (conditionalPriceEF ψ ε φ day).denote P =
      conditionalQuote (P day) φ ψ := by
  have hdenPos : 0 < P day ψ := hε.trans_le hden
  rw [conditionalPriceEF, efMin_denote]
  rw [conditionalRatioEF_denote P ψ hε hden]
  simp only [EF.denote_const]
  push_cast
  by_cases h : P day (φ ⋏ ψ) < P day ψ
  · rw [conditionalQuote_eq_div h, min_eq_right ((div_le_one hdenPos).2 h.le)]
  · rw [conditionalQuote_eq_one (le_of_not_gt h),
      min_eq_left ((one_le_div hdenPos).2 (le_of_not_gt h))]

/-- Rewrite every price leaf of an arbitrary feature to the corresponding conditional
price feature. De Bruijn sharing structure is preserved recursively. -/
def conditionPrices (ψ : ℕ → Sentence) (ε : ℚ) : EF → EF
  | .price φ day => conditionalPriceEF (ψ day) ε φ day
  | .const q => .const q
  | .add a b => .add (a.conditionPrices ψ ε) (b.conditionPrices ψ ε)
  | .mul a b => .mul (a.conditionPrices ψ ε) (b.conditionPrices ψ ε)
  | .max a b => .max (a.conditionPrices ψ ε) (b.conditionPrices ψ ε)
  | .safeRecip a => .safeRecip (a.conditionPrices ψ ε)
  | .var i => .var i
  | .letE value body =>
      .letE (value.conditionPrices ψ ε) (body.conditionPrices ψ ε)

theorem conditionalPriceEF_rank (ψ : Sentence) (ε : ℚ)
    (φ : Sentence) (day : ℕ) :
    (conditionalPriceEF ψ ε φ day).rank = day := by
  simp [conditionalPriceEF, conditionalRatioEF, lowerSafeRecip, EF.rank]

theorem conditionPrices_rank (e : EF) (ψ : ℕ → Sentence) (ε : ℚ) :
    (e.conditionPrices ψ ε).rank = e.rank := by
  induction e with
  | price φ day => exact conditionalPriceEF_rank (ψ day) ε φ day
  | const q => rfl
  | add a b iha ihb => simp [conditionPrices, EF.rank, iha, ihb]
  | mul a b iha ihb => simp [conditionPrices, EF.rank, iha, ihb]
  | max a b iha ihb => simp [conditionPrices, EF.rank, iha, ihb]
  | safeRecip a iha => simp [conditionPrices, EF.rank, iha]
  | var i => rfl
  | letE value body ihv ihb => simp [conditionPrices, EF.rank, ihv, ihb]

theorem conditionPrices_denoteWith
    (e : EF) (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ day, (ε : ℝ) ≤ P day (ψ day)) :
    ∀ ρ : List ℝ,
      (e.conditionPrices ψ ε).denoteWith ρ P =
        e.denoteWith ρ (conditionedHistory P ψ) := by
  induction e with
  | price φ day =>
      intro ρ
      exact conditionalPriceEF_denote P (ψ day) hε (hden day) φ
  | const q => intro ρ; rfl
  | add a b iha ihb => intro ρ; simp [conditionPrices, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [conditionPrices, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [conditionPrices, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [conditionPrices, iha ρ]
  | var i => intro ρ; rfl
  | letE value body ihv ihb =>
      intro ρ
      simp only [conditionPrices, EF.denoteWith_letE]
      rw [ihv ρ, ihb]

theorem conditionPrices_denote
    (e : EF) (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ day, (ε : ℝ) ≤ P day (ψ day)) :
    (e.conditionPrices ψ ε).denote P =
      e.denote (conditionedHistory P ψ) :=
  e.conditionPrices_denoteWith P ψ hε hden []

/-- Parser-transparent conditional-price substitution.  The dead binding retains the raw
source leaf, while the body is the actual conditional-price feature. -/
def retainedConditionPrices (ψ : ℕ → Sentence) (ε : ℚ) : EF → EF
  | .price φ day => .letE (.price φ day) (conditionalPriceEF (ψ day) ε φ day)
  | .const q => .const q
  | .add a b => .add (a.retainedConditionPrices ψ ε) (b.retainedConditionPrices ψ ε)
  | .mul a b => .mul (a.retainedConditionPrices ψ ε) (b.retainedConditionPrices ψ ε)
  | .max a b => .max (a.retainedConditionPrices ψ ε) (b.retainedConditionPrices ψ ε)
  | .safeRecip a => .safeRecip (a.retainedConditionPrices ψ ε)
  | .var i => .var i
  | .letE x body => .letE (x.retainedConditionPrices ψ ε)
      (body.retainedConditionPrices ψ ε)

@[simp] theorem retainedConditionPrices_rank (e : EF) (ψ : ℕ → Sentence) (ε : ℚ) :
    (e.retainedConditionPrices ψ ε).rank = e.rank := by
  induction e with
  | price φ day => simp [retainedConditionPrices, conditionalPriceEF,
      conditionalRatioEF, lowerSafeRecip, efMin, rank]
  | const q => rfl
  | add a b iha ihb => simp [retainedConditionPrices, iha, ihb]
  | mul a b iha ihb => simp [retainedConditionPrices, iha, ihb]
  | max a b iha ihb => simp [retainedConditionPrices, iha, ihb]
  | safeRecip a iha => simp [retainedConditionPrices, iha]
  | var i => rfl
  | letE x body ihx ihbody => simp [retainedConditionPrices, ihx, ihbody]

theorem retainedConditionPrices_denoteWith (e : EF) (P : History)
    (ψ : ℕ → Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d)) :
    ∀ ρ : List ℝ, (e.retainedConditionPrices ψ ε).denoteWith ρ P =
      e.denoteWith ρ (conditionedHistory P ψ) := by
  induction e with
  | price φ day =>
      intro ρ
      simp only [retainedConditionPrices, denoteWith_letE]
      exact conditionalPriceEF_denote P (ψ day) hε (hden day) φ
  | const q => intro ρ; rfl
  | add a b iha ihb => intro ρ; simp [retainedConditionPrices, iha ρ, ihb ρ]
  | mul a b iha ihb => intro ρ; simp [retainedConditionPrices, iha ρ, ihb ρ]
  | max a b iha ihb => intro ρ; simp [retainedConditionPrices, iha ρ, ihb ρ]
  | safeRecip a iha => intro ρ; simp [retainedConditionPrices, iha ρ]
  | var i => intro ρ; rfl
  | letE x body ihx ihbody =>
      intro ρ
      simp only [retainedConditionPrices, denoteWith_letE]
      rw [ihx ρ, ihbody]

theorem retainedConditionPrices_denote (e : EF) (P : History)
    (ψ : ℕ → Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d)) :
    (e.retainedConditionPrices ψ ε).denote P =
      e.denote (conditionedHistory P ψ) :=
  e.retainedConditionPrices_denoteWith P ψ hε hden []

/-- Absolute value as an expressible feature, local to the conditioning translator. -/
def absVal (e : EF) : EF :=
  .max e (.mul (.const (-1)) e)

theorem absVal_denote (e : EF) (P : History) :
    (absVal e).denote P = |e.denote P| := by
  simp only [absVal, EF.denote_max, EF.denote_mul, EF.denote_const, Pi.mul_apply]
  push_cast
  rw [neg_one_mul, abs_eq_max_neg]

@[simp] theorem absVal_rank (e : EF) :
    (absVal e).rank = e.rank := by
  simp [absVal, EF.rank]

/-- Magnitude-normalized tolerance `τ / max(1,m)`. -/
def conditioningTolerance (magnitude : EF) (τ : ℚ) : EF :=
  .mul (.const τ) (.safeRecip magnitude)

theorem conditioningTolerance_denote
    (magnitude : EF) (τ : ℚ) (P : History) :
    (conditioningTolerance magnitude τ).denote P =
      (τ : ℝ) / Max.max 1 (magnitude.denote P) := by
  simp only [conditioningTolerance, EF.denote_mul, EF.denote_const,
    EF.denote_safeRecip, Pi.mul_apply]
  rw [div_eq_mul_inv]

@[simp] theorem conditioningTolerance_rank (magnitude : EF) (τ : ℚ) :
    (conditioningTolerance magnitude τ).rank = magnitude.rank := by
  simp [conditioningTolerance, EF.rank]

/-- Continuous cap gate. It is one at raw ratios at most one, ramps linearly to zero
over the normalized tolerance, and is zero thereafter. -/
def conditioningCapGate (ratio magnitude : EF) (τ : ℚ) : EF :=
  let maxMag := EF.max (.const 1) magnitude
  let δ := conditioningTolerance magnitude τ
  clip01 (.mul
    (.add (.add (.const 1) δ) (.mul (.const (-1)) ratio))
    (.mul (.const (1 / τ)) maxMag))

theorem conditioningCapGate_denote
    (ratio magnitude : EF) (τ : ℚ) (P : History) :
    (conditioningCapGate ratio magnitude τ).denote P =
      conditioningGateVal ((τ : ℝ) / Max.max 1 (magnitude.denote P))
        (ratio.denote P) := by
  have hmax : (0 : ℝ) < Max.max 1 (magnitude.denote P) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  simp only [conditioningCapGate, clip01_denote, conditioningTolerance_denote,
    EF.denote_mul, EF.denote_add, EF.denote_const, EF.denote_max,
    Pi.mul_apply, Pi.add_apply, conditioningGateVal]
  push_cast
  congr 3
  · ring
  · rw [inv_div]
    ring

@[simp] theorem conditioningCapGate_rank (ratio magnitude : EF) (τ : ℚ) :
  (conditioningCapGate ratio magnitude τ).rank =
      Nat.max ratio.rank magnitude.rank := by
  simp [conditioningCapGate, EF.rank, Nat.max_comm]

theorem conditioningTolerance_pos
    (magnitude : EF) {τ : ℚ} (P : History) (hτ : 0 < (τ : ℝ)) :
    0 < (conditioningTolerance magnitude τ).denote P := by
  rw [conditioningTolerance_denote]
  exact div_pos hτ (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

end EF

namespace Strategy

/-- Reified magnitude of the rewritten conditional-market coefficients. -/
def conditionedMagnitudeFeature
    (ψ : ℕ → Sentence) (ε : ℚ) {day : ℕ} (T : Strategy day) : EF :=
  T.trades.foldr
    (fun p acc => EF.add (EF.absVal (p.1.conditionPrices ψ ε)) acc)
    (EF.const 0)

theorem conditionedMagnitudeFeature_denote
    {day : ℕ} (T : Strategy day) (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d)) :
    (T.conditionedMagnitudeFeature ψ ε).denote P =
      T.magnitude (conditionedHistory P ψ) := by
  simp only [conditionedMagnitudeFeature, Strategy.magnitude]
  induction T.trades with
  | nil => simp [EF.denote]
  | cons p rest ih =>
      simp only [List.foldr_cons, EF.denote_add, EF.absVal_denote,
        List.map_cons, List.sum_cons, Pi.add_apply]
      rw [p.1.conditionPrices_denote P ψ hε hden, ih]

theorem conditionedMagnitudeFeature_rank_le
    {day : ℕ} (T : Strategy day) (ψ : ℕ → Sentence) (ε : ℚ) :
    (T.conditionedMagnitudeFeature ψ ε).rank ≤ day := by
  have aux : ∀ trades : List (EF × Sentence),
      (∀ p ∈ trades, p.1.rank ≤ day) →
      (trades.foldr
        (fun p acc => EF.add (EF.absVal (p.1.conditionPrices ψ ε)) acc)
        (EF.const 0)).rank ≤ day := by
    intro trades
    induction trades with
    | nil => intro _; simp
    | cons p rest ih =>
        intro hrank
        simp only [List.foldr_cons, EF.rank_add, EF.absVal_rank]
        apply Nat.max_le.mpr
        exact ⟨(p.1.conditionPrices_rank ψ ε).le.trans
          (hrank p (List.mem_cons_self ..)),
          ih (fun q hq => hrank q (List.mem_cons_of_mem _ hq))⟩
  exact aux T.trades T.rank_le

/-- Gated version of the literal conditional contracts.  All positions share the
strategy-wide magnitude feature, so summing the per-position loss bound costs at most the
single day budget `τ`. -/
def gatedConditionalContractTrades
    (ψ : ℕ → Sentence) (ε : ℚ) (day : ℕ) (τ : ℚ) (magnitude : EF) :
    List (EF × Sentence) → List (EF × Sentence) :=
  fun trades ↦ trades.flatMap (fun p ↦
      let α := p.1.conditionPrices ψ ε
      let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
      let gate := EF.conditioningCapGate ratio magnitude τ
      let β := efMin α (EF.mul α gate)
      [(β, p.2 ⋏ ψ day),
        (EF.mul (EF.const (-1)) (EF.mul β ratio), ψ day)])

/-- Actual day strategy used by the conditioning compiler. -/
def gatedConditionalContract {day : ℕ} (ψ : ℕ → Sentence) (ε τ : ℚ)
    (T : Strategy day) : Strategy day where
  trades := gatedConditionalContractTrades ψ ε day τ
    (T.conditionedMagnitudeFeature ψ ε) T.trades
  rank_le := by
    intro out hout
    simp only [gatedConditionalContractTrades, List.mem_flatMap] at hout
    obtain ⟨p, hp, hout⟩ := hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    let α := p.1.conditionPrices ψ ε
    let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
    let magnitude := T.conditionedMagnitudeFeature ψ ε
    let gate := EF.conditioningCapGate ratio magnitude τ
    let β := efMin α (EF.mul α gate)
    have hα : α.rank ≤ day := by
      dsimp only [α]
      rw [p.1.conditionPrices_rank]
      exact T.rank_le p hp
    have hratio : ratio.rank ≤ day := by
      simp [ratio, EF.conditionalRatioEF, EF.lowerSafeRecip, EF.rank]
    have hmagnitude : magnitude.rank ≤ day := by
      exact T.conditionedMagnitudeFeature_rank_le ψ ε
    have hgate : gate.rank ≤ day := by
      rw [show gate.rank = Nat.max ratio.rank magnitude.rank by
        exact EF.conditioningCapGate_rank ratio magnitude τ]
      exact Nat.max_le.mpr ⟨hratio, hmagnitude⟩
    have hβ : β.rank ≤ day := by
      simp only [β, efMin_rank, EF.rank_mul]
      exact Nat.max_le.mpr ⟨hα, Nat.max_le.mpr ⟨hα, hgate⟩⟩
    rcases hout with rfl | rfl
    · exact hβ
    · simp only [EF.rank_mul, EF.rank_const, Nat.zero_max]
      exact Nat.max_le.mpr ⟨hβ, hratio⟩

private theorem gatedConditionalPair_lower
    {day : ℕ} (p : EF × Sentence)
    (P : History) (ψ : ℕ → Sentence) {ε τ : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (hτ : 0 < (τ : ℝ)) (magnitude : EF)
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2) -
      |p.1.denote (conditionedHistory P ψ)| *
        (EF.conditioningTolerance magnitude τ).denote P ≤
      let α := p.1.conditionPrices ψ ε
      let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
      let gate := EF.conditioningCapGate ratio magnitude τ
      let β := efMin α (EF.mul α gate)
      β.denote P * (v.payout (p.2 ⋏ ψ day) - P day (p.2 ⋏ ψ day)) +
        (EF.mul (EF.const (-1)) (EF.mul β ratio)).denote P *
          (v.payout (ψ day) - P day (ψ day)) := by
  dsimp only
  let a := p.1.denote (conditionedHistory P ψ)
  let r := P day (p.2 ⋏ ψ day) / P day (ψ day)
  let δ := (EF.conditioningTolerance magnitude τ).denote P
  let g := conditioningGateVal δ r
  let b := min a (a * g)
  have hδ : 0 < δ := EF.conditioningTolerance_pos magnitude P hτ
  have hw : v.payout p.2 = 0 ∨ v.payout p.2 = 1 := by
    by_cases hp : v.Holds p.2
    · exact Or.inr (by simp [PCWorld.payout, hp])
    · exact Or.inl (by simp [PCWorld.payout, hp])
  have hcoef : (p.1.conditionPrices ψ ε).denote P = a := by
    exact p.1.conditionPrices_denote P ψ hε hden
  have hratio :
      (EF.conditionalRatioEF (ψ day) ε p.2 day).denote P = r := by
    exact EF.conditionalRatioEF_denote P (ψ day) hε (hden day) p.2
  have hgate :
      (EF.conditioningCapGate
      (EF.conditionalRatioEF (ψ day) ε p.2 day) magnitude τ).denote P = g := by
    rw [EF.conditioningCapGate_denote, hratio,
      ← EF.conditioningTolerance_denote]
  have hbeta :
      (efMin (p.1.conditionPrices ψ ε)
        (EF.mul (p.1.conditionPrices ψ ε)
          (EF.conditioningCapGate
            (EF.conditionalRatioEF (ψ day) ε p.2 day) magnitude τ))).denote P = b := by
    simp only [efMin_denote, EF.denote_mul, Pi.mul_apply, hcoef, hgate]
    rfl
  have hquote : conditionedHistory P ψ day p.2 = min 1 r := by
    simp only [conditionedHistory]
    rw [← EF.conditionalPriceEF_denote P (ψ day) hε (hden day) p.2]
    simp only [EF.conditionalPriceEF, efMin_denote, EF.denote_const, hratio]
    push_cast
    rfl
  have hpayoutψ : v.payout (ψ day) = 1 := by
    simp [PCWorld.payout, hψ]
  have hpayoutAnd : v.payout (p.2 ⋏ ψ day) = v.payout p.2 := by
    by_cases hp : v.Holds p.2 <;>
      simp [PCWorld.payout, PCWorld.holds_and, hψ, hp]
  have hdenPos : 0 < P day (ψ day) := hε.trans_le (hden day)
  have hrden : r * P day (ψ day) = P day (p.2 ⋏ ψ day) := by
    dsimp only [r]
    field_simp [ne_of_gt hdenPos]
  have hscalar := gatedConditionalPosition_lower
    (a := a) (δ := δ) (r := r) (w := v.payout p.2) hδ hw
  dsimp only at hscalar
  rw [hbeta, hpayoutψ, hpayoutAnd, hquote]
  simp only [EF.denote_mul, EF.denote_const, Pi.mul_apply]
  rw [hbeta, hratio]
  push_cast
  dsimp only [a, δ, g, b] at hscalar ⊢
  exact hscalar.trans_eq (by
    rw [← hrden]
    ring)

private theorem gatedConditionalContractTrades_value_lower
    {day : ℕ} (trades : List (EF × Sentence))
    (P : History) (ψ : ℕ → Sentence) {ε τ : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (hτ : 0 < (τ : ℝ)) (magnitude : EF)
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    (trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2))).sum -
      (trades.map (fun p ↦
        |p.1.denote (conditionedHistory P ψ)|)).sum *
        (EF.conditioningTolerance magnitude τ).denote P ≤
      ((gatedConditionalContractTrades ψ ε day τ magnitude trades).map
        (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum := by
  induction trades with
  | nil => simp [gatedConditionalContractTrades]
  | cons p rest ih =>
      have hp := gatedConditionalPair_lower p P ψ hε hden hτ magnitude v hψ
      rw [gatedConditionalContractTrades] at ih
      rw [gatedConditionalContractTrades, List.flatMap_cons,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
      nlinarith

/-- The concrete gated day translation tracks the conditional-market strategy from
below, losing at most the polynomially writable summable budget for that day. -/
theorem gatedConditionalContract_value_lower
    {day : ℕ} (T : Strategy day)
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    T.value (conditionedHistory P ψ) v.payout -
        (conditioningBudget day : ℝ) ≤
      (T.gatedConditionalContract ψ ε (conditioningBudget day)).value P v.payout := by
  let magnitude := T.conditionedMagnitudeFeature ψ ε
  let τ := conditioningBudget day
  have hτ : 0 < (τ : ℝ) := conditioningBudget_pos day
  have hlist := gatedConditionalContractTrades_value_lower T.trades P ψ
    hε hden hτ magnitude v hψ
  have hmag : magnitude.denote P = T.magnitude (conditionedHistory P ψ) := by
    exact T.conditionedMagnitudeFeature_denote P ψ hε hden
  have hM0 : 0 ≤ T.magnitude (conditionedHistory P ψ) :=
    T.magnitude_nonneg (conditionedHistory P ψ)
  have hmaxPos : (0 : ℝ) < Max.max 1 (T.magnitude (conditionedHistory P ψ)) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hMmax : T.magnitude (conditionedHistory P ψ) ≤
      Max.max 1 (T.magnitude (conditionedHistory P ψ)) :=
    le_max_right _ _
  have hdiv : T.magnitude (conditionedHistory P ψ) /
      Max.max 1 (T.magnitude (conditionedHistory P ψ)) ≤ 1 :=
    (div_le_one hmaxPos).2 hMmax
  have herror :
      T.magnitude (conditionedHistory P ψ) *
          (EF.conditioningTolerance magnitude τ).denote P ≤ (τ : ℝ) := by
    rw [EF.conditioningTolerance_denote, hmag]
    calc
      T.magnitude (conditionedHistory P ψ) *
          ((τ : ℝ) / Max.max 1 (T.magnitude (conditionedHistory P ψ))) =
          (τ : ℝ) *
            (T.magnitude (conditionedHistory P ψ) /
              Max.max 1 (T.magnitude (conditionedHistory P ψ))) := by ring
      _ ≤ (τ : ℝ) * 1 := mul_le_mul_of_nonneg_left hdiv hτ.le
      _ = (τ : ℝ) := mul_one _
  change
    (T.trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
      (v.payout p.2 - conditionedHistory P ψ day p.2))).sum - (τ : ℝ) ≤
      ((gatedConditionalContractTrades ψ ε day τ magnitude T.trades).map
        (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum
  calc
    _ ≤ (T.trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
          (v.payout p.2 - conditionedHistory P ψ day p.2))).sum -
        T.magnitude (conditionedHistory P ψ) *
          (EF.conditioningTolerance magnitude τ).denote P :=
      sub_le_sub_left herror _
    _ = (T.trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
          (v.payout p.2 - conditionedHistory P ψ day p.2))).sum -
        (T.trades.map (fun p ↦
          |p.1.denote (conditionedHistory P ψ)|)).sum *
          (EF.conditioningTolerance magnitude τ).denote P := by
      rfl
    _ ≤ _ := hlist

private theorem gatedConditionalContractTrades_value_zero
    {day : ℕ} (trades : List (EF × Sentence))
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (τ : ℚ) (magnitude : EF) (v : PCWorld)
    (hψ : ¬v.Holds (ψ day)) :
    ((gatedConditionalContractTrades ψ ε day τ magnitude trades).map
      (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum = 0 := by
  induction trades with
  | nil => simp [gatedConditionalContractTrades]
  | cons p rest ih =>
      have hdenPos : 0 < P day (ψ day) := hε.trans_le (hden day)
      have hratio := EF.conditionalRatioEF_denote P (ψ day) hε (hden day) p.2
      have hpayoutψ : v.payout (ψ day) = 0 := by
        simp [PCWorld.payout, hψ]
      have hpayoutAnd : v.payout (p.2 ⋏ ψ day) = 0 := by
        simp [PCWorld.payout, PCWorld.holds_and, hψ]
      rw [gatedConditionalContractTrades] at ih
      rw [gatedConditionalContractTrades, List.flatMap_cons,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        add_zero, EF.denote_mul, EF.denote_const, Pi.mul_apply]
      rw [ih, hpayoutψ, hpayoutAnd, hratio]
      push_cast
      field_simp [ne_of_gt hdenPos]
      ring

/-- Once the growing condition is false in a world, every gated conditional contract on
that day has exactly zero value there—including its cash term. -/
theorem gatedConditionalContract_value_eq_zero_of_not_holds
    {day : ℕ} (T : Strategy day)
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (τ : ℚ) (v : PCWorld) (hψ : ¬v.Holds (ψ day)) :
    (T.gatedConditionalContract ψ ε τ).value P v.payout = 0 := by
  exact gatedConditionalContractTrades_value_zero T.trades P ψ hε hden τ
    (T.conditionedMagnitudeFeature ψ ε) v hψ

/-! ### Locally normalized gate

The strategy-wide magnitude above is convenient analytically but expensive to serialize:
every output coefficient repeats the whole input strategy.  The compiler uses the equivalent
per-position allocation below.  A list of `k` positions gives each position budget `τ/k`
and normalizes it by that position's own magnitude, so the errors still sum to at most `τ`.
-/

def localConditioningBudget (τ : ℚ) (count : ℕ) : ℚ := τ / (count : ℚ)

def locallyGatedConditionalContractTrades
    (ψ : ℕ → Sentence) (ε : ℚ) (day : ℕ) (τ : ℚ) (count : ℕ) :
    List (EF × Sentence) → List (EF × Sentence) :=
  fun trades ↦ trades.flatMap (fun p ↦
      let α := p.1.conditionPrices ψ ε
      let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
      let magnitude := EF.absVal α
      let gate := EF.conditioningCapGate ratio magnitude
        (localConditioningBudget τ count)
      let β := efMin α (EF.mul α gate)
      [(β, p.2 ⋏ ψ day),
        (EF.mul (EF.const (-1)) (EF.mul β ratio), ψ day)])

def locallyGatedConditionalContract {day : ℕ} (ψ : ℕ → Sentence) (ε τ : ℚ)
    (T : Strategy day) : Strategy day where
  trades := locallyGatedConditionalContractTrades ψ ε day τ T.trades.length T.trades
  rank_le := by
    intro out hout
    simp only [locallyGatedConditionalContractTrades, List.mem_flatMap] at hout
    obtain ⟨p, hp, hout⟩ := hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    let α := p.1.conditionPrices ψ ε
    let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
    let magnitude := EF.absVal α
    let gate := EF.conditioningCapGate ratio magnitude
      (localConditioningBudget τ T.trades.length)
    let β := efMin α (EF.mul α gate)
    have hα : α.rank ≤ day := by
      dsimp only [α]
      rw [p.1.conditionPrices_rank]
      exact T.rank_le p hp
    have hratio : ratio.rank ≤ day := by
      simp [ratio, EF.conditionalRatioEF, EF.lowerSafeRecip, EF.rank]
    have hmagnitude : magnitude.rank ≤ day := by
      simpa [magnitude] using hα
    have hgate : gate.rank ≤ day := by
      rw [show gate.rank = Nat.max ratio.rank magnitude.rank by
        exact EF.conditioningCapGate_rank ratio magnitude _]
      exact Nat.max_le.mpr ⟨hratio, hmagnitude⟩
    have hβ : β.rank ≤ day := by
      simp only [β, efMin_rank, EF.rank_mul]
      exact Nat.max_le.mpr ⟨hα, Nat.max_le.mpr ⟨hα, hgate⟩⟩
    rcases hout with rfl | rfl
    · exact hβ
    · simp only [EF.rank_mul, EF.rank_const, Nat.zero_max]
      exact Nat.max_le.mpr ⟨hβ, hratio⟩

/-- First output leg of the locally normalized conditioning compiler. -/
def locallyGatedFirstLeg (ψ : ℕ → Sentence) (ε : ℚ) (day : ℕ)
    (τ : ℚ) (count : ℕ) (p : EF × Sentence) : EF × Sentence :=
  let α := p.1.retainedConditionPrices ψ ε
  let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
  let bound := EF.var 0
  let magnitude := EF.absVal bound
  let gate := EF.conditioningCapGate ratio magnitude
    (localConditioningBudget τ count)
  let β := efMin bound (EF.mul bound gate)
  (EF.letE α β, p.2 ⋏ ψ day)

/-- Second output leg of the locally normalized conditioning compiler. -/
def locallyGatedSecondLeg (ψ : ℕ → Sentence) (ε : ℚ) (day : ℕ)
    (τ : ℚ) (count : ℕ) (p : EF × Sentence) : EF × Sentence :=
  let α := p.1.retainedConditionPrices ψ ε
  let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
  let bound := EF.var 0
  let magnitude := EF.absVal bound
  let gate := EF.conditioningCapGate ratio magnitude
    (localConditioningBudget τ count)
  let β := efMin bound (EF.mul bound gate)
  (EF.letE α (EF.mul (EF.const (-1)) (EF.mul β ratio)), ψ day)

/-- Compiler-order form of the locally gated contract.  It emits all first legs and then
all second legs, allowing two parser-transparent passes over an arbitrary raw certificate. -/
def separatedLocallyGatedConditionalContract {day : ℕ}
    (ψ : ℕ → Sentence) (ε τ : ℚ) (T : Strategy day) : Strategy day where
  trades :=
    T.trades.map (locallyGatedFirstLeg ψ ε day τ T.trades.length) ++
    T.trades.map (locallyGatedSecondLeg ψ ε day τ T.trades.length)
  rank_le := by
    intro out hout
    rw [List.mem_append, List.mem_map, List.mem_map] at hout
    rcases hout with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · have hα : (p.1.retainedConditionPrices ψ ε).rank ≤ day := by
        rw [p.1.retainedConditionPrices_rank]
        exact T.rank_le p hp
      have hr : (EF.conditionalRatioEF (ψ day) ε p.2 day).rank ≤ day := by
        simp [EF.conditionalRatioEF, EF.lowerSafeRecip, EF.rank]
      simpa [locallyGatedFirstLeg, EF.rank, EF.conditioningCapGate_rank, hα, hr]
        using T.rank_le p hp
    · have hα : (p.1.retainedConditionPrices ψ ε).rank ≤ day := by
        rw [p.1.retainedConditionPrices_rank]
        exact T.rank_le p hp
      have hr : (EF.conditionalRatioEF (ψ day) ε p.2 day).rank ≤ day := by
        simp [EF.conditionalRatioEF, EF.lowerSafeRecip, EF.rank]
      simpa [locallyGatedSecondLeg, EF.rank, EF.conditioningCapGate_rank, hα, hr]
        using T.rank_le p hp

theorem separatedLocallyGatedConditionalContract_value
    {day : ℕ} (ψ : ℕ → Sentence) (ε τ : ℚ) (T : Strategy day)
    (P : History) (w : Valuation) (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d)) :
    (T.separatedLocallyGatedConditionalContract ψ ε τ).value P w =
      (T.locallyGatedConditionalContract ψ ε τ).value P w := by
  let value : EF × Sentence → ℝ := fun p ↦
    p.1.denote P * (w p.2 - P day p.2)
  have hsum (count : ℕ) (trades : List (EF × Sentence)) :
      (trades.map (locallyGatedFirstLeg ψ ε day τ count) |>.map value).sum +
        (trades.map (locallyGatedSecondLeg ψ ε day τ count) |>.map value).sum =
      (locallyGatedConditionalContractTrades ψ ε day τ count trades
        |>.map value).sum := by
    induction trades with
    | nil => simp [locallyGatedConditionalContractTrades]
    | cons p rest ih =>
        simp only [List.map_cons, List.sum_cons, locallyGatedConditionalContractTrades,
          List.flatMap_cons, List.map_append, List.sum_append]
        calc
          value (locallyGatedFirstLeg ψ ε day τ count p) +
                (rest.map (locallyGatedFirstLeg ψ ε day τ count) |>.map value).sum +
              (value (locallyGatedSecondLeg ψ ε day τ count p) +
                (rest.map (locallyGatedSecondLeg ψ ε day τ count) |>.map value).sum) =
            value (locallyGatedFirstLeg ψ ε day τ count p) +
              value (locallyGatedSecondLeg ψ ε day τ count p) +
              ((rest.map (locallyGatedFirstLeg ψ ε day τ count) |>.map value).sum +
                (rest.map (locallyGatedSecondLeg ψ ε day τ count) |>.map value).sum) := by
                  ring
          _ = value (locallyGatedFirstLeg ψ ε day τ count p) +
              value (locallyGatedSecondLeg ψ ε day τ count p) +
              (locallyGatedConditionalContractTrades ψ ε day τ count rest
                |>.map value).sum := by rw [ih]
          _ = _ := by
            have hp : (p.1.retainedConditionPrices ψ ε).denote P =
                (p.1.conditionPrices ψ ε).denote P := by
              rw [p.1.retainedConditionPrices_denote P ψ hε hden,
                p.1.conditionPrices_denote P ψ hε hden]
            change (p.1.retainedConditionPrices ψ ε).denoteWith [] P =
              (p.1.conditionPrices ψ ε).denoteWith [] P at hp
            simp only [locallyGatedFirstLeg, locallyGatedSecondLeg, value,
              EF.denote, EF.denoteWith_letE]
            rw [hp]
            simp [locallyGatedFirstLeg, locallyGatedSecondLeg,
              locallyGatedConditionalContractTrades, value, EF.denote,
              EF.denoteWith, EF.conditioningCapGate, EF.conditioningTolerance,
              EF.absVal, EF.conditionalRatioEF, EF.lowerSafeRecip, efMin,
              clip01, List.getD, hp]
  simpa only [Strategy.value, separatedLocallyGatedConditionalContract,
    locallyGatedConditionalContract, List.map_append, List.sum_append, List.map_map,
    Function.comp_apply] using hsum T.trades.length T.trades

private theorem locallyGatedConditionalPair_lower
    {day count : ℕ} (p : EF × Sentence)
    (P : History) (ψ : ℕ → Sentence) {ε τ : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (hτ : 0 < (τ : ℝ)) (hcount : 0 < count)
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2) -
      (localConditioningBudget τ count : ℝ) ≤
      let α := p.1.conditionPrices ψ ε
      let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
      let magnitude := EF.absVal α
      let gate := EF.conditioningCapGate ratio magnitude
        (localConditioningBudget τ count)
      let β := efMin α (EF.mul α gate)
      β.denote P * (v.payout (p.2 ⋏ ψ day) - P day (p.2 ⋏ ψ day)) +
        (EF.mul (EF.const (-1)) (EF.mul β ratio)).denote P *
          (v.payout (ψ day) - P day (ψ day)) := by
  let α := p.1.conditionPrices ψ ε
  let magnitude := EF.absVal α
  let positionBudget := localConditioningBudget τ count
  have hposition : 0 < (positionBudget : ℝ) := by
    simp only [positionBudget, localConditioningBudget]
    push_cast
    exact div_pos hτ (by positivity)
  have hpair := gatedConditionalPair_lower p P ψ hε hden hposition magnitude v hψ
  have hα : α.denote P = p.1.denote (conditionedHistory P ψ) :=
    p.1.conditionPrices_denote P ψ hε hden
  have hmag : magnitude.denote P =
      |p.1.denote (conditionedHistory P ψ)| := by
    simp [magnitude, EF.absVal_denote, hα]
  have hmaxPos : (0 : ℝ) < Max.max 1 (magnitude.denote P) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hratio : magnitude.denote P / Max.max 1 (magnitude.denote P) ≤ 1 :=
    (div_le_one hmaxPos).2 (le_max_right _ _)
  have hratio' : |p.1.denote (conditionedHistory P ψ)| /
      Max.max 1 |p.1.denote (conditionedHistory P ψ)| ≤ 1 := by
    simpa only [hmag] using hratio
  have hmagnitude :
      |p.1.denote (conditionedHistory P ψ)| *
          (EF.conditioningTolerance magnitude positionBudget).denote P ≤
        (positionBudget : ℝ) := by
    rw [EF.conditioningTolerance_denote, hmag]
    calc
      |p.1.denote (conditionedHistory P ψ)| *
          ((positionBudget : ℝ) /
            Max.max 1 |p.1.denote (conditionedHistory P ψ)|) =
          (positionBudget : ℝ) *
            (|p.1.denote (conditionedHistory P ψ)| /
              Max.max 1 |p.1.denote (conditionedHistory P ψ)|) := by ring
      _ ≤ (positionBudget : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hratio' hposition.le
      _ = (positionBudget : ℝ) := mul_one _
  dsimp only [α, magnitude, positionBudget] at hpair ⊢
  exact (sub_le_sub_left hmagnitude _).trans hpair

private theorem locallyGatedConditionalContractTrades_value_lower
    {day count : ℕ} (trades : List (EF × Sentence))
    (P : History) (ψ : ℕ → Sentence) {ε τ : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (hτ : 0 < (τ : ℝ)) (hcount : 0 < count)
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    (trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2))).sum -
      trades.length * (localConditioningBudget τ count : ℝ) ≤
      ((locallyGatedConditionalContractTrades ψ ε day τ count trades).map
        (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum := by
  induction trades with
  | nil => simp [locallyGatedConditionalContractTrades]
  | cons p rest ih =>
      have hp := locallyGatedConditionalPair_lower p P ψ hε hden hτ hcount v hψ
      rw [locallyGatedConditionalContractTrades] at ih
      rw [locallyGatedConditionalContractTrades, List.flatMap_cons,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_zero]
      nlinarith

theorem locallyGatedConditionalContract_value_lower
    {day : ℕ} (T : Strategy day)
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    T.value (conditionedHistory P ψ) v.payout -
        (conditioningBudget day : ℝ) ≤
      (T.locallyGatedConditionalContract ψ ε (conditioningBudget day)).value P
        v.payout := by
  by_cases hempty : T.trades = []
  · have hτ0 : 0 ≤ (conditioningBudget day : ℝ) :=
      (conditioningBudget_pos day).le
    simp [Strategy.value, locallyGatedConditionalContract,
      locallyGatedConditionalContractTrades, hempty, hτ0]
  · have hcount : 0 < T.trades.length := List.length_pos_iff.mpr hempty
    have hτ : 0 < (conditioningBudget day : ℝ) := conditioningBudget_pos day
    have hlist := locallyGatedConditionalContractTrades_value_lower T.trades P ψ
      hε hden hτ hcount v hψ
    have hcancel : (T.trades.length : ℝ) *
        (localConditioningBudget (conditioningBudget day) T.trades.length : ℝ) =
          (conditioningBudget day : ℝ) := by
      simp only [localConditioningBudget]
      push_cast
      field_simp
    change
      (T.trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2))).sum -
          (conditioningBudget day : ℝ) ≤
        ((locallyGatedConditionalContractTrades ψ ε day (conditioningBudget day)
          T.trades.length T.trades).map
            (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum
    rw [← hcancel]
    exact hlist

private theorem locallyGatedConditionalContractTrades_value_zero
    {day count : ℕ} (trades : List (EF × Sentence))
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (τ : ℚ) (v : PCWorld) (hψ : ¬v.Holds (ψ day)) :
    ((locallyGatedConditionalContractTrades ψ ε day τ count trades).map
      (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum = 0 := by
  induction trades with
  | nil => simp [locallyGatedConditionalContractTrades]
  | cons p rest ih =>
      have hdenPos : 0 < P day (ψ day) := hε.trans_le (hden day)
      have hratio := EF.conditionalRatioEF_denote P (ψ day) hε (hden day) p.2
      have hpayoutψ : v.payout (ψ day) = 0 := by
        simp [PCWorld.payout, hψ]
      have hpayoutAnd : v.payout (p.2 ⋏ ψ day) = 0 := by
        simp [PCWorld.payout, PCWorld.holds_and, hψ]
      rw [locallyGatedConditionalContractTrades] at ih
      rw [locallyGatedConditionalContractTrades, List.flatMap_cons,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        add_zero, EF.denote_mul, EF.denote_const, Pi.mul_apply]
      rw [ih, hpayoutψ, hpayoutAnd, hratio]
      push_cast
      field_simp [ne_of_gt hdenPos]
      ring

theorem locallyGatedConditionalContract_value_eq_zero_of_not_holds
    {day : ℕ} (T : Strategy day)
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (τ : ℚ) (v : PCWorld) (hψ : ¬v.Holds (ψ day)) :
    (T.locallyGatedConditionalContract ψ ε τ).value P v.payout = 0 := by
  exact locallyGatedConditionalContractTrades_value_zero T.trades P ψ hε hden τ v hψ

/-- Replace one conditional-market position by the literal two-stock conditional
contract against the base market. -/
def conditionalContractTrades
    (ψ : ℕ → Sentence) (ε : ℚ) (day : ℕ) :
    List (EF × Sentence) → List (EF × Sentence) :=
  fun trades ↦ trades.flatMap (fun p ↦
      let α := p.1.conditionPrices ψ ε
      let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
      [(α, p.2 ⋏ ψ day),
        (EF.mul (EF.const (-1)) (EF.mul α ratio), ψ day)])

/-- Cap-free core of the Appendix trader translation. Each original trade becomes an
exact conditional contract; the later continuous gate only modifies positive positions
on days where conjunction monotonicity is violated. -/
def conditionalContract {day : ℕ} (ψ : ℕ → Sentence) (ε : ℚ)
    (T : Strategy day) : Strategy day where
  trades := conditionalContractTrades ψ ε day T.trades
  rank_le := by
    intro p hp
    simp only [conditionalContractTrades, List.mem_flatMap] at hp
    obtain ⟨q, hq, hp⟩ := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rw [q.1.conditionPrices_rank]
      exact T.rank_le q hq
    · simp only [EF.rank_mul, EF.rank_const, Nat.zero_max]
      rw [q.1.conditionPrices_rank]
      exact max_le (T.rank_le q hq) (by
        simp [EF.conditionalRatioEF, EF.lowerSafeRecip, EF.rank])

private theorem conditionalContractTrades_value
    {day : ℕ} (trades : List (EF × Sentence))
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (v : PCWorld) (hψ : v.Holds (ψ day))
    (hmono : ∀ p ∈ trades, P day (p.2 ⋏ ψ day) ≤ P day (ψ day)) :
    ((conditionalContractTrades ψ ε day trades).map (fun p ↦
      p.1.denote P * (v.payout p.2 - P day p.2))).sum =
    (trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
      (v.payout p.2 - conditionedHistory P ψ day p.2))).sum := by
  induction trades with
  | nil => simp [conditionalContractTrades]
  | cons p rest ih =>
      have hdenPos : 0 < P day (ψ day) := hε.trans_le (hden day)
      have hquote := conditionalQuote_eq_div_of_le hdenPos (hmono p (by simp))
      have hratio := EF.conditionalRatioEF_denote P (ψ day) hε (hden day) p.2
      have hcoef := p.1.conditionPrices_denote P ψ hε hden
      have hpayoutψ : v.payout (ψ day) = 1 := by
        rw [PCWorld.payout, if_pos hψ]
      have hpayoutAnd : v.payout (p.2 ⋏ ψ day) = v.payout p.2 := by
        by_cases hp : v.Holds p.2 <;>
          simp [PCWorld.payout, PCWorld.holds_and, hψ, hp]
      have iht := ih (fun q hq ↦ hmono q (by simp [hq]))
      rw [conditionalContractTrades] at iht
      simp only [conditionedHistory] at iht
      simp only [conditionedHistory]
      rw [conditionalContractTrades, List.flatMap_cons,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons, EF.denote_mul, EF.denote_const,
        Pi.mul_apply, List.map_nil, List.sum_nil, add_zero]
      rw [iht, hcoef, hratio,
        hpayoutψ, hpayoutAnd, hquote]
      push_cast
      field_simp [ne_of_gt hdenPos]
      ring

/-- In a world satisfying the day condition, and outside the cap-violation case, the
literal conditional-contract strategy has exactly the original strategy's value against
the capped conditional market. -/
theorem conditionalContract_value
    {day : ℕ} (T : Strategy day)
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (v : PCWorld) (hψ : v.Holds (ψ day))
    (hmono : ∀ p ∈ T.trades,
      P day (p.2 ⋏ ψ day) ≤ P day (ψ day)) :
    (T.conditionalContract ψ ε).value P v.payout =
      T.value (conditionedHistory P ψ) v.payout := by
  exact conditionalContractTrades_value T.trades P ψ hε hden v hψ hmono

end Strategy

namespace Trader

/-- Pointwise gated translation of a conditional-market trader. -/
def conditionedTranslation (ψ : ℕ → Sentence) (ε : ℚ) (T : Trader) : Trader where
  strat n := (T.strat n).separatedLocallyGatedConditionalContract
    ψ ε (conditioningBudget n)

/-- Summing the day estimates costs at most one in every world satisfying all conditions
through the assessment day. -/
theorem conditionedTranslation_netWorth_lower
    (T : Trader) (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (v : PCWorld) (n : ℕ)
    (hψ : ∀ i, i ≤ n → v.Holds (ψ i)) :
    T.netWorth (conditionedHistory P ψ) v n - 1 ≤
      (T.conditionedTranslation ψ ε).netWorth P v n := by
  have hday : ∀ i ∈ Finset.range (n + 1),
      (T.strat i).value (conditionedHistory P ψ) v.payout -
          (conditioningBudget i : ℝ) ≤
        ((T.conditionedTranslation ψ ε).strat i).value P v.payout := by
    intro i hi
    change (T.strat i).value (conditionedHistory P ψ) v.payout -
        (conditioningBudget i : ℝ) ≤
      ((T.strat i).separatedLocallyGatedConditionalContract ψ ε
        (conditioningBudget i)).value P v.payout
    rw [Strategy.separatedLocallyGatedConditionalContract_value
      ψ ε (conditioningBudget i) (T.strat i) P v.payout hε hden]
    apply Strategy.locallyGatedConditionalContract_value_lower
      (T.strat i) P ψ hε hden v
    exact hψ i (by simp only [Finset.mem_range] at hi; omega)
  have hsum := Finset.sum_le_sum hday
  have hbudget := sum_conditioningBudget_le_one n
  simp only [Trader.netWorth, conditionedTranslation]
  calc
    (∑ i ∈ Finset.range (n + 1),
        (T.strat i).value (conditionedHistory P ψ) v.payout) - 1 ≤
      (∑ i ∈ Finset.range (n + 1),
        (T.strat i).value (conditionedHistory P ψ) v.payout) -
          ∑ i ∈ Finset.range (n + 1), (conditioningBudget i : ℝ) :=
      sub_le_sub_left hbudget _
    _ = ∑ i ∈ Finset.range (n + 1),
        ((T.strat i).value (conditionedHistory P ψ) v.payout -
          (conditioningBudget i : ℝ)) := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((T.strat i).separatedLocallyGatedConditionalContract ψ ε
          (conditioningBudget i)).value P v.payout := hsum

end Trader

namespace DeductiveProcess

/-- Stagewise union of two deductive processes. -/
def union (DP extra : DeductiveProcess) : DeductiveProcess where
  D n := DP.D n ∪ extra.D n
  mono n := by
    intro φ hφ
    simp only [Finset.mem_union] at hφ ⊢
    exact hφ.elim (fun h ↦ Or.inl (DP.mono n h))
      (fun h ↦ Or.inr (extra.mono n h))

@[simp] theorem union_stage (DP extra : DeductiveProcess) (n : ℕ) :
    (DP.union extra).D n = DP.D n ∪ extra.D n := rfl

end DeductiveProcess

theorem PCWorld.consistentWith_union_iff
    (v : PCWorld) (DP extra : DeductiveProcess) (n : ℕ) :
    v.ConsistentWith ((DP.union extra).D n) ↔
      v.ConsistentWith (DP.D n) ∧ v.ConsistentWith (extra.D n) := by
  constructor
  · intro h
    constructor
    · intro φ hφ
      exact h φ (Finset.mem_union_left _ hφ)
    · intro φ hφ
      exact h φ (Finset.mem_union_right _ hφ)
  · rintro ⟨hDP, hextra⟩ φ hφ
    simp only [DeductiveProcess.union_stage, Finset.mem_union] at hφ
    exact hφ.elim (hDP φ) (hextra φ)

/-- Syntax/semantics presentation of the finite conjunction of the extra deductive stage.
This is the shared input for both the fixed-condition and growing-prefix forms of
`thm:scon`. It carries no prices or logical-inductor conclusion. -/
structure ConditioningPresentation (DP extra : DeductiveProcess) where
  condition : ℕ → Sentence
  condition_codes : PolySentenceCodes condition
  holds_condition : ∀ n (v : PCWorld),
    v.Holds (condition n) ↔ v.ConsistentWith (extra.D n)
  combined_computable : ComputableDeductiveProcess (DP.union extra)

theorem ConditioningPresentation.consistent_combined_iff
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (v : PCWorld) (n : ℕ) :
    v.ConsistentWith ((DP.union extra).D n) ↔
      v.ConsistentWith (DP.D n) ∧ v.Holds (C.condition n) := by
  rw [PCWorld.consistentWith_union_iff, C.holds_condition]

theorem ConditioningPresentation.holds_condition_of_le
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (v : PCWorld) {i n : ℕ} (hin : i ≤ n)
    (hv : v.ConsistentWith ((DP.union extra).D n)) :
    v.Holds (C.condition i) := by
  have hextraN : v.ConsistentWith (extra.D n) :=
    (PCWorld.consistentWith_union_iff v DP extra n).mp hv |>.2
  have hsub : extra.D i ⊆ extra.D n := Finset.le_iff_subset.mp
    (monotone_nat_of_le_succ
      (fun k => Finset.le_iff_subset.mpr (extra.mono k)) hin)
  apply (C.holds_condition i v).2
  intro φ hφ
  exact hextraN φ (hsub hφ)

theorem ConditioningPresentation.not_holds_condition_of_le
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (v : PCWorld) {i j : ℕ} (hij : i ≤ j)
    (hi : ¬v.Holds (C.condition i)) :
    ¬v.Holds (C.condition j) := by
  intro hj
  have hextraJ : v.ConsistentWith (extra.D j) :=
    (C.holds_condition j v).mp hj
  have hsub : extra.D i ⊆ extra.D j := Finset.le_iff_subset.mp
    (monotone_nat_of_le_succ
      (fun k => Finset.le_iff_subset.mpr (extra.mono k)) hij)
  apply hi
  apply (C.holds_condition i v).2
  intro φ hφ
  exact hextraJ φ (hsub hφ)

/-- The concrete translation realizes the compiler's same-world tracking field. -/
theorem ConditioningPresentation.conditionedTranslation_tracks
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (C.condition d))
    (T : Trader) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWith ((DP.union extra).D n)) :
    T.netWorth (conditionedHistory P C.condition) v n ≤
      (T.conditionedTranslation C.condition ε).netWorth P v n + 1 := by
  have hlower := T.conditionedTranslation_netWorth_lower P C.condition hε hden v n
    (fun i hi => C.holds_condition_of_le v hi hv)
  linarith

theorem ConditioningPresentation.conditionedTranslation_netWorth_eq_before_failure
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (C.condition d))
    (T : Trader) (v : PCWorld) {m n : ℕ} (hmn : m ≤ n)
    (hm : ¬v.Holds (C.condition m)) :
    (T.conditionedTranslation C.condition ε).netWorth P v n =
      ∑ i ∈ Finset.range m,
        ((T.conditionedTranslation C.condition ε).strat i).value P v.payout := by
  rw [Trader.netWorth]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hin hirange
  simp only [Finset.mem_range] at hin hirange
  change ((T.strat i).separatedLocallyGatedConditionalContract C.condition ε
    (conditioningBudget i)).value P v.payout = 0
  rw [Strategy.separatedLocallyGatedConditionalContract_value
    C.condition ε (conditioningBudget i) (T.strat i) P v.payout hε hden]
  apply Strategy.locallyGatedConditionalContract_value_eq_zero_of_not_holds
    (T.strat i) P C.condition hε hden (conditioningBudget i) v
  exact C.not_holds_condition_of_le v (by omega) hm

/-- The paper's first-falsified-condition argument for the concrete translator.  A base
world either satisfies every condition through `n`, where the summable tracking bound
applies, or has a least failure, after which every translated trade is exactly zero. -/
theorem ConditioningPresentation.conditionedTranslation_preserves_floor
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (C.condition d))
    (T : Trader)
    (hfloor : BddBelow (T.plausibleAssessments
      (conditionedHistory P C.condition) (DP.union extra))) :
    BddBelow ((T.conditionedTranslation C.condition ε).plausibleAssessments P DP) := by
  classical
  obtain ⟨B, hB⟩ := hfloor
  refine ⟨min (B - 1) 0, ?_⟩
  intro x hx
  obtain ⟨n, v, hvBase, rfl⟩ := hx
  by_cases hall : ∀ i, i ≤ n → v.Holds (C.condition i)
  · have hvExtra : v.ConsistentWith (extra.D n) :=
      (C.holds_condition n v).mp (hall n le_rfl)
    have hvCombined : v.ConsistentWith ((DP.union extra).D n) :=
      (PCWorld.consistentWith_union_iff v DP extra n).2 ⟨hvBase, hvExtra⟩
    have hconditional : B ≤
        T.netWorth (conditionedHistory P C.condition) v n :=
      hB ⟨n, v, hvCombined, rfl⟩
    have htrack := T.conditionedTranslation_netWorth_lower
      P C.condition hε hden v n hall
    exact (min_le_left (B - 1) 0).trans (by linarith)
  · push_neg at hall
    let m : ℕ := Nat.find hall
    have hm : m ≤ n ∧ ¬v.Holds (C.condition m) := by
      dsimp only [m]
      exact Nat.find_spec hall
    have hbefore : ∀ i, i < m → v.Holds (C.condition i) := by
      intro i hi
      by_contra hbad
      exact Nat.find_min hall (by simpa only [m] using hi)
        ⟨(Nat.le_of_lt hi).trans hm.1, hbad⟩
    have hcut :
        (T.conditionedTranslation C.condition ε).netWorth P v n =
          ∑ i ∈ Finset.range m,
            ((T.conditionedTranslation C.condition ε).strat i).value P v.payout :=
      C.conditionedTranslation_netWorth_eq_before_failure
        P hε hden T v hm.1 hm.2
    by_cases hm0 : m = 0
    · rw [hcut, hm0]
      simp
    · let k := m - 1
      have hkm : k < m := by
        dsimp only [k]
        omega
      have hkn : k ≤ n := hkm.le.trans hm.1
      have hvBaseK : v.ConsistentWith (DP.D k) := by
        have hsub : DP.D k ⊆ DP.D n := Finset.le_iff_subset.mp
          (monotone_nat_of_le_succ
            (fun j => Finset.le_iff_subset.mpr (DP.mono j)) hkn)
        intro φ hφ
        exact hvBase φ (hsub hφ)
      have hvExtraK : v.ConsistentWith (extra.D k) :=
        (C.holds_condition k v).mp (hbefore k hkm)
      have hvCombinedK : v.ConsistentWith ((DP.union extra).D k) :=
        (PCWorld.consistentWith_union_iff v DP extra k).2 ⟨hvBaseK, hvExtraK⟩
      have hconditional : B ≤
          T.netWorth (conditionedHistory P C.condition) v k :=
        hB ⟨k, v, hvCombinedK, rfl⟩
      have htrack := T.conditionedTranslation_netWorth_lower
        P C.condition hε hden v k
        (fun i hi => hbefore i (hi.trans_lt hkm))
      have hmk : k + 1 = m := by
        dsimp only [k]
        omega
      simp only [Trader.netWorth] at hconditional htrack
      rw [hmk] at hconditional htrack
      rw [hcut]
      exact (min_le_left (B - 1) 0).trans (by linarith)

/-- Operational target for the Appendix conditioning trader construction. `translate T`
is the actual base-market trader compiled from a conditional-market trader `T`.
`tracks_on_condition` is the paper's summable-error estimate, while `preserves_floor`
records the separate analysis of worlds that first falsify the growing condition. The
interface contains no exploitation or logical-induction conclusion. -/
structure ConditioningTraderCompiler
    (P : History) (DP extra : DeductiveProcess)
    (C : ConditioningPresentation DP extra) where
  conditioned_computable : ComputableMarket (conditionedHistory P C.condition)
  translate : Trader → Trader
  translate_ec : ∀ T, EfficientlyComputableTok T →
    EfficientlyComputableTok (translate T)
  tracks_on_condition : ∀ T n (v : PCWorld),
    v.ConsistentWith ((DP.union extra).D n) →
      T.netWorth (conditionedHistory P C.condition) v n ≤
        (translate T).netWorth P v n + 1
  preserves_floor : ∀ T,
    BddBelow (T.plausibleAssessments (conditionedHistory P C.condition)
      (DP.union extra)) →
    BddBelow ((translate T).plausibleAssessments P DP)

/-- The remaining operational boundary after the gated translator's economic proof.  It
contains only the patched positive denominator, computability of the rational conditional
market, and a token-level implementation of the concrete syntax transformation.  In
particular it contains no wealth, boundedness, exploitation, or logical-inductor field. -/
structure GatedConditioningOperationalWitness
    (P : History) (DP extra : DeductiveProcess)
    (C : ConditioningPresentation DP extra) (ε : ℚ) where
  epsilon_pos : 0 < (ε : ℝ)
  denominator_floor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)
  conditioned_computable : ComputableMarket (conditionedHistory P C.condition)
  translation_ec : ∀ T, EfficientlyComputableTok T →
    EfficientlyComputableTok (T.conditionedTranslation C.condition ε)

/-- Assemble the old compiler contract from the concrete gated translator.  Both economic
fields are theorems above; only executable representation data remains in the witness. -/
def GatedConditioningOperationalWitness.toCompiler
    {P : History} {DP extra : DeductiveProcess}
    {C : ConditioningPresentation DP extra} {ε : ℚ}
    (W : GatedConditioningOperationalWitness P DP extra C ε) :
    ConditioningTraderCompiler P DP extra C where
  conditioned_computable := W.conditioned_computable
  translate := fun T => T.conditionedTranslation C.condition ε
  translate_ec := W.translation_ec
  tracks_on_condition := fun T n v hv =>
    C.conditionedTranslation_tracks P W.epsilon_pos W.denominator_floor T n v hv
  preserves_floor := fun T hfloor =>
    C.conditionedTranslation_preserves_floor P W.epsilon_pos
      W.denominator_floor T hfloor

/-- The explicit compiler contract transports a genuine conditional-market exploit to a
genuine exploit of the base market. The unboundedness proof uses actual same-world wealth
tracking; no abstract exploit certificate is stored in the compiler. -/
theorem ConditioningTraderCompiler.exploits_base
    {P : History} {DP extra : DeductiveProcess}
    {C : ConditioningPresentation DP extra}
    (compiler : ConditioningTraderCompiler P DP extra C)
    {T : Trader}
    (hT : T.Exploits (conditionedHistory P C.condition) (DP.union extra)) :
    (compiler.translate T).Exploits P DP := by
  refine ⟨compiler.preserves_floor T hT.1, ?_⟩
  intro hupper
  apply hT.2
  obtain ⟨U, hU⟩ := hupper
  refine ⟨U + 1, ?_⟩
  intro x hx
  obtain ⟨n, v, hv, rfl⟩ := hx
  have hvBase : v.ConsistentWith (DP.D n) :=
    (PCWorld.consistentWith_union_iff v DP extra n).mp hv |>.1
  have htranslated : (compiler.translate T).netWorth P v n ≤ U :=
    hU ⟨n, v, hvBase, rfl⟩
  exact (compiler.tracks_on_condition T n v hv).trans (by linarith)

/-- Criterion-level Closure Under Conditioning, conditional only on the concrete Appendix
trader compiler above. This statement covers both fixed conditions and growing finite
conjunctions through `ConditioningPresentation`. -/
theorem lic_conditioned
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra)
    (compiler : ConditioningTraderCompiler P DP extra C) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) where
  marketComputable := compiler.conditioned_computable
  processComputable := C.combined_computable
  noExploit T hTec hTexp :=
    IsLogicalInductor.noExploit (P := P) (DP := DP)
      (compiler.translate T) (compiler.translate_ec T hTec)
      (compiler.exploits_base hTexp)

/-- Closure under conditioning through the concrete gated translator.  The remaining
premise is operational only; the summable tracking and first-failure downside arguments
are no longer assumed through an opaque compiler field. -/
theorem lic_conditioned_gated
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) {ε : ℚ}
    (W : GatedConditioningOperationalWitness P DP extra C ε) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned P DP extra C W.toCompiler

#print axioms conditionalQuote_mem_Icc
#print axioms EF.conditionPrices_denote
#print axioms conditioningGateVal_mul_excess_le
#print axioms gatedConditionalPosition_lower
#print axioms Strategy.gatedConditionalContract_value_lower
#print axioms Strategy.gatedConditionalContract_value_eq_zero_of_not_holds
#print axioms Trader.conditionedTranslation_netWorth_lower
#print axioms Strategy.conditionalContract_value
#print axioms PCWorld.consistentWith_union_iff
#print axioms ConditioningPresentation.consistent_combined_iff
#print axioms ConditioningPresentation.conditionedTranslation_tracks
#print axioms ConditioningPresentation.conditionedTranslation_preserves_floor
#print axioms GatedConditioningOperationalWitness.toCompiler
#print axioms ConditioningTraderCompiler.exploits_base
#print axioms lic_conditioned
#print axioms lic_conditioned_gated

end LogicalInduction
