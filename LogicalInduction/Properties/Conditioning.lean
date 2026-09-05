import LogicalInduction.Properties.UniversalSemimeasure
import LogicalInduction.Properties.FinitePerturbations
import LogicalInduction.Properties.TimelyLearning

/-!
# Conditionals (paper §4.7)

The capped conditional quote `def:condp` and Closure Under Conditioning (`thm:scon`).

`conditionalQuote` is the paper's cap: `V(φ ⋏ ψ)/V(ψ)` when that ratio is below `1`, and
`1` otherwise — including when `V(ψ) = 0`. `conditionedHistory` reads day `n` of a market
through the day-`n` member of a condition sequence.

An arbitrary conditional-market trader is compiled into the base market by rewriting price
leaves: `EF.conditionPrices`, `EF.retainedConditionPrices` and
`EF.retainedConditionPricesExceptZero` are the three substitutions,
`Strategy.separatedLocallyGatedConditionalContract` and
`Strategy.separatedExceptZeroConditionalContract` the two day translations, and
`Trader.conditionedTranslation` and `Trader.eventualConditionedTranslation` lift them to
traders.

The cap is paid for by a continuous gate (`EF.conditioningCapGate`, scalar denotation
`conditioningGateVal`) charged against the per-day budget
`conditioningBudget n = 1/((n+1)(n+2))`, whose partial sums are exactly `1 - 1/(n+2)` and
so never reach `1` (`sum_conditioningBudget`). The paper's `2⁻ⁿ` is not used because the
RPN token model cannot emit an exponential denominator
(`bigSpliceStream_two_pow_inv_not_rpnSpliceStream`); the telescoping budget is admissible
in both metering lanes, so one budget serves both.

`EventualConditioningFloor` replaces the paper's appendix double invocation of
finite-perturbation closure. The only exceptional days are those on which the condition
prices exactly zero, and on such a day the capped quote is the constant `1`, so the base
market is never modified.

`ConditioningPresentation` (the syntax/semantics of the adjoined stage, carrying
`condition_codes : BigSentenceCodes`), `ConditioningTraderCompiler`,
`GatedConditioningOperationalWitness` and `EventualConditioningOperationalWitness` are the
boundary interfaces; each is field-frozen in `AxiomAudit.lean`. The economic content —
same-world tracking and the first-falsified-condition floor — is proved here, not assumed.

Main results: `lic_conditioned`, `lic_conditioned_gated` and `lic_conditioned_eventual`
over the fuel class, and `lic_conditioned_machine`, `lic_conditioned_gated_machine` and
`lic_conditioned_eventual_machine` at `def:ec`'s own class. Neither set follows from the
other. They are stated uniformly over a `ConditioningPresentation`; the fixed-condition and
growing-prefix instances are built in
`Construction/Witnesses/ConditioningPresentation.lean`. Consumed by
`Construction/Machine/CondEndpoints.lean` and
`Construction/Witnesses/UnconditionalOverLIA.lean`, and re-exported through
`LogicalInduction.API`.

`DeductiveProcess.union` and `PCWorld.consistentWith_union_iff` give the combined process
`Θ ∪ {ψᵢ}` over which the conclusion is stated.
-/

namespace LogicalInduction

/-! ## The capped conditional quote -/

/-- The paper's capped conditional quote. It is `1` when the denominator is zero or when
the raw numerator is at least the denominator. -/
noncomputable def conditionalQuote (V : Valuation) (φ ψ : Sentence) : ℝ :=
  if V (φ ⋏ ψ) < V ψ then V (φ ⋏ ψ) / V ψ else 1

/-- Condition day `n` of a market on the day-`n` member of a condition sequence. -/
noncomputable def conditionedHistory (P : History) (ψ : ℕ → Sentence) : History :=
  fun n φ ↦ conditionalQuote (P n) φ (ψ n)

lemma conditionalQuote_eq_div {V : Valuation} {φ ψ : Sentence}
    (h : V (φ ⋏ ψ) < V ψ) :
    conditionalQuote V φ ψ = V (φ ⋏ ψ) / V ψ := by
  simp [conditionalQuote, h]

lemma conditionalQuote_eq_one {V : Valuation} {φ ψ : Sentence}
    (h : V ψ ≤ V (φ ⋏ ψ)) :
    conditionalQuote V φ ψ = 1 := by
  simp [conditionalQuote, not_lt.mpr h]

/-- The cap is inert exactly where conjunction monotonicity holds and the denominator is
positive: there the capped quote is the plain ratio. -/
lemma conditionalQuote_eq_div_of_le
    {V : Valuation} {φ ψ : Sentence} (hden : 0 < V ψ)
    (h : V (φ ⋏ ψ) ≤ V ψ) :
    conditionalQuote V φ ψ = V (φ ⋏ ψ) / V ψ := by
  rcases h.eq_or_lt with heq | hlt
  · rw [conditionalQuote_eq_one heq.symm.le, heq]
    exact (div_self (ne_of_gt hden)).symm
  · exact conditionalQuote_eq_div hlt

/-- Capping really produces a probability whenever the underlying market cells lie in
`[0,1]`; no coherence relation between conjunction and condition is assumed. -/
lemma conditionalQuote_mem_Icc
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

lemma conditionedHistory_mem_Icc
    (P : History) (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (ψ : ℕ → Sentence) (n : ℕ) (φ : Sentence) :
    0 ≤ conditionedHistory P ψ n φ ∧ conditionedHistory P ψ n φ ≤ 1 :=
  conditionalQuote_mem_Icc (P n) (hP n) φ (ψ n)

/-! ## The per-day loss budget

`conditioningBudget n = 1/((n+1)(n+2))` telescopes: its partial sums are exactly
`1 - 1/(n+2)` (`sum_conditioningBudget`), so every term is strictly positive
(`conditioningBudget_pos`) and the total mass stays below `1`
(`sum_conditioningBudget_le_one`). Those two facts are all the economic argument uses.

The paper's `2⁻ⁿ` is not available in both metering lanes. The RPN token model charges a
rational constant as a single token carrying `Encodable.encode q` (`EF.serialize`,
`Framework/Criterion.lean`), and `2⁻ⁿ` is provably outside that class
(`bigSpliceStream_two_pow_inv_not_rpnSpliceStream`). Under the write-out classes, which
meter digits of numerator and denominator, `2⁻ⁿ` would be admissible. The telescoping
budget is polynomially writable in both, so one budget serves both lanes. -/

/-- Polynomially writable summable budget for day `n`. -/
def conditioningBudget (n : ℕ) : ℚ :=
  1 / (((n + 1 : ℕ) : ℚ) * ((n + 2 : ℕ) : ℚ))

lemma conditioningBudget_pos (n : ℕ) :
    0 < (conditioningBudget n : ℝ) := by
  simp only [conditioningBudget]
  push_cast
  positivity

lemma sum_conditioningBudget (n : ℕ) :
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

lemma sum_conditioningBudget_le_one (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (conditioningBudget i : ℝ)) ≤ 1 := by
  rw [sum_conditioningBudget]
  have : 0 ≤ 1 / (n + 2 : ℝ) := by positivity
  linarith

/-! ## The continuous cap gate -/

/-- Real denotation of the continuous gate used to attenuate positive buys when the raw
conditional ratio crosses the cap at one. -/
noncomputable def conditioningGateVal (δ r : ℝ) : ℝ :=
  max 0 (min 1 ((1 + δ - r) / δ))

lemma conditioningGateVal_nonneg (δ r : ℝ) :
    0 ≤ conditioningGateVal δ r :=
  le_max_left _ _

lemma conditioningGateVal_le_one (δ r : ℝ) :
    conditioningGateVal δ r ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma conditioningGateVal_eq_one {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ 1) :
    conditioningGateVal δ r = 1 := by
  apply clipVal_eq_one
  rw [le_div_iff₀ hδ]
  linarith

/-- The gate can only retain a cap-violating buy when its excess ratio is small enough;
this is the scalar estimate that pays for the translation error. -/
lemma conditioningGateVal_mul_excess_le
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
lemma gatedConditionalPosition_lower
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

/-! ## Conditional prices as expressible features -/

namespace EF

/-- Express `1 / max(ε,e)` using the DSL's built-in `1 / max(1,·)` operation. -/
def lowerSafeRecip (e : EF) (ε : ℚ) : EF :=
  .mul (.const (1 / ε)) (.safeRecip (.mul (.const (1 / ε)) e))

lemma lowerSafeRecip_denote
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

lemma conditionalRatioEF_denote
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

lemma conditionalPriceEF_denote
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

lemma conditionalPriceEF_rank (ψ : Sentence) (ε : ℚ)
    (φ : Sentence) (day : ℕ) :
    (conditionalPriceEF ψ ε φ day).rank = day := by
  simp [conditionalPriceEF, conditionalRatioEF, lowerSafeRecip, EF.rank]

lemma conditionPrices_rank (e : EF) (ψ : ℕ → Sentence) (ε : ℚ) :
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

lemma conditionPrices_denoteWith
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

lemma conditionPrices_denote
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

@[simp] lemma retainedConditionPrices_rank (e : EF) (ψ : ℕ → Sentence) (ε : ℚ) :
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

lemma retainedConditionPrices_denoteWith (e : EF) (P : History)
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

lemma retainedConditionPrices_denote (e : EF) (P : History)
    (ψ : ℕ → Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d)) :
    (e.retainedConditionPrices ψ ε).denote P =
      e.denote (conditionedHistory P ψ) :=
  e.retainedConditionPrices_denoteWith P ψ hε hden []

/-! ## Exact treatment of zero-price condition days

The paper repairs a finite prefix of the base market and then invokes finite-perturbation
closure twice.  That route is not available for arbitrary computable markets: changing a
whole pricing day can require an inefficient infinite quote table.  Conditioning has more
structure.  After shrinking the eventual positive floor, the only exceptional days are
those on which the condition has price exactly zero; the capped conditional valuation on
such a day is identically `1`.  Precisely those historical price leaves are therefore
rewritten to the fixed constant `1`, without computing an arbitrary early pricing.
-/

/-- Parser-transparent conditional-price substitution which treats the finite set
`zeroDays` exactly.  On a zero-denominator day the source price leaf is retained as a dead
binding and the live body is the constant `1`; on every other day this is the ordinary
conditional-price substitution. -/
def retainedConditionPricesExceptZero
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ) : EF → EF
  | .price φ day =>
      .letE (.price φ day)
        (if day ∈ zeroDays then .const 1
        else conditionalPriceEF (ψ day) ε φ day)
  | .const q => .const q
  | .add a b =>
      .add (a.retainedConditionPricesExceptZero zeroDays ψ ε)
        (b.retainedConditionPricesExceptZero zeroDays ψ ε)
  | .mul a b =>
      .mul (a.retainedConditionPricesExceptZero zeroDays ψ ε)
        (b.retainedConditionPricesExceptZero zeroDays ψ ε)
  | .max a b =>
      .max (a.retainedConditionPricesExceptZero zeroDays ψ ε)
        (b.retainedConditionPricesExceptZero zeroDays ψ ε)
  | .safeRecip a =>
      .safeRecip (a.retainedConditionPricesExceptZero zeroDays ψ ε)
  | .var i => .var i
  | .letE x body =>
      .letE (x.retainedConditionPricesExceptZero zeroDays ψ ε)
        (body.retainedConditionPricesExceptZero zeroDays ψ ε)

@[simp] lemma retainedConditionPricesExceptZero_rank
    (e : EF) (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ) :
    (e.retainedConditionPricesExceptZero zeroDays ψ ε).rank = e.rank := by
  induction e with
  | price φ day =>
      by_cases hday : day ∈ zeroDays <;>
        simp [retainedConditionPricesExceptZero, hday, conditionalPriceEF,
          conditionalRatioEF, lowerSafeRecip, efMin, rank]
  | const q => rfl
  | add a b iha ihb =>
      simp [retainedConditionPricesExceptZero, iha, ihb]
  | mul a b iha ihb =>
      simp [retainedConditionPricesExceptZero, iha, ihb]
  | max a b iha ihb =>
      simp [retainedConditionPricesExceptZero, iha, ihb]
  | safeRecip a iha =>
      simp [retainedConditionPricesExceptZero, iha]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp [retainedConditionPricesExceptZero, ihx, ihbody]

/-- With no exceptional days the zero-aware substitution is the ordinary retained
substitution: `zeroDays = ∅` never takes the `.const 1` branch. -/
lemma retainedConditionPricesExceptZero_empty
    (e : EF) (ψ : ℕ → Sentence) (ε : ℚ) :
    e.retainedConditionPricesExceptZero ∅ ψ ε = e.retainedConditionPrices ψ ε := by
  induction e with
  | price φ day =>
      simp [retainedConditionPricesExceptZero, retainedConditionPrices]
  | const q => rfl
  | add a b iha ihb =>
      simp [retainedConditionPricesExceptZero, retainedConditionPrices, iha, ihb]
  | mul a b iha ihb =>
      simp [retainedConditionPricesExceptZero, retainedConditionPrices, iha, ihb]
  | max a b iha ihb =>
      simp [retainedConditionPricesExceptZero, retainedConditionPrices, iha, ihb]
  | safeRecip a iha =>
      simp [retainedConditionPricesExceptZero, retainedConditionPrices, iha]
  | var i => rfl
  | letE x body ihx ihbody =>
      simp [retainedConditionPricesExceptZero, retainedConditionPrices, ihx, ihbody]

lemma retainedConditionPricesExceptZero_denoteWith
    (e : EF) (P : History) (zeroDays : Finset ℕ)
    (ψ : ℕ → Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hP : ∀ d φ, 0 ≤ P d φ)
    (hzero : ∀ d ∈ zeroDays, P d (ψ d) = 0)
    (hfloor : ∀ d ∉ zeroDays, (ε : ℝ) ≤ P d (ψ d)) :
    ∀ ρ : List ℝ,
      (e.retainedConditionPricesExceptZero zeroDays ψ ε).denoteWith ρ P =
        e.denoteWith ρ (conditionedHistory P ψ) := by
  induction e with
  | price φ day =>
      intro ρ
      simp only [retainedConditionPricesExceptZero, denoteWith_letE]
      by_cases hday : day ∈ zeroDays
      · rw [if_pos hday]
        simp only [denoteWith_const]
        push_cast
        symm
        apply conditionalQuote_eq_one
        rw [hzero day hday]
        exact hP day (φ ⋏ ψ day)
      · rw [if_neg hday]
        exact conditionalPriceEF_denote P (ψ day) hε (hfloor day hday) φ
  | const q => intro ρ; rfl
  | add a b iha ihb =>
      intro ρ
      simp [retainedConditionPricesExceptZero, iha ρ, ihb ρ]
  | mul a b iha ihb =>
      intro ρ
      simp [retainedConditionPricesExceptZero, iha ρ, ihb ρ]
  | max a b iha ihb =>
      intro ρ
      simp [retainedConditionPricesExceptZero, iha ρ, ihb ρ]
  | safeRecip a iha =>
      intro ρ
      simp [retainedConditionPricesExceptZero, iha ρ]
  | var i => intro ρ; rfl
  | letE x body ihx ihbody =>
      intro ρ
      simp only [retainedConditionPricesExceptZero, denoteWith_letE]
      rw [ihx ρ, ihbody]

lemma retainedConditionPricesExceptZero_denote
    (e : EF) (P : History) (zeroDays : Finset ℕ)
    (ψ : ℕ → Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hP : ∀ d φ, 0 ≤ P d φ)
    (hzero : ∀ d ∈ zeroDays, P d (ψ d) = 0)
    (hfloor : ∀ d ∉ zeroDays, (ε : ℝ) ≤ P d (ψ d)) :
    (e.retainedConditionPricesExceptZero zeroDays ψ ε).denote P =
      e.denote (conditionedHistory P ψ) :=
  e.retainedConditionPricesExceptZero_denoteWith
    P zeroDays ψ hε hP hzero hfloor []

/-! ## The gate as an expressible feature -/

/-- Absolute value as an expressible feature. -/
def absVal (e : EF) : EF :=
  .max e (.mul (.const (-1)) e)

lemma absVal_denote (e : EF) (P : History) :
    (absVal e).denote P = |e.denote P| := by
  simp only [absVal, EF.denote_max, EF.denote_mul, EF.denote_const, Pi.mul_apply]
  push_cast
  rw [neg_one_mul, abs_eq_max_neg]

@[simp] lemma absVal_rank (e : EF) :
    (absVal e).rank = e.rank := by
  simp [absVal, EF.rank]

/-- Magnitude-normalized tolerance `τ / max(1,m)`. -/
def conditioningTolerance (magnitude : EF) (τ : ℚ) : EF :=
  .mul (.const τ) (.safeRecip magnitude)

lemma conditioningTolerance_denote
    (magnitude : EF) (τ : ℚ) (P : History) :
    (conditioningTolerance magnitude τ).denote P =
      (τ : ℝ) / Max.max 1 (magnitude.denote P) := by
  simp only [conditioningTolerance, EF.denote_mul, EF.denote_const,
    EF.denote_safeRecip, Pi.mul_apply]
  rw [div_eq_mul_inv]

@[simp] lemma conditioningTolerance_rank (magnitude : EF) (τ : ℚ) :
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

lemma conditioningCapGate_denote
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

@[simp] lemma conditioningCapGate_rank (ratio magnitude : EF) (τ : ℚ) :
  (conditioningCapGate ratio magnitude τ).rank =
      Nat.max ratio.rank magnitude.rank := by
  simp [conditioningCapGate, EF.rank, Nat.max_comm]

lemma conditioningTolerance_pos
    (magnitude : EF) {τ : ℚ} (P : History) (hτ : 0 < (τ : ℝ)) :
    0 < (conditioningTolerance magnitude τ).denote P := by
  rw [conditioningTolerance_denote]
  exact div_pos hτ (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

end EF

/-- Exact denominator data sufficient for conditioning without changing the base market.
All exceptional zero days lie before `cutoff`; every other condition price has one common
positive rational floor.  The finite set is used only to replace historical conditional
price leaves by the constant `1`.
Paper node: `thm:scon` -/
structure EventualConditioningFloor
    (P : History) (ψ : ℕ → Sentence) where
  cutoff : ℕ
  zeroDays : Finset ℕ
  zeroDays_lt : ∀ d ∈ zeroDays, d < cutoff
  epsilon : ℚ
  epsilon_pos : 0 < (epsilon : ℝ)
  zero_exact : ∀ d ∈ zeroDays, P d (ψ d) = 0
  positive_floor : ∀ d ∉ zeroDays, (epsilon : ℝ) ≤ P d (ψ d)

lemma EventualConditioningFloor.not_mem_of_cutoff_le
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) {d : ℕ} (hd : F.cutoff ≤ d) :
    d ∉ F.zeroDays := by
  intro hmem
  exact (Nat.not_lt_of_ge hd) (F.zeroDays_lt d hmem)

/-! ## The day translation

Each day's strategy is translated position by position. A list of `k` positions gives each
position budget `τ/k` (`localConditioningBudget`) and normalizes it by that position's own
magnitude, so the per-position errors still sum to at most `τ`. Normalizing per position
rather than by a strategy-wide magnitude keeps the emitted coefficients small: a
strategy-wide magnitude would make every output coefficient repeat the whole input
strategy. -/

/-- Both day translations emit two legs per input position, in compiler order (all first
legs, then all second legs) rather than interleaved.  Given that the two legs of a position
are together worth what the position's flat-form entry is worth, the two orders have the
same total value. -/
private lemma sum_legs_eq_sum_flatMap {α β : Type*} (f g : α → β) (h : α → List β)
    (v : β → ℝ) (hpair : ∀ p, v (f p) + v (g p) = ((h p).map v).sum) (l : List α) :
    ((l.map f).map v).sum + ((l.map g).map v).sum = ((l.flatMap h).map v).sum := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
        List.sum_append]
      linarith [ih, hpair p]

namespace Strategy

private lemma gatedConditionalPair_lower
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

/-- The share of a day's budget `τ` allocated to each of `count` positions: `τ/count`. -/
def localConditioningBudget (τ : ℚ) (count : ℕ) : ℚ := τ / (count : ℚ)

/-- The locally gated conditional contract of a day's trade list, in flat form: each
position emits both legs of its conditional contract. -/
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

/-- The day strategy that trades every position's locally gated conditional contract
against the base market. -/
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
  let boundRatio := EF.var 0
  let bound := EF.var 1
  let magnitude := EF.absVal bound
  let gate := EF.conditioningCapGate boundRatio magnitude
    (localConditioningBudget τ count)
  let β := efMin bound (EF.mul bound gate)
  (EF.letE α (EF.letE ratio β), p.2 ⋏ ψ day)

/-- Second output leg of the locally normalized conditioning compiler. -/
def locallyGatedSecondLeg (ψ : ℕ → Sentence) (ε : ℚ) (day : ℕ)
    (τ : ℚ) (count : ℕ) (p : EF × Sentence) : EF × Sentence :=
  let α := p.1.retainedConditionPrices ψ ε
  let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
  let boundRatio := EF.var 0
  let bound := EF.var 1
  let magnitude := EF.absVal bound
  let gate := EF.conditioningCapGate boundRatio magnitude
    (localConditioningBudget τ count)
  let β := efMin bound (EF.mul bound gate)
  (EF.letE α (EF.letE ratio
    (EF.mul (EF.const (-1)) (EF.mul β boundRatio))), ψ day)

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

lemma separatedLocallyGatedConditionalContract_value
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
    rw [locallyGatedConditionalContractTrades]
    refine sum_legs_eq_sum_flatMap _ _ _ value (fun p ↦ ?_) trades
    have hp : (p.1.retainedConditionPrices ψ ε).denote P =
        (p.1.conditionPrices ψ ε).denote P := by
      rw [p.1.retainedConditionPrices_denote P ψ hε hden,
        p.1.conditionPrices_denote P ψ hε hden]
    change (p.1.retainedConditionPrices ψ ε).denoteWith [] P =
      (p.1.conditionPrices ψ ε).denoteWith [] P at hp
    simp only [locallyGatedFirstLeg, locallyGatedSecondLeg, value,
      EF.denote, EF.denoteWith_letE]
    rw [hp]
    simp [EF.denoteWith, EF.conditioningCapGate, EF.conditioningTolerance,
      EF.absVal, EF.conditionalRatioEF, EF.lowerSafeRecip, efMin,
      clip01, List.getD]
  simpa only [Strategy.value, separatedLocallyGatedConditionalContract,
    locallyGatedConditionalContract, List.map_append, List.sum_append, List.map_map,
    Function.comp_apply] using hsum T.trades.length T.trades

private lemma locallyGatedConditionalPair_lower
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

private lemma locallyGatedConditionalContractTrades_value_lower
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

lemma locallyGatedConditionalContract_value_lower
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

private lemma locallyGatedConditionalContractTrades_value_zero
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

lemma locallyGatedConditionalContract_value_eq_zero_of_not_holds
    {day : ℕ} (T : Strategy day)
    (P : History) (ψ : ℕ → Sentence) {ε : ℚ}
    (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (τ : ℚ) (v : PCWorld) (hψ : ¬v.Holds (ψ day)) :
    (T.locallyGatedConditionalContract ψ ε τ).value P v.payout = 0 := by
  exact locallyGatedConditionalContractTrades_value_zero T.trades P ψ hε hden τ v hψ

/-! ### Prefix-safe form

The live coefficient below uses `retainedConditionPricesExceptZero`. The current-day
conditional-contract ratio still uses the ordinary safe reciprocal; public callers launch
this translator after every member of `zeroDays`, so that ratio is evaluated only where the
common positive floor applies. -/

/-- The zero-aware locally gated contract of a day's trade list, in flat form: the same two
legs per position, with the coefficient rewritten by `retainedConditionPricesExceptZero` so
that historical zero-denominator days denote the constant `1`. -/
def exceptZeroLocallyGatedConditionalContractTrades
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ)
    (day : ℕ) (τ : ℚ) (count : ℕ) :
    List (EF × Sentence) → List (EF × Sentence) :=
  fun trades ↦ trades.flatMap (fun p ↦
      let α := p.1.retainedConditionPricesExceptZero zeroDays ψ ε
      let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
      let magnitude := EF.absVal α
      let gate := EF.conditioningCapGate ratio magnitude
        (localConditioningBudget τ count)
      let β := efMin α (EF.mul α gate)
      [(β, p.2 ⋏ ψ day),
        (EF.mul (EF.const (-1)) (EF.mul β ratio), ψ day)])

/-- First output leg of the zero-aware conditioning compiler: `locallyGatedFirstLeg` with
the coefficient rewritten by `retainedConditionPricesExceptZero`. -/
def exceptZeroLocallyGatedFirstLeg
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ)
    (day : ℕ) (τ : ℚ) (count : ℕ) (p : EF × Sentence) : EF × Sentence :=
  let α := p.1.retainedConditionPricesExceptZero zeroDays ψ ε
  let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
  let boundRatio := EF.var 0
  let bound := EF.var 1
  let magnitude := EF.absVal bound
  let gate := EF.conditioningCapGate boundRatio magnitude
    (localConditioningBudget τ count)
  let β := efMin bound (EF.mul bound gate)
  (EF.letE α (EF.letE ratio β), p.2 ⋏ ψ day)

/-- Second output leg of the zero-aware conditioning compiler: `locallyGatedSecondLeg` with
the coefficient rewritten by `retainedConditionPricesExceptZero`. -/
def exceptZeroLocallyGatedSecondLeg
    (zeroDays : Finset ℕ) (ψ : ℕ → Sentence) (ε : ℚ)
    (day : ℕ) (τ : ℚ) (count : ℕ) (p : EF × Sentence) : EF × Sentence :=
  let α := p.1.retainedConditionPricesExceptZero zeroDays ψ ε
  let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
  let boundRatio := EF.var 0
  let bound := EF.var 1
  let magnitude := EF.absVal bound
  let gate := EF.conditioningCapGate boundRatio magnitude
    (localConditioningBudget τ count)
  let β := efMin bound (EF.mul bound gate)
  (EF.letE α (EF.letE ratio
    (EF.mul (EF.const (-1)) (EF.mul β boundRatio))), ψ day)

/-- Compiler-order zero-aware conditional contract. -/
def separatedExceptZeroConditionalContract
    {day : ℕ} (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    (ε τ : ℚ) (T : Strategy day) : Strategy day where
  trades :=
    T.trades.map
        (exceptZeroLocallyGatedFirstLeg zeroDays ψ ε day τ T.trades.length) ++
      T.trades.map
        (exceptZeroLocallyGatedSecondLeg zeroDays ψ ε day τ T.trades.length)
  rank_le := by
    intro out hout
    rw [List.mem_append, List.mem_map, List.mem_map] at hout
    rcases hout with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · have hα :
          (p.1.retainedConditionPricesExceptZero zeroDays ψ ε).rank ≤ day := by
        rw [p.1.retainedConditionPricesExceptZero_rank]
        exact T.rank_le p hp
      have hr : (EF.conditionalRatioEF (ψ day) ε p.2 day).rank ≤ day := by
        simp [EF.conditionalRatioEF, EF.lowerSafeRecip, EF.rank]
      simpa [exceptZeroLocallyGatedFirstLeg, EF.rank,
        EF.conditioningCapGate_rank, hα, hr] using T.rank_le p hp
    · have hα :
          (p.1.retainedConditionPricesExceptZero zeroDays ψ ε).rank ≤ day := by
        rw [p.1.retainedConditionPricesExceptZero_rank]
        exact T.rank_le p hp
      have hr : (EF.conditionalRatioEF (ψ day) ε p.2 day).rank ≤ day := by
        simp [EF.conditionalRatioEF, EF.lowerSafeRecip, EF.rank]
      simpa [exceptZeroLocallyGatedSecondLeg, EF.rank,
        EF.conditioningCapGate_rank, hα, hr] using T.rank_le p hp

private lemma separatedExceptZeroConditionalContract_value_eq_flatMap
    {day : ℕ} (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    (ε τ : ℚ) (T : Strategy day) (P : History) (w : Valuation) :
    (T.separatedExceptZeroConditionalContract zeroDays ψ ε τ).value P w =
      ((exceptZeroLocallyGatedConditionalContractTrades zeroDays ψ ε day τ
        T.trades.length T.trades).map
          (fun p ↦ p.1.denote P * (w p.2 - P day p.2))).sum := by
  let value : EF × Sentence → ℝ := fun p ↦
    p.1.denote P * (w p.2 - P day p.2)
  have hsum (count : ℕ) (trades : List (EF × Sentence)) :
      (trades.map
          (exceptZeroLocallyGatedFirstLeg zeroDays ψ ε day τ count) |>.map value).sum +
        (trades.map
          (exceptZeroLocallyGatedSecondLeg zeroDays ψ ε day τ count) |>.map value).sum =
      (exceptZeroLocallyGatedConditionalContractTrades
        zeroDays ψ ε day τ count trades |>.map value).sum := by
    rw [exceptZeroLocallyGatedConditionalContractTrades]
    refine sum_legs_eq_sum_flatMap _ _ _ value (fun p ↦ ?_) trades
    simp [exceptZeroLocallyGatedFirstLeg, exceptZeroLocallyGatedSecondLeg, value,
      EF.denote, EF.denoteWith_letE, EF.conditioningCapGate,
      EF.conditioningTolerance, EF.absVal, EF.conditionalRatioEF,
      EF.lowerSafeRecip, efMin, clip01, List.getD]
  simpa only [Strategy.value, separatedExceptZeroConditionalContract,
    List.map_append, List.sum_append, List.map_map, Function.comp_apply]
    using hsum T.trades.length T.trades

private lemma exceptZeroLocallyGatedPair_lower
    {day count : ℕ} (p : EF × Sentence)
    (P : History) (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    {ε τ : ℚ} (hε : 0 < (ε : ℝ))
    (hP : ∀ d φ, 0 ≤ P d φ)
    (hzero : ∀ d ∈ zeroDays, P d (ψ d) = 0)
    (hfloor : ∀ d ∉ zeroDays, (ε : ℝ) ≤ P d (ψ d))
    (hday : day ∉ zeroDays)
    (hτ : 0 < (τ : ℝ)) (hcount : 0 < count)
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2) -
      (localConditioningBudget τ count : ℝ) ≤
      let α := p.1.retainedConditionPricesExceptZero zeroDays ψ ε
      let ratio := EF.conditionalRatioEF (ψ day) ε p.2 day
      let magnitude := EF.absVal α
      let gate := EF.conditioningCapGate ratio magnitude
        (localConditioningBudget τ count)
      let β := efMin α (EF.mul α gate)
      β.denote P * (v.payout (p.2 ⋏ ψ day) - P day (p.2 ⋏ ψ day)) +
        (EF.mul (EF.const (-1)) (EF.mul β ratio)).denote P *
          (v.payout (ψ day) - P day (ψ day)) := by
  dsimp only
  let α := p.1.retainedConditionPricesExceptZero zeroDays ψ ε
  let magnitude := EF.absVal α
  let positionBudget := localConditioningBudget τ count
  let a := p.1.denote (conditionedHistory P ψ)
  let r := P day (p.2 ⋏ ψ day) / P day (ψ day)
  let δ := (EF.conditioningTolerance magnitude positionBudget).denote P
  let g := conditioningGateVal δ r
  let b := min a (a * g)
  have hposition : 0 < (positionBudget : ℝ) := by
    simp only [positionBudget, localConditioningBudget]
    push_cast
    exact div_pos hτ (by positivity)
  have hδ : 0 < δ :=
    EF.conditioningTolerance_pos magnitude P hposition
  have hw : v.payout p.2 = 0 ∨ v.payout p.2 = 1 := by
    by_cases hp : v.Holds p.2
    · exact Or.inr (by simp [PCWorld.payout, hp])
    · exact Or.inl (by simp [PCWorld.payout, hp])
  have hcoef : α.denote P = a := by
    exact p.1.retainedConditionPricesExceptZero_denote
      P zeroDays ψ hε hP hzero hfloor
  have hratio :
      (EF.conditionalRatioEF (ψ day) ε p.2 day).denote P = r := by
    exact EF.conditionalRatioEF_denote P (ψ day) hε (hfloor day hday) p.2
  have hgate :
      (EF.conditioningCapGate
        (EF.conditionalRatioEF (ψ day) ε p.2 day)
        magnitude positionBudget).denote P = g := by
    rw [EF.conditioningCapGate_denote, hratio,
      ← EF.conditioningTolerance_denote]
  have hbeta :
      (efMin α
        (EF.mul α
          (EF.conditioningCapGate
            (EF.conditionalRatioEF (ψ day) ε p.2 day)
            magnitude positionBudget))).denote P = b := by
    simp only [efMin_denote, EF.denote_mul, Pi.mul_apply, hcoef, hgate]
    rfl
  have hquote : conditionedHistory P ψ day p.2 = min 1 r := by
    simp only [conditionedHistory]
    rw [← EF.conditionalPriceEF_denote
      P (ψ day) hε (hfloor day hday) p.2]
    simp only [EF.conditionalPriceEF, efMin_denote,
      EF.denote_const, hratio]
    push_cast
    rfl
  have hpayoutψ : v.payout (ψ day) = 1 := by
    simp [PCWorld.payout, hψ]
  have hpayoutAnd : v.payout (p.2 ⋏ ψ day) = v.payout p.2 := by
    by_cases hp : v.Holds p.2 <;>
      simp [PCWorld.payout, PCWorld.holds_and, hψ, hp]
  have hdenPos : 0 < P day (ψ day) :=
    hε.trans_le (hfloor day hday)
  have hrden : r * P day (ψ day) = P day (p.2 ⋏ ψ day) := by
    dsimp only [r]
    field_simp [ne_of_gt hdenPos]
  have hscalar := gatedConditionalPosition_lower
    (a := a) (δ := δ) (r := r) (w := v.payout p.2) hδ hw
  have hmag : magnitude.denote P = |a| := by
    simp [magnitude, EF.absVal_denote, hcoef]
  have hmaxPos : (0 : ℝ) < Max.max 1 |a| :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hratioBudget : |a| / Max.max 1 |a| ≤ 1 :=
    (div_le_one hmaxPos).2 (le_max_right _ _)
  have hbudget :
      |a| * (EF.conditioningTolerance magnitude positionBudget).denote P ≤
        (positionBudget : ℝ) := by
    rw [EF.conditioningTolerance_denote, hmag]
    calc
      |a| * ((positionBudget : ℝ) / Max.max 1 |a|) =
          (positionBudget : ℝ) * (|a| / Max.max 1 |a|) := by ring
      _ ≤ (positionBudget : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hratioBudget hposition.le
      _ = (positionBudget : ℝ) := mul_one _
  dsimp only at hscalar
  rw [hbeta, hpayoutψ, hpayoutAnd, hquote]
  simp only [EF.denote_mul, EF.denote_const, Pi.mul_apply]
  rw [hbeta, hratio]
  push_cast
  dsimp only [a, δ, g, b] at hscalar ⊢
  apply (sub_le_sub_left hbudget _).trans
  exact hscalar.trans_eq (by
    rw [← hrden]
    ring)

private lemma exceptZeroLocallyGatedTrades_value_lower
    {day count : ℕ} (trades : List (EF × Sentence))
    (P : History) (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    {ε τ : ℚ} (hε : 0 < (ε : ℝ))
    (hP : ∀ d φ, 0 ≤ P d φ)
    (hzero : ∀ d ∈ zeroDays, P d (ψ d) = 0)
    (hfloor : ∀ d ∉ zeroDays, (ε : ℝ) ≤ P d (ψ d))
    (hday : day ∉ zeroDays)
    (hτ : 0 < (τ : ℝ)) (hcount : 0 < count)
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    (trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2))).sum -
      trades.length * (localConditioningBudget τ count : ℝ) ≤
      ((exceptZeroLocallyGatedConditionalContractTrades
        zeroDays ψ ε day τ count trades).map
        (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum := by
  induction trades with
  | nil => simp [exceptZeroLocallyGatedConditionalContractTrades]
  | cons p rest ih =>
      have hp := exceptZeroLocallyGatedPair_lower p P zeroDays ψ
        hε hP hzero hfloor hday hτ hcount v hψ
      rw [exceptZeroLocallyGatedConditionalContractTrades] at ih
      rw [exceptZeroLocallyGatedConditionalContractTrades, List.flatMap_cons,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_zero]
      nlinarith

lemma separatedExceptZeroConditionalContract_value_lower
    {day : ℕ} (T : Strategy day)
    (P : History) (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hP : ∀ d φ, 0 ≤ P d φ)
    (hzero : ∀ d ∈ zeroDays, P d (ψ d) = 0)
    (hfloor : ∀ d ∉ zeroDays, (ε : ℝ) ≤ P d (ψ d))
    (hday : day ∉ zeroDays)
    (v : PCWorld) (hψ : v.Holds (ψ day)) :
    T.value (conditionedHistory P ψ) v.payout -
        (conditioningBudget day : ℝ) ≤
      (T.separatedExceptZeroConditionalContract
        zeroDays ψ ε (conditioningBudget day)).value P v.payout := by
  by_cases hempty : T.trades = []
  · have hτ0 : 0 ≤ (conditioningBudget day : ℝ) :=
      (conditioningBudget_pos day).le
    simp [Strategy.value, separatedExceptZeroConditionalContract,
      hempty, hτ0]
  · have hcount : 0 < T.trades.length := List.length_pos_iff.mpr hempty
    have hτ : 0 < (conditioningBudget day : ℝ) :=
      conditioningBudget_pos day
    have hlist := exceptZeroLocallyGatedTrades_value_lower
      T.trades P zeroDays ψ hε hP hzero hfloor hday hτ hcount v hψ
    have hcancel : (T.trades.length : ℝ) *
        (localConditioningBudget
          (conditioningBudget day) T.trades.length : ℝ) =
          (conditioningBudget day : ℝ) := by
      simp only [localConditioningBudget]
      push_cast
      field_simp
    rw [separatedExceptZeroConditionalContract_value_eq_flatMap]
    change
      (T.trades.map (fun p ↦ p.1.denote (conditionedHistory P ψ) *
        (v.payout p.2 - conditionedHistory P ψ day p.2))).sum -
          (conditioningBudget day : ℝ) ≤
        ((exceptZeroLocallyGatedConditionalContractTrades zeroDays ψ ε day
          (conditioningBudget day) T.trades.length T.trades).map
            (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum
    rw [← hcancel]
    exact hlist

private lemma exceptZeroLocallyGatedTrades_value_zero
    {day count : ℕ} (trades : List (EF × Sentence))
    (P : History) (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d ∉ zeroDays, (ε : ℝ) ≤ P d (ψ d))
    (hday : day ∉ zeroDays)
    (τ : ℚ) (v : PCWorld) (hψ : ¬v.Holds (ψ day)) :
    ((exceptZeroLocallyGatedConditionalContractTrades
      zeroDays ψ ε day τ count trades).map
      (fun p ↦ p.1.denote P * (v.payout p.2 - P day p.2))).sum = 0 := by
  induction trades with
  | nil => simp [exceptZeroLocallyGatedConditionalContractTrades]
  | cons p rest ih =>
      have hdenPos : 0 < P day (ψ day) :=
        hε.trans_le (hfloor day hday)
      have hratio := EF.conditionalRatioEF_denote
        P (ψ day) hε (hfloor day hday) p.2
      have hpayoutψ : v.payout (ψ day) = 0 := by
        simp [PCWorld.payout, hψ]
      have hpayoutAnd : v.payout (p.2 ⋏ ψ day) = 0 := by
        simp [PCWorld.payout, PCWorld.holds_and, hψ]
      rw [exceptZeroLocallyGatedConditionalContractTrades] at ih
      rw [exceptZeroLocallyGatedConditionalContractTrades, List.flatMap_cons,
        List.map_append, List.sum_append]
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil,
        add_zero, EF.denote_mul, EF.denote_const, Pi.mul_apply]
      rw [ih, hpayoutψ, hpayoutAnd, hratio]
      push_cast
      field_simp [ne_of_gt hdenPos]
      ring

lemma separatedExceptZeroConditionalContract_value_eq_zero_of_not_holds
    {day : ℕ} (T : Strategy day)
    (P : History) (zeroDays : Finset ℕ) (ψ : ℕ → Sentence)
    {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hfloor : ∀ d ∉ zeroDays, (ε : ℝ) ≤ P d (ψ d))
    (hday : day ∉ zeroDays)
    (τ : ℚ) (v : PCWorld) (hψ : ¬v.Holds (ψ day)) :
    (T.separatedExceptZeroConditionalContract zeroDays ψ ε τ).value
      P v.payout = 0 := by
  rw [separatedExceptZeroConditionalContract_value_eq_flatMap]
  exact exceptZeroLocallyGatedTrades_value_zero
    T.trades P zeroDays ψ hε hfloor hday τ v hψ

end Strategy

/-! ## The trader translation -/

namespace Trader

/-- Pointwise gated translation of a conditional-market trader. -/
def conditionedTranslation (ψ : ℕ → Sentence) (ε : ℚ) (T : Trader) : Trader where
  strat n := (T.strat n).separatedLocallyGatedConditionalContract
    ψ ε (conditioningBudget n)

/-- Summing the day estimates costs at most one in every world satisfying all conditions
through the assessment day. -/
lemma conditionedTranslation_netWorth_lower
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

/-- Discard every strategy before a fixed launch day. -/
def after (cutoff : ℕ) (T : Trader) : Trader where
  strat n := if cutoff ≤ n then T.strat n else Trader.zero.strat n

@[simp] lemma after_strat_of_le (T : Trader) {cutoff n : ℕ}
    (h : cutoff ≤ n) :
    (T.after cutoff).strat n = T.strat n := by
  simp [after, h]

@[simp] lemma after_strat_of_lt (T : Trader) {cutoff n : ℕ}
    (h : n < cutoff) :
    (T.after cutoff).strat n = Trader.zero.strat n := by
  simp [after, Nat.not_le_of_lt h]

/-- Removing finitely many trading days changes wealth by a fixed amount. -/
lemma after_netWorth_difference_le
    (T : Trader) (P : History)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1)
    (cutoff : ℕ) (v : PCWorld) (n : ℕ) :
    |T.netWorth P v n - (T.after cutoff).netWorth P v n| ≤
      ∑ i ∈ Finset.range cutoff, (T.strat i).magnitude P := by
  have hw : ∀ φ, v.payout φ = 0 ∨ v.payout φ = 1 := by
    intro φ
    by_cases hφ : v.Holds φ
    · exact Or.inr (by simp [PCWorld.payout, hφ])
    · exact Or.inl (by simp [PCWorld.payout, hφ])
  rw [Trader.netWorth, Trader.netWorth, ← Finset.sum_sub_distrib]
  calc
    |(∑ i ∈ Finset.range (n + 1),
        ((T.strat i).value P v.payout -
          ((T.after cutoff).strat i).value P v.payout))| ≤
        ∑ i ∈ Finset.range (n + 1),
          |(T.strat i).value P v.payout -
            ((T.after cutoff).strat i).value P v.payout| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
          if i < cutoff then (T.strat i).magnitude P else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hic : i < cutoff
      · rw [if_pos hic, T.after_strat_of_lt hic]
        simpa [Trader.zero, Strategy.value] using
          Strategy.abs_value_le_magnitude
            (T.strat i) P v.payout hw (hP i)
      · rw [if_neg hic, T.after_strat_of_le (Nat.le_of_not_gt hic)]
        simp
    _ = ∑ i ∈ (Finset.range (n + 1)).filter (fun i ↦ i < cutoff),
          (T.strat i).magnitude P := by rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ Finset.range cutoff, (T.strat i).magnitude P := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact hi.2
      · intro i hi hnot
        exact Strategy.magnitude_nonneg (T.strat i) P

lemma Exploits.after
    (T : Trader) (P : History) (DP : DeductiveProcess)
    (hP : ∀ day φ, 0 ≤ P day φ ∧ P day φ ≤ 1)
    (hEx : T.Exploits P DP) (cutoff : ℕ) :
    (T.after cutoff).Exploits P DP := by
  apply hEx.of_boundedDifference
    (∑ i ∈ Finset.range cutoff, (T.strat i).magnitude P)
  intro n v hv
  exact T.after_netWorth_difference_le P hP cutoff v n

/-- Base-market trader used by the prefix-safe conditioning proof.  It is silent before
the common denominator floor begins and uses the exact-zero historical price rewrite
afterwards. -/
def eventualConditionedTranslation
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (T : Trader) : Trader where
  strat n :=
    if F.cutoff ≤ n then
      (T.strat n).separatedExceptZeroConditionalContract
        F.zeroDays ψ F.epsilon (conditioningBudget n)
    else Trader.zero.strat n

@[simp] lemma eventualConditionedTranslation_strat_of_le
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (T : Trader) {n : ℕ}
    (hn : F.cutoff ≤ n) :
    (T.eventualConditionedTranslation F).strat n =
      (T.strat n).separatedExceptZeroConditionalContract
        F.zeroDays ψ F.epsilon (conditioningBudget n) := by
  simp [eventualConditionedTranslation, hn]

@[simp] lemma eventualConditionedTranslation_strat_of_lt
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ) (T : Trader) {n : ℕ}
    (hn : n < F.cutoff) :
    (T.eventualConditionedTranslation F).strat n =
      Trader.zero.strat n := by
  simp [eventualConditionedTranslation, Nat.not_le_of_lt hn]

lemma eventualConditionedTranslation_netWorth_lower
    {P : History} {ψ : ℕ → Sentence}
    (F : EventualConditioningFloor P ψ)
    (T : Trader) (hP : ∀ d φ, 0 ≤ P d φ)
    (v : PCWorld) (n : ℕ)
    (hψ : ∀ i, i ≤ n → v.Holds (ψ i)) :
    (T.after F.cutoff).netWorth (conditionedHistory P ψ) v n - 1 ≤
      (T.eventualConditionedTranslation F).netWorth P v n := by
  have hday : ∀ i ∈ Finset.range (n + 1),
      ((T.after F.cutoff).strat i).value
          (conditionedHistory P ψ) v.payout -
        (conditioningBudget i : ℝ) ≤
      ((T.eventualConditionedTranslation F).strat i).value P v.payout := by
    intro i hi
    by_cases hic : i < F.cutoff
    · rw [T.after_strat_of_lt hic,
        T.eventualConditionedTranslation_strat_of_lt F hic]
      have hbudget : 0 ≤ (conditioningBudget i : ℝ) :=
        (conditioningBudget_pos i).le
      simp [Trader.zero, Strategy.value, hbudget]
    · have hci : F.cutoff ≤ i := Nat.le_of_not_gt hic
      rw [T.after_strat_of_le hci,
        T.eventualConditionedTranslation_strat_of_le F hci]
      exact (T.strat i).separatedExceptZeroConditionalContract_value_lower
        P F.zeroDays ψ F.epsilon_pos hP F.zero_exact F.positive_floor
        (F.not_mem_of_cutoff_le hci) v
        (hψ i (by simp only [Finset.mem_range] at hi; omega))
  have hsum := Finset.sum_le_sum hday
  have hbudget := sum_conditioningBudget_le_one n
  simp only [Trader.netWorth]
  calc
    (∑ i ∈ Finset.range (n + 1),
        ((T.after F.cutoff).strat i).value
          (conditionedHistory P ψ) v.payout) - 1 ≤
      (∑ i ∈ Finset.range (n + 1),
        ((T.after F.cutoff).strat i).value
          (conditionedHistory P ψ) v.payout) -
          ∑ i ∈ Finset.range (n + 1), (conditioningBudget i : ℝ) :=
      sub_le_sub_left hbudget _
    _ = ∑ i ∈ Finset.range (n + 1),
        (((T.after F.cutoff).strat i).value
          (conditionedHistory P ψ) v.payout -
          (conditioningBudget i : ℝ)) := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((T.eventualConditionedTranslation F).strat i).value
          P v.payout := hsum

end Trader

/-! ## The combined deductive process -/

namespace DeductiveProcess

/-- Stagewise union of two deductive processes. -/
def union (DP extra : DeductiveProcess) : DeductiveProcess where
  D n := DP.D n ∪ extra.D n
  mono n := by
    intro φ hφ
    simp only [Finset.mem_union] at hφ ⊢
    exact hφ.elim (fun h ↦ Or.inl (DP.mono n h))
      (fun h ↦ Or.inr (extra.mono n h))

@[simp] lemma union_stage (DP extra : DeductiveProcess) (n : ℕ) :
    (DP.union extra).D n = DP.D n ∪ extra.D n := rfl

end DeductiveProcess

lemma PCWorld.consistentWith_union_iff
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

/-! ## The conditioning presentation and its compiler -/

/-- Syntax/semantics presentation of the finite conjunction of the extra deductive stage.
This is the shared input for both the fixed-condition and growing-prefix forms of
`thm:scon`. It carries no prices or logical-inductor conclusion.

The condition family is certified at `def:ec`'s write-out class `BigSentenceCodes`, because
a growing conjunction's Gödel code is exponential in the day (README, *Efficient
computability*). `BigSentenceCodes.ofRpnSentenceCodes` embeds the token-metered
`RpnSentenceCodes` as a sufficient subclass.

Inhabitants are built in `Construction/Witnesses/ConditioningPresentation.lean`.
Paper node: `thm:scon` -/
structure ConditioningPresentation (DP extra : DeductiveProcess) where
  condition : ℕ → Sentence
  condition_codes : BigSentenceCodes condition
  holds_condition : ∀ n (v : PCWorld),
    v.Holds (condition n) ↔ v.ConsistentWith (extra.D n)
  combined_computable : ComputableDeductiveProcess (DP.union extra)

lemma ConditioningPresentation.consistent_combined_iff
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (v : PCWorld) (n : ℕ) :
    v.ConsistentWith ((DP.union extra).D n) ↔
      v.ConsistentWith (DP.D n) ∧ v.Holds (C.condition n) := by
  rw [PCWorld.consistentWith_union_iff, C.holds_condition]

lemma ConditioningPresentation.holds_condition_of_le
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

lemma ConditioningPresentation.not_holds_condition_of_le
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
lemma ConditioningPresentation.conditionedTranslation_tracks
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

lemma ConditioningPresentation.conditionedTranslation_netWorth_eq_before_failure
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

/-- The paper's first-falsified-condition argument, stated once for both translators.

A base world either satisfies every condition through day `n`, where the translated trader
tracks the source trader within `1` (`hlower`), or has a least failure at some `m ≤ n`,
after which every translated trade is exactly zero, so the translated net worth on day `n`
is the sum over `Finset.range m` (`hcut`). That truncated sum is either degenerate — the
days `Deg` on which the translator has emitted nothing at all, contributing `0` (`hdeg`) —
or it is bounded below using the source floor at day `m - 1`, which the world does reach.

The gated translator instantiates `Deg` as `m = 0`; the prefix-safe translator instantiates
it as `m ≤ F.cutoff`, where the source trader has been silenced. -/
private lemma ConditioningPresentation.preserves_floor_of_before_failure
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) {Tsrc Ttr : Trader} (Deg : ℕ → Prop) [DecidablePred Deg]
    (hlower : ∀ (v : PCWorld) (n : ℕ), (∀ i, i ≤ n → v.Holds (C.condition i)) →
      Tsrc.netWorth (conditionedHistory P C.condition) v n - 1 ≤ Ttr.netWorth P v n)
    (hcut : ∀ (v : PCWorld) (m n : ℕ), m ≤ n → ¬v.Holds (C.condition m) →
      Ttr.netWorth P v n =
        ∑ i ∈ Finset.range m, (Ttr.strat i).value P v.payout)
    (hdeg : ∀ (v : PCWorld) (m : ℕ), Deg m →
      ∑ i ∈ Finset.range m, (Ttr.strat i).value P v.payout = 0)
    (hpos : ∀ m : ℕ, ¬ Deg m → 0 < m)
    (hfloor : BddBelow (Tsrc.plausibleAssessments
      (conditionedHistory P C.condition) (DP.union extra))) :
    BddBelow (Ttr.plausibleAssessments P DP) := by
  classical
  obtain ⟨B, hB⟩ := hfloor
  refine ⟨min (B - 1) 0, ?_⟩
  intro x hx
  obtain ⟨n, v, hvBase, rfl⟩ := hx
  by_cases hall : ∀ i, i ≤ n → v.Holds (C.condition i)
  · have hvCombined : v.ConsistentWith ((DP.union extra).D n) :=
      (PCWorld.consistentWith_union_iff v DP extra n).2
        ⟨hvBase, (C.holds_condition n v).mp (hall n le_rfl)⟩
    have hconditional : B ≤
        Tsrc.netWorth (conditionedHistory P C.condition) v n :=
      hB ⟨n, v, hvCombined, rfl⟩
    have htrack := hlower v n hall
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
    have hcutm := hcut v m n hm.1 hm.2
    by_cases hdegm : Deg m
    · rw [hcutm, hdeg v m hdegm]
      exact min_le_right _ _
    · have hm0 : 0 < m := hpos m hdegm
      let k := m - 1
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
      have hvCombinedK : v.ConsistentWith ((DP.union extra).D k) :=
        (PCWorld.consistentWith_union_iff v DP extra k).2
          ⟨hvBaseK, (C.holds_condition k v).mp (hbefore k hkm)⟩
      have hconditional : B ≤
          Tsrc.netWorth (conditionedHistory P C.condition) v k :=
        hB ⟨k, v, hvCombinedK, rfl⟩
      have htrack := hlower v k (fun i hi => hbefore i (hi.trans_lt hkm))
      have hmk : k + 1 = m := by
        dsimp only [k]
        omega
      simp only [Trader.netWorth] at hconditional htrack
      rw [hmk] at hconditional htrack
      rw [hcutm]
      exact (min_le_left (B - 1) 0).trans (by linarith)

/-- The first-falsified-condition argument for the concrete gated translator: the
degenerate case is the world that already fails the day-`0` condition. -/
lemma ConditioningPresentation.conditionedTranslation_preserves_floor
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) {ε : ℚ} (hε : 0 < (ε : ℝ))
    (hden : ∀ d, (ε : ℝ) ≤ P d (C.condition d))
    (T : Trader)
    (hfloor : BddBelow (T.plausibleAssessments
      (conditionedHistory P C.condition) (DP.union extra))) :
    BddBelow ((T.conditionedTranslation C.condition ε).plausibleAssessments P DP) :=
  C.preserves_floor_of_before_failure P (fun m => m = 0)
    (fun v n hall =>
      T.conditionedTranslation_netWorth_lower P C.condition hε hden v n hall)
    (fun v _ _ hmn hm =>
      C.conditionedTranslation_netWorth_eq_before_failure P hε hden T v hmn hm)
    (fun _ m hm => by rw [show m = 0 from hm]; simp)
    (fun m hm => Nat.pos_of_ne_zero (show m ≠ 0 from hm))
    hfloor

/-- Same-world wealth tracking for the prefix-safe translator.  The conditional trader is
first silenced on the finite exceptional prefix; the base trader then tracks it with the
same total error `1` as the all-days-positive construction. -/
lemma ConditioningPresentation.eventualConditionedTranslation_tracks
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) (F : EventualConditioningFloor P C.condition)
    (T : Trader) (hP : ∀ d φ, 0 ≤ P d φ)
    (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWith ((DP.union extra).D n)) :
    (T.after F.cutoff).netWorth
        (conditionedHistory P C.condition) v n ≤
      (T.eventualConditionedTranslation F).netWorth P v n + 1 := by
  have hlower := T.eventualConditionedTranslation_netWorth_lower
    F hP v n (fun i hi => C.holds_condition_of_le v hi hv)
  linarith

lemma ConditioningPresentation.eventualConditionedTranslation_netWorth_eq_before_failure
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) (F : EventualConditioningFloor P C.condition)
    (T : Trader) (v : PCWorld) {m n : ℕ} (hmn : m ≤ n)
    (hm : ¬v.Holds (C.condition m)) :
    (T.eventualConditionedTranslation F).netWorth P v n =
      ∑ i ∈ Finset.range m,
        ((T.eventualConditionedTranslation F).strat i).value P v.payout := by
  rw [Trader.netWorth]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i hin hirange
  simp only [Finset.mem_range] at hin hirange
  by_cases hic : i < F.cutoff
  · rw [T.eventualConditionedTranslation_strat_of_lt F hic]
    simp [Trader.zero, Strategy.value]
  · have hci : F.cutoff ≤ i := Nat.le_of_not_gt hic
    rw [T.eventualConditionedTranslation_strat_of_le F hci]
    apply
      Strategy.separatedExceptZeroConditionalContract_value_eq_zero_of_not_holds
        (T.strat i) P F.zeroDays C.condition F.epsilon_pos
        F.positive_floor (F.not_mem_of_cutoff_le hci)
        (conditioningBudget i) v
    exact C.not_holds_condition_of_le v (by omega) hm

/-- First-failure downside control for the prefix-safe translator.  If the first failed
condition lies inside the silent prefix, accumulated wealth is exactly zero.  Otherwise
the ordinary preceding-day tracking argument applies after the launch cutoff. -/
lemma ConditioningPresentation.eventualConditionedTranslation_preserves_floor
    {DP extra : DeductiveProcess} (C : ConditioningPresentation DP extra)
    (P : History) (F : EventualConditioningFloor P C.condition)
    (T : Trader) (hP : ∀ d φ, 0 ≤ P d φ)
    (hfloor : BddBelow ((T.after F.cutoff).plausibleAssessments
      (conditionedHistory P C.condition) (DP.union extra))) :
    BddBelow ((T.eventualConditionedTranslation F).plausibleAssessments P DP) :=
  C.preserves_floor_of_before_failure P (fun m => m ≤ F.cutoff)
    (fun v n hall => T.eventualConditionedTranslation_netWorth_lower F hP v n hall)
    (fun v _ _ hmn hm =>
      C.eventualConditionedTranslation_netWorth_eq_before_failure P F T v hmn hm)
    (fun _ m hmc => Finset.sum_eq_zero fun i hi => by
      rw [T.eventualConditionedTranslation_strat_of_lt F
        ((Finset.mem_range.mp hi).trans_le (show m ≤ F.cutoff from hmc))]
      simp [Trader.zero, Strategy.value])
    (fun m hmc => Nat.pos_of_ne_zero fun h =>
      (show ¬ (m ≤ F.cutoff) from hmc) (by omega))
    hfloor

/-- Operational target for the Appendix conditioning trader construction. `translate T`
is the actual base-market trader compiled from a conditional-market trader `T`.
`tracks_on_condition` is the paper's summable-error estimate, while `preserves_floor`
records the separate analysis of worlds that first falsify the growing condition. The
interface contains no exploitation or logical-induction conclusion.
Paper node: `thm:scon` -/
structure ConditioningTraderCompiler
    (P : History) (DP extra : DeductiveProcess)
    (C : ConditioningPresentation DP extra) where
  conditioned_computable : ComputableMarket (conditionedHistory P C.condition)
  translate : Trader → Trader
  translate_ec : ∀ T, EfficientlyComputable T →
    EfficientlyComputable (translate T)
  /-- The same at the paper's own quantifier, ordinary machine polynomial time.  This is a
  field beside `translate_ec` rather than a second structure: the two readings of `def:ec`
  are two certificates about the *same* compiler, and neither implies the other. -/
  translate_machine : ∀ T, MachineEfficientTrader T →
    MachineEfficientTrader (translate T)
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
particular it contains no wealth, boundedness, exploitation, or logical-inductor field.
Paper node: `thm:scon` -/
structure GatedConditioningOperationalWitness
    (P : History) (DP extra : DeductiveProcess)
    (C : ConditioningPresentation DP extra) (ε : ℚ) where
  epsilon_pos : 0 < (ε : ℝ)
  denominator_floor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)
  conditioned_computable : ComputableMarket (conditionedHistory P C.condition)
  translation_ec : ∀ T, EfficientlyComputable T →
    EfficientlyComputable (T.conditionedTranslation C.condition ε)
  /-- The same at the paper's own quantifier. -/
  translation_machine : ∀ T, MachineEfficientTrader T →
    MachineEfficientTrader (T.conditionedTranslation C.condition ε)

/-- Operational target for conditioning directly against the original market once only an
eventual denominator floor is known.  `floor.zeroDays` records the exact finite zero-price
exceptions; unlike a general finite-market patch, the associated compiler needs only a
finite day-membership test and the fixed constant `1`.

Paper node: `thm:scon` -/
structure EventualConditioningOperationalWitness
    (P : History) (DP extra : DeductiveProcess)
    (C : ConditioningPresentation DP extra) where
  floor : EventualConditioningFloor P C.condition
  conditioned_computable : ComputableMarket (conditionedHistory P C.condition)
  translation_ec : ∀ T, EfficientlyComputable T →
    EfficientlyComputable (T.eventualConditionedTranslation floor)
  /-- The same at the paper's own quantifier.  Its realization is the finite-zero price
  emitter of `Construction/Machine/CondStep.lean`, whose zero-day test is a fixed-finite-set
  dispatch clamped at the floor's cutoff. -/
  translation_machine : ∀ T, MachineEfficientTrader T →
    MachineEfficientTrader (T.eventualConditionedTranslation floor)

/-- Assemble a `ConditioningTraderCompiler` from the concrete gated translator.  Both of
the compiler's economic fields are discharged by the lemmas above; only executable
representation data is supplied by the witness. -/
def GatedConditioningOperationalWitness.toCompiler
    {P : History} {DP extra : DeductiveProcess}
    {C : ConditioningPresentation DP extra} {ε : ℚ}
    (W : GatedConditioningOperationalWitness P DP extra C ε) :
    ConditioningTraderCompiler P DP extra C where
  conditioned_computable := W.conditioned_computable
  translate := fun T => T.conditionedTranslation C.condition ε
  translate_ec := W.translation_ec
  translate_machine := W.translation_machine
  tracks_on_condition := fun T n v hv =>
    C.conditionedTranslation_tracks P W.epsilon_pos W.denominator_floor T n v hv
  preserves_floor := fun T hfloor =>
    C.conditionedTranslation_preserves_floor P W.epsilon_pos
      W.denominator_floor T hfloor

/-- Transport of exploitation along a translation that tracks the source trader's wealth
within `1` on every combined-process world.  A world consistent with `(DP.union extra).D n`
is in particular consistent with `DP.D n`, so an upper bound on the translated trader's
plausible assessments bounds the source trader's, contradicting its unboundedness.  This is
the shared unboundedness half of every `exploits_base` lemma below; the differing half is
the bounded-below floor, supplied as `hfloor`. -/
private lemma exploits_base_of_tracks
    {P V : History} {DP extra : DeductiveProcess}
    {T T' : Trader}
    (hT : T.Exploits V (DP.union extra))
    (hfloor : BddBelow (T'.plausibleAssessments P DP))
    (htrack : ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith ((DP.union extra).D n) →
      T.netWorth V v n ≤ T'.netWorth P v n + 1) :
    T'.Exploits P DP := by
  refine ⟨hfloor, ?_⟩
  intro hupper
  apply hT.2
  obtain ⟨U, hU⟩ := hupper
  refine ⟨U + 1, ?_⟩
  intro x hx
  obtain ⟨n, v, hv, rfl⟩ := hx
  have hvBase : v.ConsistentWith (DP.D n) :=
    (PCWorld.consistentWith_union_iff v DP extra n).mp hv |>.1
  have htranslated : T'.netWorth P v n ≤ U := hU ⟨n, v, hvBase, rfl⟩
  exact (htrack n v hv).trans (by linarith)

/-- Witness-free gated transport: a conditional-market exploit compiled through the
gated translator exploits the base market, from the denominator floor alone.
Paper node: `thm:scon` -/
lemma Trader.conditionedTranslation_exploits_base
    {P : History} {DP extra : DeductiveProcess}
    {C : ConditioningPresentation DP extra} {ε : ℚ}
    (hε : 0 < (ε : ℝ)) (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d))
    {T : Trader}
    (hT : T.Exploits (conditionedHistory P C.condition) (DP.union extra)) :
    (T.conditionedTranslation C.condition ε).Exploits P DP :=
  exploits_base_of_tracks hT
    (C.conditionedTranslation_preserves_floor P hε hfloor T hT.1)
    (fun n v hv => C.conditionedTranslation_tracks P hε hfloor T n v hv)

/-- Witness-free eventual transport: the finite-zero exception path, from the floor
structure alone.
Paper node: `thm:scon` -/
lemma Trader.eventualConditionedTranslation_exploits_base
    {P : History} {DP extra : DeductiveProcess} [IsLogicalInductor P DP]
    {C : ConditioningPresentation DP extra}
    (floor : EventualConditioningFloor P C.condition)
    {T : Trader}
    (hT : T.Exploits (conditionedHistory P C.condition) (DP.union extra)) :
    (T.eventualConditionedTranslation floor).Exploits P DP := by
  have hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1 :=
    fun d φ => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) d φ
  have hAfter :
      (T.after floor.cutoff).Exploits
        (conditionedHistory P C.condition) (DP.union extra) :=
    Trader.Exploits.after T (conditionedHistory P C.condition)
      (DP.union extra) (conditionedHistory_mem_Icc P hP C.condition) hT floor.cutoff
  exact exploits_base_of_tracks hAfter
    (C.eventualConditionedTranslation_preserves_floor
      P floor T (fun d φ => (hP d φ).1) hAfter.1)
    (fun n v hv => C.eventualConditionedTranslation_tracks
      P floor T (fun d φ => (hP d φ).1) n v hv)

/-- The explicit compiler contract transports a genuine conditional-market exploit to a
genuine exploit of the base market. The unboundedness proof uses actual same-world wealth
tracking; no abstract exploit certificate is stored in the compiler. -/
lemma ConditioningTraderCompiler.exploits_base
    {P : History} {DP extra : DeductiveProcess}
    {C : ConditioningPresentation DP extra}
    (compiler : ConditioningTraderCompiler P DP extra C)
    {T : Trader}
    (hT : T.Exploits (conditionedHistory P C.condition) (DP.union extra)) :
    (compiler.translate T).Exploits P DP :=
  exploits_base_of_tracks hT (compiler.preserves_floor T hT.1)
    (fun n v hv => compiler.tracks_on_condition T n v hv)

/-- A conditional-market exploit compiled through the finite-zero exception path would
exploit the original base market.  The source exploit is first silenced for finitely many
days; this preserves exploitation by a concrete magnitude bound. -/
lemma EventualConditioningOperationalWitness.exploits_base
    {P : History} {DP extra : DeductiveProcess} [IsLogicalInductor P DP]
    {C : ConditioningPresentation DP extra}
    (W : EventualConditioningOperationalWitness P DP extra C)
    {T : Trader}
    (hT : T.Exploits (conditionedHistory P C.condition) (DP.union extra)) :
    (T.eventualConditionedTranslation W.floor).Exploits P DP :=
  Trader.eventualConditionedTranslation_exploits_base W.floor hT

/-! ## Closure under conditioning (`thm:scon`) -/

/-- Criterion-level Closure Under Conditioning, conditional only on the concrete Appendix
trader compiler above. This statement covers both fixed conditions and growing finite
conjunctions through `ConditioningPresentation`.
Paper node: `thm:scon` -/
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

/-- Closure under conditioning through the concrete gated translator.  Its remaining
premise is operational only: the summable tracking estimate and the first-failure
downside argument are proved here rather than assumed.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) {ε : ℚ}
    (W : GatedConditioningOperationalWitness P DP extra C ε) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned P DP extra C W.toCompiler

/-- **Criterion-level Closure Under Conditioning at the paper's own quantifier**: no trader
in ordinary machine polynomial time exploits the conditioned market either.

The economic content is shared with the fuel-class endpoint: `exploits_base`,
`tracks_on_condition` and `preserves_floor` are the same facts. The two endpoints differ
only in the class the compiler's certificate is stated at, which is why the compiler carries
both certificates as fields. Neither `lic_conditioned` nor this statement is derivable from
the other, so both stand.
Paper node: `thm:scon` -/
theorem lic_conditioned_machine
    (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra)
    (compiler : ConditioningTraderCompiler P DP extra C) :
    IsMachineLogicalInductor (conditionedHistory P C.condition) (DP.union extra) where
  marketComputable := compiler.conditioned_computable
  processComputable := C.combined_computable
  noExploit T hTm hTexp :=
    IsMachineLogicalInductor.noExploit (P := P) (DP := DP)
      (compiler.translate T) (compiler.translate_machine T hTm)
      (compiler.exploits_base hTexp)

/-- Closure under conditioning through the concrete gated translator, at the paper's own
quantifier.
Paper node: `thm:scon` -/
theorem lic_conditioned_gated_machine
    (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra) {ε : ℚ}
    (W : GatedConditioningOperationalWitness P DP extra C ε) :
    IsMachineLogicalInductor (conditionedHistory P C.condition) (DP.union extra) :=
  lic_conditioned_machine P DP extra C W.toCompiler

/-- Closure under conditioning through the prefix-safe finite-zero compiler.  This theorem
does not modify the base history and therefore does not depend on unrestricted
finite-perturbation closure.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventual
    (P : History) (DP extra : DeductiveProcess) [IsLogicalInductor P DP]
    (C : ConditioningPresentation DP extra)
    (W : EventualConditioningOperationalWitness P DP extra C) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) where
  marketComputable := W.conditioned_computable
  processComputable := C.combined_computable
  noExploit T hTec hTexp :=
    IsLogicalInductor.noExploit (P := P) (DP := DP)
      (T.eventualConditionedTranslation W.floor)
      (W.translation_ec T hTec) (W.exploits_base hTexp)

/-- Closure under conditioning through the prefix-safe finite-zero compiler, at the paper's
own quantifier.  This completes `thm:scon` at the machine class in all three forms.
Paper node: `thm:scon` -/
theorem lic_conditioned_eventual_machine
    (P : History) (DP extra : DeductiveProcess) [IsMachineLogicalInductor P DP]
    (C : ConditioningPresentation DP extra)
    (W : EventualConditioningOperationalWitness P DP extra C) :
    IsMachineLogicalInductor (conditionedHistory P C.condition) (DP.union extra) where
  marketComputable := W.conditioned_computable
  processComputable := C.combined_computable
  noExploit T hTm hTexp :=
    IsMachineLogicalInductor.noExploit (P := P) (DP := DP)
      (T.eventualConditionedTranslation W.floor)
      (W.translation_machine T hTm) (W.exploits_base hTexp)

end LogicalInduction
