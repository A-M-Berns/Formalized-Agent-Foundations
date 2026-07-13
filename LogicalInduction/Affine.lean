/-
# Affine combinations — shared M4 lift substrate

The paper's affine hubs trade expressions `c + Σ eᵢ φᵢ`.  A trade contains only the
sentence coefficients: buying the combination on day `n` automatically contributes the
cash term `-Pₙ(c + Σ eᵢ φᵢ)`, so the explicit affine constant cancels.  Keeping the
combination as syntax is nevertheless essential: its price and its value in a world are the
objects compared by affine provability/preemptive learning.
-/
import LogicalInduction.Engine
import LogicalInduction.Computable

namespace LogicalInduction

/-- `def:affcomsen`. An affine combination `c + Σ eᵢ φᵢ` with expressible-feature
coefficients. Repeated sentences are allowed, matching `Strategy`; normalization is not
needed for the value and magnitude arguments. -/
structure AffineCombination where
  const : EF
  terms : List (EF × Sentence)

namespace AffineCombination

/-- Value of an affine combination under a history (for its feature coefficients) and an
arbitrary valuation of its sentences. -/
noncomputable def value (A : AffineCombination) (V : History) (w : Valuation) : ℝ :=
  A.const.denote V + (A.terms.map (fun p => p.1.denote V * w p.2)).sum

/-- Market price of an affine combination on day `n`. -/
noncomputable def price (A : AffineCombination) (V : History) (n : ℕ) : ℝ :=
  A.value V (V n)

/-- The day-`n` market price of `A`, represented inside the expressible-feature DSL. -/
def priceFeature (A : AffineCombination) (n : ℕ) : EF :=
  A.terms.foldl (fun acc p => .add acc (.mul p.1 (.price p.2 n))) A.const

theorem priceFeature_denote (A : AffineCombination) (V : History) (n : ℕ) :
    (A.priceFeature n).denote V = A.price V n := by
  rw [price, value, priceFeature]
  have aux : ∀ (l : List (EF × Sentence)) (c : EF),
      (l.foldl (fun acc p => .add acc (.mul p.1 (.price p.2 n))) c).denote V =
        c.denote V + (l.map (fun p => p.1.denote V * V n p.2)).sum := by
    intro l
    induction l with
    | nil => intro c; simp
    | cons p ps ih =>
        intro c
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih]
        simp only [EF.denote_add, EF.denote_mul, EF.denote_price,
          Pi.add_apply, Pi.mul_apply]
        ring
  exact aux A.terms A.const

theorem priceFeature_rank (A : AffineCombination) {k n : ℕ} (hkn : k ≤ n)
    (hc : A.const.rank ≤ k) (ht : ∀ p ∈ A.terms, p.1.rank ≤ k) :
    (A.priceFeature n).rank ≤ n := by
  rw [priceFeature]
  have aux : ∀ (l : List (EF × Sentence)) (c : EF),
      c.rank ≤ n → (∀ p ∈ l, p.1.rank ≤ k) →
      (l.foldl (fun acc p => .add acc (.mul p.1 (.price p.2 n))) c).rank ≤ n := by
    intro l
    induction l with
    | nil => intro c hc' _; simpa using hc'
    | cons p ps ih =>
        intro c hc' ht'
        simp only [List.foldl_cons]
        apply ih
        · simp only [EF.rank]
          exact Nat.max_le.mpr ⟨hc', Nat.max_le.mpr ⟨(ht' p (by simp)).trans hkn, le_rfl⟩⟩
        · intro q hq
          exact ht' q (by simp [hq])
  exact aux A.terms A.const (hc.trans hkn) ht

/-- Share magnitude of an affine combination, omitting its constant term as in
`def:tradermag`. -/
noncomputable def magnitude (A : AffineCombination) (V : History) : ℝ :=
  (A.terms.map (fun p => |p.1.denote V|)).sum

theorem magnitude_nonneg (A : AffineCombination) (V : History) :
    0 ≤ A.magnitude V :=
  List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact abs_nonneg _)

/-- Buying `A` on day `n`: purchase each sentence coefficient at the current market price.
The affine constant needs no trade because it cancels between world value and price. -/
def buy (A : AffineCombination) (n : ℕ)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ n) : Strategy n where
  trades := A.terms
  rank_le := hrank

@[simp] theorem buy_trades (A : AffineCombination) (n : ℕ)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ n) :
    (A.buy n hrank).trades = A.terms := rfl

/-- The value of buying an affine combination is its world value minus its current price. -/
theorem buy_value (A : AffineCombination) (V : History) (w : Valuation) (n : ℕ)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ n) :
    (A.buy n hrank).value V w = A.value V w - A.price V n := by
  simp only [Strategy.value, buy, value, price]
  induction A.terms with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

/-- The magnitude of the buy strategy is exactly the affine combination's share
magnitude. -/
theorem buy_magnitude (A : AffineCombination) (V : History) (n : ℕ)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ n) :
    (A.buy n hrank).magnitude V = A.magnitude V := rfl

/-- Scale every coefficient, including the affine constant, by an expressible feature. -/
def scale (e : EF) (A : AffineCombination) : AffineCombination where
  const := .mul e A.const
  terms := A.terms.map (fun p => (.mul e p.1, p.2))

theorem scale_value (e : EF) (A : AffineCombination) (V : History) (w : Valuation) :
    (A.scale e).value V w = e.denote V * A.value V w := by
  simp only [scale, value, EF.denote_mul, Pi.mul_apply, List.map_map]
  have hsum :
      (A.terms.map ((fun p => p.1.denote V * w p.2) ∘
        fun p => (EF.mul e p.1, p.2))).sum =
        e.denote V * (A.terms.map (fun p => p.1.denote V * w p.2)).sum := by
    induction A.terms with
    | nil => simp
    | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons, Function.comp_apply,
          EF.denote_mul, Pi.mul_apply] at ih ⊢
        rw [ih]
        ring
  rw [hsum]
  ring

theorem scale_price (e : EF) (A : AffineCombination) (V : History) (n : ℕ) :
    (A.scale e).price V n = e.denote V * A.price V n := by
  simp [price, scale_value]

/-- Negation of an affine combination. -/
def neg (A : AffineCombination) : AffineCombination := A.scale (.const (-1))

theorem neg_value (A : AffineCombination) (V : History) (w : Valuation) :
    A.neg.value V w = -A.value V w := by
  simp [neg, scale_value]

theorem neg_price (A : AffineCombination) (V : History) (n : ℕ) :
    A.neg.price V n = -A.price V n := by
  simp [neg, scale_price]

end AffineCombination

#print axioms AffineCombination.buy_value
#print axioms AffineCombination.scale_value
#print axioms AffineCombination.priceFeature_denote

end LogicalInduction
