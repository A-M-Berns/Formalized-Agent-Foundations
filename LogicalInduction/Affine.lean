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

/-- Absolute value inside the expressible-feature DSL. -/
def absFeature (e : EF) : EF :=
  .max e (.mul (.const (-1)) e)

theorem absFeature_denoteWith (e : EF) (V : History) (ρ : List ℝ) :
    (absFeature e).denoteWith ρ V = |e.denoteWith ρ V| := by
  simp only [absFeature, EF.denoteWith, Rat.cast_neg, Rat.cast_one, neg_mul, one_mul]
  rw [abs_eq_max_neg]

@[simp] theorem absFeature_rank (e : EF) : (absFeature e).rank = e.rank := by
  simp [absFeature, EF.rank]

/-- Share magnitude reified as an expressible feature. -/
def magnitudeFeature (A : AffineCombination) : EF :=
  A.terms.foldr (fun p acc => EF.add (absFeature p.1) acc) (EF.const 0)

theorem magnitudeFeature_denoteWith (A : AffineCombination) (V : History) (ρ : List ℝ) :
    (A.magnitudeFeature).denoteWith ρ V =
      (A.terms.map (fun p => |p.1.denoteWith ρ V|)).sum := by
  have aux : ∀ l : List (EF × Sentence),
      (l.foldr (fun p acc => EF.add (absFeature p.1) acc) (EF.const 0)).denoteWith ρ V =
        (l.map (fun p => |p.1.denoteWith ρ V|)).sum := by
    intro l
    induction l with
    | nil => simp [EF.denoteWith]
    | cons p ps ih =>
        simp only [List.foldr_cons, EF.denoteWith, absFeature_denoteWith,
          List.map_cons, List.sum_cons, ih]
  exact aux A.terms

theorem magnitudeFeature_denote (A : AffineCombination) (V : History) :
    A.magnitudeFeature.denote V = A.magnitude V := by
  rw [EF.denote, magnitudeFeature_denoteWith]
  rfl

theorem magnitudeFeature_rank_le (A : AffineCombination) {n : ℕ}
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ n) : A.magnitudeFeature.rank ≤ n := by
  have aux : ∀ l : List (EF × Sentence),
      (∀ p ∈ l, p.1.rank ≤ n) →
      (l.foldr (fun p acc => EF.add (absFeature p.1) acc) (EF.const 0)).rank ≤ n := by
    intro l
    induction l with
    | nil => intro _; simp [EF.rank]
    | cons p ps ih =>
        intro h
        simp only [List.foldr_cons, EF.rank, absFeature_rank]
        exact Nat.max_le.mpr ⟨h p (by simp), ih (fun q hq => h q (by simp [hq]))⟩
  exact aux A.terms hterms

/-- Launch-risk feature for an entry-weighted affine component. -/
def riskFeature (A : AffineCombination) (entry : EF) : EF :=
  EF.mul entry A.magnitudeFeature

theorem riskFeature_denote (A : AffineCombination) (entry : EF) (V : History) :
    (A.riskFeature entry).denote V = entry.denote V * A.magnitude V := by
  simp [riskFeature, EF.denote_mul, magnitudeFeature_denote]

theorem riskFeature_rank_le (A : AffineCombination) (entry : EF) {n : ℕ}
    (hentry : entry.rank ≤ n) (hterms : ∀ p ∈ A.terms, p.1.rank ≤ n) :
    (A.riskFeature entry).rank ≤ n := by
  simp only [riskFeature, EF.rank]
  exact Nat.max_le.mpr ⟨hentry, A.magnitudeFeature_rank_le hterms⟩

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

/-- An affine combination's world value differs from its market price by at most its
share magnitude. The affine constant cancels, so it contributes no risk. -/
theorem abs_value_sub_price_le_magnitude (A : AffineCombination) (V : History)
    (w : Valuation) (n : ℕ) (hrank : ∀ p ∈ A.terms, p.1.rank ≤ n)
    (hw : ∀ φ, w φ = 0 ∨ w φ = 1) (hV : ∀ φ, 0 ≤ V n φ ∧ V n φ ≤ 1) :
    |A.value V w - A.price V n| ≤ A.magnitude V := by
  rw [← A.buy_value V w n hrank, ← A.buy_magnitude V n hrank]
  exact Strategy.abs_value_le_magnitude (A.buy n hrank) V w hw hV

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

theorem scale_magnitude (e : EF) (A : AffineCombination) (V : History) :
    (A.scale e).magnitude V = |e.denote V| * A.magnitude V := by
  simp only [scale, magnitude, List.map_map]
  induction A.terms with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, EF.denote_mul,
        Pi.mul_apply, abs_mul, ih]
      ring

theorem scale_terms_rank_le (e : EF) (A : AffineCombination) {n : ℕ}
    (he : e.rank ≤ n) (hA : ∀ p ∈ A.terms, p.1.rank ≤ n) :
    ∀ p ∈ (A.scale e).terms, p.1.rank ≤ n := by
  intro p hp
  simp only [scale, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [EF.rank]
  exact Nat.max_le.mpr ⟨he, hA q hq⟩

/-- Negation of an affine combination. -/
def neg (A : AffineCombination) : AffineCombination := A.scale (.const (-1))

theorem neg_value (A : AffineCombination) (V : History) (w : Valuation) :
    A.neg.value V w = -A.value V w := by
  simp [neg, scale_value]

theorem neg_price (A : AffineCombination) (V : History) (n : ℕ) :
    A.neg.price V n = -A.price V n := by
  simp [neg, scale_price]

theorem neg_magnitude (A : AffineCombination) (V : History) :
    A.neg.magnitude V = A.magnitude V := by
  simp only [neg, scale, magnitude, List.map_map]
  induction A.terms with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply, EF.denote_mul,
        Pi.mul_apply, EF.denote_const, Rat.cast_neg, Rat.cast_one, neg_mul,
        one_mul, abs_neg, ih]

/-! ## Finite round trips

The affine-preemptive-learning trader is assembled from finite buy-low/sell-high round
trips.  The lemmas below isolate their world-independent payoff; later constructions only
have to choose their opening weights and verified closing days.
-/

theorem neg_terms_rank_le (A : AffineCombination) {n : ℕ}
    (h : ∀ p ∈ A.terms, p.1.rank ≤ n) :
    ∀ p ∈ A.neg.terms, p.1.rank ≤ n := by
  intro p hp
  simp only [neg, scale, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  simp only [EF.rank]
  exact Nat.max_le.mpr ⟨by simp, h q hq⟩

/-- The empty strategy at an arbitrary day. -/
def emptyStrategy (n : ℕ) : Strategy n where
  trades := []
  rank_le := by simp

/-- Buy `A` on `buyDay`, sell the same affine position on `sellDay`, and otherwise do
nothing.  The strict ordering makes the two exceptional days disjoint. -/
def roundTrip (A : AffineCombination) (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) : Trader where
  strat n := by
    by_cases ho : n = buyDay
    · subst n
      exact A.buy buyDay hrank
    · by_cases hc : n = sellDay
      · subst n
        exact A.neg.buy sellDay (A.neg_terms_rank_le
          (fun p hp => (hrank p hp).trans (Nat.le_of_lt hopen)))
      · exact emptyStrategy n

@[simp] theorem roundTrip_strat_open (A : AffineCombination) (buyDay sellDay : ℕ)
    (hopen : buyDay < sellDay) (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    (A.roundTrip buyDay sellDay hopen hrank).strat buyDay = A.buy buyDay hrank := by
  simp [roundTrip]

theorem roundTrip_strat_close (A : AffineCombination) (buyDay sellDay : ℕ)
    (hopen : buyDay < sellDay) (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    (A.roundTrip buyDay sellDay hopen hrank).strat sellDay =
      A.neg.buy sellDay (A.neg_terms_rank_le
        (fun p hp => (hrank p hp).trans (Nat.le_of_lt hopen))) := by
  simp [roundTrip, ne_of_gt hopen]

theorem roundTrip_strat_other (A : AffineCombination) (buyDay sellDay n : ℕ)
    (hopen : buyDay < sellDay) (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay)
    (ho : n ≠ buyDay) (hc : n ≠ sellDay) :
    (A.roundTrip buyDay sellDay hopen hrank).strat n = emptyStrategy n := by
  simp [roundTrip, ho, hc]

theorem roundTrip_value_open (A : AffineCombination) (V : History) (w : Valuation)
    (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    ((A.roundTrip buyDay sellDay hopen hrank).strat buyDay).value V w =
      A.value V w - A.price V buyDay := by
  rw [roundTrip_strat_open]
  exact A.buy_value V w buyDay hrank

theorem roundTrip_value_close (A : AffineCombination) (V : History) (w : Valuation)
    (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    ((A.roundTrip buyDay sellDay hopen hrank).strat sellDay).value V w =
      -A.value V w + A.price V sellDay := by
  rw [roundTrip_strat_close]
  rw [A.neg.buy_value]
  rw [neg_value, neg_price]
  ring

theorem roundTrip_value_other (A : AffineCombination) (V : History) (w : Valuation)
    (buyDay sellDay n : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay)
    (ho : n ≠ buyDay) (hc : n ≠ sellDay) :
    ((A.roundTrip buyDay sellDay hopen hrank).strat n).value V w = 0 := by
  rw [roundTrip_strat_other A buyDay sellDay n hopen hrank ho hc]
  simp [emptyStrategy, Strategy.value]

theorem roundTrip_magnitude_open (A : AffineCombination) (V : History)
    (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    ((A.roundTrip buyDay sellDay hopen hrank).strat buyDay).magnitude V =
      A.magnitude V := by
  rw [roundTrip_strat_open]
  exact A.buy_magnitude V buyDay hrank

theorem roundTrip_magnitude_close (A : AffineCombination) (V : History)
    (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    ((A.roundTrip buyDay sellDay hopen hrank).strat sellDay).magnitude V =
      A.magnitude V := by
  rw [roundTrip_strat_close]
  rw [A.neg.buy_magnitude, neg_magnitude]

theorem roundTrip_magnitude_other (A : AffineCombination) (V : History)
    (buyDay sellDay n : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay)
    (ho : n ≠ buyDay) (hc : n ≠ sellDay) :
    ((A.roundTrip buyDay sellDay hopen hrank).strat n).magnitude V = 0 := by
  rw [roundTrip_strat_other A buyDay sellDay n hopen hrank ho hc]
  simp [emptyStrategy, Strategy.magnitude]

theorem roundTrip_summable (A : AffineCombination) (V : History)
    (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    Summable (fun n =>
      ((A.roundTrip buyDay sellDay hopen hrank).strat n).magnitude V) := by
  apply summable_of_finite_support
  refine ((Set.finite_singleton sellDay).insert buyDay).subset ?_
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hdays
  push_neg at hdays
  exact hn (roundTrip_magnitude_other A V buyDay sellDay n hopen hrank hdays.1 hdays.2)

/-- A round trip moves exactly two copies of the affine share magnitude. -/
theorem roundTrip_magnitude (A : AffineCombination) (V : History)
    (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) :
    (A.roundTrip buyDay sellDay hopen hrank).magnitude V = 2 * A.magnitude V := by
  let f : ℕ → ℝ := fun n =>
    ((A.roundTrip buyDay sellDay hopen hrank).strat n).magnitude V
  have hsum : Summable f := roundTrip_summable A V buyDay sellDay hopen hrank
  rw [Trader.magnitude]
  change ∑' n, f n = _
  rw [hsum.tsum_eq_add_tsum_ite buyDay]
  have hbuy : f buyDay = A.magnitude V :=
    roundTrip_magnitude_open A V buyDay sellDay hopen hrank
  rw [hbuy]
  have hrest : (∑' n, if n = buyDay then 0 else f n) = A.magnitude V := by
    calc
      (∑' n, if n = buyDay then 0 else f n) =
          ∑' n, if n = sellDay then A.magnitude V else 0 := by
            apply tsum_congr
            intro n
            by_cases hb : n = buyDay
            · subst n
              simp [ne_of_lt hopen]
            · by_cases hs : n = sellDay
              · subst n
                rw [if_neg hb, if_pos rfl]
                exact roundTrip_magnitude_close A V buyDay sellDay hopen hrank
              · rw [if_neg hb, if_neg hs]
                exact roundTrip_magnitude_other A V buyDay sellDay n hopen hrank hb hs
      _ = A.magnitude V := by
        simpa using tsum_ite_eq sellDay (fun _ : ℕ => A.magnitude V)
  rw [hrest]
  ring

/-- After the closing day, every world assigns the round trip exactly the realized price
difference.  All sentence holdings cancel. -/
theorem roundTrip_netWorth (A : AffineCombination) (V : History) (v : PCWorld)
    (buyDay sellDay n : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (hn : sellDay ≤ n) :
    (A.roundTrip buyDay sellDay hopen hrank).netWorth V v n =
      A.price V sellDay - A.price V buyDay := by
  rw [Trader.netWorth]
  let f : ℕ → ℝ := fun i =>
    ((A.roundTrip buyDay sellDay hopen hrank).strat i).value V v.payout
  have hc : sellDay ∈ Finset.range (n + 1) := by simp; omega
  rw [Finset.sum_eq_add_sum_diff_singleton hc]
  rw [Finset.sdiff_singleton_eq_erase]
  have ho : buyDay ∈ (Finset.range (n + 1)).erase sellDay := by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨ne_of_lt hopen, by omega⟩
  rw [Finset.sum_eq_add_sum_diff_singleton ho]
  rw [Finset.sdiff_singleton_eq_erase]
  have hz : ∑ x ∈ ((Finset.range (n + 1)).erase sellDay).erase buyDay, f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_erase] at hx
    exact roundTrip_value_other A V v.payout buyDay sellDay x hopen hrank hx.1 hx.2.1
  rw [hz, add_zero]
  rw [roundTrip_value_close, roundTrip_value_open]
  ring

/-- Any realized price gain that covers `rate` times the two-sided share volume gives a
`rate`-ROI witness, uniformly over all plausible worlds. -/
theorem roundTrip_hasROI (A : AffineCombination) (V : History) (DP : DeductiveProcess)
    (buyDay sellDay : ℕ) (hopen : buyDay < sellDay)
    (hrank : ∀ p ∈ A.terms, p.1.rank ≤ buyDay) (rate : ℝ)
    (hprofit : rate * (2 * A.magnitude V) ≤
      A.price V sellDay - A.price V buyDay) :
    HasROI (A.roundTrip buyDay sellDay hopen hrank) V DP rate := by
  constructor
  · exact roundTrip_summable A V buyDay sellDay hopen hrank
  · intro η hη
    refine ⟨sellDay, fun n hn v _ => ?_⟩
    rw [roundTrip_magnitude, roundTrip_netWorth A V v buyDay sellDay n hopen hrank hn]
    have hmag := A.magnitude_nonneg V
    nlinarith

end AffineCombination

#print axioms AffineCombination.buy_value
#print axioms AffineCombination.abs_value_sub_price_le_magnitude
#print axioms AffineCombination.magnitudeFeature_denote
#print axioms AffineCombination.riskFeature_denote
#print axioms AffineCombination.scale_value
#print axioms AffineCombination.priceFeature_denote
#print axioms AffineCombination.roundTrip_netWorth
#print axioms AffineCombination.roundTrip_magnitude
#print axioms AffineCombination.roundTrip_hasROI

end LogicalInduction
