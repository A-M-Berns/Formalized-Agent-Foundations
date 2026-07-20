/-
# Affine combinations — shared M4 lift substrate

Hosts `def:tradermag` (`Strategy.magnitude`, `Trader.magnitude`) and the trade
value/net-worth bounds formerly in `Engine.lean`, followed by the affine-combination
syntax the M4 lift hubs consume.

The paper's affine hubs trade expressions `c + Σ eᵢ φᵢ`.  A trade contains only the
sentence coefficients: buying the combination on day `n` automatically contributes the
cash term `-Pₙ(c + Σ eᵢ φᵢ)`, so the explicit affine constant cancels.  Keeping the
combination as syntax is nevertheless essential: its price and its value in a world are the
objects compared by affine provability/preemptive learning.
-/
import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.Asymptotics
import LogicalInduction.Framework.Computable
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace LogicalInduction

open Filter Topology

/-! ## `def:tradermag` — Magnitude

The magnitude of a trade is the total number of shares it moves, `∑_φ |T[φ](𝓥)|` — the
constant (cash) term omitted. It is the "investment" against which return is measured. -/

namespace Strategy

/-- The magnitude of an `n`-strategy against a history `𝓥`: the total absolute share
volume `∑ᵢ |eᵢ(𝓥)|`. (For a strategy in which a sentence occurs once, this is exactly
`∑_φ |T[φ]|`; with repeats it is an upper bound, which is all the value bound needs.) -/
noncomputable def magnitude {n : ℕ} (T : Strategy n) (V : History) : ℝ :=
  (T.trades.map (fun p => |p.1.denote V|)).sum

theorem magnitude_nonneg {n : ℕ} (T : Strategy n) (V : History) : 0 ≤ T.magnitude V :=
  List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx; obtain ⟨p, _, rfl⟩ := hx; exact abs_nonneg _)

end Strategy

/-- Triangle-inequality bound for a `List.sum` of mapped terms: if `|f x| ≤ g x` pointwise,
then `|∑ f| ≤ ∑ g`. -/
private theorem abs_map_sum_le {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, |f x| ≤ g x) : |(l.map f).sum| ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := h a (List.mem_cons_self ..)
      have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      calc |f a + (t.map f).sum| ≤ |f a| + |(t.map f).sum| := abs_add_le _ _
        _ ≤ g a + (t.map g).sum := by linarith

/-- **Magnitude bound** (`def:tradermag`). In a market with prices in `[0,1]`, a strategy's
value in any `{0,1}`-world is bounded by its magnitude: a share is worth at most 1 and costs
at least 0, so `|value| ≤ Σ|shares| = magnitude`. The basic tool behind return-on-investment
estimates. -/
theorem Strategy.abs_value_le_magnitude {n : ℕ} (T : Strategy n) (V : History)
    (w : Sentence → ℝ) (hw : ∀ φ, w φ = 0 ∨ w φ = 1)
    (hV : ∀ φ, 0 ≤ V n φ ∧ V n φ ≤ 1) :
    |T.value V w| ≤ T.magnitude V := by
  simp only [Strategy.value, Strategy.magnitude]
  refine abs_map_sum_le T.trades _ _ (fun p _ => ?_)
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  rcases hw p.2 with h | h <;> rcases hV p.2 with ⟨h0, h1⟩ <;> rw [h, abs_le] <;>
    constructor <;> linarith

/-- The total magnitude of a trader against `𝓥`: `∑ₙ |Tₙ(𝓥)|` (`def:tradermag`). As a
possibly-divergent series it is a `tsum`, meaningful for *bounded* traders (finite total
magnitude); the `def:roi` predicate below is what consumes it. -/
noncomputable def Trader.magnitude (Tr : Trader) (V : History) : ℝ :=
  ∑' n, (Tr.strat n).magnitude V

/-! ## `def:roi` — ε-Return on Investment -/

/-- `def:roi`. A trader has **ε return on investment** against `V` relative to `DP` when
its total share magnitude is finite and, uniformly over worlds still plausible at late
times, its net worth is eventually at least `(ε-η)` times that magnitude for every `η>0`.

The paper states the limit inequality over all worlds consistent with the completed theory
and derives this operational form by compactness plus enumeration of `DP`. Our propositional
substrate does not package the completed theory or a computability witness for `DP`, so the
uniform plausible-world form is carried explicitly. It is exactly the form the repeatable-ROI
maturity search consumes, and avoids silently assuming an unavailable uniformization lemma. -/
def HasROI (Tr : Trader) (V : History) (DP : DeductiveProcess) (ε : ℝ) : Prop :=
  Summable (fun n => (Tr.strat n).magnitude V) ∧
    ∀ η : ℝ, 0 < η → ∃ N, ∀ n, N ≤ n → ∀ v : PCWorld,
      v.ConsistentWith (DP.D n) → (ε - η) * Tr.magnitude V ≤ Tr.netWorth V v n

/-! ### Finite-magnitude risk bound

The summability clause above is load-bearing. In Mathlib, `tsum` of a non-summable real
series is defined as `0`; omitting summability would therefore let an infinite-risk trader
claim zero magnitude. The following lemmas turn genuine finite magnitude into the uniform
lower bound required by `Exploits`. -/

theorem Trader.partial_magnitude_le (Tr : Trader) (V : History)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V ≤ Tr.magnitude V := by
  exact hmag.sum_le_tsum _ (fun i _ => Strategy.magnitude_nonneg (Tr.strat i) V)

/-- Magnitude is nonnegative (including Mathlib's zero value for a divergent nonnegative
series; finiteness is still required everywhere that magnitude represents actual risk). -/
theorem Trader.magnitude_nonneg (Tr : Trader) (V : History) : 0 ≤ Tr.magnitude V := by
  exact tsum_nonneg (fun n => Strategy.magnitude_nonneg (Tr.strat n) V)

/-- Partial magnitudes eventually contain any prescribed `(1-η)` fraction of the total
magnitude. -/
theorem Trader.eventually_partial_magnitude_ge (Tr : Trader) (V : History)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) {η : ℝ} (hη : 0 < η) :
    ∃ N, ∀ n, N ≤ n →
      (1 - η) * Tr.magnitude V ≤
        ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V := by
  by_cases hzero : Tr.magnitude V = 0
  · refine ⟨0, fun n _ => ?_⟩
    rw [hzero, mul_zero]
    exact Finset.sum_nonneg (fun i _ => Strategy.magnitude_nonneg (Tr.strat i) V)
  · have htot : 0 < Tr.magnitude V := lt_of_le_of_ne
      (Tr.magnitude_nonneg V) (Ne.symm hzero)
    have htend : Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, (Tr.strat i).magnitude V)
        atTop (𝓝 (Tr.magnitude V)) := hmag.hasSum.tendsto_sum_nat
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htend (η * Tr.magnitude V)
      (mul_pos hη htot)
    refine ⟨N, fun n hn => ?_⟩
    have hclose := hN (n + 1) (by omega)
    rw [Real.dist_eq] at hclose
    have hlo : Tr.magnitude V - η * Tr.magnitude V <
        ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V := by
      rw [abs_lt] at hclose
      linarith [hclose.1]
    nlinarith

/-- Operational maturity used by the repeatable-ROI budgeter: almost all magnitude has
already been traded, and the current holdings are uniformly profitable in every plausible
world. -/
def Trader.Matured (Tr : Trader) (V : History) (DP : DeductiveProcess)
    (ε η : ℝ) (m : ℕ) : Prop :=
  (1 - η) * Tr.magnitude V ≤
      ∑ i ∈ Finset.range (m + 1), (Tr.strat i).magnitude V ∧
    ∀ v : PCWorld, v.ConsistentWith (DP.D m) →
      (ε - η) * Tr.magnitude V ≤ Tr.netWorth V v m

/-- Every positive-ROI trader matures at some finite stage, for any positive tolerance. -/
theorem HasROI.exists_matured {Tr : Trader} {V : History} {DP : DeductiveProcess}
    {ε η : ℝ} (hroi : HasROI Tr V DP ε) (hη : 0 < η) :
    ∃ m, Tr.Matured V DP ε η m := by
  obtain ⟨hmag, hprofit⟩ := hroi
  obtain ⟨Nmag, hNmag⟩ := Tr.eventually_partial_magnitude_ge V hmag hη
  obtain ⟨Nprofit, hNprofit⟩ := hprofit η hη
  refine ⟨max Nmag Nprofit, hNmag _ (le_max_left _ _), ?_⟩
  exact hNprofit _ (le_max_right _ _)

/-- At every finite day, a finite-magnitude trader's net worth in any Boolean world is
bounded in absolute value by its total magnitude. -/
theorem Trader.abs_netWorth_le_magnitude (Tr : Trader) (V : History) (v : PCWorld)
    (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) (n : ℕ) :
    |Tr.netWorth V v n| ≤ Tr.magnitude V := by
  calc
    |Tr.netWorth V v n|
        ≤ ∑ i ∈ Finset.range (n + 1), |(Tr.strat i).value V v.payout| := by
          simpa [Trader.netWorth] using
            (Finset.abs_sum_le_sum_abs (s := Finset.range (n + 1))
              (f := fun i => (Tr.strat i).value V v.payout))
    _ ≤ ∑ i ∈ Finset.range (n + 1), (Tr.strat i).magnitude V := by
          exact Finset.sum_le_sum (fun i _ => Strategy.abs_value_le_magnitude
            (Tr.strat i) V v.payout (fun φ => by
              by_cases hφ : v.Holds φ
              · exact Or.inr (by simp [PCWorld.payout, hφ])
              · exact Or.inl (by simp [PCWorld.payout, hφ])) (hP i))
    _ ≤ Tr.magnitude V := Tr.partial_magnitude_le V hmag n

/-- Finite total magnitude supplies the bounded-downside half of exploitation uniformly
over all plausible worlds. -/
theorem Trader.bddBelow_plausible_of_finiteMagnitude (Tr : Trader) (V : History)
    (DP : DeductiveProcess) (hP : ∀ n φ, 0 ≤ V n φ ∧ V n φ ≤ 1)
    (hmag : Summable (fun n => (Tr.strat n).magnitude V)) :
    BddBelow (Tr.plausibleAssessments V DP) := by
  refine ⟨-Tr.magnitude V, ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  have h := Tr.abs_netWorth_le_magnitude V v hP hmag n
  exact (neg_le_of_abs_le h)

#print axioms Trader.abs_netWorth_le_magnitude

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

/-- Operational certificate for a polynomially generated, rank-legal sequence of affine
combinations.  The paired index for a term is `⟨n,j⟩`: sequence member, then term number.
This is the affine analogue of `PolyTradeEmulatable`; it exposes syntax boundaries so
uniform transformations can emit coefficients and sentence codes without decoding an
opaque serialized value. -/
structure PolySequence (As : ℕ → AffineCombination) where
  termCount : ℕ → ℕ
  coefficient : ℕ → EF
  sentence : ℕ → Sentence
  termCount_poly : ∃ c, PolyFueled c termCount
  const_poly : PolySegStream (fun n => (As n).const.serialize)
  coefficient_poly : PolySegStream (fun z => (coefficient z).serialize)
  sentence_poly : ∃ c, PolyFueled c (fun z => Encodable.encode (sentence z))
  terms_eq : ∀ n,
    (As n).terms = (List.range (termCount n)).map (fun j =>
      (coefficient (Nat.pair n j), sentence (Nat.pair n j)))
  const_rank : ∀ n, (As n).const.rank ≤ n
  coefficient_rank : ∀ n j, j < termCount n → (coefficient (Nat.pair n j)).rank ≤ n
  const_closed : ∀ n ρ V, (As n).const.denoteWith ρ V = (As n).const.denote V
  coefficient_closed : ∀ z ρ V,
    (coefficient z).denoteWith ρ V = (coefficient z).denote V

theorem PolySequence.terms_rank {As : ℕ → AffineCombination} (h : PolySequence As)
    (n : ℕ) : ∀ p ∈ (As n).terms, p.1.rank ≤ n := by
  intro p hp
  rw [h.terms_eq] at hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  exact h.coefficient_rank n j hj

theorem PolySequence.term_closed {As : ℕ → AffineCombination} (h : PolySequence As)
    (n : ℕ) : ∀ p ∈ (As n).terms, ∀ ρ V,
      p.1.denoteWith ρ V = p.1.denote V := by
  intro p hp ρ V
  rw [h.terms_eq] at hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨j, _, rfl⟩ := hp
  exact h.coefficient_closed (Nat.pair n j) ρ V

/-- Market price of an affine combination on day `n`. -/
noncomputable def price (A : AffineCombination) (V : History) (n : ℕ) : ℝ :=
  A.value V (V n)

/-- The day-`n` market price of `A`, represented inside the expressible-feature DSL. -/
def priceFeature (A : AffineCombination) (n : ℕ) : EF :=
  A.terms.foldl (fun acc p => .add acc (.mul p.1 (.price p.2 n))) A.const

/-- Serialization of an affine price feature as its constant prefix followed by one
coefficient/price/multiply/add block per term. -/
theorem priceFeature_serialize (A : AffineCombination) (n : ℕ) :
    (A.priceFeature n).serialize = A.const.serialize ++
      A.terms.flatMap (fun p =>
        p.1.serialize ++ (EF.price p.2 n).serialize ++ [3, 2]) := by
  rw [priceFeature]
  have aux : ∀ (l : List (EF × Sentence)) (c : EF),
      (l.foldl (fun acc p => EF.add acc (EF.mul p.1 (EF.price p.2 n))) c).serialize =
        c.serialize ++ l.flatMap (fun p =>
          p.1.serialize ++ (EF.price p.2 n).serialize ++ [3, 2]) := by
    intro l
    induction l with
    | nil => intro c; simp
    | cons p ps ih =>
        intro c
        simp only [List.foldl_cons, List.flatMap_cons]
        rw [ih]
        simp [EF.serialize, List.append_assoc]
  exact aux A.terms A.const

/-- A polynomial affine sequence has a uniform segment emitter for every cross-time price
feature.  Input `z = ⟨n,m⟩` denotes the feature pricing `Aₙ` on market day `m`. -/
theorem PolySequence.priceFeature_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) :
    PolySegStream (fun z => ((As z.unpair.1).priceFeature z.unpair.2).serialize) := by
  obtain ⟨ccount, hcount⟩ := h.termCount_poly
  obtain ⟨csentence, hsentence⟩ := h.sentence_poly
  -- An individual term block is indexed by `q = ⟨⟨n,m⟩,j⟩`.
  have hmember := PolyFueled.left.comp PolyFueled.left
  have hday := PolyFueled.right.comp PolyFueled.left
  have hterm := PolyFueled.right
  have hcanonical := hmember.pair hterm
  have hcoeff := h.coefficient_poly.comp hcanonical
  have hpriceTok : PolyTokenStream (fun q =>
      (EF.price (h.sentence
          (Nat.pair q.unpair.1.unpair.1 q.unpair.2)) q.unpair.1.unpair.2).serialize) := by
    have heq : (fun q : ℕ =>
        (EF.price (h.sentence
            (Nat.pair q.unpair.1.unpair.1 q.unpair.2)) q.unpair.1.unpair.2).serialize) =
        (fun q : ℕ => [0] ++ [Encodable.encode (h.sentence
            (Nat.pair q.unpair.1.unpair.1 q.unpair.2))] ++ [q.unpair.1.unpair.2]) := by
      funext q
      simp [EF.serialize]
    rw [heq]
    exact (PolyTokenStream.const 0).append
      ((PolyTokenStream.polyTok (hsentence.comp hcanonical)).append
        (PolyTokenStream.polyTok hday))
  have hprice := PolySegStream.ofTokenStream hpriceTok
  have hmul : PolySegStream (fun _ => [3]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 3)
  have hadd : PolySegStream (fun _ => [2]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 2)
  have hblock : PolySegStream (fun q =>
      (h.coefficient (Nat.pair q.unpair.1.unpair.1 q.unpair.2)).serialize ++
        (EF.price (h.sentence (Nat.pair q.unpair.1.unpair.1 q.unpair.2))
          q.unpair.1.unpair.2).serialize ++ [3, 2]) := by
    refine PolySegStream.of_eq (((hcoeff.append hprice).append hmul).append hadd) ?_
    intro q
    simp [List.append_assoc]
  have hblocks := PolySegStream.concatVar hblock (hcount.comp PolyFueled.left)
  have hconst := h.const_poly.comp PolyFueled.left
  refine PolySegStream.of_eq (hconst.append hblocks) ?_
  intro z
  rw [priceFeature_serialize, h.terms_eq]
  simp only [List.flatMap_map, Nat.unpair_pair]

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

theorem PolySequence.priceFeature_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (n m : ℕ) (ρ : List ℝ) (V : History) :
    ((As n).priceFeature m).denoteWith ρ V = ((As n).priceFeature m).denote V := by
  rw [priceFeature]
  have aux : ∀ (l : List (EF × Sentence)) (c : EF),
      c.denoteWith ρ V = c.denote V →
      (∀ p ∈ l, p.1.denoteWith ρ V = p.1.denote V) →
      (l.foldl (fun acc p => EF.add acc (EF.mul p.1 (EF.price p.2 m))) c).denoteWith ρ V =
        (l.foldl (fun acc p => EF.add acc (EF.mul p.1 (EF.price p.2 m))) c).denote V := by
    intro l
    induction l with
    | nil => intro c hc _; exact hc
    | cons p ps ih =>
        intro c hc ht
        simp only [List.foldl_cons]
        apply ih
        · simp only [EF.denoteWith, EF.denote_add, EF.denote_mul, EF.denote_price,
            Pi.add_apply, Pi.mul_apply]
          rw [hc, ht p (by simp)]
        · intro q hq
          exact ht q (by simp [hq])
  exact aux (As n).terms (As n).const (h.const_closed n ρ V)
    (fun p hp => h.term_closed n p hp ρ V)

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

/-- The paper's affine `L¹` norm, including the trailing constant coefficient. -/
noncomputable def l1Norm (A : AffineCombination) (V : History) : ℝ :=
  |A.const.denote V| + A.magnitude V

theorem magnitude_nonneg (A : AffineCombination) (V : History) :
    0 ≤ A.magnitude V :=
  List.sum_nonneg (fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact abs_nonneg _)

theorem magnitude_le_l1Norm (A : AffineCombination) (V : History) :
    A.magnitude V ≤ A.l1Norm V := by
  simp only [l1Norm]
  exact le_add_of_nonneg_left (abs_nonneg _)

/-- Market prices in `[0,1]` evaluate an affine combination within its paper `L¹` norm. -/
theorem abs_price_le_l1Norm (A : AffineCombination) (V : History) (n : ℕ)
    (hP : ∀ φ, 0 ≤ V n φ ∧ V n φ ≤ 1) :
    |A.price V n| ≤ A.l1Norm V := by
  have hsum :
      |(A.terms.map (fun p => p.1.denote V * V n p.2)).sum| ≤
        (A.terms.map (fun p => |p.1.denote V|)).sum := by
    induction A.terms with
    | nil => simp
    | cons p ps ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          |p.1.denote V * V n p.2 +
                (ps.map (fun q => q.1.denote V * V n q.2)).sum| ≤
              |p.1.denote V * V n p.2| +
                |(ps.map (fun q => q.1.denote V * V n q.2)).sum| := abs_add_le _ _
          _ ≤ |p.1.denote V| +
                (ps.map (fun q => |q.1.denote V|)).sum := by
              apply add_le_add
              · rw [abs_mul, abs_of_nonneg (hP p.2).1]
                exact mul_le_of_le_one_right (abs_nonneg _) (hP p.2).2
              · exact ih
  calc
    |A.price V n| =
        |A.const.denote V +
          (A.terms.map (fun p => p.1.denote V * V n p.2)).sum| := rfl
    _ ≤ |A.const.denote V| +
        |(A.terms.map (fun p => p.1.denote V * V n p.2)).sum| := abs_add_le _ _
    _ ≤ A.l1Norm V := by
      simpa only [l1Norm, magnitude] using
        add_le_add_right hsum |A.const.denote V|

/-- `def:bap` / the paper's `BCS`: a uniformly polynomially generated affine sequence
whose full coefficient `L¹` norm (including the trailing constant) has one uniform bound. -/
structure BoundedCombinationSequence (As : ℕ → AffineCombination) (V : History) where
  poly : PolySequence As
  bounded : ∃ B : ℝ, ∀ n, (As n).l1Norm V ≤ B

theorem BoundedCombinationSequence.magnitudeBounded
    {As : ℕ → AffineCombination} {V : History}
    (h : BoundedCombinationSequence As V) :
    ∃ B : ℝ, ∀ n, (As n).magnitude V ≤ B := by
  obtain ⟨B, hB⟩ := h.bounded
  exact ⟨B, fun n => ((As n).magnitude_le_l1Norm V).trans (hB n)⟩

/-- Two market assessments of the same affine combination differ by at most its share
magnitude.  The affine constant again cancels. -/
theorem abs_price_sub_price_le_magnitude (A : AffineCombination) (V : History) (m n : ℕ)
    (hm : ∀ φ, 0 ≤ V m φ ∧ V m φ ≤ 1)
    (hn : ∀ φ, 0 ≤ V n φ ∧ V n φ ≤ 1) :
    |A.price V m - A.price V n| ≤ A.magnitude V := by
  simp only [price, value, magnitude]
  ring_nf
  induction A.terms with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      have hdiff : |V m p.2 - V n p.2| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hm p.2, hn p.2]
      calc
        |p.1.denote V * V m p.2 +
              (ps.map (fun q => q.1.denote V * V m q.2)).sum -
            (p.1.denote V * V n p.2 +
              (ps.map (fun q => q.1.denote V * V n q.2)).sum)| =
            |p.1.denote V * (V m p.2 - V n p.2) +
              ((ps.map (fun q => q.1.denote V * V m q.2)).sum -
                (ps.map (fun q => q.1.denote V * V n q.2)).sum)| := by ring_nf
        _ ≤ |p.1.denote V * (V m p.2 - V n p.2)| +
              |(ps.map (fun q => q.1.denote V * V m q.2)).sum -
                (ps.map (fun q => q.1.denote V * V n q.2)).sum| := abs_add_le _ _
        _ ≤ |p.1.denote V| + (ps.map (fun q => |q.1.denote V|)).sum := by
          rw [abs_mul]
          exact add_le_add (by nlinarith [abs_nonneg (p.1.denote V)]) ih

/-- Absolute value inside the expressible-feature DSL. -/
def absFeature (e : EF) : EF :=
  .max e (.mul (.const (-1)) e)

theorem absFeature_serialize (e : EF) :
    (absFeature e).serialize =
      e.serialize ++ (EF.const (-1)).serialize ++ e.serialize ++ [3, 4] := by
  simp [absFeature, EF.serialize, List.append_assoc]

theorem absFeature_denoteWith (e : EF) (V : History) (ρ : List ℝ) :
    (absFeature e).denoteWith ρ V = |e.denoteWith ρ V| := by
  simp only [absFeature, EF.denoteWith, Rat.cast_neg, Rat.cast_one, neg_mul, one_mul]
  rw [abs_eq_max_neg]

@[simp] theorem absFeature_rank (e : EF) : (absFeature e).rank = e.rank := by
  simp [absFeature, EF.rank]

/-- Share magnitude reified as an expressible feature. -/
def magnitudeFeature (A : AffineCombination) : EF :=
  A.terms.foldr (fun p acc => EF.add (absFeature p.1) acc) (EF.const 0)

theorem magnitudeFeature_serialize (A : AffineCombination) :
    A.magnitudeFeature.serialize =
      A.terms.flatMap (fun p => (absFeature p.1).serialize) ++
        (EF.const 0).serialize ++ List.replicate A.terms.length 2 := by
  rw [magnitudeFeature]
  induction A.terms with
  | nil => simp [EF.serialize]
  | cons p ps ih =>
      simp only [List.foldr_cons, List.flatMap_cons, List.length_cons]
      rw [show (EF.add (absFeature p.1)
          (ps.foldr (fun q acc => EF.add (absFeature q.1) acc) (EF.const 0))).serialize =
        (absFeature p.1).serialize ++
          (ps.foldr (fun q acc => EF.add (absFeature q.1) acc) (EF.const 0)).serialize ++
            [2] by simp [EF.serialize]]
      rw [ih]
      simp [List.replicate_succ', List.append_assoc]

/-- Uniform emission of the reified share magnitude for a polynomial affine sequence. -/
theorem PolySequence.magnitudeFeature_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) :
    PolySegStream (fun n => (As n).magnitudeFeature.serialize) := by
  obtain ⟨ccount, hcount⟩ := h.termCount_poly
  have hneg : PolySegStream (fun _ => (EF.const (-1)).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))
  have hmul : PolySegStream (fun _ => [3]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 3)
  have hmax : PolySegStream (fun _ => [4]) :=
    PolySegStream.ofTokenStream (PolyTokenStream.const 4)
  have habs : PolySegStream (fun z => (absFeature (h.coefficient z)).serialize) := by
    refine PolySegStream.of_eq
      ((((h.coefficient_poly.append hneg).append h.coefficient_poly).append hmul).append
        hmax) ?_
    intro z
    rw [absFeature_serialize]
    simp [List.append_assoc]
  have hterms := PolySegStream.concatVar habs hcount
  have hzero : PolySegStream (fun _ => (EF.const 0).serialize) :=
    PolySegStream.ofTokenStream (PolyTokenStream.serialize_const 0)
  have htags := PolySegStream.repeatTag 2 hcount
  refine PolySegStream.of_eq ((hterms.append hzero).append htags) ?_
  intro n
  rw [magnitudeFeature_serialize, h.terms_eq]
  simp only [List.flatMap_map, List.length_map, List.length_range]

theorem magnitudeFeature_denoteWith (A : AffineCombination) (V : History) (ρ : List ℝ) :
    (A.magnitudeFeature).denoteWith ρ V =
      (A.terms.map (fun p => |p.1.denoteWith ρ V|)).sum := by
  have aux : ∀ l : List (EF × Sentence),
      (l.foldr (fun p acc => EF.add (absFeature p.1) acc) (EF.const 0)).denoteWith ρ V =
        (l.map (fun p => |p.1.denoteWith ρ V|)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p ps ih =>
        simp only [List.foldr_cons, EF.denoteWith, absFeature_denoteWith,
          List.map_cons, List.sum_cons, ih]
  exact aux A.terms

theorem magnitudeFeature_denote (A : AffineCombination) (V : History) :
    A.magnitudeFeature.denote V = A.magnitude V := by
  rw [EF.denote, magnitudeFeature_denoteWith]
  rfl

theorem PolySequence.magnitudeFeature_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) (n : ℕ) (ρ : List ℝ) (V : History) :
    (As n).magnitudeFeature.denoteWith ρ V = (As n).magnitudeFeature.denote V := by
  rw [magnitudeFeature_denoteWith, magnitudeFeature_denote, magnitude]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [h.term_closed n p hp ρ V]

theorem magnitudeFeature_rank_le (A : AffineCombination) {n : ℕ}
    (hterms : ∀ p ∈ A.terms, p.1.rank ≤ n) : A.magnitudeFeature.rank ≤ n := by
  have aux : ∀ l : List (EF × Sentence),
      (∀ p ∈ l, p.1.rank ≤ n) →
      (l.foldr (fun p acc => EF.add (absFeature p.1) acc) (EF.const 0)).rank ≤ n := by
    intro l
    induction l with
    | nil => intro _; simp
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

theorem PolySequence.riskFeature_closed {As : ℕ → AffineCombination}
    (h : PolySequence As) {entry : ℕ → EF}
    (hentry : ∀ n ρ V, (entry n).denoteWith ρ V = (entry n).denote V)
    (n : ℕ) (ρ : List ℝ) (V : History) :
    ((As n).riskFeature (entry n)).denoteWith ρ V =
      ((As n).riskFeature (entry n)).denote V := by
  simp only [riskFeature, EF.denoteWith, EF.denote_mul, Pi.mul_apply]
  rw [hentry n ρ V, h.magnitudeFeature_closed n ρ V]

theorem riskFeature_rank_le (A : AffineCombination) (entry : EF) {n : ℕ}
    (hentry : entry.rank ≤ n) (hterms : ∀ p ∈ A.terms, p.1.rank ≤ n) :
    (A.riskFeature entry).rank ≤ n := by
  simp only [riskFeature, EF.rank]
  exact Nat.max_le.mpr ⟨hentry, A.magnitudeFeature_rank_le hterms⟩

/-- Uniform launch-risk emission once the entry feature is uniformly emitted. -/
theorem PolySequence.riskFeature_polySeg {As : ℕ → AffineCombination}
    (h : PolySequence As) {entry : ℕ → EF}
    (hentry : PolySegStream (fun n => (entry n).serialize)) :
    PolySegStream (fun n => ((As n).riskFeature (entry n)).serialize) :=
  PolySegStream.serialize_mul hentry h.magnitudeFeature_polySeg

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

/-- Polynomial affine families are closed under multiplication by a fixed rational.
This is the uniform normalization operation used to pass from the paper's arbitrary
bounded-combination sequences to the unit-magnitude economic core. -/
def PolySequence.scaleRat {As : ℕ → AffineCombination} (h : PolySequence As) (q : ℚ) :
    PolySequence (fun n => (As n).scale (.const q)) where
  termCount := h.termCount
  coefficient := fun z => EF.mul (EF.const q) (h.coefficient z)
  sentence := h.sentence
  termCount_poly := h.termCount_poly
  const_poly := PolySegStream.serialize_mul
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const q)) h.const_poly
  coefficient_poly := PolySegStream.serialize_mul
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const q))
    h.coefficient_poly
  sentence_poly := h.sentence_poly
  terms_eq := by
    intro n
    rw [AffineCombination.scale, h.terms_eq]
    simp [List.map_map, Function.comp_def]
  const_rank := by
    intro n
    simp only [AffineCombination.scale, EF.rank]
    exact Nat.max_le.mpr ⟨by simp, h.const_rank n⟩
  coefficient_rank := by
    intro n j hj
    simp only [EF.rank]
    exact Nat.max_le.mpr ⟨by simp, h.coefficient_rank n j hj⟩
  const_closed := by
    intro n ρ V
    simp only [AffineCombination.scale, EF.denoteWith, EF.denote_mul, EF.denote_const,
      Pi.mul_apply]
    rw [h.const_closed n ρ V]
  coefficient_closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, EF.denote_const, Pi.mul_apply]
    rw [h.coefficient_closed z ρ V]

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

/-- Polynomial affine families are closed under pointwise negation. -/
def PolySequence.neg {As : ℕ → AffineCombination} (h : PolySequence As) :
    PolySequence (fun n => (As n).neg) where
  termCount := h.termCount
  coefficient := fun z => EF.mul (EF.const (-1)) (h.coefficient z)
  sentence := h.sentence
  termCount_poly := h.termCount_poly
  const_poly := PolySegStream.serialize_mul
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1))) h.const_poly
  coefficient_poly := PolySegStream.serialize_mul
    (PolySegStream.ofTokenStream (PolyTokenStream.serialize_const (-1)))
    h.coefficient_poly
  sentence_poly := h.sentence_poly
  terms_eq := by
    intro n
    rw [AffineCombination.neg, AffineCombination.scale, h.terms_eq]
    simp [List.map_map, Function.comp_def]
  const_rank := by
    intro n
    simp only [AffineCombination.neg, AffineCombination.scale, EF.rank]
    exact Nat.max_le.mpr ⟨by simp, h.const_rank n⟩
  coefficient_rank := by
    intro n j hj
    simp only [EF.rank]
    exact Nat.max_le.mpr ⟨by simp, h.coefficient_rank n j hj⟩
  const_closed := by
    intro n ρ V
    simp only [AffineCombination.neg, AffineCombination.scale, EF.denoteWith,
      EF.denote_mul, EF.denote_const,
      Pi.mul_apply]
    rw [h.const_closed n ρ V]
  coefficient_closed := by
    intro z ρ V
    simp only [EF.denoteWith, EF.denote_mul, EF.denote_const, Pi.mul_apply]
    rw [h.coefficient_closed z ρ V]

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
        simp
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
